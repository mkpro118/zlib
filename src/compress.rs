use crate::adler::adler32;
use crate::bitwriter::BitWriter;
use crate::huffman::{
    get_distance_code, get_length_code, HuffmanTree, CODE_LENGTH_CODES_ORDER,
    DISTANCE_BASE, DISTANCE_EXTRA_BITS, LENGTH_BASE, LENGTH_EXTRA_BITS,
    ZLIB_MAX_STRING_LENGTH, ZLIB_MIN_STRING_LENGTH, ZLIB_WINDOW_SIZE,
};
use crate::lz77::{LZ77Compressor, LZ77Unit};
use LZ77Unit::{Literal, Marker};

const SIXTEEN_KB: usize = 16 * 1024;

const PREVIOUS_CODE: usize = 16;
const PREVIOUS_MIN: usize = 3;
const PREVIOUS_MAX: usize = 6;
const PREVIOUS_MIN_RANGE: usize = 4;
/* const PREVIOUS_MAX_RANGE: usize = 7; */
const SHORT_ZERO_CODE: usize = 17;
const LONG_ZERO_CODE: usize = 18;
const SHORT_ZERO_MIN: usize = 3;
const SHORT_ZERO_MAX: usize = 10;
const LONG_ZERO_MIN: usize = 11;
const LONG_ZERO_MAX: usize = 138;

#[derive(Debug)]
pub enum Strategy {
    Auto,
    Dynamic,
    Fixed,
    Raw,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug)]
enum RunLengthEncoding {
    Once(usize),
    Repeat(usize, usize),
}

use RunLengthEncoding::{Once, Repeat};

#[allow(
    clippy::unusual_byte_groupings,
    clippy::cast_possible_truncation,
    clippy::missing_panics_doc
)]
#[must_use]
pub fn compress(data: &[u8], strategy: &Strategy) -> Vec<u8> {
    use Strategy::{Auto, Dynamic, Fixed, Raw};
    const COMPRESSION_METHOD: u8 = 0b0000_1000;
    const COMPRESSION_INFO: u8 = 0b0111_0000;
    const FDICT_MASK: u8 = 0b00_1_00000;
    const FLEVEL_MASK: u8 = 0b11_000000;
    const NO_FDICT_OR_FLEVEL: u8 = !(FDICT_MASK | FLEVEL_MASK);

    let mut bitwriter = BitWriter::new();

    let cmf = COMPRESSION_INFO | COMPRESSION_METHOD;
    bitwriter.write_byte(cmf);

    let fcheck = 31 - (((cmf as usize) * 256) % 31);
    assert!(
        fcheck & 0b111_00000 == 0,
        "Incorrect FCHECK, more than 5 bits!!"
    );

    // Clear the FDICT and FLEVEL bits;
    let flg = (fcheck as u8) & NO_FDICT_OR_FLEVEL;
    bitwriter.write_byte(flg);

    match strategy {
        Dynamic => compress_dynamic(&mut bitwriter, data),
        Fixed => compress_fixed(&mut bitwriter, data),
        Raw => compress_raw(&mut bitwriter, data),
        Auto => {}
    };

    // Checksum
    let checksum = adler32(data).to_be_bytes();
    bitwriter.write_bytes(&checksum);

    bitwriter.finish()
}

#[allow(clippy::cast_possible_truncation)]
fn compress_raw(writer: &mut BitWriter, data: &[u8]) {
    let n_blocks = data.len().div_ceil(SIXTEEN_KB) - 1;

    for (curr_block, chunk) in data.chunks(SIXTEEN_KB).enumerate() {
        // BFINAL
        writer.write_bit(u8::from(curr_block == n_blocks));

        // BTYPE
        writer.write_bits(0b00, 2);

        // Write length of block
        let len = data.len() as u16;
        let bytes = [(len & 0xff) as u8, (len >> 8) as u8];
        writer.write_bytes(&bytes);

        // Write one's complement of the length of block
        let len = !len;
        let bytes = [(len & 0xff) as u8, (len >> 8) as u8];
        writer.write_bytes(&bytes);

        // Write the raw block out
        writer.write_bytes(chunk);
    }
}

fn compress_fixed(writer: &mut BitWriter, data: &[u8]) {
    // BFINAL = 1, we only write one massive block
    writer.write_bit(0b1);
    // BTYPE = 01, Fixed Huffman Codes
    writer.write_bits(0b01, 2);

    let compressor = get_zlib_compressor();
    let (mut length_tree, mut distance_tree) = HuffmanTree::get_zlib_fixed();
    length_tree.assign();
    distance_tree.assign();

    let compressed = compressor.compress(data);
    write_compressed_data(writer, &compressed, &length_tree, &distance_tree);
}

#[allow(clippy::cast_possible_truncation)]
fn compress_dynamic(writer: &mut BitWriter, data: &[u8]) {
    // BFINAL = 1, we only write one massive block
    writer.write_bit(0b1);
    // BTYPE = 10, Dynamic Huffman Codes
    writer.write_bits(0b10, 2);

    let compressor = get_zlib_compressor();
    let compressed = compressor.compress(data);

    let (ltree, dtree) = create_dynamic_trees(&compressed, &compressor);

    write_dynamic_header(writer, &ltree, &dtree);

    // the easy part, write out the data
    write_compressed_data(writer, &compressed, &ltree, &dtree);
}

#[allow(clippy::cast_possible_truncation)]
fn write_dynamic_header(
    writer: &mut BitWriter,
    ltree: &HuffmanTree,
    dtree: &HuffmanTree,
) {
    let (ltree_codelengths, dtree_codelengths) = get_codelengths(ltree, dtree);
    let combined_rle = zlib_rle(&ltree_codelengths, &dtree_codelengths);
    let code_tree = get_code_tree(&combined_rle);
    let hcodes = get_hcodes(&code_tree);

    // Now we have all the data to write out the header
    let hlit = ltree_codelengths.len() - 257;
    let hdist = dtree_codelengths.len() - 1;
    let hclen = hcodes.len() - 4;

    writer.write_bits(hlit, 5);
    writer.write_bits(hdist, 5);
    writer.write_bits(hclen, 4);

    // Write out the (hclen + 4) * 3 bits of code lengths for the code length
    // alphabet
    for hcode in hcodes {
        writer.write_bits(hcode, 3);
    }

    // Write out the encoded huffman literal/length and distance trees
    for (codelength, extra) in combined_rle {
        let sym =
            char::from_u32(codelength as u32).expect("Should be in range");
        let (encoded, len) =
            code_tree.encode(sym).expect("Just made it, should exist");

        writer.write_bits(encoded, len);
        if let Some(extra_len) = extra {
            let (extra_len, nbits) = match codelength {
                16 => (extra_len - 3, 2),
                17 => (extra_len - 3, 3),
                18 => (extra_len - 11, 7),
                _ => unreachable!(),
            };
            writer.write_bits(extra_len, nbits);
        }
    }
}

fn write_compressed_data(
    writer: &mut BitWriter,
    compressed: &[LZ77Unit],
    ltree: &HuffmanTree,
    dtree: &HuffmanTree,
) {
    for unit in compressed {
        match unit {
            Literal(byte) => {
                literal_writer(ltree, writer, char::from(*byte));
            }
            Marker(length, distance) => {
                length_writer(ltree, writer, *length);
                distance_writer(dtree, writer, *distance);
            }
        }
    }
    literal_writer(ltree, writer, '\u{100}');
}

fn create_dynamic_trees(
    compressed: &[LZ77Unit],
    compressor: &LZ77Compressor,
) -> (HuffmanTree, HuffmanTree) {
    let (mut ltree, mut dtree) = HuffmanTree::from_lz77(compressed, compressor);

    let (lmax, dmax) = (ltree.max_code_len(), dtree.max_code_len());
    assert!(
        lmax <= 15,
        "The Literal/Length code lengths are too long, found {lmax}"
    );
    assert!(
        dmax <= 15,
        "The Distance code lengths are too long, found {dmax}"
    );
    ltree.assign();
    dtree.assign();
    (ltree.to_canonical(), dtree.to_canonical())
}

fn literal_writer(ltree: &HuffmanTree, writer: &mut BitWriter, byte: char) {
    let Some((code, len)) = ltree.encode(byte) else {
        panic!("No encoding found for '{byte}'");
    };
    writer.write_bits(code, len);
}

#[allow(clippy::cast_possible_truncation)]
fn length_writer(ltree: &HuffmanTree, writer: &mut BitWriter, length: usize) {
    assert!(length >= 3, "Length too short found {length}!");
    assert!(length <= 258, "Length too long found {length}!");

    let code = get_length_code(length);
    let symbol = char::from_u32(code as u32).unwrap();
    let (huffman_code, huffman_len) =
        ltree.encode(symbol).unwrap_or_else(|| {
            panic!(
                "Symbol '{symbol}' not found, \
            (code = {code}, length = {length})"
            )
        });

    // Write Huffman code for the length symbol
    writer.write_bits(huffman_code, huffman_len);

    // Write extra bits if needed
    let extra_bits = LENGTH_EXTRA_BITS[code - 257];
    if extra_bits > 0 {
        let extra_value = length - LENGTH_BASE[code - 257];
        writer.write_bits(extra_value, extra_bits);
    }
}

#[allow(clippy::cast_possible_truncation)]
fn distance_writer(
    dtree: &HuffmanTree,
    writer: &mut BitWriter,
    distance: usize,
) {
    assert!(distance >= 1, "Distance too short, found {distance}!");
    assert!(distance <= 32768, "Distance too long, found {distance}!");

    let code = get_distance_code(distance);
    let symbol =
        char::from_u32(code as u32).expect("Should convert, already checked");
    let (huffman_code, huffman_len) = dtree
        .encode(symbol)
        .unwrap_or_else(|| panic!("No encoding for {code}"));

    // Write 5-bit distance code
    writer.write_bits(huffman_code, huffman_len);

    // Write extra bits if needed
    let extra_bits = DISTANCE_EXTRA_BITS[code];
    if extra_bits > 0 {
        let extra_value = distance - DISTANCE_BASE[code];
        writer.write_bits(extra_value, extra_bits);
    }
}

fn get_codelengths(
    ltree: &HuffmanTree,
    dtree: &HuffmanTree,
) -> (Vec<usize>, Vec<usize>) {
    // Get all encodings
    let ltree_encodings = ltree
        .encodings()
        .expect("Should exist, codes have been assigned");
    let dtree_encodings = dtree
        .encodings()
        .expect("Should exist, codes have been assigned");

    // Get the maximum length/distance values, these will eventually
    // be used to compute hlit and hdist
    let ltree_max_value = *ltree_encodings
        .keys()
        .max()
        .filter(|&max| *max > '\u{100}')
        .unwrap_or(&'\u{101}');
    let dtree_max_value = *dtree_encodings.keys().max().unwrap_or(&(1 as char));

    // Extract just the length of the codes, not the codes themselves
    let ltree_codelengths = ((0 as char)..=ltree_max_value)
        .map(|c| ltree.encode(c).map_or(0, |(_, len)| len))
        .collect::<Vec<usize>>();

    let dtree_codelengths = ((0 as char)..=dtree_max_value)
        .map(|c| dtree.encode(c).map_or(0, |(_, len)| len))
        .collect::<Vec<usize>>();

    (ltree_codelengths, dtree_codelengths)
}

#[allow(clippy::cast_possible_truncation)]
fn get_code_tree(combined: &[(usize, Option<usize>)]) -> HuffmanTree {
    let codes_only = combined
        .iter()
        .map(|&(code, _)| code as u8)
        .collect::<Vec<u8>>();

    // This combined codes is our data, make a tree from these codes.
    let mut code_tree = HuffmanTree::from_data(&codes_only);
    code_tree.assign();
    let code_tree = code_tree.to_canonical();

    // Sanity check
    let cmax = code_tree.max_code_len();
    assert!(
        cmax <= 7,
        "The Code code lengths are too long, found {cmax}"
    );

    code_tree
}

#[allow(clippy::cast_possible_truncation)]
fn get_hcodes(code_tree: &HuffmanTree) -> Vec<usize> {
    let hcodes = CODE_LENGTH_CODES_ORDER
        .iter()
        .map(|&code| {
            code_tree
                .encode(
                    char::from_u32(code as u32).expect("Should be in range"),
                )
                .map_or(0, |(_, len)| len)
        })
        .collect::<Vec<usize>>();

    let trailing_zeros = hcodes.iter().rev().position(|&x| x > 0).unwrap_or(0);
    let hcodes = hcodes[..(hcodes.len() - trailing_zeros)].to_vec();

    assert!(hcodes.len() >= 4, "Should be at least 4");
    hcodes
}

fn get_zlib_compressor() -> LZ77Compressor {
    let mut compressor = LZ77Compressor::with_window_size(ZLIB_WINDOW_SIZE);
    compressor.min_match_length = ZLIB_MIN_STRING_LENGTH;
    compressor.max_match_length = ZLIB_MAX_STRING_LENGTH;
    compressor
}

fn zlib_rle(
    ltree_codelengths: &[usize],
    dtree_codelengths: &[usize],
) -> Vec<(usize, Option<usize>)> {
    // Run Length Encode the codelengths
    let ltree_run_length = run_length_encode(ltree_codelengths);
    let ltree_run_length = rle_to_zlib_codes(&ltree_run_length);
    let dtree_run_length = run_length_encode(dtree_codelengths);
    let dtree_run_length = rle_to_zlib_codes(&dtree_run_length);

    // Combine into one long sequence
    [ltree_run_length, dtree_run_length].concat()
}

fn run_length_encode(data: &[usize]) -> Vec<RunLengthEncoding> {
    use RunLengthEncoding::{Once, Repeat};
    let len = data.len();

    let mut encoding = vec![];
    let mut pos = 0;

    while pos < len {
        let mut count = 1;

        while pos + 1 < len && data[pos] == data[pos + 1] {
            pos += 1;
            count += 1;
        }

        if count > 1 {
            encoding.push(Repeat(data[pos], count));
        } else {
            encoding.push(Once(data[pos]));
        }
        pos += 1;
    }

    encoding
}

fn rle_to_zlib_codes(rle: &[RunLengthEncoding]) -> Vec<(usize, Option<usize>)> {
    rle.iter().fold(vec![], |mut acc, encoded| {
        match encoded {
            Once(num) => acc.push((*num, None)),
            Repeat(num, repetitions) => {
                if *num == 0 {
                    zlib_rle_encode_zero(&mut acc, *repetitions);
                } else {
                    zlib_rle_encode_nonzero(&mut acc, *num, *repetitions);
                }
            }
        };
        acc
    })
}

fn zlib_rle_encode_zero(
    acc: &mut Vec<(usize, Option<usize>)>,
    mut repetitions: usize,
) {
    while repetitions > 0 {
        match repetitions {
            SHORT_ZERO_MIN..=SHORT_ZERO_MAX => {
                acc.push((SHORT_ZERO_CODE, Some(repetitions)));
                break;
            }
            LONG_ZERO_MIN.. => {
                let current_count = if repetitions > LONG_ZERO_MAX {
                    repetitions -= LONG_ZERO_MAX;
                    LONG_ZERO_MAX
                } else {
                    let temp = repetitions;
                    repetitions = 0;
                    temp
                };
                acc.push((LONG_ZERO_CODE, Some(current_count)));
            }
            _ => {
                acc.extend_from_slice(&[(0, None)].repeat(repetitions));
                break;
            }
        }
    }
}

fn zlib_rle_encode_nonzero(
    acc: &mut Vec<(usize, Option<usize>)>,
    num: usize,
    mut repetitions: usize,
) {
    while repetitions > 0 {
        match repetitions {
            ..=PREVIOUS_MIN => {
                acc.extend_from_slice(&[(num, None)].repeat(repetitions));
                break;
            }
            PREVIOUS_MIN_RANGE.. => {
                acc.push((num, None));
                repetitions -= 1;
                let current_count = if repetitions > PREVIOUS_MAX {
                    repetitions -= PREVIOUS_MAX;
                    PREVIOUS_MAX
                } else {
                    let temp = repetitions;
                    repetitions = 0;
                    temp
                };
                acc.push((PREVIOUS_CODE, Some(current_count)));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_dynamic_header() {
        use crate::bitreader::BitReader;
        let (mut tree1, mut tree2) = (HuffmanTree::new(), HuffmanTree::new());

        tree1.insert(0b11, 2, 'A');
        tree1.insert(0b10, 2, 'B');
        tree1.insert(0b01, 2, '\u{100}');
        tree1.insert(0b001, 3, '\u{101}');
        tree1.insert(0b0001, 4, '\u{102}');
        tree1.assign();

        tree2.insert(0b0, 1, 0 as char);
        tree2.insert(0b10, 2, 1 as char);
        tree2.assign();

        let (tree1, tree2) = (tree1.to_canonical(), tree2.to_canonical());

        let mut writer = BitWriter::new();

        write_dynamic_header(&mut writer, &tree1, &tree2);

        let res = writer.finish();
        let mut reader = BitReader::new(&res);
        let (mut ltree, mut dtree) = HuffmanTree::decode_trees(&mut reader);
        ltree.assign();
        dtree.assign();

        // We know that the headers were correct
        // if we can rebuild the same trees from the header
        assert_eq!(ltree.encodings(), tree1.encodings());
        assert_eq!(dtree.encodings(), tree2.encodings());
    }

    #[test]
    #[allow(clippy::unusual_byte_groupings)]
    fn test_write_compressed_data() {
        let (mut tree1, mut tree2) = (HuffmanTree::new(), HuffmanTree::new());

        tree1.insert(0b11, 2, 'A');
        tree1.insert(0b10, 2, 'B');
        tree1.insert(0b01, 2, '\u{100}');
        tree1.insert(0b001, 3, '\u{101}');
        tree1.insert(0b0001, 4, '\u{102}');
        tree1.assign();

        tree2.insert(0b0, 1, 0 as char);
        tree2.insert(0b10, 2, 1 as char);
        tree2.assign();

        let compressed = vec![
            Literal(b'A'),
            Literal(b'B'),
            Literal(b'B'),
            Literal(b'A'),
            Literal(b'A'),
            Marker(4, 1),
            Literal(b'B'),
            Marker(3, 2),
        ];

        let mut writer = BitWriter::new();

        write_compressed_data(&mut writer, &compressed, &tree1, &tree2);
        let res = writer.finish();
        let expected = vec![0b11_01_01_11u8, 0b1_0_1000_11u8, 0b10_01_100_0u8];

        assert_eq!(res, expected);
    }

    #[test]
    #[allow(clippy::unusual_byte_groupings)]
    fn test_literal_writer() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b0, 1, 'A');
        tree.insert(0b10, 2, 'B');
        tree.insert(0b110, 3, 'C');
        tree.insert(0b111, 3, 'D');
        tree.assign();

        let mut writer = BitWriter::new();
        for &sym in b"BADCADDAD" {
            literal_writer(&tree, &mut writer, sym as char);
        }

        let res = writer.finish();
        // The groupings are done to show the character encodings
        let expected = vec![0b11_111_0_01u8, 0b111_111_0_0u8, 0b111_0u8];

        assert_eq!(res, expected);
    }

    #[test]
    #[allow(clippy::unusual_byte_groupings)]
    fn test_length_writer() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b0, 1, '\u{101}');
        tree.insert(0b10, 2, '\u{104}');
        tree.insert(0b110, 3, '\u{113}');
        tree.insert(0b111, 3, '\u{11D}');
        tree.assign();

        let mut writer = BitWriter::new();
        for sym in [3, 6, 54, 258] {
            length_writer(&tree, &mut writer, sym);
        }

        let res = writer.finish();
        // The groupings are done to show the character encodings
        let expected = vec![0b11_011_01_0u8, 0b111_0u8];

        assert_eq!(res, expected);
    }

    #[test]
    #[allow(clippy::unusual_byte_groupings)]
    fn test_distance_writer() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b0, 1, 0 as char);
        tree.insert(0b10, 2, 5 as char);
        tree.insert(0b110, 3, 17 as char);
        tree.insert(0b111, 3, 20 as char);
        tree.assign();

        let mut writer = BitWriter::new();
        for sym in [1, 8, 454, 1035] {
            distance_writer(&tree, &mut writer, sym);
        }

        let res = writer.finish();
        // The groupings are done to show the character encodings
        let expected =
            vec![0b1_011_1_01_0u8, 0b11_100010u8, 0b0001010_1u8, 0b_0u8];

        assert_eq!(res, expected);
    }

    #[test]
    fn test_get_codelengths() {
        let (mut tree1, mut tree2) = (HuffmanTree::new(), HuffmanTree::new());
        for tree in [&mut tree1, &mut tree2] {
            tree.insert(0b0, 1, 0 as char);
            tree.insert(0b10, 2, 1 as char);
            tree.insert(0b110, 3, 2 as char);
            tree.insert(0b111, 3, 3 as char);
            tree.assign();
        }

        let (cl1, cl2) = get_codelengths(&tree1, &tree2);
        let expected1 = [vec![1, 2, 3, 3], vec![0; 254]].concat();
        let expected2 = vec![1, 2, 3, 3];
        assert_eq!(cl1, expected1);
        assert_eq!(cl2, expected2);
    }

    #[test]
    fn test_get_code_tree() {
        let combined = [
            vec![
                (17, Some(4)),
                (2, None),
                (2, None),
                (2, None),
                (11, None),
                (16, Some(6)),
            ],
            vec![
                (1, None),
                (16, Some(3)),
                (7, None),
                (16, Some(6)),
                (7, None),
                (16, Some(3)),
            ],
        ]
        .concat();

        let code_tree = get_code_tree(&combined);

        // TC 1, these symbols should exist
        {
            let syms: [u8; 6] = [1, 2, 7, 11, 16, 17];
            for sym in syms.map(char::from) {
                assert!(code_tree.encode(sym).is_some());
            }
        }

        // TC 2, these symbols should not exist
        {
            let syms: [u8; 12] = [3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 18];
            for sym in syms.map(char::from) {
                assert!(code_tree.encode(sym).is_none());
            }
        }
    }

    #[test]
    fn test_get_hcodes() {
        // TC 1
        {
            let mut code_tree = HuffmanTree::new();
            code_tree.insert(0b0, 1, 17 as char);
            code_tree.insert(0b10, 2, 4 as char);
            code_tree.insert(0b110, 3, 16 as char);
            code_tree.insert(0b111, 3, 15 as char);
            code_tree.assign();

            // 16 and 17 are the first two indices in CODE_LENGTH_CODES_ORDER.
            // Index of 4 is 11, So skip 9 elements (2..=10)
            // Index of 15 is 18, So skip 6 elements (12..=17)
            let expected =
                [vec![3, 1], vec![0; 9], vec![2], vec![0; 6], vec![3]].concat();

            let hcodes = get_hcodes(&code_tree);
            assert_eq!(hcodes, expected);
        }

        // TC 2, ensure trailing zeros are removed
        {
            let mut code_tree = HuffmanTree::new();
            code_tree.insert(0b0, 1, 16 as char);
            code_tree.insert(0b10, 2, 4 as char);
            code_tree.insert(0b110, 3, 17 as char);
            code_tree.insert(0b111, 3, 18 as char);
            code_tree.assign();

            // 16 17 and 18 are the first three indices.
            // Index of 4 is 11, So skip 8 elements (2..=10)
            let expected = [vec![1, 3, 3], vec![0; 8], vec![2]].concat();

            let hcodes = get_hcodes(&code_tree);
            assert_eq!(hcodes, expected);
        }
    }

    #[test]
    fn test_get_zlib_compressor() {
        let compressor = get_zlib_compressor();
        assert_eq!(compressor.window_size, ZLIB_WINDOW_SIZE);
        assert_eq!(compressor.min_match_length, ZLIB_MIN_STRING_LENGTH);
        assert_eq!(compressor.max_match_length, ZLIB_MAX_STRING_LENGTH);
    }

    #[test]
    fn test_zlib_rle() {
        let data = [(
            [[0].repeat(4), [2].repeat(3), [11].repeat(7)].concat(),
            [[1].repeat(4), [7].repeat(11)].concat(),
            [
                vec![
                    (17, Some(4)),
                    (2, None),
                    (2, None),
                    (2, None),
                    (11, None),
                    (16, Some(6)),
                ],
                vec![
                    (1, None),
                    (16, Some(3)),
                    (7, None),
                    (16, Some(6)),
                    (7, None),
                    (16, Some(3)),
                ],
            ]
            .concat(),
        )];

        for (cl1, cl2, expected) in data {
            let actual = zlib_rle(&cl1, &cl2);
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn test_run_length_encode() {
        let data = [
            (
                [[1].repeat(6), [2].repeat(3), vec![0], [5].repeat(12)]
                    .concat(),
                vec![Repeat(1, 6), Repeat(2, 3), Once(0), Repeat(5, 12)],
            ),
            (
                [[1].repeat(106), [122].repeat(23), vec![0; 5], [5].repeat(6)]
                    .concat(),
                vec![
                    Repeat(1, 106),
                    Repeat(122, 23),
                    Repeat(0, 5),
                    Repeat(5, 6),
                ],
            ),
            (
                vec![1, 2, 3, 4, 5],
                vec![Once(1), Once(2), Once(3), Once(4), Once(5)],
            ),
        ];

        for (input, expected) in data {
            let output = run_length_encode(&input);
            assert_eq!(output, expected);
        }
    }

    #[test]
    fn test_rle_to_zlib_codes() {
        let data = [
            (
                vec![Repeat(1, 6), Repeat(2, 3), Once(0), Repeat(5, 12)],
                vec![
                    (1, None),
                    (16, Some(5)),
                    (2, None),
                    (2, None),
                    (2, None),
                    (0, None),
                    (5, None),
                    (16, Some(6)),
                    (5, None),
                    (16, Some(4)),
                ],
            ),
            (
                vec![
                    Repeat(0, 106),
                    Repeat(12, 7),
                    Repeat(0, 10),
                    Repeat(0, 11),
                ],
                vec![
                    (18, Some(106)),
                    (12, None),
                    (16, Some(6)),
                    (17, Some(10)),
                    (18, Some(11)),
                ],
            ),
            (
                vec![Once(1), Once(2), Once(3), Once(4), Once(5)],
                vec![(1, None), (2, None), (3, None), (4, None), (5, None)],
            ),
            (
                vec![Repeat(1, 2), Repeat(0, 2), Repeat(3, 2)],
                vec![
                    (1, None),
                    (1, None),
                    (0, None),
                    (0, None),
                    (3, None),
                    (3, None),
                ],
            ),
            (vec![Repeat(0, 139)], vec![(18, Some(138)), (0, None)]),
        ];

        for (input, expected) in data {
            let output = rle_to_zlib_codes(&input);
            assert_eq!(output, expected);
        }
    }

    #[test]
    fn test_zlib_rle_encode_zero() {
        let data = [
            (0, vec![]),
            (1, vec![(0, None)]),
            (2, vec![(0, None), (0, None)]),
            (3, vec![(17, Some(3))]),
            (4, vec![(17, Some(4))]),
            (10, vec![(17, Some(10))]),
            (11, vec![(18, Some(11))]),
            (12, vec![(18, Some(12))]),
            (137, vec![(18, Some(137))]),
            (138, vec![(18, Some(138))]),
            (139, vec![(18, Some(138)), (0, None)]),
            (200, vec![(18, Some(138)), (18, Some(62))]),
        ];

        for (repetitions, expected) in data {
            let mut acc = vec![];
            zlib_rle_encode_zero(&mut acc, repetitions);
            assert_eq!(acc, expected);
        }
    }

    #[test]
    fn test_zlib_rle_encode_nonzero() {
        let data = [
            (0, 0, vec![]),
            (1, 1, vec![(1, None)]),
            (2, 2, vec![(2, None), (2, None)]),
            (3, 3, vec![(3, None), (3, None), (3, None)]),
            (4, 4, vec![(4, None), (16, Some(3))]),
            (5, 5, vec![(5, None), (16, Some(4))]),
            (7, 7, vec![(7, None), (16, Some(6))]),
            (8, 8, vec![(8, None), (16, Some(6)), (8, None)]),
            (
                11,
                11,
                vec![(11, None), (16, Some(6)), (11, None), (16, Some(3))],
            ),
            (
                15,
                15,
                vec![
                    (15, None),
                    (16, Some(6)),
                    (15, None),
                    (16, Some(6)),
                    (15, None),
                ],
            ),
        ];

        for (num, repetitions, expected) in data {
            let mut acc = vec![];
            zlib_rle_encode_nonzero(&mut acc, num, repetitions);
            assert_eq!(acc, expected);
        }
    }
}
