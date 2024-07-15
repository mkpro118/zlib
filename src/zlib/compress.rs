#![allow(clippy::missing_errors_doc, clippy::missing_panics_doc)]

use crate::zlib::adler::adler32;
use crate::zlib::bitwriter::BitWriter;
use crate::zlib::huffman::{
    get_distance_code, get_length_code, HuffmanTree, CODE_LENGTH_CODES_ORDER,
    DISTANCE_BASE, DISTANCE_EXTRA_BITS, LENGTH_BASE, LENGTH_EXTRA_BITS,
    ZLIB_MAX_STRING_LENGTH, ZLIB_MIN_STRING_LENGTH, ZLIB_WINDOW_SIZE,
};
use crate::zlib::lz77::{LZ77Compressor, LZ77Unit};
use LZ77Unit::{Literal, Marker};

const SIXTEEN_KB: usize = 16 * 1024;

#[derive(Debug)]
pub enum Strategy {
    Auto,
    Dynamic,
    Fixed,
    Raw,
}

#[derive(Debug)]
enum RunLengthEncoding {
    Once(usize),
    Repeat(usize, usize),
}

#[allow(clippy::unusual_byte_groupings, clippy::cast_possible_truncation)]
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

    for unit in compressor.compress(data) {
        match unit {
            Literal(byte) => {
                literal_writer(&length_tree, writer, char::from(byte));
            }
            Marker(length, distance) => {
                length_writer(&length_tree, writer, length);
                distance_writer(&distance_tree, writer, distance);
            }
        }
    }

    literal_writer(&length_tree, writer, '\u{100}');
}

#[allow(clippy::cast_possible_truncation)]
fn compress_dynamic(writer: &mut BitWriter, data: &[u8]) {
    // BFINAL = 1, we only write one massive block
    writer.write_bit(0b1);
    // BTYPE = 10, Dynamic Huffman Codes
    writer.write_bits(0b10, 2);

    let compressor = get_zlib_compressor();
    let compressed = compressor.compress(data);

    let (mut ltree, mut dtree) =
        HuffmanTree::from_lz77(&compressed, &compressor);

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
    let (ltree, dtree) = (ltree.to_canonical(), dtree.to_canonical());

    let ltree_encodings = ltree
        .encodings()
        .expect("Should exist, codes have been assigned");
    let dtree_encodings = dtree
        .encodings()
        .expect("Should exist, codes have been assigned");

    let ltree_max_value = *ltree_encodings
        .keys()
        .max()
        .filter(|&max| *max > '\u{100}')
        .unwrap_or(&'\u{101}');
    let dtree_max_value = *dtree_encodings.keys().max().unwrap_or(&(1 as char));

    let ltree_codelengths = ((0 as char)..=ltree_max_value)
        .map(|c| ltree.encode(c).map_or(0, |(_, len)| len))
        .collect::<Vec<usize>>();

    let dtree_codelengths = ((0 as char)..=dtree_max_value)
        .map(|c| dtree.encode(c).map_or(0, |(_, len)| len))
        .collect::<Vec<usize>>();

    let ltree_run_length = run_length_encode(&ltree_codelengths);
    let ltree_run_length = rle_to_zlib_codes(&ltree_run_length);
    let dtree_run_length = run_length_encode(&dtree_codelengths);
    let dtree_run_length = rle_to_zlib_codes(&dtree_run_length);

    let combined = [ltree_run_length, dtree_run_length].concat();
    let codes_only = combined
        .iter()
        .map(|&(code, _)| code as u8)
        .collect::<Vec<u8>>();

    let mut code_tree = HuffmanTree::from_data(&codes_only);
    code_tree.assign();
    let code_tree = code_tree.to_canonical();

    let cmax = code_tree.max_code_len();
    assert!(
        cmax <= 7,
        "The Code code lengths are too long, found {cmax}"
    );

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
    let hcodes = &hcodes[..(hcodes.len() - trailing_zeros)];

    assert!(hcodes.len() >= 4, "Should be at least 4");

    // Now we have all the data to write out the header
    let hlit = ltree_codelengths.len() - 257;
    let hdist = dtree_codelengths.len() - 1;
    let hclen = hcodes.len() - 4;

    writer.write_bits(hlit, 5);
    writer.write_bits(hdist, 5);
    writer.write_bits(hclen, 4);

    // Write out the (hclen + 4) * 3 bits of code lengths for the code length
    // alphabet
    for &hcode in hcodes {
        writer.write_bits(hcode, 3);
    }

    // Write out the encoded huffman literal/length and distance trees
    for (codelength, extra) in combined {
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

    // the easy part, write out the data
    for unit in compressed {
        match unit {
            Literal(byte) => {
                literal_writer(&ltree, writer, char::from(byte));
            }
            Marker(length, distance) => {
                length_writer(&ltree, writer, length);
                distance_writer(&dtree, writer, distance);
            }
        }
    }

    literal_writer(&ltree, writer, '\u{100}');
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

fn get_zlib_compressor() -> LZ77Compressor {
    let mut compressor = LZ77Compressor::with_window_size(ZLIB_WINDOW_SIZE);
    compressor.min_match_length = ZLIB_MIN_STRING_LENGTH;
    compressor.max_match_length = ZLIB_MAX_STRING_LENGTH;
    compressor
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
    use RunLengthEncoding::{Once, Repeat};
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

    rle.iter().fold(vec![], |mut acc, encoded| {
        match encoded {
            Once(num) => acc.push((*num, None)),
            Repeat(num, mut repetitions) => {
                let num = *num;
                if num == 0 {
                    while repetitions > 0 {
                        match repetitions {
                            SHORT_ZERO_MIN..=SHORT_ZERO_MAX => {
                                acc.push((SHORT_ZERO_CODE, Some(repetitions)));
                                break;
                            }
                            LONG_ZERO_MIN.. => {
                                let current_count =
                                    if repetitions > LONG_ZERO_MAX {
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
                                acc.extend_from_slice(
                                    &[(0, None)].repeat(repetitions),
                                );
                                break;
                            }
                        }
                    }
                } else {
                    while repetitions > 0 {
                        match repetitions {
                            ..=PREVIOUS_MIN => {
                                acc.extend_from_slice(
                                    &[(num, None)].repeat(repetitions),
                                );
                                break;
                            }
                            PREVIOUS_MIN_RANGE.. => {
                                acc.push((num, None));
                                repetitions -= 1;
                                let current_count =
                                    if repetitions > PREVIOUS_MAX {
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
            }
        };
        acc
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zlib::decompress;
    use std::{
        fs,
        path::{Path, PathBuf},
    };

    fn walkdir(top: &Path) -> Vec<PathBuf> {
        assert!(top.is_dir(), "Top is not a directory (top = {top:?})");
        top.read_dir()
            .expect("Should read the dir")
            .filter(|e| e.is_ok())
            .map(|e| e.unwrap())
            .map(|e| e.path())
            .filter(|path| {
                path.file_stem().is_some_and(|stem| {
                    !stem.to_str().is_some_and(|x| x.starts_with("."))
                })
            })
            .fold(vec![], |mut paths, entry| {
                if entry.is_file() {
                    paths.push(entry);
                } else {
                    paths.extend_from_slice(&walkdir(&entry));
                }
                paths
            })
    }

    #[test]
    fn test_fixed_on_license() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let license = root.join("LICENSE");
        let bytes = fs::read(license).expect("Read file!");

        let compressed = compress(&bytes, &Strategy::Fixed);
        let decompressed =
            decompress(&compressed).expect("Correct decompression");

        assert_eq!(bytes, decompressed);
    }

    #[test]
    fn test_fixed_on_source_files() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let src = root.join("src");

        for file in walkdir(&src) {
            let bytes = fs::read(file).expect("Read file!");

            let compressed = compress(&bytes, &Strategy::Fixed);
            let decompressed =
                decompress(&compressed).expect("Correct decompression");

            assert_eq!(bytes, decompressed);
        }
    }

    #[test]
    fn test_dynamic_on_license() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let license = root.join("LICENSE");
        let bytes = fs::read(license).expect("Read file!");

        let compressed = compress(&bytes, &Strategy::Dynamic);
        let decompressed =
            decompress(&compressed).expect("Correct decompression");

        assert_eq!(bytes, decompressed);
    }

    #[test]
    fn test_dynamic_on_source_files() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let src = root.join("src");

        for file in walkdir(&src) {
            let bytes = fs::read(file).expect("Read file!");

            let compressed = compress(&bytes, &Strategy::Dynamic);
            let decompressed =
                decompress(&compressed).expect("Correct decompression");

            assert_eq!(bytes, decompressed);
        }
    }
}
