//! This module provides functionality for decompressing DEFLATE-compressed data.
//! Inspired from: [this article](https://pyokagan.name/blog/2019-10-18-zlibinflate/)

use crate::zlib::bitreader::BitReader;
use crate::zlib::huffman::{
    HuffmanTree, DISTANCE_BASE, DISTANCE_EXTRA_BITS, LENGTH_BASE,
    LENGTH_EXTRA_BITS,
};

/// Decompresses DEFLATE-compressed data.
///
/// This function takes a slice of compressed bytes and returns a vector of decompressed bytes.
///
/// # Examples
///
/// ```
/// use mini_git::zlib::decompress;
///
/// let compressed_data = vec![0x78, 0x9C, 0x4B, 0xCE, 0xCF, 0x2D, 0x28, 0x4A,
///     0x2D, 0x2E, 0x4E, 0x4D, 0x01, 0x00, 0x14, 0x81, 0x03, 0x7D];
/// let decompressed_data = decompress(&compressed_data).unwrap();
/// assert_eq!(decompressed_data, b"compressed");
/// ```
///
/// # Errors
///
/// This function will return an error if:
/// - The compression method is not DEFLATE (CM != 8)
/// - The compression info is invalid (CINFO > 7)
/// - The CMF and FLAGS checksum is invalid
/// - A preset dictionary is used (not supported)
/// - The block type is invalid
pub fn decompress(input: &[u8]) -> Result<Vec<u8>, String> {
    let mut reader = BitReader::new(input);

    // CMF is Compression Method and information Field
    let cmf = reader.read_byte();

    // CM is the Compression Method
    let cm = cmf & 0b1111;

    // We only support CM = 8, i.e compressed with DEFLATE
    if cm != 8 {
        return Err(format!("CM = {cm} is not a supported compression method"));
    }

    // CINFO is the Compression INFOrmation
    let cinfo = (cmf >> 4) & 0b1111;

    if cinfo > 7 {
        return Err(format!(
            "Invalid compression info, must be < 7, found {cinfo}"
        ));
    }

    // FLGS is the compression FLAGS
    let flags = reader.read_byte();
    let cmf_flags_checksum = ((cmf as usize) * 256 + (flags as usize)) % 31;

    if cmf_flags_checksum != 0 {
        return Err("CMF + FLAGS checksum failed!".to_owned());
    }

    let fdict = (flags >> 5) & 1;

    if fdict != 0 {
        return Err("Preset dictionaries are not supported".to_owned());
    }

    // Inflate the data
    let inflated = inflate(&mut reader)?;

    // We ignore the checksum
    let _adler32 = reader.read_bytes(4);

    Ok(inflated)
}

/// Inflates DEFLATE-compressed data.
///
/// This function is called by `decompress` to handle the actual inflation process.
///
/// # Errors
///
/// This function will return an error if an invalid block type is encountered.
fn inflate(reader: &mut BitReader) -> Result<Vec<u8>, String> {
    let mut buffer: Vec<u8> = vec![];

    let mut final_block = false;

    while !final_block {
        final_block = match reader.read_bit() {
            0 => false,
            1 => true,
            _ => unreachable!(),
        };

        match reader.read_bits(2) {
            0 => inflate_block_no_compression(reader, &mut buffer),
            1 => inflate_block_fixed(reader, &mut buffer),
            2 => inflate_block_dynamic(reader, &mut buffer),
            _ => return Err("Invalid block type".to_owned()),
        };
    }

    Ok(buffer)
}

/// Inflates an uncompressed block.
///
/// This function is called by `inflate` when an uncompressed block is encountered.
#[allow(unused_variables)]
fn inflate_block_no_compression(reader: &mut BitReader, buffer: &mut Vec<u8>) {
    // Length of the data
    let len = reader.read_bytes(2);

    // One's complement of the length of the data
    let nlen = reader.read_bytes(2);

    buffer.extend((0..len).map(|_| reader.read_byte()));
}

/// Inflates a block compressed with fixed Huffman codes.
///
/// This function is called by `inflate` when a block with fixed Huffman codes is encountered.
fn inflate_block_fixed(reader: &mut BitReader, buffer: &mut Vec<u8>) {
    let (literal_tree, distance_tree) = HuffmanTree::get_zlib_fixed();
    inflate_block_data(reader, &literal_tree, &distance_tree, buffer);
}

/// Inflates a block compressed with dynamic Huffman codes.
///
/// This function is called by `inflate` when a block with dynamic Huffman codes is encountered.
fn inflate_block_dynamic(reader: &mut BitReader, buffer: &mut Vec<u8>) {
    let (literal_length_tree, distance_tree) =
        HuffmanTree::decode_trees(reader);
    inflate_block_data(reader, &literal_length_tree, &distance_tree, buffer);
}

fn inflate_block_data(
    reader: &mut BitReader,
    literal_tree: &HuffmanTree,
    distance_tree: &HuffmanTree,
    buffer: &mut Vec<u8>,
) {
    loop {
        let Some(sym) = literal_tree.decode(reader) else {
            return;
        };

        let sym_as_int = sym as usize;

        match sym_as_int {
            0..=255 => buffer.push(sym as u8),
            256 => return,
            257..=285 => {
                let idx = sym_as_int - 257;

                let length =
                    reader.read_bits(LENGTH_EXTRA_BITS[idx]) + LENGTH_BASE[idx];

                let Some(distance) = distance_tree.decode(reader) else {
                    panic!("Failed to read backwards distance!");
                };

                let idx = distance as usize;

                let dist = reader.read_bits(DISTANCE_EXTRA_BITS[idx])
                    + DISTANCE_BASE[idx];

                for _ in 0..length {
                    buffer.push(buffer[buffer.len() - dist]);
                }
            }
            _ => panic!("Invalid decoded value"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zlib::bitreader::code_to_bytes;

    #[test]
    fn test_decompress_invalid_cm() {
        // Set CInfo correctly
        let initial = 0b0111_0000u8;
        for i in 0u8..8u8 {
            let input = [initial | i];
            let res = decompress(&input);
            assert!(&res.is_err());
        }

        for i in 9u8..=15u8 {
            let input = [initial | i];
            let res = decompress(&input);
            assert!(&res.is_err());
        }
    }

    #[test]
    fn test_decompress_invalid_cinfo() {
        // Set CM correctly
        let initial = 0b1000u8;
        for i in 8u8..=15u8 {
            let input = [initial | (i << 4)];
            let res = decompress(&input);
            assert!(res.is_err());
        }
    }

    #[test]
    fn test_decompress_checksum() {
        // Need data to be at least 11 bytes
        // 2 -> Metadata
        // 1 -> Block Information
        // 2 + 2 -> Block Length + Block Length One's Complement
        // 4 bytes for Adler checksum
        // 2 + 1 + 2 + 2 + 4 = 11
        let mut input: [u8; 11] = [0; 11];

        // 0111 -> CINFO, 1110 -> CM
        input[0] = 0b0111_1000;

        // Set the very first data block as final.
        input[2] = 0b0000_0001;

        let known_cm_value = (input[0] as usize) * 256;

        // Check all possible u8 values
        for mut i in u8::MIN..u8::MAX {
            // Need to set the FDICT bit to 0, yes this wastes 32 iterations
            // but its not noticeable, plus this is a test
            i &= 0b1101_1111;
            input[1] = i;
            let checksum = known_cm_value + (i as usize);
            let res = decompress(&input);

            // Ensure the checksum is not divisible by 31
            // If it is, skip that iteration
            if checksum % 31 == 0 {
                assert!(res.is_ok());
            } else {
                assert!(res.is_err());
            }
        }
    }

    #[test]
    fn test_decompress_fdict_set() {
        // Need data to be at least 7 bytes for adler32 checksum and final block
        let mut input: [u8; 7] = [0; 7];

        // 0111 -> CINFO, 1110 -> CM
        input[0] = 0b0111_1000;

        // Set the very first data block as final.
        input[2] = 0b0000_0001;

        let known_cm_value = (input[0] as usize) * 256;

        // Check all possible u8 values
        for mut i in u8::MIN..u8::MAX {
            // Need to set the FDICT bit to 1 to force an error
            i |= 0b0010_0000;
            input[1] = i;
            let checksum = known_cm_value + (i as usize);
            if checksum % 31 != 0 {
                continue;
            }

            let res = decompress(&input);
            assert!(res.is_err());
        }
    }

    #[test]
    fn test_inflate_block_no_compression() {
        struct TestData(&'static [u8]);
        let data = vec![
            TestData(b"\x0c\x00\xf3\xffHello World!"),
            TestData(b"\x05\x00\xfa\xffRust!"),
            TestData(b"\x1d\x00\xe2\xffInflate Block No Compression!"),
            TestData(
                b"\x2c\x00\xd3\xffBeneath the starlit sky, dreams take flight.",
            ),
            TestData(
                b"\x2b\x00\xd4\xffWhispers of the wind carry ancient secrets.",
            ),
            TestData(
                b"\x2b\x00\xd4\xffIn the heart of the forest, magic is alive.",
            ),
            TestData(
                b"\x28\x00\xd7\xffTime flows like a river, never stopping.",
            ),
            TestData(
                b"\x2b\x00\xd4\xffEchoes of laughter fill the empty hallways.",
            ),
        ];

        for TestData(compressed) in data {
            // First 4 bytes are metadata, rest is the decompressed string
            let decompressed = match std::str::from_utf8(&compressed[4..]) {
                Ok(v) => v,
                Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
            };

            let mut reader = BitReader::new(compressed);
            let mut buffer: Vec<u8> = vec![];

            inflate_block_no_compression(&mut reader, &mut buffer);

            let s = match std::str::from_utf8(&buffer) {
                Ok(v) => v,
                Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
            };

            assert_eq!(decompressed, s);
        }
    }

    #[test]
    fn test_code_to_bytes() {
        struct TestData(usize, usize, &'static [u8]);
        let data = [
            TestData(0b111_0100_0001, 11, &[1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1]),
            TestData(0b1010_1010, 8, &[1, 0, 1, 0, 1, 0, 1, 0]),
            TestData(0b11_0010, 6, &[1, 1, 0, 0, 1, 0]),
        ];

        for TestData(code, length, expected_bits) in data {
            let bytes = code_to_bytes(code, length);
            let mut reader = BitReader::new(&bytes);

            for &bit in expected_bits {
                assert_eq!(reader.read_bit(), bit);
            }
        }
    }

    #[test]
    fn test_inflate_block_data_end_marker() {
        let mut literal_tree = HuffmanTree::new();
        let distance_tree = HuffmanTree::new();
        let mut buffer: Vec<u8> = vec![];

        let (code, length) = (0b1, 1);
        literal_tree.insert(code, length, '\u{100}');
        let bytes = code_to_bytes(code, length);
        let mut reader = BitReader::new(&bytes);

        inflate_block_data(
            &mut reader,
            &literal_tree,
            &distance_tree,
            &mut buffer,
        );

        assert_eq!(buffer.len(), 0);
    }

    #[test]
    fn test_inflate_block_data_literals() {
        let mut literal_tree = HuffmanTree::new();
        let distance_tree = HuffmanTree::new();
        let mut buffer: Vec<u8> = vec![];

        literal_tree.insert(0b10, 2, 'A');
        literal_tree.insert(0b0, 1, 'B');
        literal_tree.insert(0b110, 3, 'C');

        // End marker
        literal_tree.insert(0b111, 3, '\u{100}');

        let (code, length) = (0b10_0_10_110_111, 11);
        let bytes = code_to_bytes(code, length);
        let mut reader = BitReader::new(&bytes);

        inflate_block_data(
            &mut reader,
            &literal_tree,
            &distance_tree,
            &mut buffer,
        );

        assert_eq!(buffer.len(), 4);
        assert_eq!(buffer, &[b'A', b'B', b'A', b'C']);
    }

    #[test]
    fn test_inflate_block_data_distance() {
        let mut literal_tree = HuffmanTree::new();
        let mut distance_tree = HuffmanTree::new();

        literal_tree.insert(0b10, 2, 'A');
        literal_tree.insert(0b0, 1, 'B');

        // Insert 257
        literal_tree.insert(0b110, 3, '\u{101}');

        // End marker
        literal_tree.insert(0b111, 3, '\u{100}');

        // Simply use the smallest possible value
        distance_tree.insert(0b10, 2, 0 as char);
        distance_tree.insert(0b0, 1, 1 as char);
        distance_tree.insert(0b110, 3, 2 as char);

        struct TestData(usize, usize, usize, &'static [u8]);

        let data = [
            // A B A 257 0 *END*
            // This should repeat the last A 3 more times, overall, "ABAAAA"
            TestData(
                0b10_0_10_110_10_111,
                13,
                6,
                &[b'A', b'B', b'A', b'A', b'A', b'A'],
            ),
            // A B 257 1 *END*
            // This should repeat the "AB" once, and end with an "A",
            // overall, "ABABA"
            TestData(0b10_0_110_0_111, 10, 5, &[b'A', b'B', b'A', b'B', b'A']),
            // A B A 257 2 *END*
            // This should repeat the "ABA" once, overall, "ABAABA"
            TestData(
                0b10_0_10_110_110_111,
                14,
                6,
                &[b'A', b'B', b'A', b'A', b'B', b'A'],
            ),
        ];

        for TestData(code, length, exp_len, exp_seq) in data {
            let bytes = code_to_bytes(code, length);
            let mut reader = BitReader::new(&bytes);
            let mut buffer: Vec<u8> = vec![];

            inflate_block_data(
                &mut reader,
                &literal_tree,
                &distance_tree,
                &mut buffer,
            );

            assert_eq!(buffer.len(), exp_len);
            assert_eq!(buffer, exp_seq);
        }
    }
}
