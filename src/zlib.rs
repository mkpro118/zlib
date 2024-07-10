// Inspired from: https://pyokagan.name/blog/2019-10-18-zlibinflate/

#![allow(dead_code)]
#![allow(clippy::missing_errors_doc)]
#![allow(clippy::missing_panics_doc)]
#![allow(missing_docs)]

#[derive(Debug)]
struct BitReader<'a> {
    mem: &'a [u8],
    pos: usize,
    byte: u8,
    numbits: isize,
}

#[derive(Debug)]
struct HuffmanTreeNode {
    symbol: Option<u8>,
    left: Option<Box<HuffmanTreeNode>>,
    right: Option<Box<HuffmanTreeNode>>,
}

#[derive(Debug)]
struct HuffmanTree {
    root: HuffmanTreeNode,
}

impl HuffmanTreeNode {
    fn new() -> Self {
        Self {
            symbol: None,
            left: None,
            right: None,
        }
    }
}

impl HuffmanTree {
    fn new() -> Self {
        Self {
            root: HuffmanTreeNode::new(),
        }
    }

    fn insert(&mut self, code: usize, length: usize, symbol: u8) {
        let mut node = &mut self.root;

        for i in (0..length).rev() {
            // This complicated expression essentially finds the next node
            // in the huffman tree, given a particular bit
            node = if code & (1 << i) == 0 {
                // Bit is zero, left exists
                if let Some(ref mut next_node) = node.left {
                    next_node
                }
                // Bit is zero, left does not exist
                else {
                    // So create it
                    node.left = Some(Box::new(HuffmanTreeNode::new()));
                    node.left.as_mut().expect("Should exist as we just made it")
                }
            }
            // Bit is one, right exists
            else if let Some(ref mut next_node) = node.right {
                next_node
            }
            // Bit is one, right does not exist
            else {
                // So create it
                node.right = Some(Box::new(HuffmanTreeNode::new()));
                node.right
                    .as_mut()
                    .expect("Should exist as we just made it")
            }
        }

        node.symbol = Some(symbol);
    }

    fn decode(&self, reader: &mut BitReader) -> Option<u8> {
        let mut node = &self.root;

        while node.left.is_some() || node.right.is_some() {
            node = match reader.read_bit() {
                0 => {
                    if let Some(next) = &node.left {
                        next
                    } else {
                        return None;
                    }
                }
                1 => {
                    if let Some(next) = &node.right {
                        next
                    } else {
                        return None;
                    }
                }
                _ => unreachable!(),
            }
        }

        node.symbol
    }
}

impl<'a> BitReader<'a> {
    pub fn new(mem: &'a [u8]) -> Self {
        Self {
            mem,
            pos: 0,
            byte: 0,
            numbits: 0,
        }
    }

    fn read_byte(&mut self) -> u8 {
        self.numbits = 0;
        let b = self.mem[self.pos];
        self.pos += 1;
        b
    }

    fn read_bit(&mut self) -> u8 {
        if self.numbits <= 0 {
            self.byte = self.read_byte();
            self.numbits = 8;
        }

        self.numbits -= 1;

        // shift bit out of byte
        let bit = self.byte & 1;
        self.byte >>= 1;

        bit
    }

    fn read_bits(&mut self, n: usize) -> usize {
        let mut out = 0usize;

        for i in 0..n {
            out |= (self.read_bit() as usize) << i;
        }

        out
    }

    fn read_bytes(&mut self, n: usize) -> usize {
        // read bytes as an integer in little-endian
        let mut out = 0usize;

        for i in 0..n {
            out |= (self.read_byte() as usize) << (8 * i);
        }

        out
    }
}

/// Encodes a code that is `length` bits long into bytes that is conformant
/// with DEFLATE spec
fn code_to_bytes(code: usize, length: usize) -> Vec<u8> {
    let mut bytes: Vec<u8> = vec![0u8];

    let mut numbits = 0;

    for i in (0..length).rev() {
        if numbits >= 8 {
            bytes.push(0u8);
            numbits = 0;
        }

        let Some(last) = bytes.last_mut() else {
            unreachable!();
        };

        *last |= u8::from(code & (1 << i) != 0) << numbits;
        numbits += 1;
    }

    bytes
}

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

#[allow(unused_variables)]
fn inflate_block_no_compression(reader: &mut BitReader, buffer: &mut Vec<u8>) {
    // Length of the data
    let len = reader.read_bytes(2);

    // One's complement of the length of the data
    let nlen = reader.read_bytes(2);

    buffer.extend((0..len).map(|_| reader.read_byte()));
}

#[allow(unused_variables)]
fn inflate_block_fixed(reader: &mut BitReader, buffer: &mut Vec<u8>) {}

#[allow(unused_variables)]
fn inflate_block_dynamic(reader: &mut BitReader, buffer: &mut Vec<u8>) {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_bit() {
        let mut reader = BitReader::new(b"\x9d");
        let expected_bits: [u8; 8] = [1, 0, 1, 1, 1, 0, 0, 1];
        for &bit in &expected_bits {
            assert_eq!(reader.read_bit(), bit);
        }
    }

    #[test]
    fn test_read_bits() {
        let mut reader = BitReader::new(b"\x2b\x01");
        assert_eq!(reader.read_bits(9), 299);
    }

    #[test]
    fn test_read_byte() {
        let mut reader = BitReader::new(b"\x66\x36");
        assert_eq!(reader.read_bytes(2), 13926);
    }

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
    #[ignore = "This test will fail as long as inflation is not fully implemented. This has been tested in earlier revisions. Ignore while Inflation if a WIP"]
    fn test_decompress_checksum() {
        // Need data to be at least 7 bytes for adler32 checksum and final block
        let mut input: [u8; 7] = [0; 7];

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
            TestData(b"\x2c\x00\xd3\xffBeneath the starlit sky, dreams take flight."),
            TestData(b"\x2b\x00\xd4\xffWhispers of the wind carry ancient secrets."),
            TestData(b"\x2b\x00\xd4\xffIn the heart of the forest, magic is alive."),
            TestData(b"\x28\x00\xd7\xffTime flows like a river, never stopping."),
            TestData(b"\x2b\x00\xd4\xffEchoes of laughter fill the empty hallways."),
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
    fn test_huffman_tree_insertion() {
        let mut tree = HuffmanTree::new();
        {
            tree.insert(0b1, 1, b'B');

            assert!(tree.root.left.is_none());
            assert!(tree.root.right.is_some());
            assert!(tree.root.right.as_ref().unwrap().symbol.is_some());
            assert_eq!(tree.root.right.as_ref().unwrap().symbol.unwrap(), b'B');
        }

        {
            tree.insert(0b01, 2, b'A');

            assert!(tree.root.left.is_some());
            let left = tree.root.left.as_ref().unwrap();

            assert!(left.symbol.is_none());
            assert!(left.right.is_some());
            assert!(left.right.as_ref().unwrap().symbol.is_some());
            assert_eq!(left.right.as_ref().unwrap().symbol.unwrap(), b'A');
        }

        {
            tree.insert(0b000, 3, b'C');
            tree.insert(0b001, 3, b'D');

            assert!(tree.root.left.is_some());
            let left = tree.root.left.as_ref().unwrap();

            assert!(left.left.is_some());
            let left = left.left.as_ref().unwrap();

            // Check 'C'
            assert!(left.left.is_some());
            assert!(left.left.as_ref().unwrap().symbol.is_some());
            assert_eq!(left.left.as_ref().unwrap().symbol.unwrap(), b'C');

            // Check 'D'
            assert!(left.right.is_some());
            assert!(left.right.as_ref().unwrap().symbol.is_some());
            assert_eq!(left.right.as_ref().unwrap().symbol.unwrap(), b'D');
        }
    }

    #[test]
    fn test_huffman_tree_decode_good() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b1, 1, b'B');
        tree.insert(0b01, 2, b'A');
        tree.insert(0b000, 3, b'C');
        tree.insert(0b001, 3, b'D');

        struct TestData(usize, usize, &'static [u8]);

        // The underscored are placed to separate the bits as their
        // encoded characters
        let data = [
            TestData(
                0b1_1_1_01_000_001,
                11,
                &[b'B', b'B', b'B', b'A', b'C', b'D'],
            ),
            TestData(0b000_1_001_01, 9, &[b'C', b'B', b'D', b'A']),
            TestData(
                0b01_1_001_01_001_000,
                14,
                &[b'A', b'B', b'D', b'A', b'D', b'C'],
            ),
            TestData(
                0b01_001_1_001_000_1_01_000,
                18,
                &[b'A', b'D', b'B', b'D', b'C', b'B', b'A', b'C'],
            ),
            TestData(
                0b000_001_01_1_001_01,
                14,
                &[b'C', b'D', b'A', b'B', b'D', b'A'],
            ),
        ];

        for TestData(code, length, expected_symbols) in data {
            let bytes = code_to_bytes(code, length);
            let mut reader = BitReader::new(&bytes);

            for &symbol in expected_symbols {
                assert_eq!(tree.decode(&mut reader), Some(symbol));
            }
        }
    }

    #[test]
    fn test_huffman_tree_decode_bad() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b1, 1, b'B');
        tree.insert(0b01, 2, b'A');
        tree.insert(0b000, 3, b'C');
        tree.insert(0b001, 3, b'D');

        struct TestData(usize, usize, usize);

        // The underscored are placed to separate the bits as their
        // encoded characters
        let data = [
            TestData(0b01_001_1_0, 7, 3),
            TestData(0b1_000_000_000_01_01_0, 15, 6),
        ];

        for TestData(code, length, n_good_iters) in data {
            let bytes = code_to_bytes(code, length);

            let res = std::panic::catch_unwind(|| {
                let mut reader = BitReader::new(&bytes);

                // Run through the good iterations
                for _ in 0..n_good_iters {
                    let x = tree.decode(&mut reader);
                    assert!(x.is_some());
                }

                // This should cause a panic
                tree.decode(&mut reader);
            });

            assert!(res.is_err());
        }
    }
}
