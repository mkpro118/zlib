// Inspired from: https://pyokagan.name/blog/2019-10-18-zlibinflate/

#![allow(clippy::missing_errors_doc)]
#![allow(clippy::missing_panics_doc)]
#![allow(missing_docs)]

static LENGTH_EXTRA_BITS: [usize; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5,
    5, 5, 5, 0,
];
static LENGTH_BASE: [usize; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
    67, 83, 99, 115, 131, 163, 195, 227, 258,
];
static DISTANCE_EXTRA_BITS: [usize; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
    11, 11, 12, 12, 13, 13,
];
static DISTANCE_BASE: [usize; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513,
    769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];
static CODE_LENGTH_CODES_ORDER: [usize; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

#[derive(Debug)]
struct BitReader<'a> {
    mem: &'a [u8],
    pos: usize,
    byte: u8,
    numbits: isize,
}

#[derive(Debug)]
struct HuffmanTreeNode {
    symbol: Option<char>,
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

    fn insert(&mut self, code: usize, length: usize, symbol: char) {
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

    fn decode(&self, reader: &mut BitReader) -> Option<char> {
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

    fn from_bitlen_list(bitlen: &[usize], alphabet: &[char]) -> Self {
        let max_bits = *bitlen.iter().max().unwrap_or(&0);
        let bitlen_count: Vec<usize> = (0..=max_bits)
            .map(|y| {
                if y == 0 {
                    0
                } else {
                    bitlen.iter().filter(|&x| *x == y).count()
                }
            })
            .collect();

        let mut next_code = (1..max_bits).fold(vec![0, 0], |mut acc, bits| {
            acc.push((acc[bits] + bitlen_count[bits]) << 1);
            acc
        });

        bitlen
            .iter()
            .zip(alphabet.iter())
            .filter(|(&bl, _)| bl != 0)
            .fold(Self::new(), |mut tree, (&bl, &c)| {
                tree.insert(next_code[bl], bl, c);
                next_code[bl] += 1;
                tree
            })
    }

    fn decode_trees(reader: &mut BitReader) -> (Self, Self) {
        // The number of Huffman LITeral/length codes
        let hlit = reader.read_bits(5) + 257;

        // The number of Huffman Distance codes
        let hdist = reader.read_bits(5) + 1;

        // The number of Huffman Code LENgth codes
        let hclen = reader.read_bits(4) + 4;

        // Read code lengths for the code length alphabet
        let code_length_tree_bl = (0..hclen).fold([0; 19], |mut acc, i| {
            acc[CODE_LENGTH_CODES_ORDER[i]] = reader.read_bits(3);
            acc
        });

        // Construct code length tree
        let code_length_tree_alphabet: Vec<char> =
            (0u8..19u8).map(|x| x as char).collect();
        let code_length_tree = Self::from_bitlen_list(
            &code_length_tree_bl,
            &code_length_tree_alphabet,
        );

        let mut bitlen: Vec<usize> = vec![];
        let maxlen = hlit + hdist;

        while bitlen.len() < maxlen {
            let Some(sym) = code_length_tree.decode(reader) else {
                panic!("Expected sym, found nothing!");
            };

            let sym = sym as usize;

            match sym {
                0..=15 => bitlen.push(sym),
                16 => {
                    // Copy the previous code length 3-6 times.
                    // The next 2 bits indicate repeat length
                    // ( 0 -> 3, ..., 3 -> 6 )
                    let prev_code_length = *bitlen
                        .last()
                        .expect("Should have at least one element to repeat");
                    let repeat_length = reader.read_bits(2) + 3;
                    bitlen.extend_from_slice(
                        &[prev_code_length].repeat(repeat_length),
                    );
                }
                17 => {
                    // Repeat code length 0 for 3-10 times. (3 bits of length)
                    let repeat_length = reader.read_bits(3) + 3;
                    bitlen.extend_from_slice(&[0].repeat(repeat_length));
                }
                18 => {
                    // Repeat code length 0 for 11-138 times. (7 bits of length)
                    let repeat_length = reader.read_bits(7) + 11;
                    bitlen.extend_from_slice(&[0].repeat(repeat_length));
                }
                _ => panic!("Invalid Symbol!"),
            }
        }

        // Construct trees
        let lit_tree = Self::from_bitlen_list(
            &bitlen[..hlit],
            &literal_length_tree_alphabet(),
        );

        let dist_tree =
            Self::from_bitlen_list(&bitlen[hlit..], &distance_tree_alphabet());

        (lit_tree, dist_tree)
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

fn literal_length_tree_alphabet() -> Vec<char> {
    (0u32..286u32)
        .map(|x| char::from_u32(x).expect("Should be able to make a char"))
        .collect::<Vec<char>>()
}

fn distance_tree_alphabet() -> Vec<char> {
    (0u8..30u8).map(|x| x as char).collect::<Vec<char>>()
}

/// Encodes a code that is `length` bits long into bytes that is conformant
/// with DEFLATE spec
#[allow(dead_code)] // Used in tests
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

/// Decompress block with fixed huffman codes
fn inflate_block_fixed(reader: &mut BitReader, buffer: &mut Vec<u8>) {
    let mut bitlen = vec![8; 144];
    bitlen.extend_from_slice(&[9].repeat(256 - 144));
    bitlen.extend_from_slice(&[7].repeat(280 - 256));
    bitlen.extend_from_slice(&[8].repeat(288 - 280));
    let literal_tree =
        HuffmanTree::from_bitlen_list(&bitlen, &literal_length_tree_alphabet());

    let bitlen = [5; 30];
    let distance_tree =
        HuffmanTree::from_bitlen_list(&bitlen, &distance_tree_alphabet());

    inflate_block_data(reader, &literal_tree, &distance_tree, buffer);
}

/// Decompress block with dynamic huffman codes
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
    fn test_huffman_tree_insertion() {
        let mut tree = HuffmanTree::new();
        {
            tree.insert(0b1, 1, 'B');

            assert!(tree.root.left.is_none());
            assert!(tree.root.right.is_some());
            assert!(tree.root.right.as_ref().unwrap().symbol.is_some());
            assert_eq!(tree.root.right.as_ref().unwrap().symbol.unwrap(), 'B');
        }

        {
            tree.insert(0b01, 2, 'A');

            assert!(tree.root.left.is_some());
            let left = tree.root.left.as_ref().unwrap();

            assert!(left.symbol.is_none());
            assert!(left.right.is_some());
            assert!(left.right.as_ref().unwrap().symbol.is_some());
            assert_eq!(left.right.as_ref().unwrap().symbol.unwrap(), 'A');
        }

        {
            tree.insert(0b000, 3, 'C');
            tree.insert(0b001, 3, 'D');

            assert!(tree.root.left.is_some());
            let left = tree.root.left.as_ref().unwrap();

            assert!(left.left.is_some());
            let left = left.left.as_ref().unwrap();

            // Check 'C'
            assert!(left.left.is_some());
            assert!(left.left.as_ref().unwrap().symbol.is_some());
            assert_eq!(left.left.as_ref().unwrap().symbol.unwrap(), 'C');

            // Check 'D'
            assert!(left.right.is_some());
            assert!(left.right.as_ref().unwrap().symbol.is_some());
            assert_eq!(left.right.as_ref().unwrap().symbol.unwrap(), 'D');
        }
    }

    #[test]
    fn test_huffman_tree_decode_good() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b1, 1, 'B');
        tree.insert(0b01, 2, 'A');
        tree.insert(0b000, 3, 'C');
        tree.insert(0b001, 3, 'D');

        struct TestData(usize, usize, &'static [char]);

        // The underscored are placed to separate the bits as their
        // encoded characters
        let data = [
            TestData(0b1_1_1_01_000_001, 11, &['B', 'B', 'B', 'A', 'C', 'D']),
            TestData(0b000_1_001_01, 9, &['C', 'B', 'D', 'A']),
            TestData(
                0b01_1_001_01_001_000,
                14,
                &['A', 'B', 'D', 'A', 'D', 'C'],
            ),
            TestData(
                0b01_001_1_001_000_1_01_000,
                18,
                &['A', 'D', 'B', 'D', 'C', 'B', 'A', 'C'],
            ),
            TestData(
                0b000_001_01_1_001_01,
                14,
                &['C', 'D', 'A', 'B', 'D', 'A'],
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
        tree.insert(0b1, 1, 'B');
        tree.insert(0b01, 2, 'A');
        tree.insert(0b000, 3, 'C');
        tree.insert(0b001, 3, 'D');

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

    #[test]
    fn test_huffman_tree_from_bitlen_list() {
        let tree =
            HuffmanTree::from_bitlen_list(&[2, 1, 3, 3], &['A', 'B', 'C', 'D']);

        let data = [
            TestData(0b0_0_0_10_110_111, 11, &['B', 'B', 'B', 'A', 'C', 'D']),
            TestData(0b0_10_0_110_111_0, 11, &['B', 'A', 'B', 'C', 'D', 'B']),
            TestData(0b10_0_110_111, 9, &['A', 'B', 'C', 'D']),
        ];

        struct TestData(usize, usize, &'static [char]);

        for TestData(code, length, expected_symbols) in data {
            let bytes = code_to_bytes(code, length);
            let mut reader = BitReader::new(&bytes);

            for &symbol in expected_symbols {
                assert_eq!(tree.decode(&mut reader), Some(symbol));
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
