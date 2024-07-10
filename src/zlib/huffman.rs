use crate::zlib::bitreader::BitReader;

static CODE_LENGTH_CODES_ORDER: [usize; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

#[derive(Debug)]
struct HuffmanTreeNode {
    symbol: Option<char>,
    left: Option<Box<HuffmanTreeNode>>,
    right: Option<Box<HuffmanTreeNode>>,
}

#[derive(Debug)]
#[allow(clippy::module_name_repetitions)]
pub struct HuffmanTree {
    root: HuffmanTreeNode,
}

impl HuffmanTreeNode {
    pub fn new() -> Self {
        Self {
            symbol: None,
            left: None,
            right: None,
        }
    }
}

impl HuffmanTree {
    pub fn new() -> Self {
        Self {
            root: HuffmanTreeNode::new(),
        }
    }

    pub fn insert(&mut self, code: usize, length: usize, symbol: char) {
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

    pub fn decode(&self, reader: &mut BitReader) -> Option<char> {
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

    pub fn from_bitlen_list(bitlen: &[usize], alphabet: &[char]) -> Self {
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

    pub fn decode_trees(reader: &mut BitReader) -> (Self, Self) {
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

pub fn literal_length_tree_alphabet() -> Vec<char> {
    (0u32..286u32)
        .map(|x| char::from_u32(x).expect("Should be able to make a char"))
        .collect::<Vec<char>>()
}

pub fn distance_tree_alphabet() -> Vec<char> {
    (0u8..30u8).map(|x| x as char).collect::<Vec<char>>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zlib::bitreader::code_to_bytes;

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
}
