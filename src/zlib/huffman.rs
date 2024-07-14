//! This module implements Huffman coding for data compression.
//!
//! Huffman coding is a widely used method for lossless data compression. It assigns variable-length codes
//! to characters based on their frequency of occurrence, with more frequent characters getting shorter codes.
//!
//! # Examples
//!
//! ```
//! use mini_git::zlib::huffman::{HuffmanTree, literal_length_tree_alphabet};
//!
//! let bitlen = vec![2, 1, 3, 3];
//! let alphabet = vec!['A', 'B', 'C', 'D'];
//! let tree = HuffmanTree::from_bitlen_list(&bitlen, &alphabet);
//!
//! // You can now use this tree for encoding or decoding
//! ```

use core::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, VecDeque};

use crate::zlib::bitreader::BitReader;
// use crate::zlib::bitwriter::BitWriter;

use crate::zlib::lz77::{LZ77Compressor, LZ77Unit};

/// The order of code length codes used in Huffman tree construction.
static CODE_LENGTH_CODES_ORDER: [usize; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

pub static LENGTH_EXTRA_BITS: [usize; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5,
    5, 5, 5, 0,
];
pub static LENGTH_BASE: [usize; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
    67, 83, 99, 115, 131, 163, 195, 227, 258,
];
pub static DISTANCE_EXTRA_BITS: [usize; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
    11, 11, 12, 12, 13, 13,
];
pub static DISTANCE_BASE: [usize; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513,
    769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];

pub const ZLIB_WINDOW_SIZE: usize = 1 << 15;
pub const ZLIB_MIN_STRING_LENGTH: usize = 3;
pub const ZLIB_MAX_STRING_LENGTH: usize = 258;

/// Represents a node in the Huffman tree.
#[derive(Debug)]
struct HuffmanTreeNode {
    /// The symbol stored in this node, if it's a leaf node.
    symbol: Option<char>,
    /// The left child of this node.
    left: Option<Box<HuffmanTreeNode>>,
    /// The right child of this node.
    right: Option<Box<HuffmanTreeNode>>,
}

struct FreqNode(usize, HuffmanTreeNode);

/// Represents a Huffman tree used for encoding and decoding.
#[derive(Debug)]
#[allow(clippy::module_name_repetitions)]
pub struct HuffmanTree {
    /// The root node of the Huffman tree.
    root: HuffmanTreeNode,

    /// A cache for encoding
    map: Option<HashMap<char, (usize, usize)>>,
}

impl HuffmanTreeNode {
    /// Creates a new `HuffmanTreeNode`.
    pub fn new() -> Self {
        Self {
            symbol: None,
            left: None,
            right: None,
        }
    }

    pub fn from(symbol: char) -> Self {
        Self {
            symbol: Some(symbol),
            ..Self::new()
        }
    }
}

impl PartialEq for FreqNode {
    fn eq(&self, other: &Self) -> bool {
        other.0.eq(&self.0)
    }
}

impl Eq for FreqNode {}

impl Ord for FreqNode {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.cmp(&self.0)
    }
}

impl PartialOrd for FreqNode {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Default for HuffmanTree {
    fn default() -> Self {
        Self::new()
    }
}

impl HuffmanTree {
    /// Creates a new `HuffmanTree`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    ///
    /// let tree = HuffmanTree::new();
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self {
            root: HuffmanTreeNode::new(),
            map: None,
        }
    }

    #[must_use]
    pub fn from_data(data: &[u8]) -> Self {
        let map = data.iter().fold(HashMap::new(), |mut map, &sym| {
            let sym = sym as char;
            *map.entry(sym).or_insert(0) += 1;
            map
        });

        Self::from_freq(map)
    }

    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn from_freq(frequencies: HashMap<char, usize>) -> Self {
        // Convert hashmap to binary heap friendly data structure
        let mut heap = frequencies
            .into_iter()
            .map(|(sym, count)| FreqNode(count, HuffmanTreeNode::from(sym)))
            .collect::<BinaryHeap<FreqNode>>();

        // Build the huffman tree using the Huffman Encoding algorithm
        while heap.len() > 1 {
            let left = heap.pop().expect("Should exist as size is at least 2");
            let right = heap.pop().expect("Should exist as size is at least 2");

            let mut parent = HuffmanTreeNode::new();
            parent.left = Some(Box::new(left.1));
            parent.right = Some(Box::new(right.1));

            let parent = FreqNode(left.0 + right.0, parent);
            heap.push(parent);
        }

        let root = heap.pop().expect("Should have at least one element").1;
        Self {
            root,
            ..Self::default()
        }
    }

    #[must_use]
    #[allow(clippy::missing_panics_doc, clippy::cast_possible_truncation)]
    pub fn from_lz77(data: &[LZ77Unit], lz77: &LZ77Compressor) -> (Self, Self) {
        use LZ77Unit::{Literal, Marker};

        check_lz77(lz77);

        let mut sym_freq = [0usize; 286];
        let mut dist_freq = [0usize; 30];

        let mut count_sym = |byte: usize| sym_freq[byte] += 1;
        let mut count_dist = |byte| dist_freq[byte] += 1;

        for unit in data {
            match unit {
                Literal(byte) => count_sym(*byte as usize),
                Marker(length, distance) => {
                    assert!(*length >= 3, "Length too short!");
                    let length = length - 3;
                    let length_code = get_length_code(length);
                    let distance_code = get_distance_code(*distance);

                    count_sym(length_code);
                    count_dist(distance_code);
                }
            }
        }

        // convert arrays to hashmaps
        let sym_freq = sym_freq.into_iter().enumerate().fold(
            HashMap::new(),
            |mut map, (sym, count)| {
                let sym =
                    char::from_u32(sym as u32).expect("Should convert to char");
                map.insert(sym, count);
                map
            },
        );

        let dist_freq = dist_freq.into_iter().enumerate().fold(
            HashMap::new(),
            |mut map, (sym, count)| {
                let sym =
                    char::from_u32(sym as u32).expect("Should convert to char");
                map.insert(sym, count);
                map
            },
        );

        (Self::from_freq(sym_freq), Self::from_freq(dist_freq))
    }

    /// Constructs a Huffman tree from a list of bit lengths and an alphabet.
    ///
    /// # Arguments
    ///
    /// * `bitlen` - A slice of bit lengths for each symbol.
    /// * `alphabet` - A slice of symbols corresponding to the bit lengths.
    ///
    /// # Returns
    ///
    /// Returns a new `HuffmanTree`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    ///
    /// let bitlen = &[2, 1, 3, 3];
    /// let alphabet = &['A', 'B', 'C', 'D'];
    /// let tree = HuffmanTree::from_bitlen_list(bitlen, alphabet);
    /// ```
    #[must_use]
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

    #[must_use]
    pub fn get_zlib_fixed() -> (Self, Self) {
        let mut bitlen = vec![8; 144];
        bitlen.extend_from_slice(&[9].repeat(256 - 144));
        bitlen.extend_from_slice(&[7].repeat(280 - 256));
        bitlen.extend_from_slice(&[8].repeat(288 - 280));
        let literal_tree = HuffmanTree::from_bitlen_list(
            &bitlen,
            &literal_length_tree_alphabet(),
        );

        let bitlen = [5; 30];
        let distance_tree =
            HuffmanTree::from_bitlen_list(&bitlen, &distance_tree_alphabet());
        (literal_tree, distance_tree)
    }

    /// Inserts a new symbol into the Huffman tree.
    ///
    /// # Arguments
    ///
    /// * `code` - The Huffman code for the symbol.
    /// * `length` - The length of the Huffman code.
    /// * `symbol` - The symbol to insert.
    ///
    /// # Panics
    ///
    /// If creating a new node fails for any reason.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    ///
    /// let mut tree = HuffmanTree::new();
    /// tree.insert(0b1, 1, 'A');
    /// tree.insert(0b01, 2, 'B');
    /// ```
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

    /// Decodes a symbol from the given `BitReader` using this Huffman tree.
    ///
    /// # Arguments
    ///
    /// * `reader` - The `BitReader` to read bits from.
    ///
    /// # Returns
    ///
    /// Returns `Some(char)` if a symbol was successfully decoded,
    /// or `None` if decoding failed.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    /// use mini_git::zlib::bitreader::{BitReader, code_to_bytes};
    ///
    /// let mut tree = HuffmanTree::new();
    /// tree.insert(0b1, 1, 'A');
    /// tree.insert(0b01, 2, 'B');
    ///
    /// let bytes = code_to_bytes(0b101, 3);
    /// let mut reader = BitReader::new(&bytes);
    ///
    /// assert_eq!(tree.decode(&mut reader), Some('A'));
    /// assert_eq!(tree.decode(&mut reader), Some('B'));
    /// ```
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

    /// Decodes two Huffman trees (literal/length and distance) from a `BitReader`.
    ///
    /// # Arguments
    ///
    /// * `reader` - The `BitReader` to read bits from.
    ///
    /// # Returns
    ///
    /// Returns a tuple of two `HuffmanTree`s: (literal/length tree, distance tree).
    ///
    /// # Panics
    ///
    /// If data stream is invalid
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use mini_git::zlib::huffman::HuffmanTree;
    /// use mini_git::zlib::bitreader::BitReader;
    ///
    /// // Example bit sequence, this is not enough to decode trees
    /// let bytes = [0b10101010, 0b01010101];
    /// let mut reader = BitReader::new(&bytes);
    /// let (lit_tree, dist_tree) = HuffmanTree::decode_trees(&mut reader);
    /// ```
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

    #[allow(clippy::missing_panics_doc, clippy::cast_possible_truncation)]
    pub fn assign(&mut self) {
        if self.map.is_none() {
            self.map = Some(HashMap::new());
        }

        let map = self.map.as_mut().expect("Map should exist");

        let mut queue = VecDeque::new();

        queue.push_front((&self.root, 0usize, 0usize));

        while let Some((node, code, length)) = queue.pop_front() {
            if let Some(sym) = node.symbol {
                let code =
                    ((code as u32).reverse_bits() >> (32 - length)) as usize;
                map.insert(sym, (code, length));
            } else {
                if let Some(ref left) = node.left {
                    queue.push_back((left, code << 1, length + 1));
                }

                if let Some(ref right) = node.right {
                    queue.push_back((right, (code << 1) | 1, length + 1));
                }
            }
        }
    }

    #[must_use]
    pub fn encode(&self, symbol: char) -> Option<(usize, usize)> {
        self.map.as_ref()?.get(&symbol).copied()
    }
}

/// Returns the alphabet for the literal/length Huffman tree.
///
/// # Returns
///
/// A `Vec<char>` containing the alphabet for the literal/length tree.
///
/// # Panics
///
/// If conversion from u32 to char fails (It should never fail)
///
/// # Examples
///
/// ```
/// use mini_git::zlib::huffman::literal_length_tree_alphabet;
///
/// let alphabet = literal_length_tree_alphabet();
/// assert_eq!(alphabet.len(), 286);
/// assert_eq!(alphabet[0], '\u{0}');
/// assert_eq!(alphabet[285], '\u{11D}');
/// ```
#[must_use]
pub fn literal_length_tree_alphabet() -> Vec<char> {
    (0u32..286u32)
        .map(|x| char::from_u32(x).expect("Should be able to make a char"))
        .collect::<Vec<char>>()
}

/// Returns the alphabet for the distance Huffman tree.
///
/// # Returns
///
/// A `Vec<char>` containing the alphabet for the distance tree.
///
/// # Examples
///
/// ```
/// use mini_git::zlib::huffman::distance_tree_alphabet;
///
/// let alphabet = distance_tree_alphabet();
/// assert_eq!(alphabet.len(), 30);
/// assert_eq!(alphabet[0], '\u{0}');
/// assert_eq!(alphabet[29], '\u{1D}');
/// ```
#[must_use]
pub fn distance_tree_alphabet() -> Vec<char> {
    (0u8..30u8).map(|x| x as char).collect::<Vec<char>>()
}

fn check_lz77(lz77: &LZ77Compressor) {
    assert_eq!(
        lz77.window_size, ZLIB_WINDOW_SIZE,
        "Incompatible LZ77 window size, required {}, found {}",
        ZLIB_WINDOW_SIZE, lz77.window_size
    );

    assert_eq!(
        lz77.min_match_length, ZLIB_MIN_STRING_LENGTH,
        "Incompatible LZ77 min string length, required {}, found {}",
        ZLIB_MIN_STRING_LENGTH, lz77.min_match_length
    );

    assert_eq!(
        lz77.max_match_length, ZLIB_MAX_STRING_LENGTH,
        "Incompatible LZ77 max string length, required {}, found {}",
        ZLIB_MAX_STRING_LENGTH, lz77.max_match_length
    );
}

#[must_use]
pub fn get_length_code(length: usize) -> usize {
    match LENGTH_BASE.binary_search(&length) {
        Ok(index) => index + 257,
        Err(index) => index + 256,
    }
}

#[must_use]
pub fn get_distance_code(distance: usize) -> usize {
    match DISTANCE_BASE.binary_search(&distance) {
        Ok(index) => index,
        Err(index) => index - 1,
    }
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
