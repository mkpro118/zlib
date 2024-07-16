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

use crate::zlib::lz77::{LZ77Compressor, LZ77Unit};

/// The order of code length codes used in Huffman tree construction.
pub static CODE_LENGTH_CODES_ORDER: [usize; 19] = [
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

#[derive(Debug)]
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

    /// Creates a new `HuffmanTreeNode` with the given symbol.
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
        let cmp = other.0.cmp(&self.0);
        match cmp {
            Ordering::Equal => match (self.1.symbol, other.1.symbol) {
                (Some(sym_self), Some(sym_other)) => sym_other.cmp(&sym_self),
                _ => cmp,
            },
            _ => cmp,
        }
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

    /// Creates a `HuffmanTree` from the given byte data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    ///
    /// let data = b"hello world";
    /// let tree = HuffmanTree::from_data(data);
    /// ```
    #[must_use]
    pub fn from_data(data: &[u8]) -> Self {
        let map = data.iter().fold(HashMap::new(), |mut map, &sym| {
            let sym = sym as char;
            *map.entry(sym).or_insert(0) += 1;
            map
        });

        Self::from_freq(map)
    }

    /// Creates a `HuffmanTree` from a frequency map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use mini_git::zlib::huffman::HuffmanTree;
    ///
    /// let mut frequencies = HashMap::new();
    /// frequencies.insert('a', 3);
    /// frequencies.insert('b', 2);
    /// frequencies.insert('c', 1);
    /// let tree = HuffmanTree::from_freq(frequencies);
    /// ```
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn from_freq(frequencies: HashMap<char, usize>) -> Self {
        // Convert hashmap to binary heap friendly data structure
        let mut heap = frequencies
            .into_iter()
            .filter(|(_, count)| *count > 0)
            .map(|(sym, count)| FreqNode(count, HuffmanTreeNode::from(sym)))
            .collect::<BinaryHeap<FreqNode>>();

        // In case the given frequencies were all zero
        if heap.is_empty() {
            return Self::default();
        }

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

    /// Creates two Huffman trees (literal/length and distance) from LZ77-compressed data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::{huffman::*, lz77::LZ77Compressor};
    ///
    /// let data = b"abc".repeat(100);
    ///
    /// // Setup the compressor to be zlib compatible
    /// let mut lz77_compressor = LZ77Compressor::with_window_size(ZLIB_WINDOW_SIZE);
    /// lz77_compressor.min_match_length = ZLIB_MIN_STRING_LENGTH;
    /// lz77_compressor.max_match_length = ZLIB_MAX_STRING_LENGTH;
    ///
    /// let lz77_data = lz77_compressor.compress(&data);
    ///
    /// let (lit_tree, dist_tree) = HuffmanTree::from_lz77(&lz77_data, &lz77_compressor);
    /// ```
    #[must_use]
    #[allow(clippy::missing_panics_doc, clippy::cast_possible_truncation)]
    pub fn from_lz77(data: &[LZ77Unit], lz77: &LZ77Compressor) -> (Self, Self) {
        use LZ77Unit::{Literal, Marker};

        check_lz77(lz77);

        let mut sym_freq = [0usize; 286];
        let mut dist_freq = [0usize; 30];

        let mut count_sym = |byte| sym_freq[byte] += 1;
        let mut count_dist = |byte| dist_freq[byte] += 1;

        for unit in data {
            match unit {
                Literal(byte) => count_sym(*byte as usize),
                Marker(length, distance) => {
                    assert!(*length >= 3, "Length too short!");
                    let length_code = get_length_code(*length);
                    let distance_code = get_distance_code(*distance);

                    count_sym(length_code);
                    count_dist(distance_code);
                }
            }
        }

        // Ensure terminating character is encoded
        sym_freq[256] = 1.max(sym_freq[256]);

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

    /// Constructs Huffman trees for the `ZLib` fixed compression strategy.
    ///
    /// # Returns
    /// A tuple of two trees, the first is the literal/length tree
    /// the second is the distance tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    ///
    /// let (lit_tree, dist_tree) = HuffmanTree::get_zlib_fixed();
    /// ```
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

    /// Returns the number of codes in the Huffman tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    ///
    /// let tree = HuffmanTree::new();
    /// let n_codes = tree.n_codes();
    ///
    /// assert_eq!(n_codes, 0); // Should be zero for an empty tree
    /// ```
    #[must_use]
    pub fn n_codes(&self) -> usize {
        self.map.as_ref().map_or(0, HashMap::len)
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

    /// Assigns codes to symbols in the Huffman tree.
    ///
    /// This function is primarily used for encoding, and delays actually
    /// assigning codes until necessary, as the encoding is not required for
    /// decoding.
    ///
    /// See [`HuffmanTree::encode`]
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    ///
    /// let data = b"abc".repeat(5);
    ///
    /// // This creates a tree, and can be used for decoding, but not encoding.
    /// let mut tree = HuffmanTree::from_data(&data);
    ///
    /// // Assign codes to the symbols
    /// tree.assign();
    ///
    /// // Now the tree can used for encoding.
    /// assert_eq!(Some((1, 2)), tree.encode('a'));
    /// ```
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

    /// Encodes a symbol using the Huffman tree.
    ///
    /// See [`HuffmanTree::assign`]
    ///
    /// # Examples
    ///
    /// ```
    /// // Setup is the same as HuffmanTree::assign
    /// # use mini_git::zlib::huffman::HuffmanTree;
    /// #
    /// # let data = b"abc".repeat(5);
    /// #
    /// # // This creates a tree, and can be used for decoding, but not encoding.
    /// # let mut tree = HuffmanTree::from_data(&data);
    /// #
    /// # // Assign codes to the symbols
    /// # tree.assign();
    /// let encoded = tree.encode('a');
    /// assert_eq!(Some((1, 2)), encoded);
    /// ```
    #[must_use]
    pub fn encode(&self, symbol: char) -> Option<(usize, usize)> {
        self.map.as_ref()?.get(&symbol).copied()
    }

    /// Returns a reference to the internal map of encodings.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    /// let tree = HuffmanTree::new();
    ///
    /// // Add some nodes to the tree and assign codes
    ///
    /// let encodings = tree.encodings();
    /// println!("{encodings:?}");
    /// ```
    #[must_use]
    pub fn encodings(&self) -> Option<&HashMap<char, (usize, usize)>> {
        self.map.as_ref()
    }

    /// Converts the current Huffman tree to its canonical form.
    /// This form is compatible with Zlib compression
    ///
    /// This operation requires codes to be assigned, see [`HuffmanTree::assign`]
    ///
    /// # Panics
    ///
    /// This operation will panic if `tree.assign()` has not yet been called.
    /// This implementation of converting codes to canonical form requires
    /// the bit length of each symbol's code, which is created when `assign`
    /// is called.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    /// let mut tree = HuffmanTree::new();
    /// // Add some nodes to the tree and assign codes
    ///
    /// // Important: Codes must be assigned before converting to canonical form
    /// tree.assign();
    /// let canonical_tree = tree.to_canonical();
    /// ```
    #[must_use]
    pub fn to_canonical(&self) -> Self {
        assert!(
            self.map.is_some(),
            "Cannot create a canonical tree unless it has been assigned \
            codes. Help: call tree.assign() first"
        );

        let map = self.map.as_ref().unwrap();

        let mut syms = map.keys().copied().collect::<Vec<char>>();
        syms.sort_unstable();

        let bitlen_list = syms.iter().fold(vec![], |mut acc, sym| {
            acc.push(map[sym].1);
            acc
        });

        let mut tree = Self::from_bitlen_list(&bitlen_list, &syms);
        tree.assign();
        tree
    }

    /// Returns the maximum code length in the Huffman tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::huffman::HuffmanTree;
    /// let tree = HuffmanTree::new();
    /// // Add some nodes to the tree
    /// let max_len = tree.max_code_len();
    /// println!("{max_len}");
    /// ```
    #[must_use]
    pub fn max_code_len(&self) -> usize {
        match &self.map {
            Some(map) => map.values().map(|&(_, len)| len).max().unwrap_or(0),
            None => Self::get_depth(&self.root),
        }
    }

    /// Helper function to get the depth of a node in the Huffman tree.
    fn get_depth(root: &HuffmanTreeNode) -> usize {
        let left_depth = root.left.as_deref().map_or(0, Self::get_depth);
        let right_depth = root.right.as_deref().map_or(0, Self::get_depth);

        1 + left_depth.max(right_depth)
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

/// Checks if the given `LZ77Compressor` has compatible parameters for `Zlib` compression.
///
/// # Panics
///
/// Panics if the `LZ77Compressor` parameters are incompatible with `Zlib` requirements.
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

/// Returns the length code for a given length.
///
/// # Examples
///
/// ```
/// use mini_git::zlib::huffman::get_length_code;
/// let length = 10;
/// let length_code = get_length_code(length);
/// assert_eq!(257 + 7, length_code); // Values are offset by 257
/// ```
#[must_use]
pub fn get_length_code(length: usize) -> usize {
    match LENGTH_BASE.binary_search(&length) {
        Ok(index) => index + 257,
        Err(index) => index + 256,
    }
}

/// Returns the distance code for a given distance.
///
/// # Examples
///
/// ```
/// use mini_git::zlib::huffman::get_distance_code;
/// let distance = 100;
/// let distance_code = get_distance_code(distance);
/// assert_eq!(13, distance_code);
/// ```
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
    fn test_huffman_tree_node_new() {
        let node = HuffmanTreeNode::new();
        assert!(node.symbol.is_none());
        assert!(node.left.is_none());
        assert!(node.right.is_none());
    }

    #[test]
    fn test_huffman_tree_node_from() {
        let node = HuffmanTreeNode::from('A');
        assert_eq!(node.symbol, Some('A'));
        assert!(node.left.is_none());
        assert!(node.right.is_none());
    }

    #[test]
    fn test_huffman_tree_from_data() {
        let data = b"aabbbcccc";
        let mut tree = HuffmanTree::from_data(data);
        tree.assign();
        assert_eq!(tree.n_codes(), 3);
    }

    #[test]
    fn test_huffman_tree_from_freq() {
        let mut frequencies = HashMap::new();
        frequencies.insert('a', 2);
        frequencies.insert('b', 3);
        frequencies.insert('c', 4);
        let mut tree = HuffmanTree::from_freq(frequencies);
        tree.assign();
        assert_eq!(tree.n_codes(), 3);
    }

    #[test]
    fn test_huffman_tree_n_codes() {
        let mut tree = HuffmanTree::new();
        assert_eq!(tree.n_codes(), 0);
        tree.insert(0b0, 1, 'A');
        tree.insert(0b10, 2, 'B');
        tree.insert(0b11, 2, 'C');
        tree.assign();
        assert_eq!(tree.n_codes(), 3);
    }

    #[test]
    fn test_huffman_tree_assign() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b0, 1, 'A');
        tree.insert(0b10, 2, 'B');
        tree.insert(0b11, 2, 'C');
        tree.assign();
        assert!(tree.encodings().is_some());
        assert_eq!(tree.encodings().unwrap().len(), 3);
    }

    #[test]
    fn test_huffman_tree_encodings() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b0, 1, 'A');
        tree.insert(0b10, 2, 'B');
        tree.insert(0b11, 2, 'C');
        tree.assign();
        let encodings = tree.encodings().unwrap();
        assert_eq!(encodings.get(&'A'), Some(&(0, 1)));
        assert_eq!(encodings.get(&'B'), Some(&(1, 2)));
        assert_eq!(encodings.get(&'C'), Some(&(3, 2)));
    }

    #[test]
    fn test_huffman_tree_to_canonical() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b0, 1, 'A');
        tree.insert(0b10, 2, 'B');
        tree.insert(0b110, 3, 'C');
        tree.assign();
        let canonical_tree = tree.to_canonical();
        assert_eq!(canonical_tree.encode('A'), Some((0, 1)));
        assert_eq!(canonical_tree.encode('B'), Some((1, 2)));
        assert_eq!(canonical_tree.encode('C'), Some((3, 3)));
    }

    #[test]
    fn test_huffman_tree_encode() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b0, 1, 'A');
        tree.insert(0b10, 2, 'B');
        tree.insert(0b11, 2, 'C');
        tree.assign();
        assert_eq!(tree.encode('A'), Some((0, 1)));
        assert_eq!(tree.encode('B'), Some((1, 2)));
        assert_eq!(tree.encode('C'), Some((3, 2)));
        assert_eq!(tree.encode('D'), None);
    }

    #[test]
    fn test_huffman_tree_max_code_len() {
        let mut tree = HuffmanTree::new();
        tree.insert(0b0, 1, 'A');
        tree.insert(0b10, 2, 'B');
        tree.insert(0b110, 3, 'C');
        assert_eq!(tree.max_code_len(), 4);
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
    #[allow(clippy::unusual_byte_groupings)]
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
    #[allow(clippy::unusual_byte_groupings)]
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
    #[allow(clippy::unusual_byte_groupings)]
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
    fn test_get_length_code() {
        assert_eq!(get_length_code(3), 257);
        assert_eq!(get_length_code(10), 264);
        assert_eq!(get_length_code(258), 285);
    }

    #[test]
    fn test_get_distance_code() {
        assert_eq!(get_distance_code(1), 0);
        assert_eq!(get_distance_code(5), 4);
        assert_eq!(get_distance_code(100), 13);
    }

    #[test]
    #[should_panic(expected = "Incompatible LZ77 window size")]
    fn test_check_lz77_incompatible_window_size() {
        let lz77 = LZ77Compressor::with_window_size(1024);
        check_lz77(&lz77);
    }

    #[test]
    #[should_panic(expected = "Incompatible LZ77 min string length")]
    fn test_check_lz77_incompatible_min_length() {
        let mut lz77 = LZ77Compressor::with_window_size(32768);
        lz77.min_match_length = 2;
        lz77.max_match_length = 258;
        check_lz77(&lz77);
    }

    #[test]
    #[should_panic(expected = "Incompatible LZ77 max string length")]
    fn test_check_lz77_incompatible_max_length() {
        let mut lz77 = LZ77Compressor::with_window_size(32768);
        lz77.min_match_length = 3;
        lz77.max_match_length = 259;
        check_lz77(&lz77);
    }
}
