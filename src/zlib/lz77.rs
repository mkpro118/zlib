//! This module implements the LZ77 compression algorithm.
//!
//! LZ77 is a lossless data compression algorithm that replaces repeated
//! occurrences of data with references to a single copy of that data existing
//! earlier in the input stream.
//!
//! # Examples
//!
//! ```
//! use mini_git::zlib::lz77::LZ77Compressor;
//!
//! let mut compressor = LZ77Compressor::new();
//! let data = b"ABC BC BC BC BC CD";
//! let compressed = compressor.compress(data);
//! assert!(compressed.len() < data.len());
//! ```

#![allow(dead_code)]

use std::collections::VecDeque;

const REFERENCE_PREFIX: char = '`';
const REFERENCE_PREFIX_CODE: u8 = REFERENCE_PREFIX as u8;
const REFERENCE_INT_BASE: u8 = 96;
const REFERENCE_INT_FLOOR_CODE: u8 = b' ';
const REFERENCE_INT_CEIL_CODE: u8 = 127;
const DEFAULT_MAX_STRING_DISTANCE: usize = 9215; // 32KB
const DEFAULT_MIN_STRING_LENGTH: usize = 5;
const DEFAULT_MAX_STRING_LENGTH: usize = 100;
const MAX_WINDOW_SIZE: usize = 1 << 15; // 32KB
const DEFAULT_WINDOW_SIZE: usize = 144;

/// Represents an LZ77 compressor with configurable parameters.
#[derive(Debug)]
pub struct LZ77Compressor {
    /// The size of the sliding window used for finding matches.
    pub window_size: usize,
    /// The character used to indicate a reference in the compressed output.
    pub reference_prefix: char,
    /// The byte code for the reference prefix.
    pub reference_prefix_code: u8,
    /// The base used for encoding reference integers.
    pub reference_int_base: u8,
    /// The floor code for reference integers.
    pub reference_int_floor_code: u8,
    /// The ceiling code for reference integers.
    pub reference_int_ceil_code: u8,
    /// The maximum distance allowed for string references.
    pub max_string_distance: usize,
    /// The minimum length required for string references.
    pub min_string_length: usize,
    /// The maximum length allowed for string references.
    pub max_string_length: usize,
}

impl Default for LZ77Compressor {
    /// Creates a new `LZ77Compressor` with default settings.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::lz77::LZ77Compressor;
    ///
    /// let compressor = LZ77Compressor::default();
    /// dbg!(&compressor);
    /// ```
    fn default() -> Self {
        Self {
            window_size: DEFAULT_WINDOW_SIZE,
            reference_prefix: REFERENCE_PREFIX,
            reference_prefix_code: REFERENCE_PREFIX_CODE,
            reference_int_base: REFERENCE_INT_BASE,
            reference_int_floor_code: REFERENCE_INT_FLOOR_CODE,
            reference_int_ceil_code: REFERENCE_INT_CEIL_CODE,
            max_string_distance: DEFAULT_MAX_STRING_DISTANCE,
            min_string_length: DEFAULT_MIN_STRING_LENGTH,
            max_string_length: DEFAULT_MAX_STRING_LENGTH,
        }
    }
}

impl LZ77Compressor {
    /// Creates a new `LZ77Compressor` with default settings.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::lz77::LZ77Compressor;
    ///
    /// let compressor = LZ77Compressor::new();
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new `LZ77Compressor` with a custom window size.
    ///
    /// # Arguments
    ///
    /// * `window_size` - The size of the sliding window to use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::lz77::LZ77Compressor;
    ///
    /// let compressor = LZ77Compressor::with_window_size(1024);
    /// assert_eq!(compressor.window_size, 1024);
    /// ```
    #[must_use]
    pub fn with_window_size(window_size: usize) -> Self {
        let window_size = window_size.min(MAX_WINDOW_SIZE);
        Self {
            window_size,
            ..Self::default()
        }
    }

    /// Sets the window size for the compressor.
    ///
    /// # Arguments
    ///
    /// * `newsize` - The new window size to set.
    ///
    /// # Returns
    ///
    /// Returns a mutable reference to the compressor for method chaining.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::lz77::LZ77Compressor;
    ///
    /// let mut compressor = LZ77Compressor::new();
    /// compressor.set_window_size(2048);
    /// assert_eq!(compressor.window_size, 2048);
    /// ```
    pub fn set_window_size(&mut self, newsize: usize) -> &mut Self {
        self.window_size = newsize.min(MAX_WINDOW_SIZE);
        self
    }

    /// Compresses the input data using the LZ77 algorithm.
    ///
    /// # Arguments
    ///
    /// * `data` - The input data to compress.
    ///
    /// # Returns
    ///
    /// Returns a `Vec<u8>` containing the compressed data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::lz77::LZ77Compressor;
    ///
    /// let compressor = LZ77Compressor::new();
    /// let data = b"ABCBDBDBDBDBDBDBCBADBSB";
    /// let compressed = compressor.compress(data);
    /// assert!(compressed.len() < data.len());
    /// ```
    #[must_use]
    pub fn compress(&self, data: &[u8]) -> Vec<u8> {
        let mut compressed: Vec<u8> = vec![];
        let window_size = self.window_size;

        let mut pos = 0;
        let last_pos = if data.len() > self.min_string_length {
            data.len() - self.min_string_length
        } else {
            compressed.extend_from_slice(data);
            return compressed;
        };

        while pos < last_pos {
            let mut search_start = if pos > window_size {
                pos - window_size
            } else {
                0
            };

            let mut match_length = self.min_string_length;

            let mut found_match = false;
            let mut best_match_distance = self.max_string_distance;
            let mut best_match_length = 0;
            let new_compressed: Option<Vec<u8>>;

            while search_start + match_length < pos {
                let end = data.len().min(search_start + match_length);
                let m1 = &data[search_start..end];
                let end = data.len().min(pos + match_length);
                let m2 = &data[pos..end];

                if m1 == m2 && match_length < self.max_string_length {
                    match_length += 1;
                    found_match = true;
                } else {
                    let true_match_length = match_length - 1;

                    if found_match && true_match_length > best_match_length {
                        best_match_distance =
                            pos - search_start - true_match_length;
                        best_match_length = true_match_length;
                    }

                    match_length = self.min_string_length;
                    search_start += 1;
                    found_match = false;
                }
            }

            pos += if best_match_length > 0 {
                let mut new_data = vec![self.reference_prefix_code];
                new_data.extend_from_slice(
                    &self.encode_reference_int(best_match_distance, 2),
                );
                new_data.extend_from_slice(
                    &self.encode_reference_length(best_match_length),
                );

                new_compressed = Some(new_data);
                best_match_length
            } else {
                let new_data = if data[pos] == self.reference_prefix_code {
                    vec![self.reference_prefix_code, self.reference_prefix_code]
                } else {
                    vec![data[pos]]
                };

                new_compressed = Some(new_data);

                1
            };

            if let Some(chunk) = new_compressed {
                compressed.extend_from_slice(&chunk);
            }
        }

        compressed.extend(data[pos..].iter().fold(vec![], |mut acc, &x| {
            if x == self.reference_prefix_code {
                acc.push(x);
            }
            acc.push(x);
            acc
        }));

        compressed
    }

    /// Encodes a reference integer used in LZ77 compression.
    ///
    /// # Arguments
    ///
    /// * `value` - The integer value to encode.
    /// * `width` - The number of bytes to use for encoding.
    ///
    /// # Returns
    ///
    /// Returns a `Vec<u8>` containing the encoded integer.
    ///
    /// # Panics
    ///
    /// Panics if the value is out of range for the given width.
    #[allow(clippy::cast_possible_truncation)]
    fn encode_reference_int(&self, mut value: usize, width: usize) -> Vec<u8> {
        let ref_int_base = self.reference_int_base as usize;

        assert!(
            value < ref_int_base.pow(width as u32) - 1,
            "{}",
            format!("Reference value out of range: {value} (width = {width})")
        );

        let mut encoded: VecDeque<u8> = VecDeque::new();

        while value > 0 {
            let byte = (value % ref_int_base) as u8;
            let byte = byte + self.reference_int_floor_code;
            encoded.push_front(byte);

            value /= ref_int_base;
        }

        let missing_len = if width > encoded.len() {
            width - encoded.len()
        } else {
            0
        };

        let encoded = (0..missing_len).fold(encoded, |mut acc, _| {
            acc.push_front(self.reference_int_floor_code);
            acc
        });

        Vec::from(encoded)
    }

    /// Shortcut function for encoding reference lengths
    fn encode_reference_length(&self, length: usize) -> Vec<u8> {
        self.encode_reference_int(length - self.min_string_length, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compress_should_reduce_size() {
        let data = [
            (
                "ABCBDBDBDBDBDBDBCBADBSB".as_bytes(),
                "ABCBDBDBDBD` # CBADBSB".as_bytes(),
            ),
            (
                "hi hi hello hi hi wow hello hi".as_bytes(),
                "hi hi hello` $ i wow` '$".as_bytes(),
            ),
            (
                "abcdefabcdefabcdef".as_bytes(),
                "abcdefabcdef` &!".as_bytes(),
            ),
        ];

        let compressor = LZ77Compressor::default();
        for (raw_data, known_compressed) in data {
            let compressed = compressor.compress(&raw_data);
            assert!(raw_data.len() > compressed.len());
            assert_eq!(known_compressed.len(), compressed.len());
            assert_eq!(known_compressed, compressed);
        }
    }

    #[test]
    fn test_compress_should_not_reduce_size() {
        let data = [
            "ABCDEFGHIJKLMNOPQRSTUVWXYZ".as_bytes(),
            "LZ77 compression in Rust!".as_bytes(),
            "only repeat twice 2233445566".as_bytes(),
        ];

        let compressor = LZ77Compressor::new();
        for raw_data in data {
            let compressed = compressor.compress(&raw_data);
            assert_eq!(raw_data.len(), compressed.len());
            assert_eq!(raw_data, compressed);
        }
    }

    #[test]
    fn test_default() {
        let compressor = LZ77Compressor::default();
        assert_eq!(compressor.window_size, DEFAULT_WINDOW_SIZE);
        assert_eq!(compressor.reference_prefix, REFERENCE_PREFIX);
        assert_eq!(compressor.reference_prefix_code, REFERENCE_PREFIX_CODE);
        assert_eq!(compressor.reference_int_base, REFERENCE_INT_BASE);
        assert_eq!(
            compressor.reference_int_floor_code,
            REFERENCE_INT_FLOOR_CODE
        );
        assert_eq!(compressor.reference_int_ceil_code, REFERENCE_INT_CEIL_CODE);
        assert_eq!(compressor.max_string_distance, DEFAULT_MAX_STRING_DISTANCE);
        assert_eq!(compressor.min_string_length, DEFAULT_MIN_STRING_LENGTH);
        assert_eq!(compressor.max_string_length, DEFAULT_MAX_STRING_LENGTH);
    }

    #[test]
    fn test_new() {
        let compressor = LZ77Compressor::new();
        assert_eq!(compressor.window_size, DEFAULT_WINDOW_SIZE);
    }

    #[test]
    fn test_with_window_size() {
        let compressor = LZ77Compressor::with_window_size(1024);
        assert_eq!(compressor.window_size, 1024);
    }

    #[test]
    fn test_with_window_size_too_large() {
        let compressor = LZ77Compressor::with_window_size(MAX_WINDOW_SIZE + 1);
        assert_eq!(compressor.window_size, MAX_WINDOW_SIZE);
    }

    #[test]
    fn test_set_window_size() {
        let mut compressor = LZ77Compressor::default();
        compressor.set_window_size(1024);
        assert_eq!(compressor.window_size, 1024);
    }

    #[test]
    fn test_set_window_size_too_large() {
        let mut compressor = LZ77Compressor::default();
        compressor.set_window_size(MAX_WINDOW_SIZE + 1);
        assert_eq!(compressor.window_size, MAX_WINDOW_SIZE);
    }

    #[test]
    fn test_compress_empty_input() {
        let compressor = LZ77Compressor::default();
        let input = vec![];
        let compressed = compressor.compress(&input);
        assert_eq!(compressed, input);
    }

    #[test]
    fn test_compress_small_input() {
        let compressor = LZ77Compressor::default();
        let input = b"abcde".to_vec();
        let compressed = compressor.compress(&input);
        assert!(!compressed.is_empty());
        assert!(compressed.len() <= input.len());
    }

    #[test]
    fn test_compress_large_input() {
        let compressor = LZ77Compressor::default();
        let input = b"abcdefghijklmnopqrstuvwxyz".repeat(1000);
        let compressed = compressor.compress(&input);
        assert!(!compressed.is_empty());
        assert!(compressed.len() < input.len());
    }

    #[test]
    fn test_encode_reference_int() {
        let compressor = LZ77Compressor::default();

        // Test small values
        assert_eq!(compressor.encode_reference_int(0, 1), vec![b' ']);
        assert_eq!(compressor.encode_reference_int(1, 1), vec![b'!']);

        // Test larger values
        assert_eq!(compressor.encode_reference_int(31, 1), vec![b'?']);
        // assert_eq!(compressor.encode_reference_int(32, 2), vec![b' ', b'!']);

        // Test maximum value for width
        assert_eq!(compressor.encode_reference_int(94, 1), vec![b'~']);
    }

    #[test]
    #[should_panic(expected = "Reference value out of range")]
    fn test_encode_reference_int_out_of_range() {
        let compressor = LZ77Compressor::default();
        compressor.encode_reference_int(95, 1);
    }

    #[test]
    fn test_encode_reference_length() {
        let compressor = LZ77Compressor::default();

        // Test minimum length
        assert_eq!(
            compressor.encode_reference_length(DEFAULT_MIN_STRING_LENGTH),
            vec![b' ']
        );

        // Test some regular lengths
        assert_eq!(
            compressor.encode_reference_length(DEFAULT_MIN_STRING_LENGTH + 1),
            vec![b'!']
        );
        assert_eq!(
            compressor.encode_reference_length(DEFAULT_MIN_STRING_LENGTH + 31),
            vec![b'?']
        );

        // Test maximum length
        assert_eq!(
            compressor.encode_reference_length(DEFAULT_MIN_STRING_LENGTH + 90),
            vec![b'z']
        );
    }

    #[test]
    #[should_panic(expected = "Reference value out of range")]
    fn test_encode_reference_length_too_large() {
        let compressor = LZ77Compressor::default();
        compressor.encode_reference_length(DEFAULT_MIN_STRING_LENGTH + 96);
    }

    #[test]
    fn test_compress_with_different_window_sizes() {
        let input = b"abcdefghijklmnopqrstuvwxyz".repeat(100);
        let small_window = LZ77Compressor::with_window_size(64);
        let large_window = LZ77Compressor::with_window_size(1024);

        let compressed_small = small_window.compress(&input);
        let compressed_large = large_window.compress(&input);

        assert!(compressed_small.len() > compressed_large.len());
    }

    #[test]
    fn test_compress_worst_case() {
        let compressor = LZ77Compressor::default();
        let input: Vec<u8> = (0..255).collect();
        let compressed = compressor.compress(&input);
        assert!(compressed.len() >= input.len());
    }

    #[test]
    fn test_compress_best_case() {
        let compressor = LZ77Compressor::default();
        let input = vec![b'a'; 1000];
        let compressed = compressor.compress(&input);
        dbg!(compressed.len());
        assert!(compressed.len() < input.len() / 5);
    }
}
