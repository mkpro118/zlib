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

const DEFAULT_MIN_STRING_LENGTH: usize = 5;
const DEFAULT_MAX_STRING_LENGTH: usize = 100;
const MAX_WINDOW_SIZE: usize = 1 << 15; // 32KB
const DEFAULT_WINDOW_SIZE: usize = 144;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LZ77Unit {
    Literal(u8),
    Marker(usize, usize),
}

/// Represents an LZ77 compressor with configurable parameters.
#[derive(Debug)]
pub struct LZ77Compressor {
    /// The size of the sliding window used for finding matches.
    pub window_size: usize,
    /// The minimum length required for string references.
    pub min_match_length: usize,
    /// The maximum length allowed for string references.
    pub max_match_length: usize,
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
            min_match_length: DEFAULT_MIN_STRING_LENGTH,
            max_match_length: DEFAULT_MAX_STRING_LENGTH,
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
    pub fn compress(&self, data: &[u8]) -> Vec<LZ77Unit> {
        use LZ77Unit::{Literal, Marker};

        let mut compressed: Vec<LZ77Unit> = vec![];
        let window_size = self.window_size;

        let mut pos = 0;
        let last_pos = if data.len() > self.min_match_length {
            data.len() - self.min_match_length
        } else {
            return data.iter().map(|&byte| Literal(byte)).collect();
        };

        while pos < last_pos {
            let mut search_start = if pos > window_size {
                pos - window_size
            } else {
                0
            };

            let mut match_length = self.min_match_length;

            let mut found_match = false;
            let mut best_match_distance = 0;
            let mut best_match_length = 0;

            while search_start + match_length < pos {
                let end = data.len().min(search_start + match_length);
                let m1 = &data[search_start..end];
                let end = data.len().min(pos + match_length);
                let m2 = &data[pos..end];

                if m1 == m2 && match_length < self.max_match_length {
                    match_length += 1;
                    found_match = true;
                } else {
                    let true_match_length = match_length - 1;

                    if found_match && true_match_length > best_match_length {
                        best_match_distance = pos - search_start;
                        best_match_length = true_match_length;
                    }

                    match_length = self.min_match_length;
                    search_start += 1;
                    found_match = false;
                }
            }

            pos += if best_match_length > 0 {
                compressed.push(Marker(best_match_length, best_match_distance));
                best_match_length
            } else {
                compressed.push(Literal(data[pos]));
                1
            };
        }

        compressed.extend(data[pos..].iter().fold(vec![], |mut acc, &x| {
            acc.push(Literal(x));
            acc
        }));

        compressed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compress_should_reduce_size() {
        let data = [
            "ABCBDBDBDBDBDBDBCBADBSB".as_bytes(),
            "hi hi hello hi hi wow hello hi".as_bytes(),
            "abcdefabcdefabcdef".as_bytes(),
        ];

        let compressor = LZ77Compressor::default();
        for raw_data in data {
            let compressed = compressor.compress(raw_data);
            assert!(raw_data.len() > compressed.len());
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
            let compressed = compressor.compress(raw_data);
            assert_eq!(raw_data.len(), compressed.len());
            raw_data
                .iter()
                .zip(compressed.iter())
                .for_each(|(r, c)| match c {
                    LZ77Unit::Literal(b) => assert_eq!(r, b),
                    _ => panic!("Encounter non-literal data"),
                })
        }
    }

    #[test]
    fn test_default() {
        let compressor = LZ77Compressor::default();
        assert_eq!(compressor.window_size, DEFAULT_WINDOW_SIZE);
        assert_eq!(compressor.min_match_length, DEFAULT_MIN_STRING_LENGTH);
        assert_eq!(compressor.max_match_length, DEFAULT_MAX_STRING_LENGTH);
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
        assert_eq!(compressed.len(), 0);
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
