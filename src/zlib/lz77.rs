#![allow(dead_code)]

use std::{cmp::Ordering, collections::VecDeque, ops::Sub, os::windows};

use crate::zlib::bitwriter::BitWriter;

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

#[derive(Debug)]
pub struct LZ77Compressor {
    pub window_size: usize,
    pub reference_prefix: char,
    pub reference_prefix_code: u8,
    pub reference_int_base: u8,
    pub reference_int_floor_code: u8,
    pub reference_int_ceil_code: u8,
    pub max_string_distance: usize,
    pub min_string_length: usize,
    pub max_string_length: usize,
}

impl Default for LZ77Compressor {
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
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_window_size(window_size: usize) -> Self {
        let window_size = window_size.min(MAX_WINDOW_SIZE);
        Self {
            window_size,
            ..Self::default()
        }
    }

    pub fn set_window_size(&mut self, newsize: usize) -> &mut Self {
        self.window_size = newsize;
        self
    }

    pub fn compress(&self, data: &[u8]) -> Vec<u8> {
        let mut compressed: Vec<u8> = vec![];
        let window_size = self.window_size;

        let mut pos = 0;
        let last_pos = data.len() - self.min_string_length;

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
}
