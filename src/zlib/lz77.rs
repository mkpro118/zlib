#![allow(unused_mut)]
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(dead_code)]

use std::{ops::Sub, os::windows};

use crate::zlib::bitwriter::BitWriter;

const MAX_WINDOW_SIZE: usize = 1 << 15; // 32 KB

#[derive(Debug)]
pub struct LZ77 {
    window_size: usize,
    lookahead_buffer_size: usize,
}

impl LZ77 {
    pub fn new() -> Self {
        Self {
            window_size: MAX_WINDOW_SIZE,
            lookahead_buffer_size: MAX_WINDOW_SIZE / 2,
        }
    }

    pub fn with_window_size(window_size: usize) -> Self {
        let window_size = window_size.min(MAX_WINDOW_SIZE);
        let lookahead_buffer_size = window_size / 2;
        Self {
            window_size,
            lookahead_buffer_size,
        }
    }

    pub fn set_window_size(&mut self, newsize: usize) -> &mut Self {
        self.window_size = newsize;
        self.lookahead_buffer_size = newsize / 2;
        self
    }

    pub fn set_lookahead_buffer_size(&mut self, newsize: usize) -> &mut Self {
        if newsize == self.window_size {
            panic!(
                "Requested lookahead buffer size is invalid as it \
                would leave no room for the search buffer"
            );
        } else if newsize > self.window_size {
            panic!(
                "Requested lookahead buffer size is invalid as it \
                overflows the window size.\n\
                Help: First increase the window size using set_window_size(usize)"
            );
        }
        self.lookahead_buffer_size = newsize;
        self
    }

    pub fn set_search_buffer_size(&mut self, newsize: usize) -> &mut Self {
        if newsize == self.window_size {
            panic!(
                "Requested search buffer size is invalid as it \
                would leave no room for the lookahead buffer.\n\
                Help: First increase the window size using set_window_size(usize)"
            );
        } else if newsize > self.window_size {
            panic!(
                "Requested search buffer size is invalid as it \
                overflows the window size.\n\
                Help: First increase the window size using set_window_size(usize)"
            );
        }
        self.lookahead_buffer_size = self.window_size - newsize;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let lz77 = LZ77::new();

        assert_eq!(lz77.window_size, MAX_WINDOW_SIZE);
        assert_eq!(lz77.lookahead_buffer_size, MAX_WINDOW_SIZE / 2);
    }

    #[test]
    fn test_with_window_size() {
        for size in 32..64 {
            let lz77 = LZ77::with_window_size(size);

            assert_eq!(lz77.window_size, size);
            assert_eq!(lz77.lookahead_buffer_size, size / 2);
        }
    }

    #[test]
    fn test_set_window_size() {
        let mut lz77 = LZ77::new();

        for size in 32..64 {
            lz77.set_window_size(size);
            assert_eq!(lz77.window_size, size);
            assert_eq!(lz77.lookahead_buffer_size, size / 2);
        }
    }

    #[test]
    fn test_set_lookahead_buffer_size() {
        let mut lz77 = LZ77::new();

        for size in 32..64 {
            lz77.set_lookahead_buffer_size(size);
            assert_eq!(lz77.window_size, MAX_WINDOW_SIZE);
            assert_eq!(lz77.lookahead_buffer_size, size);
        }
    }

    #[test]
    #[should_panic]
    fn test_set_lookahead_buffer_size_bad_input1() {
        let size = 64;
        LZ77::with_window_size(size).set_lookahead_buffer_size(size);
    }

    #[test]
    #[should_panic]
    fn test_set_lookahead_buffer_size_bad_input2() {
        let size = 64;
        LZ77::with_window_size(size).set_lookahead_buffer_size(size + 1);
    }

    #[test]
    #[should_panic]
    fn test_set_search_buffer_size_bad_input1() {
        let size = 64;
        LZ77::with_window_size(size).set_search_buffer_size(size);
    }

    #[test]
    #[should_panic]
    fn test_set_search_buffer_size_bad_input2() {
        let size = 64;
        LZ77::with_window_size(size).set_search_buffer_size(size + 1);
    }
}
