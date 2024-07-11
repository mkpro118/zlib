//! This module provides a `BitReader` struct for reading bits from a byte slice.
//! It also includes utility functions for encoding codes into bytes.

/// A struct for reading individual bits from a byte slice.
///
/// # Examples
///
/// ```
/// use mini_git::zlib::bitreader::BitReader;
///
/// let mut reader = BitReader::new(b"\x9d");
///
/// assert_eq!(reader.read_bit(), 1);
/// assert_eq!(reader.read_bit(), 0);
/// assert_eq!(reader.read_bit(), 1);
/// ```
#[derive(Debug)]
pub struct BitReader<'a> {
    mem: &'a [u8],
    pos: usize,
    byte: u8,
    numbits: isize,
}

impl<'a> BitReader<'a> {
    /// Creates a new `BitReader` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitreader::BitReader;
    ///
    /// let data = vec![0xA5, 0x3C];
    /// let reader = BitReader::new(&data);
    /// ```
    pub fn new(mem: &'a [u8]) -> Self {
        Self {
            mem,
            pos: 0,
            byte: 0,
            numbits: 0,
        }
    }

    /// Reads a single byte from the input.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitreader::BitReader;
    ///
    /// let data = vec![0xA5, 0x3C];
    /// let mut reader = BitReader::new(&data);
    ///
    /// assert_eq!(reader.read_byte(), 0xA5);
    /// assert_eq!(reader.read_byte(), 0x3C);
    /// ```
    pub fn read_byte(&mut self) -> u8 {
        self.numbits = 0;
        let b = self.mem[self.pos];
        self.pos += 1;
        b
    }

    /// Reads a single bit from the input.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitreader::BitReader;
    ///
    /// let data = vec![0b10110001];
    /// let mut reader = BitReader::new(&data);
    ///
    /// assert_eq!(reader.read_bit(), 1);
    /// assert_eq!(reader.read_bit(), 0);
    /// ```
    pub fn read_bit(&mut self) -> u8 {
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

    /// Reads multiple bits from the input and returns them as a usize.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitreader::BitReader;
    ///
    /// let data = vec![0b10110001];
    /// let mut reader = BitReader::new(&data);
    ///
    /// assert_eq!(reader.read_bits(3), 0b001);
    /// assert_eq!(reader.read_bits(5), 0b10110);
    /// ```
    pub fn read_bits(&mut self, n: usize) -> usize {
        let mut out = 0usize;

        for i in 0..n {
            out |= (self.read_bit() as usize) << i;
        }

        out
    }

    /// Reads multiple bytes from the input and returns them as a little-endian usize.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitreader::BitReader;
    ///
    /// let data = vec![0x12, 0x34, 0x56, 0x78];
    /// let mut reader = BitReader::new(&data);
    ///
    /// assert_eq!(reader.read_bytes(2), 0x3412);
    /// assert_eq!(reader.read_bytes(2), 0x7856);
    /// ```
    pub fn read_bytes(&mut self, n: usize) -> usize {
        // read bytes as an integer in little-endian
        let mut out = 0usize;

        for i in 0..n {
            out |= (self.read_byte() as usize) << (8 * i);
        }

        out
    }
}

/// Encodes a code that is `length` bits long into bytes that is conformant
/// with DEFLATE spec.
///
/// # Examples
///
/// ```
/// use mini_git::zlib::bitreader::code_to_bytes;
///
/// let code = 0b110;
/// let length = 3;
/// let bytes = code_to_bytes(code, length);
///
/// assert_eq!(bytes, vec![3]);
/// ```
#[allow(dead_code)] // Used in tests
pub fn code_to_bytes(code: usize, length: usize) -> Vec<u8> {
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
}
