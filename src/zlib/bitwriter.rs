//! This module provides a `BitWriter` struct for writing bits to a byte vector.

#![allow(dead_code)]

/// A struct for writing individual bits or groups of bits to a byte vector.
///
/// # Examples
///
/// ```
/// use mini_git::zlib::bitwriter::BitWriter;
///
/// let mut writer = BitWriter::new();
/// writer.write_bits(0b110, 3);
/// writer.write_bit(1);
/// writer.write_bits(0b01, 2);
///
/// let result = writer.finish();
/// assert_eq!(result, vec![0b0001_1110]);
/// ```
#[derive(Debug)]
pub struct BitWriter {
    buffer: Vec<u8>,
    byte: u8,
    numbits: usize,
}

impl Default for BitWriter {
    /// Creates a default `BitWriter`
    fn default() -> Self {
        Self::new()
    }
}

impl BitWriter {
    /// Creates a new `BitWriter`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitwriter::BitWriter;
    ///
    /// let writer = BitWriter::new();
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self {
            buffer: Vec::new(),
            byte: 0,
            numbits: 0,
        }
    }

    /// Writes a single bit to the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitwriter::BitWriter;
    ///
    /// let mut writer = BitWriter::new();
    /// writer.write_bit(1);
    /// writer.write_bit(0);
    /// writer.write_bit(1);
    ///
    /// let result = writer.finish();
    /// assert_eq!(result, vec![0b0000_0101]);
    /// ```
    pub fn write_bit(&mut self, bit: u8) {
        if self.numbits == 8 {
            self.flush_byte();
        }

        self.byte |= (bit & 1) << self.numbits;
        self.numbits += 1;
    }

    /// Writes multiple bits to the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitwriter::BitWriter;
    ///
    /// let mut writer = BitWriter::new();
    /// writer.write_bits(0b110, 3);
    /// writer.write_bits(0b10101, 5);
    ///
    /// let result = writer.finish();
    /// assert_eq!(result, vec![0b1010_1110]);
    /// ```
    #[allow(clippy::missing_panics_doc)]
    pub fn write_bits(&mut self, mut value: usize, mut num_bits: usize) {
        while num_bits > 0 {
            self.write_bit(
                u8::try_from(value & 1).expect("should be able to write 1 bit"),
            );
            value >>= 1;
            num_bits -= 1;
        }
    }

    /// Writes a single byte to the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitwriter::BitWriter;
    ///
    /// let mut writer = BitWriter::new();
    /// writer.write_byte(0xA5);
    /// writer.write_byte(0x3C);
    ///
    /// let result = writer.finish();
    /// assert_eq!(result, vec![0xA5, 0x3C]);
    /// ```
    pub fn write_byte(&mut self, byte: u8) {
        // Flush any existing incomplete byte
        self.flush_byte();
        // Write the new byte
        self.buffer.push(byte);
    }

    /// Writes multiple bytes to the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitwriter::BitWriter;
    ///
    /// let mut writer = BitWriter::new();
    /// writer.write_bytes(&[0xA5, 0x3C, 0x7F]);
    ///
    /// let result = writer.finish();
    /// assert_eq!(result, vec![0xA5, 0x3C, 0x7F]);
    /// ```
    pub fn write_bytes(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_byte(byte);
        }
    }

    /// Flushes any remaining bits in the current byte to the buffer.
    ///
    /// This method is called automatically by `finish()`, but can be called
    /// manually if needed.
    ///
    /// # Panics
    ///
    /// If the `BitWriter` is in invalid state. This is more of a sanity check
    /// than a possible manual manipulation error.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitwriter::BitWriter;
    ///
    /// let mut writer = BitWriter::new();
    /// writer.write_bits(0b101, 3);
    /// writer.flush_byte();
    ///
    /// let result = writer.finish();
    /// assert_eq!(result, vec![0b0000_0101]);
    /// ```
    pub fn flush_byte(&mut self) {
        assert!(self.numbits <= 8, "Invalid state");
        if self.numbits > 0 {
            self.buffer.push(self.byte);
            self.byte = 0;
            self.numbits = 0;
        }
    }

    /// Finishes writing and returns the buffer as a vector of bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use mini_git::zlib::bitwriter::BitWriter;
    ///
    /// let mut writer = BitWriter::new();
    /// writer.write_bits(0b1101, 4);
    /// writer.write_byte(0xA5);
    ///
    /// let result = writer.finish();
    /// assert_eq!(result, vec![0b0000_1101, 0xA5]);
    /// ```
    #[must_use]
    pub fn finish(mut self) -> Vec<u8> {
        self.flush_byte();
        self.buffer
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_bit() {
        let mut writer = BitWriter::new();
        let bits = [1, 0, 1, 1, 1, 0, 0, 1];
        for &bit in &bits {
            writer.write_bit(bit);
        }
        assert_eq!(writer.finish(), vec![0x9d]);
    }

    #[test]
    fn test_write_bits() {
        let mut writer = BitWriter::new();
        writer.write_bits(0b1_0010_1011, 9);
        assert_eq!(writer.finish(), vec![0x2b, 0x01]);
    }

    #[test]
    fn test_write_byte() {
        let mut writer = BitWriter::new();
        writer.write_byte(0x66);
        writer.write_byte(0x36);
        assert_eq!(writer.finish(), vec![0x66, 0x36]);
    }

    #[test]
    fn test_write_bytes() {
        let mut writer = BitWriter::new();
        writer.write_bytes(&[0x66, 0x36]);
        assert_eq!(writer.finish(), vec![0x66, 0x36]);
    }

    #[test]
    fn test_mixed_writes() {
        let mut writer = BitWriter::new();
        writer.write_bits(0b1010, 4);
        writer.write_byte(0xF0);
        writer.write_bit(1);
        writer.write_bits(0b101, 3);
        assert_eq!(writer.finish(), vec![0x0A, 0xF0, 0x0B]);
    }

    #[test]
    fn test_write_byte_with_existing_bits() {
        let mut writer = BitWriter::new();
        writer.write_bits(0b101, 3);
        writer.write_byte(0xF0);
        writer.write_byte(0xAA);
        assert_eq!(writer.finish(), vec![0x05, 0xF0, 0xAA]);
    }
}
