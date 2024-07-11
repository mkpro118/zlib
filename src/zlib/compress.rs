use crate::zlib::huffman::{
    ZLIB_MAX_STRING_LENGTH, ZLIB_MIN_STRING_LENGTH, ZLIB_WINDOW_SIZE,
};
use crate::zlib::lz77::LZ77Compressor;

use super::bitwriter::BitWriter;

pub enum Strategy {
    Auto,
    Dynamic,
    Fixed,
    Raw,
}

#[must_use]
pub fn compress(data: &[u8], strategy: &Strategy) -> Vec<u8> {
    use Strategy::{Auto, Dynamic, Fixed, Raw};

    let mut compressor = LZ77Compressor::with_window_size(ZLIB_WINDOW_SIZE);
    compressor.min_string_length = ZLIB_MIN_STRING_LENGTH;
    compressor.max_string_length = ZLIB_MAX_STRING_LENGTH;
    compressor.max_string_distance = ZLIB_WINDOW_SIZE;

    let data = compressor.compress(data);

    let mut bitwriter = BitWriter::new();
    match strategy {
        Dynamic => compress_dynamic(&mut bitwriter, &data, &compressor),
        Fixed => compress_fixed(&mut bitwriter, &data),
        Raw => compress_raw(&mut bitwriter, &data),
        Auto => {}
    };

    bitwriter.finish()
}

#[allow(clippy::cast_possible_truncation)]
fn compress_raw(writer: &mut BitWriter, data: &[u8]) {
    // Write length of block
    let len = data.len() as u16;
    let bytes = [(len >> 8) as u8, (len & 0x0f) as u8];
    writer.write_bytes(&bytes);

    // Write one's complement of the length of block
    let len = !len;
    let bytes = [(len >> 8) as u8, (len & 0x0f) as u8];
    writer.write_bytes(&bytes);

    // Write the raw block out
    writer.write_bytes(data);
}

fn compress_fixed(_writer: &mut BitWriter, _data: &[u8]) {
    todo!()
}

fn compress_dynamic(
    _writer: &mut BitWriter,
    _data: &[u8],
    _compressor: &LZ77Compressor,
) {
    todo!()
}
