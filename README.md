<h1 align="center">
  Zlib
</h1>

<p align="center">
  <img alt="Rust 1.68" src="https://img.shields.io/badge/1.68-grey?style=flat&logo=rust&logoColor=orange&color=%232A2A2A">

  <a href="https://github.com/mkpro118/zlib/actions/workflows/tests.yml">
    <img alt="Tests" src="https://github.com/mkpro118/zlib/actions/workflows/tests.yml/badge.svg">
  </a>

  <a href="https://github.com/mkpro118/zlib/actions/workflows/clippy.yml">
    <img alt="Tests" src="https://github.com/mkpro118/zlib/actions/workflows/clippy.yml/badge.svg">
  </a>
  
  <a href="https://github.com/mkpro118/zlib/blob/main/LICENSE">
    <img alt="MIT LICENSE" src="https://img.shields.io/badge/License-MIT-blue?style=flat&labelColor=%233f3f3f"/>
  </a>
</p>

<p align="center">
  A smaller re-implementation of Zlib compression and decompression in Rust.
</p>

## Description

This project is a Rust implementation of the Zlib/DEFLATE compression and decompression
algorithm. It's designed as a side project to explore the internals of Zlib,
and as a component of a [larger project](https://github.com/mkpro118/mini-git).

## Features

- Zlib Raw, Fixed and Dynamic compression/decompression
- Huffman encoding/decoding
- LZ77 compression/decompression
- Bitstream readers/writers
- Adler32 checksum

## Installation

To use this in your project, you can add it as a git dependency in your `Cargo.toml`:

```toml
[dependencies]
zlib = { git = "https://github.com/mkpro118/zlib", version = "0.1.0" }
```

## Usage

Here are some examples of how to use the main components of this library:

### Compression

```rust
use std::fs;
use zlib::{compress, Strategy};

fn compress_file(input_path: &str, output_path: &str) {
    let input_data = fs::read(input_path).expect("Should read from file!");

    let compressed_data = compress(&input_data, &Strategy::Dynamic);

    fs::write(output_path, &compressed_data).expect("Should write to file!");
}

// Usage
compress_file("input.txt", "compressed.zlib").expect("Success");
```

### Decompression

```rust
use std::fs;
use zlib::decompress;

fn decompress_file(input_path: &str, output_path: &str) {
    let compressed_data = fs::read(input_path).expect("Should read from file!");

    let decompressed_data = decompress(&compressed_data).expect("Should decompress!");

    fs::write(output_path, &decompressed_data).expect("Should write to file!");
}

// Usage
decompress_file("compressed.zlib", "decompressed.txt").unwrap();
```

### Huffman Tree

```rust
use std::fs
use zlib::huffman::HuffmanTree;

fn create_huffman_tree(file_path: &str) -> HuffmanTree {
    let data = fs::read(file_path).expect("Should read from file!");

    HuffmanTree::from_data(&data)
}

// Usage
let tree = create_huffman_tree("input.txt");
```

### LZ77 Compression

```rust
use std::fs::{File};
use zlib::lz77::LZ77Compressor;

fn lz77_compress_file(input_path: &str, output_path: &str) {
    let data = fs::read(input_path).expect("Should read from file!");

    let compressor = LZ77Compressor::new();
    let compressed = compressor.compress(&data);

    // Note: This is a shortcut. In a real scenario, you'd need to serialize
    // the LZ77Units to bytes before writing to a file.
    // This serialization is not a part of this library, as the LZ77 compressed
    // data is intended to be a in-memory data structure.
    let mut output_file = File::create(output_path)
        .expect("Should create a file");
    for unit in compressed {
        write!(output_file, "{:?}\n", unit).expect("Should write to file!");
    }
}

// Usage
lz77_compress_file("input.txt", "lz77_compressed.txt");
```

## Dependencies

This project has *zero* dependencies. All functionality has been implemented
from scratch.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the [MIT License](/LICENSE).

## Performance

Please note that this implementation is not meant to be more performant than
the original ZLIB. It's a Rust reimplementation created as a side project based
on [RFC 1950](https://www.ietf.org/rfc/rfc1950.txt) and
[RFC 1951](https://www.ietf.org/rfc/rfc1951.txt).
