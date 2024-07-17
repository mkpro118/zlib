#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
    };
    use zlib::{compress, compress::Strategy, decompress};

    fn walkdir(top: &Path) -> Vec<PathBuf> {
        assert!(top.is_dir(), "Top is not a directory (top = {top:?})");
        top.read_dir()
            .expect("Should read the dir")
            .flatten()
            .map(|e| e.path())
            .filter(|path| {
                path.file_stem().is_some_and(|stem| {
                    !stem.to_str().is_some_and(|x| x.starts_with('.'))
                })
            })
            .fold(vec![], |mut paths, entry| {
                if entry.is_file() {
                    paths.push(entry);
                } else {
                    paths.extend_from_slice(&walkdir(&entry));
                }
                paths
            })
    }

    #[test]
    fn test_fixed_on_license() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let license = root.join("LICENSE");
        let bytes = fs::read(license).expect("Read file!");

        let compressed = compress(&bytes, &Strategy::Fixed);
        let decompressed =
            decompress(&compressed).expect("Correct decompression");

        assert_eq!(bytes, decompressed);
    }

    #[test]
    fn test_fixed_on_source_files() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let src = root.join("src");

        for file in walkdir(&src) {
            let bytes = fs::read(file).expect("Read file!");

            let compressed = compress(&bytes, &Strategy::Fixed);
            let decompressed =
                decompress(&compressed).expect("Correct decompression");

            assert_eq!(bytes, decompressed);
        }
    }

    #[test]
    fn test_dynamic_on_license() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let license = root.join("LICENSE");
        let bytes = fs::read(license).expect("Read file!");

        let compressed = compress(&bytes, &Strategy::Dynamic);
        let decompressed =
            decompress(&compressed).expect("Correct decompression");

        assert_eq!(bytes, decompressed);
    }

    #[test]
    fn test_dynamic_on_source_files() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let src = root.join("src");

        for file in walkdir(&src) {
            let bytes = fs::read(file).expect("Read file!");

            let compressed = compress(&bytes, &Strategy::Dynamic);
            let decompressed =
                decompress(&compressed).expect("Correct decompression");

            assert_eq!(bytes, decompressed);
        }
    }

    #[test]
    fn test_auto_on_license() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let license = root.join("LICENSE");
        let bytes = fs::read(license).expect("Read file!");

        let compressed = compress(&bytes, &Strategy::Auto);
        let decompressed =
            decompress(&compressed).expect("Correct decompression");

        assert_eq!(bytes, decompressed);
    }

    #[test]
    fn test_auto_on_source_files() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let src = root.join("src");

        for file in walkdir(&src) {
            let bytes = fs::read(file).expect("Read file!");

            let compressed = compress(&bytes, &Strategy::Auto);
            let decompressed =
                decompress(&compressed).expect("Correct decompression");

            assert_eq!(bytes, decompressed);
        }
    }
}
