# Change Log
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [0.2.0]
### Added
- `serde` support.
  Thanks to [@Banyc](https://github.com/Banyc).

### Changed
- MSRV bumped from 1.35 to 1.56
- Rust edition is bumped from 2018 to 2021.

## [0.1.1]
### Added
- `PartialEq<{float}>` for all types. Meaning one can write:
  ```rust
  let n = FiniteF32::new(1.0).unwrap();
  assert_eq!(n, 1.0);
  // instead of
  assert_eq!(n.get(), 1.0);
  ```
- Reexport `float_cmp::Ulps`

## 0.1.0 - 2022-07-23
### Added
- Initial version

[Unreleased]: https://github.com/RazrFalcon/strict-num/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/RazrFalcon/strict-num/compare/v0.1.1...v0.2.0
[0.1.1]: https://github.com/RazrFalcon/strict-num/compare/v0.1.0...v0.1.1
