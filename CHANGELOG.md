# Change Log
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]
### Added
- `PartialEq<{float}>` for all types. Meaning one can write:
  ```rust
  let n = FiniteF32::new(1.0).unwrap();
  assert_eq!(n, 1.0);
  // instead of
  assert_eq!(n.get(), 1.0);
  ```

## 0.1.0 - 2022-07-23
### Added
- Initial version

[Unreleased]: https://github.com/RazrFalcon/strict-num/compare/v0.1.0...HEAD
