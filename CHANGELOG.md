# Changelog

This file records notable user-facing changes to Aufbau. The project follows
[Semantic Versioning](https://semver.org/).

## [0.0.2] - Unreleased

### Added

- `unpack` code action: the language server offers to rewrite a proof line
  containing inline rule applications into separate labeled lines, one per
  hidden application, with each new line's assertion filled in from the
  checked conclusion. Offered only when the document checks cleanly and the
  rewritten document does too.

## [0.0.1] - 2026-07-16

### Added

- Initial experimental release of the `abc` proof compiler and `mm0-zig`
  verifier.
- WebAssembly compiler and verifier packages for browsers and Node.
- Browser packages for the language server and embeddable proof editor.
- Hosted web demo.

See the [0.0.1 release notes](RELEASE_NOTES.md) for further details.

[0.0.2]: https://github.com/gleachkr/Aufbau/compare/v0.0.1...HEAD
[0.0.1]: https://github.com/gleachkr/Aufbau/releases/tag/v0.0.1
