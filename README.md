# srp-mdns-proxy firmware probe

Measures whether Apple's `/usr/libexec/srp-mdns-proxy` contains multi-precision (public-key)
arithmetic, across OS platforms. A constant-time bignum implementation is defined by its
add-with-carry chains, so counting `adcs`/`sbcs` answers the question on a stripped binary without
needing symbols.

Security research for an Apple Security Bounty report. Uses only publicly downloadable Apple
firmware and standard Apple developer tools (`lipo`, `otool`, `nm`, `hdiutil`).

**No Apple code is published by this repository.** Workflow artifacts contain only aggregate facts
about the binary — hashes, section sizes, symbol and import lists, instruction counts. The firmware,
the binary, and any full disassembly are produced on the runner, used, and discarded; a guard step
fails the run if anything binary-looking or larger than 2 MB reaches the upload directory.
