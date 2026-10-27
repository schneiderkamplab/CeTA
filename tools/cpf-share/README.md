# CPF term sharing

`cpf-share INPUT.xml NEW-OUTPUT.xml` factors byte-identical repeated `funapp`
and `var` elements into CPF's existing sequential `termIndexTable`. Bindings
precede their references. The output file must not already exist.

Build with `cargo build --release --manifest-path tools/cpf-share/Cargo.toml`.
The lockfile pins dependencies. This is an optional certificate export pass,
not part of the checker's trusted acceptance path. Use it with a consumer that
supports CPF term lookup tables; the current LeTA Python adapter requires
explicit terms and must continue using the compact, unshared archive.

Relative-ADP documents (whose adapters use fresh term maps), existing tables or
references, namespace-bearing XML, non-CPF XML, and
certificates that do not shrink are retained byte-for-byte. Malformed XML is
an error. No rewrite rules, proof obligations, or input terms are removed.
The transformation is deterministic and uses no benchmark-specific information.

Audit with `python3 tools/consolidation/audit_cpf_sharing.py INPUT.xml OUTPUT.xml`.
The audit compares the complete expanded XML tree, including significant leaf
text, attributes, input, proof, and metadata. It is independent of the Rust
interning implementation. Always certify the result as well.

`tools/consolidation/share_frontier.py` applies the pass to a frozen corpus,
audits every changed proof, records hashes and sizes, and preserves original
proof identities. It accepts the same arguments as `compact_frontier.py`.
Non-XML artifacts are retained without invoking this tool.
