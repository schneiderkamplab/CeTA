# Layered Isabelle builds

The proof checker is split into persistent Isabelle heaps so that CSR
development does not rebuild the complete checker after every edit.

| Target | Contents | Use |
| --- | --- | --- |
| `Proof_Checker_Base` | Generic termination checker | Stable dependency heap |
| `CSR_Checker_Base` | Stable CSR definitions and soundness lemmas | Rebuild after foundational CSR changes |
| `CSR_Checker_Core` | CSR proof driver and recursive graph checking | Default target while editing CSR processors |
| `CSR_Checker_Extensions` | Minimal, improved, and conservative CSDP theories | Validate CSR extension changes |
| `Proof_Checker` | Parsers, verifier, and complete checker | Final certification gate |

Use the same Isabelle options between builds because options are part of the
heap identity. For this workspace:

```sh
export AFP=/work/dfm/festschrift/ferrum/.tools/afp-current/thys
export ISABELLE=/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle

make isabelle-csr-core
make isabelle-csr-extensions
make isabelle-proof-checker
```

`ISABELLE_JOBS` defaults to 16 and can be overridden. The core target is the
normal edit/test loop. Run the full checker before exporting generated code or
claiming certification.

Measured on 2026-07-26 after warming the dependency heaps:

- `CSR_Checker_Core`: 39 seconds with standard options.
- `CSR_Checker_Extensions`: 13 seconds with the core cached.
- `Proof_Checker`: 3 minutes 7 seconds for the full production gate.

## Temporary feature layers

For a new checker feature, do not iterate through `Proof_Checker` and `Code`.
Create a temporary `ROOT` under `target/` with three uniquely named sessions:

1. an extension-baseline session containing the unchanged extension theories;
2. a semantic child session containing only the new definitions and soundness
   theorem;
3. an executable child session containing the processor/checker adapter.

Build these sessions with a dedicated `ISABELLE_IDENTIFIER` and identical
thread/options settings.  Edits to executable plumbing then reuse both cached
parent heaps, while edits to the semantic theorem avoid rebuilding parsers and
code generation.  Never run two builds that write the same identifier.  Once
both temporary children pass, move the theories into the production session
and run the final gates exactly once:

```sh
isabelle build -d thys CSR_Checker_Extensions
isabelle build -d thys Proof_Checker Code
isabelle export -n -x 'Code.Code_Haskell:**' -O target/feature-export \
  -d "$AFP" -d thys Code
make haskell
```

The production checker and generated Haskell must always come from that final
production build, never directly from a temporary development heap.
