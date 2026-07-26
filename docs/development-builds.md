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
