# Frozen Isabelle build dependencies

`afp-source.tar.gz` preserves the exact private AFP 2025-2 snapshot used for the
verified baseline: all 15,849 files, including theory headers and accompanying
metadata. `afp-files.json.gz` records each original file's size and SHA-256.
The archive is about 103 MB; it is a build dependency, separate from the compact
certificate suite. Keeping the complete snapshot avoids dependence on a mutable
AFP release directory or an incorrectly inferred Git revision.

`manifest.json` pins these assets and the required Isabelle2025-2 / GHC 9.6.7
versions. The two toolchain metadata files were captured before the builds.
Isabelle and GHC installations are external prerequisites; shared dependency
heaps are not required. Build into a private Isabelle user/output directory.

Verify archive hashes against `manifest.json`, extract AFP into a new private
directory, and set `AFP` to its `thys` subdirectory. Keep this source path stable
across incremental milestones. Never replace an AFP directory while a build is
reading it, and never rebuild another worktree's heaps in place.
