#!/usr/bin/env bash
# Rebuild only from checked Isabelle theories; never modify exported Haskell.
set -euo pipefail
if [[ $# != 1 ]]; then
  echo "Usage: $0 NEW_OUTPUT_DIRECTORY" >&2
  exit 2
fi
its_source=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
its_output=$(realpath -m "$1")
[[ ! -e "$its_output" ]] || { echo "Output already exists: $its_output" >&2; exit 2; }
its_isabelle=${ISABELLE_TOOL:-/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle}
its_ghc=${GHC:-ghc}
mkdir -p "$its_output"
export USER_HOME="${ITS_ISABELLE_USER_HOME:-$its_output/isabelle-user}"
export ISABELLE_IDENTIFIER="${ITS_ISABELLE_IDENTIFIER:-its_isolated}"
cd "$its_source"
"$its_isabelle" build -v -j2 -o threads=4 -o parallel_proofs=0 \
  -d thys -D thys/ITS_Ext ITS_Ext >"$its_output/isabelle-build.log" 2>&1
"$its_isabelle" export -d thys -d thys/ITS_Ext -x '*:code/**' \
  -O "$its_output/export" ITS_Ext >"$its_output/export.log" 2>&1
its_generated="$its_output/export/ITS_Ext.ITS4_Parser/code/export1"
"$its_ghc" -O1 -i"$its_generated" -outputdir "$its_output/ghc" \
  -o "$its_output/ceta-its" thys/ITS_Ext/Main.hs >"$its_output/ghc-build.log" 2>&1
sha256sum "$its_output/ceta-its" "$its_generated"/*.hs >"$its_output/checksums.sha256"
git rev-parse HEAD >"$its_output/source-commit.txt"
git status --porcelain >"$its_output/source-status.txt"
git diff --binary >"$its_output/source.diff"
# Include untracked theories in the reproducible build identity as well.
python3 - "$its_output" <<'PY'
import hashlib, json, pathlib, sys
out = pathlib.Path(sys.argv[1])
paths = sorted(pathlib.Path('thys/ITS_Ext').rglob('*'))
paths += [pathlib.Path('scripts/build_its_checker.sh'), pathlib.Path('xml/lts4.xsd'), pathlib.Path('xml/cpf4.xsd')]
files = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths if p.is_file()}
(out / 'source-checksums.json').write_text(json.dumps(files, indent=2) + '\n')
PY
printf '%s\n' "$its_output/ceta-its"
