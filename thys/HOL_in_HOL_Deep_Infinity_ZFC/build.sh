#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# Self-contained build for the companion session HOL_in_HOL_Deep_Infinity_ZFC.
#
# Runs from this session's own directory, so only this session's ROOT is read
# (not the repo-level ROOTS aggregate). Unlike the main entry, this session is
# NOT AFP-free: it depends on the AFP session ZFC_in_HOL and on the sibling
# session HOL_in_HOL_Deep.
#
#   AFP=~/GITHUBS/afp-devel/thys ISABELLE=/path/to/isabelle ./build.sh
# AFP must point at your AFP "thys" directory; ISABELLE defaults to the
# "isabelle" on PATH.
# NOTE: output/ holds build artifacts -- exclude it from any AFP zip.
# ---------------------------------------------------------------------------
set -euo pipefail
cd "$(dirname "$0")"

ISABELLE="${ISABELLE:-isabelle}"
AFP="${AFP:-$HOME/GITHUBS/afp-devel/thys}"

if [ ! -d "$AFP/ZFC_in_HOL" ]; then
  echo "error: AFP session ZFC_in_HOL not found under: $AFP" >&2
  echo "       set AFP to your AFP 'thys' directory, e.g." >&2
  echo "         AFP=~/afp/thys ./build.sh" >&2
  exit 1
fi

"$ISABELLE" build -c -v -o document_output=output \
  -d "$AFP" -d ../HOL_in_HOL_Deep -D .
echo "PDF written to: $(pwd)/output/document.pdf"
