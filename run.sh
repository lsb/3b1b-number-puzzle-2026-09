#!/bin/sh
# Usage:
#   ./run.sh prove              re-check both Lean files and list the axioms they use
#   ./run.sh multiplier N...    find multipliers for each N
set -e
cd "$(dirname "$0")"

case "$1" in
  prove)
    for f in OnesZeros.lean OnesZerosMathlib.lean; do
      echo "Checking $f"
      lake env lean "$f"
    done
    lake build -q OnesZeros OnesZerosMathlib
    axioms="$(lake env lean Axioms.lean)"
    echo "$axioms"
    if echo "$axioms" | grep -q sorryAx; then
      echo "FAILED: a proof uses sorry" >&2
      exit 1
    fi
    echo "All proofs check."
    ;;
  multiplier)
    shift
    exec python3 find_multiplier.py "$@"
    ;;
  *)
    sed -n '2,4p' "$0" | sed 's/^# //'
    exit 2
    ;;
esac
