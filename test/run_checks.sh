#!/usr/bin/env bash
# Run every offline check and leave its output under test/results/.
#
# Each log opens with the toolchain, the resolved dependency revisions and a fingerprint of
# the game sources, so a log can be matched to the tree it describes instead of being taken
# on trust. The browser tests live in test/play_levels.py and test/check_inventory_docs.py;
# they need a running server and are not run from here.
#
# check_names.py is the cheap stand-in for the part of the browser test that catches an
# unlocked name: that failure shows up in the browser as a level which simply never completes,
# while the proof itself elaborates and the info view reads "No goals".
#
# Usage: bash test/run_checks.sh
set -u
cd "$(dirname "$0")/.."
OUT=test/results
mkdir -p "$OUT"

fingerprint() {
  # A digest of everything that decides what the game contains.
  find Game images .i18n/en .i18n/zh -type f \
       \( -name '*.lean' -o -name '*.svg' -o -name '*.po' -o -name '*.pot' -o -name '*.csv' \) \
    | sort | xargs cat | sha256sum | cut -c1-16
}

header() {
  echo "# $1"
  echo "# run at        $(date -Is)"
  echo "# toolchain     $(cat lean-toolchain)"
  echo "# cslib         $(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='cslib'][0])")"
  echo "# GameServer    $(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='GameServer'][0])")"
  echo "# mathlib       $(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")"
  echo "# game sources  sha256:$(fingerprint)"
  echo
}

run() {
  local name="$1" log="$2" status; shift 2
  # Capture the check's status before anything else runs: `$?` after an `echo` is always 0.
  { header "$name"; "$@" 2>&1; status=$?; echo; echo "# exit $status"; } > "$OUT/$log"
  if [ "$status" -ne 0 ]; then
    echo "FAIL  $name  -> $OUT/$log"
    return 1
  fi
  echo "ok    $name  -> $OUT/$log"
}

rc=0
run "lake build (includes the MakeGame diagnostics)" lake-build.log lake build || rc=1
run "reference solutions use only Lean's standard axioms" check-axioms.log \
    python3 test/check_axioms.py || rc=1
run "world tree, inventory, level content and images" check-game.log \
    python3 test/check_game.py || rc=1
run "every name a reference proof mentions is unlocked" check-names.log \
    python3 test/check_names.py || rc=1
run "no unlocked one-liner closes a level" check-shortcuts.log \
    lake env lean test/Shortcuts.lean || rc=1
run "translation coverage, placeholders, assets, glossary" check-i18n.log \
    python3 .i18n/tools/check_i18n.py || rc=1

echo
if [ "$rc" -eq 0 ]; then echo "all offline checks passed"; else echo "some checks failed"; fi
exit "$rc"
