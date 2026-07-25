#!/usr/bin/env bash
#
# run_manifest.sh
# ===============
# Emit the provenance manifest that Section 10 (items 1-3) requires the
# exhaustive run to be archived with:
#
#   1. the tagged commit / release the binaries were built from;
#   2. compiler, version, flags, operating system and architecture;
#   3. checksums of the source, executable and output files.
#
# Run it TWICE: once right after building (records commit, toolchain, source
# and executable checksums) and once after the run completes (adds output-file
# checksums and the summary line). It appends, so both snapshots are kept.
#
# Usage:
#   ./run_manifest.sh                       # writes/*appends* results/run_manifest.txt
#   ./run_manifest.sh --out FILE            # custom path
#   BUILD_FLAGS="-O2 -std=c++17 -fopenmp" ./run_manifest.sh   # record the flags you used
#
# It records the flags from $BUILD_FLAGS if set (so pass the same string you
# built with); otherwise it notes them as UNRECORDED and you should fill them in.

set -euo pipefail

OUT="results/run_manifest.txt"
if [[ "${1:-}" == "--out" && -n "${2:-}" ]]; then OUT="$2"; fi
mkdir -p "$(dirname "$OUT")"

SUM=sha256sum
command -v sha256sum >/dev/null 2>&1 || SUM="shasum -a 256"   # macOS fallback

{
  echo "================================================================"
  echo "RUN MANIFEST  ($(date -u '+%Y-%m-%dT%H:%M:%SZ') UTC)"
  echo "================================================================"

  echo
  echo "-- [1] Source revision --"
  if command -v git >/dev/null 2>&1 && git rev-parse --git-dir >/dev/null 2>&1; then
    echo "commit:      $(git rev-parse HEAD)"
    echo "tag/describe: $(git describe --tags --always --dirty 2>/dev/null || echo '(no tag)')"
    echo "branch:      $(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo '?')"
    if ! git diff --quiet 2>/dev/null; then
      echo "WORKING TREE: DIRTY  <-- commit/stash before an archival run"
    else
      echo "working tree: clean"
    fi
  else
    echo "(not a git checkout -- record the release tag manually)"
  fi

  echo
  echo "-- [2] Toolchain, OS, architecture --"
  echo "os/kernel:   $(uname -srmo 2>/dev/null || uname -a)"
  echo "hostname:    $(uname -n)"
  if command -v lscpu >/dev/null 2>&1; then
    echo "cpu:         $(lscpu | awk -F: '/Model name/{gsub(/^ +/,"",$2);print $2; exit}')"
    echo "cores/threads: $(nproc) logical"
  else
    echo "cpu:         $(uname -m)"
  fi
  echo "OMP_NUM_THREADS: ${OMP_NUM_THREADS:-(unset -> OpenMP default = all cores)}"
  echo
  CXX="${CXX:-g++}"
  echo "compiler:    $CXX"
  if command -v "$CXX" >/dev/null 2>&1; then
    echo "version:     $($CXX --version | head -1)"
  else
    echo "version:     ($CXX not found on PATH)"
  fi
  echo "build flags: ${BUILD_FLAGS:-UNRECORDED  <-- set BUILD_FLAGS to the exact flags you compiled with}"
  echo "backend of record: default (deterministic Miller-Rabin, 12 Sorenson-Webster bases; unconditional)."
  echo "                   -DUSE_BPSW builds are conjectural cross-checks, NOT results of record."

  echo
  echo "-- [3a] Source + header checksums --"
  for f in verify_odd.cpp verify_even.cpp verify_large_prime.cpp prime64.hpp verify_results.py; do
    [[ -f "$f" ]] && $SUM "$f" || echo "MISSING  $f"
  done

  echo
  echo "-- [3b] Executable checksums --"
  found_exe=0
  for f in verify_odd verify_even verify_large_prime; do
    if [[ -f "$f" ]]; then $SUM "$f"; found_exe=1; fi
  done
  [[ $found_exe -eq 0 ]] && echo "(no executables present -- run this again after building)"

  echo
  echo "-- [3c] Output (results) checksums + summary --"
  shopt -s nullglob
  outs=( results/*.csv )
  if [[ ${#outs[@]} -eq 0 ]]; then
    echo "(no results/*.csv yet -- run this again after the exhaustive run)"
  else
    for f in "${outs[@]}"; do
      lines=$(wc -l < "$f")
      ok=$(grep -c ',OK,' "$f" 2>/dev/null || echo 0)
      exc=$(grep -Ec ',EXCEPTION(S)?,' "$f" 2>/dev/null || echo 0)
      printf '%s\n' "$($SUM "$f")"
      printf '    rows=%s  OK=%s  exceptions=%s\n' "$lines" "$ok" "$exc"
    done
    echo
    echo "NOTE: run  python3 verify_results.py --sample 500  to cross-check coverage,"
    echo "      exact count, and re-derived witnesses independently of the C++ code."
  fi

  echo
} >> "$OUT"

echo "Appended manifest snapshot to $OUT"
