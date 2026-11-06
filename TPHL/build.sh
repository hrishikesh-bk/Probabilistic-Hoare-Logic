#!/bin/sh
# Compile the TPHL development with its own opam switch in TPHL/.toolchain
# (Rocq 9.0.0, MathComp 2.6.0, MathComp-Analysis 1.18.0; exact package set
# in toolchain.export). Create the switch once with:
#   opam switch create "$PWD/.toolchain" --empty
#   opam switch import toolchain.export --switch "$PWD/.toolchain"
# Override the switch location with TPHL_SWITCH=/path/to/switch.
set -e
cd "$(dirname "$0")"
SW=${TPHL_SWITCH:-$PWD/.toolchain}
ROCQ="$SW/_opam/bin/rocq"
export OCAMLPATH="$SW/_opam/lib"
export ROCQLIB="$SW/_opam/lib/coq"
export COQLIB="$SW/_opam/lib/coq"
FILES=${*:-$(grep '\.v$' _CoqProject)}
for f in $FILES; do
  echo "== $f"
  "$ROCQ" compile -q -w -notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-redundant-canonical-projection -Q . "" "$f"
done
