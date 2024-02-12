#!/usr/bin/env bash
set -euo pipefail

PROJECTS_HOME="$(dirname "$(realpath "$0")")"

check_z3() {
  expected_z3_version=$(grep -Po 'Z3 version \K\S*' "$PROJECTS_HOME/FStar/INSTALL.md")
  actual_z3_version=$(z3 --version | grep -Po 'Z3 version \K\S*')
  if [ "$expected_z3_version" != "$actual_z3_version" ]; then
    echo "Wrong Z3 version in PATH: $actual_z3_version (expected: $expected_z3_version)"
    exit 1
  fi
}

fstar_env() {
  cat <<EOF
export FSTAR_HOME="$PROJECTS_HOME/FStar";
export KRML_HOME="$PROJECTS_HOME/karamel";
export STEEL_HOME="$PROJECTS_HOME/steel";
export EVERPARSE_HOME="$PROJECTS_HOME/everparse";
export HACL_HOME="$PROJECTS_HOME/hacl-star";
export VALE_HOME="$PROJECTS_HOME/vale";
export EVERQUIC_HOME="$PROJECTS_HOME/everquic-crypto";
export MERKLE_HOME="$PROJECTS_HOME/merkle-tree";
export MITLS_HOME="$PROJECTS_HOME/mitls-fstar";
export ZETA_HOME="$PROJECTS_HOME/zeta";
export PATH="\$FSTAR_HOME/bin:\$PATH";
export OTHERFLAGS=--record_options;
EOF
}

build() {
  eval $(fstar_env)
  cd "$PROJECTS_HOME"
  set -x
  (cd FStar
    make $MAKEOPTS
    make $MAKEOPTS boot
    touch -r ocaml/_build/default/fstar/main.exe bin/fstar.exe # prevent useless rebuilds in HACL*
    )
  (cd steel; make $MAKEOPTS test)
  (cd karamel; make $MAKEOPTS)
  (cd FStar; make $MAKEOPTS -C examples)
  (cd everparse; make $MAKEOPTS)
  (cd hacl-star; ./tools/get_vale.sh; make $MAKEOPTS)
  (cd everquic-crypto; make $MAKEOPTS)
  (cd merkle-tree; make $MAKEOPTS)
  (cd mitls-fstar; make $MAKEOPTS -C src/tls model-all)
  (cd Armada; make $MAKEOPTS -C experimental/lib)
  (cd zeta; make $MAKEOPTS extract-all)
}

check_z3
MAKEOPTS="-j$(nproc)"

case "${1:-build}" in
  build) build ;;
  env) fstar_env ;;
  *) echo "Usage: ./build.sh (build|env)"; exit 1 ;;
esac
