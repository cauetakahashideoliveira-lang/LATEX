#!/bin/bash
# Reinstala Lean 4.35.0 + Mathlib (cache pré-compilado) numa sessão nova.
# Uso, a partir da raiz do repositório:  bash verificacao-lean/instalar.sh
# Download: ~0,9 GB (Lean) + alguns GB (cache do Mathlib, de cache.mathlib.org).
# O `elan toolchain install` não funciona neste ambiente (o proxy bloqueia a
# página releases/expanded_assets do GitHub), então o Lean é baixado direto do
# release oficial e posto onde o elan o procura.
set -euo pipefail
V=4.35.0
command -v elan >/dev/null 2>&1 || { apt-get update -qq; apt-get install -y -qq --no-install-recommends elan; }
TC="$HOME/.elan/toolchains/leanprover--lean4---v$V"
if [ ! -x "$TC/bin/lean" ]; then
  T=$(mktemp -d)
  curl -sSfL -o "$T/lean.zip" "https://github.com/leanprover/lean4/releases/download/v$V/lean-$V-linux.zip"
  unzip -q "$T/lean.zip" -d "$T"
  mkdir -p "$HOME/.elan/toolchains"
  mv "$T/lean-$V-linux" "$TC"
  rm -rf "$T"
fi
elan default "leanprover/lean4:v$V"
cd "$(dirname "$0")"
lake exe cache get
lake build
