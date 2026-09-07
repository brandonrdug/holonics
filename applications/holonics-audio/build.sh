#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
SDK=$(xcrun --sdk macosx --show-sdk-path)
mkdir -p "$ROOT/.build"
xcrun swiftc -O -parse-as-library -sdk "$SDK" \
  -framework Foundation -framework AVFoundation -framework CoreAudio -framework AudioToolbox \
  "$ROOT/main.swift" -o "$ROOT/.build/holonics-audio"
echo "$ROOT/.build/holonics-audio"
