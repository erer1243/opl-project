#!/usr/bin/env bash

# Rust does a LOT of disk io when recompiling, even after very minor changes.
# This helps speed up that io by putting it into ram instead, and makes
# tests in high-level/hl.hs run significantly faster on my machine.

set -e
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd "$SCRIPT_DIR"

make_ramdisk() {
  echo "making low-level/target ramdisk"
  rm -rf target
  mkdir target
  sudo mount -t tmpfs opl-low-level-target target
}

if [ ! -e "./target" ]; then
  make_ramdisk
  exit
fi

MOUNTPOINT="$(stat --format="%m" ./target)"
REALPATH="$(realpath ./target)"

if [ "$MOUNTPOINT" != "$REALPATH" ]; then
  make_ramdisk
else
  echo "low-level/target is already a ramdisk"
fi
