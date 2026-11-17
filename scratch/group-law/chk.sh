#!/bin/bash
# usage: gl_chk.sh file
cd "$(git rev-parse --show-toplevel)"; export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
timeout 1500 lake env lean "$1" > /tmp/gl_out.txt 2>&1
echo "exit $?"; grep -n "error" /tmp/gl_out.txt | head -40
