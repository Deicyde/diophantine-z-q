#!/bin/bash
# compile one vendored module (short name or path) and print errors
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
cd ~/dzq-wt/neron-flt
f=$1; [ -f "$f" ] || f=$(find ZInQKernel/Contrib/OneProof/NeronFLT -name "$1.lean" | head -1)
lake env lean "$f" 2>&1 | grep -v "^warning" | awk '/error/{p=1;c=0} p{print; c++; if(c>='${2:-12}'){p=0}}' | cut -c1-220
