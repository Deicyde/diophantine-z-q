#!/bin/sh
# args: mode j k depth
if [ "$1" = strict ]; then D=-1; else D=-1,-3,-5,-7; fi
r=$(timeout 2400 ./chain_search $2 $3 $4 $D $D 2>/dev/null | head -2 | tr "\n" " ")
echo "$1 $r"
