#!/bin/bash
# importers.sh MODULE : vendored (non-Backport) files importing MODULE, restricted to the KW closure list /tmp/kwloc.txt
m=$1
grep -rlE "^(public )?import (all )?$m\$" ZInQKernel/Contrib/TauCeti | while read f; do mm=$(echo ${f%.lean} | tr / .); grep -qx $mm /tmp/kwloc.txt && echo "IN-CLOSURE $mm" || echo "outside $mm"; done
