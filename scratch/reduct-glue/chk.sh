#!/bin/bash
# compile a scratch file importing ReductSplitBase from /tmp/rglib
cd ~/dzq-wt/reduct-glue; export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
lake env bash -c 'LEAN_PATH=/tmp/rglib:$LEAN_PATH lean "$@"' _ "$@" 2>&1 | grep -v "^warning\|deprecated\|^Hint\|^  [a-zA-Z̵]*$\|linter\|^Note" 
