#!/bin/bash
# triage2 probe runner: plain lean with the worktree's lake LEAN_PATH plus ~/dzq/lean/.lake (upstream ZInQ build,
# same lean/ZInQ tree hash 02e27597). Usage: scratch/triage2/run.sh scratch/triage2/File.lean
export PATH=$HOME/bin:$HOME/.elan/bin:$PATH
export LEAN_PATH="$(cat /home/jackmccarthy/dzq-wt/triage2/scratch/triage2/.leanpath)"
cd /home/jackmccarthy/dzq-wt/triage2 && lean "$1"
