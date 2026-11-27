#!/bin/bash
# usage: request-when-green.sh N WORKTREE NOTE — wait for ~/dzq-runs/wN-done; if it is for WORKTREE's HEAD and every
# autoland key passed, append "<sha> NOTE" to land-request.txt and a log line; then wait for landed.txt. Prints the outcome.
R=~/dzq-runs; N=$1; W=$2; NOTE=$3; S=$(git -C "$W" rev-parse HEAD)
for i in $(seq 720); do [ -e $R/w$N-done ] && break; tmux list-windows -t dioph | grep -q "chain-w$N" || { sleep 5; [ -e $R/w$N-done ] || { echo CHAIN-GONE; exit 1; }; }; sleep 10; done
D=$R/w$N-done; OK=1
grep -q "head ${S:0:8} " $D || OK=0
grep -q 'nonstandard 0 \[\] no-sorry target-ok' $D || OK=0
for k in CHECK CHECKLR RENDER MKDOCS SITECHECK CONTRIB-BUILD CONTRIB-CHECK LEAVES ALLCONTRIB ONEPROOF-BUILD ONEPROOF-AX; do grep -q "^$k-EXIT=0" $D || OK=0; done
grep -q 'site: .*, 0 problem' $D || OK=0
grep -q 'OneProof.frozenTarget. depends on axioms: .propext, Classical.choice, Quot.sound.' $D || OK=0
if [ $OK != 1 ]; then echo NOT-GREEN; grep -E 'EXIT=[1-9]|PARTS' $D; exit 2; fi
M=$(grep -o 'open hypotheses in regenerated open-statements.json: [0-9]*' $D | grep -o '[0-9]*$')
echo "$S $NOTE" >> $R/land-request.txt
echo "$(date +%m-%d_%H:%M) chain w$N RESULT on ${S:0:9} ($(grep -o 'base-main [0-9a-f]*' $D), $(grep -o 'chain minutes: [0-9]*' $D)): every stage passed (frozenTarget standard, nonstandard 0, $M open); requested $S" >> $R/lead-log.md
for i in $(seq 30); do grep -q "^$S" $R/landed.txt && break; sleep 10; done
grep "^$S" $R/landed.txt | cut -c1-140 || echo NOT-YET-LANDED
