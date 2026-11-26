#!/bin/bash
export PATH="$HOME/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
R=~/dzq-runs; touch $R/landed.txt $R/land-request.txt
while true; do
  L=$(grep -E '^[0-9a-f]{40}' $R/land-request.txt | tail -1); S=${L%% *}
  if [ -n "$S" ] && ! grep -q "^$S" $R/landed.txt; then
    D=$(grep -l "head ${S:0:8} " $R/w*-done 2>/dev/null | tail -1); OK=1; [ -n "$D" ] || OK=0
    if [ $OK = 1 ]; then grep -q 'nonstandard 0 \[\] no-sorry target-ok' $D || OK=0; for k in CHECK CHECKLR RENDER MKDOCS SITECHECK CONTRIB-BUILD CONTRIB-CHECK LEAVES ALLCONTRIB ONEPROOF-BUILD ONEPROOF-AX; do grep -q "^$k-EXIT=0" $D || OK=0; done; grep -q 'site: .*, 0 problem' $D || OK=0; grep -q 'OneProof.frozenTarget. depends on axioms: .propext, Classical.choice, Quot.sound.' $D || OK=0; fi
    cd ~/dzq && git fetch -q origin && git cat-file -e "$S^{commit}" 2>/dev/null || OK=0
    P=""
    if [ $OK = 1 ]; then
      if git merge-base --is-ancestor origin/main $S; then P=$S; else
        MB=$(git merge-base origin/main $S); CH=$(git diff --name-only $MB origin/main)
        if [ -n "$CH" ] && ! echo "$CH" | grep -qvE '(\.md$|^blueprint/|^\.github/|^CODEOWNERS|^contrib-upstream/|^docs/one-proof/(claims|volatile)\.tsv$)'; then
          T=$(git merge-tree --write-tree $S origin/main 2>/dev/null) && [ -z "$(git diff --name-only $S $T | grep -vxF "$CH")" ] && P=$(git commit-tree $T -p $S -p origin/main -m "Merge fork main (docs only) into ${S:0:8}")
        fi
      fi
    fi
    if [ -n "$P" ] && git push -q origin $P:main; then echo "$S $(date +%m-%d_%H:%M) LANDED main=$P $D | $L" >> $R/landed.txt; else echo "$(date +%m-%d_%H:%M) SKIP $S ok=$OK D=$D" >> $R/autoland-skips.txt; echo "$S SKIPPED $(date +%m-%d_%H:%M)" >> $R/landed.txt; fi
  fi
  sleep 120
done
