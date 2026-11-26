#!/bin/bash
# usage: chain.sh N REF
# Full landing chain for origin/REF (fetched here, so run it from a tmux window, where git fetch works).
# Builds REF in ~/dzq-check2, one Lean job at a time (each in a MEMMAX systemd scope; 16 threads, or 4 when a host task runs Lean), and writes
# ~/dzq-runs/wN-done atomically at the end. Each autoland key appears exactly once; when a key covers several
# sub-checks its value is the largest sub-exit and a "<KEY>-PARTS" line lists them. Logs: ~/dzq-runs/wN/.
# Stages: lake build ZInQKernel; print_axioms + check_target; every Contrib module; contrib-check; AllContrib;
# Leaves.lean; OneProof Main + Discharges; frozenTarget axioms; OpenStatements.json regeneration; the repo's Python
# checks (CI's research-checks and pr-guard steps that run here); Blueprint Pages steps at the CI autoform pin.
# Not run here: scripts/check_construction.py (needs Node.js 22, not installed), scripts/build_paper.py,
# check_lean.py --build (CI's fresh helper rebuild).
export PATH="$HOME/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
N="$1"; REF="$2"
[ -n "$N" ] && [ -n "$REF" ] || { echo "usage: chain.sh N REF"; exit 2; }
R=$HOME/dzq-runs; C=$HOME/dzq-check2; D=$R/w$N; OUT=$R/w$N-done
AF="git+https://github.com/facebookresearch/autoform-bot.git@46b46d6defaa19c618341e05c4cc0d819072a03d"
exec 9> "$R/chain.lock"
flock -n 9 || { echo "another chain holds $R/chain.lock"; exit 1; }
mkdir -p "$D"; rm -f "$OUT" "$OUT.tmp"
T0=$(date +%s)
note() { echo "$(date +%m-%d_%H:%M:%S) $*" >> "$D/progress.txt"; }
# One Lean/lake job, foreground, capped (MEMMAX, default 60G). When a Lean/lake/repl process that is not this
# chain's (not in ~/dzq-check2) runs on the host, the job gets LEAN_NUM_THREADS=4 and CPUQuota=1600%, else 16 threads.
MEMMAX=${MEMMAX:-60G}
foreign() { local p a c; for p in $(pgrep -x lean; pgrep -x lake; pgrep -x repl); do
  a=$(tr '\0' ' ' < /proc/$p/cmdline 2> /dev/null); c=$(readlink /proc/$p/cwd 2> /dev/null)
  case "$a $c" in *"$HOME/dzq-check2"*) ;; *) [ -n "$a" ] && return 0 ;; esac; done; return 1; }
L() { if foreign; then note "  (host task Lean running: 4 threads, CPUQuota=1600%) $*"
    systemd-run --user --scope -q -p MemoryMax=$MEMMAX -p CPUQuota=1600% env LEAN_NUM_THREADS=4 "$@"
  else note "  (16 threads) $*"; systemd-run --user --scope -q -p MemoryMax=$MEMMAX env LEAN_NUM_THREADS=16 "$@"; fi; }
# 0 if every "depends on axioms" list in the file is standard and nothing mentions sorry, else 1.
axok() { python3 -I -c '
import sys
t = " ".join(open(sys.argv[1]).read().split()); std = {"propext", "Classical.choice", "Quot.sound"}
bad = [s for s in t.split("depends on axioms:")[1:] if not {a.strip() for a in s.split("]")[0].strip().lstrip("[").split(",")} <= std]
print(1 if bad or "sorry" in t else 0)' "$1" 2> /dev/null || echo 1; }
max() { local m=0 x; for x in "$@"; do [ "$x" -gt "$m" ] 2> /dev/null && m=$x; [[ "$x" =~ ^[0-9]+$ ]] || m=99; done; echo $m; }

note "chain w$N for $REF starts"
git -C "$HOME/dzq" fetch -q origin || { note "fetch failed"; exit 1; }
SHA=$(git -C "$HOME/dzq" rev-parse "origin/$REF^{commit}") || { note "no origin/$REF"; exit 1; }
[ -d "$C" ] || git -C "$HOME/dzq" worktree add -q --detach "$C" "$SHA"
cd "$C" || exit 1
for d in site-src site; do test -e "$d" && mv "$d" "$D/$d.old.$(date +%s)"; done
git checkout -q -f --detach "$SHA" || { note "checkout failed"; exit 1; }
git status --porcelain > "$D/dirty-at-start.txt"
note "checked out $(git log --oneline -1 | cut -c1-90)"

# 1. lake build ZInQKernel
note "build ZInQKernel"
{ date; L lake build ZInQKernel; echo "EXIT=$?"; date; } > "$D/build.log" 2>&1
E_BUILD=$(sed -n 's/^EXIT=//p' "$D/build.log" | tail -1)

# 2. print_axioms + check_target
note "print_axioms"
{ echo "$SHA"; L lake env lean scripts/print_axioms.lean; echo "PRINTAX-EXIT=$?"; python3 scripts/check_target.py; echo "TARGET-EXIT=$?"; } > "$D/axioms-w$N.txt" 2>&1
E_PRINTAX=$(sed -n 's/^PRINTAX-EXIT=//p' "$D/axioms-w$N.txt"); E_TARGET=$(sed -n 's/^TARGET-EXIT=//p' "$D/axioms-w$N.txt")

# 3. every module under ZInQKernel/Contrib
note "contrib build"
git ls-files 'ZInQKernel/Contrib/*.lean' | sed 's#[.]lean$##; s#/#.#g' > "$D/contrib-modules.txt"
{ date; echo "modules $(wc -l < "$D/contrib-modules.txt")"; L lake build $(cat "$D/contrib-modules.txt"); echo "EXIT=$?"; date; } > "$D/contrib-build.log" 2>&1
E_CB=$(sed -n 's/^EXIT=//p' "$D/contrib-build.log" | tail -1)

# 4. contrib-check
note "contrib check"
{ L lake env lean scratch/contrib-check/Check.lean; echo "EXIT=$?"; } > "$D/contrib-check.log" 2>&1
E_CC=$(sed -n 's/^EXIT=//p' "$D/contrib-check.log" | tail -1)
E_CCAX=$(axok "$D/contrib-check.log")

# 5. AllContrib (co-import of the Contrib modules)
note "allcontrib"
{ L lake build ZInQKernel.Contrib.AllContrib; echo "EXIT=$?"; } > "$D/allcontrib.log" 2>&1
E_AC=$(sed -n 's/^EXIT=//p' "$D/allcontrib.log" | tail -1)

# 6. Leaves.lean
note "leaves"
{ L lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant 2>&1 | tail -2; echo "PRE-EXIT=${PIPESTATUS[0]}"; } > "$D/leaves-pre.log" 2>&1
E_LPRE=$(sed -n 's/^PRE-EXIT=//p' "$D/leaves-pre.log")
L lake env lean scratch/h-decomposition/Leaves.lean > "$D/leaves.log" 2>&1; E_LV=$?
E_LVAX=$(axok "$D/leaves.log")

# 7. OneProof targets (as CI's main build cache)
note "oneproof build"
{ date; L lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges; echo "EXIT=$?"; date; } > "$D/oneproof-build.log" 2>&1
E_OB=$(sed -n 's/^EXIT=//p' "$D/oneproof-build.log" | tail -1)

# 8. frozenTarget axioms (CI's probe and checker)
note "oneproof axioms"
printf '%s\n' 'import ZInQKernel.OneProof.Main' '#print axioms ZInQ.OneProof.frozenTarget' > "$D/FrozenTargetAxioms.lean"
L lake env lean "$D/FrozenTargetAxioms.lean" > "$D/frozen-target-axioms.txt" 2>&1; E_OAL=$?
python3 -I scripts/one_proof/check_axioms.py "$D/frozen-target-axioms.txt" > "$D/check-axioms.txt" 2>&1; E_OAC=$?

# 8b. extra Lean files named by the inbox entry (EXTRA_LEAN, space-separated paths): each must exit 0 with no
# "error" line and only standard axioms; folded into CHECK-EXIT.
E_EXTRA=0; EXTRA_PARTS=""
for x in ${EXTRA_LEAN:-}; do
  k=$(basename "$x" .lean); note "extra $x"
  L lake env lean "$x" > "$D/extra-$k.log" 2>&1; e=$?
  grep -q ': error' "$D/extra-$k.log" && [ $e = 0 ] && e=97
  a=$(axok "$D/extra-$k.log"); grep -q 'depends on axioms' "$D/extra-$k.log" || a=0
  EXTRA_PARTS="$EXTRA_PARTS $k=$e/ax$a"; E_EXTRA=$(max "$E_EXTRA" "$e" "$a")
done

# 9. open-statements.json regenerated from the build must equal the committed one
note "open statements"
{ L lake env lean scripts/one_proof/OpenStatements.lean; echo "GEN-EXIT=$?"; git diff --stat --exit-code -- docs/one-proof/open-statements.json; echo "DIFF-EXIT=$?"; } > "$D/open-statements.log" 2>&1
E_OSG=$(sed -n 's/^GEN-EXIT=//p' "$D/open-statements.log"); E_OSD=$(sed -n 's/^DIFF-EXIT=//p' "$D/open-statements.log")
NOPEN=$(python3 -c "import json,sys; d=json.load(open(sys.argv[1])); print(len(d) if isinstance(d,list) else len(d.get('hypotheses', d)))" docs/one-proof/open-statements.json 2>/dev/null || echo '?')
git checkout -q -- docs/one-proof/open-statements.json

# 10. the repo's Python checks
note "python checks"
py() { local k=$1; shift; "$@" > "$D/py-$k.log" 2>&1; echo "$k=$?"; }
PY=$(
  py render_open python3 scripts/one_proof/render_open.py --check
  py test_scoring python3 -I scripts/one_proof/test_scoring.py
  py claims_tests python3 -I -m unittest discover -s scripts/claims -p 'test_*.py'
  py check_lean python3 scripts/check_lean.py
  py inventory python3 docs/theorem-application-audit/validate.py
  PR_BODY="$(git log --format=%B "origin/main..$SHA")" py guard_rows python3 scripts/guard/check_pr.py rows --base origin/main
)
pv() { echo "$PY" | sed -n "s/^$1=//p"; }

# 10b. roadmap drift check (not in CI; report only)
python3 scripts/roadmap/check_current.py > "$D/roadmap.log" 2>&1; E_ROAD=$?

# 11. Blueprint Pages steps (autoform at the CI pin)
note "site"
{
  echo "$SHA"
  uvx --from "$AF" autoform check blueprint; echo "AF-CHECK-EXIT=$?"
  help="$(uvx --from "$AF" autoform check --help 2>&1)"; case "$help" in *--no-site-warnings*) ltr=--no-site-warnings ;; *) ltr= ;; esac
  uvx --from "$AF" autoform check blueprint --lean-root . $ltr; echo "AF-CHECKLR-EXIT=$?"
  uvx --from "$AF" autoform audit blueprint --lean-root .; echo "AF-AUDIT-EXIT=$?"
  uvx --from "$AF" autoform render blueprint --output site-src --lean-root . --require-declarations --ref "$SHA"; echo "AF-RENDER-EXIT=$?"
  uvx --from mkdocs==1.6.1 --with mkdocs-material==9.7.7 --with mkdocs-literate-nav==0.6.2 --with markdown==3.10.3 --with pymdown-extensions==11.0.1 mkdocs build --strict; echo "AF-MKDOCS-EXIT=$?"
  if [ -f docs/companion/manuscript/pdf-overlay/tools/build_site.py ]; then
    ( set -e; python3 docs/companion/manuscript/pdf-overlay/tools/build_site.py; mkdir -p site/companion; cp -R docs/companion/manuscript/site/. site/companion/
      test -f site/companion/pdf-overlay/viewer/index.html; test -z "$(find site/companion -name '*.pdf' -print -quit)" ); echo "AF-MANUSCRIPT-EXIT=$?"
  else echo "AF-MANUSCRIPT-EXIT=0 (absent)"; fi
  uvx --from "$AF" autoform site check site --source site-src; echo "AF-SITECHECK-EXIT=$?"
} > "$D/site.txt" 2>&1
sv() { sed -n "s/^AF-$1-EXIT=\([0-9]*\).*/\1/p" "$D/site.txt" | tail -1; }
SITELINE=$(grep -E '^site: ' "$D/site.txt" | tail -1)

# 12. assemble
[ "$(git rev-parse HEAD)" = "$SHA" ] || { note "check2 HEAD moved during the chain"; E_BUILD=98; }
git diff --quiet || { git status --porcelain | head > "$D/dirty-at-end.txt"; }
CHECK=$(max "$E_BUILD" "$E_PRINTAX" "$E_TARGET" "$(sv CHECK)" "$(pv test_scoring)" "$(pv claims_tests)" "$(pv check_lean)" "$(pv inventory)" "$(pv guard_rows)" "$E_EXTRA")
RENDER=$(max "$(sv RENDER)" "$(pv render_open)" "$E_OSG" "$E_OSD")
MKDOCS=$(max "$(sv MKDOCS)" "$(sv MANUSCRIPT)")
LEAVES=$(max "$E_LPRE" "$E_LV" "$E_LVAX")
OAX=$(max "$E_OAL" "$E_OAC")
FROZEN=$(tr '\n' ' ' < "$D/frozen-target-axioms.txt" | tr -s ' ' | grep -o "'ZInQ.OneProof.frozenTarget' depends on axioms: \[[^]]*\]")
{
  echo "head ${SHA:0:8} $SHA $REF w$N"
  echo "CHECK-EXIT=$CHECK"
  echo "CHECK-PARTS: build-ZInQKernel=$E_BUILD print_axioms=$E_PRINTAX check_target=$E_TARGET autoform-check=$(sv CHECK) test_scoring=$(pv test_scoring) claims_tests=$(pv claims_tests) check_lean=$(pv check_lean) inventory=$(pv inventory) guard_rows=$(pv guard_rows) extra=$E_EXTRA"
  [ -n "$EXTRA_PARTS" ] && echo "EXTRA-PARTS:$EXTRA_PARTS"
  echo "roadmap check_current (report only): exit $E_ROAD"
  echo "CHECKLR-EXIT=$(max "$(sv CHECKLR)")"
  echo "RENDER-EXIT=$RENDER"
  echo "RENDER-PARTS: autoform-render=$(sv RENDER) render_open-check=$(pv render_open) open-statements-gen=$E_OSG open-statements-diff=$E_OSD"
  echo "MKDOCS-EXIT=$MKDOCS"
  echo "MKDOCS-PARTS: mkdocs-strict=$(sv MKDOCS) manuscript=$(sv MANUSCRIPT)"
  echo "SITECHECK-EXIT=$(max "$(sv SITECHECK)")"
  echo "${SITELINE:-site: line missing}"
  echo "audit (report only): exit $(sv AUDIT)"
  echo "CONTRIB-BUILD-EXIT=$(max "$E_CB")"
  echo "CONTRIB-BUILD-INFO: $(sed -n 's/^modules /modules /p' "$D/contrib-build.log"); $(grep -E 'Build completed|jobs' "$D/contrib-build.log" | tail -1)"
  echo "CONTRIB-CHECK-EXIT=$(max "$E_CC" "$E_CCAX")"
  echo "CONTRIB-CHECK-PARTS: lean=$E_CC axioms-standard-no-sorry=$E_CCAX ($(grep -c 'depends on axioms' "$D/contrib-check.log") axiom reports)"
  echo "LEAVES-EXIT=$LEAVES"
  echo "LEAVES-PARTS: pre-build=$E_LPRE lean=$E_LV axioms-standard-no-sorry=$E_LVAX"
  echo "LEAVES-INFO: errors=$(grep -c 'error' "$D/leaves.log") sorry-warnings=$(grep -c 'declaration uses .sorry' "$D/leaves.log") sorryAx=$(grep -c 'sorryAx' "$D/leaves.log")"
  echo "ALLCONTRIB-EXIT=$(max "$E_AC")"
  echo "ONEPROOF-BUILD-EXIT=$(max "$E_OB")"
  echo "ONEPROOF-BUILD-INFO: $(grep -E 'Build completed' "$D/oneproof-build.log" | tail -1)"
  echo "ONEPROOF-AX-EXIT=$OAX"
  echo "${FROZEN:-frozenTarget axioms line missing}"
  python3 "$R/axcheck.py" "$D/axioms-w$N.txt"
  echo "open hypotheses in regenerated open-statements.json: $NOPEN"
  echo "chain minutes: $(( ($(date +%s) - T0) / 60 ))"
} > "$OUT.tmp" 2>&1
mv "$OUT.tmp" "$OUT"
note "chain w$N done"
echo "CHAIN-W$N-DONE"
