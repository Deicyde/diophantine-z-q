# fold-b115 (2026-11-17)

**Verdict: all three items are in, built and checked. The count is unchanged at 5/24 on 29 strict, 30 open, and no
manuscript step was found to be an error.** The branch is 1496913c plus this task's commits, so wip/leaf-fold33b can
fast-forward to it. Report: docs/research/fold-b115.md. Log: scratch/fold-b115/log.md. Replay:
scratch/fold-b115/REPLAY.md.

**What was folded:**
1. **ss-faltings.** `sga7_IX_Cor3_3_Def34` is replaced by `faltingsSemistableHeightBC` (Faltings 1983 §1, GLUE,
   pending reading). This is a bypass: TailZ84, with `sixContactMin_of_open77` on `OpenResearchLeaves58`.
   - Two changes from the branch as delivered:
     - the default names (`...open77sf`, `...58SF`) broke autofold's parser and so gate.sh, so the fold uses numeric
       names;
     - the generated chain SSFChain moved from Contrib to OneProof/H, because in Contrib `#discharges` listed 231
       self-matches.
   - No SGA 7 IX Cor. 3.3 statement is left in the closure. IX 3.5 (d2a6b) remains.
2. **Tau Ceti pin lines.** The Map.lean `simp` line, the Polynomial.lean `rw [ite_eq_right ...]` line and the Sylow
   line split are applied. Both pin lines compile, and the full OneProof chain rebuilds (about 20 min).
   - The diff count against 86b92544 could not be computed: the pin's source is not on this host.
   - Measured against the integrator's list, 0 code differences remain.
   - Two layout points are UNVERIFIED: the Sylow line break and Map.lean's comment wrapping.
3. **pb-dimform + htmult-model.** The queue29 rows are applied with inbox 75's amendment; panPrintedF's kind became
   consequence in the same commit as its flag. The field docstrings were edited in TailZ83 and TailZ84. The dimension
   form is now in the closure and the basis form is out.
   - htmult-model was cherry-picked rather than merged, because its branch also merges main's blueprint changes.

**What compiles** (VERIFIED after each item): Main, Discharges and the touched modules build.
- `frozenTarget` uses only the standard axioms.
- Hash guard: only `frozenTarget` changed, in item 1; items 2 and 3 changed nothing.
- No `sorryAx`. OpenStatements gives 30.
- render_open, crosswalk and both `--check` runs pass. DischargesTest was rerun, the autoform check passes, and gate.sh
  gives GATE=ok.

**What remains (lead):**
- **HTModel cannot go into AllContrib on this base.** The pre-existing clash on `PkgI6.TraceContainsRamificationIdx`
  between Contrib/Different/Local and HDecomp/Textbook/Different makes the import fail. Add the line after
  wip/contrib-clashes is folded (`field_docs_q29.py --allcontrib`).
- **d2a6b** must be regenerated on this top (TailZ84 / `open77` / `OpenResearchLeaves58`; the next free number is
  TailZ85), and its chain should go under OneProof/H.
- The older TailZ77-82 docstring copies were not regenerated, so they still say "basis form".
