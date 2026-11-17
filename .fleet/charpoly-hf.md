# charpoly-hf (2026-11-16)

**Verdict: −1 with no new leaf is not reachable. The deliverable is a verified count-neutral swap.**

- **What the reroute needs.** At FrobTraceLink's characteristic-`p` abelian variety, charpoly-charp's argument reads
  exactly one fact. For the one endomorphism `α'`, the polynomials over `ℚ_ℓ` killing `V_ℓ(α')` are the multiples of
  one monic `m ∈ ℚ[X]`, for every `ℓ ≠ p`. This is `CharpolyHF.MinpolyIndepOfEllCharP`. `common_trace`, its two
  consumers and `linkedTateData_of_local_minpolyCharP` are proved from it plus I3.M0 (Lean, standard axioms).
- **Why the listed inputs are not enough.** Faithfulness, divisibility, `T_ℓ` free of rank 4, integrality of `α'`
  and G8's `M ⊕ M` structure do not imply that fact. There is an explicit model (`ℚ(ζ₈)`, report §3) where all of
  them hold and the traces at 3 and 5 differ. The missing ingredient is discreteness: `ℚ[α'] ∩ End(Ā)` finitely
  generated, which comes from the polynomiality of `deg`. No bundle field and no proved tree result gives it in
  characteristic `p`.
- **The input as a leaf.** `MinpolyIndepOfEllCharP` is not printed form; it is a consequence of Mumford §19 Thm 3.
  The implication from `HomFreeFiniteAlgClosedCharP` (Thm 3 printed form, `k` algebraically closed of
  characteristic `p`) plus I3.M0 is compiled.
- **The fold** (`scratch/charpoly-hf/fold_edit.py`, `fold.patch`, `fold-docs.patch`; to be applied by the lead).
  It replaces `charPolyIndepOfEllAlgClosed` (Thm 4) by `homFreeFiniteAlgClosedCharP` (Thm 3, characteristic `p`),
  and R16 uses the characteristic-0 proof. Count unchanged: 40 open hypotheses, 33 H, strictest 13/20.
- **Checks run on a copy of the tree, all passing:** Main builds, `frozenTarget` uses only the standard axioms,
  FoldCheck (closure free of T7, T6, `HomFreeFiniteAlgClosed` and `sorryAx`), the hash guard, the blueprint-target
  check, OpenStatements, `render_open --check` and the crosswalk check. It also composes with fold33-combine (built
  and checked).
- **New Lean** (all build): `ZInQKernel/Contrib/OneProof/MinpolyIndepCharP.lean`, `MinpolyIndepCharPThm3.lean`, plus
  verbatim copies of `CharPolyLattice.lean` and `R16PrintedC.lean` from wip/charpoly-charp.
- **Not done:** autoform is not installed here (a substitute check found no blueprint target deleted). The blueprint
  page `characteristic-polynomial.md` still targets `OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed`, which is now
  off the route and should be retargeted if the swap is applied. The split into P-fg, P-div and P-faith is described
  in the report but not formalized.
- **Report:** `docs/research/charpoly-hf.md`.
