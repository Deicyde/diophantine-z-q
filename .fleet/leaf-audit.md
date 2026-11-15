# leaf-audit (2026-11-15)

**Verdict: `LinYangEx29All` (theta-fold) is false. The other 15 leaves of 11-15 pass.** Details:
docs/research/leaf-audit.md.

**The false leaf.**
- It quantifies over every continuous `j₆ : ℍ → ℂ ∪ {∞}` that:
  - has the `Γ*`-orbits as fibres;
  - is surjective;
  - takes the values `0, ∞, −16/27` at the CM points.
- `conj ∘ j₆` meets all of these premises, but the conclusion `s₃² = z s₂³` is not conjugation-invariant.
- In Lean (`LeafAudit1115.not_linYangEx29All`, standard axioms), the leaf together with `IgusaThetaExpressions` and
  `QMHauptmodul` makes `j_θ = jNum/jDen ∘ Ω` real wherever `jDen ≠ 0`.
- But `j_θ(0.3+1.1i) = 4.2732 − 0.6831i` (40-digit evaluation of the Lean definitions; the CM values 0 and −16/27
  are reproduced).
- So theta-fold's hypotheses are inconsistent, and the leaf is advertised as an open LEAF (elliotglazer #86).

**The fix.** Use theta-fold's own existential `LinYangEx29`.
- It needs no `QMHauptmodul`.
- The corrected chain top compiles (`scratch/leaf-audit/FoldFix.lean`).
- With `j₆ = j_θ` its relations hold numerically to 1e-39.
- The spec is in `scratch/leaf-audit/autofold.json` (by-hand change).

**Integration finding.** theta-fold's `hθ` threading breaks leaf-fold25's `TailZ35` (line 117). theta-fold must be
re-folded on top of leaf-fold25.

**What compiles (VERIFIED).**
- `ZInQKernel/Contrib/OneProof/LeafAudit1115.lean`, built with `lake build`, standard axioms. Its helper
  `LeafAudit1115H29.lean` is a verbatim copy of h29-ne3's drop-in. The module contains:
  - the LinYang refutation;
  - non-vacuity instances:
    - `MumfordGroupLaw` at the trivial family;
    - `FaltingsTateSurj` at `A = B = 0`;
    - `X0ModuliGaloisMero` at `N = 1`, `τ = i`;
    - the TYZ leaves at `n = 3, 11`, from their sibling leaves;
    - Elkies' function-field premises, from its charts;
  - `TYZLemma29Printed ↔ TYZLemma29PrintedNe3 ∧ TYZThm21At31`;
  - pinned old/new implications for every leaf.
- `#discharges` was run against a temporary theta-fold-based `Main` (restored afterwards): no new discharge, as
  expected. The output is recorded.

**Numerics (VERIFIED).**
- Igusa's theta expressions on the diagonal: `E₄⊗E₄`, `E₆⊗E₆`, `0`, `Δ⊗Δ`.
- h29-fix's `brandt.py`, re-run: `Q(3) = ±3`, `Q(11) = Q(19) = ±1`.
- PARI for `C_5`, `D = −31`: `L'(E/K,1) = 7.51 > 0`, and the Heegner point lies in `E(ℚ)` with `ε = −1`.

**Remains.**
- Human readings of all prints (locators UNVERIFIED).
- `PanPrinted` and `BergerPrinted` are OK only if `B_st^{G_K}` is finite-dimensional and nonzero. Otherwise the
  finrank equation makes every representation "semistable" and `PanPrinted` false. This is pb-sanity's check.
- Non-vacuity is not provable in Lean today for:
  - `NewformRepConductor` and the GZ `C_d` leaves (no Lean newforms);
  - `MainTheoremCM`, which is instantiated only inside its consumer at the route.
