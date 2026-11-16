# gz-heegner (fleet summary)

**Result: gz-hl3's composite leaf `ZInQ.GZHL3.HeegnerPointRational` is proved in Lean from two printed leaves, with no
new open Prop.** `ZInQ.GZHeegner.heegnerPointRational_of_printed : T5Glue.ShimuraMainCM → X0ModuliGaloisMero →
HeegnerPointRational`. Axioms: `[propext, Classical.choice, Quot.sound]` (compiled with `lake build`).

**Finding.** The kernel's `T5Glue.X0ModuliGalois` (`hX`) only covers modular functions that are regular on all of `ℍ`.
The coordinates of a modular parametrization have poles in `ℍ`, so `hX` cannot give the Heegner point. The task stated
`X0ModuliGaloisMero` as the hypothesis to use. It is the printed canonical-model theorem, for every `g ∈ ℚ(X₀(N))`
regular at the two points. It implies `hX` (`x0ModuliGalois_of_mero`, compiled), so a fold replaces `hX` by it
(same kind: consequence).

**Effect on the strict GLUE count.**
- Against gz-hl3's split: −1 strict and −1 strictest GLUE (`HeegnerPointRational` gone, nothing added).
- The `hL3` split now has 2 composites (`StrongWeilCurve`, `IsogenyLattice`) and 3 printed leaves. Against the current
  `frozenTarget` that is +1, down from +2.

**Proved in Lean** (`ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean`, 137 KB, and `HeegnerCd.lean`):
- Lattice algebra: Dirichlet composition `J·⟨1, τ_{Q'}⟩ = ⟨1, τ_Q⟩`; homothetic lattice pairs ⇔ `Γ₀(N)`-equivalent forms.
- Class field theory: every ideal class contains `⟨a, (−b + √D)/2⟩` with `a` prime to `M` (Tau Ceti's Chebotarev
  theorem).
- Galois theory of `ℂ`: restriction to `ℚ̄`; the fixed fields of `Aut(ℂ/K)` and `Aut(ℂ)`.
- The permutation of the Heegner points by `Aut(ℂ/K)`.
- The analysis that puts `x∘φ`, `y∘φ`, `1/(x∘φ − t)` in `ℚ(X₀(N))`:
  - `D φ_f = f`;
  - `φ_f(γτ) = K₀ + G(q_N)` at every cusp;
  - meromorphy of `℘`, `℘'` and `1/(℘ − c₀)`;
  - rational `q`-expansions: the Weierstrass equation in `q` has a unique formal solution, which is fixed by
    `Aut(ℂ)` and so rational.
- The `C_d` form.

`#discharges`:
- `[hL3] by grossZagierHeegner_of_printed` (assumes gz-hl3's five other leaves, `ShimuraMainCM`,
  `X0ModuliGaloisMero`);
- `[hX] by x0ModuliGalois_of_mero`.

**What remains.**
- A human reading of Shimura 1971 §6.7 and Deligne–Rapoport VI–VII, to confirm the printed statement is for `g` regular
  at the point.
- The `Main.lean` / kinds.tsv edit (report §3).
- For the whole `hL3` split to be net negative, `StrongWeilCurve` / `IsogenyLattice` (or `ShimuraCMParamCd`) still
  need printed forms. Not in this task.

Report: `docs/research/gz-heegner.md`. Log and checks: `scratch/gz-heegner/`.
