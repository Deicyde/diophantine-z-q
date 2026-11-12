# bp-modcurves results log

- 11:45 `Gamma1Genus.lean`: defs `pmSubgroup`, `Cosets`, `belyiDeg`, `nu2`, `nu3`, `nuInf`, `genus` over
  Mathlib `SL(2,ℤ)`, `Gamma1`, `ModularGroup.S/T`. Theorems `nu2_Gamma1` (N ≥ 3: ν₂ = 0),
  `nu3_Gamma1` (N ≥ 4: ν₃ = 0), `genus_Gamma1` (N ≥ 4: g = 1 + μ/12 − ν∞/2), `belyiDeg_Gamma1_le`
  (μ ≤ N²), `genus_Gamma1_le` (g ≤ N²), `index_Gamma1_le` (copied from glue-assembly).
  `lake env lean`: exit 0, no errors, no warnings; axioms propext, Classical.choice, Quot.sound. VERIFIED.
- 11:48 `genus_check.py` (N = 1..30, sequential): μ, ν₂, ν₃, ν∞ from the action of S, ST, T on
  primitive vectors of (ℤ/N)² mod ±; μ = J₂(N)/2 (N ≥ 3), ν∞ = ½Σ_{d|N} φ(d)φ(N/d) (N ≥ 5), genus
  equal to the reference table (from memory, UNVERIFIED reference; all 30 agree), μ ≤ N² for all. VERIFIED (computed).
- 11:58 `TateNormalForm.lean`: `tateNF b c = ⟨1−c, −b, −b, 0, 0⟩`; `exists_tateNF_coord`
  (Equation, not 2-torsion, not flex ⇒ ∃ VariableChange C with C•W = tateNF b c, C.r = x₀, C.t = y₀);
  `not_two_torsion`, `not_flex` (from `P+P ≠ 0`, `P+P+P ≠ 0` in Mathlib's `Affine.Point` group);
  `exists_tateNF` (point form); `tateNF_unique` (b ≠ 0, C fixes (0,0) ⇒ C = 1, b = b', c = c').
  `lake env lean`: exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. VERIFIED.
- 12:00 `tate_check.py`: symbolic order of (0,0) on Kubert's genus-0 families for N = 4..10 is exactly N
  (families from memory; all 7 confirmed by the computation). A remembered N = 12 family failed and was dropped. VERIFIED (computed).
- 12:02 `Jacobian.lean`: `AbVar` (copied from pkg-I3), `IsCurve`, `IsJacobian X P₀ J aj` (Albanese
  property), `JacobianExists K` (leaf statement, a Prop), `IsJacobian.unique` (two Jacobians are
  isomorphic by a unique homomorphism compatible with aj; proved), `jacobian`, `jacobian_spec`.
  `lake env lean`: exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. VERIFIED.
- 12:04 `TateNormalForm.lean` extended: `tateNF_Δ` (Δ = b³(16b² − 8bc² − 20bc + b + c(c−1)³), factor
  first computed by sympy), `tateNF_b_ne_zero` (IsElliptic ⇒ b ≠ 0), `tateNF_unique'` (IsElliptic form).
  `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.
