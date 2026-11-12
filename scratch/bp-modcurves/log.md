# bp-modcurves results log

(Times are PST by the host clock, approximate to a few minutes.)

- 11:45 `Gamma1Genus.lean`: defs `pmSubgroup`, `Cosets`, `belyiDeg`, `nu2`, `nu3`, `nuInf`, `genus` over
  Mathlib `SL(2,ℤ)`, `Gamma1`, `ModularGroup.S/T`. Theorems `nu2_Gamma1` (N ≥ 3: ν₂ = 0),
  `nu3_Gamma1` (N ≥ 4: ν₃ = 0), `genus_Gamma1` (N ≥ 4: g = 1 + μ/12 − ν∞/2), `belyiDeg_Gamma1_le`
  (μ ≤ N²), `genus_Gamma1_le` (g ≤ N²), `index_Gamma1_le` (copied from glue-assembly).
  `lake env lean`: exit 0, no errors, no warnings; axioms propext, Classical.choice, Quot.sound. VERIFIED.
- 11:48 `genus_check.py` (N = 1..30, sequential): μ, ν₂, ν₃, ν∞ from the action of S, ST, T on
  primitive vectors of (ℤ/N)² mod ±; μ = J₂(N)/2 (N ≥ 3), ν∞ = ½Σ_{d|N} φ(d)φ(N/d) (N ≥ 5), genus
  equal to the reference table (from memory, UNVERIFIED reference; all 30 agree), μ ≤ N² for all. VERIFIED (computed).
- 11:52 `TateNormalForm.lean`: `tateNF b c = ⟨1−c, −b, −b, 0, 0⟩`; `exists_tateNF_coord`
  (Equation, not 2-torsion, not flex ⇒ ∃ VariableChange C with C•W = tateNF b c, C.r = x₀, C.t = y₀);
  `not_two_torsion`, `not_flex` (from `P+P ≠ 0`, `P+P+P ≠ 0` in Mathlib's `Affine.Point` group);
  `exists_tateNF` (point form); `tateNF_unique` (b ≠ 0, C fixes (0,0) ⇒ C = 1, b = b', c = c').
  `lake env lean`: exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. VERIFIED.
- 11:54 `tate_check.py`: symbolic order of (0,0) on Kubert's genus-0 families for N = 4..10 is exactly N
  (families from memory; all 7 confirmed by the computation). A remembered N = 12 family failed and was dropped. VERIFIED (computed).
- 11:59 `Jacobian.lean`: `AbVar` (copied from pkg-I3), `IsCurve`, `IsJacobian X P₀ J aj` (Albanese
  property), `JacobianExists K` (leaf statement, a Prop), `IsJacobian.unique` (two Jacobians are
  isomorphic by a unique homomorphism compatible with aj; proved), `jacobian`, `jacobian_spec`.
  `lake env lean`: exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. VERIFIED.
- 12:00 `TateNormalForm.lean` extended: `tateNF_Δ` (Δ = b³(16b² − 8bc² − 20bc + b + c(c−1)³), factor
  first computed by sympy), `tateNF_b_ne_zero` (IsElliptic ⇒ b ≠ 0), `tateNF_unique'` (IsElliptic form).
  `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.
- 12:03 `Gamma1Genus.lean` extended (MC0b): `PrimVec N`, `firstColMod_prim`, `lift_coprime`,
  `exists_SL2_firstColMod` (every primitive vector mod N is a first column of SL₂(ℤ)),
  `cosetEquivPrimVec : SL(2,ℤ) ⧸ Gamma1 N ≃ PrimVec N`, `index_Gamma1_eq_card`,
  `neg_one_not_mem_Gamma1` (N ≥ 3), `relIndex_pmSubgroup_Gamma1` (= 2), `two_mul_belyiDeg_Gamma1`
  (2μ = #PrimVec N, N ≥ 3); `example : (Gamma1 5).index = 24` by `decide`.
  `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.
- 12:05 `ModularCurveDefs.lean` (MC1, MC3a, MC4 definitions): `Qj = RatFunc ℚ`, `Ej = ofJNe0Or1728 X`
  with `Ej_j : Ej.j = X` (proved) and `IsElliptic`; `EjBar` over `AlgebraicClosure Qj`; `xCoord`;
  `fieldX1 P = ℚ(j)⟮x(P)⟯`; `Y1j P` = Mathlib relative normalization of Spec ℚ[j] in `fieldX1 P`;
  `jMap`. Open statements (Props, not proved): `TorsionCardLe`, `FieldX1DegreeLe`, `FieldX1Degree` (leaf MC1').
  `lake env lean`: exit 0, no warnings; `Ej_j` standard axioms. VERIFIED.
- 12:09 `AnalyticModuli.lean` (MC2d): `lat τ = ℤτ + ℤ`, `jfac γ τ = cτ + d`, `jfac_ne_zero`,
  `coe_smul_eq`, `lattice_homothety` (j·Λ_{γτ} = Λ_τ), `lat_coeff_unique`, `point_preserved_iff`
  (j·(1/N) ≡ 1/N mod Λ_τ ↔ γ ∈ Gamma1 N), `exactOrder` (k/N ∈ Λ_τ ↔ N ∣ k).
  `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.
- 12:11 `AnalyticModuli.lean` extended: `exists_SL2_of_homothety` (α·Λ_{τ'} = Λ_τ ⇒ ∃ γ ∈ SL₂(ℤ),
  τ' = γτ, α = j(γ,τ); orientation from Im), `pair_iso_iff` ((ℂ/Λ_{τ'}, 1/N) ≅ (ℂ/Λ_τ, 1/N) by a
  homothety ⇔ ∃ γ ∈ Gamma1 N, τ' = γ • τ). `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.
- 12:12 `AnalyticModuli.lean` extended: `lift_coprime` (copied), `exists_SL2_bottomRow` (primitive
  bottom row mod N lifts to SL₂(ℤ)), `exists_normalize` (for (c,d) primitive mod N, ∃ γ with
  j(γ,τ)/N ≡ (cτ+d)/N mod Λ_τ). `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.
- 12:16 `PointTransport.lean` (MC2c, first half): `tx`, `ty` (new coordinates), `poly_transport`,
  `equation_transport`, `negY_transport`, `nonsingular_transport`, `slope_transport` (ℓ' = (ℓ − s)/u),
  `mapPt` (transport of `Affine.Point`), `mapPt_add` (additive), `mapPtHom`, `mapPt_injective`,
  `addOrderOf_mapPt` (orders preserved). `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.
- 12:19 `PointTransport.lean` extended: Tate NF existence copied; `exists_tateNF_order` (a point of
  exact order N ≥ 4 is carried by a change of variables C with C.r = x₀, C.t = y₀ to (0,0) on some
  E(b,c), and (0,0) has exact order N there). `lake env lean`: exit 0, no warnings; standard axioms. VERIFIED.
- 12:18 Final check, sequentially, all six files with `lake env lean`: Gamma1Genus, TateNormalForm,
  Jacobian, ModularCurveDefs, AnalyticModuli, PointTransport: exit 0, 0 errors, 0 warnings, no
  `sorry`/`admit`/`axiom` in the sources; every `#print axioms` line is ⊆ {propext, Classical.choice,
  Quot.sound}. VERIFIED.
