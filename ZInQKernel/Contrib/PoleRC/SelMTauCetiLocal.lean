import ZInQKernel.Contrib.PoleRC.SelMTwoDescent
import ZInQKernel.Contrib.PoleRC.Defs

/-!
# The local `2`-descent of `E_m : y² = x(x − m)(x + 3m)` in Tau Ceti's Galois cohomology

Lane R7 of fork issue #83: the field-level half of the bridge between the explicit `2`-Selmer
system `SelM ℓ` (`Defs.lean`) and the genuine `Sel₂(E_ℓ/ℚ)` of
`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean` (Tau Ceti's `WeierstrassCurve.selmerGroup`).
Everything here is over an arbitrary field `F` with `2, 3 ≠ 0` and a curve `W` of the shape
`y² = x³ + 2m x² − 3m² x` (`IsCurveE W m`, `m ≠ 0`), in the manuscript's Kummer coordinates
`(x + 3m, x − m)` (`diophantine_zq.tex` line 1058), i.e. at the two-torsion points
`T_A = (−3m, 0)` and `T_B = (m, 0)`.

* `smul_torsionCoeff_two`: `G_F` acts trivially on `W[2](Fˢ)` (the roots `0, m, −3m` lie in `F`).
* `chiA`, `chiB`: the characters `W[2] → μ₂` trivial exactly on `{O, T_A}`, `{O, T_B}`
  (`twoTorsionCharacter` of `SelMTwoDescent.lean`, adapted from Tau Ceti; they are the Weil
  pairings `e₂(·, T_A)`, `e₂(·, T_B)`, which is not used); `eq_zero_of_chi`: together they detect
  `H¹(G_F, W[2])`; `sec`, `chiA_sec`, `chiB_sec`: every pair of classes of `H¹(G_F, μ₂)` is hit.
  So `H¹(G_F, W[2]) ≅ H¹(G_F, μ₂)²`, which is `(F*/F*²)²` by Kummer theory (Silverman X.1.4,
  first step).
* `locM_iff_exists_point`: the x-form `LocM F m a b` of `Defs.lean` says exactly that `(a, b)` is
  the image mod squares of a point `P ∈ W(F)` under the descent map `(uA, uB)`,
  `twoDescentUnit` at `T_A` and `T_B` (`x + 3m`, `x − m`, with `f'(e)` at `T_e` and `1` at `O`).
* `torsionRes_mem_range_kummerMap_iff`: **the local condition**. For a field extension `L/K`, a
  curve `E/K` of this shape and a class `c ∈ H¹(G_K, E[2])` whose two characters are the Kummer
  classes of `a, b ∈ K*`, the restriction of `c` to `G_L` lies in the image of the local Kummer
  map `E(L) → H¹(G_L, E[2])` iff `LocM L ℓ a b`. The core input is
  `explicitCoeff1_twoTorsionCharacter_kummerMap` (the Kummer map read through `T` is `x − e`,
  Silverman X.1.4; Tau Ceti's proof) with `explicitMap1_explicitCoeff1_twoTorsionCharacter` (its
  compatibility with restriction), both in `SelMTwoDescent.lean`.

The import closure avoids Tau Ceti's Weil-pairing development (see `SelMTwoDescent.lean`).
-/

noncomputable section

namespace ZInQ.Manuscript.PoleRC.SelMTauCeti

open TauCeti TauCeti.ContCohomology WeierstrassCurve

/-! ### The curve `E_m` over a field -/

section Shape

variable {F : Type*} [Field F]

/-- `W` is the curve `E_m : y² = x³ + 2m x² − 3m² x = x(x − m)(x + 3m)`. -/
structure IsCurveE (W : WeierstrassCurve F) (m : F) : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 2 * m
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = -3 * m ^ 2
  a₆ : W.a₆ = 0

namespace IsCurveE

variable {W : WeierstrassCurve F} {m : F} (hW : IsCurveE W m)
include hW

theorem equation_iff (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + 2 * m * x ^ 2 - 3 * m ^ 2 * x := by
  rw [Affine.equation_iff]
  simp only [hW.a₁, hW.a₂, hW.a₃, hW.a₄, hW.a₆]
  constructor <;> intro h <;> linear_combination h

theorem Δ_eq : W.Δ = 2304 * m ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, hW.a₁, hW.a₂, hW.a₃, hW.a₄, hW.a₆]
  ring

theorem Δ_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hm : m ≠ 0) : W.Δ ≠ 0 := by
  rw [hW.Δ_eq, show (2304 : F) = 2 ^ 8 * 3 ^ 2 by norm_num]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) (pow_ne_zero _ hm)

theorem isElliptic (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hm : m ≠ 0) : W.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (hW.Δ_ne_zero h2 h3 hm)⟩

theorem polynomialY_evalEval (x y : F) : W.toAffine.polynomialY.evalEval x y = 2 * y := by
  rw [Affine.evalEval_polynomialY]
  simp only [hW.a₁, hW.a₃]
  ring

theorem polynomialX_evalEval (x y : F) :
    W.toAffine.polynomialX.evalEval x y = -(3 * x ^ 2 + 4 * m * x - 3 * m ^ 2) := by
  rw [Affine.evalEval_polynomialX]
  simp only [hW.a₁, hW.a₂, hW.a₄]
  ring

theorem map {L : Type*} [Field L] (f : F →+* L) : IsCurveE (W.map f) (f m) where
  a₁ := by simp only [WeierstrassCurve.map_a₁, hW.a₁, map_zero]
  a₂ := by simp only [WeierstrassCurve.map_a₂, hW.a₂, map_mul, map_ofNat]
  a₃ := by simp only [WeierstrassCurve.map_a₃, hW.a₃, map_zero]
  a₄ := by simp only [WeierstrassCurve.map_a₄, hW.a₄, map_mul, map_neg, map_pow, map_ofNat]
  a₆ := by simp only [WeierstrassCurve.map_a₆, hW.a₆, map_zero]

theorem baseChange (L : Type*) [Field L] [Algebra F L] :
    IsCurveE (W.baseChange L) (algebraMap F L m) :=
  hW.map (algebraMap F L)

theorem equation_root {e : F} (he : e = 0 ∨ e = m ∨ e = -3 * m) : W.toAffine.Equation e 0 := by
  rw [hW.equation_iff]
  rcases he with rfl | rfl | rfl <;> ring

theorem nonsingular_root (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hm : m ≠ 0) {e : F}
    (he : e = 0 ∨ e = m ∨ e = -3 * m) : W.toAffine.Nonsingular e 0 :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (hW.Δ_ne_zero h2 h3 hm)).mp (hW.equation_root he)

theorem psi_root (e : F) : W.toAffine.polynomialY.evalEval e 0 = 0 := by
  rw [hW.polynomialY_evalEval]; ring

end IsCurveE

theorem two_ne_zero_of_algebra {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (h : (n : K) ≠ 0) : (n : L) ≠ 0 := by
  have := (map_ne_zero (algebraMap K L)).mpr h
  rwa [map_natCast] at this

theorem isUnit_two_nat (h2 : (2 : F) ≠ 0) : IsUnit ((2 : ℕ) : F) :=
  isUnit_iff_ne_zero.mpr (by exact_mod_cast h2)

end Shape

/-! ### `G_F` acts trivially on `E_m[2]` -/

section Torsion

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {m : F}

omit [DecidableEq F] in
/-- **The two-torsion of `E_m` is rational**: `G_F` fixes every point of `E_m[2](Fˢ)`, whose
abscissae are the roots `0, m, −3m ∈ F` (for `2 ≠ 0` in `F`). -/
theorem smul_torsionCoeff_two (hW : IsCurveE W m) (h2 : (2 : F) ≠ 0) (σ : AbsoluteGaloisGroup F)
    (P : W.TorsionCoeff 2) : σ • P = P := by
  classical
  obtain ⟨Q, hQ⟩ := P
  refine Subtype.ext ?_
  rw [coe_smul_torsionCoeff]
  change σ • Q = Q
  have h2Q : (2 : ℕ) • Q = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hQ
  obtain ⟨R, rfl⟩ := W.pointCoeffEquiv.surjective Q
  have hR : R + R = 0 := by
    apply W.pointCoeffEquiv.injective
    rw [map_add, ← two_nsmul, h2Q, map_zero]
  rw [smul_pointCoeffEquiv]
  congr 1
  rcases R with _ | ⟨x, y, h⟩
  · rfl
  · have hWs := hW.baseChange (SeparableClosure F)
    rw [Affine.Point.some_add_self_eq_zero_iff, hWs.polynomialY_evalEval] at hR
    have h2s : (2 : SeparableClosure F) ≠ 0 := by
      have := two_ne_zero_of_algebra (K := F) (L := SeparableClosure F) (n := 2)
        (by exact_mod_cast h2)
      exact_mod_cast this
    have hy : y = 0 := (mul_eq_zero.mp hR).resolve_left h2s
    subst hy
    have hx := (hWs.equation_iff x 0).mp h.1
    have hσm : σ (algebraMap F (SeparableClosure F) m) = algebraMap F (SeparableClosure F) m :=
      σ.commutes m
    have hfac : x * (x - algebraMap F (SeparableClosure F) m) *
        (x + 3 * algebraMap F (SeparableClosure F) m) = 0 := by
      linear_combination -hx
    have hσx : σ x = x := by
      rcases mul_eq_zero.mp hfac with h1 | h1
      · rcases mul_eq_zero.mp h1 with h1 | h1
        · rw [h1, map_zero]
        · rw [show x = algebraMap F (SeparableClosure F) m by linear_combination h1, hσm]
      · rw [show x = -3 * algebraMap F (SeparableClosure F) m by linear_combination h1, map_mul,
          hσm, map_neg, map_ofNat]
    rw [Affine.Point.map_some]
    simp only [AlgEquiv.coe_toAlgHom, hσx, map_zero]

end Torsion

/-! ### The two characters `E_m[2] → μ₂` and the section -/

section Characters

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {m : F}
  (hW : IsCurveE W m) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hm : m ≠ 0)

omit [DecidableEq F] in
include hW h2 h3 hm in
/-- `T_A = (−3m, 0)` is a point of `E_m`. -/
theorem nsA : W.toAffine.Nonsingular (-3 * m) 0 :=
  hW.nonsingular_root h2 h3 hm (Or.inr (Or.inr rfl))

omit [DecidableEq F] in
include hW h2 h3 hm in
/-- `T_B = (m, 0)` is a point of `E_m`. -/
theorem nsB : W.toAffine.Nonsingular m 0 :=
  hW.nonsingular_root h2 h3 hm (Or.inr (Or.inl rfl))

/-- `T_A = (−3m, 0)` in `E_m[2](Fˢ)`. -/
def TA : W.TorsionCoeff 2 := twoTorsionCoeff W (nsA hW h2 h3 hm) (hW.psi_root _)

/-- `T_B = (m, 0)` in `E_m[2](Fˢ)`. -/
def TB : W.TorsionCoeff 2 := twoTorsionCoeff W (nsB hW h2 h3 hm) (hW.psi_root _)

/-- The character `E_m[2] → μ₂` trivial exactly on `{O, T_A}` (the Weil pairing `e₂(·, T_A)`):
the coordinate `x + 3m` of the manuscript's Kummer map. -/
def chiA [W.IsElliptic] : W.TorsionCoeff 2 →+[AbsoluteGaloisGroup F] KummerCoeff F 2 :=
  twoTorsionCharacter W (nsA hW h2 h3 hm) (hW.psi_root _) (isUnit_two_nat h2)

/-- The character `E_m[2] → μ₂` trivial exactly on `{O, T_B}` (the Weil pairing `e₂(·, T_B)`):
the coordinate `x − m` of the manuscript's Kummer map. -/
def chiB [W.IsElliptic] : W.TorsionCoeff 2 →+[AbsoluteGaloisGroup F] KummerCoeff F 2 :=
  twoTorsionCharacter W (nsB hW h2 h3 hm) (hW.psi_root _) (isUnit_two_nat h2)

include hW h2 h3 hm in
theorem baseA_ne_baseB :
    W.basePointCoeff (.some (-3 * m) 0 (nsA hW h2 h3 hm)) ≠
      W.basePointCoeff (.some m 0 (nsB hW h2 h3 hm)) := by
  intro h
  have h' := W.basePointCoeff_injective h
  rw [Affine.Point.some.injEq] at h'
  apply hm
  have h4 : (4 : F) * m = 0 := by linear_combination -h'.1
  have h4' : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  exact (mul_eq_zero.mp h4).resolve_left h4'

theorem chiA_eq_zero_iff [W.IsElliptic] {S : W.TorsionCoeff 2} :
    chiA hW h2 h3 hm S = 0 ↔ (S : W.PointCoeff) = 0 ∨
      (S : W.PointCoeff) = W.basePointCoeff (.some (-3 * m) 0 (nsA hW h2 h3 hm)) :=
  twoTorsionCharacter_eq_zero_iff W _ _ _

theorem chiB_eq_zero_iff [W.IsElliptic] {S : W.TorsionCoeff 2} :
    chiB hW h2 h3 hm S = 0 ↔ (S : W.PointCoeff) = 0 ∨
      (S : W.PointCoeff) = W.basePointCoeff (.some m 0 (nsB hW h2 h3 hm)) :=
  twoTorsionCharacter_eq_zero_iff W _ _ _

theorem chiA_TA [W.IsElliptic] : chiA hW h2 h3 hm (TA hW h2 h3 hm) = 0 :=
  (chiA_eq_zero_iff hW h2 h3 hm).mpr (Or.inr (coe_twoTorsionCoeff W _ _))

theorem chiB_TB [W.IsElliptic] : chiB hW h2 h3 hm (TB hW h2 h3 hm) = 0 :=
  (chiB_eq_zero_iff hW h2 h3 hm).mpr (Or.inr (coe_twoTorsionCoeff W _ _))

theorem chiA_TB [W.IsElliptic] : chiA hW h2 h3 hm (TB hW h2 h3 hm) = mu2NegOne := by
  refine (eq_zero_or_eq_mu2NegOne _).resolve_left fun h0 => ?_
  have hTB : ((TB hW h2 h3 hm : W.TorsionCoeff 2) : W.PointCoeff) =
      W.basePointCoeff (.some m 0 (nsB hW h2 h3 hm)) := coe_twoTorsionCoeff W _ _
  rcases (chiA_eq_zero_iff hW h2 h3 hm).mp h0 with h1 | h1
  · exact twoTorsionCoeff_ne_zero W _ _ (ZeroMemClass.coe_eq_zero.mp h1)
  · exact baseA_ne_baseB hW h2 h3 hm (h1.symm.trans hTB)

theorem chiB_TA [W.IsElliptic] : chiB hW h2 h3 hm (TA hW h2 h3 hm) = mu2NegOne := by
  refine (eq_zero_or_eq_mu2NegOne _).resolve_left fun h0 => ?_
  have hTA : ((TA hW h2 h3 hm : W.TorsionCoeff 2) : W.PointCoeff) =
      W.basePointCoeff (.some (-3 * m) 0 (nsA hW h2 h3 hm)) := coe_twoTorsionCoeff W _ _
  rcases (chiB_eq_zero_iff hW h2 h3 hm).mp h0 with h1 | h1
  · exact twoTorsionCoeff_ne_zero W _ _ (ZeroMemClass.coe_eq_zero.mp h1)
  · exact baseA_ne_baseB hW h2 h3 hm (hTA.symm.trans h1)

/-- **The two characters detect `H¹(G_F, E_m[2])`.** `G_F` acts trivially on `E_m[2]` and on
`μ₂`, so a class is a continuous homomorphism `z : G_F → E_m[2]`, and its images are `χ_A ∘ z`,
`χ_B ∘ z` (no coboundaries); if both vanish, `z(g) ∈ {O, T_A} ∩ {O, T_B} = {O}`. -/
theorem eq_zero_of_chi [W.IsElliptic] (c : H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff 2))
    (hA : explicitCoeff1 _ _ (chiA hW h2 h3 hm) continuous_of_discreteTopology c = 0)
    (hB : explicitCoeff1 _ _ (chiB hW h2 h3 hm) continuous_of_discreteTopology c = 0) :
    c = 0 := by
  induction c using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitCoeff1_mk, H1pi_eq_zero_iff, B1_eq_bot_of_smul_eq_self (mu2_smul_eq_self F),
      AddSubgroup.mem_bot] at hA hB
    rw [H1pi_eq_zero_iff]
    have key : (z : AbsoluteGaloisGroup F → W.TorsionCoeff 2) = 0 := by
      funext g
      have hAg : chiA hW h2 h3 hm ((z : AbsoluteGaloisGroup F → W.TorsionCoeff 2) g) = 0 :=
        congrFun hA g
      have hBg : chiB hW h2 h3 hm ((z : AbsoluteGaloisGroup F → W.TorsionCoeff 2) g) = 0 :=
        congrFun hB g
      rcases (chiA_eq_zero_iff hW h2 h3 hm).mp hAg with h1 | h1
      · exact ZeroMemClass.coe_eq_zero.mp h1
      rcases (chiB_eq_zero_iff hW h2 h3 hm).mp hBg with h1' | h1'
      · exact ZeroMemClass.coe_eq_zero.mp h1'
      exact absurd (h1.symm.trans h1') (baseA_ne_baseB hW h2 h3 hm)
    rw [key]
    exact AddSubgroup.zero_mem _

/-- Injectivity form of `eq_zero_of_chi`. -/
theorem eq_of_chi [W.IsElliptic] {c c' : H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff 2)}
    (hA : explicitCoeff1 _ _ (chiA hW h2 h3 hm) continuous_of_discreteTopology c =
      explicitCoeff1 _ _ (chiA hW h2 h3 hm) continuous_of_discreteTopology c')
    (hB : explicitCoeff1 _ _ (chiB hW h2 h3 hm) continuous_of_discreteTopology c =
      explicitCoeff1 _ _ (chiB hW h2 h3 hm) continuous_of_discreteTopology c') :
    c = c' := by
  rw [← sub_eq_zero]
  exact eq_zero_of_chi hW h2 h3 hm _ (by rw [map_sub, hA, sub_self])
    (by rw [map_sub, hB, sub_self])

/-- Coefficient maps that agree induce the same map on `H¹`. -/
theorem explicitCoeff1_congr {G : Type*} [Monoid G] [TopologicalSpace G]
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
    {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
    {f g : M →+[G] N} (hf : Continuous f) (hg : Continuous g) (h : f = g) :
    explicitCoeff1 G M f hf = explicitCoeff1 G M g hg := by
  subst h; rfl

/-- A coefficient map that vanishes pointwise induces zero on `H¹`. (Stated pointwise: on
endomorphisms `A →+[G] A` the literal `0` can elaborate to the identity, through the additive
translation of `One (A →*[G] A)`.) -/
theorem explicitCoeff1_eq_zero_of_forall {G : Type*} [Monoid G] [TopologicalSpace G]
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
    {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (hf : Continuous f) (hf0 : ∀ x, f x = 0) (x : H1 G M) :
    explicitCoeff1 G M f hf x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitCoeff1_mk, H1pi_eq_zero_iff]
    convert AddSubgroup.zero_mem (B1 G N)
    funext g
    exact hf0 _

variable [Invertible (2 : F)]

/-- The homomorphism `μ₂ → E_m[2]`, `−1 ↦ T`, for a point `T` of `E_m[2]`. -/
def iotaHom (T : W.TorsionCoeff 2) : KummerCoeff F 2 →+ W.TorsionCoeff 2 :=
  (ZMod.lift 2 ⟨zmultiplesHom (W.TorsionCoeff 2) T, by
      rw [zmultiplesHom_apply, natCast_zsmul]
      exact AddSubgroup.torsionBy.nsmul T⟩).comp (mu2EquivZMod2 F).toAddMonoidHom

omit [DecidableEq F] in
theorem iotaHom_negOne (T : W.TorsionCoeff 2) : iotaHom T mu2NegOne = T := by
  rw [iotaHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    mu2EquivZMod2_apply_mu2NegOne,
    show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) from Int.cast_one.symm, ZMod.lift_coe]
  change zmultiplesHom (W.TorsionCoeff 2) T 1 = T
  rw [zmultiplesHom_apply, one_zsmul]

/-- The equivariant map `μ₂ → E_m[2]`, `−1 ↦ T`, for a point `T` of `E_m[2]` (both actions are
trivial). -/
def iota (T : W.TorsionCoeff 2) : KummerCoeff F 2 →+[AbsoluteGaloisGroup F] W.TorsionCoeff 2 :=
  { iotaHom T with
    map_smul' := fun σ ζ => by
      simp only [MonoidHom.id_apply, AddMonoidHom.toFun_eq_coe, mu2_smul_eq_self]
      exact (smul_torsionCoeff_two hW h2 σ _).symm }

omit [DecidableEq F] in
theorem iota_apply (T : W.TorsionCoeff 2) (ζ : KummerCoeff F 2) :
    iota hW h2 T ζ = iotaHom T ζ := rfl

omit [DecidableEq F] in
theorem iota_negOne (T : W.TorsionCoeff 2) : iota hW h2 T mu2NegOne = T := by
  rw [iota_apply, iotaHom_negOne]

theorem chiA_comp_iotaB [W.IsElliptic] :
    (chiA hW h2 h3 hm).comp (iota hW h2 (TB hW h2 h3 hm)) = DistribMulActionHom.id _ := by
  refine DistribMulActionHom.ext fun ζ => ?_
  rw [DistribMulActionHom.comp_apply, DistribMulActionHom.id_apply]
  rcases eq_zero_or_eq_mu2NegOne ζ with rfl | rfl
  · rw [map_zero, map_zero]
  · rw [iota_negOne, chiA_TB]

theorem chiA_comp_iotaA [W.IsElliptic] (ζ : KummerCoeff F 2) :
    chiA hW h2 h3 hm (iota hW h2 (TA hW h2 h3 hm) ζ) = 0 := by
  rcases eq_zero_or_eq_mu2NegOne ζ with rfl | rfl
  · rw [map_zero, map_zero]
  · rw [iota_negOne, chiA_TA]

theorem chiB_comp_iotaA [W.IsElliptic] :
    (chiB hW h2 h3 hm).comp (iota hW h2 (TA hW h2 h3 hm)) = DistribMulActionHom.id _ := by
  refine DistribMulActionHom.ext fun ζ => ?_
  rw [DistribMulActionHom.comp_apply, DistribMulActionHom.id_apply]
  rcases eq_zero_or_eq_mu2NegOne ζ with rfl | rfl
  · rw [map_zero, map_zero]
  · rw [iota_negOne, chiB_TA]

theorem chiB_comp_iotaB [W.IsElliptic] (ζ : KummerCoeff F 2) :
    chiB hW h2 h3 hm (iota hW h2 (TB hW h2 h3 hm) ζ) = 0 := by
  rcases eq_zero_or_eq_mu2NegOne ζ with rfl | rfl
  · rw [map_zero, map_zero]
  · rw [iota_negOne, chiB_TB]

/-- **The section** `H¹(G_F, μ₂)² → H¹(G_F, E_m[2])`, `(x, y) ↦ ι_{T_B*}(x) + ι_{T_A*}(y)`. -/
def sec (x y : H1 (AbsoluteGaloisGroup F) (KummerCoeff F 2)) :
    H1 (AbsoluteGaloisGroup F) (W.TorsionCoeff 2) :=
  explicitCoeff1 _ _ (iota hW h2 (TB hW h2 h3 hm)) continuous_of_discreteTopology x +
    explicitCoeff1 _ _ (iota hW h2 (TA hW h2 h3 hm)) continuous_of_discreteTopology y

omit [DecidableEq F] [Invertible (2 : F)] in
private theorem explicitCoeff1_comp_apply {N P : Type*} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction (AbsoluteGaloisGroup F) N]
    [ContinuousSMul (AbsoluteGaloisGroup F) N] [DiscreteTopology N]
    [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction (AbsoluteGaloisGroup F) P] [ContinuousSMul (AbsoluteGaloisGroup F) P]
    [DiscreteTopology P]
    (f : KummerCoeff F 2 →+[AbsoluteGaloisGroup F] N) (q : N →+[AbsoluteGaloisGroup F] P)
    (x : H1 (AbsoluteGaloisGroup F) (KummerCoeff F 2)) :
    explicitCoeff1 _ _ q continuous_of_discreteTopology
        (explicitCoeff1 _ _ f continuous_of_discreteTopology x) =
      explicitCoeff1 _ _ (q.comp f) continuous_of_discreteTopology x := by
  rw [explicitCoeff1_comp (AbsoluteGaloisGroup F) (KummerCoeff F 2) f q
    continuous_of_discreteTopology continuous_of_discreteTopology]
  rfl

theorem chiA_sec [W.IsElliptic] (x y : H1 (AbsoluteGaloisGroup F) (KummerCoeff F 2)) :
    explicitCoeff1 _ _ (chiA hW h2 h3 hm) continuous_of_discreteTopology
      (sec hW h2 h3 hm x y) = x := by
  have e3 : explicitCoeff1 _ _ ((chiA hW h2 h3 hm).comp (iota hW h2 (TB hW h2 h3 hm)))
      continuous_of_discreteTopology x = x := by
    rw [explicitCoeff1_congr _ continuous_id (chiA_comp_iotaB hW h2 h3 hm), explicitCoeff1_id,
      AddMonoidHom.id_apply]
  have e4 : explicitCoeff1 _ _ ((chiA hW h2 h3 hm).comp (iota hW h2 (TA hW h2 h3 hm)))
      continuous_of_discreteTopology y = 0 := by
    exact explicitCoeff1_eq_zero_of_forall _ _ (chiA_comp_iotaA hW h2 h3 hm) y
  rw [sec, map_add, explicitCoeff1_comp_apply, explicitCoeff1_comp_apply, e3, e4, add_zero]

theorem chiB_sec [W.IsElliptic] (x y : H1 (AbsoluteGaloisGroup F) (KummerCoeff F 2)) :
    explicitCoeff1 _ _ (chiB hW h2 h3 hm) continuous_of_discreteTopology
      (sec hW h2 h3 hm x y) = y := by
  have e3 : explicitCoeff1 _ _ ((chiB hW h2 h3 hm).comp (iota hW h2 (TA hW h2 h3 hm)))
      continuous_of_discreteTopology y = y := by
    rw [explicitCoeff1_congr _ continuous_id (chiB_comp_iotaA hW h2 h3 hm), explicitCoeff1_id,
      AddMonoidHom.id_apply]
  have e4 : explicitCoeff1 _ _ ((chiB hW h2 h3 hm).comp (iota hW h2 (TB hW h2 h3 hm)))
      continuous_of_discreteTopology x = 0 := by
    exact explicitCoeff1_eq_zero_of_forall _ _ (chiB_comp_iotaB hW h2 h3 hm) x
  rw [sec, map_add, explicitCoeff1_comp_apply, explicitCoeff1_comp_apply, e3, e4, zero_add]

end Characters

/-! ### Kummer classes of units and square classes -/

section KummerUnits

variable {F : Type*} [Field F]

/-- Two units have the same Kummer class in `H¹(G_F, μ₂)` iff their quotient is a square. -/
theorem kummerMap_eq_iff (hu : IsUnit ((2 : ℕ) : F)) (u a : Fˣ) :
    TauCeti.kummerMap F 2 hu u = TauCeti.kummerMap F 2 hu a ↔ IsSquare ((u : F) / a) := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, TauCeti.kummerMap_eq_one_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have := congrArg Units.val hw
    rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val] at this
    rw [div_eq_mul_inv, ← this, sq]
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_eq_zero_iff] at hr
      rcases hr with h | h
      · exact u.ne_zero h
      · exact a.ne_zero h
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val, sq,
      ← hr, div_eq_mul_inv]

theorem isSquare_div_iff {z a : F} (ha : a ≠ 0) : IsSquare (z / a) ↔ ∃ s, z = a * s ^ 2 := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [div_eq_iff ha] at hr
    rw [hr]; ring
  · rintro ⟨s, rfl⟩
    exact ⟨s, by field_simp⟩

end KummerUnits

/-! ### The descent map `(uA, uB)` and the x-form `LocM` -/

section Descent

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {m : F}
  (hW : IsCurveE W m) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hm : m ≠ 0)

/-- The descent unit at `T_A`: `x + 3m`, with `f'(−3m) = 12m²` at `T_A` and `1` at `O`. -/
def uA : W.toAffine.Point → Fˣ := twoDescentUnit W (nsA hW h2 h3 hm) (hW.psi_root _)

/-- The descent unit at `T_B`: `x − m`, with `f'(m) = 4m²` at `T_B` and `1` at `O`. -/
def uB : W.toAffine.Point → Fˣ := twoDescentUnit W (nsB hW h2 h3 hm) (hW.psi_root _)

theorem uA_zero : uA hW h2 h3 hm 0 = 1 := twoDescentUnit_zero W _ _

theorem uB_zero : uB hW h2 h3 hm 0 = 1 := twoDescentUnit_zero W _ _

theorem uA_some_of_ne {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x ≠ -3 * m) :
    (uA hW h2 h3 hm (.some x y h) : F) = x + 3 * m := by
  rw [uA, coe_twoDescentUnit_some_of_ne W _ _ h hx]; ring

theorem uA_some_of_eq {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = -3 * m) :
    (uA hW h2 h3 hm (.some x y h) : F) = 12 * m ^ 2 := by
  rw [uA, coe_twoDescentUnit_some_of_eq W _ _ h hx, hW.polynomialX_evalEval]; ring

theorem uB_some_of_ne {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x ≠ m) :
    (uB hW h2 h3 hm (.some x y h) : F) = x - m := by
  rw [uB, coe_twoDescentUnit_some_of_ne W _ _ h hx]

theorem uB_some_of_eq {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = m) :
    (uB hW h2 h3 hm (.some x y h) : F) = 4 * m ^ 2 := by
  rw [uB, coe_twoDescentUnit_some_of_eq W _ _ h hx, hW.polynomialX_evalEval]; ring

omit [DecidableEq F] in
include h2 hm in
theorem neg_three_mul_ne : -3 * m ≠ m := by
  intro h
  apply hm
  have h4 : (4 : F) * m = 0 := by linear_combination -h
  have h4' : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  exact (mul_eq_zero.mp h4).resolve_left h4'

/-- **A point gives the x-form local condition**: if `(uA P, uB P) ≡ (a, b)` mod squares for
some `P ∈ E_m(F)`, then `LocM F m a b`. -/
theorem locM_of_point (a b : Fˣ) (P : W.toAffine.Point)
    (hA : IsSquare ((uA hW h2 h3 hm P : F) / a)) (hB : IsSquare ((uB hW h2 h3 hm P : F) / b)) :
    LocM F m a b := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hb : (b : F) ≠ 0 := b.ne_zero
  have hab : (a : F) * b ≠ 0 := mul_ne_zero ha hb
  rw [isSquare_div_iff ha] at hA
  rw [isSquare_div_iff hb] at hB
  obtain ⟨s, hs⟩ := hA
  obtain ⟨t, ht⟩ := hB
  have hm3 := neg_three_mul_ne h2 hm
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h16' : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 4 * 4 by norm_num]; exact mul_ne_zero h4 h4
  have h16 : (16 : F) * m ^ 2 ≠ 0 := mul_ne_zero h16' (pow_ne_zero _ hm)
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, uA_zero, Units.val_one] at hs
    rw [← Affine.Point.zero_def, uB_zero, Units.val_one] at ht
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht
    left
    exact ⟨⟨s⁻¹, by field_simp; linear_combination -hs⟩,
      ⟨t⁻¹, by field_simp; linear_combination -ht⟩⟩
  · have heq : y ^ 2 = x * (x - m) * (x + 3 * m) := by
      have := (hW.equation_iff x y).mp h.1
      linear_combination this
    right
    by_cases hxA : x = -3 * m
    · rw [uA_some_of_eq hW h2 h3 hm h hxA] at hs
      rw [uB_some_of_ne hW h2 h3 hm h (by rw [hxA]; exact hm3)] at ht
      refine ⟨x, ?_, (isSquare_div_iff hb).mpr ⟨t, ht⟩, ?_⟩
      · rw [hxA, show -3 * m + 3 * m = 0 by ring, zero_div]
        exact ⟨0, by ring⟩
      · refine (isSquare_div_iff hab).mpr ⟨s * t / (4 * m), ?_⟩
        have e1 : (a : F) * b * (s * t / (4 * m)) ^ 2 =
            (a * s ^ 2) * (b * t ^ 2) / (16 * m ^ 2) := by
          field_simp; try ring
        rw [e1, ← hs, ← ht, hxA, eq_div_iff h16]
        ring
    · rw [uA_some_of_ne hW h2 h3 hm h hxA] at hs
      by_cases hxB : x = m
      · rw [uB_some_of_eq hW h2 h3 hm h hxB] at ht
        refine ⟨x, (isSquare_div_iff ha).mpr ⟨s, hs⟩, ?_, ?_⟩
        · rw [hxB, sub_self, zero_div]
          exact ⟨0, by ring⟩
        · refine (isSquare_div_iff hab).mpr ⟨s * t / (4 * m), ?_⟩
          have e1 : (a : F) * b * (s * t / (4 * m)) ^ 2 =
              (a * s ^ 2) * (b * t ^ 2) / (16 * m ^ 2) := by
            field_simp; try ring
          rw [e1, ← hs, ← ht, hxB, eq_div_iff h16]
          ring
      · rw [uB_some_of_ne hW h2 h3 hm h hxB] at ht
        refine ⟨x, (isSquare_div_iff ha).mpr ⟨s, hs⟩, (isSquare_div_iff hb).mpr ⟨t, ht⟩, ?_⟩
        by_cases hx0 : x = 0
        · rw [hx0, zero_div]
          exact ⟨0, by ring⟩
        have hxa : x + 3 * m ≠ 0 := fun h0 => hxA (by linear_combination h0)
        have hxb : x - m ≠ 0 := sub_ne_zero.mpr hxB
        have hs0 : s ≠ 0 := by rintro rfl; apply hxa; rw [hs]; ring
        have ht0 : t ≠ 0 := by rintro rfl; apply hxb; rw [ht]; ring
        refine (isSquare_div_iff hab).mpr ⟨y / (a * b * s * t), ?_⟩
        have e1 : (a : F) * b * (y / (a * b * s * t)) ^ 2 =
            y ^ 2 / ((a * s ^ 2) * (b * t ^ 2)) := by
          field_simp
        rw [e1, ← hs, ← ht, heq, eq_div_iff (mul_ne_zero hxa hxb)]
        ring

/-- **The x-form local condition gives a point**: `LocM F m a b` gives `P ∈ E_m(F)` with
`(uA P, uB P) ≡ (a, b)` mod squares. -/
theorem exists_point_of_locM (a b : Fˣ) (hloc : LocM F m a b) :
    ∃ P : W.toAffine.Point, IsSquare ((uA hW h2 h3 hm P : F) / a) ∧
      IsSquare ((uB hW h2 h3 hm P : F) / b) := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hb : (b : F) ≠ 0 := b.ne_zero
  have hab : (a : F) * b ≠ 0 := mul_ne_zero ha hb
  have hm3 := neg_three_mul_ne h2 hm
  rcases hloc with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩ | ⟨x, hxa, hxb, hxab⟩
  · have hα0 : α ≠ 0 := by rintro rfl; exact ha (by rw [hα, mul_zero])
    have hβ0 : β ≠ 0 := by rintro rfl; exact hb (by rw [hβ, mul_zero])
    refine ⟨0, ?_, ?_⟩
    · rw [uA_zero, Units.val_one]
      exact (isSquare_div_iff ha).mpr ⟨α⁻¹, by rw [hα]; field_simp⟩
    · rw [uB_zero, Units.val_one]
      exact (isSquare_div_iff hb).mpr ⟨β⁻¹, by rw [hβ]; field_simp⟩
  · rw [isSquare_div_iff ha] at hxa
    rw [isSquare_div_iff hb] at hxb
    rw [isSquare_div_iff hab] at hxab
    obtain ⟨s, hs⟩ := hxa
    obtain ⟨t, ht⟩ := hxb
    obtain ⟨r, hr⟩ := hxab
    have hE : W.toAffine.Equation x (a * b * r * s * t) := by
      rw [hW.equation_iff]
      calc (a * b * r * s * t : F) ^ 2 = (a * b * r ^ 2) * (b * t ^ 2) * (a * s ^ 2) := by ring
        _ = x * (x - m) * (x + 3 * m) := by rw [← hr, ← ht, ← hs]
        _ = x ^ 3 + 2 * m * x ^ 2 - 3 * m ^ 2 * x := by ring
    have hN : W.toAffine.Nonsingular x (a * b * r * s * t) :=
      (Affine.equation_iff_nonsingular_of_Δ_ne_zero (hW.Δ_ne_zero h2 h3 hm)).mp hE
    refine ⟨.some x _ hN, ?_, ?_⟩
    · by_cases hxA : x = -3 * m
      · rw [uA_some_of_eq hW h2 h3 hm hN hxA]
        have ht0 : t ≠ 0 := by
          rintro rfl
          apply hm
          have : x - m = 0 := by rw [ht]; ring
          rw [hxA] at this
          have h4 : (4 : F) * m = 0 := by linear_combination -this
          have h4' : (4 : F) ≠ 0 := by
            rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
          exact (mul_eq_zero.mp h4).resolve_left h4'
        refine (isSquare_div_iff ha).mpr ⟨4 * m * r / t, ?_⟩
        have e1 : (a : F) * (4 * m * r / t) ^ 2 = 16 * m ^ 2 * (a * b * r ^ 2) / (b * t ^ 2) := by
          field_simp; try ring
        rw [e1, ← hr, ← ht, hxA, eq_div_iff]
        · ring
        · intro h0
          apply hm
          have h4 : (4 : F) * m = 0 := by linear_combination -h0
          have h4' : (4 : F) ≠ 0 := by
            rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
          exact (mul_eq_zero.mp h4).resolve_left h4'
      · rw [uA_some_of_ne hW h2 h3 hm hN hxA]
        exact (isSquare_div_iff ha).mpr ⟨s, hs⟩
    · by_cases hxB : x = m
      · rw [uB_some_of_eq hW h2 h3 hm hN hxB]
        have hs0 : s ≠ 0 := by
          rintro rfl
          apply hm
          have : x + 3 * m = 0 := by rw [hs]; ring
          rw [hxB] at this
          have h4 : (4 : F) * m = 0 := by linear_combination this
          have h4' : (4 : F) ≠ 0 := by
            rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
          exact (mul_eq_zero.mp h4).resolve_left h4'
        refine (isSquare_div_iff hb).mpr ⟨4 * m * r / s, ?_⟩
        have e1 : (b : F) * (4 * m * r / s) ^ 2 = 16 * m ^ 2 * (a * b * r ^ 2) / (a * s ^ 2) := by
          field_simp; try ring
        rw [e1, ← hr, ← hs, hxB, eq_div_iff]
        · ring
        · intro h0
          apply hm
          have h4 : (4 : F) * m = 0 := by linear_combination h0
          have h4' : (4 : F) ≠ 0 := by
            rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
          exact (mul_eq_zero.mp h4).resolve_left h4'
      · rw [uB_some_of_ne hW h2 h3 hm hN hxB]
        exact (isSquare_div_iff hb).mpr ⟨t, ht⟩

/-- **`LocM` is the image of the descent map**, Silverman X.1.4 in the x-form of `Defs.lean`. -/
theorem locM_iff_exists_point (a b : Fˣ) :
    LocM F m a b ↔ ∃ P : W.toAffine.Point, IsSquare ((uA hW h2 h3 hm P : F) / a) ∧
      IsSquare ((uB hW h2 h3 hm P : F) / b) :=
  ⟨exists_point_of_locM hW h2 h3 hm a b,
    fun ⟨P, hA, hB⟩ => locM_of_point hW h2 h3 hm a b P hA hB⟩

end Descent

/-! ### The local condition -/

section Local

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq K] [DecidableEq L]
  {E : WeierstrassCurve K} {ℓ : K} (hE : IsCurveE E ℓ) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
  (hℓ : ℓ ≠ 0)

omit [DecidableEq K] [DecidableEq L] in
theorem ne_zero_map {x : K} (hx : x ≠ 0) : algebraMap K L x ≠ 0 :=
  (map_ne_zero (algebraMap K L)).mpr hx

omit [DecidableEq K] [DecidableEq L] in
theorem two_ne_zero_map (h2 : (2 : K) ≠ 0) : (2 : L) ≠ 0 := by
  have := ne_zero_map (L := L) h2; rwa [map_ofNat] at this

omit [DecidableEq K] [DecidableEq L] in
theorem three_ne_zero_map (h3 : (3 : K) ≠ 0) : (3 : L) ≠ 0 := by
  have := ne_zero_map (L := L) h3; rwa [map_ofNat] at this

variable [E.IsElliptic] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- **Restriction carries `χ_A(c)` to `χ_A(res c)`.** -/
theorem chiA_torsionRes (c : H1 (AbsoluteGaloisGroup K) (E.TorsionCoeff 2)) :
    explicitCoeff1 _ _ (chiA (hE.baseChange L) (two_ne_zero_map h2) (three_ne_zero_map h3)
        (ne_zero_map hℓ)) continuous_of_discreteTopology (E.torsionRes τ 2 c) =
      explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange 2 τ)
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul 2 τ)
        (explicitCoeff1 _ _ (chiA hE h2 h3 hℓ) continuous_of_discreteTopology c) := by
  unfold chiA
  exact (explicitMap1_explicitCoeff1_twoTorsionCharacter τ _ _ _ _ _ _
    (by rw [map_mul, map_neg, map_ofNat]) (map_zero _).symm c).symm

/-- **Restriction carries `χ_B(c)` to `χ_B(res c)`.** -/
theorem chiB_torsionRes (c : H1 (AbsoluteGaloisGroup K) (E.TorsionCoeff 2)) :
    explicitCoeff1 _ _ (chiB (hE.baseChange L) (two_ne_zero_map h2) (three_ne_zero_map h3)
        (ne_zero_map hℓ)) continuous_of_discreteTopology (E.torsionRes τ 2 c) =
      explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange 2 τ)
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul 2 τ)
        (explicitCoeff1 _ _ (chiB hE h2 h3 hℓ) continuous_of_discreteTopology c) := by
  unfold chiB
  exact (explicitMap1_explicitCoeff1_twoTorsionCharacter τ _ _ _ _ _ _ rfl (map_zero _).symm c).symm

/-- **The local condition at `L`, in the x-form.** Let `c ∈ H¹(G_K, E[2])` have characters
`χ_A(c) = κ(a)`, `χ_B(c) = κ(b)` (Kummer classes of `a, b ∈ K*`). Its restriction to `G_L` is the
local Kummer class of a point of `E(L)` iff `LocM L ℓ a b`. -/
theorem torsionRes_mem_range_kummerMap_iff (a b : Kˣ)
    (c : H1 (AbsoluteGaloisGroup K) (E.TorsionCoeff 2))
    (ha : explicitCoeff1 _ _ (chiA hE h2 h3 hℓ) continuous_of_discreteTopology c =
      (TauCeti.kummerMap K 2 (isUnit_two_nat h2) a).toAdd)
    (hb : explicitCoeff1 _ _ (chiB hE h2 h3 hℓ) continuous_of_discreteTopology c =
      (TauCeti.kummerMap K 2 (isUnit_two_nat h2) b).toAdd) :
    E.torsionRes τ 2 c ∈
        ((E.baseChange L).kummerMap 2 (isUnit_two_nat (two_ne_zero_map h2))).range ↔
      LocM L (algebraMap K L ℓ) (algebraMap K L a) (algebraMap K L b) := by
  set hW := hE.baseChange L
  set h2' : (2 : L) ≠ 0 := two_ne_zero_map h2
  set h3' : (3 : L) ≠ 0 := three_ne_zero_map h3
  set hℓ' : algebraMap K L ℓ ≠ 0 := ne_zero_map hℓ
  set aL : Lˣ := Units.map (algebraMap K L : K →* L) a
  set bL : Lˣ := Units.map (algebraMap K L : K →* L) b
  have hu' : IsUnit ((2 : ℕ) : L) := isUnit_two_nat h2'
  have hA' : explicitCoeff1 _ _ (chiA hW h2' h3' hℓ') continuous_of_discreteTopology
      (E.torsionRes τ 2 c) = (TauCeti.kummerMap L 2 hu' aL).toAdd := by
    rw [chiA_torsionRes hE h2 h3 hℓ τ c, ha, explicitMap1_kummerMap 2 τ (isUnit_two_nat h2) a]
  have hB' : explicitCoeff1 _ _ (chiB hW h2' h3' hℓ') continuous_of_discreteTopology
      (E.torsionRes τ 2 c) = (TauCeti.kummerMap L 2 hu' bL).toAdd := by
    rw [chiB_torsionRes hE h2 h3 hℓ τ c, hb, explicitMap1_kummerMap 2 τ (isUnit_two_nat h2) b]
  have hPA : ∀ P : (E.baseChange L).toAffine.Point,
      explicitCoeff1 _ _ (chiA hW h2' h3' hℓ') continuous_of_discreteTopology
        ((E.baseChange L).kummerMap 2 hu' P) =
        (TauCeti.kummerMap L 2 hu' (uA hW h2' h3' hℓ' P)).toAdd := fun P =>
    explicitCoeff1_twoTorsionCharacter_kummerMap _ _ hu' P
  have hPB : ∀ P : (E.baseChange L).toAffine.Point,
      explicitCoeff1 _ _ (chiB hW h2' h3' hℓ') continuous_of_discreteTopology
        ((E.baseChange L).kummerMap 2 hu' P) =
        (TauCeti.kummerMap L 2 hu' (uB hW h2' h3' hℓ' P)).toAdd := fun P =>
    explicitCoeff1_twoTorsionCharacter_kummerMap _ _ hu' P
  have haL : (aL : L) = algebraMap K L a := rfl
  have hbL : (bL : L) = algebraMap K L b := rfl
  constructor
  · rintro ⟨P, hP⟩
    have e1 := hPA P
    have e2 := hPB P
    rw [hP, hA'] at e1
    rw [hP, hB'] at e2
    have sA : IsSquare ((uA hW h2' h3' hℓ' P : L) / aL) :=
      (kummerMap_eq_iff hu' _ _).mp (Multiplicative.toAdd.injective e1).symm
    have sB : IsSquare ((uB hW h2' h3' hℓ' P : L) / bL) :=
      (kummerMap_eq_iff hu' _ _).mp (Multiplicative.toAdd.injective e2).symm
    have := locM_of_point hW h2' h3' hℓ' aL bL P sA sB
    rwa [haL, hbL] at this
  · intro hloc
    rw [← haL, ← hbL] at hloc
    obtain ⟨P, sA, sB⟩ := exists_point_of_locM hW h2' h3' hℓ' aL bL hloc
    refine ⟨P, ?_⟩
    have kA := (kummerMap_eq_iff hu' _ _).mpr sA
    have kB := (kummerMap_eq_iff hu' _ _).mpr sB
    refine eq_of_chi hW h2' h3' hℓ' ?_ ?_
    · rw [hPA, hA', kA]
    · rw [hPB, hB', kB]

end Local

end ZInQ.Manuscript.PoleRC.SelMTauCeti
