import ZInQKernel.Contrib.OneProof.CMHeight62.ShortModel
import ZInQKernel.Contrib.OneProof.CMHeight62Full.HodgeLineGlue

/-!
# cmHeight62 (finite place): the N13 instance on the tree (item H4)

The differential of the short model is `η_W = D.etaW 𝒢 = 𝒢.wedge ![tG]`, where `tG ∈ 𝔪_ξ` is the
germ of `−x/y` moved to the generic unit of the model (`ShortModel.tG`). This file supplies the
hosted part of node N13.

* `treeH4_etaW_eq`, `treeH4_abVarIdentity_eq`: `D.etaW 𝒢 = 𝒢.wedge ![D.tG 𝒢]`, and the identity
  `abVarIdentity` used by `tL` is the point `identityPoint` used by `originStalkEquiv`; both are
  definitional.
* `treeH4_tG_not_mem_sq`, `treeH4_tL_not_mem_sq`: `η_W ≠ 0` forces `tG ∉ 𝔪_ξ²`, hence
  `tL ∉ 𝔪_{E_L,0}²` (the shortcut of the design note: no ramification theory is needed).
* `treeH4_ord_tL`: for the identity place `P_L` of `K(E_L)` (its valuation ring is the image of
  the stalk at the identity), `ord_{P_L}(t_L) = 1`.
* `treeH4_mem_sq_of_ord`: a germ of `𝒪_{𝒢,ξ}` whose image in `K(E_L)` has order at least two at
  `P_L` lies in `𝔪_ξ²` (how node N2 is read in `𝒪_{𝒢,ξ}`).
* `treeH4_etaW_eq_smul`, `treeH4_comparison`: with the line `θ = 𝒢.wedge ![tS]` of the section
  parameter (`HodgeLineGlue`), a unit multiple `t₀` of it (node N12-alg) and
  `d · tG ≡ n · t₀ (mod 𝔪_ξ²)` with `u_C = n / d`, `η_W = b • θ` with `v(b) = v(u_C)`, and the
  tuple at `v` in the shape of `abs_norm_le_of_comparisons`.

The first three sections are general (places, local rings, wedges); the last uses the tree.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory IsLocalRing
open ZInQ.DefFaltings

/-! ## 1. Places: orders from the maximal ideal -/

section PlaceOrd

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : TauCeti.Place k F)

theorem tree34_exists_ord_one : ∃ t : F, t ≠ 0 ∧ P.ord t = 1 ∧ t ∈ P.integers := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have ht1 : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.1 ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [P.ord_zero] at ht1
    exact zero_ne_one ht1
  exact ⟨t, ht0, ht1, P.mem_integers_iff_ord_nonneg.2 (by omega)⟩

/-- An element of `𝒪_P` of order at least two lies in `𝔪_P²`. -/
theorem tree34_mem_sq_of_two_le_ord (a : P.integers) (ha : (a : F) ≠ 0 → 2 ≤ P.ord a) :
    a ∈ maximalIdeal P.integers ^ 2 := by
  by_cases ha0 : (a : F) = 0
  · rw [show a = 0 from Subtype.ext ha0]
    exact zero_mem _
  obtain ⟨t, ht0, ht1, htI⟩ := tree34_exists_ord_one P
  let tt : P.integers := ⟨t, htI⟩
  have htm : tt ∈ maximalIdeal P.integers :=
    (P.mem_maximalIdeal_iff_ord_pos (f := tt) ht0).2 (by change 0 < P.ord t; omega)
  have h2 := ha ha0
  have hq : (a : F) / (t * t) ∈ P.integers := by
    refine P.mem_integers_iff_ord_nonneg.2 ?_
    rw [P.ord_div ha0 (mul_ne_zero ht0 ht0), P.ord_mul ht0 ht0, ht1]
    omega
  have hdec : a = tt * tt * ⟨_, hq⟩ := by
    apply Subtype.ext
    change (a : F) = t * t * ((a : F) / (t * t))
    field_simp
  rw [hdec, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul htm htm)

/-- An element of `𝔪_P ∖ 𝔪_P²` has order one. -/
theorem tree34_ord_eq_one_of_not_mem_sq (a : P.integers) (ha : a ∈ maximalIdeal P.integers)
    (hsq : a ∉ maximalIdeal P.integers ^ 2) : P.ord (a : F) = 1 := by
  have ha0 : (a : F) ≠ 0 := by
    intro h
    apply hsq
    rw [show a = 0 from Subtype.ext h]
    exact zero_mem _
  have h1 : 0 < P.ord a := (P.mem_maximalIdeal_iff_ord_pos ha0).1 ha
  by_contra hne
  exact hsq (tree34_mem_sq_of_two_le_ord P a fun _ => by omega)

theorem tree34_valuation_of_ord {f : F} (hf : f ≠ 0) {n : ℕ} (h : P.ord f = -(n : ℤ)) :
    P.valuation f = WithZero.exp (1 : ℤ) ^ n := by
  rw [P.valuation_eq_exp_neg_ord hf, h, neg_neg, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_one]

end PlaceOrd

section PlaceMap

variable {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
  [Algebra k' F'] (P : TauCeti.Place k F) (Q : TauCeti.Place k' F') (ι : F →+* F')

/-- A ring map carrying `𝒪_P` into `𝒪_Q` carries elements of order zero to elements of order
zero. -/
theorem tree34_ord_map_eq_zero (hι : ∀ f, P.valuation f ≤ 1 → Q.valuation (ι f) ≤ 1) {f : F}
    (h0 : P.ord f = 0) : Q.ord (ι f) = 0 := by
  have h1 : 0 ≤ Q.ord (ι f) := Q.mem_integers_iff_ord_nonneg.1
    (hι f (P.mem_integers_iff_ord_nonneg.2 (by omega)))
  have h2 : 0 ≤ Q.ord (ι f⁻¹) := Q.mem_integers_iff_ord_nonneg.1
    (hι _ (P.mem_integers_iff_ord_nonneg.2 (by rw [P.ord_inv]; omega)))
  rw [map_inv₀, Q.ord_inv] at h2
  omega

/-- The pole orders of a Weierstrass pair from those of `−x/y` and `x³/y²`. -/
theorem tree34_ord_xy {x y : F'} (hx : x ≠ 0) (hy : y ≠ 0) (h1 : Q.ord (-x / y) = 1)
    (h0 : Q.ord (x ^ 3 / y ^ 2) = 0) : Q.ord x = -2 ∧ Q.ord y = -3 := by
  rw [Q.ord_div (neg_ne_zero.2 hx) hy, Q.ord_neg] at h1
  rw [Q.ord_div (pow_ne_zero 3 hx) (pow_ne_zero 2 hy), Q.ord_pow, Q.ord_pow] at h0
  push_cast at h0
  constructor <;> omega

end PlaceMap

/-! ## 2. Local rings and stalks -/

section LocalRing

theorem tree34_ringEquiv_mem_maximalIdeal {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) {x : A} (hx : x ∈ maximalIdeal A) :
    e x ∈ maximalIdeal B := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  simpa using hu.map (e.symm : B →+* A)

theorem tree34_mem_sq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) {x : A} (hx : e x ∈ maximalIdeal B ^ 2) :
    x ∈ maximalIdeal A ^ 2 := by
  by_contra h
  exact ringEquiv_notMem_maximalIdeal_sq e h hx

/-- The stalk at a point whose image in the function field is the valuation ring of a place,
as a ring isomorphism onto that valuation ring. -/
def tree34_stalkEquivIntegers {X : Scheme} [IsIntegral X] (x : X) {k : Type*} [Field k]
    [Algebra k X.functionField] (P : TauCeti.Place k X.functionField)
    (hP : (algebraMap (X.presheaf.stalk x) X.functionField).range = P.integers.toSubring) :
    X.presheaf.stalk x ≃+* P.integers :=
  RingEquiv.ofBijective ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
      P.integers.toSubring (fun a => hP ▸ ⟨a, rfl⟩))
    ⟨fun _ _ h => IsFractionRing.injective (X.presheaf.stalk x) X.functionField
        (congrArg Subtype.val h),
      fun ⟨a, ha⟩ => by
        obtain ⟨b, hb⟩ : a ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range :=
          hP.symm ▸ ha
        exact ⟨b, Subtype.ext hb⟩⟩

theorem tree34_stalkEquivIntegers_coe {X : Scheme} [IsIntegral X] (x : X) {k : Type*} [Field k]
    [Algebra k X.functionField] (P : TauCeti.Place k X.functionField)
    (hP : (algebraMap (X.presheaf.stalk x) X.functionField).range = P.integers.toSubring)
    (g : X.presheaf.stalk x) :
    ((tree34_stalkEquivIntegers x P hP g : P.integers) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField g := rfl

/-- A germ in `𝔪_x ∖ 𝔪_x²` at the centre of a place has order one there. -/
theorem tree34_ord_algebraMap_eq_one {X : Scheme} [IsIntegral X] (x : X) {k : Type*} [Field k]
    [Algebra k X.functionField] (P : TauCeti.Place k X.functionField)
    (hP : (algebraMap (X.presheaf.stalk x) X.functionField).range = P.integers.toSubring)
    {g : X.presheaf.stalk x} (hg : g ∈ maximalIdeal (X.presheaf.stalk x))
    (hsq : g ∉ maximalIdeal (X.presheaf.stalk x) ^ 2) :
    P.ord (algebraMap (X.presheaf.stalk x) X.functionField g) = 1 := by
  have h := tree34_ord_eq_one_of_not_mem_sq P (tree34_stalkEquivIntegers x P hP g)
    (tree34_ringEquiv_mem_maximalIdeal _ hg) (ringEquiv_notMem_maximalIdeal_sq _ hsq)
  rwa [tree34_stalkEquivIntegers_coe] at h

/-- Through a ring isomorphism `φ` onto the stalk at the centre of a place, an element whose
image has order at least two lies in `𝔪²`. -/
theorem tree34_mem_sq_of_ord {X : Scheme} [IsIntegral X] (x : X) {k : Type*} [Field k]
    [Algebra k X.functionField] (P : TauCeti.Place k X.functionField)
    (hP : (algebraMap (X.presheaf.stalk x) X.functionField).range = P.integers.toSubring)
    {A : Type*} [CommRing A] [IsLocalRing A] (φ : A ≃+* X.presheaf.stalk x) (a : A)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField (φ a) ≠ 0 →
      2 ≤ P.ord (algebraMap (X.presheaf.stalk x) X.functionField (φ a))) :
    a ∈ maximalIdeal A ^ 2 := by
  apply tree34_mem_sq_of_ringEquiv (φ.trans (tree34_stalkEquivIntegers x P hP))
  exact tree34_mem_sq_of_two_le_ord P _ ha

end LocalRing

/-! ## 3. Wedges of germs congruent modulo `𝔪_ξ²` -/

section Wedge

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] (𝒢 : GroupModel E L)

/-- `d • m = n • x` with `d ≠ 0` gives `1 ⊗ m = (n / d) • (1 ⊗ x)`. -/
theorem tree34_toHodgeOne_eq_div_smul {M : Type*} [AddCommGroup M] [Module (𝓞 L) M]
    {n d : 𝓞 L} (hd : d ≠ 0) {m x : M} (h : d • m = n • x) :
    toHodgeOne L m = (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) • toHodgeOne L x := by
  have hd0 : algebraMap (𝓞 L) L d ≠ 0 := by
    intro h0
    exact hd (IsFractionRing.injective (𝓞 L) L (by rw [h0, map_zero]))
  have key : algebraMap (𝓞 L) L d • toHodgeOne L m =
      algebraMap (𝓞 L) L n • toHodgeOne L x := by
    rw [algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul, h]
  calc toHodgeOne L m
      = (algebraMap (𝓞 L) L d)⁻¹ • (algebraMap (𝓞 L) L d • toHodgeOne L m) := by
        rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    _ = _ := by rw [key, smul_smul, div_eq_inv_mul]

/-- If `d · g ≡ n · h (mod 𝔪_ξ²)` with `n, d ∈ 𝓞_L`, `d ≠ 0`, then
`1 ⊗ dg = (n / d) • (1 ⊗ dh)`. -/
theorem tree34_wedge_eq_smul_of_sub_mem_sq (g h : maximalIdeal 𝒢.genStalk) {n d : 𝓞 L}
    (hd : d ≠ 0)
    (hsub : 𝒢.structMap d * (g : 𝒢.genStalk) - 𝒢.structMap n * (h : 𝒢.genStalk) ∈
      maximalIdeal 𝒢.genStalk ^ 2) :
    𝒢.wedge ![g] = (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) • 𝒢.wedge ![h] := by
  have hdg : 𝒢.structMap d * (g : 𝒢.genStalk) ∈ maximalIdeal 𝒢.genStalk :=
    Ideal.mul_mem_left _ _ g.2
  have hnh : 𝒢.structMap n * (h : 𝒢.genStalk) ∈ maximalIdeal 𝒢.genStalk :=
    Ideal.mul_mem_left _ _ h.2
  have hcot : d • 𝒢.dCls g = n • 𝒢.dCls h := by
    rw [smul_cotangent_def, smul_cotangent_def, ← dCls_mul 𝒢 _ g hdg, ← dCls_mul 𝒢 _ h hnh]
    exact (Ideal.toCotangent_eq _).2 hsub
  rw [wedge_eq_toHodgeOne, wedge_eq_toHodgeOne]
  exact tree34_toHodgeOne_eq_div_smul hd hcot

/-- **`η = b • θ` with `v(b) = v(n / d)`.** The line `θ = 𝒢.wedge ![tS]` comes from a generator
`τ` (`tS` its specialization), `t₀` is the specialization of `u · τ` for a unit `u` (node
N12-alg), and `d · g ≡ n · t₀ (mod 𝔪_ξ²)` (node N2 read in `𝒪_{𝒢,ξ}`). -/
theorem tree34_wedge_eq_smul_line (s : Spec (CommRingCat.of (𝓞 L)))
    (v : HeightOneSpectrum (𝓞 L)) (hs : s.asIdeal = v.asIdeal)
    (τ u : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) (hu : IsUnit u)
    (tS t₀ g : maximalIdeal 𝒢.genStalk)
    (htS : (tS : 𝒢.genStalk) =
      𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) τ)
    (ht₀ : (t₀ : 𝒢.genStalk) =
      𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) (u * τ))
    {n d : 𝓞 L} (hd : d ≠ 0)
    (hsub : 𝒢.structMap d * (g : 𝒢.genStalk) - 𝒢.structMap n * (t₀ : 𝒢.genStalk) ∈
      maximalIdeal 𝒢.genStalk ^ 2) :
    ∃ b : L, 𝒢.wedge ![g] = b • 𝒢.wedge ![tS] ∧
      v.valuation L b = v.valuation L (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) := by
  obtain ⟨r, hr, hθ⟩ := exists_wedge_eq_smul_of_isUnit 𝒢 s v hs τ u hu tS t₀ htS ht₀
  refine ⟨(algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) * r, ?_, ?_⟩
  · rw [tree34_wedge_eq_smul_of_sub_mem_sq 𝒢 g t₀ hd hsub, hθ, smul_smul]
  · rw [map_mul, hr, mul_one]

/-- **The comparison tuple at `v`** (the hypothesis `hcmp v` of `abs_norm_le_of_comparisons`)
for `η = 𝒢.wedge ![g]` and `u_C = n / d`. -/
theorem tree34_comparison_of_wedge (s : Spec (CommRingCat.of (𝓞 L)))
    (v : HeightOneSpectrum (𝓞 L)) (hs : s.asIdeal = v.asIdeal)
    (τ u : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) (hu : IsUnit u)
    (hker : RingHom.ker (𝒢.unitSection.stalkMap s).hom = Ideal.span {τ})
    (tS t₀ g : maximalIdeal 𝒢.genStalk)
    (htS : (tS : 𝒢.genStalk) =
      𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) τ)
    (ht₀ : (t₀ : 𝒢.genStalk) =
      𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) (u * τ))
    (hsq : (tS : 𝒢.genStalk) ∉ maximalIdeal 𝒢.genStalk ^ 2)
    (W : WeierstrassCurve K) (W₀ : WeierstrassCurve L) (hW₀ : v.valuation L W₀.Δ = 1)
    (C : WeierstrassCurve.VariableChange L) (hC : C⁻¹ • W.map (algebraMap K L) = W₀)
    {n d : 𝓞 L} (hd : d ≠ 0)
    (hCu : (C.u : L) = algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d)
    (hsub : 𝒢.structMap d * (g : 𝒢.genStalk) - 𝒢.structMap n * (t₀ : 𝒢.genStalk) ∈
      maximalIdeal 𝒢.genStalk ^ 2) :
    ∃ (W₀ : WeierstrassCurve L) (C : WeierstrassCurve.VariableChange L)
      (θ : 𝒢.hodgeSpace 1) (b : L), v.valuation L W₀.Δ = 1 ∧
        C⁻¹ • W.map (algebraMap K L) = W₀ ∧ θ ≠ 0 ∧
        (∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) ∧
        𝒢.wedge ![g] = b • θ ∧ v.valuation L (C.u : L) = v.valuation L b := by
  obtain ⟨b, hb, hbv⟩ := tree34_wedge_eq_smul_line 𝒢 s v hs τ u hu tS t₀ g htS ht₀ hd hsub
  refine ⟨W₀, C, 𝒢.wedge ![tS], b, hW₀, hC, wedge_ne_zero 𝒢 hsq,
    detLattice_one_le_line 𝒢 s v hs τ hker tS htS, hb, ?_⟩
  rw [hbv, hCu]

end Wedge

/-! ## 4. The tree: `η_W`, `t_G` and `t_L` -/

section Tree

open HDec.CMBranch.CMjBridges (abVar_isIntegral abVarFunctionFieldAlgebra AbVarFunctionField
  abVarIdentity)
open ZInQ.Contrib.CMHeight62 (ShortData)
open ZInQ.Contrib.RC53Assist.HodgeLineBinding (originStalkEquiv)
open ZInQ.Contrib.RC53Assist.S2aNumberField (identityPoint)

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

/-- `η_W = 𝒢.wedge ![tG]` (definition of `ShortModel.etaW`). -/
theorem treeH4_etaW_eq {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L) :
    D.etaW 𝒢 = 𝒢.wedge ![D.tG 𝒢] := rfl

/-- The identity `abVarIdentity` of `E_L` (used by `tL`) is the point `identityPoint` (used by
`originStalkEquiv`), definitionally. -/
theorem treeH4_abVarIdentity_eq {L : Type} [Field L] (B : PkgI3.AbVar L) :
    abVarIdentity B = identityPoint B.X := rfl

/-- **The shortcut of the design note.** `η_W ≠ 0` gives `tG ∉ 𝔪_ξ²`. -/
theorem treeH4_tG_not_mem_sq {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L)
    (hη : D.etaW 𝒢 ≠ 0) :
    ((D.tG 𝒢 : maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) ∉ maximalIdeal 𝒢.genStalk ^ 2 := by
  intro h
  apply hη
  rw [treeH4_etaW_eq, wedge_eq_toHodgeOne, (dCls_eq_zero_iff 𝒢 _).2 h, map_zero]

theorem treeH4_originStalkEquiv_tG {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type}
    [Field L] [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L) :
    originStalkEquiv 𝒢 (D.tG 𝒢 : 𝒢.genStalk) = D.tL (L := L) :=
  RingEquiv.apply_symm_apply _ _

/-- `η_W ≠ 0` gives `tL ∉ 𝔪_{E_L,0}²`. -/
theorem treeH4_tL_not_mem_sq {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L)
    (hη : D.etaW 𝒢 ≠ 0) :
    D.tL (L := L) ∉ maximalIdeal ((E.baseChange L).X.left.presheaf.stalk
      (abVarIdentity (E.baseChange L))) ^ 2 := by
  have h := ringEquiv_notMem_maximalIdeal_sq (originStalkEquiv 𝒢)
    (treeH4_tG_not_mem_sq D 𝒢 hη)
  rw [treeH4_originStalkEquiv_tG] at h
  exact h

/-- **`ord_{P_L}(t_L) = 1`** at the identity place `P_L` of `K(E_L)`. -/
theorem treeH4_ord_tL {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L)
    (hη : D.etaW 𝒢 ≠ 0) (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring) :
    PL.ord (algebraMap ((E.baseChange L).X.left.presheaf.stalk
      (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))
        (D.tL (L := L))) = 1 :=
  tree34_ord_algebraMap_eq_one (abVarIdentity (E.baseChange L)) PL hpL
    (ShortData.tL_mem (L := L) D) (treeH4_tL_not_mem_sq D 𝒢 hη)

/-- **Node N2 read in `𝒪_{𝒢,ξ}`.** A germ whose image in `K(E_L)` (through `originStalkEquiv`)
has order at least two at `P_L` lies in `𝔪_ξ²`. -/
theorem treeH4_mem_sq_of_ord {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (𝒢 : GroupModel E L)
    (PL : TauCeti.Place L (AbVarFunctionField (E.baseChange L)))
    (hpL : (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))).range =
      PL.integers.toSubring) (g : 𝒢.genStalk)
    (hg : algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
        (AbVarFunctionField (E.baseChange L)) (originStalkEquiv 𝒢 g) ≠ 0 →
      2 ≤ PL.ord (algebraMap ((E.baseChange L).X.left.presheaf.stalk
        (abVarIdentity (E.baseChange L))) (AbVarFunctionField (E.baseChange L))
          (originStalkEquiv 𝒢 g))) :
    g ∈ maximalIdeal 𝒢.genStalk ^ 2 :=
  tree34_mem_sq_of_ord (abVarIdentity (E.baseChange L)) PL hpL (originStalkEquiv 𝒢) g hg

/-- **`η_W = b • θ` with `v(b) = v(n / d)`** for the line `θ = 𝒢.wedge ![tS]`. -/
theorem treeH4_etaW_eq_smul {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L)
    (s : Spec (CommRingCat.of (𝓞 L))) (v : HeightOneSpectrum (𝓞 L))
    (hs : s.asIdeal = v.asIdeal) (τ u : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    (hu : IsUnit u) (tS t₀ : maximalIdeal 𝒢.genStalk)
    (htS : (tS : 𝒢.genStalk) =
      𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) τ)
    (ht₀ : (t₀ : 𝒢.genStalk) =
      𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) (u * τ))
    {n d : 𝓞 L} (hd : d ≠ 0)
    (hsub : 𝒢.structMap d * (D.tG 𝒢 : 𝒢.genStalk) - 𝒢.structMap n * (t₀ : 𝒢.genStalk) ∈
      maximalIdeal 𝒢.genStalk ^ 2) :
    ∃ b : L, D.etaW 𝒢 = b • 𝒢.wedge ![tS] ∧
      v.valuation L b = v.valuation L (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) :=
  tree34_wedge_eq_smul_line 𝒢 s v hs τ u hu tS t₀ (D.tG 𝒢) htS ht₀ hd hsub

/-- **Node N13 on the tree: the tuple `hcmp v` of `abs_norm_le_of_comparisons`** for
`W = D.W` and `η = D.etaW 𝒢`, from the line of the section parameter, the comparison
`C⁻¹ • W_L = W₀` with `v(Δ_{W₀}) = 1` and `u_C = n / d`, and `d · tG ≡ n · t₀ (mod 𝔪_ξ²)`. -/
theorem treeH4_comparison {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] (D : ShortData E) (𝒢 : GroupModel E L)
    (s : Spec (CommRingCat.of (𝓞 L))) (v : HeightOneSpectrum (𝓞 L))
    (hs : s.asIdeal = v.asIdeal) (τ u : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    (hu : IsUnit u) (hker : RingHom.ker (𝒢.unitSection.stalkMap s).hom = Ideal.span {τ})
    (tS t₀ : maximalIdeal 𝒢.genStalk)
    (htS : (tS : 𝒢.genStalk) =
      𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) τ)
    (ht₀ : (t₀ : 𝒢.genStalk) =
      𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) (u * τ))
    (hsq : (tS : 𝒢.genStalk) ∉ maximalIdeal 𝒢.genStalk ^ 2)
    (W₀ : WeierstrassCurve L) (hW₀ : v.valuation L W₀.Δ = 1)
    (C : WeierstrassCurve.VariableChange L) (hC : C⁻¹ • D.W.map (algebraMap K L) = W₀)
    {n d : 𝓞 L} (hd : d ≠ 0)
    (hCu : (C.u : L) = algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d)
    (hsub : 𝒢.structMap d * (D.tG 𝒢 : 𝒢.genStalk) - 𝒢.structMap n * (t₀ : 𝒢.genStalk) ∈
      maximalIdeal 𝒢.genStalk ^ 2) :
    ∃ (W₀ : WeierstrassCurve L) (C : WeierstrassCurve.VariableChange L)
      (θ : 𝒢.hodgeSpace 1) (b : L), v.valuation L W₀.Δ = 1 ∧
        C⁻¹ • D.W.map (algebraMap K L) = W₀ ∧ θ ≠ 0 ∧
        (∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) ∧
        D.etaW 𝒢 = b • θ ∧ v.valuation L (C.u : L) = v.valuation L b :=
  tree34_comparison_of_wedge 𝒢 s v hs τ u hu hker tS t₀ (D.tG 𝒢) htS ht₀ hsq D.W W₀ hW₀ C hC
    hd hCu hsub

end Tree

end ZInQ.Contrib.CMHeight62Full
