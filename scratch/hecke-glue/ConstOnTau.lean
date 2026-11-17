import ZInQKernel.Contrib.OneProof.HeckePin
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension

noncomputable section

namespace AfTateLam.HeckeGlue

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open AfTateLam.HeckePin

/-! ## 1. The `j`-function on `ℍ` -/

/-- `j(τ)` (`= jL(pp τ)`). -/
def jfun (τ : UpperHalfPlane) : ℂ := X1Igusa.Weber.Jf (τ : ℂ)

theorem continuous_jfun : Continuous jfun :=
  X1Igusa.Weber.diffOn_Jf.continuousOn.comp_continuous UpperHalfPlane.continuous_coe
    fun τ => τ.coe_im_pos

theorem jfun_I : jfun UpperHalfPlane.I = 1728 := X1Igusa.Weber.Jf_I

theorem jfun_ρ : jfun X1Igusa.Weber.τρ = 0 := X1Igusa.Weber.Jf_ρ

open Polynomial in
theorem evAn_CX (N : ℕ) (τ : UpperHalfPlane) :
    X1Igusa.Weber.evAn N (AfTateOr.toQ (C X)) τ = jfun τ := by
  simp [X1Igusa.Weber.evAn, AfTateOr.toQ, jfun, X1Igusa.Weber.Jf]

theorem evAn_one (N : ℕ) (τ : UpperHalfPlane) :
    X1Igusa.Weber.evAn N (AfTateOr.toQ 1) τ = 1 := by
  simp [X1Igusa.Weber.evAn, AfTateOr.toQ]

open Polynomial in
theorem ev2_CX {K : Type*} [CommRing K] (a b : K) : AfTateOr.ev2 (C X) a b = a := by
  simp [AfTateOr.ev2]

theorem ev2_one {K : Type*} [CommRing K] (a b : K) : AfTateOr.ev2 1 a b = 1 := by
  simp [AfTateOr.ev2]

variable {N : ℕ} {X : Over SpecQ} [IsIntegral X.left]

/-- `j_X` is regular at `x_τ` with value `j(τ)`. -/
theorem regAt_jX {jX tX : X.left.functionField} {x : CPt X} {τ : UpperHalfPlane}
    (h : AtTau N jX tX x τ) : RegAt x jX (jfun τ) := by
  have := h (Polynomial.C Polynomial.X) 1 (jfun τ) (by rw [ev2_one]; exact one_ne_zero) (by
    simp only [evAn_CX, evAn_one, div_one]
    exact (continuous_jfun.tendsto τ).mono_left nhdsWithin_le_nhds)
  rwa [ev2_CX, ev2_one, div_one] at this

open Polynomial in
/-- `j_X ≠ 0` in `K(X)`. -/
theorem jX_ne_zero {jX tX : X.left.functionField} (hG : IsX1Gen N X jX tX) : jX ≠ 0 := by
  intro h0
  have := (hG.2 (Polynomial.C Polynomial.X)).1 (by rw [ev2_CX]; exact h0)
  obtain ⟨z, hz, h2, h3⟩ := X1Igusa.Weber.exists_good_point
  have h := this (UpperHalfPlane.ofComplex z) h2 h3
  rw [evAn_CX] at h
  have hJ : X1Igusa.Weber.Jf z ≠ 0 := by
    rw [X1Igusa.Weber.Jf_eq]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h2)) (X1Igusa.Weber.Dlf_ne z)
  apply hJ
  simpa [jfun, X1Igusa.Weber.Jf, X1Igusa.Weber.ofComplex_coe hz] using h


/-! ## 2. Regular functions at complex points -/

/-- The point of `X` under a complex point. -/
abbrev cpt (x : CPt X) : X.left := x.left (IsLocalRing.closedPoint ℂ)

/-- The value of a rational function at a complex point is unique. -/
theorem regAt_unique {x : CPt X} {a : X.left.functionField} {c c' : ℂ}
    (h : RegAt x a c) (h' : RegAt x a c') : c = c' := by
  obtain ⟨U, hU, s, hle, hs, rfl⟩ := h
  obtain ⟨U', hU', s', hle', hs', rfl⟩ := h'
  have hle'' : ⊤ ≤ x.left ⁻¹ᵁ (U ⊓ U') := fun p hp => ⟨hle hp, hle' hp⟩
  have hne : Nonempty (U ⊓ U' : X.left.Opens) :=
    ⟨⟨cpt x, hle'' (Set.mem_univ (IsLocalRing.closedPoint ℂ))⟩⟩
  have e1 : X.left.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op s =
      X.left.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op s' := by
    apply X.left.germToFunctionField_injective (U ⊓ U')
    simp only [Scheme.germToFunctionField, TopCat.Presheaf.germ_res_apply]
    exact hs.trans hs'.symm
  have a1 := congrArg (fun φ => φ.hom s)
    (Scheme.Hom.map_appLE x.left hle'' (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op)
  have a2 := congrArg (fun φ => φ.hom s')
    (Scheme.Hom.map_appLE x.left hle'' (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op)
  simp only [CommRingCat.comp_apply] at a1 a2
  rw [← a1, ← a2, e1]

theorem value_ne_zero_aux {Y : Scheme} (f : Spec (CommRingCat.of ℂ) ⟶ Y) {U : Y.Opens}
    (s : Γ(Y, U)) (hle : ⊤ ≤ f ⁻¹ᵁ U) (h : f (IsLocalRing.closedPoint ℂ) ∈ Y.basicOpen s) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (f.appLE U ⊤ hle s) ≠ 0 := by
  intro h0
  have h1 : f.appLE U ⊤ hle s = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom h0
    rwa [map_zero, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at this
  have h2 := Scheme.basicOpen_appLE f ⊤ U hle s
  rw [h1, Scheme.basicOpen_zero] at h2
  have h3 : IsLocalRing.closedPoint ℂ ∈ (⊥ : (Spec (CommRingCat.of ℂ)).Opens) := by
    rw [h2]; exact ⟨trivial, h⟩
  exact h3

/-- At the generic point a nonzero rational function has a nonzero value. -/
theorem regAt_ne_zero_of_generic {x : CPt X} {a : X.left.functionField} {c : ℂ}
    (h : RegAt x a c) (ha : a ≠ 0) (hx : cpt x = genericPoint X.left) : c ≠ 0 := by
  obtain ⟨U, hU, s, hle, hs, rfl⟩ := h
  have hη : genericPoint X.left ∈ X.left.basicOpen s := by
    rw [X.left.mem_basicOpen'']
    refine ⟨((genericPoint_spec X.left).mem_open_set_iff U.isOpen).mpr (by simpa using hU), ?_⟩
    have : X.left.germToFunctionField U s = a := hs
    rw [isUnit_iff_ne_zero]
    exact this ▸ ha
  rw [← hx] at hη
  exact value_ne_zero_aux x.left s hle hη

/-! ## 3. Finitely many complex points over finitely many closed points -/

/-- A closed point of a `ℚ`-scheme of finite type has finitely many embeddings `κ(p) → ℂ`. -/
theorem finite_residueField_hom [LocallyOfFiniteType X.hom] (p : X.left) (hp : IsClosed {p}) :
    Finite (X.left.residueField p ⟶ CommRingCat.of ℂ) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have h1 : LocallyOfFiniteType (X.left.fromSpecResidueField p) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hp
  have h2 : LocallyOfFiniteType (X.left.fromSpecResidueField p ≫ X.hom) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.fromSpecResidueField p ≫ X.hom)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h2
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType ℚ (X.left.residueField p) := h2
  have : Module.Finite ℚ (X.left.residueField p) := finite_of_finite_type_of_isJacobsonRing ℚ _
  refine Finite.of_injective (β := X.left.residueField p →ₐ[ℚ] ℂ)
    (fun f => { f.hom with commutes' := fun r => ?_ }) ?_
  · change (f.hom.comp φ.hom) r = algebraMap ℚ ℂ r
    rw [RingHom.ext_rat (f.hom.comp φ.hom) (algebraMap ℚ ℂ)]
  · intro f g h
    ext a
    exact congrArg (fun u : X.left.residueField p →ₐ[ℚ] ℂ => u a) h

/-- Finitely many complex points lie over a finite set of closed points. -/
theorem finite_cpts [LocallyOfFiniteType X.hom] {F : Set X.left} (hF : F.Finite)
    (hcl : ∀ p ∈ F, IsClosed {p}) : {y : CPt X | cpt y ∈ F}.Finite := by
  let e := Scheme.SpecToEquivOfField ℂ X.left
  have hinj : Function.Injective (fun y : CPt X => e y.left) := fun y y' h =>
    Over.OverMorphism.ext (e.injective h)
  have hS : {σ : Σ p, X.left.residueField p ⟶ CommRingCat.of ℂ | σ.1 ∈ F}.Finite := by
    have : {σ : Σ p, X.left.residueField p ⟶ CommRingCat.of ℂ | σ.1 ∈ F} =
        ⋃ p ∈ F, Set.range (Sigma.mk p) := by
      ext ⟨p, f⟩; simp
    rw [this]
    exact hF.biUnion fun p hp => by
      have := finite_residueField_hom p (hcl p hp); exact Set.finite_range _
  exact (hS.preimage hinj.injOn).subset fun y hy => hy

/-! ## 4. Ring homomorphisms out of a field with a map to `ℚ` -/

theorem ringHom_ext_of_toRat {k K : Type*} [Field k] [Field K] (ψ : k →+* ℚ)
    (f₁ f₂ : k →+* K) : f₁ = f₂ := by
  have : CharZero k := RingHom.charZero ψ
  have key : ∀ a, (Rat.castHom k) (ψ a) = a := fun a => ψ.injective (by
    have := RingHom.ext_rat (ψ.comp (Rat.castHom k)) (RingHom.id ℚ)
    exact congrArg (fun u : ℚ →+* ℚ => u (ψ a)) this)
  ext a
  rw [← key a]
  exact congrArg (fun u : ℚ →+* K => u (ψ a))
    (RingHom.ext_rat (f₁.comp (Rat.castHom k)) (f₂.comp (Rat.castHom k)))


/-! ## 5. `ConstOnTauPoints` from `X1TauPoints` -/

/-- **`ConstOnTauPoints` holds, given `X1TauPoints`.** -/
theorem constOnTauPoints_of_x1TauPoints (hP : X1TauPoints) : ConstOnTauPoints := by
  classical
  intro N hN X _ jX tX hC hG P₀ J g hP₀ hc
  choose x hx using hP N hN X jX tX hC hG
  have : IsProper X.hom := hC.proper
  have : SmoothOfRelativeDimension 1 X.hom := hC.smooth
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have hdim : topologicalKrullDim X.left ≤ 1 := by
    exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension X.hom 1
  -- `x_ρ` lies over a closed point
  have hρ : IsClosed {cpt (x X1Igusa.Weber.τρ)} := by
    by_contra hnc
    exact regAt_ne_zero_of_generic (regAt_jX (hx _)) (jX_ne_zero hG)
      (Scheme.eq_genericPoint_of_not_isClosed hdim hnc) jfun_ρ
  have : JacobsonSpace J.X.left := LocallyOfFiniteType.jacobsonSpace J.X.hom
  have : LocallyOfFiniteType g.left := by
    have : LocallyOfFiniteType (g.left ≫ J.X.hom) := by rw [Over.w g]; infer_instance
    exact locallyOfFiniteType_of_comp g.left J.X.hom
  set q := g.left (cpt (x X1Igusa.Weber.τρ)) with hqdef
  have hq : IsClosed {q} := g.left.closedPoints_subset_preimage_closedPoints hρ
  have hpq : ∀ τ, g.left (cpt (x τ)) = q := fun τ => by
    have h := hc τ X1Igusa.Weber.τρ (x τ) (x X1Igusa.Weber.τρ) (hx τ) (hx _)
    have := congrArg (fun h : ptObj (K := ℚ) ℂ ⟶ J.X => h.left (IsLocalRing.closedPoint ℂ)) h
    exact this
  -- the generic point maps to `q`
  have hη : g.left (genericPoint X.left) = q := by
    by_contra hne
    have hopen : IsOpen (g.left ⁻¹' {q})ᶜ := (hq.preimage g.left.continuous).isOpen_compl
    have hF := IsOpen.finite_compl_of_topologicalKrullDim_le_one hdim hopen
      ⟨genericPoint X.left, hne⟩
    rw [compl_compl] at hF
    have hcl : ∀ r ∈ g.left ⁻¹' {q}, IsClosed ({r} : Set X.left) := fun r hr => by
      by_contra h
      exact hne (Scheme.eq_genericPoint_of_not_isClosed hdim h ▸ hr)
    have hS := finite_cpts hF hcl
    let val : CPt X → ℂ := fun y => if h : ∃ c, RegAt y jX c then h.choose else 0
    have hval : ∀ τ, jfun τ = val (x τ) := fun τ => by
      have h1 := regAt_jX (hx τ)
      have h2 : ∃ c, RegAt (x τ) jX c := ⟨_, h1⟩
      simp only [val, dite_eq_left h2]
      exact regAt_unique h1 h2.choose_spec
    have hrange : (Set.range jfun).Countable := by
      refine ((hS.image val).subset ?_).countable
      rintro _ ⟨τ, rfl⟩
      exact ⟨x τ, hpq τ, (hval τ).symm⟩
    have := const_of_countable continuous_jfun hrange UpperHalfPlane.I X1Igusa.Weber.τρ
    rw [jfun_I, jfun_ρ] at this
    norm_num at this
  -- the identity point is `q`
  have hηJ : ∀ a : SpecQ, (η[J.X] : 𝟙_ (Over SpecQ) ⟶ J.X).left a = q := by
    intro a
    have h1 : (P₀ ≫ g).left a = (η[J.X] : 𝟙_ (Over SpecQ) ⟶ J.X).left a := by
      rw [hP₀, Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over SpecQ))) (𝟙 _), Category.id_comp]
    rw [← h1, Over.comp_left, Scheme.Hom.comp_apply]
    have h2 : genericPoint X.left ⤳ P₀.left a := genericPoint_specializes _
    have h3 := h2.map g.left.continuous
    rw [hη] at h3
    exact h3.mem_closed hq rfl
  -- conclusion at the generic point
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq g.left (1 : X ⟶ J.X).left J.X.hom {genericPoint X.left}
    (dense_iff_closure_eq.mpr (genericPoint_spec X.left).def) ?_
    (by rw [Over.w g, Over.w (1 : X ⟶ J.X)])
  rintro r rfl
  apply (Scheme.SpecToEquivOfField _ J.X.left).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  have e1 : (X.left.fromSpecResidueField (genericPoint X.left) ≫ g.left)
      (IsLocalRing.closedPoint _) = q := by
    change g.left ((X.left.fromSpecResidueField (genericPoint X.left)) (IsLocalRing.closedPoint _)) = q
    rw [← hη]; congr 1; exact Scheme.fromSpecResidueField_apply _ _
  have e2 : (X.left.fromSpecResidueField (genericPoint X.left) ≫ (1 : X ⟶ J.X).left)
      (IsLocalRing.closedPoint _) = q := by
    exact hηJ _
  refine ⟨e1.trans e2.symm, ?_⟩
  have hψ : ∀ y : J.X.left, y = q → Nonempty (J.X.left.residueField y ⟶ CommRingCat.of ℚ) := by
    rintro y rfl
    let f0 : Spec (CommRingCat.of ℚ) ⟶ J.X.left := (η[J.X] : 𝟙_ (Over SpecQ) ⟶ J.X).left
    have h0 : f0 (IsLocalRing.closedPoint ℚ) = q := hηJ _
    exact ⟨(J.X.left.residueFieldCongr h0.symm).hom ≫
      J.X.left.descResidueField (Scheme.stalkClosedPointTo f0)⟩
  obtain ⟨ψ⟩ := hψ _ e1
  apply CommRingCat.hom_ext
  exact ringHom_ext_of_toRat ψ.hom _ _

end AfTateLam.HeckeGlue
