import ZInQKernel.Contrib.BrauerT14T15.Kummer2
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.BaseChange

/-!
# The Brauer class of a `ℤ/2`-cocycle of `G_ℚ`, and its base change

For a continuous `ℤ/2`-cocycle `ε` of Mathlib's `G_ℚ = Field.absoluteGaloisGroup ℚ`, `brClass ε`
is the class of `(-1)^ε` in Tau Ceti's `Br ℚ = H²(G_ℚ, (ℚˢ)ˣ)`.  The main result,
`brBaseChange_brClass_eq_zero_iff`, says that for every field `F ⊇ ℚ` (of characteristic zero)

  `brBaseChange ℚ F (brClass ε) = 0  ↔  IsCoboundary2 (resC F ε)`,

where `resC F` is the kernel's restriction along Mathlib's `Field.absoluteGaloisGroup.map`.  Two
inputs: the commutative square relating Mathlib's map of absolute Galois groups (built from
`IsAlgClosed.lift`) to Tau Ceti's `absoluteGaloisGroupMap τ` for the induced embedding of
separable closures `τ` (`square`), and the Kummer bridge (`Kummer2.lean`) over `F`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

namespace ZInQ.Contrib.BrauerT14T15

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory PkgI6

section Square

variable {K L : Type} [Field K] [Field L]

/-- Mathlib's chosen embedding of algebraic closures along `f : K →+* L` (the one used by
`Field.absoluteGaloisGroup.map f`). -/
noncomputable def algClosureLift (f : K →+* L) : AlgebraicClosure K →+* AlgebraicClosure L :=
  letI : Algebra K L := f.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom

lemma algClosureLift_map (f : K →+* L) (σ : Field.absoluteGaloisGroup L)
    (x : AlgebraicClosure K) :
    algClosureLift f (DFunLike.coe (F := Gal(AlgebraicClosure K/K))
        (Field.absoluteGaloisGroup.map f σ) x) =
      DFunLike.coe (F := Gal(AlgebraicClosure L/L)) σ (algClosureLift f x) := by
  let : Algebra K L := f.toAlgebra
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure L) :=
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toAlgebra
  exact absoluteGaloisGroup_mapOfAlgebra_commutes K L σ x

end Square

attribute [-instance] DivisionRing.toRatAlgebra

section RatSquare

variable (F : Type) [Field F] [Algebra ℚ F] [CharZero F]

omit [Algebra ℚ F] in
lemma mem_separableClosure_of_charZero (y : AlgebraicClosure F) :
    y ∈ separableClosure F (AlgebraicClosure F) :=
  mem_separableClosure_iff.mpr (Algebra.IsSeparable.isSeparable F y)

/-- The embedding `ℚˢ → Fˢ` of separable closures induced by Mathlib's `algClosureLift`. -/
noncomputable def sepLift : SeparableClosure ℚ →+* SeparableClosure F where
  toFun x := ⟨algClosureLift (algebraMap ℚ F) (x : AlgebraicClosure ℚ),
    mem_separableClosure_of_charZero F _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

lemma coe_sepLift (x : SeparableClosure ℚ) :
    ((sepLift F x : SeparableClosure F) : AlgebraicClosure F) =
      algClosureLift (algebraMap ℚ F) (x : AlgebraicClosure ℚ) := rfl

/-- `sepLift` as a `ℚ`-algebra map. -/
noncomputable def sepLiftAlg : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure F :=
  { sepLift F with
    commutes' := fun r => congrArg (fun f : ℚ →+* SeparableClosure F => f r)
      (Subsingleton.elim ((sepLift F).comp (algebraMap ℚ (SeparableClosure ℚ)))
        (algebraMap ℚ (SeparableClosure F))) }

lemma coe_sepLiftAlg (x : SeparableClosure ℚ) :
    ((sepLiftAlg F x : SeparableClosure F) : AlgebraicClosure F) =
      algClosureLift (algebraMap ℚ F) (x : AlgebraicClosure ℚ) := rfl

/-- **The square**: Tau Ceti's `absoluteGaloisGroupMap` along `sepLiftAlg F`, read through the
restriction isomorphisms, is Mathlib's `Field.absoluteGaloisGroup.map (algebraMap ℚ F)`. -/
theorem square (σ : Field.absoluteGaloisGroup F) :
    absoluteGaloisGroupMap (sepLiftAlg F) (absoluteGaloisGroupRestrictEquiv F σ) =
      absoluteGaloisGroupRestrictEquiv ℚ (Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ) := by
  rw [absoluteGaloisGroupMap_eq_iff]
  intro x
  apply Subtype.ext
  have e1 := coe_absoluteGaloisGroupRestrictEquiv_apply (K := F) σ (sepLiftAlg F x)
  have e2 := coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ)
    (Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ) x
  rw [coe_sepLiftAlg]
  refine e1.trans ?_
  rw [coe_sepLiftAlg, e2, algClosureLift_map]

end RatSquare

/-! ### The Brauer class of a `ℤ/2`-cocycle -/

local notation "rQ" => absoluteGaloisGroupRestrictEquiv ℚ

/-- A cochain on Mathlib's `G_ℚ`, read on Tau Ceti's `Gal(ℚˢ/ℚ)`. -/
noncomputable def toSep (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2) :
    AbsoluteGaloisGroup ℚ → AbsoluteGaloisGroup ℚ → ZMod 2 :=
  fun a b => ε ((rQ).symm a) ((rQ).symm b)

lemma isCocycle2_toSep {ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2}
    (hε : IsCocycle2 ε) : IsCocycle2 (toSep ε) :=
  isCocycle2_comp (rQ).symm.toMonoidHom (rQ).symm.continuous hε

/-- **The Brauer class of a `ℤ/2`-cocycle `ε` of `G_ℚ`**: the class of `(-1)^ε` in `Br ℚ`. -/
noncomputable def brClass (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2)
    (hε : IsCocycle2 ε) : Br ℚ :=
  unitsRepH2Equiv ℚ (H2pi _ _ ⟨_, sgn_mem_Z2 (isCocycle2_toSep hε)⟩)

lemma unitsCoeffBaseChange_sgn {L : Type} [Field L] [Algebra ℚ L]
    (τ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure L) (a : ZMod 2) :
    unitsCoeffBaseChange τ (sgn ℚ a) = sgn L a := by
  fin_cases a
  · exact (map_zero _).trans (map_zero _).symm
  · change unitsCoeffBaseChange τ (sgn ℚ 1) = sgn L 1
    rw [sgn_one, sgn_one]
    apply Additive.toMul.injective
    apply Units.ext
    simp

/-- `brClass ε = 0` iff `ε` is a continuous coboundary. -/
theorem brClass_eq_zero_iff (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2)
    (hε : IsCocycle2 ε) : brClass ε hε = 0 ↔ IsCoboundary2 ε := by
  rw [brClass, AddEquivClass.map_eq_zero_iff]
  constructor
  · intro h
    have hB := H2pi_eq_zero_iff.mp h
    have := isCoboundary2_of_sgn_mem_B2 (K := ℚ) two_ne_zero (isCocycle2_toSep hε) hB
    have := isCoboundary2_comp (rQ).toMonoidHom (rQ).continuous this
    convert this using 1
    funext a b; simp [toSep]
  · intro h
    have := isCoboundary2_comp (rQ).symm.toMonoidHom (rQ).symm.continuous h
    exact H2pi_eq_zero_iff.mpr (sgn_mem_B2_of_isCoboundary2 (K := ℚ) this)

/-- **Base change of `brClass ε` to `F` vanishes iff `resC F ε` is a coboundary.** -/
theorem brBaseChange_brClass_eq_zero_iff (F : Type) [Field F] [Algebra ℚ F] [CharZero F]
    (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2) (hε : IsCocycle2 ε) :
    brBaseChange ℚ F (brClass ε hε) = 0 ↔ IsCoboundary2 (resC F ε) := by
  set τ := sepLiftAlg F
  set φ := absoluteGaloisGroupMap τ
  set δ : AbsoluteGaloisGroup F → AbsoluteGaloisGroup F → ZMod 2 :=
    fun a b => toSep ε (φ a) (φ b) with hδ
  have hδc : IsCocycle2 δ := isCocycle2_comp φ.toMonoidHom φ.continuous (isCocycle2_toSep hε)
  -- `δ` read on Mathlib's `G_F` is `resC F ε`.
  have hres : (fun a b => δ (absoluteGaloisGroupRestrictEquiv F a)
      (absoluteGaloisGroupRestrictEquiv F b)) = resC F ε := by
    funext a b
    simp only [hδ, φ, τ, square, toSep, ContinuousMulEquiv.symm_apply_apply, resC]
  have hres' : δ = fun a b => resC F ε ((absoluteGaloisGroupRestrictEquiv F).symm a)
      ((absoluteGaloisGroupRestrictEquiv F).symm b) := by
    rw [← hres]; funext a b; simp
  rw [brBaseChange_apply ℚ F τ, brClass, AddEquiv.symm_apply_apply, AddEquivClass.map_eq_zero_iff,
    QuotientAddGroup.mk'_apply, explicitMap2_mk]
  have hcoch : ((cocyclesMap2 _ _ _ _ φ (unitsCoeffBaseChange τ) continuous_of_discreteTopology
      (unitsCoeffBaseChange_smul τ) ⟨_, sgn_mem_Z2 (isCocycle2_toSep hε)⟩ :
        Z2 (AbsoluteGaloisGroup F) (UnitsCoeff F)) :
          AbsoluteGaloisGroup F × AbsoluteGaloisGroup F → UnitsCoeff F) =
      fun q => sgn F (δ q.1 q.2) := by
    funext q
    rw [cocyclesMap2_apply]
    exact unitsCoeffBaseChange_sgn τ _
  constructor
  · intro h
    have hB := H2pi_eq_zero_iff.mp h
    rw [hcoch] at hB
    have := isCoboundary2_of_sgn_mem_B2 (K := F) two_ne_zero hδc hB
    rw [← hres]
    exact isCoboundary2_comp (absoluteGaloisGroupRestrictEquiv F).toMonoidHom
      (absoluteGaloisGroupRestrictEquiv F).continuous this
  · intro h
    refine H2pi_eq_zero_iff.mpr ?_
    rw [hcoch]
    refine sgn_mem_B2_of_isCoboundary2 (K := F) ?_
    rw [hres']
    exact isCoboundary2_comp (absoluteGaloisGroupRestrictEquiv F).symm.toMonoidHom
      (absoluteGaloisGroupRestrictEquiv F).symm.continuous h

end ZInQ.Contrib.BrauerT14T15
