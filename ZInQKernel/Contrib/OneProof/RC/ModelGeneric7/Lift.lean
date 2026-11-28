import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelReducedFibres
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-! **Lifting cover points to the Witt vectors** (rc-model-generic7, item 3, piece (c); 3b (ii)).

For an algebraically closed field `k` of characteristic `ell` with an arbitrary
`Algebra (LocalIntegers ell) k`, every point of the universal exact-order cover
`UniversalExactOrderAlgebra ell N h₅ htame` over `k` lifts to a point over `W(k) = WittVector ell k`
whose constant coefficient is the given point (`exists_wittLift`).

* `wittLocalAlgebra ell k`: the `LocalIntegers ell`-algebra structure on `WittVector ell k`,
  `IsLocalization.lift` of `Int.castRingHom` (integers prime to `ell` have constant coefficient
  nonzero in `k`, hence are units, `WittVector.isUnit_of_coeff_zero_ne_zero`).
* The cover is smooth over `LocalIntegers ell`: the tree's private `detectorCover_smooth`
  (`RC/ModelLevels3/Y0LevelReducedFibres.lean`), reached with `open private`.
* The lift is Mathlib's `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` with
  `WittVector.isAdicCompleteIdealSpanP` (`k` is perfect, `IsAlgClosed.perfectRing`) and
  `WittVector.quotientPEquiv : W(k) ⧸ (ell) ≃+* k`, which is `LocalIntegers ell`-linear because
  ring maps out of `LocalIntegers ell` are unique (`IsLocalization.ringHom_ext`,
  `RingHom.ext_int`).

No Hensel citation is used. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric7

open WeierstrassCurve.ModelLevels WeierstrassCurve.ModelTorsion

open private detectorCover_smooth from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelReducedFibres

variable (ell : ℕ) [Fact ell.Prime]

/-- Ring maps out of `LocalIntegers ell` are unique. -/
theorem localIntegers_ringHom_ext {T : Type*} [Semiring T] (f g : LocalIntegers ell →+* T) :
    f = g :=
  IsLocalization.ringHom_ext (integerPrimeIdeal ell).primeCompl (RingHom.ext_int _ _)

variable (k : Type*) [Field k] [CharP k ell]

/-- Integers prime to `ell` are units in `W(k)`. -/
theorem wittVector_isUnit_intCast (z : (integerPrimeIdeal ell).primeCompl) :
    IsUnit (Int.castRingHom (WittVector ell k) z) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [eq_intCast, ← WittVector.constantCoeff_apply, map_intCast]
  intro h
  apply z.2
  rw [CharP.intCast_eq_zero_iff k ell] at h
  simpa [integerPrimeIdeal, Ideal.mem_span_singleton] using h

/-- **The `LocalIntegers ell`-algebra structure on `W(k)`**: `IsLocalization.lift` of the
integers, which are units off `(ell)` (`wittVector_isUnit_intCast`). -/
@[reducible] def wittLocalAlgebra : Algebra (LocalIntegers ell) (WittVector ell k) :=
  (IsLocalization.lift (M := (integerPrimeIdeal ell).primeCompl) (S := LocalIntegers ell)
    (g := Int.castRingHom (WittVector ell k)) (wittVector_isUnit_intCast ell k)).toAlgebra

variable {ell k}

/-- The constant coefficient `W(k) → k` intertwines the two `LocalIntegers ell`-algebra
structures. -/
theorem constantCoeff_comp_algebraMap [Algebra (LocalIntegers ell) k] :
    letI := wittLocalAlgebra ell k
    (WittVector.constantCoeff : WittVector ell k →+* k).comp
        (algebraMap (LocalIntegers ell) (WittVector ell k)) =
      algebraMap (LocalIntegers ell) k :=
  localIntegers_ringHom_ext ell _ _

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 1000000 in
/-- **Every cover point over `k` lifts to `W(k)`** (3b (ii)): for algebraically closed `k` of
characteristic `ell` with any `Algebra (LocalIntegers ell) k`, every
`f : UniversalExactOrderAlgebra ell N h₅ htame →ₐ[LocalIntegers ell] k` has a lift
`F` to `W(k)` (with `wittLocalAlgebra`) whose constant coefficient is `f`. -/
theorem exists_wittLift [IsAlgClosed k] [Algebra (LocalIntegers ell) k] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ N * N.totient)
    (f : UniversalExactOrderAlgebra ell N h₅ htame →ₐ[LocalIntegers ell] k) :
    letI := wittLocalAlgebra ell k
    ∃ F : UniversalExactOrderAlgebra ell N h₅ htame →ₐ[LocalIntegers ell] WittVector ell k,
      ∀ a, WittVector.constantCoeff (F a) = f a := by
  letI := wittLocalAlgebra ell k
  letI := detectorCover_smooth (ell := ell) (N := N) h₅ htame
  let I : Ideal (WittVector ell k) := Ideal.span {(ell : WittVector ell k)}
  let e : (WittVector ell k ⧸ I) ≃+* k := WittVector.quotientPEquiv
  have he : (e.symm : k →+* WittVector ell k ⧸ I).comp (algebraMap (LocalIntegers ell) k) =
      algebraMap (LocalIntegers ell) (WittVector ell k ⧸ I) :=
    localIntegers_ringHom_ext ell _ _
  let eA : k →ₐ[LocalIntegers ell] WittVector ell k ⧸ I :=
    { (e.symm : k →+* WittVector ell k ⧸ I) with
      commutes' := fun r => RingHom.congr_fun he r }
  obtain ⟨F, hF⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (R := LocalIntegers ell) (I := I) (eA.comp f)
  refine ⟨F, fun a => ?_⟩
  have h := congrArg e (DFunLike.congr_fun hF a)
  have h1 : e ((Ideal.Quotient.mkₐ (LocalIntegers ell) I).comp F a) =
      WittVector.constantCoeff (F a) :=
    WittVector.quotientPEquiv_mk _
  have h2 : e ((eA.comp f) a) = f a := e.apply_symm_apply (f a)
  rw [← h1, ← h2]
  exact h

end ZInQ.Manuscript.RC.ModelGeneric7

#print axioms ZInQ.Manuscript.RC.ModelGeneric7.localIntegers_ringHom_ext
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.wittVector_isUnit_intCast
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.wittLocalAlgebra
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.constantCoeff_comp_algebraMap
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.exists_wittLift
