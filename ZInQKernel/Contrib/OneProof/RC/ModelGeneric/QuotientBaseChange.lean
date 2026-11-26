import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.CoverCompatibility
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-! # One rational quotient for every detector -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open ModelTorsion RC.ModelInvariants
open scoped TensorProduct

open private fixedEquivOfEquivariant from
  ZInQKernel.Contrib.OneProof.RC.ModelInvariants.Compatibility
open private rationalLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
open private detectorLevel_isUnit detectorShort_domain from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel
open private detectorCoverAlgebra detectorCoverTower from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0Level

private noncomputable def degreeZeroEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (gr : ℤ → Submodule R S) (gr' : ℤ → Submodule R T)
    [GradedAlgebra gr] [GradedAlgebra gr'] (e : S ≃ₐ[R] T)
    (h : ∀ i x, x ∈ gr i → e x ∈ gr' i) :
    degreeZero gr ≃ₐ[R] degreeZero gr' := by
  let f : gr →+*ᵍ gr' := { e.toRingHom with map_mem := fun {i x} hx => h i x hx }
  refine AlgEquiv.ofBijective ((e.toAlgHom.comp (degreeZero gr).val).codRestrict _
    (fun x => h 0 x x.property)) ⟨?_, ?_⟩
  · intro x y eq
    exact Subtype.ext (e.injective (congrArg Subtype.val eq))
  · intro y
    have hy : e.symm (y : T) ∈ gr 0 := by
      have he := f.map_directSumDecompose (x := e.symm (y : T)) (i := 0)
      change e (DirectSum.decompose gr (e.symm (y : T)) 0 : S) =
        (DirectSum.decompose gr' (e (e.symm (y : T))) 0 : T) at he
      rw [AlgEquiv.apply_symm_apply, DirectSum.decompose_of_mem_same gr' y.property] at he
      have hs := e.injective (he.trans (e.apply_symm_apply (y : T)).symm)
      rw [← hs]
      exact (DirectSum.decompose gr (e.symm (y : T)) 0).property
    exact ⟨⟨e.symm y, hy⟩, Subtype.ext (e.apply_symm_apply y)⟩

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
/-- For every admissible detector, the pinned generic fibre algebra is canonically the
single short-level quotient constructed over `ℚ`. This uses the pinned invariant
base change, followed by the equivariant, graded comparison of the two marked covers. -/
noncomputable def Y0RationalBaseChange :
    ℚ ⊗[LocalIntegers ell] Pinned.Y0LevelAlgebra h₅ htame h₂ ≃ₐ[ℚ] Y0RationalAlgebra h₂ := by
  obtain _ | _ | n := N
  · omega
  · omega
  let R := LocalIntegers ell
  let hn := detectorLevel_isUnit h₅ htame
  let hQ := rationalLevel_isUnit (N := n + 2)
  let S := UniversalExactOrderAlgebra ell (n + 2) h₅ htame
  let G := (ZMod (n + 2))ˣ
  letI := detectorShort_domain h₅ htame
  letI := detectorCoverAlgebra h₅ htame
  letI := detectorCoverTower h₅ htame
  letI := Pinned.detectorLevelAction h₅ htame h₂
  letI := Pinned.detectorLevelAction_comm h₅ htame h₂
  letI := Pinned.detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := Pinned.detectorLevelAction_preserves h₅ htame h₂
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  let gr := fun i => (Pinned.detectorExactOrderGrading h₅ htame h₂ i).baseChange ℚ
  let gr' := rationalGrading h₂
  let e : ℚ ⊗[R] S ≃ₐ[ℚ] rationalCover (n + 2) := shortCoverBaseChange hn hQ
  have hgrade (i : ℤ) (x : ℚ ⊗[R] S) (hx : x ∈ gr i) : e x ∈ gr' i :=
    shortCoverBaseChange_mem hn hQ i hx
  let e₀ := degreeZeroEquiv gr gr' e hgrade
  have he (a : G) (x : ℚ ⊗[R] S) : e (a • x) = a • e x := by
    induction x with
    | tmul q b =>
      rw [scalarExtension_smul_tmul]
      change e (q ⊗ₜ[R] shortLevelUnitAut hn a b) =
        shortLevelUnitAut hQ a (e (q ⊗ₜ[R] b))
      have hs := shortCoverBaseChange_units hn hQ a b
      change e ((1 : ℚ) ⊗ₜ[R] shortLevelUnitAut hn a b) =
        shortLevelUnitAut hQ a (e ((1 : ℚ) ⊗ₜ[R] b)) at hs
      rw [TensorProduct.tmul_eq_smul_one_tmul q (shortLevelUnitAut hn a b),
        TensorProduct.tmul_eq_smul_one_tmul q b]
      simp only [map_smul, hs]
    | add x y hx hy =>
      have hxy : a • (x + y) = a • x + a • y := smul_add a x y
      rw [hxy, map_add, hx, hy, map_add, smul_add]
  have he₀ (a : G) (x : degreeZero gr) : e₀ (a • x) = a • e₀ x := by
    apply Subtype.ext
    change e (a • x.val) = a • e x.val
    exact he a x.val
  exact (Pinned.levelQuotientBaseChange h₅ htame h₂ ℚ).trans
    ((fixedDegreeZeroEquiv gr).trans
      ((fixedEquivOfEquivariant ℚ e₀ he₀).trans (fixedDegreeZeroEquiv gr').symm))

#print axioms degreeZeroEquiv
#print axioms Y0RationalBaseChange

end WeierstrassCurve.ModelLevels.ModelGeneric
