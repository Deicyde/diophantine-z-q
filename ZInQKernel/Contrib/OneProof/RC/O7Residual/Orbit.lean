import ZInQKernel.Contrib.OneProof.RC.O7Residual.OrbitQuotient

/-! The chosen representative of a Picard label, tex 9155–9169.
The quotient computation is on-the-spot (c). -/

noncomputable section

open scoped NumberField
open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing

namespace ZInQ.Manuscript.RC.O7Residual

open Eichler Adelic O7Actual O7Orbits PicardFibers Visibility O7Assemble

section Fibre

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D : ℤ}
    {F : Type} [Field F] [NumberField F]
    (s : StageAt O N M hN m) (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)

variable (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (T : ∀ p, Nonempty (LocalTorusChart (ActualOrder s) ι
      (referenceUnit s A Q ι) (referenceAffine s Q ι) p))
    (R : ∀ t, HasLocalRealizations s (referenceAffine s Q ι) t)

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
/-- Compute the actual fibre parametrization on any prescribed family of
class ideles. In particular it applies to the normalized coprime ones. -/
theorem orbitRead (a : ClassGroup (𝓞 F) → (FiniteAdeleRing (𝓞 F) F)ˣ)
    (ha : ∀ c, toClassGroup (𝓞 F) F (a c) = c) :
    OrbitRead s A H hh Q ι T R a := by
  intro t c
  let x := referenceUnit s A Q ι
  let hα := referenceAffine_spec s A Q ι
  let hx := (referenceUnit_sphere s A Q ι).1
  let hn := (referenceUnit_sphere s A Q ι).2
  let z := tupleBase s A H Q ι R t
  let e := chartEquiv s A H Q ι T R
  let z₀ := tupleBase s A H Q ι R (fun _ => false)
  have hrat := ideleCentralizerEquiv_rational _ ι x _ (fun p => (T p).some)
    z₀.val z₀.prop Q s.weights.ha.ne s.weights.hb.ne hx rfl
  have hint := ideleCentralizerEquiv_integral _ ι x _ (fun p => (T p).some)
    z₀.val z₀.prop z.val z.prop
  let R₀ := ActualOrder s
  let C := adelicCentralizer R₀ (diagonal R₀ x).val
  let L := diagonalCentralizer R₀ x
  let U := integralUnits R₀
  let E := ideleOrbitEquiv L C U (diagonalCentralizer_le R₀ x) z.val e hrat hint
  let ht := (realize_tuple s A H hα hx hn t (R t)).choose_spec
  let B := basedFiberEquiv s A H hh x hα hx hn z t ht
  have he₀ := ideleOrbitEquiv_toClassGroup L C U (diagonalCentralizer_le R₀ x)
    z.val e hrat hint (a c)
  have he : (E c).val = DoubleCoset.mk L U ((e (a c)).val * z.val) :=
    (congrArg (fun j => (E j).val) (ha c)).symm.trans he₀
  let b : Set.range (fun g : C => DoubleCoset.mk L U (g.val * z.val)) :=
    ⟨DoubleCoset.mk L U ((e (a c)).val * z.val), e (a c), rfl⟩
  simp only [OrbitFibers.param, Equiv.trans_apply, Equiv.sigmaEquivProd_symm_apply,
    Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply, orbitFibers_of_local,
    O7Orbits.orbitFibers, id_eq, picardFibers_of_local, picardFibers_of_comparison]
  change (B (E c)).val = _
  exact (congrArg (fun j => (B j).val) (show E c = b from Subtype.ext he)).trans
    (basedFiberEquiv_mk s A H hh x hα hx hn z t ht (e (a c)))

end Fibre

end ZInQ.Manuscript.RC.O7Residual
