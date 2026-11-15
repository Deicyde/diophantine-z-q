import ZInQKernel.Contrib.TYZDecomp.Leaves
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Adeles.FiniteBaseChange
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

noncomputable section

namespace ZInQ.Contrib.TYZDecomp.H29Split

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp NumberField
  IsDedekindDomain
open scoped Quaternion TensorProduct FiniteAdeleExtension

abbrev AQ : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

/-- `ℍ[ℚ] → ℍ[𝔸ᶠ_ℚ]`, coordinatewise. -/
def qι : ℍ[ℚ] →ₐ[ℚ] ℍ[AQ] where
  toFun q := ⟨algebraMap ℚ AQ q.re, algebraMap ℚ AQ q.imI, algebraMap ℚ AQ q.imJ,
    algebraMap ℚ AQ q.imK⟩
  map_one' := by apply Quaternion.ext <;> simp
  map_mul' a b := by
    apply Quaternion.ext <;>
      simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
        map_mul, map_add, map_sub]
  map_zero' := by apply Quaternion.ext <;> simp
  map_add' a b := by apply Quaternion.ext <;> simp
  commutes' r := by apply Quaternion.ext <;> simp [Algebra.algebraMap_eq_smul_one]

example (n : ℕ) [NeZero n] : QNeg n := QuadraticAlgebra.omega

/-- base change -/
def tauHat (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) :
    FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n) →+* ℍ[AQ] :=
  (AlgHom.liftEquiv ℚ AQ (QNeg n) ℍ[AQ] ((qι).comp τ)).toRingHom.comp
    (TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv ℚ (QNeg n)).symm.toRingHom

theorem tauHat_algebraMap (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (k : QNeg n) :
    tauHat n τ (algebraMap (QNeg n) _ k) = qι (τ k) := by
  simp [tauHat]

open Classical in
/-- the idempotent at `v` -/
def eAt (v : HeightOneSpectrum (𝓞 ℚ)) : AQ :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

def ιAt (v : HeightOneSpectrum (𝓞 ℚ)) (α : ℍ[ℚ]) : ℍ[AQ] :=
  algebraMap AQ ℍ[AQ] (eAt v) * qι α + algebraMap AQ ℍ[AQ] (1 - eAt v)

def apE (p : ℕ) : ℤ := -∑ x ∈ Finset.range p, jacobiSym ((x : ℤ) ^ 3 - x) p

example (x : ℍ[AQ]) (v : HeightOneSpectrum (𝓞 ℚ)) : v.adicCompletion ℚ := x.re v

example (n : ℕ) [NeZero n] : (FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n))ˣ →* ClassGroup (𝓞 (QNeg n)) :=
  FiniteAdeleRing.toClassGroup (𝓞 (QNeg n)) (QNeg n)

example (z : AQ) : z ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ ↔ True := by
  rw [FiniteAdeleRing.mem_integralAdeles]; sorry

end ZInQ.Contrib.TYZDecomp.H29Split
