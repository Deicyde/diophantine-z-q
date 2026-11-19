import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralCoefficientLimit
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TraceFromHomology
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncTrace

/-!
# The integral compact-support trace from its cited top cohomology

Nekovář, Selmer complexes, 5.4.1 (printed pp. 125–126), gives degree-three
compact-support cohomology equal to the coefficient module. The setting is
5.1 (printed p. 113): a finite support containing the primes above two and
all infinite places, with no real places at the prime two. Here the infinite
places are implicit and the local sum is indexed by finite primes only.

The displayed literature parameter concerns only the number field, support,
and actual integral cyclotomic coefficient line. It contains no elliptic
curve, Kummer condition, retained model, rank, pairing or self-duality input.
The scalar-valued cochain trace is constructed from that cohomology result
using the proved saturated-kernel extension; it is not a field of the
literature parameter. The local truncation changes neither degree-three
cycles nor boundaries, as in the existing trace-descent comparison.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.CalibrationModel

/-- Compactly supported continuous cochains with the actual integral cyclotomic coefficients. -/
def integralCompactTarget (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) : GCx ℤ_[2] :=
  coneCx (resS ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (IntegralTate1 K S))

/-- Nekovář 5.4.1, pp. 125–126: the top compact cohomology of the cyclotomic line.
The proposition records the cited coefficient result; no proof or new axiom is declared here. -/
def NekovarIntegralCompactTopCohomology : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ [HasTwoPowerRoots K S],
      Nonempty ((integralCompactTarget K S).toCC.homology 3 ≃ₗ[ℤ_[2]] ℤ_[2])

/-- The coefficient line is torsion-free with exactly its inherited scalar module. -/
theorem integralTate1_torsionFree (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    Module.IsTorsionFree ℤ_[2] (IntegralTate1 K S) :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
    change r * (show ℤ_[2] from x) = 0 at h
    exact mul_eq_zero.mp h

/-- Degree four of the compact cone is a product of actual torsion-free cochain terms. -/
theorem integralCompactTarget_four_torsionFree (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    Module.IsTorsionFree ℤ_[2] ((integralCompactTarget K S).X 4) := by
  let : Module.IsTorsionFree ℤ_[2] (IntegralTate1 K S) := integralTate1_torsionFree K S
  let : Module.IsTorsionFree ℤ_[2]
      ((globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).X 4) := by
    change Module.IsTorsionFree ℤ_[2]
      (contCochain ℤ_[2] (GKS K S) (IntegralTate1 K S) 4)
    exact contCochain_torsionFree 4
  let : ∀ v : Places K S, Module.IsTorsionFree ℤ_[2]
      ((localCx ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (IntegralTate1 K S) v).X 3) := fun v => by
    let : Module.IsTorsionFree ℤ_[2]
        (ResMod (locMap K S v.1) (IntegralTate1 K S)) := integralTate1_torsionFree K S
    change Module.IsTorsionFree ℤ_[2]
      (contCochain ℤ_[2] (Gloc K v.1)
        (ResMod (locMap K S v.1) (IntegralTate1 K S)) 3)
    exact contCochain_torsionFree 3
  change Module.IsTorsionFree ℤ_[2]
    (((globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).X 4) ×
      (∀ v : Places K S,
        (localCx ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (IntegralTate1 K S) v).X 3))
  infer_instance

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} [HasTwoPowerRoots K S]

/-- The cited top cohomology constructs an actual degree-three trace on the full compact cone. -/
theorem exists_integralCompactTrace (h541 : NekovarIntegralCompactTopCohomology)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∃ tr : (integralCompactTarget K S).X 3 →ₗ[ℤ_[2]] ℤ_[2],
      (∀ y, tr ((integralCompactTarget K S).d 2 3 rfl y) = 0) ∧ InducesIsoH3 tr := by
  obtain ⟨e⟩ := h541 K hK S hS h2
  let : Module.IsTorsionFree ℤ_[2] ((integralCompactTarget K S).X 4) :=
    integralCompactTarget_four_torsionFree K S
  exact ⟨traceFromHomology (integralCompactTarget K S) e,
    traceFromHomology_boundary (integralCompactTarget K S) e,
    traceFromHomology_inducesIsoH3 (integralCompactTarget K S) e⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality
