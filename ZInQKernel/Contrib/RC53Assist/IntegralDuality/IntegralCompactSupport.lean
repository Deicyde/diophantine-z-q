import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralCompactTrace
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CyclotomicCohomology

/-!
# Actual integral compact-support cohomological support

The finite-level Milne inputs and the constructed cyclotomic inverse limit
supply global and local vanishing above degree two. The existing exact
sequence of the compact cone therefore gives vanishing above degree three.
The next-degree exactness and torsion-free terms needed for integral trace
comparison are proved here, not added as trace or duality assumptions.
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
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith

/-- Vanishing of the actual cohomology makes every actual cocycle a boundary. -/
theorem cocycleBoundary_of_homology_subsingleton {R : Type} [CommRing R]
    (C : GCx R) (n : ℤ) (h : Subsingleton (C.toCC.homology n))
    (z : C.X n) (hz : C.d n (n + 1) rfl z = 0) :
    ∃ y : C.X (n - 1), C.d (n - 1) n (by omega) y = z := by
  let := h
  let : Subsingleton (subquot (LinearMap.range (C.d (n - 1) n (by omega)))
      (LinearMap.ker (C.d n (n + 1) rfl))) :=
    (gcxRawHomologyEquiv C (n - 1) n (n + 1) (by omega) rfl).symm.injective.subsingleton
  have hq : (Submodule.Quotient.mk (⟨z, hz⟩ : LinearMap.ker (C.d n (n + 1) rfl)) :
      subquot (LinearMap.range (C.d (n - 1) n (by omega)))
        (LinearMap.ker (C.d n (n + 1) rfl))) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at hq
  exact hq

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}

/-- All full compact cyclotomic cochain terms are torsion-free, without a cohomology hypothesis. -/
theorem integralCompactTarget_torsionFree (n : ℤ) :
    Module.IsTorsionFree ℤ_[2] ((integralCompactTarget K S).X n) := by
  let : Module.IsTorsionFree ℤ_[2] (IntegralTate1 K S) := integralTate1_torsionFree K S
  have hG : Module.IsTorsionFree ℤ_[2]
      ((globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).X n) :=
    natCx_torsionFree _ (fun m => contCochain_torsionFree m) n
  have hL : ∀ v : Places K S, Module.IsTorsionFree ℤ_[2]
      ((localCx ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (IntegralTate1 K S) v).X (n - 1)) := by
    intro v
    let : Module.IsTorsionFree ℤ_[2] (ResMod (locMap K S v.1) (IntegralTate1 K S)) :=
      resMod_torsionFree (locMap K S v.1)
    exact natCx_torsionFree _ (fun m => contCochain_torsionFree m) (n - 1)
  let := hG
  let : ∀ v : Places K S, Module.IsTorsionFree ℤ_[2]
      ((localCx ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (IntegralTate1 K S) v).X (n - 1)) := hL
  change Module.IsTorsionFree ℤ_[2]
    (((globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).X n) ×
      (∀ v : Places K S,
        (localCx ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (IntegralTate1 K S) v).X (n - 1)))
  infer_instance

variable [HasTwoPowerRoots K S]

/-- The actual compact cyclotomic cohomology vanishes above degree three. -/
theorem integralCompactTarget_homology_high
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (n : ℤ) (hn : 3 < n) :
    Subsingleton ((integralCompactTarget K S).toCC.homology n) := by
  let G := globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)
  let Lv := fun v : Places K S => localCx ℤ_[2] (GKS K S)
    (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) (IntegralTate1 K S) v
  let L := piCx Lv
  let f : GHom G L := resS ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (IntegralTate1 K S)
  have hg : Subsingleton (G.toCC.homology n) :=
    globalIntegralCyclotomic_homology_high hglob hglobal hK hS h2 n (by omega)
  have hl : Subsingleton (L.toCC.homology (n - 1)) :=
    pi_homology_subsingleton Lv (n - 1) (fun v =>
      localIntegralCyclotomic_homology_high hloc hlocal v.1 (n - 1) (by omega))
  exact subsingleton_of_exact ((coneSES_shortExact f).homology_exact₂ n)
    (shiftDown_homology_subsingleton L n hl) hg

/-- Degree-four exactness is supplied by the actual cohomological support proof. -/
theorem integralCompactTarget_degree_four_exact
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (z : (integralCompactTarget K S).X 4)
    (hz : (integralCompactTarget K S).d 4 5 rfl z = 0) :
    ∃ y : (integralCompactTarget K S).X 3, (integralCompactTarget K S).d 3 4 rfl y = z :=
  cocycleBoundary_of_homology_subsingleton (integralCompactTarget K S) 4
    (integralCompactTarget_homology_high hglob hloc hglobal hlocal hK hS h2 4 (by decide)) z hz

/-- Global degree-three cyclotomic cocycles are boundaries under the stated field and support guards. -/
theorem globalIntegralCyclotomic_degree_three_exact
    (hglob : MilneGlobalFiniteness) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (z : (globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).X 3)
    (hz : (globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).d 3 4 rfl z = 0) :
    ∃ y : (globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).X 2,
      (globalCx ℤ_[2] (GKS K S) (IntegralTate1 K S)).d 2 3 rfl y = z :=
  cocycleBoundary_of_homology_subsingleton _ 3
    (globalIntegralCyclotomic_homology_high hglob hglobal hK hS h2 3 (by decide)) z hz

end ZInQ.Contrib.RC53Assist.IntegralDuality
