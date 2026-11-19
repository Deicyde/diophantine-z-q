import ZInQKernel.Contrib.RC53Assist.DerivedKummerActual.Actual
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso

/-!
# Scoped exactness of termwise duals over a compact scalar PID

The dual of an acyclic complex of torsion-free modules is acyclic over a
compact Hausdorff topological principal ideal domain. The extension is made
only from a saturated kernel with torsion-free target. Self-injectivity of
the scalar ring is neither assumed nor inferred.

A quasi-isomorphism between termwise torsion-free complexes has an acyclic,
termwise torsion-free cone. The existing split cone sequences and their duals
then give quasi-isomorphism preservation for this precise class of maps.
No unrestricted derived Hom functor is constructed or identified here.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TraceExtension

universe u

section ExactImages

variable {R : Type u} [CommRing R]

/-- Exactness identifies each boundary image with the next differential kernel. -/
theorem acyclic_range_eq_kernel (C : GCx R) (hC : GAcyclic C)
    (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    LinearMap.range (C.d i j hij) = LinearMap.ker (C.d j k hjk) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact C.d_d i j k hij hjk x
  · intro x hx
    exact hC i j k hij hjk x hx

end ExactImages

section CompactScalar

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- Acyclic torsion-free complexes have acyclic exact-sign termwise duals. -/
theorem dualCx_acyclic_torsionFree (C : GCx R)
    (hTF : ∀ n : ℤ, Module.IsTorsionFree R (C.X n))
    (hC : GAcyclic C) (m : ℤ) : GAcyclic (dualCx C m) := by
  intro i j k hij hjk φ hφ
  have hkill : ∀ x : C.X (m - k),
      asDual φ (C.d (m - k) (m - j) (by omega) x) = 0 := by
    intro x
    have h := congrArg (fun χ => asDual χ x) hφ
    change (-(sgn j)) • asDual φ (C.d (m - k) (m - j) _ x) = 0 at h
    have h2 := congrArg (fun z : R => (-(sgn j)) • z) h
    simp only [smul_smul, neg_mul_neg, sgn_mul_self, one_smul, smul_zero] at h2
    exact h2
  set dout := C.d (m - j) (m - i) (by omega) with hdout
  set dnext := C.d (m - i) (m - i + 1) rfl with hdnext
  have hker : LinearMap.ker dout ≤ LinearMap.ker (asDual φ) := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    obtain ⟨x, rfl⟩ := hC (m - k) (m - j) (m - i) (by omega) (by omega) z hz
    exact hkill x
  let g : LinearMap.range dout →ₗ[R] R :=
    ((LinearMap.ker dout).liftQ (asDual φ) hker).comp
      dout.quotKerEquivRange.symm.toLinearMap
  have hkernel : LinearMap.range dout = LinearMap.ker dnext :=
    acyclic_range_eq_kernel C hC (m - j) (m - i) (m - i + 1) (by omega) rfl
  let gKernel : LinearMap.ker dnext →ₗ[R] R :=
    g.comp (LinearEquiv.ofEq _ _ hkernel).symm.toLinearMap
  let : Module.IsTorsionFree R (C.X (m - i + 1)) := hTF (m - i + 1)
  obtain ⟨h, hh⟩ := kernel_extension_of_compact_scalar dnext gKernel
  refine ⟨(-(sgn i)) • h, dualCx_ext fun z => ?_⟩
  change (-(sgn i)) • (((-(sgn i)) • h) (dout z)) = asDual φ z
  rw [LinearMap.smul_apply, smul_smul, neg_mul_neg, sgn_mul_self, one_smul]
  have hdz : dout z ∈ LinearMap.ker dnext :=
    C.d_d (m - j) (m - i) (m - i + 1) (by omega) rfl z
  have hv := hh ⟨dout z, hdz⟩
  change h (dout z) = g ((LinearEquiv.ofEq _ _ hkernel).symm ⟨dout z, hdz⟩) at hv
  have he : (LinearEquiv.ofEq _ _ hkernel).symm ⟨dout z, hdz⟩ =
      (⟨dout z, LinearMap.mem_range_self dout z⟩ : LinearMap.range dout) := rfl
  rw [he] at hv
  rw [hv]
  change ((LinearMap.ker dout).liftQ (asDual φ) hker)
    (dout.quotKerEquivRange.symm ⟨dout z, _⟩) = asDual φ z
  rw [show (⟨dout z, LinearMap.mem_range_self dout z⟩ : LinearMap.range dout) =
    dout.quotKerEquivRange (Submodule.Quotient.mk z) from rfl,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]

/-- The cochain-complex form of scoped dual acyclicity. -/
theorem dualCx_toCC_acyclic_torsionFree (C : GCx R)
    (hTF : ∀ n : ℤ, Module.IsTorsionFree R (C.X n))
    (hC : C.toCC.Acyclic) (m : ℤ) : (dualCx C m).toCC.Acyclic :=
  (acyclic_toCC_iff _).2 (dualCx_acyclic_torsionFree C hTF ((acyclic_toCC_iff C).1 hC) m)

/-- Each shifted-cone term is a product of torsion-free source and target terms. -/
theorem coneCx_torsionFree {A B : GCx R} (f : GHom A B)
    (hA : ∀ n : ℤ, Module.IsTorsionFree R (A.X n))
    (hB : ∀ n : ℤ, Module.IsTorsionFree R (B.X n)) (n : ℤ) :
    Module.IsTorsionFree R ((coneCx f).X n) := by
  let := hA n
  let := hB (n - 1)
  change Module.IsTorsionFree R (A.X n × B.X (n - 1))
  infer_instance

/-- Termwise duals preserve quasi-isomorphisms in the torsion-free comparison class. -/
theorem dualHom_quasiIso_torsionFree {A B : GCx R} (f : GHom A B)
    (hA : ∀ n : ℤ, Module.IsTorsionFree R (A.X n))
    (hB : ∀ n : ℤ, Module.IsTorsionFree R (B.X n))
    (m : ℤ) (hf : QuasiIso (GHom.toCC f)) :
    QuasiIso (GHom.toCC (dualHom f m)) := by
  have hcf : (dualCx (coneCx f) m).toCC.Acyclic :=
    (acyclic_toCC_iff _).2 (dualCx_acyclic_torsionFree (coneCx f)
      (coneCx_torsionFree f hA hB) (coneCx_acyclic_of_quasiIso f hf) m)
  have hcid : (dualCx (coneCx (idGHom B)) m).toCC.Acyclic :=
    (acyclic_toCC_iff _).2 (dualCx_acyclic_torsionFree (coneCx (idGHom B))
      (coneCx_torsionFree (idGHom B) hB hB) (coneCx_id_acyclic B) m)
  have h2 : QuasiIso (dualConeSESHom f m).τ₂ := quasiIso_of_acyclic _ hcid hcf
  have h3 : QuasiIso (dualConeSESHom f m).τ₃ := by
    change QuasiIso (GHom.toCC (dualHom (idGHom (shiftDown B)) m))
    rw [toCC_dualHom_idGHom]
    infer_instance
  exact quasiIso_τ₁ (dualConeSESHom f m) (dualConeSES_shortExact (idGHom B) m)
    (dualConeSES_shortExact f m) h2 h3

end CompactScalar

end ZInQ.Contrib.RC53Assist.IntegralDuality
