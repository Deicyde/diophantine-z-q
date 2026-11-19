import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TraceHomotopy
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralCompactSupport

/-!
# Integral trace comparison by a saturated-kernel extension

If two degree-m traces agree on cycles, their difference factors through
the differential. Exactness in degree m+1 identifies that differential
image with the next kernel. Torsion-freeness of the degree m+2 target and
compactness of the scalar PID extend the induced functional on the kernel.
The existing explicit signed adjoint homotopy then applies unchanged.
Scalar self-injectivity and agreement off cycles are not assumed.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TraceExtension

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- A trace difference factors through the differential using only next-degree exactness. -/
theorem exists_trace_sub_eq_comp_d_compact {T : GCx R} (m : ℤ)
    (tr₁ tr₂ : T.X m →ₗ[R] R) [Module.IsTorsionFree R (T.X (m + 2))]
    (hnext : ∀ z : T.X (m + 1), T.d (m + 1) (m + 2) (by omega) z = 0 →
      ∃ y : T.X m, T.d m (m + 1) rfl y = z)
    (hcyc : ∀ z : T.X m, T.d m (m + 1) rfl z = 0 → tr₁ z = tr₂ z) :
    ∃ h : T.X (m + 1) →ₗ[R] R,
      ∀ x : T.X m, tr₁ x - tr₂ x = h (T.d m (m + 1) rfl x) := by
  let δ : T.X m →ₗ[R] R := tr₁ - tr₂
  let d := T.d m (m + 1) rfl
  let dnext := T.d (m + 1) (m + 2) (by omega)
  have hker : LinearMap.ker d ≤ LinearMap.ker δ := by
    intro z hz
    change tr₁ z - tr₂ z = 0
    rw [hcyc z hz, sub_self]
  let g : LinearMap.range d →ₗ[R] R :=
    ((LinearMap.ker d).liftQ δ hker).comp d.quotKerEquivRange.symm.toLinearMap
  have hkernel : LinearMap.range d = LinearMap.ker dnext := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact T.d_d m (m + 1) (m + 2) rfl (by omega) x
    · intro z hz
      exact hnext z hz
  let gKernel : LinearMap.ker dnext →ₗ[R] R :=
    g.comp (LinearEquiv.ofEq _ _ hkernel).symm.toLinearMap
  obtain ⟨h, hh⟩ := kernel_extension_of_compact_scalar dnext gKernel
  refine ⟨h, fun x => ?_⟩
  have hx : d x ∈ LinearMap.ker dnext := T.d_d m (m + 1) (m + 2) rfl (by omega) x
  have hv := hh ⟨d x, hx⟩
  change h (d x) = g ((LinearEquiv.ofEq _ _ hkernel).symm ⟨d x, hx⟩) at hv
  have he : (LinearEquiv.ofEq _ _ hkernel).symm ⟨d x, hx⟩ =
      (⟨d x, LinearMap.mem_range_self d x⟩ : LinearMap.range d) := rfl
  rw [he] at hv
  rw [hv]
  change δ x = ((LinearMap.ker d).liftQ δ hker)
    (d.quotKerEquivRange.symm ⟨d x, LinearMap.mem_range_self d x⟩)
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- The proved compact-scalar factorization supplies the existing exact-sign adjoint homotopy. -/
theorem adjHom_quasiIso_iff_of_eq_on_cycles_compact {A B T : GCx R}
    (P : GPair A B T) (m : ℤ) (tr₁ tr₂ : T.X m →ₗ[R] R)
    (htr₁ : ∀ z, tr₁ (T.d (m - 1) m (by omega) z) = 0)
    (htr₂ : ∀ z, tr₂ (T.d (m - 1) m (by omega) z) = 0)
    [Module.IsTorsionFree R (T.X (m + 2))]
    (hnext : ∀ z : T.X (m + 1), T.d (m + 1) (m + 2) (by omega) z = 0 →
      ∃ y : T.X m, T.d m (m + 1) rfl y = z)
    (hcyc : ∀ z : T.X m, T.d m (m + 1) rfl z = 0 → tr₁ z = tr₂ z) :
    Nonempty (Homotopy (GHom.toCC (adjHom P m tr₁ htr₁))
      (GHom.toCC (adjHom P m tr₂ htr₂))) ∧
      (QuasiIso (GHom.toCC (adjHom P m tr₁ htr₁)) ↔
        QuasiIso (GHom.toCC (adjHom P m tr₂ htr₂))) := by
  obtain ⟨h, hh⟩ := exists_trace_sub_eq_comp_d_compact m tr₁ tr₂ hnext hcyc
  exact ⟨⟨adjHomHomotopy P m tr₁ tr₂ htr₁ htr₂ h hh⟩,
    adjHom_quasiIso_iff P m tr₁ tr₂ htr₁ htr₂ h hh⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality
