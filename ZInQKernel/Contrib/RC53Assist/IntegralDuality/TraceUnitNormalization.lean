import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralTraceHomotopy
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.QuasiIsoTracePullbackGCx

/-!
# Unit normalization of traces on the same top cohomology

Two scalar traces inducing an isomorphism on the same cohomology quotient
are related on cycles by one unique scalar unit. A trace-one cycle proves
this directly: subtracting its scalar multiple from any cycle leaves a
trace-zero cycle, hence a boundary. No equality of unrelated trace maps,
local normalization choices or self-duality hypothesis is introduced.

Unit multiplication gives an actual isomorphism of cochain complexes.
Together with the proved compact-scalar trace homotopy, this shows that
the two fixed traced adjoints are quasi-isomorphic simultaneously. The
next-degree exactness and next-next-term torsion-freeness stay explicit.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory HomologicalComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

section ScalarQuotient

variable {R X₀ X₁ X₂ : Type*} [CommRing R]
  [AddCommGroup X₀] [Module R X₀] [AddCommGroup X₁] [Module R X₁]
  [AddCommGroup X₂] [Module R X₂]
  {d₀ : X₀ →ₗ[R] X₁} {d₁ : X₁ →ₗ[R] X₂} {tr₁ tr₂ : X₁ →ₗ[R] R}

/-- Two trace isomorphisms on the same quotient differ on cycles by a scalar unit. -/
theorem topTraceUnit_on_cycles (h₁ : IsTopTraceIso d₀ d₁ tr₁)
    (h₂ : IsTopTraceIso d₀ d₁ tr₂) :
    ∃ u : Rˣ, ∀ z : X₁, d₁ z = 0 → tr₁ z = (u : R) * tr₂ z := by
  obtain ⟨a, ha, hta⟩ := h₁.2.2
  obtain ⟨b, hb, htb⟩ := h₂.2.2
  have hformula (z : X₁) (hz : d₁ z = 0) : tr₁ z = tr₂ z * tr₁ b := by
    obtain ⟨y, hy⟩ := h₂.2.1 (z - tr₂ z • b)
      (by rw [map_sub, map_smul, hz, hb, smul_zero, sub_zero])
      (by rw [map_sub, map_smul, htb, smul_eq_mul, mul_one, sub_self])
    have h := h₁.1 y
    rw [hy, map_sub, map_smul, smul_eq_mul] at h
    exact sub_eq_zero.mp h
  have hab : tr₂ a * tr₁ b = 1 := by
    have h := hformula a ha
    rw [hta] at h
    exact h.symm
  let u : Rˣ := ⟨tr₁ b, tr₂ a, (mul_comm _ _).trans hab, hab⟩
  refine ⟨u, fun z hz => ?_⟩
  change tr₁ z = tr₁ b * tr₂ z
  exact (hformula z hz).trans (mul_comm _ _)

/-- The scalar unit is unique because the second trace has a trace-one cycle. -/
theorem topTraceUnit_unique (h₂ : IsTopTraceIso d₀ d₁ tr₂) {u v : Rˣ}
    (hu : ∀ z : X₁, d₁ z = 0 → tr₁ z = (u : R) * tr₂ z)
    (hv : ∀ z : X₁, d₁ z = 0 → tr₁ z = (v : R) * tr₂ z) : u = v := by
  obtain ⟨b, hb, htb⟩ := h₂.2.2
  apply Units.ext
  have h := (hu b hb).symm.trans (hv b hb)
  simpa only [htb, mul_one] using h

end ScalarQuotient

section UnitComplex

universe u
variable {R : Type u} [CommRing R]

/-- Multiplication by one scalar unit on every term, as an actual chain map. -/
def unitScalarRelationHom (C : GCx R) (u : Rˣ) : GHom C C where
  f i j h := by
    subst h
    exact (u : R) • LinearMap.id
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change (u : R) • C.d i i₁ h₁ x = C.d i i₁ h₂ ((u : R) • x)
    exact (map_smul (C.d i i₁ h₂) (u : R) x).symm

/-- The map's components are the same scalar multiplication in every degree. -/
theorem unitScalarRelationHom_apply (C : GCx R) (u : Rˣ) (n : ℤ) (x : C.X n) :
    (unitScalarRelationHom C u).f n n rfl x = (u : R) • x := rfl

/-- Unit multiplication is an isomorphism, with the inverse unit as its inverse map. -/
def unitScalarCochainIso (C : GCx R) (u : Rˣ) : C.toCC ≅ C.toCC where
  hom := GHom.toCC (unitScalarRelationHom C u)
  inv := GHom.toCC (unitScalarRelationHom C u⁻¹)
  hom_inv_id := by
    ext n x
    change ((u⁻¹ : Rˣ) : R) • ((u : R) • x) = x
    rw [smul_smul, Units.inv_mul, one_smul]
  inv_hom_id := by
    ext n x
    change (u : R) • (((u⁻¹ : Rˣ) : R) • x) = x
    rw [smul_smul, Units.mul_inv, one_smul]

/-- Rescaling a boundary-annihilating trace by a unit still annihilates boundaries. -/
theorem unitScaledTrace_boundary {T : GCx R} (m : ℤ) (tr : T.X m →ₗ[R] R)
    (htr : ∀ z, tr (T.d (m - 1) m (by omega) z) = 0) (u : Rˣ) :
    ∀ z, ((u : R) • tr) (T.d (m - 1) m (by omega) z) = 0 := by
  intro z
  rw [LinearMap.smul_apply, htr, smul_zero]

/-- The adjoint of the scaled trace is the same adjoint followed by unit multiplication. -/
theorem adjHom_unit_trace_eq_comp {A B T : GCx R} (P : GPair A B T)
    (m : ℤ) (tr : T.X m →ₗ[R] R)
    (htr : ∀ z, tr (T.d (m - 1) m (by omega) z) = 0) (u : Rˣ) :
    GHom.toCC (adjHom P m ((u : R) • tr) (unitScaledTrace_boundary m tr htr u)) =
      GHom.toCC (adjHom P m tr htr) ≫ (unitScalarCochainIso (dualCx B m) u).hom := by
  ext n x
  apply dualCx_ext
  intro y
  rfl

/-- Unit rescaling preserves quasi-isomorphy of the same traced adjoint. -/
theorem adjHom_quasiIso_iff_unit_trace {A B T : GCx R} (P : GPair A B T)
    (m : ℤ) (tr : T.X m →ₗ[R] R)
    (htr : ∀ z, tr (T.d (m - 1) m (by omega) z) = 0) (u : Rˣ) :
    QuasiIso (GHom.toCC (adjHom P m ((u : R) • tr) (unitScaledTrace_boundary m tr htr u))) ↔
      QuasiIso (GHom.toCC (adjHom P m tr htr)) := by
  rw [adjHom_unit_trace_eq_comp]
  exact quasiIso_iff_comp_right (GHom.toCC (adjHom P m tr htr))
    (unitScalarCochainIso (dualCx B m) u).hom

end UnitComplex

section CompactScalar

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
  {A B T : GCx R}

/-- Any two top traces with the required next-degree support give the same quasi-isomorphy verdict. -/
theorem adjHom_quasiIso_iff_of_topTraceIso_compact (P : GPair A B T)
    (m : ℤ) (tr₁ tr₂ : T.X m →ₗ[R] R)
    (h₁ : IsTopTraceIso (T.d (m - 1) m (by omega)) (T.d m (m + 1) rfl) tr₁)
    (h₂ : IsTopTraceIso (T.d (m - 1) m (by omega)) (T.d m (m + 1) rfl) tr₂)
    [Module.IsTorsionFree R (T.X (m + 2))]
    (hnext : ∀ z : T.X (m + 1), T.d (m + 1) (m + 2) (by omega) z = 0 →
      ∃ y : T.X m, T.d m (m + 1) rfl y = z) :
    QuasiIso (GHom.toCC (adjHom P m tr₁ h₁.1)) ↔
      QuasiIso (GHom.toCC (adjHom P m tr₂ h₂.1)) := by
  obtain ⟨u, hu⟩ := topTraceUnit_on_cycles h₁ h₂
  have hcyc : ∀ z : T.X m, T.d m (m + 1) rfl z = 0 → tr₁ z = ((u : R) • tr₂) z := by
    intro z hz
    exact hu z hz
  have h := adjHom_quasiIso_iff_of_eq_on_cycles_compact P m tr₁ ((u : R) • tr₂)
    h₁.1 (unitScaledTrace_boundary m tr₂ h₂.1 u) hnext hcyc
  exact h.2.trans (adjHom_quasiIso_iff_unit_trace P m tr₂ h₂.1 u)

end CompactScalar

end ZInQ.Contrib.RC53Assist.IntegralDuality
