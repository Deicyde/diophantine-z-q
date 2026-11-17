/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside (git blob 5f7110c8f59ac89b698c859c5d057bf5afc78807, sha256 c47af94bacb5d6fe5144d9fae4540b8a4f436a1ccc1cd46d2f48b117b628b31b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_IsDedekindDomain_FiniteUnitIdeles

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

def unitIdelesOutside (S : Set (HeightOneSpectrum R)) : Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {δ | ∀ v : HeightOneSpectrum R, v ∉ S →
    (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
      ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' v _ := ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y hx hy v hv
    obtain ⟨hx1, hx2⟩ := hx v hv
    obtain ⟨hy1, hy2⟩ := hy v hv
    exact ⟨by rw [Units.val_mul]; exact mul_mem hx1 hy1, by rw [mul_inv, Units.val_mul]; exact mul_mem hx2 hy2⟩
  inv_mem' := by
    rintro x hx v hv
    obtain ⟨hx1, hx2⟩ := hx v hv
    exact ⟨hx2, by rw [inv_inv]; exact hx1⟩

variable {R K} in
theorem mem_unitIdelesOutside_iff (S : Set (HeightOneSpectrum R)) (δ : (FiniteAdeleRing R K)ˣ) :
    δ ∈ unitIdelesOutside R K S ↔
      ∀ v : HeightOneSpectrum R, v ∉ S →
        (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem unitIdelesOutside_empty : unitIdelesOutside R K (∅ : Set (HeightOneSpectrum R)) = unitIdeles R K :=
  Subgroup.ext fun _ =>
    ⟨fun h => ⟨fun v => (h v fun hv => hv).1, fun v => (h v fun hv => hv).2⟩, fun h v _ => ⟨h.1 v, h.2 v⟩⟩

theorem unitIdelesOutside_mono {S T : Set (HeightOneSpectrum R)} (h : S ⊆ T) :
    unitIdelesOutside R K S ≤ unitIdelesOutside R K T :=
  fun _ hx v hv => hx v fun hvS => hv (h hvS)

theorem unitIdeles_le_unitIdelesOutside (S : Set (HeightOneSpectrum R)) :
    unitIdeles R K ≤ unitIdelesOutside R K S :=
  fun _ hx v _ => ⟨hx.1 v, hx.2 v⟩

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def unitIdelesOutside (S : Set (IsDedekindDomain.HeightOneSpectrum R)) : Subgroup (AdeleRing R K)ˣ :=
  (IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S).comap
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom)

variable {R K} in
theorem mem_unitIdelesOutside_iff (S : Set (IsDedekindDomain.HeightOneSpectrum R)) (x : (AdeleRing R K)ˣ) :
    x ∈ unitIdelesOutside R K S ↔
      Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom x ∈
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S :=
  Iff.rfl

end NumberField.AdeleRing
