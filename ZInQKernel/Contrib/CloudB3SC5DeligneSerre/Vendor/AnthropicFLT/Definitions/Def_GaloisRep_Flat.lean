/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_GaloisRep_Flat (git blob a72d8d467c48eedb603d4147e8cd8142817ee8cd, sha256 39c0c22e6cb81c0773f77335066bf873e21e94750b16b7ae114a9b60499a325f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Flat.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace GaloisRep

def ratLocalizedAt (p : ℕ) : Subring ℚ where
  carrier := {q : ℚ | q.den.Coprime p}
  mul_mem' {a b} ha hb := Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (ha.mul_left hb)
  one_mem' := by simp
  add_mem' {a b} ha hb := Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (ha.mul_left hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

end GaloisRep

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

noncomputable def levelAction (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) →ₗ[A] (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) :=
  Submodule.mapQ _ _ (ρ.ρ σ) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

def IsFlatAt (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  Finite (IsLocalRing.ResidueField A) ∧ ∀ I : Ideal A, Finite (A ⧸ I) →
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))),
        (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.levelAction I σ (e f)

end GaloisRepAdic

namespace GaloisRep

def flatCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ρ.DetIsCyclotomic p ∧ ρ.IsFlatAt p ∧
    ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q

def minimalFlatCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => flatCondition 𝒪 p S ρ ∧
    ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q

end GaloisRep
