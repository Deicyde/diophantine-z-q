/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_GaloisRep_ComplexConjugation (git blob dd49c4198b0a59f535e48e1aaa15505b2b2d5771, sha256 ba2fe1792ce8ef766c7bb9cb950092c68c9b2eb658427a0a0c5479e048cc7bd5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

local instance isAlgebraicQbar_cc : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_cc : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar_cc : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
noncomputable local instance instDecEqQbar_cc : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

noncomputable def complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift

noncomputable local instance instAlgebraQbarComplex : Algebra (AlgebraicClosure ℚ) ℂ :=
  complexEmbedding.toRingHom.toAlgebra
local instance instTowerQbarComplex : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

noncomputable def complexConjAlgEquiv : ℂ ≃ₐ[ℚ] ℂ :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => map_ratCast (starRingEnd ℂ) x

@[simp] lemma complexConjAlgEquiv_apply (z : ℂ) : complexConjAlgEquiv z = starRingEnd ℂ z := rfl

lemma complexConjAlgEquiv_mul_self : complexConjAlgEquiv * complexConjAlgEquiv = 1 :=
  AlgEquiv.ext fun z => Complex.conj_conj z

noncomputable def complexConjugation : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ :=
  AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℂ) (AlgebraicClosure ℚ) complexConjAlgEquiv

theorem complexEmbedding_complexConjugation (x : AlgebraicClosure ℚ) :
    complexEmbedding (complexConjugation x) = starRingEnd ℂ (complexEmbedding x) :=
  AlgEquiv.restrictNormal_commutes complexConjAlgEquiv (AlgebraicClosure ℚ) x

theorem complexConjugation_mul_self : complexConjugation * complexConjugation = 1 := by
  rw [complexConjugation, ← map_mul, complexConjAlgEquiv_mul_self, map_one]

theorem complexConjugation_sq : complexConjugation ^ 2 = 1 := by
  rw [sq]; exact complexConjugation_mul_self

theorem complexConjugation_inv : complexConjugation⁻¹ = complexConjugation :=
  inv_eq_of_mul_eq_one_right complexConjugation_mul_self

namespace ExtCitation

noncomputable def archimedeanDecomposition :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  Subgroup.zpowers complexConjugation

noncomputable def archimedeanGen : archimedeanDecomposition :=
  ⟨complexConjugation, Subgroup.mem_zpowers complexConjugation⟩

noncomputable def archimedeanLoc :
    archimedeanDecomposition →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  archimedeanDecomposition.subtype

@[simp] lemma archimedeanLoc_archimedeanGen :
    archimedeanLoc archimedeanGen = complexConjugation := rfl

end ExtCitation
