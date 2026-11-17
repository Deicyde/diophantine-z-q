/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_HeckeModule (git blob 1df2d7bac37814bef58f30b1b70166452372199a, sha256 d9d6b104ecbe2a0db9c3510f3cdac631c6084af6c83f57d42028927e3f4055c3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeOperatorTotal
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Operators

variable (N : ℕ) [NeZero N]

def heckeOperatorBar (ℓ : Nat.Primes) : Module.End ℤ (JZero N) :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ).toIntLinearMap

theorem heckeOperatorBar_apply (ℓ : Nat.Primes) (x : JZero N) :
    heckeOperatorBar N ℓ x =
      (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ x) :=
  rfl

def HeckeOperatorsCommuteBar : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeOperatorBar N ℓ * heckeOperatorBar N ℓ' = heckeOperatorBar N ℓ' * heckeOperatorBar N ℓ

end Operators

section Eval

variable {N : ℕ} [NeZero N]

theorem isMulCommutative_adjoin_heckeOperatorBar (h : HeckeOperatorsCommuteBar N) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeOperatorBar N))) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩ _ -- [port]
    exact h ℓ ℓ')

open scoped IsMulCommutative in

def heckeEvalBarAux (h : HeckeOperatorsCommuteBar N) :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (heckeOperatorBar N)) :
      Subalgebra ℤ (Module.End ℤ (JZero N))) :=
  haveI := isMulCommutative_adjoin_heckeOperatorBar h
  MvPolynomial.aeval fun ℓ =>
    (⟨heckeOperatorBar N ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :
      Algebra.adjoin ℤ (Set.range (heckeOperatorBar N)))

def heckeEvalBar (h : HeckeOperatorsCommuteBar N) : HeckeAlg →+* Module.End ℤ (JZero N) :=
  ((Algebra.adjoin ℤ (Set.range (heckeOperatorBar N))).val.comp (heckeEvalBarAux h)).toRingHom

theorem heckeEvalBar_apply (h : HeckeOperatorsCommuteBar N) (t : HeckeAlg) :
    heckeEvalBar h t = (heckeEvalBarAux h t : Module.End ℤ (JZero N)) :=
  rfl

open scoped IsMulCommutative in
theorem heckeEvalBarAux_heckeGen (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) :
    heckeEvalBarAux h (heckeGen ℓ) =
      ⟨heckeOperatorBar N ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :=
  haveI := isMulCommutative_adjoin_heckeOperatorBar h
  MvPolynomial.aeval_X _ ℓ

theorem heckeEvalBar_heckeGen (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) :
    heckeEvalBar h (heckeGen ℓ) = heckeOperatorBar N ℓ := by
  rw [heckeEvalBar_apply, heckeEvalBarAux_heckeGen]

theorem heckeEvalBar_C (h : HeckeOperatorsCommuteBar N) (a : ℤ) :
    heckeEvalBar h (MvPolynomial.C a) = (a : Module.End ℤ (JZero N)) := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

end Eval

section TheModule

variable (N : ℕ) [NeZero N]

open Classical in

@[implicit_reducible]
def heckeModuleBar : Module HeckeAlg (JZero N) :=
  if h : HeckeOperatorsCommuteBar N then Module.compHom (JZero N) (heckeEvalBar h)
  else Module.compHom (JZero N) (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))

variable {N}

theorem heckeModuleBar_smul_def (h : HeckeOperatorsCommuteBar N) (t : HeckeAlg) (x : JZero N) :
    (letI := heckeModuleBar N; t • x) = heckeEvalBar h t x := by
  have e : heckeModuleBar N = Module.compHom (JZero N) (heckeEvalBar h) := dif_pos h
  rw [e]
  rfl

theorem heckeModuleBar_heckeGen_smul (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes)
    (x : JZero N) : (letI := heckeModuleBar N; heckeGen ℓ • x) = heckeOperatorBar N ℓ x := by
  rw [heckeModuleBar_smul_def h, heckeEvalBar_heckeGen]

theorem heckeModuleBar_smul_of_not (h : ¬ HeckeOperatorsCommuteBar N) (t : HeckeAlg) (x : JZero N) :
    (letI := heckeModuleBar N; t • x) = MvPolynomial.constantCoeff t • x := by
  have e : heckeModuleBar N =
      Module.compHom (JZero N)
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ)) :=
    dif_neg h
  rw [e]
  show (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ) t) • x = _
  rw [MvPolynomial.eval₂Hom_zero_apply, eq_intCast, Int.cast_id]

theorem heckeModuleBar_heckeGen_smul_of_not (h : ¬ HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes)
    (x : JZero N) : (letI := heckeModuleBar N; heckeGen ℓ • x) = 0 := by
  rw [heckeModuleBar_smul_of_not h, heckeGen, MvPolynomial.constantCoeff_X, zero_zsmul]

theorem heckeModuleBar_C_smul (a : ℤ) (x : JZero N) :
    (letI := heckeModuleBar N; (MvPolynomial.C a : HeckeAlg) • x) = a • x := by
  by_cases h : HeckeOperatorsCommuteBar N
  · rw [heckeModuleBar_smul_def h, heckeEvalBar_C, Module.End.intCast_apply]
  · rw [heckeModuleBar_smul_of_not h, MvPolynomial.constantCoeff_C]

end TheModule

end ModularCurve

end
