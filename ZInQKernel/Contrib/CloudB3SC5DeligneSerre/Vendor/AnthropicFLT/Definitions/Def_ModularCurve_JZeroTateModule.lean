/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_JZeroTateModule (git blob 7b8fa0dbe9be8d74c3833522ff42e9ca8ecc0693, sha256 d0cc311c42241c07f0156c551003feeca061dbce7a1afe5e41a19e622e9b5f56).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ArithmeticGalois
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_HeckeGalois_EichlerShimura
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_TateModule
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Basis.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve

section Integral

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

def tateHeckeRep : HeckeAlg →+* Module.End ℤ_[p] (TateModule p J) where
  toMonoidHom := TateModule.rep p J HeckeAlg
  map_zero' := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show (0 : HeckeAlg) • (x : ℕ → J) n = 0
    exact zero_smul HeckeAlg ((x : ℕ → J) n)
  map_add' s t := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show (s + t) • (x : ℕ → J) n = s • (x : ℕ → J) n + t • (x : ℕ → J) n
    exact add_smul s t ((x : ℕ → J) n)

theorem tateHeckeRep_apply (t : HeckeAlg) :
    tateHeckeRep p J t = TateModule.rep p J HeckeAlg t :=
  rfl

theorem coe_tateHeckeRep_apply_apply (t : HeckeAlg) (x : TateModule p J) (n : ℕ) :
    ((tateHeckeRep p J t x : TateModule p J) : ℕ → J) n = t • (x : ℕ → J) n :=
  rfl

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J]

abbrev RationalTateModule : Type :=
  ℚ_[p] ⊗[ℤ_[p]] TateModule p J

def rationalGaloisRep (G : Type) [Monoid G] [DistribMulAction G J] :
    G →* Module.End ℚ_[p] (RationalTateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J) :
      Module.End ℤ_[p] (TateModule p J) →* Module.End ℚ_[p] (RationalTateModule p J)).comp
    (TateModule.rep p J G)

theorem rationalGaloisRep_apply (G : Type) [Monoid G] [DistribMulAction G J] (g : G) :
    rationalGaloisRep p J G g = (TateModule.rep p J G g).baseChange ℚ_[p] :=
  rfl

theorem rationalGaloisRep_tmul (G : Type) [Monoid G] [DistribMulAction G J] (g : G) (a : ℚ_[p])
    (x : TateModule p J) :
    rationalGaloisRep p J G g (a ⊗ₜ x) = a ⊗ₜ TateModule.rep p J G g x :=
  rfl

variable [Module HeckeAlg J]

def rationalHeckeRep : HeckeAlg →+* Module.End ℚ_[p] (RationalTateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)).toRingHom.comp (tateHeckeRep p J)

theorem rationalHeckeRep_apply (t : HeckeAlg) :
    rationalHeckeRep p J t = (tateHeckeRep p J t).baseChange ℚ_[p] :=
  rfl

theorem rationalHeckeRep_tmul (t : HeckeAlg) (a : ℚ_[p]) (x : TateModule p J) :
    rationalHeckeRep p J t (a ⊗ₜ x) = a ⊗ₜ tateHeckeRep p J t x :=
  rfl

def rationalHeckeAlgebra : Subalgebra ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p J)) :=
  Algebra.adjoin ℚ_[p] (Set.range (rationalHeckeRep p J))

theorem rationalHeckeRep_mem_rationalHeckeAlgebra (t : HeckeAlg) :
    rationalHeckeRep p J t ∈ rationalHeckeAlgebra p J :=
  Algebra.subset_adjoin (Set.mem_range_self t)

end Rational

section Predicate

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]

def RationalRankTwoCyclotomicOf : Prop :=
  ∃ b : Module.Basis (Fin 2) (rationalHeckeAlgebra p J) (RationalTateModule p J),
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
      ∀ A' : ValuationSubring L, A'.LiesOverPrime ℓ →
        ∀ σ : L ≃ₐ[K] L, A'.IsFrobeniusAt σ ℓ →
          (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 0))) 0
              * (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 1))) 1
            - (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 1))) 0
              * (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 0))) 1
            = (ℓ : rationalHeckeAlgebra p J)

end Predicate

section ModularInstance

def RationalRankTwoCyclotomic (M p : ℕ) [Fact p.Prime] [Module HeckeAlg (JZero M)] : Prop :=
  RationalRankTwoCyclotomicOf (K := ℚ) (L := AlgebraicClosure ℚ) M p (JZero M)

end ModularInstance

end ModularCurve

end
