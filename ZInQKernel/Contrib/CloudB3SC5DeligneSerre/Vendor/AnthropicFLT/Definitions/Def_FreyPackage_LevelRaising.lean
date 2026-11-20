/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_FreyPackage_LevelRaising (git blob b6ab3b3e799c95bc4fecdbe220e022691e3bc0c6, sha256 e796da04320cfa5264d4f8ea44051a0d49c646a634af7d878ca92ec00d00bac2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

namespace CuspForm

def IsNewAt {M : ℕ} (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) : Prop :=
  ModularFormClass.qCoeff g q ^ 2 = 1

end CuspForm

namespace FreyPackage

noncomputable local instance instDecEqQbarLevelRaising :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def IsCongruentWitness (P : FreyPackage) (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) : Prop :=
  f.IsNormalizedEigenform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def ModularRepOfLevelNewAt (P : FreyPackage) (M q : ℕ) : Prop :=
  ∃ (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)), P.IsCongruentWitness M g W 𝔪 ∧ g.IsNewAt q

def LevelRaising (P : FreyPackage) (N q' : ℕ) : Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)),
    0 < N → q'.Prime → ¬ q' ∣ N → q' ≠ P.p →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.IsCongruentWitness N f W 𝔪 →
    (∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f q' ∧
      a ^ 2 - ((q' : integralClosure ℤ ℂ) + 1) ^ 2 ∈ 𝔪) →
    P.ModularRepOfLevelNewAt (N * q') q'

end FreyPackage
