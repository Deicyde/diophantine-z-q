import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8Lift
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8Isometry

/-!
# Theorem 5.3, Lane RC32 round 5: the decomposition group is the local Galois group

For every valuation `w` of `ℚ̄_r` extending `v_r` and every embedding `ι : ℚ̄ → ℚ̄_r`, every element
of the decomposition group of the centre `P` of `ι` is the restriction of an element of
`Gal(ℚ̄_r/ℚ_r)` along `ι` (Neukirch, *Algebraic Number Theory*, II.9.6), PROVED:

* `exists_lift_of_smul_eq`: the third conjunct of `LocalGaloisDecomposition`, from
  `exists_lift_of_integral_iff` (`CommonCoordinate8Lift.lean`: density of `ℚ` in `ℚ_r`, closed range
  of the restriction map, infinite Galois correspondence) and `le_one_iff_of_smul_eq`
  (`CommonCoordinate8Isometry.lean`: the valuation ring of `w ∘ ι` is `ℤ̄_P`);
* `localGaloisDecomposition_of_valuation`: hence `LocalGaloisDecomposition r hr` follows from a
  `Gal(ℚ̄_r/ℚ_r)`-invariant valuation of `ℚ̄_r` extending `v_r` whose residues are reached from `ℤ̄`
  along every embedding (`InvariantResidueValuation r hr`);
* `decompositionFrobeniusQ_of_valuation` and `frobeniusTrace_of_RD_valuation`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.AddressGenuine (Zbar)
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)
open ZInQ.Contrib.CloudB3RC53.ModularWeil (TateReductionComparison DetEqDegree)
open scoped WithZero Pointwise

variable {r : ℕ} {hr : r.Prime}

/-- **The decomposition group lifts to `Gal(ℚ̄_r/ℚ_r)`** (PROVED; Neukirch ANT II.9.6): for every
valuation `w` of `ℚ̄_r` extending `v_r`, every embedding `ι` and every `g ∈ G_ℚ` fixing the
centre of `ι`, there is `σ ∈ Gal(ℚ̄_r/ℚ_r)` with `σ ∘ ι = ι ∘ g`. -/
theorem exists_lift_of_smul_eq {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hg : g • centre hw ι = centre hw ι) :
    ∃ σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr, ∀ x : Qbar, σ (ι x) = ι (g x) :=
  exists_lift_of_integral_iff hw ι g (le_one_iff_of_smul_eq hw ι g hg)

/-- **A `Gal(ℚ̄_r/ℚ_r)`-invariant valuation of `ℚ̄_r` extending `v_r` whose residues are reached
from `ℤ̄` along every embedding** (the first conjuncts of `LocalGaloisDecomposition`;
Neukirch ANT II.4.8 and II.7). -/
def InvariantResidueValuation (r : ℕ) (hr : r.Prime) : Prop :=
  ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (w : Valuation (Qrbar r hr) Γ)
    (_ : ExtendsVr w),
    (∀ (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) (y : Qrbar r hr), w (σ y) = w y) ∧
    (∀ (ι : Qbar →ₐ[ℚ] Qrbar r hr) (y : Qrbar r hr), w y ≤ 1 →
      ∃ x : Zbar, w (y - ι x) < 1)

/-- **The local Galois decomposition from an invariant valuation** (PROVED). -/
theorem localGaloisDecomposition_of_valuation (H : InvariantResidueValuation r hr) :
    LocalGaloisDecomposition r hr := by
  obtain ⟨Γ, inst, w, hw, hinv, hres⟩ := H
  exact ⟨Γ, inst, w, hw, hinv, hres, fun ι g hg => exists_lift_of_smul_eq hw ι g hg⟩

/-- **`DecompositionFrobeniusQ` from an invariant valuation** (PROVED). -/
theorem decompositionFrobeniusQ_of_valuation (H : InvariantResidueValuation r hr) :
    DecompositionFrobeniusQ r hr :=
  decompositionFrobeniusQ_of_local (localGaloisDecomposition_of_valuation H)

/-- **`FrobeniusTrace` from (R), (D) and invariant valuations at the odd primes** (PROVED, for
every elliptic `E`). -/
theorem frobeniusTrace_of_RD_valuation (hR : TateReductionComparison) (hD : DetEqDegree)
    (hV : ∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → InvariantResidueValuation r hr)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] : FrobeniusTrace E :=
  frobeniusTrace_of_RD_local hR hD
    (fun r hr hr2 => localGaloisDecomposition_of_valuation (hV r hr hr2)) E

end ZInQ.Manuscript.RC.Wiring
