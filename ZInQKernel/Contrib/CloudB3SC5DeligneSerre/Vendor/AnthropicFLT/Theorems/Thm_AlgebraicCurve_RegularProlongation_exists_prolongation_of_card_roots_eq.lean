/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq (git blob 89faa27bf45611c1250725617c812a7c33b7f766, sha256 76117ef76d347c80d1b0cac0db9c70edf8942521eaddb5e85882e3f3013fddb5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.RegularProlongation.exists_prolongation_of_card_roots_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    {q : ℕ} [Fact q.Prime] (f : R.integers)
    (S : Finset Fbar) (hS : S.card = q) (hSf : ∀ s ∈ S, s ^ q = R.residue f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C (f : F))] (hdeg : Module.finrank F F' = q) :
    ∃ R' : Fin q → RegularProlongation A F' Fbar,
      Function.Injective (fun i => (R' i).integers) ∧
      ∀ i, (R' i).integers.comap (algebraMap F F') = R.integers ∧
        ∀ (x : (R' i).integers) (y : R.integers), algebraMap F F' y = x →
          (R' i).residue x = R.residue y := by
  revert L A F Fbar R q f S hS hSf F' hdeg
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.solution
