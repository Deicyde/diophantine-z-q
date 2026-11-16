import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.Contrib.CloudB3W16Torsion.RelativeBridges
import ZInQKernel.Contrib.CloudB3W16FiniteGroup.TorsionStructure
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero

/-!
# Mumford's prime-to-characteristic torsion theorem over an algebraically closed field

The source degree theorem is imported with its complete proof, rather than taken
as an additional hypothesis. The final map respects the original PkgI2
multiplication. The generic finite-group classification is the independently
ported CloudB3W16FiniteGroup theorem; this file does not duplicate that proof.

Source provenance and full credits/notices/license are preserved in
`CloudB3W16Torsion/Vendor/AnthropicFLT` and `CloudB3W16FiniteGroup`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudB3W16Torsion

/-- The cardinality of the *original* torsion set, obtained from the genuine geometric
source cardinality theorem, including its proved degree formula. -/
theorem card_torsion {k : Type} [Field k] [IsAlgClosed k]
    (A : Grp (Over (Spec (.of k)))) [PkgI2.IsAbelianVariety A] (g n : ℕ)
    (hg : topologicalKrullDim A.X.left = (g : WithBot ℕ∞)) (hnk : (n : k) ≠ 0) :
    Nat.card (PkgI2.torsion A k n) = n ^ (2 * g) := by
  haveI := smoothOfRelativeDimension A g hg
  rw [Nat.card_congr (torsionEquivRelative A n)]
  exact GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
    k A.X.hom (relativeLaw A) (relativeLaw_commutative A)
    (abelianSchemePropertyBundle A) g n hnk

/-- Exact TailQ1257, with no additional hypothesis. -/
theorem mumfordTorsionAlgClosed_proof : AvSplit.MumfordTorsionAlgClosed := by
  intro k _ _ A _ g n hg hn hnk
  obtain ⟨e⟩ :=
    ZInQ.Contrib.CloudB3W16FiniteGroup.nonempty_torsionBy_addEquiv_pi_zmod
      (M := Additive (PkgI2.Pts A k)) (r := 2 * g) hn (fun d hd => by
        have hdk : IsUnit (d : k) :=
          isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) (isUnit_iff_ne_zero.mpr hnk)
        change Nat.card (AddSubgroup.torsionBy (Additive (PkgI2.Pts A k)) d) = d ^ (2 * g)
        rw [← Nat.card_congr (torsionEquivAddSubgroup A d)]
        exact card_torsion A g d hg (isUnit_iff_ne_zero.mp hdk))
  refine ⟨(torsionEquivAddSubgroup A n).trans e.toEquiv, ?_⟩
  intro x y h
  change e (torsionEquivAddSubgroup A n ⟨x.1 * y.1, h⟩) =
    e (torsionEquivAddSubgroup A n x) + e (torsionEquivAddSubgroup A n y)
  rw [torsionEquivAddSubgroup_mul, map_add]

end ZInQ.Contrib.CloudB3W16Torsion
