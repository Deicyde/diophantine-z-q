import ZInQKernel.Contrib.OneProof.CasselsTate.PrimaryFiniteLayer
import ZInQKernel.Contrib.OneProof.CasselsTate.PrimaryPairingSum
import ZInQKernel.Contrib.OneProof.CasselsTate.SelmerLayerDescent

/-!
# The pairing on Sha from finite Selmer pairings

For each prime, a finite Selmer pairing at one sufficiently high power gives
a nondegenerate form on the finite summand of the primary part of Sha. The
primary forms combine because every class in Sha has finite order. This proves
the existence form of the Cassels–Tate pairing used by the manuscript.
-/

noncomputable section

namespace ZInQ.Manuscript.CasselsTateGlobal

open SelmerTwoPower

/-- The prime-power specialization of the finite Selmer theorem restated by
Tom Fisher, *On binary quartics and the Cassels–Tate pairing*, Research in
Number Theory 8 (2022), article 74, §1 (arXiv:2208.14977v1, p. 1, the
two displays and the sentences following them). For an elliptic curve over a
number field, the finite Selmer groups at levels `n ≥ 2` carry alternating
pairings with kernel the image from level `n²`. Here the field is `ℚ`,
finiteness is used at prime level, and the pairings at positive prime powers. -/
def FisherPrimePowerSelmer (E : WeierstrassCurve ℚ) : Prop :=
  ∀ p : ℕ, p.Prime → Finite (E.selmerGroup Fam.emb p) ∧
    ∀ k : ℕ, 0 < k → FiniteSelmerPairingAt E (p ^ k)

/-- On an elliptic curve over `ℚ`, the finite Selmer inputs give an alternating
pairing on Sha whose left radical is its maximal divisible subgroup. -/
theorem casselsTatePairing_of_finiteSelmer (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : FisherPrimePowerSelmer E) : CasselsTatePairing E := by
  apply pairing_of_primary_pairings (sha E)
  · intro x
    obtain ⟨n, hn, hx⟩ := exists_nsmul_eq_zero_H1 E x.val
    exact ⟨n, Nat.pos_of_ne_zero hn, Subtype.ext hx⟩
  · intro p hp
    let _ : Fact p.Prime := ⟨hp⟩
    obtain ⟨hfin, hpair⟩ := h p hp
    apply primary_pairing_of_finite_layers (sha E) p
    · exact sha_torsion_finite_of_finiteSelmer E p hp.two_le hfin
    · intro k hk
      exact sha_torsion_pairing_of_finiteSelmerPairing E (p ^ k)
        (one_lt_pow' hp.one_lt hk.ne') (hpair k hk)

/-- Fisher's finite-level input restricted to the manuscript's curves in Lemma 5.4. -/
def FisherPrimePowerSelmerCurves : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → FisherPrimePowerSelmer (Manuscript.curve ℓ)

/-- The full all-prime Cassels–Tate hypothesis of the frozen target follows
from the finite prime-power Selmer pairings and finiteness at prime level. -/
theorem casselsTatePairingCurves_of_finiteSelmer (h : FisherPrimePowerSelmerCurves) :
    PoleS12.CasselsTatePairingCurves := by
  intro ℓ hℓ hsf hmod
  let _ := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne' : (ℓ : ℚ) ≠ 0)
  exact casselsTatePairing_of_finiteSelmer _ (h ℓ hℓ hsf hmod)

end ZInQ.Manuscript.CasselsTateGlobal
