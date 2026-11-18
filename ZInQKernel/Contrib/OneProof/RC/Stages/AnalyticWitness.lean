import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Curve
import ZInQKernel.Contrib.CloudB3RC53.Assembly

/-! Fixed witness discriminants and prepared support (tex 8246–8260).
Use the two existing BFH clauses with the same modularity input as RC13. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Stages

open ZInQ.Manuscript ZInQ.Manuscript.RC.Nonvanishing ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.CloudB3RC53

/-- The positive unit squareclass filter containing one. -/
def positivePrepared (S : Finset ℕ) (D : ℤ) : Prop :=
  0 < D ∧ Squarefree D ∧ ∀ p ∈ S, ¬ (p : ℤ) ∣ D ∧ IsSquareAt p (D : ℚ)

/-- Its empty squareclass is prepared. -/
theorem positivePrepared_one {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    positivePrepared S 1 := by
  refine ⟨by decide, squarefree_one, fun p hp => ⟨?_, ?_⟩⟩
  · intro hd
    exact (hS p hp).ne_one (Nat.dvd_one.mp (Int.natCast_dvd.mp hd))
  · intro _
    simp

/-- The two discriminants and the enlarged prepared support, all chosen before any
detecting prime. Retain fundamental-discriminant data from the original BFH clauses. -/
theorem exists_fixed_discriminants {ℓ : ℕ} (P : Prints) (hAdm : Adm ℓ)
    (hSel : SelmerCorankOne (Ecurve ℓ))
    (hBFH₀ : BFHNonvanishing) (hBFH₁ : BFHSimpleZero)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hbase : S0 ℓ ⊆ S) :
    ∃ hstar Dw : ℤ, ∃ S' : Finset ℕ,
      S' = S ∪ hstar.natAbs.primeFactors ∧
      (∀ p ∈ S', p.Prime) ∧
      hstar < 0 ∧ hstar % 8 = 1 ∧ IsFundamentalDiscriminant hstar ∧
      (∀ p ∈ S, SplitsIn hstar p) ∧
      CentralNonzero (qtwist (Ecurve ℓ) hstar) ∧
      IsFundamentalDiscriminant Dw ∧ positivePrepared S' Dw ∧
      AnalyticRank (qtwist (Ecurve ℓ) Dw) 1 := by
  have hℓ : 0 < ℓ := hAdm.1
  have hw := rootNumberNode_proof P ℓ hAdm hSel
  have h2 : 2 ∈ S := hbase (by simp [S0])
  have h3 : 3 ∈ S := hbase (by simp [S0])
  have hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S := fun p hp h =>
    hbase (by simp [S0, Nat.mem_primeFactors, hp, h, hℓ.ne'])
  obtain ⟨hstar, hneg, h8, hfund, hsplit, hcen⟩ :=
    genusPartner_of_BFH hBFH₀ P.bcdt hℓ hw hS h2 h3 hℓS
  let S' := S ∪ hstar.natAbs.primeFactors
  have hS' : ∀ p ∈ S', p.Prime := fun p hp =>
    (Finset.mem_union.mp hp).elim (hS p) Nat.prime_of_mem_primeFactors
  have hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt (Ecurve ℓ) p → p ∈ S' := by
    intro p hp hn
    apply Finset.mem_union_left
    exact bad_curve_mem (m := (ℓ : ℤ)) h2 h3
      (fun v hv hd => hℓS v hv (by exact_mod_cast hd)) p hp (by simpa [Ecurve] using hn)
  obtain ⟨Dw, hd, hpos, hdsplit, hL⟩ :=
    hBFH₁ _ (curve_nat_isElliptic hℓ) (P.bcdt _ (curve_nat_isElliptic hℓ)) (-1) hw S' hS' hbad
  have hd8 := (hdsplit 2 (Finset.mem_union_left _ h2)).two
  have hsf := (hd.squarefree_of_odd (Int.odd_iff.mpr (by omega))).1
  have hc : CentralNonzero (qtwist (Ecurve ℓ) hstar) := by
    rwa [qtwist_Ecurve]
  exact ⟨hstar, Dw, S', rfl, hS', hneg, h8, hfund, hsplit, hc, hd,
    ⟨by linarith, hsf, fun p hp => ⟨SplitsIn.not_dvd (hS' p hp) (hdsplit p hp),
      isSquareAt_of_splitsIn (hS' p hp) (hdsplit p hp)⟩⟩, hL⟩

#print axioms positivePrepared_one
#print axioms exists_fixed_discriminants

end ZInQ.Manuscript.RC.Stages
