import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedSeed

/-! The fixed-place divisibility used by the actual two-fresh orbit. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs EvenBudget IsDedekindDomain NumberField ThetaCoeff Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

/-- The calculation takes place in the fixed ring, before passing to any
field extension or residual constituent representation. -/
theorem fixedH_two_fresh (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
    {q r n : ℕ} (hn : n ≠ 0) (hq : (evenTypes W.S hS.1).Good q)
    (hr : (evenTypes W.S hS.1).Good r) (hqU : q ∉ U) (hrU : r ∉ U)
    (hqr : q ≠ r) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n) :
    (2 : FixedRing v) ∣ timesTheta (fixedH (hS := hS) C₀ i U hU) (r * (q * n)) := by
  let J := U.toList
  let j := r * (q * n)
  have hg : ∀ p ∈ J, (evenTypes W.S hS.1).Good p :=
    fun p hp => hU p (Finset.mem_toList.mp hp)
  let H := source_at_place C₀ hS Subtype.val_injective
  have hw : 2 ≤ (oddPart j \ J.toFinset).card := by
    rw [show J.toFinset = U from Finset.toList_toFinset U]
    exact two_fresh_weight hn hq.1 hr.1 hqr hqn hrn hqU hrU
  have hoff : ¬ oddPart j ⊆ J.toFinset := by
    intro h
    rw [Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.card_empty] at hw
    omega
  obtain ⟨c, hc⟩ := normalized_double (K := FixedField v) H J U.nodup_toList hg hw
  have he : dividedCoeff H i J U.nodup_toList hg j = 2 * c := by
    apply (Subtype.val_injective : Function.Injective (algebraMap (FixedRing v) (FixedField v)))
    change algebraMap (FixedRing v) (FixedField v) (dividedCoeff H i J U.nodup_toList hg j) =
      algebraMap (FixedRing v) (FixedField v) (2 * c)
    rw [dividedCoeff_spec, rawNumerator_off i J (fun p hp => (hg p hp).1) hoff,
      map_mul, map_ofNat]
    exact hc
  change (2 : FixedRing v) ∣ timesTheta (dividedCoeff H i J U.nodup_toList hg) j
  have hθ := timesTheta_congr (dividedCoeff H i J U.nodup_toList hg) j
  have hd : (2 : FixedRing v) ∣ dividedCoeff H i J U.nodup_toList hg j := ⟨c, he⟩
  simpa only [sub_add_cancel] using dvd_add hθ hd

end ZInQ.Manuscript.RC.EvenJoin
