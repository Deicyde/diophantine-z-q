import ZInQKernel.Contrib.OneProof.RC.O12Theta.Expansions
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Source
import ZInQKernel.Contrib.OneProof.RC.Odd.Traces

/-! The first-shell comparison for the odd source using only the recurrence
modulo the stage precision (tex 9905–9918). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open ThetaCoeff ZInQ.Manuscript.RC.Odd
open scoped Classical

variable {O K : Type} [CommRing O] [IsDomain O] [CharZero O] [Field K] [CharZero K]
  [Algebra O K]
variable {M W R : ℕ} {S : AppF.ThetaStage (StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable (E : Lift S) (D : Divisions E δ W R adm)

private theorem tl_stage (J : List ℕ) (n : ℕ) :
    stageReduction O M (TL E.η J E.aθ n) = TL S.η J S.aθ n := by
  induction J generalizing n with
  | nil => exact E.aθ_reduce n
  | cons p J ih =>
    simp only [TL_cons, Odd.Top, map_sub, map_mul, E.phase, ih, ← divCoeff_map]

/-- At the first omission shell the actual divided coefficient has the
manuscript's `η(p) C_p(vr)` multiplier modulo integer two. This applies to
the lifted forms without an exact characteristic-zero Brandt eigenrelation. -/
theorem omission_coeff_mod_two (hinj : Function.Injective (algebraMap O K))
    {U : Finset ℕ} {p r : ℕ} (hu : Admissible S W U) (hpU : p ∈ U)
    (hr : r.Prime) (hrU : r ∉ U)
    (hv : Admissible S W (U.erase p)) :
    letI : Fact p.Prime := ⟨S.good_prime p (hu.2 p hpU)⟩
    let κ := ratio p (S.good_prime p (hu.2 p hpU)) *
      legendreSym p (-(((∏ s ∈ U.erase p, s) * r : ℕ) : ℤ))
    (2 : O) ∣ E.HU D hu (p * r) - E.η p * (Cp (S.ap p) κ : O) * E.HU D hv r := by
  let V := U.erase p
  let J := V.toList
  let hp := S.good_prime p (hu.2 p hpU)
  letI : Fact p.Prime := ⟨hp⟩
  let κ := ratio p hp * legendreSym p (-(((∏ s ∈ V, s) * r : ℕ) : ℤ))
  let c := Cp (S.ap p) κ
  change (2 : O) ∣ E.HU D hu (p * r) - E.η p * (c : O) * E.HU D hv r
  have hn (q : ℕ) (hq : q ∈ U) : ¬ q ∣ r := fun h =>
    hrU ((Nat.prime_dvd_prime_iff_eq (S.good_prime q (hu.2 q hq)) hr).mp h ▸ hq)
  have hJ (q : ℕ) (hq : q ∈ J) : q ∈ V := Finset.mem_toList.mp hq
  have hJV : J.toFinset = V := Finset.toList_toFinset V
  have hpJ : p ∉ J := fun h => Finset.notMem_erase p U (hJ p h)
  have hJU : (p :: J).toFinset = U := by
    rw [List.toFinset_cons, hJV, Finset.insert_erase hpU]
  have hprod : ¬ p ∣ J.prod := by
    intro h
    obtain ⟨q, hq, hd⟩ := (Prime.dvd_prod_iff hp.prime).mp h
    exact hpJ ((Nat.prime_dvd_prime_iff_eq hp (S.good_prime q (hv.2 q (hJ q hq)))).mp hd ▸ hq)
  have hκ : κ = 1 ∨ κ = -1 := by
    apply legendreSym_neg_eq_one_or _ (ratio_sign hp)
    rw [← Finset.prod_toList V]
    exact fun h => (hp.dvd_mul.mp h).elim hprod (hn p hpU)
  have hCp : S.ap p - κ - 1 = 2 * c := by
    obtain ⟨d, hd⟩ := (D.stage.2.ap_mod p (hu.2 p hpU)).dvd
    obtain ⟨j, hj⟩ := D.stage.2.odd p (hu.2 p hpU)
    change S.ap p - κ - 1 = 2 * Cp (S.ap p) κ
    rcases hκ with h | h <;> rw [h] <;> unfold Cp <;> omega
  have hTL := TL_omission S.η S.aθ (S.recAt (hu.2 p hpU)) J
    (fun q hq => S.good_prime q (hv.2 q (hJ q hq))) V.nodup_toList hpJ (hn p hpU)
    (fun q hq => hn q (Finset.mem_of_mem_erase (hJ q hq)))
  rw [show J.prod = ∏ s ∈ V, s from Finset.prod_toList V] at hTL
  change TL S.η (p :: J) S.aθ (p * r) =
    S.η p * ((S.ap p - κ - 1 : ℤ) : StageRing O M) * S.aθ ((∏ s ∈ V, s) * r) at hTL
  rw [hCp] at hTL
  let x := TL E.η (p :: J) E.aθ (p * r)
  let y := E.η p * ((2 * c : ℤ) : O) * E.aθ ((∏ s ∈ V, s) * r)
  have hxy : stageReduction O M x = stageReduction O M y := by
    simpa only [x, y, tl_stage, map_mul, map_intCast, E.phase, E.aθ_reduce] using hTL
  have hOff : ¬ oddPart (p * r) ⊆ U := by
    rw [oddPart_mul_prime hp hr.ne_zero (hn p hpU)]
    exact fun h => theta_index_ne_fresh hr hrU (fun s hs => h (Finset.mem_insert_of_mem hs))
  have hrV : r ∉ V := fun h => hrU (Finset.mem_of_mem_erase h)
  have hUeq := hu_off_unary (K := K) E D hu (p :: J) (List.nodup_cons.mpr ⟨hpJ, V.nodup_toList⟩) hJU hOff
  have hVeq := hu_off_unary (K := K) E D hv J V.nodup_toList hJV (theta_index_ne_fresh hr hrV)
  rw [TL_fresh E.η E.aθ J (fun q hq => S.good_prime q (hv.2 q (hJ q hq)))
    V.nodup_toList (fun q hq => hn q (Finset.mem_of_mem_erase (hJ q hq))),
    show J.prod = ∏ s ∈ V, s from Finset.prod_toList V] at hVeq
  have hprec := D.stage.precision D.precision hu.1
  have hs : (2 : K) ^ (-(δ + (U.card : ℤ) + 1)) * 2 =
      (2 : K) ^ (-(δ + (V.card : ℤ) + 1)) := by
    have : V.card + 1 = U.card := Finset.card_erase_add_one hpU
    have he : -(δ + (U.card : ℤ) + 1) + 1 = -(δ + (V.card : ℤ) + 1) := by omega
    calc
      _ = (2 : K) ^ (-(δ + (U.card : ℤ) + 1)) * (2 : K) ^ (1 : ℤ) := by rw [zpow_one]
      _ = _ := by rw [← zpow_add₀ (by norm_num : (2 : K) ≠ 0), he]
  apply normalized_congr hinj (by omega : δ + (U.card : ℤ) + 1 < (M : ℤ)) hxy hUeq
  rw [map_mul, map_mul, map_intCast, hVeq]
  simp only [y, map_mul, map_intCast, Int.cast_mul, Int.cast_ofNat, map_ofNat]
  rw [← hs]
  ring


end ZInQ.Manuscript.RC.O12Theta
