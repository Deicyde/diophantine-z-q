import ZInQKernel.Contrib.TauCeti.GroupTheory.FiniteAbelian.RankTwo
import ZInQKernel.Contrib.TauCeti.Algebra.Module.Torsion.Decomposition
import ZInQKernel.Contrib.TauCeti.Algebra.Group.Equiv.Pi
import ZInQKernel.Contrib.TauCeti.Data.ZMod.Torsion
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Data.ZMod.QuotientRing

/-!
# t5-torsion, part 1: the group-theoretic glue (rank `r` structure from torsion counts)

Generalizes Tau Ceti's rank-two lemmas (vendored in `ZInQKernel/Contrib/TauCeti/`, Apache-2.0,
`GroupTheory/FiniteAbelian/RankTwo.lean` and
`AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Torsion/Structure.lean`) from rank `2` to rank
`r`; the proofs follow theirs.
-/

namespace T5Torsion

open scoped DirectSum

/-- **Rank-`r` prime-power characterisation.** An abelian group killed by `p ^ k`, with
order `p ^ (r * k)` and `p ^ r` elements killed by `p`, is `(ZMod (p ^ k))^r`. -/
theorem nonempty_addEquiv_pi_zmod_primePow {G : Type*} [AddCommGroup G] {p k r : ℕ}
    (hp : p.Prime)
    (hpow : ∀ x : G, p ^ k • x = 0)
    (hcard : Nat.card G = p ^ (r * k))
    (hcardp : Nat.card (AddSubgroup.torsionBy G (p : ℤ)) = p ^ r) :
    Nonempty (G ≃+ (Fin r → ZMod (p ^ k))) := by
  classical
  have : Finite G := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ hp.ne_zero)
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let E : G ≃+ (∀ i : ι, ZMod (n i)) := e.trans (DirectSum.addEquivProd _)
  have hn_dvd (i : ι) : n i ∣ p ^ k := by
    let x : (j : ι) → ZMod (n j) := Function.update 0 i 1
    have hx : p ^ k • x = 0 := by
      simpa using congrArg E (hpow (E.symm x))
    have hxi := congrFun hx i
    have hxi' : ((p ^ k : ℕ) : ZMod (n i)) = 0 := by
      simpa [x, nsmul_eq_mul] using hxi
    exact (ZMod.natCast_eq_zero_iff (p ^ k) (n i)).mp hxi'
  choose a ha_le ha using fun i ↦ (Nat.dvd_prime_pow hp).mp (hn_dvd i)
  have ha_pos (i : ι) : 0 < a i := by
    rw [Nat.pos_iff_ne_zero]
    intro hai
    simpa [ha i, hai] using hn i
  have hcard_prod : ∏ i, n i = p ^ (r * k) := by
    rw [← hcard, Nat.card_congr E.toEquiv, Nat.card_pi]
    simp only [Nat.card_zmod]
  have hcard_torsion_pi :
      Nat.card (AddSubgroup.torsionBy (∀ i : ι, ZMod (n i)) (p : ℤ)) = p ^ Fintype.card ι := by
    rw [Nat.card_congr (TauCeti.AddSubgroup.torsionByPiEquiv (fun i ↦ ZMod (n i)) (p : ℤ)).toEquiv,
      Nat.card_pi]
    let : NeZero p := ⟨hp.ne_zero⟩
    calc
      ∏ i, Nat.card (AddSubgroup.torsionBy (ZMod (n i)) (p : ℤ)) = ∏ _i : ι, p := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [ha i]
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ha_pos i).ne'
        rw [hj]
        simpa only [Nat.card_zmod] using
          Nat.card_congr (TauCeti.zmodTorsionByEquiv p j).symm.toEquiv
      _ = p ^ Fintype.card ι := by simp
  have hιcard : Fintype.card ι = r := by
    have ht : p ^ Fintype.card ι = p ^ r := by
      rw [← hcard_torsion_pi, ← hcardp]
      exact Nat.card_congr (AddEquiv.torsionByCongr E (p : ℤ)).symm.toEquiv
    exact Nat.pow_right_injective hp.two_le ht
  have hsum : ∑ i, a i = r * k := by
    apply Nat.pow_right_injective hp.two_le
    dsimp only
    rw [← Finset.prod_pow_eq_pow_sum Finset.univ a p]
    simp only [← ha, hcard_prod]
  have ha_eq (i : ι) : a i = k := by
    apply le_antisymm (ha_le i)
    by_contra hki
    have hai : a i < k := Nat.lt_of_not_ge hki
    have hlt : ∑ j, a j < ∑ _j : ι, k :=
      Finset.sum_lt_sum (fun j _ ↦ ha_le j) ⟨i, Finset.mem_univ i, hai⟩
    simp only [Finset.sum_const, Finset.card_univ, hιcard, smul_eq_mul] at hlt
    omega
  let rι : ι ≃ Fin r := Fintype.equivFinOfCardEq hιcard
  exact ⟨E |>.trans (AddEquiv.piCongrRight fun i ↦
      (ZMod.ringEquivCongr (by rw [ha i, ha_eq i])).toAddEquiv) |>.trans
      (AddEquiv.arrowCongr rι (AddEquiv.refl (ZMod (p ^ k))))⟩

open scoped Classical in
/-- A primary component of `A[N]` is `(ZMod q)^r`, given the counts `#A[m] = m^r` for `m ∣ N`. -/
noncomputable def primePowerComponentEquiv {A : Type*} [AddCommGroup A] (N r : ℕ) [NeZero N]
    (hcount : ∀ m : ℕ, m ∣ N → Nat.card (AddSubgroup.torsionBy A (m : ℤ)) = m ^ r)
    (p : N.primeFactors) :
    let q := (p : ℕ) ^ N.factorization p
    Submodule.torsionBy ℤ (AddSubgroup.torsionBy A (N : ℤ)) (q : ℤ) ≃+
      (Fin r → ZMod q) := by
  let G := AddSubgroup.torsionBy A (N : ℤ)
  let q := (p : ℕ) ^ N.factorization p
  have hN0 : N ≠ 0 := NeZero.ne N
  have hq_dvd : q ∣ N :=
    (Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hN0 |>.2 le_rfl
  have hp_dvd_q : (p : ℕ) ∣ q := by
    apply dvd_pow_self
    exact (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors p.2) hN0
      (Nat.dvd_of_mem_primeFactors p.2)).ne'
  let e : Submodule.torsionBy ℤ G (q : ℤ) ≃+
      AddSubgroup.torsionBy A (q : ℤ) :=
        TauCeti.AddSubgroup.torsionByTorsionByEquiv (by exact_mod_cast hq_dvd)
  have hpow (x : Submodule.torsionBy ℤ G (q : ℤ)) : q • x = 0 :=
    AddSubgroup.torsionBy.nsmul x
  have hcardq : Nat.card (Submodule.torsionBy ℤ G (q : ℤ)) = q ^ r := by
    rw [Nat.card_congr e.toEquiv]
    exact hcount q hq_dvd
  have hcardp : Nat.card
      (AddSubgroup.torsionBy (Submodule.torsionBy ℤ G (q : ℤ)) (p : ℤ)) = p ^ r := by
    let ep := (AddEquiv.torsionByCongr e p).trans
      (TauCeti.AddSubgroup.torsionByTorsionByEquiv (by exact_mod_cast hp_dvd_q))
    rw [Nat.card_congr ep.toEquiv]
    exact hcount p (dvd_trans hp_dvd_q hq_dvd)
  have hcardq' : Nat.card (Submodule.torsionBy ℤ G (q : ℤ)) =
      p ^ (r * N.factorization p) := by
    rw [hcardq, pow_mul, mul_comm]
    dsimp only [q]
    rw [← pow_mul, ← pow_mul, mul_comm]
  exact (nonempty_addEquiv_pi_zmod_primePow
    (Nat.prime_of_mem_primeFactors p.2) hpow hcardq' hcardp).some

/-- **Structure from counts.** If `#A[m] = m^r` for every `m ∣ N` (`N ≥ 1`), then
`A[N] ≃+ (ZMod N)^r`. -/
theorem nonempty_torsionBy_addEquiv_pi {A : Type*} [AddCommGroup A] (N r : ℕ) (hN0 : N ≠ 0)
    (hcount : ∀ m : ℕ, m ∣ N → Nat.card (AddSubgroup.torsionBy A (m : ℤ)) = m ^ r) :
    Nonempty (AddSubgroup.torsionBy A (N : ℤ) ≃+ (Fin r → ZMod N)) := by
  classical
  haveI : NeZero N := ⟨hN0⟩
  let G := AddSubgroup.torsionBy A (N : ℤ)
  let q : ℕ → ℕ := fun p ↦ p ^ N.factorization p
  let componentEquiv (p : N.primeFactors) :
      Submodule.torsionBy ℤ G (q p : ℤ) ≃+ (Fin r → ZMod (q p)) :=
    primePowerComponentEquiv N r hcount p
  have hinternal : DirectSum.IsInternal fun p : N.primeFactors ↦
      Submodule.torsionBy ℤ G (q p : ℤ) :=
    TauCeti.AddSubgroup.torsionBy_primeFactors_isInternal N hN0
  letI := hinternal.chooseDecomposition
  let primary : G ≃+ (∀ p : N.primeFactors, Fin r → ZMod (q p)) :=
    (DirectSum.decomposeAddEquiv fun p : N.primeFactors ↦
      Submodule.torsionBy ℤ G (q p : ℤ)).trans <|
      (DFinsupp.mapRange.addEquiv componentEquiv).trans (DirectSum.addEquivProd _)
  let comm : (∀ p : N.primeFactors, Fin r → ZMod (q p)) ≃+
      (Fin r → ∀ p : N.primeFactors, ZMod (q p)) :=
    { Equiv.piComm _ with map_add' := fun _ _ ↦ rfl }
  let crt : (∀ p : N.primeFactors, ZMod (q p)) ≃+ ZMod N :=
    (ZMod.equivPi (n := N) hN0).symm.toAddEquiv
  exact ⟨primary.trans (comm.trans (AddEquiv.piCongrRight fun _ ↦ crt))⟩

end T5Torsion

#print axioms T5Torsion.nonempty_torsionBy_addEquiv_pi
