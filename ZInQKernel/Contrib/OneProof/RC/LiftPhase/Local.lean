import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz

/-! (O.3) and (O.5), tex 8499–8577, 8903–8923 and 8982–8985.
Cancellation and transport to finite residue groups are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.LiftPhase

open Adelic ThetaJoin LocalWeights
open scoped BigOperators

variable {O : Type} [CommRing O] {ell N m : ℕ}
variable (C : LevelRoots O N) (hn : 2 * m * N * ell ≠ 0)

abbrev Places (m N ell : ℕ) (hn : 2 * m * N * ell ≠ 0) :=
  ↥(exceptionalPlaces m N ell hn)

theorem prime_dvd_rootModulus (q : Adelic.Prime) : q.val ∣ rootModulus q := by
  unfold rootModulus
  split
  · simpa only [pow_two] using dvd_mul_right q.val q.val
  · simpa only [pow_one] using dvd_refl q.val

/-- The quadratic local factor on the same finite residue group as a root
factor at this prime. At an odd prime the modulus is the prime itself. -/
def residueQuadratic (q : Adelic.Prime) : (ZMod (rootModulus q))ˣ →* Oˣ :=
  ((Units.map (Int.castRingHom O)).comp (quadraticChar (ZMod q.val)).toUnitHom).comp
    (ZMod.unitsMap (prime_dvd_rootModulus q))

/-- The residue characters of the actual Schwartz factors, with the case
split of `ThetaJoin.localAlpha` (including the trivial dyadic factor). -/
def residueAlpha (q : Adelic.Prime) : (ZMod (rootModulus q))ˣ →* Oˣ :=
  if q.val = ell then residueQuadratic q
  else if hq : q.val ∣ N then C.alpha q hq
  else if q.val = 2 then 1
  else if q.val ∣ m then residueQuadratic q
  else 1

private theorem reduce_natUnit (q : Adelic.Prime) {n : ℕ} (h : ¬ q.val ∣ n)
    (v : (ZMod (rootModulus q))ˣ) (hv : (v : ZMod (rootModulus q)) = n) :
    (Units.map (PadicInt.toZModPow (if q.val = 2 then 2 else 1)).toMonoidHom)
      (PhaseData.natUnit q n h) = v := by
  apply Units.ext
  change (PadicInt.toZModPow _) (PhaseData.natUnit q n h : ℤ_[q.val]) = _
  rw [PhaseData.natUnit_val, map_natCast]
  exact hv.symm

private theorem residueQuadratic_nat (q : Adelic.Prime) {n : ℕ}
    (u : (ZMod (rootModulus q))ˣ) (hu : (u : ZMod (rootModulus q)) = n) :
    (residueQuadratic (O := O) q u : O) = (jacobiSym (n : ℤ) q.val : O) := by
  have h : (ZMod.unitsMap (prime_dvd_rootModulus q) u : ZMod q.val) = n := by
    rw [ZMod.unitsMap_val, hu, ZMod.cast_natCast (prime_dvd_rootModulus q)]
  change ((↑((quadraticChar (ZMod q.val)).toUnitHom
    (ZMod.unitsMap (prime_dvd_rootModulus q) u)) : ℤ) : O) = _
  rw [MulChar.coe_toUnitHom, h, ← jacobiSym.legendreSym.to_jacobiSym]
  simp [legendreSym]

private theorem legendreUnit_nat (q : Adelic.Prime) {n : ℕ} (h : ¬ q.val ∣ n) :
    (legendreUnit (O := O) q.val (PhaseData.natUnit q n h) : O) =
      (jacobiSym (n : ℤ) q.val : O) := by
  rw [legendreUnit_apply, PhaseData.natUnit_val, map_natCast,
    ← jacobiSym.legendreSym.to_jacobiSym]
  simp [legendreSym]

/-- On an integer unit, the character on the residue group has the value
of the scalar multiplier used in the actual local weight. -/
theorem residueAlpha_nat (q : Adelic.Prime) {n : ℕ} (h : ¬ q.val ∣ n)
    (u : (ZMod (rootModulus q))ˣ) (hu : (u : ZMod (rootModulus q)) = n) :
    (residueAlpha (ell := ell) (m := m) C q u : O) =
      (localAlpha (ell := ell) C m q (PhaseData.natUnit q n h) : O) := by
  classical
  by_cases he : q.val = ell
  · simp only [residueAlpha, localAlpha, ite_eq_left he]
    rw [residueQuadratic_nat q u hu, legendreUnit_nat]
  by_cases hq : q.val ∣ N
  · simp only [residueAlpha, localAlpha, ite_eq_right he, dite_eq_left hq, MonoidHom.comp_apply]
    exact congrArg (fun v => (C.alpha q hq v : O)) (reduce_natUnit q h u hu).symm
  by_cases h₂ : q.val = 2
  · simp only [residueAlpha, localAlpha, ite_eq_right he, dite_eq_right hq, ite_eq_left h₂, MonoidHom.one_apply, Units.val_one]
  · by_cases hm : q.val ∣ m
    · simp only [residueAlpha, localAlpha, ite_eq_right he, dite_eq_right hq, ite_eq_right h₂, ite_eq_left hm,
        residueQuadratic_nat q u hu, legendreUnit_nat q h]
    · simp [residueAlpha, localAlpha, he, hq, h₂, hm]

private theorem dvd_product_of_extraction (q : Adelic.Prime) (hq : q.val ∣ m) :
    q.val ∣ 2 * m * N * ell :=
  dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hq 2) N) ell

private def rootValue {n : ℕ} (h : (schwartzPhase C m hn).Away n)
    (q : Places m N ell hn) : O :=
  if hq : q.val.val ∣ N then
    (C.alpha q.val hq
      (Units.map (PadicInt.toZModPow (if q.val.val = 2 then 2 else 1)).toMonoidHom
        (PhaseData.natUnit q.val n (h q.val q.prop))) : O)
  else 1

/-- The manuscript phase, by construction: on the old unit domain take
the root characters at the elliptic conductor times the detecting sign.
Off that domain use the stage's zero extension, including at primes of
the extraction even though their factors have cancelled on units. -/
def etaSource (n : ℕ) : O :=
  open Classical in
  if h : (schwartzPhase C m hn).Away n then
    (∏ q : Places m N ell hn, rootValue C hn h q) * (jacobiSym (n : ℤ) ell : O)
  else 0

private theorem extraction_prod {n : ℕ} (h3 : m % 4 = 3) (hm : Squarefree m)
    (hodd : Odd n) :
    (∏ q : Places m N ell hn,
      if q.val.val ∣ m then (jacobiSym (n : ℤ) q.val.val : O) else 1) =
      (jacobiSym (-(m : ℤ)) n : O) := by
  classical
  let emb : Adelic.Prime ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hS : ((exceptionalPlaces m N ell hn).filter fun q => q.val ∣ m).map emb =
      m.primeFactors := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Nat.mem_primeFactors, emb,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨q, ⟨_, hq⟩, rfl⟩
      exact ⟨q.prop, hq, by omega⟩
    · rintro ⟨hp, hd, _⟩
      let q : Adelic.Prime := ⟨p, hp⟩
      exact ⟨q, ⟨(mem_exceptionalPlaces m N ell hn q).mpr
        (dvd_product_of_extraction q hd), hd⟩, rfl⟩
  rw [Finset.prod_coe_sort (exceptionalPlaces m N ell hn)
      (fun q => if q.val ∣ m then (jacobiSym (n : ℤ) q.val : O) else 1),
    ← Finset.prod_filter, negativeDiscriminant_unit_character m n h3 hm hodd,
    Int.cast_prod, ← hS, Finset.prod_map]
  rfl

private theorem genus_sq {n : ℕ} (h : (schwartzPhase C m hn).Away n) :
    (jacobiSym (-(m : ℤ)) n : O) ^ 2 = 1 := by
  have hc : m.Coprime n := Nat.coprime_of_dvd fun p hp hd =>
    h ⟨p, hp⟩ ((mem_exceptionalPlaces m N ell hn _).mpr
      (dvd_product_of_extraction ⟨p, hp⟩ hd))
  have hg : (-(m : ℤ)).gcd (n : ℤ) = 1 := by
    simpa only [Int.gcd_eq_natAbs, Int.natAbs_neg, Int.natAbs_natCast] using hc
  rcases jacobiSym.eq_one_or_neg_one hg with he | he <;> simp [he]

/-- The manuscript product agrees in characteristic zero with the full
scaling product times the genus twist, on every natural number. -/
theorem etaSource_eq [Fact ell.Prime] (h3 : m % 4 = 3) (hm : Squarefree m)
    (hcop : N.Coprime ell) (hdis : ∀ q : Adelic.Prime, q.val ∣ m →
      q.val ≠ ell ∧ ¬ q.val ∣ N ∧ q.val ≠ 2) (n : ℕ) :
    etaSource C hn n = (schwartzPhase C m hn).eta m n := by
  classical
  by_cases h : (schwartzPhase C m hn).Away n
  · have h2 := h ⟨2, Nat.prime_two⟩ ((mem_exceptionalPlaces m N ell hn _).mpr
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right 2 m) N) ell))
    change ¬ 2 ∣ n at h2
    have ho : Odd n := Nat.odd_iff.mpr (by rw [Nat.dvd_iff_mod_eq_zero] at h2; omega)
    have he : ¬ ell ∣ N := (Fact.out : ell.Prime).coprime_iff_not_dvd.mp hcop.symm
    let detector : Adelic.Prime := ⟨ell, Fact.out⟩
    have hdet : detector ∈ exceptionalPlaces m N ell hn :=
      (mem_exceptionalPlaces m N ell hn _).mpr (dvd_mul_left _ _)
    let detect (q : Adelic.Prime) : O :=
      if q = detector then (jacobiSym (n : ℤ) ell : O) else 1
    let extract (q : Adelic.Prime) : O :=
      if q.val ∣ m then (jacobiSym (n : ℤ) q.val : O) else 1
    have hs : ((schwartzPhase C m hn).scalar n h : O) =
        (∏ q : Places m N ell hn, rootValue C hn h q) *
          (∏ q ∈ exceptionalPlaces m N ell hn, detect q) *
          (∏ q : Places m N ell hn, extract q.val) := by
      rw [← Finset.prod_coe_sort (exceptionalPlaces m N ell hn) detect,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      simp only [PhaseData.scalar, Units.coe_prod]
      change (∏ q : Places m N ell hn, _) = _
      apply Finset.prod_congr rfl
      intro q _
      change (localAlpha (ell := ell) C m q.val (PhaseData.natUnit q.val n (h q.val q.prop)) : O) =
        rootValue C hn h q * detect q.val * extract q.val
      by_cases hq : q.val.val = ell
      · have h' : q.val = detector := Subtype.ext hq
        have hnN : ¬ q.val.val ∣ N := by simpa [hq] using he
        have hnm : ¬ q.val.val ∣ m := fun hd => (hdis q.val hd).1 hq
        simp only [localAlpha, ite_eq_left hq, legendreUnit_nat, rootValue, dite_eq_right hnN,
          detect, ite_eq_left h', extract, ite_eq_right hnm, one_mul, mul_one]
        exact congrArg (fun p : ℕ => (jacobiSym (n : ℤ) p : O)) hq
      · have h' : q.val ≠ detector := fun e => hq (congrArg Subtype.val e)
        by_cases hqN : q.val.val ∣ N
        · have hnm : ¬ q.val.val ∣ m := fun hd => (hdis q.val hd).2.1 hqN
          simp only [localAlpha, ite_eq_right hq, dite_eq_left hqN, MonoidHom.comp_apply,
            rootValue, detect, ite_eq_right h', extract, ite_eq_right hnm, mul_one]
          rfl
        · by_cases hqm : q.val.val ∣ m
          · have hq2 := (hdis q.val hqm).2.2
            simp [localAlpha, hq, hqN, hqm, hq2, rootValue, detect, h', extract, legendreUnit_nat]
          · by_cases hq2 : q.val.val = 2
            · simp only [localAlpha, ite_eq_right hq, dite_eq_right hqN, ite_eq_left hq2,
                rootValue, detect, ite_eq_right h', extract, ite_eq_right hqm,
                MonoidHom.one_apply, Units.val_one, mul_one]
            · simp [localAlpha, hq, hqN, hqm, hq2, rootValue, detect, h', extract]
    simp only [etaSource, PhaseData.eta, PhaseData.phase, h, dite_eq_left, ite_eq_left]
    rw [hs, show (∏ q ∈ exceptionalPlaces m N ell hn, detect q) =
        (jacobiSym (n : ℤ) ell : O) from
      Finset.prod_ite_eq_of_mem' _ detector (fun _ => (jacobiSym (n : ℤ) ell : O)) hdet]
    change _ = _ * _ * (∏ q : Places m N ell hn,
      if q.val.val ∣ m then (jacobiSym (n : ℤ) q.val.val : O) else 1) * _
    rw [extraction_prod hn h3 hm ho, mul_assoc (_ * _), ← pow_two, genus_sq C hn h, mul_one]
  · simp [etaSource, PhaseData.eta, h]

/-- The full (O.5) value has two-power order on the old unit domain. -/
theorem eta_order_of_away {n : ℕ} (h : (schwartzPhase C m hn).Away n) :
    (schwartzPhase C m hn).eta m n ^ (2 ^ ((schwartzPhase C m hn).exponent + 1) : ℕ) =
      1 := by
  classical
  let A := schwartzPhase C m hn
  have hs : (A.scalar n h : O) ^ (2 ^ A.exponent : ℕ) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val (A.scalar_order h)
  change A.eta m n ^ (2 ^ (A.exponent + 1) : ℕ) = 1
  rw [PhaseData.eta, ite_eq_left h, PhaseData.phase, dite_eq_left h, mul_pow,
    pow_succ (2 : ℕ), pow_mul, hs, one_pow, one_mul, mul_comm (2 ^ A.exponent) 2,
    pow_mul, genus_sq C hn h, one_pow]


end ZInQ.Manuscript.RC.LiftPhase
