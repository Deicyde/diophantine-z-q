import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Realize
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Rules

/-! Stationary realization, retaining the prime sets and total types at every
address. The construction follows tex 2151–2174, 2222–2238 and 2318–2322,
using the same binary family as `EvenUpper.realized_cubes`. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenUpperCubes

open Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open ZInQ.Contrib.CloudB3RC53.EvenUpper

/-- The realized cube keeps the old primes, avoids the full support, and
reads the same symbol at the unchanged total type. -/
theorem realized_cubes_with_total {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
    (T : TypeData L ε) (a : ℕ → ℚ_[2]) (δ : ℤ) (F : ℕ → Prop)
    (hswap : ∀ B, FixedUFactorization T (coeffReading a δ F) B)
    (hA : CoefficientRules ε (symb T (coeffReading a δ F)))
    (htyp1 : ∀ q : ℕ, q.Prime → (q : ZMod T.m) = 1 → T.typ q = 0)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {N₀ : ℕ} (hN₀ : 0 < N₀) (d : ℤ) (hd : d < 0) (hsq : Squarefree d)
    (havoid : ∀ p ∈ S, ¬ (p : ℤ) ∣ d)
    (hgood : ∀ p ∈ d.natAbs.primeFactors, T.Good p ∧ Nat.Coprime p N₀)
    (hpart : IsPartitionable ε (symb T (coeffReading a δ F))
      (primeConfig d.natAbs.primeFactors T.typ))
    (b : ℕ) (hb : 1 ≤ b) :
    ∃ (fam : Even.BinaryFamily N₀) (Q : (Fin fam.b → ZMod 2) → ℕ),
      fam.b = b ∧ fam.h 0 = d ∧
      (∀ x, fam.h x = d * (Q x : ℤ) ∧
        (Q x : ZMod (T.m * (8 * N₀ * ∏ p ∈ S, p))) = 1) ∧
      (∀ x, ∀ p ∈ d.natAbs.primeFactors, (p : ℤ) ∣ fam.h x) ∧
      (∀ x, (primeConfig (fam.h x).natAbs.primeFactors T.typ).total =
        (primeConfig d.natAbs.primeFactors T.typ).total) ∧
      ∀ x, x ≠ 0 → fam.h x < 0 ∧ (∀ p ∈ S, ¬ (p : ℤ) ∣ fam.h x) ∧
        symb T (coeffReading a δ F) (primeConfig (fam.h x).natAbs.primeFactors T.typ) = 1 := by
  classical
  let P := d.natAbs.primeFactors
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hn0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
  let Γ := primeConfig P T.typ
  have hf0 : IsReal T Γ id :=
    ⟨Set.injOn_id _, fun v hv => ⟨(hgood v hv).1, rfl⟩, fun v _ w _ _ => rfl⟩
  have hΓ : Γ.Compatible ε := compatible_of_real T hf0
  obtain ⟨Γ', act'', hΓ', hext, hact, hnew, hunit⟩ :=
    one_symbol_address hA Γ hΓ hpart.1 (partitionable_terminalNonzero hA hΓ hpart) b hb
  let K := 8 * N₀ * ∏ p ∈ S, p
  have hK : 0 < K := Nat.mul_pos (by omega) (Finset.prod_pos fun p hp => (hS p hp).pos)
  have hcop8 : ∀ p ∈ P, Nat.Coprime p K := by
    intro p hp
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ (hgood p hp).2) ?_
    swap
    · refine Nat.Coprime.prod_right fun q hq => (Nat.coprime_primes (hgood p hp).1.1 (hS q hq)).mpr ?_
      rintro rfl
      exact havoid p hq (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
    have h2 : Nat.Coprime p 2 :=
      (Nat.coprime_primes (hgood p hp).1.1 Nat.prime_two).mpr (hgood p hp).1.ne_two
    simpa using Nat.Coprime.pow_right 3 h2
  obtain ⟨f, hf, hfP, hfN⟩ := exists_real_extension T K hK htyp1 P
    (fun p hp => ⟨(hgood p hp).1, hcop8 p hp⟩) Γ' hΓ' hext (fun v hv hvP => (hnew v hv hvP).1)
  set Vn := Γ'.V.filter (· ∉ P) with hVn
  have hVact : ∀ v ∈ Vn, ∃ w, act'' v = some w := fun v hv => by
    obtain ⟨hv, hvP⟩ := Finset.mem_filter.mp hv
    obtain ⟨-, w, -, hw⟩ := hnew v hv hvP
    exact ⟨w, hw⟩
  have hVprime : ∀ v ∈ Vn, (f v).Prime ∧ f v ∉ P := fun v hv => by
    obtain ⟨hv, hvP⟩ := Finset.mem_filter.mp hv
    exact ⟨(hf.2.1 v hv).1.1, (hfN v hv hvP).1⟩
  have hVmod : ∀ v ∈ Vn, ((f v : ℕ) : ZMod (T.m * K)) = 1 := fun v hv =>
    (hfN v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2).2
  have hinjVn : Set.InjOn f Vn := fun v hv w hw h =>
    hf.1 (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1 h
  set Q := cubeQ act'' Vn f with hQdef
  have hQ0 : Q 0 = 1 := cubeQ_zero act'' Vn f hVact
  have hQfull : ∀ x, ((Q x : ℕ) : ZMod (T.m * K)) = 1 := cubeQ_mod act'' Vn f _ hVmod
  have hQmod (x) (n : ℕ) (hn : n ∣ T.m * K) : ((Q x : ℕ) : ZMod n) = 1 := by
    simpa only [map_natCast, map_one] using congrArg (ZMod.castHom hn (ZMod n)) (hQfull x)
  have h8N : 8 * N₀ ∣ T.m * K :=
    (dvd_mul_right _ (∏ p ∈ S, p)).trans (dvd_mul_left K T.m)
  have hQodd : ∀ x, Odd (Q x) := by
    intro x
    have h := hQmod x _ h8N
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
    have h2 : Q x ≡ 1 [MOD 2] := Nat.ModEq.of_dvd ⟨4 * N₀, by ring⟩ h
    exact Nat.odd_iff.mpr h2
  have hQpos : ∀ x, (0 : ℤ) < Q x := fun x => by exact_mod_cast (hQodd x).pos
  have hdodd : Odd d := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    have h2P : 2 ∈ P := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, Int.ofNat_dvd_left.mp h2, hn0⟩
    exact (hgood 2 h2P).1.ne_two rfl
  let fam : ZInQ.Manuscript.RC.Even.BinaryFamily N₀ :=
    { b := b
      h := fun x => d * (Q x : ℤ)
      odd := fun x => Int.odd_mul.mpr ⟨hdodd, (hQodd x).natCast⟩
      sqfree := fun x => by
        rw [← Int.squarefree_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.squarefree_mul_iff.mpr ⟨coprime_cubeQ act'' Vn f _ hn0 hVprime x,
          Int.squarefree_natAbs.mpr hsq, cubeQ_squarefree act'' Vn f
            (fun v hv => (hVprime v hv).1) hinjVn x⟩
      sign := fun x => by
        simp only [hQ0, Nat.cast_one, mul_one]
        have := hQpos x
        constructor
        · intro h; by_contra hd; nlinarith [not_lt.mp hd]
        · intro h; positivity
      local_sq := fun x p hp => by
        have := Fact.mk p.2
        have hs := ZInQ.Manuscript.RC.Nonvanishing.isSquareAt_mul
          (ZInQ.Manuscript.RC.Nonvanishing.isSquareAt_sq (d : ℚ))
          (isSquareAt_of_mod (Q x) (hQmod x _ h8N) p.2 hp) (Fact.mk p.2)
        have he : (((d * (Q x : ℤ) * (d * (Q 0 : ℤ)) : ℤ) : ℚ_[(p : ℕ)])) =
            ((((d : ℚ) ^ 2 * (Q x : ℚ) : ℚ)) : ℚ_[(p : ℕ)]) := by
          rw [hQ0]; push_cast; ring
        rw [he]; exact hs
      hom := fun x y => by
        obtain ⟨r, hr⟩ := cubeQ_hom act'' Vn f hVact x y
        have hr' : ((Q (x + y) : ℕ) : ℤ) * Q x * Q y = (r : ℤ) * r := by exact_mod_cast hr
        refine ⟨d * d * r, ?_⟩
        rw [hQ0]; push_cast
        linear_combination d ^ 4 * hr' }
  have hzero : fam.h 0 = d := by simp [fam, hQ0]
  have hVxP (x : Fin b → ZMod 2) : (Γ'.at act'' x).V.filter (· ∈ P) = P := by
    ext v
    simp only [Config.at, Finset.mem_filter]
    constructor
    · rintro ⟨-, hv⟩; exact hv
    · intro hv
      exact ⟨⟨hext.1 hv, by simp [present, hact v hv]⟩, hv⟩
  have hVxN (x : Fin b → ZMod 2) :
      (Γ'.at act'' x).V.filter (· ∉ P) = Vn.filter (present act'' x) := by
    ext v
    simp only [Config.at, hVn, Finset.mem_filter]
    tauto
  have hcop (x : Fin b → ZMod 2) (p : ℕ) (hp : p ∈ S) : ¬ p ∣ Q x := by
    have hdiv : p ∣ T.m * K :=
      (Finset.dvd_prod_of_mem id hp).trans (dvd_mul_left _ _)
      |>.trans (dvd_mul_left K T.m)
    have h := hQmod x p hdiv
    intro hpd
    let : Fact p.Prime := ⟨hS p hp⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hpd] at h
    exact zero_ne_one h
  have himage (x : Fin b → ZMod 2) :
      ∏ p ∈ (Γ'.at act'' x).V.image f, p = (fam.h x).natAbs := by
    have hfx := isReal_at T hf act'' x
    rw [Finset.prod_image (fun v hv w hw h => hfx.1 hv hw h),
      ← Finset.prod_filter_mul_prod_filter_not (Γ'.at act'' x).V (· ∈ P),
      hVxP, hVxN, Finset.prod_congr rfl (fun v hv => hfP v hv), ← cubeQ_eq_prod_filter,
      Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hsq)]
    simp [fam, Int.natAbs_mul, hQdef]
  have hgoodW (x : Fin b → ZMod 2) (p : ℕ) (hp : p ∈ (Γ'.at act'' x).V.image f) : T.Good p := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact ((isReal_at T hf act'' x).2.1 v hv).1
  have hprimes (x : Fin b → ZMod 2) :
      (fam.h x).natAbs.primeFactors = (Γ'.at act'' x).V.image f := by
    rw [← himage, Nat.primeFactors_prod fun p hp => (hgoodW x p hp).1]
  refine ⟨fam, Q, rfl, hzero, fun x => ⟨rfl, hQfull x⟩, ?_, ?_, ?_⟩
  · intro x p hp
    exact dvd_mul_of_dvd_left (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)) _
  · intro x
    rw [hprimes]
    change (∑ p ∈ (Γ'.at act'' x).V.image f, T.typ p) = ∑ p ∈ P, T.typ p
    have hfx := isReal_at T hf act'' x
    rw [Finset.sum_image (fun v hv w hw h => hfx.1 hv hw h),
      ← Finset.sum_filter_add_sum_filter_not (Γ'.at act'' x).V (· ∈ P),
      hVxP, hVxN, Finset.sum_congr rfl (fun v hv => by rw [hfP v hv])]
    have hz : ∑ v ∈ Vn.filter (present act'' x), T.typ (f v) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      obtain ⟨hv', hvP⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hv).1
      exact (hf.2.1 v hv').2.trans (hnew v hv' hvP).1
    rw [hz, add_zero]
  · intro x hx
    refine ⟨(show d * (Q x : ℤ) < 0 from mul_neg_of_neg_of_pos hd (hQpos x)),
      fun p hp hpd => ?_, ?_⟩
    · have hpd' : p ∣ d.natAbs * Q x := by
        simpa only [fam, Int.natAbs_mul, Int.natAbs_natCast] using Int.ofNat_dvd_left.mp hpd
      rcases (hS p hp).dvd_mul.mp hpd' with h | h
      · exact havoid p hp (Int.natCast_dvd.mpr h)
      · exact hcop x p hp h
    · have h1 : symb T (coeffReading a δ F) (Γ'.at act'' x) = 1 := by simpa using hunit x hx 0
      rw [symb_eq T _ (hswap _) (Config.at_compatible hΓ' act'' x) le_rfl
        (isReal_at T hf act'' x)] at h1
      rw [hprimes, symb_primeConfig T a δ F (hswap _) _ (hgoodW x) le_rfl]
      exact h1

end ZInQ.Manuscript.RC.EvenUpperCubes
