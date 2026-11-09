import ZInQKernel.RouteK.Assembly.Realize

/-!
# cr3-check: evaluating `Σ(𝒞_d)` on real numbers

`ZInQ.RouteK.natConfig d hd` is noncomputable: its bits are `legBit q p`, defined by a classical
`if IsSquare ((p : ℤ) : ZMod q)`. We define a computable mirror `natConfigC` whose bits come from
Euler's criterion (`Nat.powMod`), prove that it has *the same solution set* as `natConfig`
(`natConfig_sols_eq`), and evaluate through it. So `cardOf d` and `firstsOf d` below are,
provably, `(natConfig d _).sols.card` and the decisions of `∃ σ ∈ (natConfig d _).sols,
σ.first = natClass d a` (`cardOf_spec`, `firstsOf_spec`).
-/

namespace ZInQ.RouteK.CR3Check

open ZInQ.RouteK

/-- Euler's criterion as a computable bit: `0` iff `(a mod p)^(p/2) ≡ 1 (mod p)`. -/
def legBitC (p : ℕ) (a : ℤ) : ZMod 2 :=
  if Nat.powMod (a % (p : ℤ)).toNat (p / 2) p = 1 then 0 else 1

theorem legBit_eq_legBitC {p : ℕ} [hp : Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legBit p a = legBitC p a := by
  have hp1 : 1 < p := hp.out.one_lt
  have hcast : (((a % (p : ℤ)).toNat : ℕ) : ZMod p) = (a : ZMod p) := by
    have h0 : 0 ≤ a % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0, ZMod.intCast_mod]
  have key : IsSquare (a : ZMod p) ↔ Nat.powMod (a % (p : ℤ)).toNat (p / 2) p = 1 := by
    rw [ZMod.euler_criterion p ha, Nat.powMod_def, ← hcast, ← Nat.cast_pow,
      ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.one_mod_eq_one.mpr hp1.ne']
  unfold legBit legBitC
  by_cases h : IsSquare (a : ZMod p)
  · rw [if_pos h, if_pos (key.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (key.mpr h'))]

theorem cast_prime_ne_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (((p : ℤ)) : ZMod q) ≠ 0 := by
  rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm

/-- The computable mirror of `natConfig d hd`: same classes, off-diagonal bits by Euler's
criterion, diagonal bits `0` (never used). -/
def natConfigC (d : ℕ) (hd : Odd d) : Config d.primeFactors where
  cls p := (p.1 : ZMod 8)
  cls_mem := (natConfig d hd).cls_mem
  bit a b := if a = b then 0 else legBitC b.1 a.1
  recip x y h := by
    have hx := prime_ne_two_of_mem_primeFactors hd x.2
    have hy := prime_ne_two_of_mem_primeFactors hd y.2
    have hxy : x.1 ≠ y.1 := fun e => h (Subtype.ext e)
    have := (natConfig d hd).recip x y h
    rw [if_neg h, if_neg (Ne.symm h)]
    have e1 : (natConfig d hd).bit x y = legBitC y.1 x.1 := by
      have := Fact.mk hy.1
      exact legBit_eq_legBitC (cast_prime_ne_zero hx.1 hy.1 hxy)
    have e2 : (natConfig d hd).bit y x = legBitC x.1 y.1 := by
      have := Fact.mk hx.1
      exact legBit_eq_legBitC (cast_prime_ne_zero hy.1 hx.1 (Ne.symm hxy))
    rw [← e1, ← e2]
    exact this

/-- The mirror has the same solution set as `natConfig d hd`. -/
theorem natConfig_sols_eq (d : ℕ) (hd : Odd d) : (natConfig d hd).sols = (natConfigC d hd).sols :=
  (natConfig d hd).sols_congr (𝒞' := natConfigC d hd) (fun _ => rfl) fun x y h => by
    have hx := prime_ne_two_of_mem_primeFactors hd x.2
    have hy := prime_ne_two_of_mem_primeFactors hd y.2
    have hxy : x.1 ≠ y.1 := fun e => h (Subtype.ext e)
    show legBit y.1 x.1 = if x = y then 0 else legBitC y.1 x.1
    rw [if_neg h]
    have := Fact.mk hy.1
    exact legBit_eq_legBitC (cast_prime_ne_zero hx.1 hy.1 hxy)

/-- The number of solutions of `Σ(𝒞_d)` (for odd `d`). -/
def cardOf (d : ℕ) : Option ℕ :=
  if hd : Odd d then some (natConfigC d hd).sols.card else none

theorem cardOf_spec (d : ℕ) (hd : Odd d) : cardOf d = some (natConfig d hd).sols.card := by
  rw [cardOf, dif_pos hd, natConfig_sols_eq]

/-- The signed divisors `a` of a squarefree `d` with `|a| ≡ 7 (mod 8)` (products of subsets of
the prime factors; `Nat.divisors` would scan `[1, d]`). -/
def divs7 (d : ℕ) : List ℤ :=
  (((d.primeFactors.powerset.image fun s => ∏ p ∈ s, p).sort (· ≤ ·)).filter
    (fun a => a % 8 = 7)).flatMap fun a => [(a : ℤ), -(a : ℤ)]

/-- For each signed divisor `a` with `|a| ≡ 7 (mod 8)`: does `Σ(𝒞_d)` have a solution with first
coordinate `natClass d a`? Together with the number of solutions. -/
def report (d : ℕ) : Option (ℕ × List (ℤ × Bool)) :=
  if hd : Odd d then
    let S := (natConfigC d hd).sols
    some (S.card, (divs7 d).map fun a => (a, decide (∃ σ ∈ S, σ.first = natClass d a)))
  else none

theorem report_spec (d : ℕ) (hd : Odd d) :
    report d = some ((natConfig d hd).sols.card, (divs7 d).map fun a =>
      (a, decide (∃ σ ∈ (natConfig d hd).sols, σ.first = natClass d a))) := by
  rw [report, dif_pos hd, natConfig_sols_eq]

/-- The full solution set, as the set of pairs `(first class, second class)` of signed integers
`((−1)^{a₀}2^{a₁}Π p^{u_p}, (−1)^{b₀}2^{b₁}Π p^{v_p})`, for comparison with an exact descent. -/
def solPairs (d : ℕ) : Finset (ℤ × ℤ) :=
  if hd : Odd d then
    let cl : ZMod 2 → ZMod 2 → (d.primeFactors → ZMod 2) → ℤ := fun s t w =>
      (if s = 1 then -1 else 1) * (if t = 1 then 2 else 1) *
        ∏ p : d.primeFactors, if w p = 1 then (p.1 : ℤ) else 1
    (natConfigC d hd).sols.image fun σ => (cl σ.a0 σ.a1 σ.u, cl σ.b0 σ.b1 σ.v)
  else ∅


/-! ### Products of a given list of primes

For the slot configurations the primes have about 70 digits, so `Nat.primeFactors` (trial division)
cannot be evaluated. We evaluate `Σ(𝒞_d)` for `d = l.prod` through the configuration of the family
`i ↦ l[i]` (`primeCfg`), transported to `natConfig l.prod` along the bijection
`Fin l.length ≃ l.prod.primeFactors` (as in `selmerCertified_of_primeCfg`). The bits are tabulated
once (`evalList`); `evalList_spec` says that, when `l` is a list of distinct odd primes, its value is
the number of solutions of `Σ(𝒞_{l.prod})` and the decisions of `∃ σ ∈ sols, σ.first = natClass`.
Primality of the entries is a hypothesis of `evalList_spec` (checked outside Lean, by Miller–Rabin
and PARI `isprime`). -/

section List

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → ℕ) (hf : Function.Injective f)
  (hp : ∀ k, (f k).Prime ∧ f k ≠ 2)

include hf hp

/-- The bijection `κ ≃ (∏ f).primeFactors`. -/
noncomputable def primeEquiv : κ ≃ (∏ k, f k).primeFactors :=
  Equiv.ofBijective (fun k => ⟨f k, by
      rw [primeFactors_prod_primes f hf hp]; exact Finset.mem_image_of_mem f (Finset.mem_univ k)⟩)
    ⟨fun a b h => hf (congrArg Subtype.val h), fun q => by
      have h : q.1 ∈ Finset.univ.image f := by
        rw [← primeFactors_prod_primes f hf hp]; exact q.2
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h
      exact ⟨k, Subtype.ext hk⟩⟩

theorem primeEquiv_val (k : κ) : (primeEquiv f hf hp k).1 = f k := rfl

theorem natConfig_prod_card (hd : Odd (∏ k, f k)) :
    (natConfig (∏ k, f k) hd).sols.card = (primeCfg f hf hp).sols.card :=
  ((natConfig (∏ k, f k) hd).card_sols_of_iso (primeEquiv f hf hp) (fun _ => rfl)
    (fun _ _ _ => rfl)).symm

theorem natConfig_prod_first (hd : Odd (∏ k, f k)) (a : ℤ) :
    (∃ σ ∈ (natConfig (∏ k, f k) hd).sols, σ.first = natClass (∏ k, f k) a) ↔
      ∃ σ ∈ (primeCfg f hf hp).sols,
        σ.first = (signBit a, 0, fun k => if (f k : ℤ) ∣ a then 1 else 0) := by
  set e := primeEquiv f hf hp
  have hc : ∀ x, (primeCfg f hf hp).cls x = (natConfig (∏ k, f k) hd).cls (e x) := fun _ => rfl
  have hb : ∀ x y, x ≠ y → (primeCfg f hf hp).bit x y = (natConfig (∏ k, f k) hd).bit (e x) (e y) :=
    fun _ _ _ => rfl
  constructor
  · rintro ⟨σ, hσ, h⟩
    refine ⟨(((natConfig _ hd).solsEquivOfIso e hc hb).symm ⟨σ, hσ⟩).1,
      (((natConfig _ hd).solsEquivOfIso e hc hb).symm ⟨σ, hσ⟩).2, ?_⟩
    rw [Config.solsEquivOfIso_symm_apply]
    simp only [Unknowns.first, Unknowns.comp, natClass, Prod.mk.injEq] at h ⊢
    refine ⟨h.1, h.2.1, ?_⟩
    funext k
    rw [Function.comp_apply, h.2.2]
    rfl
  · rintro ⟨σ, hσ, h⟩
    refine ⟨((natConfig _ hd).solsEquivOfIso e hc hb ⟨σ, hσ⟩).1,
      ((natConfig _ hd).solsEquivOfIso e hc hb ⟨σ, hσ⟩).2, ?_⟩
    rw [Config.solsEquivOfIso_apply]
    simp only [Unknowns.first, Unknowns.comp, natClass, Prod.mk.injEq] at h ⊢
    refine ⟨h.1, h.2.1, ?_⟩
    funext q
    have hq : f (e.symm q) = q.1 := by
      rw [← primeEquiv_val f hf hp]; exact congrArg Subtype.val (e.apply_symm_apply q)
    rw [Function.comp_apply, h.2.2]
    simp only [hq]

end List

/-- Validity of a table of classes and bits (the fields `cls_mem` and `recip` of `Config`). -/
def Valid {k : ℕ} (c : Fin k → ZMod 8) (t : Fin k → Fin k → ZMod 2) : Prop :=
  (∀ i, c i ∈ oddClasses) ∧ ∀ i j, i ≠ j → t i j + t j i = lam8 (c i) * lam8 (c j)

instance {k : ℕ} (c : Fin k → ZMod 8) (t : Fin k → Fin k → ZMod 2) : Decidable (Valid c t) := by
  unfold Valid; infer_instance

/-- The configuration given by a valid table. -/
def tblCfg {k : ℕ} (c : Fin k → ZMod 8) (t : Fin k → Fin k → ZMod 2) (h : Valid c t) :
    Config (Fin k) where
  cls := c
  cls_mem := h.1
  bit := t
  recip := h.2

/-- `Σ(𝒞_d)` for `d = l.prod`: the number of solutions and, for each `a ∈ as`, whether some solution
has first coordinate the class of `a`. The bits are computed once, into an array. -/
def evalList (l : List ℕ) (as : List ℤ) : Option (ℕ × List (ℤ × Bool)) :=
  let arr : Array (Array (ZMod 2)) :=
    Array.ofFn fun i : Fin l.length => Array.ofFn fun j : Fin l.length => legBitC l[j] l[i]
  let t : Fin l.length → Fin l.length → ZMod 2 := fun i j =>
    if i = j then 0 else (arr[i.1]'(by simp [arr]))[j.1]'(by simp [arr])
  let c : Fin l.length → ZMod 8 := fun i => (l[i] : ZMod 8)
  if h : Valid c t then
    let S := (tblCfg c t h).sols
    some (S.card, as.map fun a =>
      (a, decide (∃ σ ∈ S, σ.first = (signBit a, (0 : ZMod 2),
        fun i : Fin l.length => if ((l[i] : ℕ) : ℤ) ∣ a then (1 : ZMod 2) else 0))))
  else none

theorem evalList_spec (l : List ℕ) (hl : l.Nodup) (hp : ∀ p ∈ l, p.Prime ∧ p ≠ 2) (as : List ℤ)
    (hd : Odd l.prod) {r : ℕ × List (ℤ × Bool)} (h : evalList l as = some r) :
    r = ((natConfig l.prod hd).sols.card, as.map fun a =>
      (a, decide (∃ σ ∈ (natConfig l.prod hd).sols, σ.first = natClass l.prod a))) := by
  set f : Fin l.length → ℕ := fun i => l[i.1]
  have hf : Function.Injective f := fun i j hij => Fin.ext ((List.Nodup.getElem_inj_iff hl).mp hij)
  have hpf : ∀ k, (f k).Prime ∧ f k ≠ 2 := fun k => hp _ (List.getElem_mem _)
  have hprod : ∏ k, f k = l.prod := Fin.prod_univ_getElem l
  unfold evalList at h
  dsimp only at h
  split_ifs at h with hv
  · simp only [Option.some.injEq] at h
    subst h
    have hsols : (tblCfg _ _ hv).sols = (primeCfg f hf hpf).sols :=
      (tblCfg _ _ hv).sols_congr (𝒞' := primeCfg f hf hpf) (fun _ => rfl) fun x y hxy => by
        show (if x = y then 0 else _) = legBit (f y) (f x)
        rw [if_neg hxy]
        simp only [Array.getElem_ofFn]
        have := Fact.mk (hpf y).1
        exact (legBit_eq_legBitC (cast_prime_ne_zero (hpf x).1 (hpf y).1 (hf.ne hxy))).symm
    have hd' : Odd (∏ k, f k) := hprod ▸ hd
    have hcard := natConfig_prod_card f hf hpf hd'
    have hfirst := natConfig_prod_first f hf hpf hd'
    rw [hsols]
    revert hd hcard hfirst hd'
    rw [hprod]
    intro hd hd' hcard hfirst
    rw [hcard]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    rw [Prod.mk.injEq]
    exact ⟨rfl, decide_eq_decide.mpr (hfirst a).symm⟩

end ZInQ.RouteK.CR3Check

/-! ### The 40 test values of `d` (output parsed by `compare.py`) -/

open ZInQ.RouteK.CR3Check in
#eval ([2413, 5549, 1133, 13493, 14141, 3781, 13973, 2501, 4181, 11461, 106997, 280789, 731573, 1214501, 518629, 11077, 433493, 1427077, 527669, 74269, 22212173, 303405, 138165, 5671693, 19886717, 64057229, 86948237, 1981293, 38820013, 3896269, 41594005133, 5361627277, 4584527461, 3741938677, 15335133, 252336837, 57049269, 365904845, 71760581861, 1320054901] : List ℕ).map fun d => (d, report d, solPairs d)

/-! ### Step 5: the slot configurations of `slot5.py` (`slot5.json`): `|n|` and `|nθ|`, with the classes
of `β`, `−β` and `q₀` -/

#eval ("B1:n_primes", ZInQ.RouteK.CR3Check.evalList [367, 10485400588664660974772121827, 10486432232002953463171525529] [367, -367, 10485400588664660974772121827])
#eval ("B1:ntheta_primes", ZInQ.RouteK.CR3Check.evalList [367, 4033196781289538209, 10485400588664660974772121827, 10486432232002953463171525529] [367, -367, 10485400588664660974772121827])
#eval ("B2:n_primes", ZInQ.RouteK.CR3Check.evalList [223, 82622780052435858962049641833, 82623673552927285355577806747, 82637524598148424450700482033] [223, -223, 82623673552927285355577806747])
#eval ("B2:ntheta_primes", ZInQ.RouteK.CR3Check.evalList [17, 223, 3076771135964606057, 82622780052435858962049641833, 82623673552927285355577806747, 82637524598148424450700482033] [223, -223, 82623673552927285355577806747])
#eval ("B3:n_primes", ZInQ.RouteK.CR3Check.evalList [179, 229, 2643037467799195686912273774886081, 2643069913946436493351180819541537, 2643127850188248995022751289448523] [40991, -40991, 2643127850188248995022751289448523])
#eval ("B3:ntheta_primes", ZInQ.RouteK.CR3Check.evalList [179, 229, 9102564911044178045161, 2643037467799195686912273774886081, 2643069913946436493351180819541537, 2643127850188248995022751289448523] [40991, -40991, 2643127850188248995022751289448523])
#eval ("B4:n_primes", ZInQ.RouteK.CR3Check.evalList [193, 383, 1790778506488270270387878673570537, 1790823313543614094306036082244323, 1791172562002766057157308845422793, 1791217261487075325120362834083481] [73919, -73919, 1790823313543614094306036082244323])
#eval ("B4:ntheta_primes", ZInQ.RouteK.CR3Check.evalList [193, 383, 5751037, 594686806521853, 1790778506488270270387878673570537, 1790823313543614094306036082244323, 1791172562002766057157308845422793, 1791217261487075325120362834083481] [73919, -73919, 1790823313543614094306036082244323])
#eval ("B5:n_primes", ZInQ.RouteK.CR3Check.evalList [191, 30039734092753806250543727617, 30039835293247733668292649571] [-191, 191, 30039835293247733668292649571])
#eval ("B5:ntheta_primes", ZInQ.RouteK.CR3Check.evalList [191, 22202828856388273129, 30039734092753806250543727617, 30039835293247733668292649571] [-191, 191, 30039835293247733668292649571])
#eval ("B6:n_primes", ZInQ.RouteK.CR3Check.evalList [43, 101, 4646129580770491510820588434819, 4646223175023900123790802082953, 4646708085574066043006471889553, 4646805666491538512351471594089] [-4343, 4343, 4646129580770491510820588434819])
#eval ("B6:ntheta_primes", ZInQ.RouteK.CR3Check.evalList [43, 101, 37337, 4044912535591457, 4646129580770491510820588434819, 4646223175023900123790802082953, 4646708085574066043006471889553, 4646805666491538512351471594089] [-4343, 4343, 4646129580770491510820588434819])
