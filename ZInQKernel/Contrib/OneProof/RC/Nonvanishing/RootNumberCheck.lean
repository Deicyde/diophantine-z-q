import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.FivePrime

/-!
# Lane RC13 (nonvanishing), part 5: the root-number check (tex 1994–2001)

"The root-number check includes ramified dyadic quadratic characters. At the primes in `S` equal
squareclasses give isomorphic local curves. At a good odd prime newly ramified in the parameter,
the root factor is `(−1/p)` [Desjardins, Proposition 3.3]. Its product outside `S` is fixed by the
real sign and the dyadic unit class. Thus unit classes `3` or `7` modulo eight are allowed; the
field discriminant may be four times the parameter. We do not invoke an odd-discriminant root
formula on those parameters."

`rootNumber_of_mem` (PROVED from the interface `LocalRootNumbers`, whose `desjardins` field is
Desjardins' Proposition 3.3): if one squarefree parameter `u₀` of a signed unit filter at
`S ∋ 2, 3` twists `A` to root number `w`, then every squarefree parameter does. The proof is the
text's: `w(A^{(u)}) = W_∞ · ∏_{p ∈ S} W_p(A^{(u)}) · ∏_{p ∣ u} (−1/p)`; the factors at `S` depend
only on the squareclasses (`w_iso`), and `∏_{p ∣ u} (−1/p) = χ₄(|u|)` depends only on `|u| mod 4`,
which is fixed by the real sign and the class mod `8`. No formula `w(E^{(d)}) = w(E)χ_d(−N)` is
used, so parameters `≡ 3, 7 (mod 8)` (field discriminant `4u`) are covered.

`fivePrime_of_mem`, `nonvanishing_even_of_mem`, `nonvanishing_odd_of_mem`: Propositions
`ex:app-five-prime` and `ex:sec7-nonvanishing` with the root number of the filter read off a
single parameter.
-/

namespace ZInQ.Manuscript.RC.Nonvanishing

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53 SignedUnitFilter ZMod

/-- `∏_{p ∣ n} χ₄(p) = χ₄(n)` for squarefree `n`. PROVED. -/
theorem prod_chi4_primeFactors {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (χ₄ (p : ZMod 4) : ℤ) = χ₄ (n : ZMod 4) := by
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hn, Nat.cast_prod, map_prod]

/-- **The local root numbers of a twist outside `S`.** For a squarefree `v` prime to `S ∋ 2, 3`
(with `S` containing every prime at which the model of `A` is not good) and a finite set `T ⊇ S`
of primes containing the primes of `v`: the product of the local root numbers of `A^{(v)}` over
`T` is its product over `S` times `χ₄(|v|) = ∏_{p ∣ v} (−1/p)`. At `p ∣ v` this is Desjardins'
Proposition 3.3 (`W_p = (−1/p)`, "a good odd prime newly ramified in the parameter"); at the
other primes of `T ∖ S` the twist is good. PROVED from the interface. -/
theorem prod_w_qtwist (L : LocalRootNumbers) {A : WeierstrassCurve ℚ} (hA : A.IsElliptic)
    {S : Finset ℕ} (h2 : 2 ∈ S) (h3 : 3 ∈ S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ S)
    {v : ℤ} (hvsf : Squarefree v) (hvS : ∀ p ∈ S, ¬ (p : ℤ) ∣ v)
    {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (hST : S ⊆ T) (hvT : v.natAbs.primeFactors ⊆ T) :
    ∏ p ∈ T, L.w p (qtwist A v) =
      (∏ p ∈ S, L.w p (qtwist A v)) * (χ₄ (v.natAbs : ZMod 4) : ℤ) := by
  classical
  have hv0 : v ≠ 0 := hvsf.ne_zero
  have hvA : v.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hv0
  have hsfA : Squarefree v.natAbs := Int.squarefree_natAbs.mpr hvsf
  rw [← Finset.prod_sdiff hST, mul_comm]
  congr 1
  -- the factors at `T ∖ S`
  have hfac : ∀ p ∈ T \ S, L.w p (qtwist A v) =
      if p ∈ v.natAbs.primeFactors then (χ₄ (p : ZMod 4) : ℤ) else 1 := by
    intro p hp
    obtain ⟨hpT, hpS⟩ := Finset.mem_sdiff.mp hp
    have hpp := hT p hpT
    have hp2 : p ≠ 2 := fun h => hpS (h ▸ h2)
    have hp3 : p ≠ 3 := fun h => hpS (h ▸ h3)
    have hgood : GoodAt A p := by by_contra h; exact hpS (hbad p hpp h)
    split_ifs with hpv
    · -- `p ∣ v`: Desjardins, Proposition 3.3, type `I₀`
      have : Fact p.Prime := ⟨hpp⟩
      have hp5 : 5 ≤ p := by
        have := hpp.two_le
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p <;> first | omega | exact absurd hpp (by decide)
        · exact h
      have hdvd : (p : ℤ) ∣ v := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hpv)
      have hD := L.desjardins A p hA hp5 hgood v hvsf hdvd
      rw [L.w_good A p hA hpp hgood] at hD
      have hsq : legendreSym p (-1) ^ 2 = 1 := legendreSym.sq_one p (by
        intro h0
        have : ((-1 : ℤ) : ZMod p) = 0 := h0
        rw [Int.cast_neg, Int.cast_one, neg_eq_zero] at this
        exact one_ne_zero this)
      rw [← legendreSym.at_neg_one hp2]
      calc L.w p (qtwist A v) = legendreSym p (-1) ^ 2 * L.w p (qtwist A v) := by rw [hsq, one_mul]
        _ = legendreSym p (-1) * (legendreSym p (-1) * L.w p (qtwist A v)) := by ring
        _ = legendreSym p (-1) := by rw [← hD, mul_one]
    · -- `p ∤ v`: the twist is good at `p`
      have hnd : ¬ (p : ℤ) ∣ v := by
        intro hdvd
        exact hpv (Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp hdvd, hvA⟩)
      exact L.w_good _ p (qtwist_isElliptic hA (by exact_mod_cast hv0)) hpp
        (goodAt_twist hpp hp2 hgood hnd)
  rw [Finset.prod_congr rfl hfac, Finset.prod_ite_mem]
  have hinter : (T \ S) ∩ v.natAbs.primeFactors = v.natAbs.primeFactors := by
    apply Finset.inter_eq_right.mpr
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨hvT hp, fun hpS => hvS p hpS ?_⟩
    exact Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
  rw [hinter, prod_chi4_primeFactors hsfA]

theorem bad_qtwist_mem {A : WeierstrassCurve ℚ} {S : Finset ℕ} (h2 : 2 ∈ S)
    (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ S) {v : ℤ} (hv0 : v ≠ 0) :
    ∀ p : ℕ, p.Prime → ¬ GoodAt (qtwist A v) p → p ∈ S ∪ v.natAbs.primeFactors := by
  intro p hp hng
  by_contra hcon
  rw [Finset.mem_union, not_or] at hcon
  obtain ⟨hpS, hpv⟩ := hcon
  have hp2 : p ≠ 2 := fun h => hpS (h ▸ h2)
  have hgood : GoodAt A p := by by_contra h; exact hpS (hbad p hp h)
  have hnd : ¬ (p : ℤ) ∣ v := fun hdvd =>
    hpv (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr hv0⟩)
  exact hng (goodAt_twist hp hp2 hgood hnd)

/-- Two members of a filter at `S ∋ 2` have `|u| ≡ |u'| (mod 4)`. PROVED. -/
theorem natAbs_mod_four_eq {Φ : SignedUnitFilter} (h2 : 2 ∈ Φ.S) {u u' : ℤ} (hu : Φ.Mem u)
    (hu' : Φ.Mem u') : (u.natAbs : ZMod 4) = (u'.natAbs : ZMod 4) := by
  have h8 : u' ≡ u [ZMOD 8] :=
    modEq_eight_of_isSquareAt_two (hu'.odd h2) (hu.odd h2) (hu.isSquareAt_ratio hu' h2)
  have hs : Int.sign u = Int.sign u' := hu.2.1.trans hu'.2.1.symm
  have hu0 := hu.ne_zero
  have hu0' := hu'.ne_zero
  have key : (u.natAbs : ℤ) ≡ (u'.natAbs : ℤ) [ZMOD 8] := by
    rcases lt_or_gt_of_ne hu0 with hneg | hpos
    · have hneg' : u' < 0 := by
        by_contra h
        have hpos' : 0 < u' := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hu0')
        rw [Int.sign_eq_neg_one_of_neg hneg, Int.sign_eq_one_of_pos hpos'] at hs
        exact absurd hs (by decide)
      rw [Int.ofNat_natAbs_of_nonpos hneg.le, Int.ofNat_natAbs_of_nonpos hneg'.le]
      exact (h8.symm).neg
    · have hpos' : 0 < u' := by
        by_contra h
        have hneg' : u' < 0 := lt_of_le_of_ne (not_lt.mp h) hu0'
        rw [Int.sign_eq_one_of_pos hpos, Int.sign_eq_neg_one_of_neg hneg'] at hs
        exact absurd hs (by decide)
      rw [Int.natAbs_of_nonneg hpos.le, Int.natAbs_of_nonneg hpos'.le]
      exact h8.symm
  have key4 : (u.natAbs : ℤ) ≡ (u'.natAbs : ℤ) [ZMOD 4] :=
    Int.ModEq.of_mul_left 2 (by simpa using key)
  have := (ZMod.intCast_eq_intCast_iff _ _ 4).mpr key4
  rw [Int.cast_natCast, Int.cast_natCast] at this
  exact this

/-- **The root-number check** (tex 1994–2001; PROVED from `LocalRootNumbers`, i.e. from
Desjardins' Proposition 3.3 and the local-global properties of root numbers). In a signed unit
filter at `S ∋ 2, 3` (with every prime at which the model of `A` is not good in `S`), the root
number of `A^{(u)}` does not depend on the squarefree parameter `u`: if one squarefree `u₀` in the
filter gives root number `w`, the filter has root number `w`. -/
theorem rootNumber_of_mem (L : LocalRootNumbers) (hBCDT : BCDTThmA) {A : WeierstrassCurve ℚ}
    (hA : A.IsElliptic) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S) (h3 : 3 ∈ Φ.S)
    (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ Φ.S) {u₀ : ℤ} (hu₀ : Φ.Mem u₀)
    (hsf₀ : Squarefree u₀) {w : ℤ} (hw : RootNumber (qtwist A u₀) w) : Φ.RootNumber A w := by
  classical
  intro u hu hsf
  let T : Finset ℕ := Φ.S ∪ u₀.natAbs.primeFactors ∪ u.natAbs.primeFactors
  have hTp : ∀ p ∈ T, p.Prime := by
    intro p hp
    simp only [T, Finset.mem_union] at hp
    rcases hp with (hp | hp) | hp
    · exact Φ.prime_of_mem p hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have hST : Φ.S ⊆ T := fun p hp => by simp [T, hp]
  have h0T : u₀.natAbs.primeFactors ⊆ T := fun p hp => by simp [T, hp]
  have h1T : u.natAbs.primeFactors ⊆ T := fun p hp => by simp [T, hp]
  have hA₀ : (qtwist A u₀).IsElliptic := qtwist_isElliptic hA (by exact_mod_cast hu₀.ne_zero)
  have hA₁ : (qtwist A u).IsElliptic := qtwist_isElliptic hA (by exact_mod_cast hu.ne_zero)
  have hbad₀ : ∀ p : ℕ, p.Prime → ¬ GoodAt (qtwist A u₀) p → p ∈ T := by
    intro p hp hng
    rcases Finset.mem_union.mp (bad_qtwist_mem h2 hbad hu₀.ne_zero p hp hng) with h | h
    · exact hST h
    · exact h0T h
  have hbad₁ : ∀ p : ℕ, p.Prime → ¬ GoodAt (qtwist A u) p → p ∈ T := by
    intro p hp hng
    rcases Finset.mem_union.mp (bad_qtwist_mem h2 hbad hu.ne_zero p hp hng) with h | h
    · exact hST h
    · exact h1T h
  have hglob₀ := (L.global _ hA₀ (hBCDT _ hA₀) T hTp hbad₀ w).mp hw
  refine (L.global _ hA₁ (hBCDT _ hA₁) T hTp hbad₁ w).mpr ?_
  rw [hglob₀, L.wInf_eq _ hA₀, L.wInf_eq _ hA₁,
    prod_w_qtwist L hA h2 h3 hbad hsf₀ (fun p hp => hu₀.not_dvd hp) hTp hST h0T,
    prod_w_qtwist L hA h2 h3 hbad hsf (fun p hp => hu.not_dvd hp) hTp hST h1T,
    natAbs_mod_four_eq h2 hu₀ hu]
  congr 2
  refine Finset.prod_congr rfl fun p hp => ?_
  exact L.w_iso A p hA (Φ.prime_of_mem p hp) u₀ u hu₀.ne_zero hu.ne_zero
    (hu₀.isSquareAt_ratio hu hp)

/-- **Proposition `ex:app-five-prime`, with the filter's root number read off one parameter**
(tex 10001–10006, with the root-number check 1994–2001). PROVED. -/
theorem fivePrime_of_mem (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    (L : LocalRootNumbers) {A : WeierstrassCurve ℚ} (hA : A.IsElliptic) (Φ : SignedUnitFilter)
    (h2 : 2 ∈ Φ.S) (h3 : 3 ∈ Φ.S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ Φ.S)
    {u₀ : ℤ} (hu₀ : Φ.Mem u₀) (hsf₀ : Squarefree u₀) (heven : RootNumber (qtwist A u₀) 1)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧ omega u ≤ 5 ∧
      CentralNonzero (qtwist A u) :=
  fivePrime_four hHL hTS hBCDT hA Φ h2 hbad B hB
    (rootNumber_of_mem L hBCDT hA Φ h2 h3 hbad hu₀ hsf₀ heven)

/-- **Proposition `ex:sec7-nonvanishing`, odd case, with the filter's root number read off one
parameter** (tex 1979, 1984–2001). PROVED. -/
theorem nonvanishing_odd_of_mem (hBFH : BFHSimpleZero) (hBCDT : BCDTThmA)
    (L : LocalRootNumbers) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) (Φ : SignedUnitFilter)
    (h2 : 2 ∈ Φ.S) (h3 : 3 ∈ Φ.S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ Φ.S)
    {u₀ : ℤ} (hu₀ : Φ.Mem u₀) (hsf₀ : Squarefree u₀) (hodd : RootNumber (qtwist E u₀) (-1))
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧
      AnalyticRank (qtwist E u) 1 :=
  nonvanishing_odd hBFH hBCDT hE Φ h2 hbad B hB
    (rootNumber_of_mem L hBCDT hE Φ h2 h3 hbad hu₀ hsf₀ hodd)

end ZInQ.Manuscript.RC.Nonvanishing
