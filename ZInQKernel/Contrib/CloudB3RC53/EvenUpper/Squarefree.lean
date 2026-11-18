import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Realize

/-!
# EvenUpper, part 8: the realized cubes are squarefree, explicitly

Corrected-shape check after the integration team's review: clause (iii) of the even upper inputs
asks for binary families based at partitionable parameters, and the base and every parameter of
the family must be squarefree. `realized_cubes_sq` (`PROVED`; the construction of
`realized_cubes`) exhibits every parameter as `h_x = d · Q_x`:
* `Q_x > 0` is the product of the new primes present at `x`;
* `d` and `Q_x` are coprime, because the new primes are distinct and avoid the primes of `d`;
* `h_x` is squarefree, with base `h_0 = d`.
`hcubes_of_dictionary_sq` is the corresponding form of `hcubes_of_dictionary`: on the filter (a
negative squarefree `d` prime to the support, the corrected meaning of `W.Partitionable`) the
families are based at `d` and squarefree at every address.
-/

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

section Cube

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **The realized cubes with their factorization** (`PROVED`): `h_x = d · Q_x` with `Q_x > 0`
prime to `d`, every `h_x` squarefree, `h_0 = d`. -/
theorem realized_cubes_sq (T : TypeData L ε) (R : Finset ℕ → ZMod 2)
    (hswap : ∀ B, FixedUFactorization T R B) (hA : CoefficientRules ε (symb T R))
    (htyp1 : ∀ q : ℕ, q.Prime → ((q : ℕ) : ZMod T.m) = 1 → T.typ q = 0)
    {N₀ : ℕ} (hN₀ : 0 < N₀) (unitSym : ℤ → Prop) (d : ℤ) (hsq : Squarefree d)
    (hgood : ∀ p ∈ d.natAbs.primeFactors, T.Good p ∧ Nat.Coprime p N₀)
    (hpart : IsPartitionable ε (symb T R) (primeConfig d.natAbs.primeFactors T.typ))
    (hunitR : ∀ W : Finset ℕ, (∀ p ∈ W, T.Good p) → R W = 1 →
      unitSym (d.sign * ∏ p ∈ W, (p : ℤ)))
    (b : ℕ) (hb : 1 ≤ b) :
    ∃ fam : ZInQ.Manuscript.RC.Even.BinaryFamily N₀, fam.b = b ∧ fam.h 0 = d ∧
      (∀ x, ∃ Q : ℤ, 0 < Q ∧ fam.h x = d * Q ∧ IsCoprime d Q ∧ Squarefree (fam.h x)) ∧
      ∀ x, x ≠ 0 → unitSym (fam.h x) := by
  classical
  set P := d.natAbs.primeFactors with hPdef
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hn0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
  set Γ := primeConfig P T.typ with hΓdef
  have hf0 : IsReal T Γ id :=
    ⟨Set.injOn_id _, fun v hv => ⟨(hgood v hv).1, rfl⟩, fun v _ w _ _ => rfl⟩
  have hΓ : Γ.Compatible ε := compatible_of_real T hf0
  obtain ⟨Γ', act'', hΓ', hext, hact, hnew, hunit⟩ :=
    one_symbol_address hA Γ hΓ hpart.1 (partitionable_terminalNonzero hA hΓ hpart) b hb
  have hcop8 : ∀ p ∈ P, Nat.Coprime p (8 * N₀) := by
    intro p hp
    refine Nat.Coprime.mul_right ?_ (hgood p hp).2
    have h2 : Nat.Coprime p 2 :=
      (Nat.coprime_primes (hgood p hp).1.1 Nat.prime_two).mpr (hgood p hp).1.ne_two
    simpa using Nat.Coprime.pow_right 3 h2
  obtain ⟨f, hf, hfP, hfN⟩ := exists_real_extension T (8 * N₀) (by omega) htyp1 P
    (fun p hp => ⟨(hgood p hp).1, hcop8 p hp⟩) Γ' hΓ' hext (fun v hv hvP => (hnew v hv hvP).1)
  set Vn := Γ'.V.filter (· ∉ P) with hVn
  have hVact : ∀ v ∈ Vn, ∃ w, act'' v = some w := fun v hv => by
    obtain ⟨hv, hvP⟩ := Finset.mem_filter.mp hv
    obtain ⟨-, w, -, hw⟩ := hnew v hv hvP
    exact ⟨w, hw⟩
  have hVprime : ∀ v ∈ Vn, (f v).Prime ∧ f v ∉ P := fun v hv => by
    obtain ⟨hv, hvP⟩ := Finset.mem_filter.mp hv
    exact ⟨(hf.2.1 v hv).1.1, (hfN v hv hvP).1⟩
  have hVmod : ∀ v ∈ Vn, ((f v : ℕ) : ZMod (8 * N₀)) = 1 := fun v hv => by
    obtain ⟨hv, hvP⟩ := Finset.mem_filter.mp hv
    have := congrArg (ZMod.castHom (dvd_mul_left (8 * N₀) T.m) (ZMod (8 * N₀)))
      (hfN v hv hvP).2
    simpa using this
  have hinjVn : Set.InjOn f Vn := fun v hv w hw h =>
    hf.1 (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1 h
  set Q := cubeQ act'' Vn f with hQdef
  have hQ0 : Q 0 = 1 := cubeQ_zero act'' Vn f hVact
  have hQmod : ∀ x, ((Q x : ℕ) : ZMod (8 * N₀)) = 1 := cubeQ_mod act'' Vn f _ hVmod
  have hQodd : ∀ x, Odd (Q x) := by
    intro x
    have h := hQmod x
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
          (isSquareAt_of_mod (Q x) (hQmod x) p.2 hp) (Fact.mk p.2)
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
  refine ⟨fam, rfl, by simp [fam, hQ0], fun x => ⟨Q x, hQpos x, rfl, ?_, fam.sqfree x⟩,
    fun x hx => ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]
    exact coprime_cubeQ act'' Vn f _ hn0 hVprime x
  have h1 : symb T R (Γ'.at act'' x) = 1 := by simpa using hunit x hx 0
  have hfx := isReal_at T hf act'' x
  rw [symb_eq T R (hswap _) (Config.at_compatible hΓ' act'' x) le_rfl hfx] at h1
  have hgoodW : ∀ p ∈ (Γ'.at act'' x).V.image f, T.Good p := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact (hfx.2.1 v hv).1
  have hu := hunitR _ hgoodW h1
  have heq : d.sign * ∏ p ∈ (Γ'.at act'' x).V.image f, (p : ℤ) = fam.h x := by
    rw [Finset.prod_image (fun v hv w hw h => hfx.1 hv hw h),
      ← Finset.prod_filter_mul_prod_filter_not (Γ'.at act'' x).V (· ∈ P)]
    have hVxP : (Γ'.at act'' x).V.filter (· ∈ P) = P := by
      ext v
      simp only [Config.at, Finset.mem_filter]
      constructor
      · rintro ⟨-, hv⟩; exact hv
      · intro hv
        exact ⟨⟨hext.1 hv, by simp [present, hact v hv]⟩, hv⟩
    have hVxN : (Γ'.at act'' x).V.filter (· ∉ P) = Vn.filter (present act'' x) := by
      ext v
      simp only [Config.at, hVn, Finset.mem_filter]
      tauto
    rw [hVxP, hVxN, Finset.prod_congr rfl (fun v hv => by rw [hfP v hv])]
    have hprodP : ∏ v ∈ P, (v : ℤ) = d.natAbs := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hsq)]
    rw [hprodP, ← mul_assoc, Int.sign_mul_natAbs]
    simp only [fam, hQdef, cubeQ_eq_prod_filter]
    push_cast
    rfl
  rw [← heq]; exact hu

end Cube

section Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **`hcubes` with squarefree base and squarefree parameters** (`PROVED` from
`realized_cubes_sq`). -/
theorem hcubes_of_dictionary_sq {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (R : ℤ → Finset ℕ → ZMod 2) (hswap : ∀ d B, FixedUFactorization T (R d) B)
    (hA : ∀ d, CoefficientRules ε (symb T (R d)))
    (htyp1 : ∀ q : ℕ, q.Prime → ((q : ℕ) : ZMod T.m) = 1 → T.typ q = 0)
    {N₀ : ℕ} (hN₀ : 0 < N₀) (unitSym : ℤ → Prop)
    (hspec : ∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      Squarefree d ∧ (∀ p ∈ d.natAbs.primeFactors, T.Good p ∧ Nat.Coprime p N₀) ∧
        IsPartitionable ε (symb T (R d)) (primeConfig d.natAbs.primeFactors T.typ))
    (hunitR : ∀ d : ℤ, d ≠ 0 → W.Partitionable d → ∀ V : Finset ℕ, (∀ p ∈ V, T.Good p) →
      R d V = 1 → unitSym (d.sign * ∏ p ∈ V, (p : ℤ))) :
    ∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : ZInQ.Manuscript.RC.Even.BinaryFamily N₀, b ≤ fam.b ∧ fam.h 0 = d ∧
        Squarefree d ∧ (∀ x, Squarefree (fam.h x)) ∧ ∀ x, x ≠ 0 → unitSym (fam.h x) := by
  intro d hd0 hpart hcz b
  obtain ⟨hsq, hgood, hP⟩ := hspec d hd0 hpart hcz
  obtain ⟨fam, hb, h0, hfac, hu⟩ := realized_cubes_sq T (R d) (hswap d) (hA d) htyp1 hN₀ unitSym d
    hsq hgood hP (hunitR d hd0 hpart) (b + 1) (Nat.le_add_left 1 b)
  exact ⟨fam, by omega, h0, hsq, fun x => by obtain ⟨Q, -, -, -, h⟩ := hfac x; exact h, hu⟩

end Wiring

end ZInQ.Contrib.CloudB3RC53.EvenUpper
