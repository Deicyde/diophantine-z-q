import Mathlib
import ZInQKernel.HDecomp.Sqrt.Disj
import ZInQKernel.HDecomp.Descent.B2Glue

/-!
# t30-adelic, part T30: the local square-root criterion from local Kronecker–Weber

`GlueDescent.B2Q.LeafSqrtCrit` (leaf L-B2c) is proved from `PkgI6.LocalKroneckerWeber p` at
every prime `p` (leaf T16).  The finite-level criterion is `GlueSqrtDisj` (imported); this file
does the descent through `Gal(ℚ_p(μ_n)/ℚ_p)` and the inflation to `G_{ℚ_p}`.
-/

open GlueDescent.B2Q GlueSqrtDisj

namespace T30

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### Elementary lemmas on roots of unity -/

section Roots

variable {F : Type*} [Field F]

theorem zpow_congr_of_dvd {x : F} {q : ℕ} (hq : x ^ q = 1) (hx : x ≠ 0) {s t : ℤ}
    (h : (q : ℤ) ∣ s - t) : x ^ s = x ^ t := by
  obtain ⟨c, hc⟩ := h
  have : s = t + q * c := by linarith
  rw [this, zpow_add₀ hx, zpow_mul, zpow_natCast, hq, one_zpow, mul_one]

theorem ne_zero_of_pow_eq_one {x : F} {q : ℕ} (hq0 : 0 < q) (hq : x ^ q = 1) : x ≠ 0 := by
  rintro rfl
  rw [zero_pow hq0.ne'] at hq
  exact zero_ne_one hq

/-- Bezout decomposition of a root of unity of order dividing `a b` with `a ⊥ b`. -/
theorem exists_decomp {a b : ℕ} (hab : a.Coprime b) (h0 : 0 < a * b) {z : F}
    (hz : z ^ (a * b) = 1) : ∃ x y : F, x ^ a = 1 ∧ y ^ b = 1 ∧ z = x * y := by
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq_one h0 hz
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hab
  have hzab : z ^ ((a * b : ℕ) : ℤ) = 1 := by rw [zpow_natCast, hz]
  refine ⟨z ^ (v * b), z ^ (u * a), ?_, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul, show v * (b : ℤ) * a = (a * b : ℕ) * v by push_cast; ring,
      zpow_mul, hzab, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul, show u * (a : ℤ) * b = (a * b : ℕ) * u by push_cast; ring,
      zpow_mul, hzab, one_zpow]
  · rw [← zpow_add₀ hz0, show v * (b : ℤ) + u * a = 1 by linarith, zpow_one]

/-- An automorphism acting by `x ↦ x^e` on `μ_a` and on `μ_b` (`a ⊥ b`) acts so on `μ_{ab}`. -/
theorem act_crt (f : F ≃+* F) {a b : ℕ} (hab : a.Coprime b) (h0 : 0 < a * b) (e : ℕ)
    (h1 : ∀ x : F, x ^ a = 1 → f x = x ^ e) (h2 : ∀ y : F, y ^ b = 1 → f y = y ^ e)
    (z : F) (hz : z ^ (a * b) = 1) : f z = z ^ e := by
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_decomp hab h0 hz
  rw [map_mul, h1 x hx, h2 y hy, mul_pow]

/-- `((a.val : ℤ) : ZMod N) = a`. -/
theorem intCast_val {N : ℕ} [NeZero N] (a : ZMod N) : (((a.val : ℕ) : ℤ) : ZMod N) = a := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem dvd_val_sub {N : ℕ} [NeZero N] (a : ZMod N) (t : ℤ) (h : (t : ZMod N) = a) :
    (N : ℤ) ∣ ((a.val : ℕ) : ℤ) - t := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, h, intCast_val]

end Roots

/-! ### The decomposition map and the cyclotomic character -/

section Resp

variable (p : Nat.Primes)

/-- An element of `G_{ℚ_p}` as an automorphism of `\bar ℚ_p`. -/
def actp (σ : GQp p) : PadicAlgCl (p : ℕ) ≃ₐ[ℚ_[(p : ℕ)]] PadicAlgCl (p : ℕ) := σ

/-- `resp p σ` is the restriction of `σ` along an embedding `ℚ̄ → ℚ̄_p`. -/
theorem exists_emb : ∃ g : AlgebraicClosure ℚ →+* PadicAlgCl (p : ℕ),
    ∀ (σ : GQp p) (x : AlgebraicClosure ℚ), g (act (resp p σ) x) = actp p σ (g x) := by
  letI : Algebra ℚ ℚ_[(p : ℕ)] := (algebraMap ℚ ℚ_[(p : ℕ)]).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[(p : ℕ)] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[(p : ℕ)]) := g.toAlgebra
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x)

/-- **The cyclotomic character of `resp p σ`** is read off from the action of `σ` on the `N`-th
roots of unity of `\bar ℚ_p`. -/
theorem cyc_resp_eq (N : ℕ) [NeZero N] (σ : GQp p) (u : (ZMod N)ˣ)
    (h : ∀ x : PadicAlgCl (p : ℕ), x ^ N = 1 → actp p σ x = x ^ ((u : ZMod N)).val) :
    cyc N (resp p σ) = u := by
  obtain ⟨g, hg⟩ := exists_emb p
  apply Units.ext
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (toRingAut (resp p σ)) (c := (u : ZMod N)) ?_).symm
  intro t ht
  apply g.injective
  have ht' : (t : AlgebraicClosure ℚ) ^ N = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  change g (act (resp p σ) t) = _
  rw [hg, map_pow]
  exact h _ (by rw [← map_pow, ht', map_one])

theorem cyc_resp_eq_one (N : ℕ) [NeZero N] (σ : GQp p)
    (h : ∀ x : PadicAlgCl (p : ℕ), x ^ N = 1 → actp p σ x = x) : cyc N (resp p σ) = 1 := by
  apply cyc_resp_eq
  intro x hx
  rw [h x hx]
  have hx0 := ne_zero_of_pow_eq_one (Nat.pos_of_ne_zero (NeZero.ne N)) hx
  have := zpow_congr_of_dvd hx hx0 (dvd_val_sub ((1 : (ZMod N)ˣ) : ZMod N) 1 (by simp))
  rw [zpow_natCast, zpow_one] at this
  exact this.symm

/-- If `σ` inverts `μ_{p^k}` and fixes `μ_{N'}`, `N = p^k N'`, then `cyc_N(σ) = u` for the unit
`u ≡ -1 mod p^k`, `u ≡ 1 mod N'`. -/
theorem cyc_resp_eq_u (N k N' : ℕ) [NeZero N] (hN : N = (p : ℕ) ^ k * N')
    (hcop : ((p : ℕ) ^ k).Coprime N') (σ : GQp p) (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod N') = 1)
    (h1 : ∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k) = 1 → actp p σ x = x⁻¹)
    (h2 : ∀ y : PadicAlgCl (p : ℕ), y ^ N' = 1 → actp p σ y = y) :
    cyc N (resp p σ) = u := by
  have hN0 : 0 < (p : ℕ) ^ k * N' := hN ▸ Nat.pos_of_ne_zero (NeZero.ne N)
  have hpk0 : 0 < (p : ℕ) ^ k := Nat.pos_of_ne_zero (fun h => by simp [h] at hN0)
  have hN'0 : 0 < N' := Nat.pos_of_ne_zero (fun h => by simp [h] at hN0)
  haveI : NeZero ((p : ℕ) ^ k) := ⟨hpk0.ne'⟩
  haveI : NeZero N' := ⟨hN'0.ne'⟩
  set e := (u : ZMod N).val with he
  have he1 : (((p : ℕ) ^ k : ℕ) : ℤ) ∣ (-1 : ℤ) - (e : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := hu1
    rw [ZMod.cast_eq_val] at this
    push_cast
    exact this
  have he2 : (N' : ℤ) ∣ (1 : ℤ) - (e : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := hu2
    rw [ZMod.cast_eq_val] at this
    push_cast
    exact this
  apply cyc_resp_eq
  intro z hz
  rw [hN] at hz
  refine act_crt (actp p σ).toRingEquiv hcop hN0 e (fun x hx => ?_) (fun y hy => ?_) z hz
  · rw [AlgEquiv.coe_toRingEquiv, h1 x hx]
    have hx0 := ne_zero_of_pow_eq_one hpk0 hx
    have := zpow_congr_of_dvd hx hx0 he1
    rw [zpow_neg_one, zpow_natCast] at this
    exact this
  · rw [AlgEquiv.coe_toRingEquiv, h2 y hy]
    have hy0 := ne_zero_of_pow_eq_one hN'0 hy
    have := zpow_congr_of_dvd hy hy0 he2
    rw [zpow_one, zpow_natCast] at this
    exact this

end Resp

/-! ### The action of `σ` on the roots of unity of a cyclotomic level -/

section Level

variable (p : Nat.Primes)

/-- If `τ' ∈ Gal(ℚ_p(μ_{p^k m})/ℚ_p)` is the restriction of `σ`, then `σ` acts on `μ_{p^k}` and
`μ_m` through `galToProd τ'`. -/
theorem act_of_gal (k m : ℕ) [NeZero m] (σ : GQp p)
    (τ' : Gal(muField (p : ℕ) ((p : ℕ) ^ k * m)/ℚ_[(p : ℕ)]))
    (hc : ∀ x : muField (p : ℕ) ((p : ℕ) ^ k * m), ((τ' x : _) : PadicAlgCl (p : ℕ)) = actp p σ x) :
    (∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k) = 1 → actp p σ x =
        x ^ (((galToProd (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ').1 :
          ZMod ((p : ℕ) ^ k))).val) ∧
    (∀ y : PadicAlgCl (p : ℕ), y ^ m = 1 → actp p σ y =
        y ^ (((galToProd (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ').2 :
          ZMod m)).val) := by
  have hmem : ∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k * m) = 1 →
      x ∈ muField (p : ℕ) ((p : ℕ) ^ k * m) := fun x hx => IntermediateField.subset_adjoin _ _ hx
  constructor
  · intro x hx
    have hxK := hmem x (by rw [pow_mul, hx, one_pow])
    have h2 := galToProd_fst_spec (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ'
      ⟨x, hxK⟩ (Subtype.ext (by simpa using hx))
    have h1 := hc ⟨x, hxK⟩
    rw [h2] at h1
    rw [← h1]
    simp
  · intro y hy
    have hyK := hmem y (by rw [mul_comm, pow_mul, hy, one_pow])
    have h2 := galToProd_snd_spec (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ'
      ⟨y, hyK⟩ (Subtype.ext (by simpa using hy))
    have h1 := hc ⟨y, hyK⟩
    rw [h2] at h1
    rw [← h1]
    simp

/-- The restriction of `σ` satisfies the compatibility of `act_of_gal`. -/
theorem restrictNormal_compat (n : ℕ) [NeZero n] (σ : GQp p) (x : muField (p : ℕ) n) :
    ((((actp p σ).restrictNormal (muField (p : ℕ) n)) x : _) : PadicAlgCl (p : ℕ)) =
      actp p σ x :=
  AlgEquiv.restrictNormal_commutes (actp p σ) (muField (p : ℕ) n) x

end Level

/-! ### Square roots of `ℂˣ`-valued characters -/

section SqrtC

theorem complexUnits_pow_surj {n : ℕ} (hn : n ≠ 0) : Function.Surjective (fun a : ℂˣ => a ^ n) := by
  intro x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact x.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩

/-- **A `ℂˣ`-valued character of an abelian group is a square iff it kills the `2`-torsion.**
(`ℂˣ` is divisible, hence an injective `ℤ`-module.) -/
theorem exists_sqrt_iff {Γ : Type*} [CommGroup Γ] (χ : Γ →* ℂˣ) :
    (∃ ψ : Γ →* ℂˣ, ∀ g, ψ g ^ 2 = χ g) ↔ ∀ g : Γ, g ^ 2 = 1 → χ g = 1 := by
  constructor
  · rintro ⟨ψ, hψ⟩ g hg
    rw [← hψ, ← map_pow, hg, map_one]
  · intro h
    letI : RootableBy ℂˣ ℕ := rootableByOfPowLeftSurj _ _ complexUnits_pow_surj
    letI : RootableBy ℂˣ ℤ := Group.rootableByIntOfRootableByNat ℂˣ
    letI : DivisibleBy (Additive ℂˣ) ℤ := divisibleByOfSMulRightSurj _ _ (fun {n} hn a => by
      obtain ⟨b, hb⟩ := RootableBy.surjective_pow ℂˣ ℤ hn (Additive.toMul a)
      exact ⟨Additive.ofMul b, by show n • Additive.ofMul b = a; rw [← ofMul_zpow]; exact congrArg Additive.ofMul hb⟩)
    let χa : Additive Γ →+ Additive ℂˣ := MonoidHom.toAdditive χ
    let d : Additive Γ →+ Additive Γ :=
      { toFun := fun g => 2 • g, map_zero' := smul_zero 2, map_add' := fun a b => smul_add 2 a b }
    have hker : d.ker ≤ χa.ker := fun g hg => by
      have h2 : (Additive.toMul g) ^ 2 = 1 := AddMonoidHom.mem_ker.mp hg
      exact AddMonoidHom.mem_ker.mpr (congrArg Additive.ofMul (h _ h2))
    let χq := QuotientAddGroup.lift d.ker χa hker
    let e := QuotientAddGroup.quotientKerEquivRange d
    let χr : d.range →+ Additive ℂˣ := χq.comp e.symm.toAddMonoidHom
    obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
      d.range.subtype Subtype.val_injective χr
    refine ⟨MonoidHom.toAdditive.symm ψ, fun g => ?_⟩
    have hm : d (Additive.ofMul g) ∈ d.range := AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h1 := DFunLike.congr_fun hψ ⟨d (Additive.ofMul g), hm⟩
    have h2 : e.symm ⟨d (Additive.ofMul g), hm⟩ = ((Additive.ofMul g : Additive Γ) : _ ⧸ d.ker) := by
      rw [AddEquiv.symm_apply_eq]; rfl
    have h3 : ψ (d (Additive.ofMul g)) = χa (Additive.ofMul g) := by
      rw [show ψ (d (Additive.ofMul g)) = (ψ.comp d.range.subtype) ⟨d (Additive.ofMul g), hm⟩
        from rfl, h1]
      simp only [χr, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h2, χq,
        QuotientAddGroup.lift_mk]
    have h4 : ψ (d (Additive.ofMul g)) = 2 • ψ (Additive.ofMul g) := map_nsmul ψ 2 _
    rw [h4] at h3
    exact congrArg Additive.toMul h3

end SqrtC

/-! ### Two-torsion at the bigger level (from the proof of `sqrt_criterion_level`) -/

section Torsion

open GlueSqrtLocal

/-- At the level `L = ℚ_p(μ_{p^{k+1} m'})` with `ord_{m'}(p) = 2 ord_m(p)`, an element of order
`≤ 2` restricts to `1` or to `τ₋₁` on `K = ℚ_p(μ_{p^k m})`. -/
theorem restrict_sq_eq_one {p : ℕ} [hp : Fact p.Prime] {L : Type} [Field L] [Algebra ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
    (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (k m m' : ℕ) [NeZero m] [NeZero m'] (hcop : p.Coprime m) (hcop' : p.Coprime m')
    [IsCyclotomicExtension {p ^ k * m} ℚ_[p] K] [IsCyclotomicExtension {p ^ (k + 1) * m'} ℚ_[p] L]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] (hm : m ∣ m')
    (hord : orderOf (ZMod.unitOfCoprime p hcop') = 2 * orderOf (ZMod.unitOfCoprime p hcop))
    (g' : Gal(L/ℚ_[p])) (hg2 : g' ^ 2 = 1) :
    galToProd (p := p) (L := K) k m (g'.restrictNormal K) = 1 ∨
      galToProd (p := p) (L := K) k m (g'.restrictNormal K) = (-1, 1) := by
  have hk : k ≤ k + 1 := Nat.le_succ k
  have hres := fun g => galToProd_restrict (p := p) (L := L) (k + 1) m' K k m hk hm g
  set a := (galToProd (p := p) (L := L) (k + 1) m' g').1 with ha_def
  set b := (galToProd (p := p) (L := L) (k + 1) m' g').2 with hb_def
  have hsq : galToProd (p := p) (L := L) (k + 1) m' g' ^ 2 = 1 := by
    rw [← map_pow, hg2, map_one]
  have ha : a ^ 2 = 1 := by rw [ha_def, ← Prod.pow_fst, hsq, Prod.fst_one]
  have hb : b ^ 2 = 1 := by rw [hb_def, ← Prod.pow_snd, hsq, Prod.snd_one]
  have hbmem : b ∈ Subgroup.zpowers (ZMod.unitOfCoprime p hcop') := by
    have hmem : galToProd (p := p) (L := L) (k + 1) m' g' ∈
        (galToProd (p := p) (L := L) (k + 1) m').range := ⟨g', rfl⟩
    rw [range_galToProd (k + 1) m' hcop'] at hmem
    exact hmem.2
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbmem
  have h2j : (orderOf (ZMod.unitOfCoprime p hcop') : ℤ) ∣ j * 2 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, hj]
    exact_mod_cast hb
  rw [hord] at h2j
  push_cast at h2j
  have hfj : (orderOf (ZMod.unitOfCoprime p hcop) : ℤ) ∣ j := by
    rw [mul_comm j] at h2j
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2j
  have hbK : ZMod.castHom hm (ZMod m) (b : ZMod m') = 1 := by
    have hU : Units.map (ZMod.castHom hm (ZMod m)).toMonoidHom (ZMod.unitOfCoprime p hcop') =
        ZMod.unitOfCoprime p hcop := Units.ext (by simp)
    have := congrArg (Units.map (ZMod.castHom hm (ZMod m)).toMonoidHom) hj
    rw [map_zpow, hU, orderOf_dvd_iff_zpow_eq_one.mp hfj] at this
    have := congrArg Units.val this
    simpa using this.symm
  obtain ⟨h1, h2⟩ := hres g'
  rw [← ha_def] at h1
  rw [← hb_def, hbK] at h2
  have hsnd : (galToProd (p := p) (L := K) k m (g'.restrictNormal K)).2 = 1 := Units.ext h2
  rcases redU_sq_eq_one hp.out k a ha with hpos | hneg
  · left
    ext
    · rw [h1, ← redU_val, hpos]; rfl
    · rw [hsnd]; rfl
  · right
    ext
    · rw [h1, ← redU_val, hneg]
    · rw [hsnd]

end Torsion

/-! ### The criterion over `G_{ℚ_p}` -/

section Main

theorem pow_val_one {F : Type*} [Field F] {q : ℕ} [NeZero q] {x : F} (hx : x ^ q = 1) :
    x ^ ((1 : ZMod q).val) = x := by
  have hx0 := ne_zero_of_pow_eq_one (Nat.pos_of_ne_zero (NeZero.ne q)) hx
  have := zpow_congr_of_dvd hx hx0 (dvd_val_sub (1 : ZMod q) 1 (by simp))
  rwa [zpow_natCast, zpow_one] at this

theorem pow_val_neg_one {F : Type*} [Field F] {q : ℕ} [NeZero q] {x : F} (hx : x ^ q = 1) :
    x ^ ((-1 : ZMod q).val) = x⁻¹ := by
  have hx0 := ne_zero_of_pow_eq_one (Nat.pos_of_ne_zero (NeZero.ne q)) hx
  have := zpow_congr_of_dvd hx hx0 (dvd_val_sub (-1 : ZMod q) (-1) (by simp))
  rwa [zpow_natCast, zpow_neg_one] at this

variable (p : Nat.Primes)

/-- The type of `G_{ℚ_p}` written as a Galois group. -/
abbrev Gp := PadicAlgCl (p : ℕ) ≃ₐ[ℚ_[(p : ℕ)]] PadicAlgCl (p : ℕ)

/-- `σ` restricts to `1` on `ℚ_p(μ_{p^k m})`: it fixes `μ_{p^k m}`. -/
theorem fix_of_galToProd_one (k m : ℕ) [NeZero m] (σ : GQp p)
    (τ' : Gal(muField (p : ℕ) ((p : ℕ) ^ k * m)/ℚ_[(p : ℕ)]))
    (hc : ∀ x : muField (p : ℕ) ((p : ℕ) ^ k * m), ((τ' x : _) : PadicAlgCl (p : ℕ)) = actp p σ x)
    (h : galToProd (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ' = 1) :
    (∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k) = 1 → actp p σ x = x) ∧
      (∀ y : PadicAlgCl (p : ℕ), y ^ m = 1 → actp p σ y = y) := by
  obtain ⟨h1, h2⟩ := act_of_gal p k m σ τ' hc
  rw [h] at h1 h2
  exact ⟨fun x hx => by rw [h1 x hx]; exact pow_val_one hx,
    fun y hy => by rw [h2 y hy]; exact pow_val_one hy⟩

/-- `σ` restricts to `τ₋₁` on `ℚ_p(μ_{p^k m})`: it inverts `μ_{p^k}` and fixes `μ_m`. -/
theorem act_of_galToProd_tau (k m : ℕ) [NeZero m] (σ : GQp p)
    (τ' : Gal(muField (p : ℕ) ((p : ℕ) ^ k * m)/ℚ_[(p : ℕ)]))
    (hc : ∀ x : muField (p : ℕ) ((p : ℕ) ^ k * m), ((τ' x : _) : PadicAlgCl (p : ℕ)) = actp p σ x)
    (h : galToProd (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ' = (-1, 1)) :
    (∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k) = 1 → actp p σ x = x⁻¹) ∧
      (∀ y : PadicAlgCl (p : ℕ), y ^ m = 1 → actp p σ y = y) := by
  obtain ⟨h1, h2⟩ := act_of_gal p k m σ τ' hc
  rw [h] at h1 h2
  refine ⟨fun x hx => ?_, fun y hy => by rw [h2 y hy]; exact pow_val_one hy⟩
  rw [h1 x hx]
  simpa using pow_val_neg_one hx

/-- Abstract inflation: a character `χ'` of `G_{ℚ_p}` trivial on `Gal(\bar ℚ_p/L)` (`L` finite
abelian) and on every element whose image in `Gal(L/ℚ_p)` has order `≤ 2` has a locally constant
square root. -/
theorem sqrt_of_inflated (L : IntermediateField ℚ_[(p : ℕ)] (PadicAlgCl (p : ℕ)))
    [FiniteDimensional ℚ_[(p : ℕ)] L] [IsGalois ℚ_[(p : ℕ)] L]
    (hcomm : ∀ a b : Gal(L/ℚ_[(p : ℕ)]), a * b = b * a) (χ' : Gp p →* ℂˣ)
    (hker : ∀ σ : Gp p, AlgEquiv.restrictNormalHom L σ = 1 → χ' σ = 1)
    (htor : ∀ σ : Gp p, (AlgEquiv.restrictNormalHom L σ) ^ 2 = 1 → χ' σ = 1) :
    ∃ φ : Gp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = χ' x := by
  let rL : Gp p →* Gal(L/ℚ_[(p : ℕ)]) := AlgEquiv.restrictNormalHom L
  have hsurj : Function.Surjective rL := AlgEquiv.restrictNormalHom_surjective _
  have hker' : rL.ker ≤ χ'.ker := fun σ hσ => hker σ hσ
  let χL : Gal(L/ℚ_[(p : ℕ)]) →* ℂˣ :=
    rL.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨χ', hker'⟩
  have hχL : ∀ σ, χL (rL σ) = χ' σ := fun σ =>
    rL.liftOfRightInverse_comp_apply _ _ ⟨χ', hker'⟩ σ
  letI : CommGroup Gal(L/ℚ_[(p : ℕ)]) := { (inferInstance : Group Gal(L/ℚ_[(p : ℕ)])) with
    mul_comm := hcomm }
  obtain ⟨ψ, hψ⟩ := (exists_sqrt_iff χL).mpr (by
    intro g' hg'
    obtain ⟨σ, rfl⟩ := hsurj g'
    rw [hχL]
    exact htor σ hg')
  refine ⟨ψ.comp rL, ?_, fun x => ?_⟩
  · exact (IsLocallyConstant.of_discrete ψ).comp_continuous
      (InfiniteGalois.restrictNormalHom_continuous L)
  · show ψ (rL x) ^ 2 = χ' x
    rw [hψ]
    exact hχL x

/-- `σ` trivial on `ℚ_p(μ_n)`, `N ∣ n`, has trivial `cyc_N`. -/
theorem cyc_eq_one_of_restrict (N n : ℕ) [NeZero N] [NeZero n] (hNn : N ∣ n) (σ : Gp p)
    (hσ : AlgEquiv.restrictNormalHom (muField (p : ℕ) n) σ = 1) : cyc N (resp p σ) = 1 := by
  apply cyc_resp_eq_one
  intro x hx
  have hxL : x ∈ muField (p : ℕ) n := IntermediateField.subset_adjoin _ _ (by
    obtain ⟨c, hc⟩ := hNn
    show x ^ n = 1
    rw [hc, pow_mul, hx, one_pow])
  have := AlgEquiv.restrictNormalHom_apply (muField (p : ℕ) n) σ ⟨x, hxL⟩
  rw [hσ, AlgEquiv.one_apply] at this
  exact this.symm

theorem coe_algebraMap_mu (a b : ℕ) [Fact (a ∣ b)] (y : muField (p : ℕ) a) :
    ((algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b) y : muField (p : ℕ) b) :
      PadicAlgCl (p : ℕ)) = y := by
  have : algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b) y =
      IntermediateField.inclusion (muField_mono (p : ℕ) (Fact.out : a ∣ b)) y := rfl
  rw [this, IntermediateField.coe_inclusion]

/-- Restriction in two steps `\bar ℚ_p ⊇ ℚ_p(μ_b) ⊇ ℚ_p(μ_a)`. -/
theorem restrict_restrict_compat (a b : ℕ) [NeZero a] [NeZero b] [Fact (a ∣ b)] (σ : Gp p)
    (x : muField (p : ℕ) a) :
    ((((AlgEquiv.restrictNormalHom (muField (p : ℕ) b) σ).restrictNormal
      (muField (p : ℕ) a)) x : muField (p : ℕ) a) : PadicAlgCl (p : ℕ)) = actp p σ x := by
  have e1 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom (muField (p : ℕ) b) σ)
    (muField (p : ℕ) a) x
  calc _ = ((algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b)
        (((AlgEquiv.restrictNormalHom (muField (p : ℕ) b) σ).restrictNormal
          (muField (p : ℕ) a)) x) : muField (p : ℕ) b) : PadicAlgCl (p : ℕ)) :=
        (coe_algebraMap_mu p a b _).symm
    _ = ((AlgEquiv.restrictNormalHom (muField (p : ℕ) b) σ
          (algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b) x) : muField (p : ℕ) b) :
          PadicAlgCl (p : ℕ)) := by rw [e1]
    _ = actp p σ (algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b) x) :=
        AlgEquiv.restrictNormalHom_apply _ σ _
    _ = actp p σ x := by rw [coe_algebraMap_mu]

/-- The two-torsion step at the level `L = ℚ_p(μ_{p^{k+1}(p^{2f}-1)})`. -/
theorem cyc_of_torsion (N k N' : ℕ) [NeZero N] [NeZero N'] (hN : N = (p : ℕ) ^ k * N')
    (hcopN' : (p : ℕ).Coprime N')
    [NeZero ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)]
    [Fact ((p : ℕ) ^ k * N' ∣
      (p : ℕ) ^ (k + 1) * ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1))]
    (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod N') = 1) (σ : Gp p)
    (hσ : (AlgEquiv.restrictNormalHom (muField (p : ℕ) ((p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1))) σ) ^ 2 = 1) :
    cyc N (resp p σ) = 1 ∨ cyc N (resp p σ) = u := by
  have hcop : ((p : ℕ) ^ k).Coprime N' := hcopN'.pow_left k
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hf0 : 0 < orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN') := orderOf_pos _
  have h2f : 0 < 2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN') := by omega
  have hcop' := coprime_pow_sub_one hp2 h2f
  have hord := orderOf_unit_pow_sub_one hp2 h2f
  have hm := dvd_pow_orderOf_sub_one hcopN' 2
  have hc := restrict_restrict_compat p ((p : ℕ) ^ k * N') ((p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)) σ
  rcases restrict_sq_eq_one (L := muField (p : ℕ) ((p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)))
      (muField (p : ℕ) ((p : ℕ) ^ k * N')) k N' _ hcopN' hcop' hm hord.symm.symm _ hσ with h1 | h1
  · left
    obtain ⟨a1, a2⟩ := fix_of_galToProd_one p k N' σ _ hc h1
    apply cyc_resp_eq_one
    intro z hz
    rw [hN] at hz
    have := act_crt (actp p σ).toRingEquiv hcop (hN ▸ Nat.pos_of_ne_zero (NeZero.ne N)) 1
      (fun x hx => by rw [AlgEquiv.coe_toRingEquiv, a1 x hx, pow_one])
      (fun y hy => by rw [AlgEquiv.coe_toRingEquiv, a2 y hy, pow_one]) z hz
    rwa [pow_one] at this
  · right
    obtain ⟨a1, a2⟩ := act_of_galToProd_tau p k N' σ _ hc h1
    exact cyc_resp_eq_u p N k N' hN hcop σ u hu1 hu2 a1 a2

/-- **The "if" direction** (no Kronecker–Weber needed), with `N = p^k N'` given. -/
theorem sqrt_of_chi' (N k N' : ℕ) [NeZero N] [NeZero N'] (hN : N = (p : ℕ) ^ k * N')
    (hcopN' : (p : ℕ).Coprime N') (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod N') = 1) (hχ : χ.toUnitHom u = 1) :
    ∃ φ : Gp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = χ.toUnitHom (cyc N (resp p x)) := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hf0 : 0 < orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN') := orderOf_pos _
  have h2f : 0 < 2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN') := by omega
  have hcop' := coprime_pow_sub_one hp2 h2f
  have hm'0 : (p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1 ≠ 0 := by
    have := Nat.le_self_pow h2f.ne' (p : ℕ)
    omega
  haveI : NeZero ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1) := ⟨hm'0⟩
  haveI : Fact ((p : ℕ) ^ k * N' ∣
      (p : ℕ) ^ (k + 1) * ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)) :=
    ⟨level_dvd (p : ℕ) k N' hcopN'⟩
  have hNL : N ∣ (p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1) :=
    hN ▸ level_dvd (p : ℕ) k N' hcopN'
  refine sqrt_of_inflated p (muField (p : ℕ) ((p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)))
    (fun a b => galToProd_injective (p := (p : ℕ)) (k + 1) _ hcop' (by
      rw [map_mul, map_mul]; exact mul_comm _ _))
    ((χ.toUnitHom.comp (cyc N)).comp (resp p)) (fun σ hσ => ?_) (fun σ hσ => ?_)
  · show χ.toUnitHom (cyc N (resp p σ)) = 1
    rw [cyc_eq_one_of_restrict p N _ hNL σ hσ, map_one]
  · show χ.toUnitHom (cyc N (resp p σ)) = 1
    rcases cyc_of_torsion p N k N' hN hcopN' u hu1 hu2 σ hσ with h | h
    · rw [h, map_one]
    · rw [h, hχ]

/-- **The "only if" direction, from local Kronecker–Weber.** -/
theorem chi_of_sqrt' (hLKW : PkgI6.LocalKroneckerWeber (p : ℕ)) (N k N' : ℕ) [NeZero N]
    [NeZero N'] (hN : N = (p : ℕ) ^ k * N') (hcopN' : (p : ℕ).Coprime N')
    (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod N') = 1) (φ : Gp p →* ℂˣ) (hφl : IsLocallyConstant φ)
    (hφ : ∀ x, φ x ^ 2 = χ.toUnitHom (cyc N (resp p x))) : χ.toUnitHom u = 1 := by
  have hcop := hcopN'.pow_left k
  have hHo : IsOpen ((φ.ker : Subgroup (Gp p)) : Set (Gp p)) := by
    have := hφl.isOpen_fiber 1
    convert this using 1
    ext x
    simp
  have hHc : IsClosed ((φ.ker : Subgroup (Gp p)) : Set (Gp p)) :=
    Subgroup.isClosed_of_isOpen _ hHo
  have hMH : (IntermediateField.fixedField φ.ker).fixingSubgroup = φ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨φ.ker, hHc⟩
  haveI : FiniteDimensional ℚ_[(p : ℕ)] (IntermediateField.fixedField φ.ker) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hMH]; exact hHo)
  haveI hgal : IsGalois ℚ_[(p : ℕ)] (IntermediateField.fixedField φ.ker) :=
    (InfiniteGalois.normal_iff_isGalois _).mp (by rw [hMH]; exact φ.normal_ker)
  have hsM : Function.Surjective
      (AlgEquiv.restrictNormalHom (IntermediateField.fixedField φ.ker) : Gp p →* _) :=
    AlgEquiv.restrictNormalHom_surjective _
  have hcommM : ∀ a b : Gal(IntermediateField.fixedField φ.ker/ℚ_[(p : ℕ)]), a * b = b * a := by
    intro a b
    obtain ⟨σ, rfl⟩ := hsM a
    obtain ⟨τ, rfl⟩ := hsM b
    rw [← map_mul, ← map_mul, MonoidHom.eq_iff, IntermediateField.restrictNormalHom_ker, hMH,
      MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_comm (φ τ) (φ σ),
      inv_mul_cancel]
  haveI : IsAbelianGalois ℚ_[(p : ℕ)] (IntermediateField.fixedField φ.ker) :=
    { toIsGalois := hgal, toIsMulCommutative := ⟨⟨hcommM⟩⟩ }
  obtain ⟨a, b, hb, hcopb, hMle⟩ := le_muField_of_lkw (p : ℕ) hLKW
    (IntermediateField.fixedField φ.ker)
  haveI : NeZero (N' * b) := ⟨Nat.mul_ne_zero (NeZero.ne N') hb.ne'⟩
  have hcop0 : (p : ℕ).Coprime (N' * b) := Nat.Coprime.mul_right hcopN' hcopb
  have hMK : IntermediateField.fixedField φ.ker ≤ muField (p : ℕ) ((p : ℕ) ^ (k + a) * (N' * b)) :=
    hMle.trans (muField_mono _ (Nat.mul_dvd_mul (pow_dvd_pow _ (Nat.le_add_left a k))
      (dvd_mul_left b N')))
  obtain ⟨τ, hτ⟩ := exists_tau (p := (p : ℕ))
    (L := muField (p : ℕ) ((p : ℕ) ^ (k + a) * (N' * b))) (k + a) (N' * b) hcop0
  have hsK : Function.Surjective (AlgEquiv.restrictNormalHom
      (muField (p : ℕ) ((p : ℕ) ^ (k + a) * (N' * b))) : Gp p →* _) :=
    AlgEquiv.restrictNormalHom_surjective _
  obtain ⟨σ, hσ⟩ := hsK τ
  have hτ2 : τ ^ 2 = 1 := galToProd_injective (p := (p : ℕ)) (k + a) (N' * b) hcop0 (by
    rw [map_pow, hτ, map_one]
    ext <;> simp)
  have hσ2 : σ ^ 2 ∈ φ.ker := by
    rw [← hMH]
    apply IntermediateField.fixingSubgroup_antitone hMK
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_pow, hσ, hτ2]
  have hc : ∀ x : muField (p : ℕ) ((p : ℕ) ^ (k + a) * (N' * b)),
      ((τ x : _) : PadicAlgCl (p : ℕ)) = actp p σ x := fun x => by
    rw [← hσ]
    exact AlgEquiv.restrictNormalHom_apply _ σ x
  obtain ⟨a1, a2⟩ := act_of_galToProd_tau p (k + a) (N' * b) σ τ hc hτ
  have hcyc := cyc_resp_eq_u p N k N' hN hcop σ u hu1 hu2
    (fun x hx => a1 x (by
      obtain ⟨c, hc⟩ := pow_dvd_pow (p : ℕ) (Nat.le_add_right k a)
      rw [hc, pow_mul, hx, one_pow]))
    (fun y hy => a2 y (by rw [pow_mul, hy, one_pow]))
  rw [← hcyc, ← hφ σ, ← map_pow]
  exact hσ2

end Main

/-! ### The leaf -/

/-- **T30 at one prime:** the square-root criterion at `p` follows from local Kronecker–Weber at
`p` (only the "only if" direction uses it). -/
theorem sqrtCrit_at (p : Nat.Primes) (hLKW : PkgI6.LocalKroneckerWeber (p : ℕ)) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ N.factorization p)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod (N / (p : ℕ) ^ N.factorization p)) = 1) :
    (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = galChar χ (resp p x)) ↔
      χ.toUnitHom u = 1 := by
  have hN : N = (p : ℕ) ^ N.factorization p * (N / (p : ℕ) ^ N.factorization p) :=
    (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  have hcopN' := Nat.coprime_ordCompl p.2 (NeZero.ne N)
  haveI : NeZero (N / (p : ℕ) ^ N.factorization p) :=
    ⟨fun h => NeZero.ne N (by rw [hN, h, mul_zero])⟩
  constructor
  · rintro ⟨φ, hφl, hφ⟩
    exact chi_of_sqrt' p hLKW N _ _ hN hcopN' χ u hu1 hu2 φ hφl hφ
  · intro hχ
    exact sqrt_of_chi' p N _ _ hN hcopN' χ u hu1 hu2 hχ

/-- **T30: the local square-root criterion `LeafSqrtCrit` (leaf L-B2c) follows from local
Kronecker–Weber (leaf T16, `PkgI6.LocalKroneckerWeber`) at every prime.** -/
theorem leafSqrtCrit_of_localKroneckerWeber
    (hLKW : ∀ p : Nat.Primes, PkgI6.LocalKroneckerWeber (p : ℕ)) : LeafSqrtCrit :=
  fun p N _ χ u hu1 hu2 => sqrtCrit_at p (hLKW p) N χ u hu1 hu2

/-- The same with T16 in the form of the field `t16a` of `HSyn` (`scratch/h-decomposition`). -/
theorem leafSqrtCrit_of_t16a (h : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p) :
    LeafSqrtCrit :=
  leafSqrtCrit_of_localKroneckerWeber fun p => h (p : ℕ)

end T30

/-! Axiom audit. -/
#print axioms T30.leafSqrtCrit_of_localKroneckerWeber
#print axioms T30.leafSqrtCrit_of_t16a
