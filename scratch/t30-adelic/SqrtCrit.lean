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

end T30
