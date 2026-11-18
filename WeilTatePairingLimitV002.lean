import WeilTateWildRootsV002

/-!
# From finite-level `μ`-valued pairings to the `ℓ`-adic Tate pairing, with Galois covariance

For commutative groups `M`, `N` (in the application: the actual point groups `A(Ω)`, and `Â(Ω)` or the
translation-invariant classes in `Pic(A_Ω)`), a field `Ω` and a prime `ℓ`, a `LevelPairing` is a family
`e_k : M × N → Ωˣ` that is bimultiplicative on `M[ℓᵏ] × N[ℓᵏ]` and satisfies Mumford's compatibility
`e_{ℓᵏ⁺¹}(x, y) = e_{ℓᵏ}(ℓx, y)` for `x ∈ M[ℓᵏ⁺¹]`, `y ∈ N[ℓᵏ]` (Mumford, *Abelian varieties*, §20).  No
perfectness, alternation, polarization or Galois property is part of the structure.

* `LevelPairing.tatePairing`: the `ℤ_ℓ`-bilinear limit `T_ℓ M × T_ℓ N → T_ℓ(μ(Ω))` on the kernel's
  Tate modules `PkgI3.Tate.T`, with components `e_{ℓᵏ}(t_k, s_k)`;
* `tatePairing_map`: covariance at every finite level gives covariance of the limit;
* `tatePairing_map_eq_of_fix`, `tatePairing_defect_eq_zero`: if the action on `μ_{ℓ^∞}` is trivial, the
  limit is invariant and every defect `g t - t` pairs to zero with every `g`-fixed `s`;
* `e_defect_eq_one`: the same at every finite level;
* `tatePairing_left_ker`, `tatePairing_right_ker`: finite-level perfectness and surjectivity of the Tate
  projections give trivial kernels in the limit;
* `wild_tatePairing_invariant`, `wild_tatePairing_defect_eq_zero`: the case `M = A(Ω)` with the actual
  Galois action `A.galAct σ` of a wild `σ` (literal valuation inequality) over a valuation ring `O` in
  which `ℓ` is invertible.

`TΩ` and `galTΩ` below have the bodies of `ReductSplit.TΩ` and `ReductSplit.galTΩ`
(`ZInQKernel/OneProof/H/TailZ7.lean`), restated because that module is not in the ready import frame.
-/

noncomputable section

namespace WeilTate

open PkgI3

section Generic

variable (ℓ : ℕ) [Fact ℓ.Prime] (M N : Type*) [CommGroup M] [CommGroup N] (Ω : Type) [Field Ω]

/-- A finite-level system of pairings `M[ℓᵏ] × N[ℓᵏ] → Ωˣ`, bimultiplicative on torsion, with Mumford's
compatibility `e_{ℓᵏ⁺¹}(x, y) = e_{ℓᵏ}(ℓx, y)` for `y ∈ N[ℓᵏ]`. -/
structure LevelPairing where
  /-- the pairing at level `ℓᵏ` -/
  e : ℕ → M → N → Ωˣ
  mul_left : ∀ (k : ℕ) (x x' : M) (y : N), x ^ (ℓ ^ k) = 1 → x' ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
    e k (x * x') y = e k x y * e k x' y
  mul_right : ∀ (k : ℕ) (x : M) (y y' : N), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 → y' ^ (ℓ ^ k) = 1 →
    e k x (y * y') = e k x y * e k x y'
  compat : ∀ (k : ℕ) (x : M) (y : N), x ^ (ℓ ^ (k + 1)) = 1 → y ^ (ℓ ^ k) = 1 →
    e (k + 1) x y = e k (x ^ ℓ) y

variable {ℓ M N Ω}

theorem tors_pow {G : Type*} [CommMonoid G] {x : G} {k : ℕ} (h : x ^ (ℓ ^ k) = 1) (c : ℕ) :
    (x ^ c) ^ (ℓ ^ k) = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem tors_mul {G : Type*} [CommMonoid G] {x y : G} {k : ℕ} (hx : x ^ (ℓ ^ k) = 1)
    (hy : y ^ (ℓ ^ k) = 1) : (x * y) ^ (ℓ ^ k) = 1 := by
  rw [mul_pow, hx, hy, one_mul]

theorem tors_inv {G : Type*} [CommGroup G] {x : G} {k : ℕ} (hx : x ^ (ℓ ^ k) = 1) :
    x⁻¹ ^ (ℓ ^ k) = 1 := by
  rw [inv_pow, hx, inv_one]

theorem tors_map {G H : Type*} [Monoid G] [Monoid H] (g : G →* H) {x : G} {k : ℕ}
    (hx : x ^ (ℓ ^ k) = 1) : (g x) ^ (ℓ ^ k) = 1 := by
  rw [← map_pow, hx, map_one]

/-- The `k`-th component of an element of `T_ℓ(G)` is killed by `ℓᵏ`. -/
theorem tors_of_tate {G : Type*} [CommGroup G] (t : Tate.T ℓ (Additive G)) (k : ℕ) :
    (Additive.toMul (t.1 k)) ^ (ℓ ^ k) = 1 := by
  have h := Tate.pow_smul_eq_zero t.2 k
  have h' := congrArg Additive.toMul h
  rwa [toMul_nsmul, toMul_zero] at h'

theorem tate_step {G : Type*} [CommGroup G] (t : Tate.T ℓ (Additive G)) (k : ℕ) :
    (Additive.toMul (t.1 (k + 1))) ^ ℓ = Additive.toMul (t.1 k) := by
  have h := congrArg Additive.toMul (t.2.2 k)
  rwa [toMul_nsmul] at h

namespace LevelPairing

variable (P : LevelPairing ℓ M N Ω)

theorem e_one_left (k : ℕ) (y : N) (hy : y ^ (ℓ ^ k) = 1) : P.e k 1 y = 1 := by
  have h := P.mul_left k 1 1 y (one_pow _) (one_pow _) hy
  rw [mul_one] at h
  have h' : P.e k 1 y * 1 = P.e k 1 y * P.e k 1 y := by rw [mul_one]; exact h
  exact (mul_left_cancel h').symm

theorem e_one_right (k : ℕ) (x : M) (hx : x ^ (ℓ ^ k) = 1) : P.e k x 1 = 1 := by
  have h := P.mul_right k x 1 1 hx (one_pow _) (one_pow _)
  rw [mul_one] at h
  have h' : P.e k x 1 * 1 = P.e k x 1 * P.e k x 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel h').symm

theorem e_pow_left (k : ℕ) (x : M) (y : N) (hx : x ^ (ℓ ^ k) = 1) (hy : y ^ (ℓ ^ k) = 1)
    (c : ℕ) : P.e k (x ^ c) y = (P.e k x y) ^ c := by
  induction c with
  | zero => rw [pow_zero, pow_zero, P.e_one_left k y hy]
  | succ c ih => rw [pow_succ, P.mul_left k _ _ _ (tors_pow hx c) hx hy, ih, pow_succ]

theorem e_pow_right (k : ℕ) (x : M) (y : N) (hx : x ^ (ℓ ^ k) = 1) (hy : y ^ (ℓ ^ k) = 1)
    (c : ℕ) : P.e k x (y ^ c) = (P.e k x y) ^ c := by
  induction c with
  | zero => rw [pow_zero, pow_zero, P.e_one_right k x hx]
  | succ c ih => rw [pow_succ, P.mul_right k _ _ _ hx (tors_pow hy c) hy, ih, pow_succ]

theorem e_inv_left (k : ℕ) (x : M) (y : N) (hx : x ^ (ℓ ^ k) = 1) (hy : y ^ (ℓ ^ k) = 1) :
    P.e k x⁻¹ y = (P.e k x y)⁻¹ := by
  have h := P.mul_left k x x⁻¹ y hx (tors_inv hx) hy
  rw [mul_inv_cancel, P.e_one_left k y hy] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The values at level `ℓᵏ` are `ℓᵏ`-th roots of unity. -/
theorem e_pow_eq_one (k : ℕ) (x : M) (y : N) (hx : x ^ (ℓ ^ k) = 1) (hy : y ^ (ℓ ^ k) = 1) :
    (P.e k x y) ^ (ℓ ^ k) = 1 := by
  rw [← P.e_pow_left k x y hx hy, hx, P.e_one_left k y hy]

/-- The component sequence of the limit pairing. -/
def pairSeq (t : Tate.T ℓ (Additive M)) (s : Tate.T ℓ (Additive N)) : ℕ → Additive Ωˣ :=
  fun k => Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k)))

theorem pairSeq_mem (t : Tate.T ℓ (Additive M)) (s : Tate.T ℓ (Additive N)) :
    P.pairSeq t s ∈ Tate.T ℓ (Additive Ωˣ) := by
  refine ⟨?_, fun k => ?_⟩
  · change Additive.ofMul (P.e 0 (Additive.toMul (t.1 0)) (Additive.toMul (s.1 0))) = 0
    rw [t.2.1, toMul_zero, P.e_one_left 0 _ (tors_of_tate s 0)]
    rfl
  · change ℓ • Additive.ofMul (P.e (k + 1) (Additive.toMul (t.1 (k + 1))) (Additive.toMul (s.1 (k + 1)))) =
      Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k)))
    rw [← ofMul_pow, ← P.e_pow_right (k + 1) _ _ (tors_of_tate t (k + 1)) (tors_of_tate s (k + 1)) ℓ,
      tate_step s k, P.compat k _ _ (tors_of_tate t (k + 1)) (tors_of_tate s k), tate_step t k]

/-- The limit pairing as a function. -/
def pairFun (t : Tate.T ℓ (Additive M)) (s : Tate.T ℓ (Additive N)) : TMu Ω ℓ :=
  ⟨P.pairSeq t s, P.pairSeq_mem t s⟩

theorem pairFun_apply (t : Tate.T ℓ (Additive M)) (s : Tate.T ℓ (Additive N)) (k : ℕ) :
    (P.pairFun t s).1 k = Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k))) :=
  rfl

/-- **The `ℓ`-adic Tate pairing** `T_ℓ M × T_ℓ N → T_ℓ(μ(Ω))`, `ℤ_ℓ`-bilinear. -/
def tatePairing : Tate.T ℓ (Additive M) →ₗ[ℤ_[ℓ]] Tate.T ℓ (Additive N) →ₗ[ℤ_[ℓ]] TMu Ω ℓ :=
  LinearMap.mk₂ ℤ_[ℓ] P.pairFun
    (fun t t' s => Subtype.ext <| funext fun k => by
      change Additive.ofMul (P.e k (Additive.toMul (t.1 k + t'.1 k)) (Additive.toMul (s.1 k))) =
        Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k))) +
          Additive.ofMul (P.e k (Additive.toMul (t'.1 k)) (Additive.toMul (s.1 k)))
      rw [toMul_add, P.mul_left k _ _ _ (tors_of_tate t k) (tors_of_tate t' k) (tors_of_tate s k),
        ofMul_mul])
    (fun a t s => Subtype.ext <| funext fun k => by
      change Additive.ofMul (P.e k (Additive.toMul ((PadicInt.toZModPow k a).val • t.1 k))
          (Additive.toMul (s.1 k))) =
        (PadicInt.toZModPow k a).val • Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k)))
      rw [toMul_nsmul, P.e_pow_left k _ _ (tors_of_tate t k) (tors_of_tate s k), ofMul_pow])
    (fun t s s' => Subtype.ext <| funext fun k => by
      change Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k + s'.1 k))) =
        Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k))) +
          Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s'.1 k)))
      rw [toMul_add, P.mul_right k _ _ _ (tors_of_tate t k) (tors_of_tate s k) (tors_of_tate s' k),
        ofMul_mul])
    (fun a t s => Subtype.ext <| funext fun k => by
      change Additive.ofMul (P.e k (Additive.toMul (t.1 k))
          (Additive.toMul ((PadicInt.toZModPow k a).val • s.1 k))) =
        (PadicInt.toZModPow k a).val • Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k)))
      rw [toMul_nsmul, P.e_pow_right k _ _ (tors_of_tate t k) (tors_of_tate s k), ofMul_pow])

theorem tatePairing_apply (t : Tate.T ℓ (Additive M)) (s : Tate.T ℓ (Additive N)) (k : ℕ) :
    (P.tatePairing t s).1 k =
      Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k))) :=
  rfl

/-- **Covariance passes to the limit.** -/
theorem tatePairing_map (gM : M →* M) (gN : N →* N) (gμ : Ωˣ →* Ωˣ)
    (hcov : ∀ (k : ℕ) (x : M) (y : N), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      P.e k (gM x) (gN y) = gμ (P.e k x y))
    (t : Tate.T ℓ (Additive M)) (s : Tate.T ℓ (Additive N)) :
    P.tatePairing (Tate.map (MonoidHom.toAdditive gM) t) (Tate.map (MonoidHom.toAdditive gN) s) =
      Tate.map (MonoidHom.toAdditive gμ) (P.tatePairing t s) := by
  apply Subtype.ext
  funext k
  change Additive.ofMul (P.e k (gM (Additive.toMul (t.1 k))) (gN (Additive.toMul (s.1 k)))) =
    Additive.ofMul (gμ (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k))))
  rw [hcov k _ _ (tors_of_tate t k) (tors_of_tate s k)]

/-- **Invariance** when the action on `μ_{ℓ^∞}(Ω)` is trivial. -/
theorem tatePairing_map_eq_of_fix (gM : M →* M) (gN : N →* N) (gμ : Ωˣ →* Ωˣ)
    (hcov : ∀ (k : ℕ) (x : M) (y : N), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      P.e k (gM x) (gN y) = gμ (P.e k x y))
    (hμ : ∀ (k : ℕ) (u : Ωˣ), u ^ (ℓ ^ k) = 1 → gμ u = u)
    (t : Tate.T ℓ (Additive M)) (s : Tate.T ℓ (Additive N)) :
    P.tatePairing (Tate.map (MonoidHom.toAdditive gM) t) (Tate.map (MonoidHom.toAdditive gN) s) =
      P.tatePairing t s := by
  rw [P.tatePairing_map gM gN gμ hcov]
  apply Subtype.ext
  funext k
  change Additive.ofMul (gμ (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k)))) =
    Additive.ofMul (P.e k (Additive.toMul (t.1 k)) (Additive.toMul (s.1 k)))
  rw [hμ k _ (P.e_pow_eq_one k _ _ (tors_of_tate t k) (tors_of_tate s k))]

/-- **Defects pair to zero with fixed vectors**: if `g s = s` then `E(g t - t, s) = 0`. -/
theorem tatePairing_defect_eq_zero (gM : M →* M) (gN : N →* N) (gμ : Ωˣ →* Ωˣ)
    (hcov : ∀ (k : ℕ) (x : M) (y : N), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      P.e k (gM x) (gN y) = gμ (P.e k x y))
    (hμ : ∀ (k : ℕ) (u : Ωˣ), u ^ (ℓ ^ k) = 1 → gμ u = u)
    (t : Tate.T ℓ (Additive M)) (s : Tate.T ℓ (Additive N))
    (hs : Tate.map (MonoidHom.toAdditive gN) s = s) :
    P.tatePairing (Tate.map (MonoidHom.toAdditive gM) t - t) s = 0 := by
  have h := P.tatePairing_map_eq_of_fix gM gN gμ hcov hμ t s
  rw [hs] at h
  rw [map_sub, LinearMap.sub_apply, h, sub_self]

/-- **The finite-level defect**: `e_{ℓᵏ}(g x · x⁻¹, y) = 1` for `y` fixed by `g`. -/
theorem e_defect_eq_one (gM : M →* M) (gN : N →* N) (gμ : Ωˣ →* Ωˣ)
    (hcov : ∀ (k : ℕ) (x : M) (y : N), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      P.e k (gM x) (gN y) = gμ (P.e k x y))
    (hμ : ∀ (k : ℕ) (u : Ωˣ), u ^ (ℓ ^ k) = 1 → gμ u = u)
    (k : ℕ) (x : M) (y : N) (hx : x ^ (ℓ ^ k) = 1) (hy : y ^ (ℓ ^ k) = 1) (hfix : gN y = y) :
    P.e k (gM x * x⁻¹) y = 1 := by
  rw [P.mul_left k _ _ _ (tors_map gM hx) (tors_inv hx) hy, P.e_inv_left k x y hx hy]
  have h1 : P.e k (gM x) y = gμ (P.e k x y) := by
    have h := hcov k x y hx hy
    rwa [hfix] at h
  rw [h1, hμ k _ (P.e_pow_eq_one k x y hx hy), mul_inv_cancel]

/-- **Left kernel**: finite-level left perfectness and lifting of `N[ℓᵏ]` to `T_ℓ N` give a trivial left
kernel. -/
theorem tatePairing_left_ker
    (hperf : ∀ (k : ℕ) (x : M), x ^ (ℓ ^ k) = 1 → (∀ y : N, y ^ (ℓ ^ k) = 1 → P.e k x y = 1) → x = 1)
    (hlift : ∀ (k : ℕ) (y : N), y ^ (ℓ ^ k) = 1 →
      ∃ s : Tate.T ℓ (Additive N), Additive.toMul (s.1 k) = y)
    (t : Tate.T ℓ (Additive M)) (ht : ∀ s, P.tatePairing t s = 0) : t = 0 := by
  apply Subtype.ext
  funext k
  have hx : Additive.toMul (t.1 k) = 1 := by
    refine hperf k _ (tors_of_tate t k) fun y hy => ?_
    obtain ⟨s, rfl⟩ := hlift k y hy
    have h := congrArg (fun z : TMu Ω ℓ => Additive.toMul (z.1 k)) (ht s)
    exact h
  change t.1 k = 0
  rw [← ofMul_toMul (t.1 k), hx]
  rfl

/-- **Right kernel**, symmetrically. -/
theorem tatePairing_right_ker
    (hperf : ∀ (k : ℕ) (y : N), y ^ (ℓ ^ k) = 1 → (∀ x : M, x ^ (ℓ ^ k) = 1 → P.e k x y = 1) → y = 1)
    (hlift : ∀ (k : ℕ) (x : M), x ^ (ℓ ^ k) = 1 →
      ∃ t : Tate.T ℓ (Additive M), Additive.toMul (t.1 k) = x)
    (s : Tate.T ℓ (Additive N)) (hs : ∀ t, P.tatePairing t s = 0) : s = 0 := by
  apply Subtype.ext
  funext k
  have hy : Additive.toMul (s.1 k) = 1 := by
    refine hperf k _ (tors_of_tate s k) fun x hx => ?_
    obtain ⟨t, rfl⟩ := hlift k x hx
    have h := congrArg (fun z : TMu Ω ℓ => Additive.toMul (z.1 k)) (hs t)
    exact h
  change s.1 k = 0
  rw [← ofMul_toMul (s.1 k), hy]
  rfl

end LevelPairing

end Generic

section Actual

open CategoryTheory MonObj
open scoped CategoryTheory.MonObj

variable {K : Type} [Field K]

/-- `T_ℓ(A)` over a `K`-field `Ω`, with the body of `ReductSplit.TΩ`. -/
abbrev TΩ (A : PkgI3.AbVar K) (Ω : Type) [Field Ω] [Algebra K Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  PkgI3.Tate.T ℓ (Additive (A.Pt Ω))

/-- The action of `σ ∈ Aut_K(Ω)` on `T_ℓ(A)`, with the body of `ReductSplit.galTΩ`. -/
def galTΩ (A : PkgI3.AbVar K) {Ω : Type} [Field Ω] [Algebra K Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Ω ≃ₐ[K] Ω) : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct σ))

variable (O : ValuationSubring K) {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

theorem wild_hμ (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω) (hσ : IsWildInertia w σ)
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : O)) (k : ℕ) (u : Ωˣ) (hu : u ^ (ℓ ^ k) = 1) :
    Units.map (σ : Ω →* Ω) u = u := by
  have hpow : IsUnit ((ℓ ^ k : ℕ) : O) := by
    rw [Nat.cast_pow]
    exact hℓ.pow k
  exact wild_units_fix O w hw σ hσ hpow hu

/-- **Wild invariance of the Tate pairing on the actual `T_ℓ(A)`.** For a level pairing on
`A(Ω) × N` that is covariant for the actual action `A.galAct σ` on points, an action `gN` on `N` and the
action of `σ` on `Ωˣ`, a wild `σ` preserves the limit pairing. -/
theorem wild_tatePairing_invariant (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hσ : IsWildInertia w σ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O)) (A : PkgI3.AbVar K)
    {N : Type*} [CommGroup N] (gN : N →* N) (P : LevelPairing ℓ (A.Pt Ω) N Ω)
    (hcov : ∀ (k : ℕ) (x : A.Pt Ω) (y : N), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      P.e k (A.galAct σ x) (gN y) = Units.map (σ : Ω →* Ω) (P.e k x y))
    (t : TΩ A Ω ℓ) (s : Tate.T ℓ (Additive N)) :
    P.tatePairing (galTΩ A ℓ σ t) (Tate.map (MonoidHom.toAdditive gN) s) = P.tatePairing t s :=
  P.tatePairing_map_eq_of_fix (A.galAct σ) gN (Units.map (σ : Ω →* Ω)) hcov
    (wild_hμ O w hw σ hσ ℓ hℓ) t s

/-- **Wild defects pair to zero with the `σ`-fixed part of the second factor.** -/
theorem wild_tatePairing_defect_eq_zero (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hσ : IsWildInertia w σ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O)) (A : PkgI3.AbVar K)
    {N : Type*} [CommGroup N] (gN : N →* N) (P : LevelPairing ℓ (A.Pt Ω) N Ω)
    (hcov : ∀ (k : ℕ) (x : A.Pt Ω) (y : N), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      P.e k (A.galAct σ x) (gN y) = Units.map (σ : Ω →* Ω) (P.e k x y))
    (t : TΩ A Ω ℓ) (s : Tate.T ℓ (Additive N)) (hs : Tate.map (MonoidHom.toAdditive gN) s = s) :
    P.tatePairing (galTΩ A ℓ σ t - t) s = 0 :=
  P.tatePairing_defect_eq_zero (A.galAct σ) gN (Units.map (σ : Ω →* Ω)) hcov
    (wild_hμ O w hw σ hσ ℓ hℓ) t s hs

/-- The case of a second abelian variety `B` (e.g. the dual) with its actual Galois action. -/
theorem wild_tatePairing_defect_eq_zero_abVar (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hσ : IsWildInertia w σ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O)) (A B : PkgI3.AbVar K)
    (P : LevelPairing ℓ (A.Pt Ω) (B.Pt Ω) Ω)
    (hcov : ∀ (k : ℕ) (x : A.Pt Ω) (y : B.Pt Ω), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      P.e k (A.galAct σ x) (B.galAct σ y) = Units.map (σ : Ω →* Ω) (P.e k x y))
    (t : TΩ A Ω ℓ) (s : TΩ B Ω ℓ) (hs : galTΩ B ℓ σ s = s) :
    P.tatePairing (galTΩ A ℓ σ t - t) s = 0 :=
  wild_tatePairing_defect_eq_zero O w hw σ hσ ℓ hℓ A (B.galAct σ) P hcov t s hs

end Actual

end WeilTate

#check @WeilTate.LevelPairing.tatePairing
#check @WeilTate.LevelPairing.tatePairing_map
#check @WeilTate.LevelPairing.tatePairing_defect_eq_zero
#check @WeilTate.LevelPairing.e_defect_eq_one
#check @WeilTate.LevelPairing.tatePairing_left_ker
#check @WeilTate.LevelPairing.tatePairing_right_ker
#check @WeilTate.wild_tatePairing_invariant
#check @WeilTate.wild_tatePairing_defect_eq_zero
#check @WeilTate.wild_tatePairing_defect_eq_zero_abVar
#print axioms WeilTate.LevelPairing.tatePairing
#print axioms WeilTate.LevelPairing.tatePairing_left_ker
#print axioms WeilTate.LevelPairing.tatePairing_right_ker
#print axioms WeilTate.LevelPairing.e_defect_eq_one
#print axioms WeilTate.wild_tatePairing_invariant
#print axioms WeilTate.wild_tatePairing_defect_eq_zero
#print axioms WeilTate.wild_tatePairing_defect_eq_zero_abVar
