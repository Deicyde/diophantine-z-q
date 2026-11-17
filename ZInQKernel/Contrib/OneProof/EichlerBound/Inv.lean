import ZInQKernel.Contrib.OneProof.EichlerBound.Key6

/-! eichler-bound, part B6: the lattice `𝔞 = {a ∈ k : c Ψ(a) ∈ 𝒪}` of an intertwiner is an invertible
`R`-submodule of `k` (so it has a class in `Pic R`), and equal classes give `𝒪^×`-conjugate embeddings.
No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k} (Bs : QBasis R)

theorem emb_comm (Ψ : OptEmb k R) (a b : k) : Ψ.1 a * Ψ.1 b = Ψ.1 b * Ψ.1 a := by
  rw [← map_mul, mul_comm, map_mul]

theorem subring_smul (r : R) (a : k) : r • a = (r : k) * a := rfl

/-- `𝔞(c) = {a ∈ k : c Ψ(a) ∈ 𝒪}`. -/
def latA (Ψ : OptEmb k R) (c : B) : Submodule R k where
  carrier := {a | c * Ψ.1 a ∈ LeafQM.O}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add, mul_add] at *; exact LeafQM.O.add_mem ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, mul_zero]; exact LeafQM.O.zero_mem
  smul_mem' r a ha := by
    simp only [Set.mem_setOf_eq] at *
    rw [subring_smul, map_mul, emb_comm, ← mul_assoc]
    exact LeafQM.O.mul_mem ha ((optEmb_mem Ψ _).2 r.2)

/-- `𝔟(c) = {b ∈ k : Ψ(b) c⁻¹ ∈ 𝒪}`. -/
def latB (Ψ : OptEmb k R) (c : B) : Submodule R k where
  carrier := {b | Ψ.1 b * qinv c ∈ LeafQM.O}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add, add_mul] at *; exact LeafQM.O.add_mem ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, zero_mul]; exact LeafQM.O.zero_mem
  smul_mem' r a ha := by
    simp only [Set.mem_setOf_eq] at *
    rw [subring_smul, map_mul, mul_assoc]
    exact LeafQM.O.mul_mem ((optEmb_mem Ψ _).2 r.2) ha

theorem mem_latA {Ψ : OptEmb k R} {c : B} {a : k} : a ∈ latA Ψ c ↔ c * Ψ.1 a ∈ LeafQM.O := Iff.rfl

theorem mem_latB {Ψ : OptEmb k R} {c : B} {b : k} : b ∈ latB Ψ c ↔ Ψ.1 b * qinv c ∈ LeafQM.O := Iff.rfl

theorem star_qinv (c : B) : star (qinv c) = (nrd c)⁻¹ • c := by
  unfold qinv; rw [star_smul, star_star, star_trivial]

theorem mem_one_iff {x : k} : x ∈ (1 : Submodule R k) ↔ x ∈ R := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

theorem latA_mul_latB_le {Ψ : OptEmb k R} {c : B} (hne : c ≠ 0) : latA Ψ c * latB Ψ c ≤ 1 := by
  rw [Submodule.mul_le]
  intro a ha b hb
  rw [mem_one_iff, ← optEmb_mem Ψ, mul_comm, map_mul,
    show Ψ.1 b * Ψ.1 a = (Ψ.1 b * qinv c) * (c * Ψ.1 a) by
      rw [mul_assoc, qinv_mul_cancel_left hne]]
  exact LeafQM.O.mul_mem hb ha

theorem sk_add (Ψ : OptEmb k R) (a b : k) : sk Ψ (a + b) = sk Ψ a + sk Ψ b := by
  apply emb_injective Ψ; rw [emb_sk, map_add, map_add, emb_sk, emb_sk, star_add]

theorem sk_mem_latAB {Ψ : OptEmb k R} {c : B} (hne : c ≠ 0) {x : k}
    (hx : x ∈ latA Ψ c * latB Ψ c) : sk Ψ x ∈ latA Ψ c * latB Ψ c := by
  have hn0 : nrd c ≠ 0 := nrd_ne_zero hne
  induction hx using Submodule.mul_induction_on' with
  | mem_mul_mem a ha b hb =>
    have hb' : sk Ψ b * ((nrd c)⁻¹ : ℚ) ∈ latA Ψ c := by
      rw [mem_latA, map_mul, emb_ratCast, emb_sk]
      have := star_mem hb
      rw [star_mul, star_qinv, smul_mul_assoc] at this
      rw [mul_coe_eq_smul, mul_smul_comm]; exact this
    have ha' : ((nrd c : ℚ) : k) * sk Ψ a ∈ latB Ψ c := by
      rw [mem_latB, map_mul, emb_ratCast, emb_sk, mul_assoc,
        show star (Ψ.1 a) * qinv c = (nrd c)⁻¹ • star (c * Ψ.1 a) by
          rw [star_mul, qinv, mul_smul_comm]]
      rw [coe_mul_eq_smul, smul_smul, mul_inv_cancel₀ hn0, one_smul]
      exact star_mem ha
    have : sk Ψ (a * b) = (sk Ψ b * ((nrd c)⁻¹ : ℚ)) * (((nrd c : ℚ) : k) * sk Ψ a) := by
      rw [sk_mul]
      have : ((nrd c)⁻¹ : ℚ) * (nrd c : ℚ) = (1 : ℚ) := inv_mul_cancel₀ hn0
      have h' : (((nrd c)⁻¹ : ℚ) : k) * ((nrd c : ℚ) : k) = 1 := by exact_mod_cast this
      linear_combination (-(sk Ψ a * sk Ψ b)) * h'
    rw [this]; exact Submodule.mul_mem_mul hb' ha'
  | add x _ y _ hx hy => rw [sk_add]; exact Submodule.add_mem _ hx hy

/-- `x s(x) = nrd Ψ(x)`. -/
theorem mul_sk (Ψ : OptEmb k R) (x : k) : x * sk Ψ x = ((nrd (Ψ.1 x) : ℚ) : k) := by
  apply emb_injective Ψ; rw [map_mul, emb_sk, mul_star_self', emb_ratCast]

theorem add_sk (Ψ : OptEmb k R) (x : k) : x + sk Ψ x = ((trd (Ψ.1 x) : ℚ) : k) := by
  unfold sk; ring

include Bs in
/-- **Lemma D**: an `s`-stable `R`-submodule `N ⊆ R` of `k` with `1 ∉ N` has a prime `ℓ` with `N · N ⊆ ℓR`. -/
theorem lemmaD (Ψ : OptEmb k R) (N : Submodule R k) (hN1 : N ≤ 1) (hs : ∀ x ∈ N, sk Ψ x ∈ N)
    (h1 : (1 : k) ∉ N) : ∃ ℓ : ℕ, ℓ.Prime ∧ ∀ x ∈ N, ∀ y ∈ N, ∃ r ∈ R, x * y = (ℓ : k) * r := by
  have hR : ∀ x ∈ N, x ∈ R := fun x hx => mem_one_iff.mp (hN1 hx)
  have hint : ∀ z : ℤ, ∀ x ∈ N, (z : k) * x ∈ N := fun z x hx => by
    have := N.smul_mem (⟨(z : k), _root_.intCast_mem R z⟩ : R) hx
    rwa [subring_smul] at this
  have hmul : ∀ x ∈ N, ∀ r ∈ R, r * x ∈ N := fun x hx r hr => by
    have := N.smul_mem (⟨r, hr⟩ : R) hx
    rwa [subring_smul] at this
  -- the integers in `N`
  by_cases hz : ∃ g : ℕ, 0 < g ∧ ((g : ℤ) : k) ∈ N
  · classical
    obtain ⟨hg0, hgN⟩ := Nat.find_spec hz
    set g := Nat.find hz
    have hgmin : ∀ m < g, ¬ (0 < m ∧ ((m : ℤ) : k) ∈ N) := fun m hm => Nat.find_min hz hm
    have hg1 : g ≠ 1 := by intro h; apply h1; rw [h] at hgN; simpa using hgN
    have hdvd : ∀ z : ℤ, (z : k) ∈ N → (g : ℤ) ∣ z := by
      intro z hzN
      have hrem : ((z % g : ℤ) : k) ∈ N := by
        have e : ((z % g : ℤ) : k) = (z : k) - ((z / g : ℤ) : k) * ((g : ℤ) : k) := by
          rw [Int.emod_def]; push_cast; ring
        rw [e]; exact N.sub_mem hzN (hint _ _ hgN)
      have h0 : 0 ≤ z % g := Int.emod_nonneg _ (by omega)
      have hlt : z % g < g := Int.emod_lt_of_pos _ (by omega)
      by_contra hnd
      have hne : z % g ≠ 0 := fun h => hnd (Int.dvd_of_emod_eq_zero h)
      apply hgmin (z % g).toNat (by omega)
      refine ⟨by omega, ?_⟩
      rw [Int.toNat_of_nonneg h0]; exact hrem
    set ℓ := g.minFac
    have hℓ : ℓ.Prime := Nat.minFac_prime hg1
    have hℓg : (ℓ : ℤ) ∣ g := Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd g)
    have hdvdℓ : ∀ z : ℤ, (z : k) ∈ N → (ℓ : ℤ) ∣ z := fun z hzN => hℓg.trans (hdvd z hzN)
    -- trace and norm of elements of `N` are divisible by `ℓ`
    have htrn : ∀ x ∈ N, ∃ T M : ℤ, x * x = (T : k) * x - (M : k) ∧ (ℓ : ℤ) ∣ T ∧ (ℓ : ℤ) ∣ M ∧
        trd (Ψ.1 x) = T ∧ nrd (Ψ.1 x) = M := by
      intro x hx
      obtain ⟨T, hT⟩ := trd_int ((optEmb_mem Ψ x).2 (hR x hx))
      obtain ⟨M, hM⟩ := nrd_int ((optEmb_mem Ψ x).2 (hR x hx))
      refine ⟨T, M, ?_, hdvdℓ T ?_, hdvdℓ M ?_, hT, hM⟩
      · apply emb_injective Ψ
        rw [map_mul, sq_eq_trd, map_sub, map_mul, emb_intCast, emb_intCast, hT, hM]
      · have := N.add_mem hx (hs x hx); rwa [add_sk, hT, Rat.cast_intCast] at this
      · have := hmul _ hx _ (hR _ (hs x hx)); rwa [mul_comm, mul_sk, hM, Rat.cast_intCast] at this
    refine ⟨ℓ, hℓ, fun x hx y hy => ?_⟩
    rcases hℓ.eq_two_or_odd with h2 | hodd
    · -- `ℓ = 2`: coordinates
      obtain ⟨X, Y, rfl⟩ := Bs.span x (hR x hx)
      obtain ⟨X', Y', rfl⟩ := Bs.span y (hR y hy)
      obtain ⟨T, M, -, hT, hM, hTe, hMe⟩ := htrn _ hx
      obtain ⟨T', M', -, hT', hM', hTe', hMe'⟩ := htrn _ hy
      have lin : ∀ U V : ℤ, Ψ.1 ((U : k) + (V : k) * Bs.ω) = ((U : ℚ) : B) + ((V : ℚ) : B) * Ψ.1 Bs.ω := by
        intro U V; rw [show ((U : k)) = ((U : ℚ) : k) by push_cast; rfl,
          show ((V : k)) = ((V : ℚ) : k) by push_cast; rfl, emb_lin]
      rw [lin, trd_add_mul, trd_omega] at hTe hTe'
      rw [lin, nrd_add_mul, trd_omega, nrd_omega] at hMe hMe'
      have e1 : T = 2 * X + Y * Bs.t := by exact_mod_cast hTe.symm
      have e2 : M = X ^ 2 + X * Y * Bs.t + Y ^ 2 * Bs.n := by exact_mod_cast hMe.symm
      have e3 : T' = 2 * X' + Y' * Bs.t := by exact_mod_cast hTe'.symm
      have e4 : M' = X' ^ 2 + X' * Y' * Bs.t + Y' ^ 2 * Bs.n := by exact_mod_cast hMe'.symm
      rw [h2] at hT hM hT' hM'
      obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := two_mul_cond X Y X' Y' Bs.t Bs.n
        (by rw [e1] at hT; simpa [mul_comm] using hT) (by rw [e2] at hM; convert hM using 1; ring)
        (by rw [e3] at hT'; simpa [mul_comm] using hT') (by rw [e4] at hM'; convert hM' using 1; ring)
      refine ⟨(p : k) + (q : k) * Bs.ω, R.add_mem (_root_.intCast_mem R p)
        (R.mul_mem (_root_.intCast_mem R q) Bs.mem), ?_⟩
      have hq' := Bs.quad
      have ep : ((X * X' - Bs.n * Y * Y' : ℤ) : k) = 2 * p := by rw [hp]; push_cast; ring
      have eq' : ((X * Y' + X' * Y + Bs.t * Y * Y' : ℤ) : k) = 2 * q := by rw [hq]; push_cast; ring
      push_cast at ep eq'
      rw [h2]; push_cast
      linear_combination (↑Y * ↑Y' : k) * hq' + ep + Bs.ω * eq'
    · -- `ℓ` odd
      have hsq : ∀ z ∈ N, ∃ r ∈ R, z * z = (ℓ : k) * r := by
        intro z hz
        obtain ⟨T, M, he, ⟨T1, hT1⟩, ⟨M1, hM1⟩, -, -⟩ := htrn z hz
        refine ⟨(T1 : k) * z - (M1 : k), R.sub_mem (R.mul_mem (_root_.intCast_mem R T1) (hR z hz))
          (_root_.intCast_mem R M1), ?_⟩
        rw [he, hT1, hM1]; push_cast; ring
      obtain ⟨r1, hr1, e1⟩ := hsq x hx
      obtain ⟨r2, hr2, e2⟩ := hsq y hy
      obtain ⟨r3, hr3, e3⟩ := hsq (x + y) (N.add_mem hx hy)
      have hcop : IsCoprime (2 : ℤ) (ℓ : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have : Nat.Coprime 2 ℓ := (Nat.coprime_primes Nat.prime_two hℓ).mpr (by omega)
        exact_mod_cast this
      obtain ⟨u, v, huv⟩ := hcop
      refine ⟨(u : k) * (r3 - r1 - r2) + (v : k) * (x * y), ?_, ?_⟩
      · exact R.add_mem (R.mul_mem (_root_.intCast_mem R u) (R.sub_mem (R.sub_mem hr3 hr1) hr2))
          (R.mul_mem (_root_.intCast_mem R v) (R.mul_mem (hR x hx) (hR y hy)))
      · have huv' : (u : k) * 2 + (v : k) * (ℓ : k) = 1 := by exact_mod_cast huv
        linear_combination (-(x * y)) * huv' + (u : k) * e3 - (u : k) * e1 - (u : k) * e2
  · -- `N ∩ ℤ = 0`, so `N = 0`
    push Not at hz
    have hN0 : ∀ x ∈ N, x = 0 := by
      intro x hx
      obtain ⟨M, hM⟩ := nrd_int ((optEmb_mem Ψ x).2 (hR x hx))
      have hMN : ((M : ℤ) : k) ∈ N := by
        have := hmul _ hx _ (hR _ (hs x hx)); rwa [mul_comm, mul_sk, hM, Rat.cast_intCast] at this
      have hM0 : M = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · have := hint (-1) _ hMN
          have h' := hz M.natAbs (by omega)
          apply h'
          rw [show ((M.natAbs : ℕ) : ℤ) = -1 * M by omega]; push_cast at this ⊢; exact this
        · have h' := hz M.natAbs (by omega)
          apply h'
          rw [show ((M.natAbs : ℕ) : ℤ) = M by omega]; exact hMN
      rw [hM0, Int.cast_zero] at hM
      exact emb_injective Ψ (by rw [map_zero]; exact nrd_eq_zero_iff.mp hM)
    refine ⟨2, Nat.prime_two, fun x hx y hy => ⟨0, R.zero_mem, ?_⟩⟩
    rw [hN0 x hx]; ring

end Emb

end EichlerBound
