import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import ZInQKernel.Hypotheses.TYZInputs

/-!
# Proposition N in Lean: `TYZInputs → TYZRow5b`

The Lean proof of Proposition N (`docs/research/nt-tyz.md` §4): for squarefree `n ≡ 5 (mod 8)`,
`𝓛(n) = 0` forces both genus sums `T5aCl n` and `T5bCl n` to vanish, so `T5bCl n = 1` gives
analytic rank at most one. The hypothesis is `TYZInputs` (`Hypotheses/TYZInputs.lean`), the
encoding of the Tian–Yuan–Zhang results I1–I7 that the argument uses. This file replaces the two
model reviews of the argument (`docs/research/rv-nt-tyz.md`, `docs/research/rv-prop-n.md`) by a
kernel-checked proof from that encoding; the faithfulness of the encoding to TYZ is the subject
of `docs/research/pn-design.md` §2, `docs/research/rv-tyz-inputs.md` and
`docs/research/rv-pn-encoding.md`. The one residual doubt of rv-tyz-inputs, T1 (the constant of
TYZ Theorem 3.3, whose computation TYZ do not print, L2014–2015), is closed by
`docs/research/tyz-t1.md`: Theorem 3.3 holds as printed; the constant does not depend on `d₁` for
fixed `d₀` (written out from TYZ's Theorem A.9, and checked on 30 values of `n`, 73 pairs, from
Heegner points on `X₀(32)`). What remains external is Theorem A.9 itself, the Yuan–Zhang–Zhang
Gross–Zagier formula made explicit by TYZ.

Design: `docs/research/pn-design.md`. Main steps:

* `lemmaN1_core`, `lemmaN1` — Lemma N1: `𝓛(m) ≡ Λ(m) (mod 2)` for squarefree `m ≡ 1, 3`, where
  `Λ` (`Lam`, nt-tyz §4.3) is a sum over set partitions of the primes of `m`; `lemmaN1_core` is
  the combinatorial identity, `lemmaN1` the uniqueness induction from Lemma 2.9 (the hypothesis
  `LemmaTwoEight`, whose name is historical: it encodes TYZ's convolution Lemma 2.9, and TYZ's
  Lemma 2.8 is the symmetry lemma; locator corrected 2026-11-12 after
  `docs/research/locators.md`);
* `lemmaN2` — Lemma N2 in its `𝓛`-form: `P(n) = Σ_e 𝓛(n/e) Z(e) + 2X`;
* `finalStep` — §4.4: if `𝓛(n) = 0`, the integers `Σ_{e≡5} 𝓛(n/e) g(e)` and
  `Σ_{e≡7} 𝓛(n/e) g(e)` are even;
* `matching` — `Σ_{e≡5} Λ(n/e) g(e) = T5aCl n` and `Σ_{e≡7} Λ(n/e) g(e) = T5bCl n` in `𝔽₂`;
* `genusSums_eq_zero`, `tyzRow5b_of_tyzInputs`, `tyzThm35ReadingA_of_tyzInputs` (reading A of
  TYZ Theorem 3.5(2), both rows; TYZ's Theorem 1.2, journal Theorem 1.4, is not used), and `Witness.genusData_nonempty`,
  `Witness.genusData_nonempty_iff_parities` (consistency of `GenusData`: for `L n ≠ 0` it is always
  inhabited; for `L n = 0` exactly when the two parities of `finalStep` hold).
-/

noncomputable section

namespace ZInQ.PropN

open ZInQ.Literature ZInQ.RouteK.Rank5b

/-! ### `Λ` (nt-tyz §4.3) -/

/-- The partitions counted by `Λ(m)`: all blocks `≡ 1` or `3 (mod 8)`, at most one block `≡ 3`
(for `m ≡ 1` this means none, for `m ≡ 3` exactly one). -/
def LamAdm (m : ℕ) (P : Finpartition (Finset.univ : Finset m.primeFactors)) : Prop :=
  (∀ B ∈ P.parts, dProd B % 8 = 1 ∨ dProd B % 8 = 3) ∧
  (P.parts.filter fun B => dProd B % 8 = 3).card ≤ 1

instance (m : ℕ) (P : Finpartition (Finset.univ : Finset m.primeFactors)) :
    Decidable (LamAdm m P) := by
  unfold LamAdm; infer_instance

/-- `Λ(m) = Σ_π Π_{B∈π} g(d_B)` over the set partitions of the primes of `m` counted by `LamAdm`
(nt-tyz §4.3): `Λ(m) = 𝓛₁(m)` for `m ≡ 1`, `Λ(m) = Σ_{d≡3} g(d)𝓛₁(m/d)` for `m ≡ 3`, `Λ(1) = 1`. -/
def Lam (m : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset m.primeFactors),
    if LamAdm m P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

/-! ### The four lemmas -/

/-! ### part: partition sets -/

section part_generic

variable {α : Type*} [DecidableEq α]

/-- `Q` is the set of blocks of a set partition of `s`. -/
def part_IsP (s : Finset α) (Q : Finset (Finset α)) : Prop :=
  (∀ B ∈ Q, ∀ C ∈ Q, B ≠ C → Disjoint B C) ∧ Q.sup id = s ∧ ∅ ∉ Q

instance part_decIsP (s : Finset α) : DecidablePred (part_IsP s) := fun Q => by
  unfold part_IsP; infer_instance

/-- The finset of the block sets of the set partitions of `s`. -/
def part_PS (s : Finset α) : Finset (Finset (Finset α)) :=
  s.powerset.powerset.filter (part_IsP s)

theorem part_mem_sup {Q : Finset (Finset α)} {x : α} : x ∈ Q.sup id ↔ ∃ B ∈ Q, x ∈ B := by
  simp [Finset.mem_sup]

theorem part_subset_of_mem {s : Finset α} {Q : Finset (Finset α)} (h : part_IsP s Q)
    {B : Finset α} (hB : B ∈ Q) : B ⊆ s := by
  rw [← h.2.1]; exact Finset.le_sup (f := id) hB

theorem part_mem_PS {s : Finset α} {Q : Finset (Finset α)} : Q ∈ part_PS s ↔ part_IsP s Q := by
  unfold part_PS
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨fun B hB => Finset.mem_powerset.mpr (part_subset_of_mem h hB), h⟩⟩

theorem part_sup_sdiff {s : Finset α} {Q S : Finset (Finset α)} (h : part_IsP s Q) (hS : S ⊆ Q) :
    (Q \ S).sup id = s \ S.sup id := by
  ext x
  rw [Finset.mem_sdiff, part_mem_sup, part_mem_sup, ← h.2.1, part_mem_sup]
  constructor
  · rintro ⟨B, hB, hxB⟩
    rw [Finset.mem_sdiff] at hB
    refine ⟨⟨B, hB.1, hxB⟩, ?_⟩
    rintro ⟨C, hCS, hxC⟩
    have hBC : B ≠ C := fun e => hB.2 (e ▸ hCS)
    exact Finset.disjoint_left.mp (h.1 B hB.1 C (hS hCS) hBC) hxB hxC
  · rintro ⟨⟨B, hBQ, hxB⟩, hn⟩
    exact ⟨B, Finset.mem_sdiff.mpr ⟨hBQ, fun hBS => hn ⟨B, hBS, hxB⟩⟩, hxB⟩

theorem part_IsP_sdiff {s : Finset α} {Q S : Finset (Finset α)} (h : part_IsP s Q) (hS : S ⊆ Q) :
    part_IsP (s \ S.sup id) (Q \ S) :=
  ⟨fun B hB C hC => h.1 B (Finset.sdiff_subset hB) C (Finset.sdiff_subset hC),
    part_sup_sdiff h hS, fun h0 => h.2.2 (Finset.sdiff_subset h0)⟩

theorem part_IsP_subset {s : Finset α} {Q S : Finset (Finset α)} (h : part_IsP s Q) (hS : S ⊆ Q) :
    part_IsP (S.sup id) S :=
  ⟨fun B hB C hC => h.1 B (hS hB) C (hS hC), rfl, fun h0 => h.2.2 (hS h0)⟩

theorem part_IsP_parts {s : Finset α} (P : Finpartition s) : part_IsP s P.parts :=
  ⟨fun _ hB _ hC hBC => P.disjoint hB hC hBC, P.sup_parts, P.bot_notMem⟩

/-- The set partition with block set `Q`. -/
def part_toFP {s : Finset α} {Q : Finset (Finset α)} (h : part_IsP s Q) : Finpartition s where
  parts := Q
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun B hB C hC hBC => h.1 B hB C hC hBC
  sup_parts := h.2.1
  bot_notMem := h.2.2

theorem part_sum_fp {M : Type*} [AddCommMonoid M] (s : Finset α) (G : Finset (Finset α) → M) :
    ∑ P : Finpartition s, G P.parts = ∑ Q ∈ part_PS s, G Q :=
  Finset.sum_bij (fun P _ => P.parts) (fun P _ => part_mem_PS.mpr (part_IsP_parts P))
    (fun _ _ _ _ h => Finpartition.ext h)
    (fun _ hQ => ⟨part_toFP (part_mem_PS.mp hQ), Finset.mem_univ _, rfl⟩) (fun _ _ => rfl)

theorem part_sum_subtype {M : Type*} [AddCommMonoid M] (t : Finset α)
    (G : Finset (Finset α) → M) :
    ∑ Q ∈ part_PS (Finset.univ : Finset t),
      G (Q.image fun B => B.map (Function.Embedding.subtype _)) = ∑ R ∈ part_PS t, G R := by
  set φ : Finset t → Finset α := fun B => B.map (Function.Embedding.subtype _) with hφ
  set ψ : Finset α → Finset t := fun B => B.subtype (· ∈ t) with hψ
  have hψφ : ∀ B, ψ (φ B) = B := by
    intro B; ext x; simp [hψ, hφ]
  have hφψ : ∀ B ⊆ t, φ (ψ B) = B := fun B hB => Finset.subtype_map_of_mem hB
  have hφinj : Function.Injective φ := Finset.map_injective _
  refine Finset.sum_nbij' (fun Q => Q.image φ) (fun R => R.image ψ) ?_ ?_ ?_ ?_
    (fun _ _ => rfl)
  · intro Q hQ
    have h := part_mem_PS.mp hQ
    refine part_mem_PS.mpr ⟨?_, ?_, ?_⟩
    · simp only [Finset.mem_image]
      rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ hBC
      exact Finset.disjoint_map _ |>.mpr (h.1 B hB C hC fun e => hBC (e ▸ rfl))
    · ext x
      rw [part_mem_sup]
      constructor
      · rintro ⟨_, hB, hxB⟩
        obtain ⟨B, -, rfl⟩ := Finset.mem_image.mp hB
        obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hxB
        exact y.2
      · intro hx
        have : (⟨x, hx⟩ : t) ∈ Q.sup id := h.2.1 ▸ Finset.mem_univ _
        obtain ⟨B, hB, hxB⟩ := part_mem_sup.mp this
        exact ⟨φ B, Finset.mem_image_of_mem _ hB, Finset.mem_map.mpr ⟨_, hxB, rfl⟩⟩
    · intro h0
      obtain ⟨B, hB, hB0⟩ := Finset.mem_image.mp h0
      rw [hφ, Finset.map_eq_empty] at hB0
      exact h.2.2 (hB0 ▸ hB)
  · intro R hR
    have h := part_mem_PS.mp hR
    refine part_mem_PS.mpr ⟨?_, ?_, ?_⟩
    · simp only [Finset.mem_image]
      rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ hBC
      have hd := h.1 B hB C hC fun e => hBC (e ▸ rfl)
      rw [Finset.disjoint_left] at hd ⊢
      intro x hxB hxC
      exact hd (Finset.mem_subtype.mp hxB) (Finset.mem_subtype.mp hxC)
    · ext ⟨x, hx⟩
      simp only [Finset.mem_univ, iff_true]
      rw [← h.2.1, part_mem_sup] at hx
      obtain ⟨B, hB, hxB⟩ := hx
      exact part_mem_sup.mpr ⟨ψ B, Finset.mem_image_of_mem _ hB, Finset.mem_subtype.mpr hxB⟩
    · intro h0
      obtain ⟨B, hB, hB0⟩ := Finset.mem_image.mp h0
      have := hφψ B (part_subset_of_mem h hB)
      rw [hB0] at this
      have hB' : B = ∅ := by rw [← this]; simp [hφ]
      exact h.2.2 (hB' ▸ hB)
  · intro Q _
    simp only [Finset.image_image]
    rw [show ψ ∘ φ = id from funext hψφ, Finset.image_id]
  · intro R hR
    have h := part_mem_PS.mp hR
    simp only [Finset.image_image]
    rw [Finset.image_congr (f := φ ∘ ψ) (g := id) (fun B hB => hφψ B (part_subset_of_mem h hB)),
      Finset.image_id]

end part_generic

/-! ### part: block sets of primes -/

/-- The weight `Π_{B ∈ Q} g(d_B)` of a block set. -/
def part_wt (Q : Finset (Finset ℕ)) : ZMod 2 := ∏ B ∈ Q, ((gNat (∏ p ∈ B, p) : ℕ) : ZMod 2)

/-- `LamAdm` on block sets. -/
def part_LamAdm (Q : Finset (Finset ℕ)) : Prop :=
  (∀ B ∈ Q, (∏ p ∈ B, p) % 8 = 1 ∨ (∏ p ∈ B, p) % 8 = 3) ∧
  (Q.filter fun B => (∏ p ∈ B, p) % 8 = 3).card ≤ 1

instance part_decLamAdm : DecidablePred part_LamAdm := fun Q => by
  unfold part_LamAdm; infer_instance

/-- `Λ` on a finset of primes. -/
def part_LamS (s : Finset ℕ) : ZMod 2 :=
  ∑ Q ∈ part_PS s, if part_LamAdm Q then part_wt Q else 0

theorem part_gNat_eq (e : ℕ) [NeZero e] : gNat e = gCl e := by
  unfold gNat; rw [dite_eq_right (NeZero.ne e)]

theorem part_prod_map {m : ℕ} (B : Finset m.primeFactors) :
    ∏ p ∈ B.map (Function.Embedding.subtype _), p = dProd B := by
  rw [Finset.prod_map]; rfl

theorem part_transport (m : ℕ) (A' : Finset (Finset ℕ) → Prop) [DecidablePred A']
    (F : Finpartition (Finset.univ : Finset m.primeFactors) → ZMod 2)
    (hF : ∀ P, F P = if A' (P.parts.image fun B => B.map (Function.Embedding.subtype _))
      then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0) :
    ∑ P, F P = ∑ R ∈ part_PS m.primeFactors, if A' R then part_wt R else 0 := by
  have hφinj : Function.Injective
      (fun B : Finset m.primeFactors => B.map (Function.Embedding.subtype _)) :=
    Finset.map_injective _
  rw [Finset.sum_congr rfl fun P _ => hF P,
    part_sum_fp (Finset.univ : Finset m.primeFactors) (fun Q =>
      if A' (Q.image fun B => B.map (Function.Embedding.subtype _))
      then ∏ B ∈ Q, ((gCl (dProd B) : ℕ) : ZMod 2) else 0),
    ← part_sum_subtype m.primeFactors]
  refine Finset.sum_congr rfl fun Q _ => ?_
  refine if_congr Iff.rfl ?_ rfl
  rw [part_wt, Finset.prod_image fun B _ C _ h => hφinj h]
  refine Finset.prod_congr rfl fun B _ => ?_
  rw [part_prod_map, part_gNat_eq]

theorem part_card_filter_image {m : ℕ} (Q : Finset (Finset m.primeFactors)) (c : ℕ) :
    ((Q.image fun B => B.map (Function.Embedding.subtype _)).filter
      fun B => (∏ p ∈ B, p) % 8 = c).card = (Q.filter fun B => dProd B % 8 = c).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (Finset.map_injective _)]
  simp only [part_prod_map]

theorem part_Lam_eq (m : ℕ) : Lam m = part_LamS m.primeFactors := by
  refine part_transport m part_LamAdm _ fun P => if_congr ?_ rfl rfl
  simp only [LamAdm, part_LamAdm, Finset.forall_mem_image, part_prod_map,
    part_card_filter_image]

theorem part_prod_IsP {t : Finset ℕ} {R : Finset (Finset ℕ)} (h : part_IsP t R) :
    ∏ p ∈ t, p = ∏ B ∈ R, ∏ p ∈ B, p := by
  conv_lhs => rw [← h.2.1, Finset.sup_eq_biUnion]
  exact Finset.prod_biUnion fun B hB C hC hBC => h.1 B hB C hC hBC

theorem part_pow3 {R : Finset (Finset ℕ)}
    (hR : ∀ B ∈ R, (∏ p ∈ B, p) % 8 = 1 ∨ (∏ p ∈ B, p) % 8 = 3) :
    (∏ B ∈ R, ∏ p ∈ B, p) % 8 = 3 ^ (R.filter fun B => (∏ p ∈ B, p) % 8 = 3).card % 8 := by
  rw [← Finset.prod_filter_mul_prod_filter_not R (fun B => (∏ p ∈ B, p) % 8 = 3), Nat.mul_mod,
    Finset.prod_nat_mod, Finset.prod_nat_mod (Finset.filter (fun B => ¬ _) R)]
  have h1 : ∏ B ∈ R.filter (fun B => (∏ p ∈ B, p) % 8 = 3), (∏ p ∈ B, p) % 8 =
      ∏ B ∈ R.filter (fun B => (∏ p ∈ B, p) % 8 = 3), 3 :=
    Finset.prod_congr rfl fun B hB => (Finset.mem_filter.mp hB).2
  have h2 : ∏ B ∈ R.filter (fun B => ¬ (∏ p ∈ B, p) % 8 = 3), (∏ p ∈ B, p) % 8 =
      ∏ B ∈ R.filter (fun B => ¬ (∏ p ∈ B, p) % 8 = 3), 1 := by
    refine Finset.prod_congr rfl fun B hB => ?_
    have := Finset.mem_filter.mp hB
    rcases hR B this.1 with h | h
    · exact h
    · exact absurd h this.2
  rw [h1, h2, Finset.prod_const, Finset.prod_const_one]
  simp [Nat.pow_mod]

theorem part_adm_one {t : Finset ℕ} {R : Finset (Finset ℕ)} (h : part_IsP t R)
    (ht : (∏ p ∈ t, p) % 8 = 1) : part_LamAdm R ↔ ∀ B ∈ R, (∏ p ∈ B, p) % 8 = 1 := by
  constructor
  · rintro ⟨h13, hk⟩
    have h3 := part_pow3 h13
    rw [← part_prod_IsP h, ht] at h3
    have hk0 : (R.filter fun B => (∏ p ∈ B, p) % 8 = 3).card = 0 := by
      interval_cases hc : (R.filter fun B => (∏ p ∈ B, p) % 8 = 3).card
      · rfl
      · norm_num at h3
    intro B hB
    rcases h13 B hB with h1 | h1
    · exact h1
    · have : B ∈ R.filter fun B => (∏ p ∈ B, p) % 8 = 3 := Finset.mem_filter.mpr ⟨hB, h1⟩
      rw [Finset.card_eq_zero.mp hk0] at this
      exact absurd this (Finset.notMem_empty _)
  · intro h1
    refine ⟨fun B hB => Or.inl (h1 B hB), ?_⟩
    rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun B hB => by rw [h1 B hB]; norm_num)]
    norm_num

theorem part_adm_three {t : Finset ℕ} {R : Finset (Finset ℕ)} (h : part_IsP t R)
    (ht : (∏ p ∈ t, p) % 8 = 3) : part_LamAdm R ↔
      (∀ B ∈ R, (∏ p ∈ B, p) % 8 = 1 ∨ (∏ p ∈ B, p) % 8 = 3) ∧
      (R.filter fun B => (∏ p ∈ B, p) % 8 = 3).card = 1 := by
  constructor
  · rintro ⟨h13, hk⟩
    have h3 := part_pow3 h13
    rw [← part_prod_IsP h, ht] at h3
    refine ⟨h13, ?_⟩
    interval_cases hc : (R.filter fun B => (∏ p ∈ B, p) % 8 = 3).card
    · norm_num at h3
    · rfl
  · rintro ⟨h13, hk⟩
    exact ⟨h13, hk.le⟩

theorem part_sum_divisors {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : Squarefree n)
    (p : ℕ → Prop) [DecidablePred p] (f : ℕ → M) :
    ∑ e ∈ n.divisors.filter p, f e =
      ∑ B ∈ n.primeFactors.powerset.filter (fun B => p (∏ q ∈ B, q)), f (∏ q ∈ B, q) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  symm
  refine Finset.sum_nbij' (fun B => ∏ q ∈ B, q) (fun e => e.primeFactors) ?_ ?_ ?_ ?_
    (fun _ _ => rfl)
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hn0⟩, hB.2⟩
    calc ∏ q ∈ B, q ∣ ∏ q ∈ n.primeFactors, q := Finset.prod_dvd_prod_of_subset _ _ _ hB.1
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Nat.primeFactors_mono he.1.1 hn0), ?_⟩
    rw [Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd he.1.1)]; exact he.2
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB
    exact Nat.primeFactors_prod fun q hq => Nat.prime_of_mem_primeFactors (hB.1 hq)
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    exact Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd he.1.1)

theorem part_Lam_prod {n : ℕ} {B : Finset ℕ} (hB : B ⊆ n.primeFactors) :
    Lam (∏ q ∈ B, q) = part_LamS B := by
  rw [part_Lam_eq, Nat.primeFactors_prod fun q hq => Nat.prime_of_mem_primeFactors (hB hq)]

theorem part_Lam_div {n : ℕ} (hn : Squarefree n) {B : Finset ℕ} (hB : B ⊆ n.primeFactors) :
    Lam (n / ∏ q ∈ B, q) = part_LamS (n.primeFactors \ B) := by
  rw [← Nat.prod_primeFactors_sdiff_of_squarefree hn hB, part_Lam_eq,
    Nat.primeFactors_prod fun q hq => Nat.prime_of_mem_primeFactors (Finset.sdiff_subset hq)]

/-- The class mod 8 of the complement of `B` in the primes of squarefree `n`. -/
theorem part_mod_sdiff {n : ℕ} (hn : Squarefree n) {B : Finset ℕ} (hB : B ⊆ n.primeFactors)
    {a b c : ℕ} (hna : n % 8 = a) (hBb : (∏ q ∈ B, q) % 8 = b)
    (habc : ∀ x : ℕ, x < 8 → (x * b) % 8 = a → x = c) :
    (∏ q ∈ n.primeFactors \ B, q) % 8 = c := by
  have h := Nat.mul_mod (∏ q ∈ n.primeFactors \ B, q) (∏ q ∈ B, q) 8
  rw [Finset.prod_sdiff hB, Nat.prod_primeFactors_of_squarefree hn, hna, hBb] at h
  exact habc _ (Nat.mod_lt _ (by norm_num)) h.symm

theorem part_ne_empty_of_mod {B : Finset ℕ} {c : ℕ} (hc : c ≠ 1) (h : (∏ q ∈ B, q) % 8 = c) :
    B ≠ ∅ := by
  rintro rfl; simp at h; omega

theorem part_not_mem_of_ne_empty {t B : Finset ℕ} {R : Finset (Finset ℕ)}
    (hR : part_IsP (t \ B) R) (hB0 : B ≠ ∅) : B ∉ R := by
  intro hBR
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hB0
  exact (Finset.mem_sdiff.mp (part_subset_of_mem hR hBR hx)).2 hx

/-! ### part: lemmaN1_core -/

section part_gen2

variable {α : Type*} [DecidableEq α]

theorem part_PS_empty : part_PS (∅ : Finset α) = {∅} := by
  ext Q
  rw [part_mem_PS, Finset.mem_singleton]
  constructor
  · intro h
    refine Finset.eq_empty_of_forall_notMem fun B hB => h.2.2 ?_
    have := part_subset_of_mem h hB
    rwa [Finset.subset_empty.mp this] at hB
  · rintro rfl
    exact ⟨fun B hB => absurd hB (Finset.notMem_empty _), Finset.sup_empty, Finset.notMem_empty _⟩

theorem part_IsP_single {s : Finset α} (hs : s ≠ ∅) : part_IsP s {s} := by
  refine ⟨fun B hB C hC hBC => ?_, Finset.sup_singleton, fun h => hs (Finset.mem_singleton.mp h).symm⟩
  rw [Finset.mem_singleton] at hB hC
  exact absurd (hB.trans hC.symm) hBC

theorem part_eq_single {s : Finset α} {π : Finset (Finset α)} (hπ : part_IsP s π) (hs : s ≠ ∅)
    (hc : π.card ≤ 1) : π = {s} := by
  have hne : π ≠ ∅ := by
    rintro rfl; exact hs (hπ.2.1.symm.trans Finset.sup_empty)
  obtain ⟨B, rfl⟩ := Finset.card_eq_one.mp
    (le_antisymm hc (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)))
  rw [← hπ.2.1, Finset.sup_singleton]; rfl

theorem part_disjoint_PS {s A : Finset α} {Q₁ Q₂ : Finset (Finset α)} (h₁ : part_IsP A Q₁)
    (h₂ : part_IsP (s \ A) Q₂) : Disjoint Q₁ Q₂ := by
  rw [Finset.disjoint_left]
  intro B hB₁ hB₂
  have hB : B = ∅ := by
    ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    exact (Finset.mem_sdiff.mp (part_subset_of_mem h₂ hB₂ hx)).2 (part_subset_of_mem h₁ hB₁ hx)
  exact h₁.2.2 (hB ▸ hB₁)

/-- **Product lemma**: pairs of partitions of `A ⊆ s` and of `s \ A` are the pairs `(π, S)` of a
partition `π` of `s` and a subset `S ⊆ π` (with `A = ⋃ S`). -/
theorem part_prod_lemma {M : Type*} [AddCommMonoid M] (s : Finset α)
    (F : Finset (Finset α) → Finset (Finset α) → M) :
    ∑ A ∈ s.powerset, ∑ Q₁ ∈ part_PS A, ∑ Q₂ ∈ part_PS (s \ A), F Q₁ Q₂ =
      ∑ π ∈ part_PS s, ∑ S ∈ π.powerset, F S (π \ S) := by
  simp only [← Finset.sum_product' (f := F)]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2.1 ∪ x.2.2, x.2.1⟩)
    (fun y => ⟨y.2.sup id, (y.2, y.1 \ y.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A, Q₁, Q₂⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product] at hx
    obtain ⟨hA, hQ₁, hQ₂⟩ := hx
    have h₁ := part_mem_PS.mp hQ₁
    have h₂ := part_mem_PS.mp hQ₂
    simp only [Finset.mem_sigma, Finset.mem_powerset]
    refine ⟨part_mem_PS.mpr ⟨?_, ?_, ?_⟩, Finset.subset_union_left⟩
    · intro X hX Y hY hXY
      rw [Finset.mem_union] at hX hY
      rcases hX with hX | hX <;> rcases hY with hY | hY
      · exact h₁.1 X hX Y hY hXY
      · exact Finset.disjoint_of_subset_left (part_subset_of_mem h₁ hX)
          (Finset.disjoint_of_subset_right (part_subset_of_mem h₂ hY) Finset.disjoint_sdiff)
      · exact Finset.disjoint_of_subset_left (part_subset_of_mem h₂ hX)
          (Finset.disjoint_of_subset_right (part_subset_of_mem h₁ hY) Finset.sdiff_disjoint)
      · exact h₂.1 X hX Y hY hXY
    · rw [Finset.sup_union, h₁.2.1, h₂.2.1]; exact Finset.union_sdiff_of_subset hA
    · rw [Finset.mem_union]; rintro (h | h)
      · exact h₁.2.2 h
      · exact h₂.2.2 h
  · rintro ⟨π, S⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hy
    obtain ⟨hπ, hS⟩ := hy
    have h := part_mem_PS.mp hπ
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product]
    refine ⟨?_, part_mem_PS.mpr (part_IsP_subset h hS), part_mem_PS.mpr (part_IsP_sdiff h hS)⟩
    rw [← h.2.1]; exact Finset.sup_mono hS
  · rintro ⟨A, Q₁, Q₂⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product] at hx
    have h₁ := part_mem_PS.mp hx.2.1
    have h₂ := part_mem_PS.mp hx.2.2
    simp only
    rw [h₁.2.1, Finset.union_sdiff_cancel_left (part_disjoint_PS h₁ h₂)]
  · rintro ⟨π, S⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hy
    simp only
    rw [Finset.union_sdiff_of_subset hy.2]
  · rintro ⟨A, Q₁, Q₂⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product] at hx
    have h₁ := part_mem_PS.mp hx.2.1
    have h₂ := part_mem_PS.mp hx.2.2
    simp only
    rw [Finset.union_sdiff_cancel_left (part_disjoint_PS h₁ h₂)]

theorem part_two_pow_smul (k : ℕ) (c : ZMod 2) : (2 ^ k : ℕ) • c = if k = 0 then c else 0 := by
  split_ifs with hk
  · subst hk; simp
  · rw [nsmul_eq_mul, Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 from ZMod.natCast_self 2,
      zero_pow hk, zero_mul]

theorem part_count_subset {π X : Finset (Finset α)} (hX : X ⊆ π) (c : ZMod 2) :
    ∑ S ∈ π.powerset, (if S ⊆ X then c else 0) = if X = ∅ then c else 0 := by
  rw [← Finset.sum_filter]
  have : π.powerset.filter (· ⊆ X) = X.powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hX, h⟩⟩
  rw [this, Finset.sum_const, Finset.card_powerset, part_two_pow_smul]
  simp only [Finset.card_eq_zero]

theorem part_count_mem {π : Finset (Finset α)} {B₀ : Finset α} (hB₀ : B₀ ∈ π) (c : ZMod 2) :
    ∑ S ∈ π.powerset, (if B₀ ∈ S then c else 0) = if π.card = 1 then c else 0 := by
  rw [← Finset.insert_erase hB₀, Finset.sum_powerset_insert (Finset.notMem_erase _ _),
    Finset.card_insert_of_notMem (Finset.notMem_erase _ _)]
  rw [Finset.sum_eq_zero fun t ht => ite_eq_right fun h =>
    Finset.notMem_erase B₀ π (Finset.mem_powerset.mp ht h), zero_add]
  simp only [Finset.mem_insert_self, ite_true]
  rw [Finset.sum_const, Finset.card_powerset, part_two_pow_smul]
  simp

end part_gen2

theorem part_LamS_empty : part_LamS ∅ = 1 := by
  rw [part_LamS, part_PS_empty, Finset.sum_singleton, ite_eq_left]
  · simp [part_wt]
  · exact ⟨fun B hB => absurd hB (Finset.notMem_empty _), by simp⟩

theorem part_Lam_one : Lam 1 = 1 := by
  rw [part_Lam_eq, Nat.primeFactors_one, part_LamS_empty]

theorem part_adm_of_all_one {R : Finset (Finset ℕ)} (h : ∀ B ∈ R, (∏ p ∈ B, p) % 8 = 1) :
    part_LamAdm R := by
  refine ⟨fun B hB => Or.inl (h B hB), ?_⟩
  rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun B hB => by rw [h B hB]; norm_num)]
  norm_num

theorem part_mod_one_of_all {t : Finset ℕ} {S : Finset (Finset ℕ)} (h : part_IsP t S)
    (h1 : ∀ B ∈ S, (∏ p ∈ B, p) % 8 = 1) : (∏ p ∈ t, p) % 8 = 1 := by
  rw [part_prod_IsP h, Finset.prod_nat_mod, Finset.prod_congr rfl h1, Finset.prod_const_one]
  norm_num

theorem part_wt_split {π S : Finset (Finset ℕ)} (hS : S ⊆ π) :
    part_wt S * part_wt (π \ S) = part_wt π := by
  rw [mul_comm]; exact Finset.prod_sdiff hS

/-- The inner sum for `m ≡ 3`: only `S` made of class-1 blocks contribute. -/
theorem part_inner3 {s : Finset ℕ} {π : Finset (Finset ℕ)} (hπ : part_IsP s π) :
    ∑ S ∈ π.powerset, (if (∏ p ∈ S.sup id, p) % 8 = 1 ∧ part_LamAdm S ∧ part_LamAdm (π \ S)
      then part_wt S * part_wt (π \ S) else 0) =
    if (π.filter fun B => (∏ p ∈ B, p) % 8 = 1) = ∅ then
      (if part_LamAdm π then part_wt π else 0) else 0 := by
  rw [← part_count_subset (Finset.filter_subset _ π)]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  have hSP := part_IsP_subset hπ hS
  have hiff : ((∏ p ∈ S.sup id, p) % 8 = 1 ∧ part_LamAdm S ∧ part_LamAdm (π \ S)) ↔
      (S ⊆ π.filter fun B => (∏ p ∈ B, p) % 8 = 1) ∧ part_LamAdm π := by
    constructor
    · rintro ⟨h1, hS', h13R, hkR⟩
      have hS1 := (part_adm_one hSP h1).mp hS'
      refine ⟨fun B hB => Finset.mem_filter.mpr ⟨hS hB, hS1 B hB⟩, fun B hB => ?_, ?_⟩
      · by_cases hBS : B ∈ S
        · exact Or.inl (hS1 B hBS)
        · exact h13R B (Finset.mem_sdiff.mpr ⟨hB, hBS⟩)
      · refine le_trans (Finset.card_le_card fun B hB => ?_) hkR
        rw [Finset.mem_filter] at hB ⊢
        refine ⟨Finset.mem_sdiff.mpr ⟨hB.1, fun hBS => ?_⟩, hB.2⟩
        have := hS1 B hBS; omega
    · rintro ⟨hSX, h13, hk⟩
      have hS1 : ∀ B ∈ S, (∏ p ∈ B, p) % 8 = 1 := fun B hB => (Finset.mem_filter.mp (hSX hB)).2
      exact ⟨part_mod_one_of_all hSP hS1, part_adm_of_all_one hS1,
        fun B hB => h13 B (Finset.sdiff_subset hB),
        (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)).trans hk⟩
  by_cases h1 : (S ⊆ π.filter fun B => (∏ p ∈ B, p) % 8 = 1)
  · by_cases h2 : part_LamAdm π
    · rw [ite_eq_left (hiff.mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2, part_wt_split hS]
    · rw [ite_eq_right fun h => h2 (hiff.mp h).2, ite_eq_left h1, ite_eq_right h2]
  · rw [ite_eq_right fun h => h1 (hiff.mp h).1, ite_eq_right h1]

/-- The inner sum for `m ≡ 1`: `S` must contain the block `B₀` of `p₀`, and all blocks are
class 1. -/
theorem part_inner1 {s : Finset ℕ} {π : Finset (Finset ℕ)} (hπ : part_IsP s π)
    (hs : (∏ p ∈ s, p) % 8 = 1) {p₀ : ℕ} (hp₀ : p₀ ∈ s) :
    ∑ S ∈ π.powerset, (if (∏ p ∈ S.sup id, p) % 8 = 1 ∧ p₀ ∈ S.sup id ∧ part_LamAdm S ∧
      part_LamAdm (π \ S) then part_wt S * part_wt (π \ S) else 0) =
    if π.card = 1 then (if ∀ B ∈ π, (∏ p ∈ B, p) % 8 = 1 then part_wt π else 0) else 0 := by
  obtain ⟨B₀, hB₀, hpB₀⟩ := part_mem_sup.mp (hπ.2.1 ▸ hp₀ : p₀ ∈ π.sup id)
  rw [← part_count_mem hB₀]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  have hSP := part_IsP_subset hπ hS
  have hp : p₀ ∈ S.sup id ↔ B₀ ∈ S := by
    constructor
    · intro h
      obtain ⟨B, hB, hpB⟩ := part_mem_sup.mp h
      by_contra hne
      have hBB : B ≠ B₀ := fun e => hne (e ▸ hB)
      exact Finset.disjoint_left.mp (hπ.1 B (hS hB) B₀ hB₀ hBB) hpB hpB₀
    · intro h; exact part_mem_sup.mpr ⟨B₀, h, hpB₀⟩
  have hiff : ((∏ p ∈ S.sup id, p) % 8 = 1 ∧ p₀ ∈ S.sup id ∧ part_LamAdm S ∧
      part_LamAdm (π \ S)) ↔ B₀ ∈ S ∧ ∀ B ∈ π, (∏ p ∈ B, p) % 8 = 1 := by
    rw [hp]
    constructor
    · rintro ⟨h1, hB, hS', hR⟩
      refine ⟨hB, ?_⟩
      have hS1 := (part_adm_one hSP h1).mp hS'
      have hRP := part_IsP_sdiff hπ hS
      have hsub : S.sup id ⊆ s := by rw [← hπ.2.1]; exact Finset.sup_mono hS
      have ht : (∏ p ∈ s \ S.sup id, p) % 8 = 1 := by
        have h := Nat.mul_mod (∏ p ∈ s \ S.sup id, p) (∏ p ∈ S.sup id, p) 8
        rw [Finset.prod_sdiff hsub, hs, h1] at h
        omega
      have hR1 := (part_adm_one hRP ht).mp hR
      intro B hB
      by_cases hBS : B ∈ S
      · exact hS1 B hBS
      · exact hR1 B (Finset.mem_sdiff.mpr ⟨hB, hBS⟩)
    · rintro ⟨hB, h1⟩
      have hS1 : ∀ B ∈ S, (∏ p ∈ B, p) % 8 = 1 := fun B hB => h1 B (hS hB)
      exact ⟨part_mod_one_of_all hSP hS1, hB, part_adm_of_all_one hS1,
        part_adm_of_all_one fun B hB => h1 B (Finset.sdiff_subset hB)⟩
  by_cases h1 : B₀ ∈ S
  · by_cases h2 : ∀ B ∈ π, (∏ p ∈ B, p) % 8 = 1
    · rw [ite_eq_left (hiff.mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2, part_wt_split hS]
    · rw [ite_eq_right fun h => h2 (hiff.mp h).2, ite_eq_left h1, ite_eq_right h2]
  · rw [ite_eq_right fun h => h1 (hiff.mp h).1, ite_eq_right h1]

/-- `Σ_{A ⊆ s, P A} Λ(A) Λ(s \ A)` as a triple sum over `A` and partitions of `A` and `s \ A`. -/
theorem part_expand (s : Finset ℕ) (P : Finset ℕ → Prop) [DecidablePred P] :
    ∑ A ∈ s.powerset.filter P, part_LamS A * part_LamS (s \ A) =
      ∑ A ∈ s.powerset, ∑ Q₁ ∈ part_PS A, ∑ Q₂ ∈ part_PS (s \ A),
        (if P (Q₁.sup id) ∧ part_LamAdm Q₁ ∧ part_LamAdm Q₂ then part_wt Q₁ * part_wt Q₂
          else 0) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases hA : P A
  · rw [ite_eq_left hA, part_LamS, part_LamS, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun Q₁ hQ₁ => Finset.sum_congr rfl fun Q₂ _ => ?_
    rw [(part_mem_PS.mp hQ₁).2.1]
    by_cases h1 : part_LamAdm Q₁ <;> by_cases h2 : part_LamAdm Q₂ <;> simp [hA, h1, h2]
  · rw [ite_eq_right hA]
    refine (Finset.sum_eq_zero fun Q₁ hQ₁ => Finset.sum_eq_zero fun Q₂ _ => ?_).symm
    rw [(part_mem_PS.mp hQ₁).2.1, ite_eq_right fun h => hA h.1]

theorem part_N1_three {m : ℕ} (hsq : Squarefree m) (hm : m % 8 = 3) :
    ∑ d ∈ m.divisors.filter (fun d => d % 8 = 1), Lam (m / d) * Lam d = (gNat m : ZMod 2) := by
  set s := m.primeFactors with hs_def
  have hsm : ∏ p ∈ s, p = m := Nat.prod_primeFactors_of_squarefree hsq
  have hs3 : (∏ p ∈ s, p) % 8 = 3 := hsm ▸ hm
  have hs0 : s ≠ ∅ := part_ne_empty_of_mod (by norm_num) hs3
  rw [part_sum_divisors hsq]
  rw [Finset.sum_congr rfl fun A hA => by
    rw [part_Lam_div hsq (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1),
      part_Lam_prod (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1), mul_comm]]
  rw [part_expand s (fun A => (∏ q ∈ A, q) % 8 = 1), part_prod_lemma]
  rw [Finset.sum_congr rfl fun π hπ => part_inner3 (part_mem_PS.mp hπ)]
  rw [Finset.sum_eq_single_of_mem {s} (part_mem_PS.mpr (part_IsP_single hs0))]
  · have hf : (({s} : Finset (Finset ℕ)).filter fun B => (∏ p ∈ B, p) % 8 = 1) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun B hB => by
        rw [Finset.mem_singleton.mp hB, hs3]; norm_num
    have ha : part_LamAdm {s} := ⟨fun B hB => by rw [Finset.mem_singleton.mp hB, hs3]; right; rfl,
      (Finset.card_filter_le _ _).trans (by simp)⟩
    rw [ite_eq_left hf, ite_eq_left ha, part_wt, Finset.prod_singleton, hsm]
  · intro π hπ hne
    split_ifs with hf ha
    · exfalso; refine hne (part_eq_single (part_mem_PS.mp hπ) hs0 ?_)
      have : π.filter (fun B => (∏ p ∈ B, p) % 8 = 3) = π := by
        refine Finset.filter_true_of_mem fun B hB => ?_
        rcases ha.1 B hB with h | h
        · exact absurd (Finset.mem_filter.mpr ⟨hB, h⟩) (hf ▸ Finset.notMem_empty B)
        · exact h
      rw [← this]; exact ha.2
    · rfl
    · rfl

theorem part_sum_halves {M : Type*} [AddCommMonoid M] {D : Finset ℕ} (σ : ℕ → ℕ)
    (hσD : ∀ d ∈ D, σ d ∈ D) (hσσ : ∀ d ∈ D, σ (σ d) = d) (p q : ℕ → Prop) [DecidablePred p]
    [DecidablePred q] (hp : ∀ d ∈ D, (p (σ d) ↔ ¬ p d)) (hq : ∀ d ∈ D, (q (σ d) ↔ ¬ q d))
    (f : ℕ → M) (hf : ∀ d ∈ D, f (σ d) = f d) :
    ∑ d ∈ D.filter p, f d = ∑ d ∈ D.filter q, f d := by
  refine Finset.sum_nbij' (fun d => if q d then d else σ d) (fun d => if p d then d else σ d)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    have hd' := Finset.mem_filter.mp hd
    by_cases h : q d
    · simp only [ite_eq_left h]; exact Finset.mem_filter.mpr ⟨hd'.1, h⟩
    · simp only [ite_eq_right h]; exact Finset.mem_filter.mpr ⟨hσD d hd'.1, (hq d hd'.1).mpr h⟩
  · intro d hd
    have hd' := Finset.mem_filter.mp hd
    by_cases h : p d
    · simp only [ite_eq_left h]; exact Finset.mem_filter.mpr ⟨hd'.1, h⟩
    · simp only [ite_eq_right h]; exact Finset.mem_filter.mpr ⟨hσD d hd'.1, (hp d hd'.1).mpr h⟩
  · intro d hd
    have hd' := Finset.mem_filter.mp hd
    by_cases h : q d
    · simp only [ite_eq_left h, ite_eq_left hd'.2]
    · have : ¬ p (σ d) := fun h' => (hp d hd'.1).mp h' hd'.2
      simp only [ite_eq_right h, ite_eq_right this, hσσ d hd'.1]
  · intro d hd
    have hd' := Finset.mem_filter.mp hd
    by_cases h : p d
    · simp only [ite_eq_left h, ite_eq_left hd'.2]
    · have : ¬ q (σ d) := fun h' => (hq d hd'.1).mp h' hd'.2
      simp only [ite_eq_right h, ite_eq_right this, hσσ d hd'.1]
  · intro d hd
    have hd' := Finset.mem_filter.mp hd
    by_cases h : q d
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h, hf d hd'.1]

theorem part_N1_one {m : ℕ} (hsq : Squarefree m) (hm1 : 1 < m) (hm : m % 8 = 1) :
    ∑ d ∈ m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m), Lam d * Lam (m / d) =
      (gNat m : ZMod 2) := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨p₀, hp₀⟩ := Nat.nonempty_primeFactors.mpr hm1
  have hp₀p : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀
  have hp₀m : p₀ ∣ m := Nat.dvd_of_mem_primeFactors hp₀
  -- representatives `d² < m` → `p₀ ∣ d`
  rw [← Finset.filter_filter]
  rw [part_sum_halves (fun d => m / d) ?_ ?_ (fun d => d * d < m)
    (fun d => p₀ ∈ d.primeFactors) ?_ ?_ (fun d => Lam d * Lam (m / d)) ?_]
  rotate_left
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    refine ⟨⟨Nat.div_dvd_of_dvd hd.1.1, hm0⟩, ?_⟩
    have h := Nat.mul_mod (m / d) d 8
    rw [Nat.div_mul_cancel hd.1.1, hm, hd.2] at h
    omega
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1.1 hm0
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    have hde : d * (m / d) = m := Nat.mul_div_cancel' hd.1.1
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hde; omega)
    have he0 : 0 < m / d := Nat.pos_of_ne_zero (by intro h; rw [h] at hde; omega)
    have hne : d ≠ m / d := by
      intro h
      have hdd : d * d = m := by
        calc d * d = d * (m / d) := by rw [← h]
          _ = m := hde
      have hu := hsq d ⟨1, by rw [hdd, mul_one]⟩
      rw [Nat.isUnit_iff] at hu
      subst hu
      omega
    show (m / d) * (m / d) < m ↔ ¬ d * d < m
    constructor
    · intro h1 h2
      rcases lt_or_gt_of_ne hne with h' | h' <;> nlinarith
    · intro h
      rcases lt_or_gt_of_ne hne with h' | h'
      · exfalso; exact h (by nlinarith)
      · nlinarith
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    have hde : d * (m / d) = m := Nat.mul_div_cancel' hd.1.1
    have he0 : m / d ≠ 0 := by intro h; rw [h] at hde; omega
    have hd0 : d ≠ 0 := by rintro rfl; simp at hde; omega
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨-, he, -⟩ ⟨-, hd', -⟩
      have := hsq p₀ (by rw [← hde]; exact Nat.mul_dvd_mul hd' he)
      exact hp₀p.not_isUnit this
    · intro h
      refine ⟨hp₀p, ?_, he0⟩
      rcases (Nat.Prime.dvd_mul hp₀p).mp (by rw [hde]; exact hp₀m : p₀ ∣ d * (m / d)) with h' | h'
      · exact absurd ⟨hp₀p, h', hd0⟩ h
      · exact h'
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    show Lam (m / d) * Lam (m / (m / d)) = Lam d * Lam (m / d)
    rw [Nat.div_div_self hd.1.1 hm0, mul_comm]
  rw [Finset.filter_filter]
  -- reindex by `A = d.primeFactors`
  set s := m.primeFactors with hs_def
  have hsm : ∏ p ∈ s, p = m := Nat.prod_primeFactors_of_squarefree hsq
  have hs1 : (∏ p ∈ s, p) % 8 = 1 := hsm ▸ hm
  have hs0 : s ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨p₀, hp₀⟩
  rw [part_sum_divisors hsq]
  rw [Finset.sum_congr (s₂ := s.powerset.filter fun A => (∏ q ∈ A, q) % 8 = 1 ∧ p₀ ∈ A) ?_
    fun A hA => by
      rw [part_Lam_div hsq (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1),
        part_Lam_prod (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)]]
  swap
  · refine Finset.filter_congr fun A hA => ?_
    rw [Nat.primeFactors_prod fun q hq =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hA hq)]
  rw [part_expand s (fun A => (∏ q ∈ A, q) % 8 = 1 ∧ p₀ ∈ A), part_prod_lemma]
  simp only [and_assoc]
  rw [Finset.sum_congr rfl fun π hπ => part_inner1 (part_mem_PS.mp hπ) hs1 hp₀]
  rw [Finset.sum_eq_single_of_mem {s} (part_mem_PS.mpr (part_IsP_single hs0))]
  · have ha : ∀ B ∈ ({s} : Finset (Finset ℕ)), (∏ p ∈ B, p) % 8 = 1 := fun B hB => by
      rw [Finset.mem_singleton.mp hB, hs1]
    rw [ite_eq_left (Finset.card_singleton s), ite_eq_left ha, part_wt, Finset.prod_singleton, hsm]
  · intro π hπ hne
    split_ifs with hc ha <;>
      first | rfl | exact absurd (part_eq_single (part_mem_PS.mp hπ) hs0 hc.le) hne

/-- **Lemma N1, combinatorial core**: `Λ(1) = 1` and `Λ` satisfies the identity of
`LemmaTwoEight` modulo 2. (nt-tyz §4.3: a partition with `b` class-1 blocks refines
`2^{b−1} − 1` unordered pairs; with one class-3 block and a set `S` of class-1 blocks it arises
`2^{|S|} − 1` times.) -/
theorem lemmaN1_core :
    Lam 1 = 1 ∧
    (∀ m : ℕ, Squarefree m → 1 < m → m % 8 = 1 →
      ∑ d ∈ m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m), Lam d * Lam (m / d) =
        (gNat m : ZMod 2)) ∧
    (∀ m : ℕ, Squarefree m → m % 8 = 3 →
      ∑ d ∈ m.divisors.filter (fun d => d % 8 = 1), Lam (m / d) * Lam d = (gNat m : ZMod 2)) :=
  ⟨part_Lam_one, fun _ hsq hm1 hm => part_N1_one hsq hm1 hm, fun _ hsq hm => part_N1_three hsq hm⟩

/-! ### Lemma N2: helpers (prefix `n2_`) -/

theorem n2_div_mod8 {m q a c : ℕ} (hq : q ∣ m) (hm : m % 8 = a) (hc : q % 8 = c)
    (hc' : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) : m / q % 8 = (a * c) % 8 := by
  have h : m % 8 = (m / q % 8) * (q % 8) % 8 := by
    conv_lhs => rw [← Nat.div_mul_cancel hq]
    exact Nat.mul_mod _ _ _
  have hx : m / q % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [hm, hc] at h
  subst hm hc
  rcases hc' with hb | hb | hb | hb <;> rw [hb] at h ⊢ <;>
    interval_cases hr : m / q % 8 <;> omega

theorem n2_mod8_mul {m q : ℕ} (hq : q ∣ m) : (q % 8) * (m / q % 8) % 8 = m % 8 := by
  conv_rhs => rw [← Nat.mul_div_cancel' hq]
  exact (Nat.mul_mod _ _ _).symm

/-- The ring `ℤ[i]/(2)`. -/
abbrev n2_R : Type := GaussianInt ⧸ Ideal.span {(2 : GaussianInt)}

abbrev n2_π : GaussianInt →+* n2_R := Ideal.Quotient.mk _

theorem n2_two : (2 : n2_R) = 0 := by
  rw [show (2 : n2_R) = n2_π 2 from (map_ofNat n2_π 2).symm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem n2_neg (x : n2_R) : -x = x :=
  neg_eq_iff_add_eq_zero.mpr (by rw [← two_mul, n2_two, zero_mul])

/-- The class of `i` in `ℤ[i]/(2)`. -/
def n2_I : n2_R := n2_π gi

/-- The class of `ε(d₀, d₁)` modulo 2, from the classes `a = d₀ % 8`, `c = d₁ % 8`. -/
def n2_epsR (a c : ℕ) : n2_R := if a = 5 ∧ c = 3 then n2_I else 1

/-- `φ(d, e)` modulo 2, from `a = d % 8`, `b = e % 8`. -/
def n2_phi (a b : ℕ) : n2_R := if a = 7 ∧ b = 5 then n2_I else 1

theorem n2_eps {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) {x y : ℕ} (hxy : x * y ∣ n)
    (hx : x % 8 = 5 ∨ x % 8 = 7) (hy : y % 8 = 1 ∨ y % 8 = 3) :
    n2_π (G.ε x y) = n2_epsR (x % 8) (y % 8) := by
  by_cases h53 : x % 8 = 5 ∧ y % 8 = 3
  · rw [n2_epsR, ite_eq_left h53, n2_I]
    rcases G.eps_53 x y hxy h53.1 h53.2 with h | h <;> simp [h, n2_neg]
  · rw [n2_epsR, ite_eq_right h53]
    have : x % 8 = 5 ∧ y % 8 = 1 ∨ x % 8 = 7 ∧ y % 8 = 1 ∨ x % 8 = 7 ∧ y % 8 = 3 := by omega
    rcases G.eps_pm1 x y hxy this with h | h <;> simp [h, n2_neg]

/-- `κ(q) = ε(d/q, q) φ(d/q, e)` modulo 2 takes the same value at `q` and `m/q` (`m = d/e`). -/
theorem n2_kappa {a b c c' x x' : ℕ} (ha : a = 5 ∨ a = 7) (hb : b = 5 ∨ b = 7)
    (hc : c = 1 ∨ c = 3) (hc' : c' = 1 ∨ c' = 3) (hx : x = a * c % 8) (hx' : x' = a * c' % 8)
    (h : c * c' % 8 = a * b % 8) :
    n2_epsR x c * n2_phi x b = n2_epsR x' c' * n2_phi x' b := by
  subst hx hx'
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> revert h <;> norm_num [n2_epsR, n2_phi]

/-- The surviving term: `ε(e, d/e) ≡ φ(d, e)`. -/
theorem n2_last {a b : ℕ} (ha : a = 5 ∨ a = 7) (hb : b = 5 ∨ b = 7) :
    n2_epsR b (a * b % 8) * n2_phi b b = n2_phi a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [n2_epsR, n2_phi]

/-- The coefficient of `Z(e)` in `P(d)`, defined by the recursion of TYZ §3.1. -/
def n2_c (ε : ℕ → ℕ → GaussianInt) (L : ℕ → ℤ) (e : ℕ) : ℕ → GaussianInt
  | d => (if e = d then 1 else 0) -
      ∑ q ∈ (d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))).attach,
        (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q)
decreasing_by
  have h := q.2
  simp only [Finset.mem_filter, Nat.mem_divisors] at h
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h.1.2) h.2.1

theorem n2_c_eq (ε : ℕ → ℕ → GaussianInt) (L : ℕ → ℤ) (e d : ℕ) :
    n2_c ε L e d = (if e = d then 1 else 0) -
      ∑ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
        (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q) := by
  rw [n2_c]
  congr 1
  exact Finset.sum_attach _ (fun q => (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q))

theorem n2_mem_Q {n d q : ℕ} (hd : d ∈ n.divisors) (hcl : d % 8 = 5 ∨ d % 8 = 7)
    (hq : q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))) :
    q ∣ d ∧ 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3) ∧ d / q < d ∧ d / q ∈ n.divisors ∧
      (d / q % 8 = 5 ∨ d / q % 8 = 7) := by
  simp only [Finset.mem_filter, Nat.mem_divisors] at hq
  obtain ⟨⟨hqd, hd0⟩, hq1, hq8⟩ := hq
  refine ⟨hqd, hq1, hq8, Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hq1, ?_, ?_⟩
  · rw [Nat.mem_divisors] at hd ⊢
    exact ⟨(Nat.div_dvd_of_dvd hqd).trans hd.1, hd.2⟩
  · rcases hcl with h | h <;> rcases hq8 with h' | h' <;>
      rw [n2_div_mod8 hqd h h' (by omega)] <;> norm_num

/-- `P(d) = Σ_e c_d(e) Z(e)` over the fixed index set `e ∣ n`, `e ≡ 5, 7`. -/
theorem n2_P_eq {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) :
    ∀ d ∈ n.divisors, (d % 8 = 5 ∨ d % 8 = 7) →
      G.P d = ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
        n2_c G.ε L e d • G.Z e := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hcl
  have hdE : d ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7) :=
    Finset.mem_filter.mpr ⟨hd, hcl⟩
  rw [G.recursion d hd hcl]
  have hstep : ∀ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
      (G.ε (d / q) q * (L q : GaussianInt)) • G.P (d / q) =
        ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
          ((G.ε (d / q) q * (L q : GaussianInt)) * n2_c G.ε L e (d / q)) • G.Z e := by
    intro q hq
    obtain ⟨-, -, -, hlt, hdn, hcl'⟩ := n2_mem_Q hd hcl hq
    rw [ih (d / q) hlt hdn hcl', Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← mul_smul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  conv_rhs => enter [2, e]; rw [n2_c_eq]
  simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', hdE, ite_true]

/-- `e ∣ d/q ↔ q ∣ d/e` for divisors `e, q` of `d`. -/
theorem n2_dvd_iff {d e q : ℕ} (he : e ∣ d) (hq : q ∣ d) : e ∣ d / q ↔ q ∣ d / e := by
  rw [Nat.dvd_div_iff_mul_dvd hq, Nat.dvd_div_iff_mul_dvd he, mul_comm]

/-- **The inductive identity**: `c_d(e) ≡ φ(d, e) 𝓛(d/e)` modulo `2ℤ[i]` (and `c_d(e) ≡ 0` if
`e ∤ d`). -/
theorem n2_c_mod {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hsq : Squarefree n) (hL1 : L 1 = 1)
    {e : ℕ} (he : e % 8 = 5 ∨ e % 8 = 7) :
    ∀ d ∈ n.divisors, (d % 8 = 5 ∨ d % 8 = 7) →
      n2_π (n2_c G.ε L e d) =
        if e ∣ d then n2_phi (d % 8) (e % 8) * ((L (d / e) : ℤ) : n2_R) else 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hcl
  have hd0 : d ≠ 0 := by omega
  have he0 : e ≠ 0 := by omega
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [n2_c_eq, map_sub, map_sum]
  have hterm : ∀ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
      n2_π ((G.ε (d / q) q * (L q : GaussianInt)) * n2_c G.ε L e (d / q)) =
        if e ∣ d / q then n2_epsR (d / q % 8) (q % 8) * ((L q : ℤ) : n2_R) *
          (n2_phi (d / q % 8) (e % 8) * ((L (d / q / e) : ℤ) : n2_R)) else 0 := by
    intro q hq
    obtain ⟨hqd, -, hq8, hlt, hdqn, hcl'⟩ := n2_mem_Q hd hcl hq
    rw [map_mul, map_mul, n2_eps G (by rw [Nat.div_mul_cancel hqd]; exact hdn) hcl' hq8,
      map_intCast, ih (d / q) hlt hdqn hcl']
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  by_cases hed : e ∣ d
  swap
  · have hne : e ≠ d := by rintro rfl; exact hed dvd_rfl
    rw [ite_eq_right hed, ite_eq_right hne, map_zero, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [ite_eq_right]
    intro h
    exact hed (h.trans (Nat.div_dvd_of_dvd (n2_mem_Q hd hcl hq).1))
  rw [ite_eq_left hed]
  by_cases hee : e = d
  · subst hee
    rw [ite_eq_left rfl, map_one, Nat.div_self (Nat.pos_of_ne_zero he0), hL1, Finset.sum_eq_zero,
      sub_zero, n2_phi, ite_eq_right (by omega), Int.cast_one, one_mul]
    intro q hq
    obtain ⟨hqd, hq1, -, -, -, -⟩ := n2_mem_Q hd hcl hq
    rw [ite_eq_right]
    intro h
    have hpos : 0 < e / q := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hqd) (by omega)
    have h1 := Nat.le_of_dvd hpos h
    have h2 := Nat.div_lt_self (Nat.pos_of_ne_zero he0) hq1
    omega
  rw [ite_eq_right hee, map_zero, zero_sub, n2_neg]
  obtain ⟨m, hm⟩ : ∃ m, d / e = m := ⟨_, rfl⟩
  rw [hm]
  have hdem : e * m = d := by rw [← hm]; exact Nat.mul_div_cancel' hed
  have hm1 : 1 < m := by
    rcases (show m = 0 ∨ m = 1 ∨ 1 < m by omega) with h | h | h
    · subst h; omega
    · subst h; omega
    · exact h
  have hm0 : m ≠ 0 := by omega
  have hmd : m ∣ d := Dvd.intro_left e hdem
  have hdme : d / m = e := Nat.div_eq_of_eq_mul_left (by omega) hdem.symm
  have hm8 : m % 8 = d % 8 * (e % 8) % 8 := by
    rw [← hm]; exact n2_div_mod8 hed rfl rfl (by omega)
  have hm13 : m % 8 = 1 ∨ m % 8 = 3 := by
    rw [hm8]; rcases hcl with h | h <;> rcases he with h' | h' <;> rw [h, h'] <;> norm_num
  have hmQ : m ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)) := by
    rw [Finset.mem_filter, Nat.mem_divisors]; exact ⟨⟨hmd, hd0⟩, hm1, hm13⟩
  have hdiv : ∀ q, q ∣ m → d / q / e = m / q := fun q _ => by
    rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul, hm]
  rw [← Finset.add_sum_erase _ _ hmQ]
  have hrest : ∑ q ∈ (d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))).erase m,
      (if e ∣ d / q then n2_epsR (d / q % 8) (q % 8) * ((L q : ℤ) : n2_R) *
          (n2_phi (d / q % 8) (e % 8) * ((L (d / q / e) : ℤ) : n2_R)) else 0) = 0 := by
    refine Finset.sum_involution (fun q _ => if e ∣ d / q then m / q else q) ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, hq8, -, -, hcl'⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        have hq'd : m / q ∣ d := (Nat.div_dvd_of_dvd hqm').trans hmd
        have h' : e ∣ d / (m / q) := by
          rw [n2_dvd_iff hed hq'd, hm]; exact Nat.div_dvd_of_dvd hqm'
        simp only [h, h', ↓reduceIte]
        rw [hdiv q hqm', hdiv (m / q) (Nat.div_dvd_of_dvd hqm'), Nat.div_div_self hqm' hm0]
        have hq'8 : m / q % 8 = 1 ∨ m / q % 8 = 3 := by
          rcases hm13 with h1 | h1 <;> rcases hq8 with h2 | h2 <;>
            rw [n2_div_mod8 hqm' h1 h2 (by omega)] <;> norm_num
        have hk := n2_kappa hcl he hq8 hq'8 (n2_div_mod8 hqd rfl rfl (by omega))
          (n2_div_mod8 hq'd rfl rfl (by omega)) (by rw [n2_mod8_mul hqm', hm8])
        linear_combination (((L q : ℤ) : n2_R) * ((L (m / q) : ℤ) : n2_R)) * hk +
          (n2_epsR (d / (m / q) % 8) (m / q % 8) * n2_phi (d / (m / q) % 8) (e % 8) *
            ((L q : ℤ) : n2_R) * ((L (m / q) : ℤ) : n2_R)) * n2_two
      · simp only [h, ↓reduceIte, add_zero]
    · intro q hq hf
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, -, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      have h : e ∣ d / q := by
        by_contra h; apply hf; simp only [h, ↓reduceIte]
      have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
      simp only [h, ↓reduceIte]
      intro heq
      have hmqq : q * q = m := by
        conv_rhs => rw [← Nat.div_mul_cancel hqm', heq]
      have hu := hsq q (by rw [hmqq]; exact hmd.trans hdn)
      rw [Nat.isUnit_iff] at hu
      omega
    · intro q hq
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, hq8, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        simp only [h, ↓reduceIte]
        refine Finset.mem_erase.mpr ⟨(Nat.div_lt_self (by omega) hq1).ne, ?_⟩
        rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨(Nat.div_dvd_of_dvd hqm').trans hmd, hd0⟩, ?_, ?_⟩
        · obtain ⟨k, hk⟩ := id hqm'
          rw [hk, Nat.mul_div_cancel_left _ (by omega : 0 < q)]
          rcases k with _ | _ | k
          · simp at hk; omega
          · simp at hk; omega
          · omega
        · rcases hm13 with h1 | h1 <;> rcases hq8 with h2 | h2 <;>
            rw [n2_div_mod8 hqm' h1 h2 (by omega)] <;> norm_num
      · simp only [h, ↓reduceIte]; exact hq
    · intro q hq
      obtain ⟨-, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, -, -, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        have hq'd : m / q ∣ d := (Nat.div_dvd_of_dvd hqm').trans hmd
        have h' : e ∣ d / (m / q) := by
          rw [n2_dvd_iff hed hq'd, hm]; exact Nat.div_dvd_of_dvd hqm'
        simp only [h, h', ↓reduceIte]
        exact Nat.div_div_self hqm' hm0
      · simp only [h, ↓reduceIte]
  rw [hrest, add_zero]
  simp only [hdme, dvd_rfl, ↓reduceIte, Nat.div_self (Nat.pos_of_ne_zero he0), hL1, Int.cast_one,
    mul_one]
  rw [hm8]
  linear_combination ((L m : ℤ) : n2_R) * n2_last hcl he

/-- **Lemma N2** (`𝓛`-form): for squarefree `n ≡ 5 (mod 8)`, unwinding the recursion gives
`P(n) = Σ_{e ∣ n, e ≡ 5, 7} 𝓛(n/e) Z(e) + 2X` with `X ∈ M` (the span of `A[(1+i)³]` and the
`Z(e)` in `A(ℍ'_n)`, so finalStep needs no action of `β'` beyond `M`). Uses only `recursion`,
`eps_53`, `eps_pm1` and `L 1 = 1`; no Lemma 2.9. (Inductive identity: for `d ∣ n`, `d ≡ 5, 7`,
`P(d) ≡ Σ_e φ(d, e) 𝓛(d/e) Z(e)` mod `2M`, with `φ = i` for `(d, e) ≡ (7, 5)` and `1` otherwise;
the induction step pairs `d₁ ↔ (d/e)/d₁`.) -/
theorem lemmaN2 {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL1 : L 1 = 1) :
    ∃ X : G.M, G.P n =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), L (n / e) • G.Z e + (2 : ℤ) • X := by
  have hn0 : n ≠ 0 := by omega
  have hnD : n ∈ n.divisors := Nat.mem_divisors_self n hn0
  have hP := n2_P_eq G n hnD (Or.inl hn)
  have hw : ∀ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
      ∃ w : GaussianInt, n2_c G.ε L e n = (L (n / e) : GaussianInt) + 2 * w := by
    intro e he
    obtain ⟨hen, he8⟩ := Finset.mem_filter.mp he
    have h := n2_c_mod G hsq hL1 he8 n hnD (Or.inl hn)
    rw [ite_eq_left (Nat.dvd_of_mem_divisors hen), n2_phi, ite_eq_right (by omega), one_mul] at h
    have h0 : n2_π (n2_c G.ε L e n - (L (n / e) : GaussianInt)) = 0 := by
      rw [map_sub, h, map_intCast, sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    obtain ⟨w, hw⟩ := h0
    exact ⟨w, by linear_combination hw⟩
  choose! w hw using hw
  refine ⟨∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), w e • G.Z e, ?_⟩
  rw [hP, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [hw e he, add_smul, Int.cast_smul_eq_zsmul, mul_smul, two_smul, two_smul]

/-- `Re : ℤ[i] → ℤ` as an additive hom. -/
def final_reHom : GaussianInt →+ ℤ where
  toFun z := z.re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `Im : ℤ[i] → ℤ` as an additive hom. -/
def final_imHom : GaussianInt →+ ℤ where
  toFun z := z.im
  map_zero' := rfl
  map_add' _ _ := rfl

theorem final_reHom_apply (z : GaussianInt) : final_reHom z = z.re := rfl

theorem final_imHom_apply (z : GaussianInt) : final_imHom z = z.im := rfl

/-- A multiple of `2 + 2i` has even components: `(2+2i)(p+qi) = (2p−2q) + (2p+2q)i`. -/
theorem final_two_dvd_of_dvd {z : GaussianInt} (h : twoTwoI ∣ z) : 2 ∣ z.re ∧ 2 ∣ z.im := by
  obtain ⟨c, rfl⟩ := h
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, twoTwoI]
  exact ⟨⟨c.re - c.im, by ring⟩, ⟨c.im + c.re, by ring⟩⟩

/-- `4 • τ(z) = 0`, since `4 = (2+2i)(1−i)`. -/
theorem final_four_nsmul_τ {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (z : GaussianInt) :
    (4 : ℕ) • G.τ z = 0 := by
  rw [← map_nsmul, G.τ_eq_zero]
  refine ⟨⟨1, -1⟩ * z, ?_⟩
  rw [nsmul_eq_mul, ← mul_assoc]
  congr 1

/-- **The final step** (nt-tyz §4.4): if `𝓛(n) = 0`, then `a = Σ_{e≡5} 𝓛(n/e) g(e)` and
`N = Σ_{e≡7} 𝓛(n/e) g(e)` are even. Uses `torsion_of_zero`, `τ_eq_zero`, `tors_mem_range`, `β_τ`,
`beta_five`, `beta_seven`. -/
theorem finalStep {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hn : n % 8 = 5) (hL : L n = 0)
    {X : G.M}
    (hX : G.P n =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), L (n / e) • G.Z e + (2 : ℤ) • X) :
    (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2) = 0) ∧
    (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2) = 0) := by
  classical
  obtain ⟨y, hy⟩ := G.tors_mem_range _ (G.torsion_of_zero hL)
  choose! k hk using G.beta_five
  let f : G.M →+ G.M := G.β + AddMonoidHom.id G.M
  have hf : ∀ x, f x = G.β x + x := fun x => rfl
  have hτf : ∀ z, f (G.τ z) = G.τ (2 • z) := by
    intro z; rw [hf, G.β_τ, map_nsmul, two_nsmul]
  set F5 := n.divisors.filter (fun e => e % 8 = 5) with hF5
  set F7 := n.divisors.filter (fun e => e % 8 = 7) with hF7
  have hsplit : n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7) = F5 ∪ F7 :=
    Finset.filter_or _ _ _
  have hdisj : Disjoint F5 F7 :=
    Finset.disjoint_filter.2 (fun _ _ h1 h2 => by omega)
  set A5 : GaussianInt :=
    ∑ e ∈ F5, L (n / e) • ((gNat e : ℤ) • (⟨1, -1⟩ : GaussianInt) + k e • 2) with hA5
  set A7 : GaussianInt := ∑ e ∈ F7, L (n / e) • ((gNat e : ℤ) • (1 : GaussianInt)) with hA7
  have h5 : ∑ e ∈ F5, L (n / e) • f (G.Z e) = G.τ A5 := by
    rw [hA5, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hF5, Finset.mem_filter] at he
    rw [hf, hk e he.1 he.2, map_zsmul, map_add, map_zsmul, map_zsmul]
  have h7 : ∑ e ∈ F7, L (n / e) • f (G.Z e) = G.τ A7 := by
    rw [hA7, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hF7, Finset.mem_filter] at he
    rw [hf, G.beta_seven e he.1 he.2, map_zsmul, map_zsmul]
  have hW : G.τ (2 • y) = G.τ A5 + G.τ A7 + (2 : ℤ) • f X := by
    rw [← hτf, hy, hX, map_add, map_sum, map_zsmul, hsplit, Finset.sum_union hdisj]
    simp only [map_zsmul]
    rw [h5, h7]
  set W := f X with hWdef
  have h2W : (2 : ℤ) • W = G.τ (2 • y - A5 - A7) := by
    rw [map_sub, map_sub, hW]; abel
  have hWt : IsOfFinAddOrder W := by
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨8, by norm_num, ?_⟩
    have h84 : (8 : ℕ) • W = (4 : ℕ) • ((2 : ℤ) • W) := by
      rw [← natCast_zsmul, ← natCast_zsmul, smul_smul]; norm_num
    rw [h84, h2W, final_four_nsmul_τ]
  obtain ⟨w, hw⟩ := G.tors_mem_range W hWt
  set z : GaussianInt := 2 • y - A5 - A7 - (2 : ℤ) • w with hz
  have hz0 : G.τ z = 0 := by
    rw [hz, map_sub, ← h2W, map_zsmul, hw, sub_self]
  obtain ⟨hre, him⟩ := final_two_dvd_of_dvd ((G.τ_eq_zero z).mp hz0)
  set a := ∑ e ∈ F5, L (n / e) * (gNat e : ℤ) with ha
  set N := ∑ e ∈ F7, L (n / e) * (gNat e : ℤ) with hN
  set K := ∑ e ∈ F5, L (n / e) * k e with hK
  have hzre : z.re = 2 * y.re - (a + 2 * K) - N - 2 * w.re := by
    rw [← final_reHom_apply, hz, hA5, hA7]
    simp only [map_sub, map_sum, map_zsmul, map_add, map_nsmul, final_reHom_apply]
    simp only [Zsqrtd.re_one, Zsqrtd.re_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    have e1 : ∑ x ∈ F5, L (n / x) * ((gNat x : ℤ) * 1 + k x * 2) = a + 2 * K := by
      rw [ha, hK, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    have e2 : ∑ x ∈ F7, L (n / x) * ((gNat x : ℤ) * 1) = N := by
      rw [hN]; simp only [mul_one]
    rw [e1, e2]
  have hzim : z.im = 2 * y.im + a - 2 * w.im := by
    rw [← final_imHom_apply, hz, hA5, hA7]
    simp only [map_sub, map_sum, map_zsmul, map_add, map_nsmul, final_imHom_apply]
    simp only [Zsqrtd.im_one, Zsqrtd.im_ofNat, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    have e1 : ∑ x ∈ F5, L (n / x) * ((gNat x : ℤ) * (-1) + k x * 0) = -a := by
      rw [ha, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    have e2 : ∑ x ∈ F7, L (n / x) * ((gNat x : ℤ) * 0) = 0 := by
      simp only [mul_zero, Finset.sum_const_zero]
    rw [e1, e2]
    ring
  rw [hzre] at hre
  rw [hzim] at him
  have ha2 : (2 : ℤ) ∣ a := by omega
  have hN2 : (2 : ℤ) ∣ N := by omega
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mpr ha2,
    (ZMod.intCast_zmod_eq_zero_iff_dvd N 2).mpr hN2⟩

/-! ### part: helpers for `matching` -/

section part_split_sec

variable {α : Type*} [DecidableEq α]

theorem part_split {M : Type*} [AddCommMonoid M] (s : Finset α) (C : Finset α → Prop)
    [DecidablePred C] (G : Finset (Finset α) → M) :
    ∑ Q ∈ part_PS s, (if (Q.filter C).card = 1 then G Q else 0) =
      ∑ B ∈ s.powerset.filter (fun B => B ≠ ∅ ∧ C B),
        ∑ R ∈ part_PS (s \ B), (if ∀ B' ∈ R, ¬ C B' then G (insert B R) else 0) := by
  simp only [← Finset.sum_filter]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => insert x.1 x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨B, R⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset] at hx
    obtain ⟨⟨hBs, hB0, hCB⟩, hR, hRC⟩ := hx
    have h := part_mem_PS.mp hR
    refine Finset.mem_filter.mpr ⟨part_mem_PS.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro X hX Y hY hXY
      rw [Finset.mem_insert] at hX hY
      rcases hX with rfl | hX <;> rcases hY with rfl | hY
      · exact absurd rfl hXY
      · exact Finset.disjoint_of_subset_right (part_subset_of_mem h hY) Finset.disjoint_sdiff
      · exact Finset.disjoint_of_subset_left (part_subset_of_mem h hX) Finset.sdiff_disjoint
      · exact h.1 X hX Y hY hXY
    · rw [Finset.sup_insert, h.2.1]; exact Finset.union_sdiff_of_subset hBs
    · rw [Finset.mem_insert]
      rintro (h0 | h0)
      · exact hB0 h0.symm
      · exact h.2.2 h0
    · rw [Finset.filter_insert, ite_eq_left hCB, Finset.filter_eq_empty_iff.mpr hRC]; rfl
  · rintro ⟨B, R⟩ hx ⟨B', R'⟩ hx' he
    simp only [Finset.mem_sigma, Finset.mem_filter] at hx hx'
    simp only at he
    have hBB : B = B' := by
      have : B ∈ insert B' R' := he ▸ Finset.mem_insert_self B R
      rcases Finset.mem_insert.mp this with h1 | h1
      · exact h1
      · exact absurd hx.1.2.2 (hx'.2.2 B h1)
    subst hBB
    have hR : R = R' := by
      rw [← Finset.erase_insert (fun h => hx.2.2 B h hx.1.2.2), he,
        Finset.erase_insert (fun h => hx'.2.2 B h hx'.1.2.2)]
    subst hR; rfl
  · intro Q hQ
    rw [Finset.mem_filter] at hQ
    obtain ⟨B, hB⟩ := Finset.card_eq_one.mp hQ.2
    have hBQ : B ∈ Q.filter C := hB ▸ Finset.mem_singleton_self B
    rw [Finset.mem_filter] at hBQ
    have h := part_mem_PS.mp hQ.1
    refine ⟨⟨B, Q.erase B⟩, ?_, Finset.insert_erase hBQ.1⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨part_subset_of_mem h hBQ.1, fun h0 => h.2.2 (h0 ▸ hBQ.1), hBQ.2⟩, ?_, ?_⟩
    · have := part_IsP_sdiff h (Finset.singleton_subset_iff.mpr hBQ.1)
      rw [Finset.sup_singleton, ← Finset.erase_eq] at this
      exact part_mem_PS.mpr this
    · intro X hX hCX
      have : X ∈ Q.filter C := Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hX, hCX⟩
      rw [hB, Finset.mem_singleton] at this
      exact Finset.ne_of_mem_erase hX this

end part_split_sec

/-- `Admissible5aNat` on block sets. -/
def part_T5aAdm (Q : Finset (Finset ℕ)) : Prop :=
  (Q.filter fun B => (∏ p ∈ B, p) % 8 = 5).card = 1 ∧
  ∀ B ∈ Q, (∏ p ∈ B, p) % 8 = 5 ∨ (∏ p ∈ B, p) % 8 = 1

instance part_decT5aAdm : DecidablePred part_T5aAdm := fun Q => by
  unfold part_T5aAdm; infer_instance

/-- `Admissible5bNat` on block sets. -/
def part_T5bAdm (Q : Finset (Finset ℕ)) : Prop :=
  (Q.filter fun B => (∏ p ∈ B, p) % 8 = 7).card = 1 ∧
  (Q.filter fun B => (∏ p ∈ B, p) % 8 = 3).card = 1 ∧
  ∀ B ∈ Q, (∏ p ∈ B, p) % 8 = 7 ∨ (∏ p ∈ B, p) % 8 = 3 ∨ (∏ p ∈ B, p) % 8 = 1

instance part_decT5bAdm : DecidablePred part_T5bAdm := fun Q => by
  unfold part_T5bAdm; infer_instance

theorem part_T5a_eq (n : ℕ) :
    T5aCl n = ∑ Q ∈ part_PS n.primeFactors, if part_T5aAdm Q then part_wt Q else 0 := by
  refine part_transport n part_T5aAdm _ fun P => if_congr ?_ rfl rfl
  simp only [Admissible5aNat, part_T5aAdm, Finset.forall_mem_image, part_prod_map,
    part_card_filter_image]

theorem part_T5b_eq (n : ℕ) :
    T5bCl n = ∑ Q ∈ part_PS n.primeFactors, if part_T5bAdm Q then part_wt Q else 0 := by
  refine part_transport n part_T5bAdm _ fun P => if_congr ?_ rfl rfl
  simp only [Admissible5bNat, part_T5bAdm, Finset.forall_mem_image, part_prod_map,
    part_card_filter_image]

theorem part_matching_lhs {n : ℕ} (hn : Squarefree n) (c : ℕ) :
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = c), Lam (n / e) * (gNat e : ZMod 2) =
      ∑ B ∈ n.primeFactors.powerset.filter (fun B => (∏ q ∈ B, q) % 8 = c),
        part_LamS (n.primeFactors \ B) * (gNat (∏ q ∈ B, q) : ZMod 2) := by
  rw [part_sum_divisors hn]
  refine Finset.sum_congr rfl fun B hB => ?_
  rw [part_Lam_div hn (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)]

theorem part_ite_and {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R] (h : R ↔ P ∧ Q)
    (a : ZMod 2) : (if R then a else 0) = if P then (if Q then a else 0) else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, h]

theorem part_matching5a {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), Lam (n / e) * (gNat e : ZMod 2) = T5aCl n := by
  rw [part_matching_lhs hsq, part_T5a_eq]
  rw [Finset.sum_congr rfl fun Q _ => part_ite_and (R := part_T5aAdm Q) Iff.rfl (part_wt Q),
    part_split]
  rw [Finset.filter_congr (p := fun B => (∏ q ∈ B, q) % 8 = 5)
    (q := fun B => B ≠ ∅ ∧ (∏ q ∈ B, q) % 8 = 5)
    fun B _ => ⟨fun h => ⟨part_ne_empty_of_mod (by norm_num) h, h⟩, fun h => h.2⟩]
  refine Finset.sum_congr rfl fun B hB => ?_
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB
  obtain ⟨hBs, hB0, hB5⟩ := hB
  have ht : (∏ q ∈ n.primeFactors \ B, q) % 8 = 1 :=
    part_mod_sdiff hsq hBs hn hB5 (by decide)
  rw [part_LamS, Finset.sum_mul]
  refine Finset.sum_congr rfl fun R hR => ?_
  have hRP := part_mem_PS.mp hR
  have hiff := part_adm_one hRP ht
  rw [show part_wt (insert B R) = _ * part_wt R from
    Finset.prod_insert (part_not_mem_of_ne_empty hRP hB0)]
  by_cases h1 : ∀ B' ∈ R, (∏ p ∈ B', p) % 8 = 1
  · have h2 : ∀ B' ∈ R, ¬ (∏ p ∈ B', p) % 8 = 5 := fun B' hB' => by rw [h1 B' hB']; norm_num
    have h3 : ∀ B' ∈ insert B R, (∏ p ∈ B', p) % 8 = 5 ∨ (∏ p ∈ B', p) % 8 = 1 := by
      intro B' hB'
      rcases Finset.mem_insert.mp hB' with rfl | hB'
      · exact Or.inl hB5
      · exact Or.inr (h1 B' hB')
    rw [ite_eq_left h2, ite_eq_left h3, ite_eq_left (hiff.mpr h1), mul_comm]
  · rw [ite_eq_right (fun h => h1 (hiff.mp h)), zero_mul]
    split_ifs with h2 h3
    · exfalso; refine h1 fun B' hB' => ?_
      rcases h3 B' (Finset.mem_insert_of_mem hB') with h | h
      · exact absurd h (h2 B' hB')
      · exact h
    · rfl
    · rfl

theorem part_matching5b {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), Lam (n / e) * (gNat e : ZMod 2) = T5bCl n := by
  rw [part_matching_lhs hsq, part_T5b_eq]
  rw [Finset.sum_congr rfl fun Q _ => part_ite_and (R := part_T5bAdm Q) Iff.rfl (part_wt Q),
    part_split]
  rw [Finset.filter_congr (p := fun B => (∏ q ∈ B, q) % 8 = 7)
    (q := fun B => B ≠ ∅ ∧ (∏ q ∈ B, q) % 8 = 7)
    fun B _ => ⟨fun h => ⟨part_ne_empty_of_mod (by norm_num) h, h⟩, fun h => h.2⟩]
  refine Finset.sum_congr rfl fun B hB => ?_
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB
  obtain ⟨hBs, hB0, hB7⟩ := hB
  have ht : (∏ q ∈ n.primeFactors \ B, q) % 8 = 3 :=
    part_mod_sdiff hsq hBs hn hB7 (by decide)
  rw [part_LamS, Finset.sum_mul]
  refine Finset.sum_congr rfl fun R hR => ?_
  have hRP := part_mem_PS.mp hR
  have hBR := part_not_mem_of_ne_empty hRP hB0
  have hiff := part_adm_three hRP ht
  rw [show part_wt (insert B R) = _ * part_wt R from Finset.prod_insert hBR]
  have hf3 : ((insert B R).filter fun B' => (∏ p ∈ B', p) % 8 = 3) =
      R.filter fun B' => (∏ p ∈ B', p) % 8 = 3 := by
    rw [Finset.filter_insert, ite_eq_right (by rw [hB7]; norm_num)]
  rw [hf3]
  by_cases h1 : (∀ B' ∈ R, (∏ p ∈ B', p) % 8 = 1 ∨ (∏ p ∈ B', p) % 8 = 3) ∧
      (R.filter fun B => (∏ p ∈ B, p) % 8 = 3).card = 1
  · have h2 : ∀ B' ∈ R, ¬ (∏ p ∈ B', p) % 8 = 7 := fun B' hB' => by
      rcases h1.1 B' hB' with h | h <;> rw [h] <;> norm_num
    have h3 : (R.filter fun B => (∏ p ∈ B, p) % 8 = 3).card = 1 ∧
        ∀ B' ∈ insert B R, (∏ p ∈ B', p) % 8 = 7 ∨ (∏ p ∈ B', p) % 8 = 3 ∨
          (∏ p ∈ B', p) % 8 = 1 := by
      refine ⟨h1.2, fun B' hB' => ?_⟩
      rcases Finset.mem_insert.mp hB' with rfl | hB'
      · exact Or.inl hB7
      · rcases h1.1 B' hB' with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
    rw [ite_eq_left h2, ite_eq_left h3, ite_eq_left (hiff.mpr h1), mul_comm]
  · rw [ite_eq_right (fun h => h1 (hiff.mp h)), zero_mul]
    split_ifs with h2 h3
    · exfalso; refine h1 ⟨fun B' hB' => ?_, h3.1⟩
      rcases h3.2 B' (Finset.mem_insert_of_mem hB') with h | h | h
      · exact absurd h (h2 B' hB')
      · exact Or.inr h
      · exact Or.inl h
    · rfl
    · rfl

/-- **Matching** (nt-tyz §4.4, last line): the brackets in `Λ` are the fork's genus sums,
`Σ_{e≡5} Λ(n/e) g(e) = T_5a(n)` and `Σ_{e≡7} Λ(n/e) g(e) = T_5b(n)` (split a partition at its
unique block of class 5, resp. 7). -/
theorem matching {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), Lam (n / e) * (gNat e : ZMod 2) = T5aCl n ∧
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), Lam (n / e) * (gNat e : ZMod 2) = T5bCl n :=
  ⟨part_matching5a hn hsq, part_matching5b hn hsq⟩

/-! ### Lemma N1 from its core (uniqueness of the solution of the I2 recursion) -/

theorem mod8_div {m d : ℕ} (hd : d ∣ m) : m % 8 = (m / d % 8) * (d % 8) % 8 := by
  conv_lhs => rw [← Nat.div_mul_cancel hd]
  exact Nat.mul_mod _ _ _

theorem div_mod8_of {m d a b : ℕ} (hd : d ∣ m) (hm : m % 8 = a) (hdb : d % 8 = b)
    (hb : b = 1 ∨ b = 3 ∨ b = 5 ∨ b = 7) :
    m / d % 8 = (a * b) % 8 := by
  have h := mod8_div hd
  have hx : m / d % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [hm, hdb] at h
  subst hm hdb
  rcases hb with hb | hb | hb | hb <;> rw [hb] at h ⊢ <;>
    interval_cases hq : m / d % 8 <;> omega

/-- **Lemma N1**: `𝓛(m) ≡ Λ(m) (mod 2)` for squarefree `m ≡ 1, 3 (mod 8)`, from `L 1 = 1` and
`LemmaTwoEight` (TYZ Lemma 2.9 with Proposition 2.3, modulo 2). -/
theorem lemmaN1 {L : ℕ → ℤ} (h1 : L 1 = 1) (h2 : LemmaTwoEight L) :
    ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((L m : ℤ) : ZMod 2) = Lam m := by
  obtain ⟨c1, c2, c3⟩ := lemmaN1_core
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hsq hcl
  have hm0 : m ≠ 0 := hsq.ne_zero
  rcases hcl with h | h
  · by_cases hm1 : m = 1
    · subst hm1; rw [h1, c1]; simp
    have hm : 1 < m := by omega
    have hL := h2.1 m hsq hm h
    have hΛ := c2 m hsq hm h
    set D := m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m) with hD
    have h1D : 1 ∈ D := by
      rw [hD, Finset.mem_filter, Nat.mem_divisors]; exact ⟨⟨one_dvd _, hm0⟩, rfl, by omega⟩
    push_cast at hL
    rw [← Finset.add_sum_erase _ _ h1D] at hL hΛ
    have hrest : ∑ d ∈ D.erase 1, ((L d : ZMod 2) * (L (m / d) : ZMod 2)) =
        ∑ d ∈ D.erase 1, Lam d * Lam (m / d) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [hD, Finset.mem_erase, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨hd1, ⟨hdm, -⟩, hd8, hdd⟩ := hd
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdm; omega
      have hdlt : d < m := lt_of_le_of_lt (Nat.le_mul_self d) hdd
      have hqlt : m / d < m := Nat.div_lt_self (by omega) (by omega)
      have hq8 : m / d % 8 = 1 := by rw [div_mod8_of hdm h hd8 (Or.inl rfl)]
      rw [ih d hdlt (hsq.squarefree_of_dvd hdm) (Or.inl hd8),
        ih (m / d) hqlt (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)) (Or.inl hq8)]
    rw [hrest, Nat.div_one, h1] at hL
    rw [Nat.div_one, c1] at hΛ
    simp only [Int.cast_one, one_mul] at hL hΛ
    exact add_right_cancel (hL.trans hΛ.symm)
  · have hm : 1 < m := by omega
    have hL := h2.2 m hsq h
    have hΛ := c3 m hsq h
    set D := m.divisors.filter (fun d => d % 8 = 1) with hD
    have h1D : 1 ∈ D := by
      rw [hD, Finset.mem_filter, Nat.mem_divisors]; exact ⟨⟨one_dvd _, hm0⟩, rfl⟩
    push_cast at hL
    rw [← Finset.add_sum_erase _ _ h1D] at hL hΛ
    have hrest : ∑ d ∈ D.erase 1, ((L (m / d) : ZMod 2) * (L d : ZMod 2)) =
        ∑ d ∈ D.erase 1, Lam (m / d) * Lam d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [hD, Finset.mem_erase, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨hd1, ⟨hdm, -⟩, hd8⟩ := hd
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdm; omega
      have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdm
      have hdlt : d < m := lt_of_le_of_ne hdle (by rintro rfl; omega)
      have hqlt : m / d < m := Nat.div_lt_self (by omega) (by omega)
      have hq8 : m / d % 8 = 3 := by rw [div_mod8_of hdm h hd8 (Or.inl rfl)]
      rw [ih d hdlt (hsq.squarefree_of_dvd hdm) (Or.inl hd8),
        ih (m / d) hqlt (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)) (Or.inr hq8)]
    rw [hrest, Nat.div_one, h1] at hL
    rw [Nat.div_one, c1] at hΛ
    simp only [Int.cast_one, mul_one] at hL hΛ
    exact add_right_cancel (hL.trans hΛ.symm)

/-! ### Proposition N -/

/-- `𝓛(n) = 0` forces both genus sums to vanish (reading A of TYZ Theorem 3.5(2), `n ≡ 5`). -/
theorem genusSums_eq_zero {L : ℕ → ℤ} (hL1 : L 1 = 1) (h28 : LemmaTwoEight L) {n : ℕ}
    (hn : n % 8 = 5) (hsq : Squarefree n) (G : GenusData L n) (hL : L n = 0) :
    T5aCl n = 0 ∧ T5bCl n = 0 := by
  obtain ⟨X, hX⟩ := lemmaN2 G hn hsq hL1
  obtain ⟨h5, h7⟩ := finalStep G hn hL hX
  obtain ⟨m5, m7⟩ := matching hn hsq
  have key : ∀ c : ℕ, (c = 5 ∨ c = 7) →
      (((∑ e ∈ n.divisors.filter (fun e => e % 8 = c), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2)) =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = c), Lam (n / e) * (gNat e : ZMod 2) := by
    intro c hc
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hen, -⟩, he8⟩ := he
    have hq : n / e % 8 = 1 ∨ n / e % 8 = 3 := by
      rw [div_mod8_of hen hn he8 (by omega)]; rcases hc with rfl | rfl <;> norm_num
    rw [lemmaN1 hL1 h28 (n / e) (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hen)) hq]
  constructor
  · rw [← m5, ← key 5 (Or.inl rfl), h5]
  · rw [← m7, ← key 7 (Or.inr rfl), h7]

/-- **`TYZRow5b` from the TYZ inputs** (Proposition N, row `(7, 3)`). -/
theorem tyzRow5b_of_tyzInputs (h : TYZInputs) : TYZRow5b := by
  obtain ⟨L, hL1, h28, hI7, hG⟩ := h
  intro d hd hsq h5b
  by_cases hLd : L d = 0
  · exfalso
    obtain ⟨G⟩ := hG d hd hsq
    have h0 := (genusSums_eq_zero hL1 h28 hd hsq G hLd).2
    rw [h0] at h5b
    exact zero_ne_one h5b
  · exact hI7 d hd hsq hLd

/-- **Reading A of TYZ Theorem 3.5(2) for `n ≡ 5 (mod 8)`** (both rows) from the TYZ inputs. -/
theorem tyzThm35ReadingA_of_tyzInputs (h : TYZInputs) : TYZThm35ReadingA := by
  obtain ⟨L, hL1, h28, hI7, hG⟩ := h
  intro d hd hsq F hF h2
  obtain ⟨G⟩ := hG d hd hsq
  refine genusSums_eq_zero hL1 h28 hd hsq G ?_
  by_contra hLd
  obtain ⟨F', hF', hle⟩ := hI7 d hd hsq hLd
  rw [hF'.eq hF] at hle
  exact absurd (hle.trans_lt (by norm_num)) (not_lt.mpr h2)


/-! ### Consistency of `GenusData` (sanity check, no `sorry`)

For any `L` and `n` with `L n ≠ 0` (so that `torsion_of_zero` is vacuous) and any values of `g`,
the fields of `GenusData` are jointly satisfiable (`genusData_nonempty`): `M = ℤ[i]/(2+2i) ×
(ℕ →₀ ℤ[i])`, `τ` the inclusion of the first factor, `Z e` the basis vectors,
`β (t, v) = (t + Σ_e v_e c_e, −v)`, `P` defined by the recursion. So no field (τ's kernel, the
torsion statement, `β_τ`, I5) contradicts the others.

For `L n = 0`, where all of the content of `GenusData` sits (I7 forces `L n = 0` at every
squarefree `n ≡ 5` of analytic rank at least two, e.g. `n = 26565`), `witnessData₀` modifies the
model at `n` only: `Z n := Sw L n`, the correction term of the recursion, and `P n := 0`. The
recursion then reads `0 = Sw − Sw` at `n`, `torsion_of_zero` is trivial, and `beta_five` at `e = n`
follows from the two parities of `finalStep`'s conclusion hold (via `lemmaN2` applied to the
first witness, `Φw_Sw`). Hence `genusData_nonempty_iff_parities`: for squarefree `n ≡ 5 (mod 8)`
with `L 1 = 1` and `L n = 0`, `GenusData L n` is inhabited if and only if
`Σ_{e≡5} L(n/e) g(e)` and `Σ_{e≡7} L(n/e) g(e)` are even (`lemmaN2` and `finalStep` give one
direction, `genusData_nonempty_of_parities` the other). With `genusData_nonempty`, this shows that
the content of `GenusData` is exactly the conclusion of Proposition N's final step. Under
`LemmaTwoEight L`, `lemmaN1` and `matching` turn the two parities into `T5aCl n = 0` and
`T5bCl n = 0` (as in `genusSums_eq_zero`), i.e. into the `n`-instance of reading A of TYZ
Theorem 3.5(2). (Readings B and C fail at `n = 26565`, where `GenusData 𝓛 26565` is inhabited
because `T5aCl = T5bCl = 0` there.) So `GenusData` asks for nothing beyond reading A: taking
`L = Λ` on classes 1 and 3, `TYZInputs` holds whenever reading A and Hecke's continuation do (this
last assembly, `tyzInputs_iff` of `rv-pn-encoding` F1, is not written in Lean). Since
`tyzThm35ReadingA_of_tyzInputs` is proved, `TYZInputs` is not weaker than reading A either: its
trust rests on the faithfulness of each field (`pn-design` §2, `TYZInputs.lean`). -/

namespace Witness

/-- The torsion part `ℤ[i]/(2+2i) ≅ A[(1+i)³]`. -/
abbrev Tq : Type := GaussianInt ⧸ Ideal.span {twoTwoI}

/-- The module `ℤ[i]/(2+2i) × (ℕ →₀ ℤ[i])`. -/
abbrev Mw : Type := Tq × (ℕ →₀ GaussianInt)

/-- The values of `Z(e)^{β+1}` prescribed by I5. -/
def cw (e : ℕ) : Tq :=
  if e % 8 = 5 then (gNat e : ℤ) • Ideal.Quotient.mk _ (⟨1, -1⟩ : GaussianInt)
  else (gNat e : ℤ) • Ideal.Quotient.mk _ (1 : GaussianInt)

def epsW (d₀ d₁ : ℕ) : GaussianInt := if d₀ % 8 = 5 ∧ d₁ % 8 = 3 then gi else 1

def Zw (e : ℕ) : Mw := (0, Finsupp.single e 1)

/-- `P` defined by the recursion of TYZ §3.1. -/
def Pw (L : ℕ → ℤ) : ℕ → Mw
  | d => Zw d - ∑ d₁ ∈ (d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3))).attach,
      (epsW (d / d₁) d₁ * (L d₁ : GaussianInt)) • Pw L (d / d₁)
decreasing_by
  have h := d₁.2
  simp only [Finset.mem_filter, Nat.mem_divisors] at h
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h.1.2) h.2.1

theorem Pw_eq (L : ℕ → ℤ) (d : ℕ) :
    Pw L d = Zw d - ∑ d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3)),
      (epsW (d / d₁) d₁ * (L d₁ : GaussianInt)) • Pw L (d / d₁) := by
  rw [Pw]
  congr 1
  exact Finset.sum_attach _ (fun d₁ => (epsW (d / d₁) d₁ * (L d₁ : GaussianInt)) • Pw L (d / d₁))

def τw : GaussianInt →+ Mw :=
  (AddMonoidHom.inl Tq (ℕ →₀ GaussianInt)).comp (Ideal.Quotient.mk (Ideal.span {twoTwoI})).toAddMonoidHom

def βw : Mw →+ Mw where
  toFun x := (x.1 + Finsupp.linearCombination GaussianInt cw x.2, -x.2)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp [map_add] <;> abel

theorem torsionFree_finsupp {v : ℕ →₀ GaussianInt} {k : ℕ} (hk : 0 < k) (h : k • v = 0) : v = 0 := by
  refine Finsupp.ext fun i => ?_
  have h' := congrArg (fun w => w i) h
  simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, nsmul_eq_mul] at h'
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd h0 (by exact_mod_cast hk.ne')
  · simpa using h0

/-- The witness. -/
def witnessData (L : ℕ → ℤ) (n : ℕ) (hL : L n ≠ 0) : GenusData L n where
  M := Mw
  Z := Zw
  P := Pw L
  ε := epsW
  eps_53 := by intro d₀ d₁ _ h5 h3; left; simp [epsW, h5, h3]
  eps_pm1 := by
    intro d₀ d₁ _ h; left; simp only [epsW]; split_ifs with h'
    · omega
    · rfl
  recursion := by intro d _ _; exact Pw_eq L d
  torsion_of_zero := by intro h; exact absurd h hL
  τ := τw
  τ_eq_zero := by
    intro y
    simp only [τw, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, Prod.mk_eq_zero, and_true]
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  tors_mem_range := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).mp hx
    have h2 : x.2 = 0 := torsionFree_finsupp hk (by simpa using congrArg Prod.snd hkx)
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective x.1
    exact ⟨y, by ext <;> simp [τw, hy, h2]⟩
  β := βw
  β_τ := by intro y; ext <;> simp [τw, βw]
  beta_five := by
    intro e _ h5
    refine ⟨0, ?_⟩
    ext <;> simp [βw, Zw, τw, cw, h5]
  beta_seven := by
    intro e _ h7
    have h5 : ¬ e % 8 = 5 := by omega
    ext <;> simp [βw, Zw, τw, cw, h5]

theorem genusData_nonempty (L : ℕ → ℤ) (n : ℕ) (hL : L n ≠ 0) : Nonempty (GenusData L n) :=
  ⟨witnessData L n hL⟩

/-! #### The witness for `L n = 0` (`rv-pn-encoding` F1) -/

/-- `Pw L` reads `L` only on the classes `1, 3 (mod 8)`. -/
theorem Pw_congr {L L' : ℕ → ℤ} (h : ∀ q, (q % 8 = 1 ∨ q % 8 = 3) → L q = L' q) :
    Pw L = Pw L' := by
  funext d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rw [Pw_eq, Pw_eq L']
    congr 1
    refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd₁
    rw [h d₁ hd₁.2.2, ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero hd₁.1.2) hd₁.2.1)]

/-- The points `Pw L d` have zero torsion component. -/
theorem Pw_fst (L : ℕ → ℤ) (d : ℕ) : (Pw L d).1 = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rw [Pw_eq, Prod.fst_sub, Prod.fst_sum]
    simp only [Prod.smul_fst, Zw, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun d₁ hd₁ => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd₁
    rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero hd₁.1.2) hd₁.2.1), smul_zero]

/-- The correction term of the recursion at `n`: `Pw L n = Zw n − Sw L n`. -/
def Sw (L : ℕ → ℤ) (n : ℕ) : Mw :=
  ∑ q ∈ n.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
    (epsW (n / q) q * (L q : GaussianInt)) • Pw L (n / q)

theorem Pw_eq_sub (L : ℕ → ℤ) (n : ℕ) : Pw L n = Zw n - Sw L n := Pw_eq L n

theorem Sw_fst (L : ℕ → ℤ) (n : ℕ) : (Sw L n).1 = 0 := by
  rw [Sw, Prod.fst_sum]
  exact Finset.sum_eq_zero fun q _ => by rw [Prod.smul_fst, Pw_fst, smul_zero]

/-- `Φ = λ ∘ pr₂`, where `λ = Σ_e v_e c_e`; `βw x + x = (2 x.1 + Φ x, 0)`. -/
def Φw : Mw →+ Tq :=
  (Finsupp.linearCombination GaussianInt cw).toAddMonoidHom.comp
    (AddMonoidHom.snd Tq (ℕ →₀ GaussianInt))

theorem Φw_Zw (e : ℕ) : Φw (Zw e) = cw e := by
  simp [Φw, Zw, Finsupp.linearCombination_single]

/-- The key identity for `beta_five` at `e = n`: with `a = Σ_{e≡5} L(n/e) g(e)` and
`N = Σ_{e≡7} L(n/e) g(e)` both even, `Φ(Sw L n) ∈ g(n) τ(1−i) + ℤ τ(2)` in `Tq`. -/
theorem Φw_Sw {L : ℕ → ℤ} {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) (hL1 : L 1 = 1)
    (h5 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0))
    (h7 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0)) :
    ∃ k : ℤ, Φw (Sw L n) = (gNat n : ℤ) • Ideal.Quotient.mk _ (⟨1, -1⟩ : GaussianInt) +
      k • Ideal.Quotient.mk (Ideal.span {twoTwoI}) (2 : GaussianInt) := by
  classical
  have hn1 : n ≠ 1 := by omega
  set L' := Function.update L n 1 with hL'
  have hL'n : L' n ≠ 0 := by simp [hL']
  have hL'1 : L' 1 = 1 := by rw [hL', Function.update_of_ne (Ne.symm hn1), hL1]
  obtain ⟨X, hX⟩ := lemmaN2 (witnessData L' n hL'n) hn hsq hL'1
  have hPw : Pw L' = Pw L :=
    Pw_congr fun q hq => by rw [hL', Function.update_of_ne (by omega)]
  set Xw : Mw := X with hXw
  have hX' : Pw L' n = ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
      L' (n / e) • Zw e + (2 : ℤ) • Xw := hX
  clear_value Xw
  rw [hPw, Pw_eq_sub] at hX'
  clear hX
  have hX := hX'
  have hΦ := congrArg Φw hX
  simp only [map_sub, map_add, map_sum, map_zsmul, Φw_Zw] at hΦ
  -- the coefficients `L'(n/e) = L(n/e)` (`n/e < n`)
  have hcoef : ∀ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
      L' (n / e) = L (n / e) := by
    intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    rw [hL', Function.update_of_ne]
    exact (Nat.div_lt_self (by omega) (by omega)).ne
  rw [Finset.sum_congr rfl fun e he => by rw [hcoef e he]] at hΦ
  set F5 := n.divisors.filter (fun e => e % 8 = 5) with hF5
  set F7 := n.divisors.filter (fun e => e % 8 = 7) with hF7
  have hsplit : n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7) = F5 ∪ F7 :=
    Finset.filter_or _ _ _
  have hdisj : Disjoint F5 F7 :=
    Finset.disjoint_filter.2 (fun _ _ h1 h2 => by omega)
  set a := ∑ e ∈ F5, L (n / e) * (gNat e : ℤ) with ha
  set N := ∑ e ∈ F7, L (n / e) * (gNat e : ℤ) with hN
  let mk := Ideal.Quotient.mk (Ideal.span {twoTwoI})
  have hs5 : ∑ e ∈ F5, L (n / e) • cw e = mk (a • (⟨1, -1⟩ : GaussianInt)) := by
    rw [map_zsmul, ha, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hF5, Finset.mem_filter] at he
    rw [cw, ite_eq_left he.2, smul_smul]
  have hs7 : ∑ e ∈ F7, L (n / e) • cw e = mk (N • (1 : GaussianInt)) := by
    rw [map_zsmul, hN, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hF7, Finset.mem_filter] at he
    rw [cw, ite_eq_right (by omega), smul_smul]
  rw [hsplit, Finset.sum_union hdisj, hs5, hs7] at hΦ
  have hcwn : cw n = mk ((gNat n : ℤ) • (⟨1, -1⟩ : GaussianInt)) := by
    rw [cw, ite_eq_left hn, map_zsmul]
  rw [hcwn] at hΦ
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (Φw Xw)
  rw [← hx] at hΦ
  obtain ⟨a₁, ha₁⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h5
  obtain ⟨N₁, hN₁⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd N 2).mp h7
  refine ⟨-N₁ - x.re + x.im, ?_⟩
  have hS : Φw (Sw L n) = mk ((gNat n : ℤ) • (⟨1, -1⟩ : GaussianInt) - a • (⟨1, -1⟩ : GaussianInt)
      - N • (1 : GaussianInt) - (2 : ℤ) • x) := by
    rw [map_sub, map_sub, map_sub, map_zsmul _ (2 : ℤ) x]
    rw [← sub_eq_zero] at hΦ ⊢
    rw [← neg_eq_zero, ← hΦ]; abel
  rw [hS, ← map_zsmul, ← map_zsmul, ← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨-x.im, a₁⟩, ?_⟩
  ext <;> simp [twoTwoI, ha₁, hN₁] <;> ring

/-- The witness for `L n = 0` (`rv-pn-encoding` F1): as `witnessData`, but `Z n := Sw L n` and
`P n := 0`. It needs the two parities of `finalStep`'s conclusion, for `beta_five` at `e = n`. -/
def witnessData₀ (L : ℕ → ℤ) (n : ℕ) (hn : n % 8 = 5) (hsq : Squarefree n) (hL1 : L 1 = 1)
    (h5 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0))
    (h7 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0)) : GenusData L n where
  M := Mw
  Z := Function.update Zw n (Sw L n)
  P := Function.update (Pw L) n 0
  ε := epsW
  eps_53 := (witnessData (Function.update L n 1) n (by simp)).eps_53
  eps_pm1 := (witnessData (Function.update L n 1) n (by simp)).eps_pm1
  recursion := by
    intro d hd _
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hn0 : n ≠ 0 := by omega
    -- `P (d / d₁) = Pw L (d / d₁)`, since `d / d₁ < d ≤ n`
    have hsum : ∀ d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3)),
        (epsW (d / d₁) d₁ * (L d₁ : GaussianInt)) • Function.update (Pw L) n 0 (d / d₁) =
        (epsW (d / d₁) d₁ * (L d₁ : GaussianInt)) • Pw L (d / d₁) := by
      intro d₁ hd₁
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd₁
      rw [Function.update_of_ne]
      exact ((Nat.div_lt_self (Nat.pos_of_ne_zero hd₁.1.2) hd₁.2.1).trans_le
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn)).ne
    rw [Finset.sum_congr rfl hsum]
    by_cases hdn' : d = n
    · subst hdn'
      rw [Function.update_self, Function.update_self]
      exact (sub_self _).symm
    · rw [Function.update_of_ne hdn', Function.update_of_ne hdn']
      exact Pw_eq L d
  torsion_of_zero := by
    intro _
    rw [Function.update_self]
    exact IsOfFinAddOrder.zero
  τ := τw
  τ_eq_zero := (witnessData (Function.update L n 1) n (by simp)).τ_eq_zero
  tors_mem_range := (witnessData (Function.update L n 1) n (by simp)).tors_mem_range
  β := βw
  β_τ := (witnessData (Function.update L n 1) n (by simp)).β_τ
  beta_five := by
    intro e he h5e
    by_cases hen : e = n
    · subst hen
      rw [Function.update_self]
      obtain ⟨k, hk⟩ := Φw_Sw hn hsq hL1 h5 h7
      refine ⟨k, ?_⟩
      have hΦ : (βw (Sw L e) + Sw L e) = (Φw (Sw L e), 0) := by
        refine Prod.ext ?_ ?_
        · simp only [βw, Prod.fst_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sw_fst, zero_add,
            add_zero]
          rfl
        · show -(Sw L e).2 + (Sw L e).2 = 0
          exact neg_add_cancel _
      rw [hΦ, hk]
      ext <;> simp [τw]
    · rw [Function.update_of_ne hen]
      exact (witnessData (Function.update L n 1) n (by simp)).beta_five e he h5e
  beta_seven := by
    intro e he h7e
    rw [Function.update_of_ne (by omega)]
    exact (witnessData (Function.update L n 1) n (by simp)).beta_seven e he h7e

/-- **`GenusData`'s content for `L n = 0` is exactly the conclusion of Proposition N's final step**
(`rv-pn-encoding` F1): for squarefree `n ≡ 5 (mod 8)` with `L 1 = 1` and `L n = 0`, `GenusData L n`
is inhabited if and only if `Σ_{e≡5} L(n/e) g(e)` and `Σ_{e≡7} L(n/e) g(e)` are even. -/
theorem genusData_nonempty_iff_parities (L : ℕ → ℤ) (n : ℕ) (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL1 : L 1 = 1) (hL : L n = 0) :
    Nonempty (GenusData L n) ↔
      ((((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) :
        ZMod 2) = 0) ∧
      (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) :
        ZMod 2) = 0)) := by
  constructor
  · rintro ⟨G⟩
    obtain ⟨X, hX⟩ := lemmaN2 G hn hsq hL1
    exact finalStep G hn hL hX
  · rintro ⟨h5, h7⟩
    exact ⟨witnessData₀ L n hn hsq hL1 h5 h7⟩

/-- **Consistency of `GenusData` when `L n = 0`**: for squarefree `n ≡ 5 (mod 8)` with `L 1 = 1`,
`L n = 0` and the two parities of `finalStep`'s conclusion, `GenusData L n` is inhabited. -/
theorem genusData_nonempty_of_parities (L : ℕ → ℤ) (n : ℕ) (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL1 : L 1 = 1) (hL : L n = 0)
    (h5 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0))
    (h7 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0)) :
    Nonempty (GenusData L n) :=
  (genusData_nonempty_iff_parities L n hn hsq hL1 hL).mpr ⟨h5, h7⟩

end Witness
end ZInQ.PropN
