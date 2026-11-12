import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import ZInQKernel.Hypotheses.CR3Literature

noncomputable section

namespace ZInQ.PropN

open ZInQ.Literature ZInQ.RouteK.Rank5b

def gNat (e : ℕ) : ℕ := if h : e = 0 then 0 else haveI : NeZero e := ⟨h⟩; gCl e

def LamAdm (m : ℕ) (P : Finpartition (Finset.univ : Finset m.primeFactors)) : Prop :=
  (∀ B ∈ P.parts, dProd B % 8 = 1 ∨ dProd B % 8 = 3) ∧
  (P.parts.filter fun B => dProd B % 8 = 3).card ≤ 1

instance (m : ℕ) (P : Finpartition (Finset.univ : Finset m.primeFactors)) :
    Decidable (LamAdm m P) := by
  unfold LamAdm; infer_instance

def Lam (m : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset m.primeFactors),
    if LamAdm m P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

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
    · rw [Finset.filter_insert, if_pos hCB, Finset.filter_eq_empty_iff.mpr hRC]; rfl
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

/-- `Λ` on a finset of primes. -/
def part_LamS (s : Finset ℕ) : ZMod 2 :=
  ∑ Q ∈ part_PS s, if part_LamAdm Q then part_wt Q else 0

theorem part_gNat_eq (e : ℕ) [NeZero e] : gNat e = gCl e := by
  unfold gNat; rw [dif_neg (NeZero.ne e)]

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

theorem part_matching_lhs {n : ℕ} (hn : Squarefree n) (c : ℕ) :
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = c), Lam (n / e) * (gNat e : ZMod 2) =
      ∑ B ∈ n.primeFactors.powerset.filter (fun B => (∏ q ∈ B, q) % 8 = c),
        part_LamS (n.primeFactors \ B) * (gNat (∏ q ∈ B, q) : ZMod 2) := by
  rw [part_sum_divisors hn]
  refine Finset.sum_congr rfl fun B hB => ?_
  rw [part_Lam_div hn (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)]

theorem part_ne_empty_of_mod {B : Finset ℕ} {c : ℕ} (hc : c ≠ 1) (h : (∏ q ∈ B, q) % 8 = c) :
    B ≠ ∅ := by
  rintro rfl; simp at h; omega

theorem part_not_mem_of_ne_empty {t B : Finset ℕ} {R : Finset (Finset ℕ)}
    (hR : part_IsP (t \ B) R) (hB0 : B ≠ ∅) : B ∉ R := by
  intro hBR
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hB0
  exact (Finset.mem_sdiff.mp (part_subset_of_mem hR hBR hx)).2 hx

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
    rw [if_pos h2, if_pos h3, if_pos (hiff.mpr h1), mul_comm]
  · rw [if_neg (fun h => h1 (hiff.mp h)), zero_mul]
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
    rw [Finset.filter_insert, if_neg (by rw [hB7]; norm_num)]
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
    rw [if_pos h2, if_pos h3, if_pos (hiff.mpr h1), mul_comm]
  · rw [if_neg (fun h => h1 (hiff.mp h)), zero_mul]
    split_ifs with h2 h3
    · exfalso; refine h1 ⟨fun B' hB' => ?_, h3.1⟩
      rcases h3.2 B' (Finset.mem_insert_of_mem hB') with h | h | h
      · exact absurd h (h2 B' hB')
      · exact Or.inr h
      · exact Or.inl h
    · rfl
    · rfl

theorem matching {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), Lam (n / e) * (gNat e : ZMod 2) = T5aCl n ∧
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), Lam (n / e) * (gNat e : ZMod 2) = T5bCl n :=
  ⟨part_matching5a hn hsq, part_matching5b hn hsq⟩

end ZInQ.PropN
