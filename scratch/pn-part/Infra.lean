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

end part_generic

end ZInQ.PropN
