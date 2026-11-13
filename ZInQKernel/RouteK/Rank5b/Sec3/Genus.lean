import ZInQKernel.RouteK.Rank5b.Sec3.Count

/-!
# The genus sum: block weights as forest sums, and the marked form of `T_5b`

For a block `B`, write `g(B)` restricted to a class as a sum over the forests of `B`:

* class 7 (`blockW7`): `Σ_{g ∈ allF B, one root ρ} (y_ρ + z_ρ) wt(g) y(B)` (by (2.1));
* class 3 (`blockW3`): `Σ_{g ∈ allF B, one root ρ} z_ρ wt(g) y(B)` (by (2.1));
* class 1 (`blockW1`): `Σ_{g ∈ allF B, two roots i, j} z_i z_j wt(g) y(T_i) y(T_j)` — by Lemma 2.2(3) and
  `(1 + y(B)) c(T_i) = y(T_i) y(T_j)`, as in the proof of tyz-5b Proposition 3.5.

`genusSum5b_eq_marked`: `T_5b = Σ_π Σ_{B₇ ∈ π} Σ_{B₃ ∈ π, B₃ ≠ B₇} w₇(B₇) w₃(B₃) Π_{B ≠ B₇, B₃} w₁(B)`.
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The products of the tree sums `Π_{ρ∈F} Σ_{v ∈ U, root v = ρ} y_v`. -/
def treeY (y : ι → ZMod 2) (U F : Finset ι) (f : ι → ι) : ZMod 2 :=
  ∏ ρ ∈ F, ∑ v ∈ U.filter (fun v => root f v = ρ), y v

/-- The forest weight of a block: `[#roots = k] e(roots) wt(g) treeY`. -/
def blockH (a : ι → ι → ZMod 2) (y : ι → ZMod 2) (k : ℕ) (e : Finset ι → ZMod 2) (B : Finset ι)
    (g : ι → ι) : ZMod 2 :=
  if (rootsOf B g).card = k then
    e (rootsOf B g) * wt a (B \ rootsOf B g) g * treeY y B (rootsOf B g) g else 0

/-- `w₇(B) = [B has class 7] g(B)`. -/
noncomputable def w7 (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) (B : Finset ι) : ZMod 2 :=
  if ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0 then redeiG a y z B else 0

/-- `w₃(B) = [B has class 3] g(B)`. -/
noncomputable def w3 (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) (B : Finset ι) : ZMod 2 :=
  if ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1 then redeiG a y z B else 0

/-- `w₁(B) = [B has class 1] g(B)`. -/
noncomputable def w1 (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) (B : Finset ι) : ZMod 2 :=
  if ∑ i ∈ B, y i = 0 ∧ ∑ i ∈ B, z i = 0 then redeiG a y z B else 0

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

theorem sum_powerset_card_one (B : Finset ι) (H : Finset ι → ZMod 2) :
    ∑ F ∈ B.powerset, (if F.card = 1 then H F else 0) = ∑ ρ ∈ B, H {ρ} := by
  rw [← Finset.sum_filter]
  rw [show B.powerset.filter (fun F => F.card = 1) = B.powersetCard 1 by
    ext F; simp [Finset.mem_powersetCard]]
  rw [Finset.powersetCard_one, Finset.sum_map]
  rfl

theorem sum_powerset_card_eq (B : Finset ι) (k : ℕ) (H : Finset ι → ZMod 2) :
    ∑ F ∈ B.powerset, (if F.card = k then H F else 0) = ∑ F ∈ B.powersetCard k, H F := by
  rw [← Finset.sum_filter]
  congr 1
  ext F; simp [Finset.mem_powersetCard]

/-- `Σ_g blockH = Σ_{F ⊆ B, |F| = k} Σ_{g rooted at F} e(F) wt(g) treeY`. -/
theorem sum_blockH (a : ι → ι → ZMod 2) (y : ι → ZMod 2) (k : ℕ) (e : Finset ι → ZMod 2)
    (B : Finset ι) :
    ∑ g ∈ allF B, blockH a y k e B g = ∑ F ∈ B.powersetCard k, ∑ g ∈ forests B F,
      e F * wt a (B \ F) g * treeY y B F g := by
  have := sum_allF B (fun F g => if F.card = k then e F * wt a (B \ F) g * treeY y B F g else 0)
  unfold blockH
  rw [← this, ← sum_powerset_card_eq]
  refine Finset.sum_congr rfl fun F _ => ?_
  split_ifs <;> simp

theorem treeY_single {y : ι → ZMod 2} {B : Finset ι} {ρ : ι} {g : ι → ι}
    (hg : g ∈ forests B {ρ}) : treeY y B {ρ} g = ∑ i ∈ B, y i := by
  rw [treeY, Finset.prod_singleton]
  congr 1
  ext v
  simp only [Finset.mem_filter, and_iff_left_iff_imp]
  exact fun hv => Finset.mem_singleton.1 (root_mem_of_forests hg hv)

/-- Single-root forests: `Σ_ρ e_ρ y(B) κ_ρ(B) = Σ_{g ∈ allF B} [one root] e(roots) wt(g) treeY`. -/
theorem sum_kappa_eq_allF (a : ι → ι → ZMod 2) (y : ι → ZMod 2) (B : Finset ι)
    (e : Finset ι → ZMod 2) :
    ∑ ρ ∈ B, e {ρ} * (∑ i ∈ B, y i) * kappa a B ρ = ∑ g ∈ allF B, blockH a y 1 e B g := by
  rw [sum_blockH, Finset.powersetCard_one, Finset.sum_map]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [kappa_eq_forests a hρ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [treeY_single hg]
  ring

theorem w7_eq {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) (z : ι → ZMod 2)
    (B : Finset ι) :
    w7 a y z B = ∑ g ∈ allF B, blockH a y 1 (fun F => ∑ ρ ∈ F, (y ρ + z ρ)) B g := by
  rw [← sum_kappa_eq_allF]
  simp only [Finset.sum_singleton]
  rcases zmod2_cases (∑ i ∈ B, y i) with hy | hy
  · rw [w7, if_neg (by rw [hy]; simp), hy]; simp
  · rw [hy]
    simp only [mul_one, add_mul, Finset.sum_add_distrib, sum_y_kappa (z := z) hy,
      sum_z_kappa hrec hy]
    rw [w7]
    rcases zmod2_cases (∑ i ∈ B, z i) with hz | hz
    · rw [if_pos ⟨hy, hz⟩, hz]; ring
    · rw [if_neg (by rw [hz]; simp), hz, one_mul, CharTwo.add_self_eq_zero]

theorem w3_eq {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) (z : ι → ZMod 2)
    (B : Finset ι) :
    w3 a y z B = ∑ g ∈ allF B, blockH a y 1 (fun F => ∏ ρ ∈ F, z ρ) B g := by
  rw [← sum_kappa_eq_allF]
  simp only [Finset.prod_singleton]
  rcases zmod2_cases (∑ i ∈ B, y i) with hy | hy
  · rw [w3, if_neg (by rw [hy]; simp), hy]; simp
  · rw [hy]
    simp only [mul_one, sum_z_kappa hrec hy]
    rw [w3]
    rcases zmod2_cases (∑ i ∈ B, z i) with hz | hz
    · rw [if_neg (by rw [hz]; simp), hz, zero_mul]
    · rw [if_pos ⟨hy, hz⟩, hz, one_mul]

theorem sum_offDiag_eq (B : Finset ι) (G : ι × ι → ZMod 2) :
    ∑ p ∈ B.offDiag, G p = ∑ F ∈ B.powersetCard 2, ∑ p ∈ F.offDiag, G p := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ι × ι => ({p.1, p.2} : Finset ι))
    (t := B.powersetCard 2)]
  · refine Finset.sum_congr rfl fun F hF => ?_
    congr 1
    obtain ⟨hFB, hF2⟩ := Finset.mem_powersetCard.1 hF
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨-, -, hne⟩, rfl⟩
      simp [hne]
    · rintro ⟨h1, h2, hne⟩
      refine ⟨⟨hFB h1, hFB h2, hne⟩, ?_⟩
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · rw [hF2, Finset.card_pair hne]
  · intro p hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.1 hp
    rw [Finset.mem_powersetCard]
    refine ⟨fun x hx => ?_, Finset.card_pair hne⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption

theorem sum_offDiag_eq_erase (B : Finset ι) (G : ι × ι → ZMod 2) :
    ∑ p ∈ B.offDiag, G p = ∑ ρ ∈ B, ∑ j ∈ B.erase ρ, G (ρ, j) := by
  refine Finset.sum_finset_product _ _ _ fun p => ?_
  simp only [Finset.mem_offDiag, Finset.mem_erase]
  tauto

theorem w1_eq {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) (z : ι → ZMod 2)
    (B : Finset ι) :
    w1 a y z B = ∑ g ∈ allF B, blockH a y 2 (fun F => ∏ ρ ∈ F, z ρ) B g := by
  -- `w₁ = (1 + y(B)) (1 + z(B)) Σ_ρ z_ρ κ_ρ`
  have h1 : w1 a y z B = (1 + ∑ i ∈ B, y i) * ((1 + ∑ i ∈ B, z i) * ∑ ρ ∈ B, z ρ * kappa a B ρ) := by
    rw [w1]
    rcases zmod2_cases (∑ i ∈ B, y i) with hy | hy
    · rw [sum_z_kappa_of_y_zero hy, hy]
      rcases zmod2_cases (∑ i ∈ B, z i) with hz | hz
      · rw [if_pos ⟨rfl, hz⟩, hz]; ring
      · rw [if_neg (by rw [hz]; simp), hz, CharTwo.add_self_eq_zero]; ring
    · rw [if_neg (by rw [hy]; simp), hy, CharTwo.add_self_eq_zero, zero_mul]
  -- ordered pairs
  have h2 : (1 + ∑ i ∈ B, z i) * ∑ ρ ∈ B, z ρ * kappa a B ρ =
      ∑ p ∈ B.offDiag, z p.1 * z p.2 * kappa a B p.1 := by
    rw [sum_offDiag_eq_erase, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [← Finset.add_sum_erase B z hρ]
    simp only
    rw [show ∑ j ∈ B.erase ρ, z ρ * z j * kappa a B ρ = z ρ * (∑ j ∈ B.erase ρ, z j) * kappa a B ρ by
      rw [Finset.mul_sum, Finset.sum_mul]]
    have h2 : (2 : ZMod 2) = 0 := rfl
    rcases zmod2_cases (z ρ) with h | h <;> rw [h]
    · ring
    · linear_combination (kappa a B ρ) * h2
  rw [h1, h2, sum_offDiag_eq, Finset.mul_sum, sum_blockH]
  refine Finset.sum_congr rfl fun F hF => ?_
  obtain ⟨hFB, hF2⟩ := Finset.mem_powersetCard.1 hF
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hF2
  have hi : i ∈ B := hFB (by simp)
  have hj : j ∈ B := hFB (by simp)
  have hoff : ({i, j} : Finset ι).offDiag = {(i, j), (j, i)} := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton]
    rcases p with ⟨p1, p2⟩
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl | rfl, rfl | rfl, hne⟩ <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hij, Ne.symm hij]
  rw [hoff, Finset.sum_pair (by simp [hij])]
  simp only
  rw [show z i * z j * kappa a B i + z j * z i * kappa a B j = z i * z j * (kappa a B i + kappa a B j)
    by ring, kappa_add_kappa a hi hj hij, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  -- `(1 + y(B)) c(T_i) = y(T_i) y(T_j)`
  have hcol : ∑ v ∈ B.filter (fun v => root g v = i), colSum a B v =
      (∑ v ∈ B.filter (fun v => root g v = i), y v) * (∑ u ∈ B, y u + 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun v hv => colSum_lapl hrec (Finset.mem_filter.1 hv).1
  have hyB : ∑ u ∈ B, y u = (∑ v ∈ B.filter (fun v => root g v = i), y v) +
      ∑ v ∈ B.filter (fun v => root g v = j), y v := by
    rw [← Finset.sum_pair (f := fun ρ => ∑ v ∈ B.filter (fun v => root g v = ρ), y v) hij]
    exact (Finset.sum_fiberwise_of_maps_to (fun v hv => root_mem_of_forests hg hv) y).symm
  have htree : treeY y B {i, j} g = (∑ v ∈ B.filter (fun v => root g v = i), y v) *
      ∑ v ∈ B.filter (fun v => root g v = j), y v := by
    rw [treeY, Finset.prod_pair hij]
  rw [hcol, htree, Finset.prod_pair hij]
  set Ti := ∑ v ∈ B.filter (fun v => root g v = i), y v
  set Tj := ∑ v ∈ B.filter (fun v => root g v = j), y v
  rw [hyB]
  rcases zmod2_cases Ti with h | h <;> rcases zmod2_cases Tj with h' | h' <;> rw [h, h'] <;>
    ring_nf <;> reduce_mod_char

/-! ### The marked form of `T_5b` -/

/-- The weight of block `B` once the blocks `B₇` and `B₃` are marked. -/
noncomputable def markW (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) (B7 B3 B : Finset ι) : ZMod 2 :=
  if B = B7 then w7 a y z B else if B = B3 then w3 a y z B else w1 a y z B

theorem w7_eq_zero {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} {B : Finset ι}
    (h : ¬(∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0)) : w7 a y z B = 0 := by rw [w7, if_neg h]

theorem w3_eq_zero {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} {B : Finset ι}
    (h : ¬(∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1)) : w3 a y z B = 0 := by rw [w3, if_neg h]

theorem w1_eq_zero {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} {B : Finset ι}
    (h : ¬(∑ i ∈ B, y i = 0 ∧ ∑ i ∈ B, z i = 0)) : w1 a y z B = 0 := by rw [w1, if_neg h]

/-- A nonzero marked product forces the classes: `B₇` of class 7, `B₃` of class 3, the others of
class 1. -/
theorem classes_of_markW_ne_zero {a : ι → ι → ZMod 2} {y z : ι → ZMod 2}
    {P : Finpartition (univ : Finset ι)} {B7 B3 : Finset ι} (h7 : B7 ∈ P.parts)
    (h3 : B3 ∈ P.parts.erase B7) (hne : ∏ B ∈ P.parts, markW a y z B7 B3 B ≠ 0) :
    (∑ i ∈ B7, y i = 1 ∧ ∑ i ∈ B7, z i = 0) ∧ (∑ i ∈ B3, y i = 1 ∧ ∑ i ∈ B3, z i = 1) ∧
      ∀ B ∈ P.parts, B ≠ B7 → B ≠ B3 → (∑ i ∈ B, y i = 0 ∧ ∑ i ∈ B, z i = 0) := by
  have hfac := Finset.prod_ne_zero_iff.1 hne
  obtain ⟨h37, h3'⟩ := Finset.mem_erase.1 h3
  refine ⟨?_, ?_, fun B hB hB7 hB3 => ?_⟩
  · by_contra hc
    have := hfac B7 h7
    rw [markW, if_pos rfl, w7_eq_zero hc] at this
    exact this rfl
  · by_contra hc
    have := hfac B3 h3'
    rw [markW, if_neg h37, if_pos rfl, w3_eq_zero hc] at this
    exact this rfl
  · by_contra hc
    have := hfac B hB
    rw [markW, if_neg hB7, if_neg hB3, w1_eq_zero hc] at this
    exact this rfl

/-- **Marked form of the genus sum**:
`T_5b = Σ_π Σ_{B₇ ∈ π} Σ_{B₃ ∈ π, B₃ ≠ B₇} Π_B markW(B₇, B₃, B)`. -/
theorem genusSum5b_eq_marked (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) :
    genusSum5b a y z = ∑ P : Finpartition (univ : Finset ι), ∑ B7 ∈ P.parts,
      ∑ B3 ∈ P.parts.erase B7, ∏ B ∈ P.parts, markW a y z B7 B3 B := by
  unfold genusSum5b
  refine Finset.sum_congr rfl fun P _ => ?_
  split_ifs with hadm
  · obtain ⟨h7c, h3c, h5⟩ := hadm
    obtain ⟨B7, hB7⟩ := Finset.card_eq_one.1 h7c
    obtain ⟨B3, hB3⟩ := Finset.card_eq_one.1 h3c
    have hB7m : B7 ∈ P.parts.filter _ := hB7 ▸ Finset.mem_singleton_self B7
    have hB3m : B3 ∈ P.parts.filter _ := hB3 ▸ Finset.mem_singleton_self B3
    obtain ⟨hB7p, hc7⟩ := Finset.mem_filter.1 hB7m
    obtain ⟨hB3p, hc3⟩ := Finset.mem_filter.1 hB3m
    have hne : B3 ≠ B7 := by
      rintro rfl; rw [hc7.2] at hc3; exact zero_ne_one hc3.2
    have huniq7 : ∀ B ∈ P.parts, (∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0) → B = B7 := fun B hB hc => by
      have : B ∈ P.parts.filter (fun B => ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0) :=
        Finset.mem_filter.2 ⟨hB, hc⟩
      rw [hB7] at this; exact Finset.mem_singleton.1 this
    have huniq3 : ∀ B ∈ P.parts, (∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1) → B = B3 := fun B hB hc => by
      have : B ∈ P.parts.filter (fun B => ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1) :=
        Finset.mem_filter.2 ⟨hB, hc⟩
      rw [hB3] at this; exact Finset.mem_singleton.1 this
    rw [Finset.sum_eq_single B7, Finset.sum_eq_single B3]
    · refine Finset.prod_congr rfl fun B hB => ?_
      unfold markW
      split_ifs with h1 h2
      · subst h1; rw [w7, if_pos hc7]
      · subst h2; rw [w3, if_pos hc3]
      · rw [w1, if_pos]
        rcases zmod2_cases (∑ i ∈ B, y i) with hy | hy <;>
          rcases zmod2_cases (∑ i ∈ B, z i) with hz | hz
        · exact ⟨hy, hz⟩
        · exact absurd ⟨hy, hz⟩ (h5 B hB)
        · exact absurd (huniq7 B hB ⟨hy, hz⟩) h1
        · exact absurd (huniq3 B hB ⟨hy, hz⟩) h2
    · intro B3' hB3' hne'
      refine Finset.prod_eq_zero (Finset.mem_of_mem_erase hB3') ?_
      rw [markW, if_neg (Finset.ne_of_mem_erase hB3'), if_pos rfl]
      exact w3_eq_zero fun hc => hne' (huniq3 B3' (Finset.mem_of_mem_erase hB3') hc)
    · intro h; exact absurd (Finset.mem_erase.2 ⟨hne, hB3p⟩) h
    · intro B7' hB7' hne'
      refine Finset.sum_eq_zero fun B3' _ => Finset.prod_eq_zero hB7' ?_
      rw [markW, if_pos rfl]
      exact w7_eq_zero fun hc => hne' (huniq7 B7' hB7' hc)
    · intro h; exact absurd hB7p h
  · symm
    refine Finset.sum_eq_zero fun B7 hB7 => Finset.sum_eq_zero fun B3 hB3 => ?_
    by_contra hne
    obtain ⟨hc7, hc3, hc1⟩ := classes_of_markW_ne_zero hB7 hB3 hne
    obtain ⟨h37, hB3p⟩ := Finset.mem_erase.1 hB3
    apply hadm
    refine ⟨Finset.card_eq_one.2 ⟨B7, ?_⟩, Finset.card_eq_one.2 ⟨B3, ?_⟩, fun B hB hc5 => ?_⟩
    · ext B
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hB, hc⟩
        by_contra hBne
        by_cases hB3' : B = B3
        · subst hB3'; rw [hc.2] at hc3; exact zero_ne_one hc3.2
        · rw [(hc1 B hB hBne hB3').1] at hc; exact zero_ne_one hc.1
      · rintro rfl; exact ⟨hB7, hc7⟩
    · ext B
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hB, hc⟩
        by_contra hBne
        by_cases hB7' : B = B7
        · subst hB7'; rw [hc.2] at hc7; exact zero_ne_one hc7.2.symm
        · rw [(hc1 B hB hB7' hBne).1] at hc; exact zero_ne_one hc.1
      · rintro rfl; exact ⟨hB3p, hc3⟩
    · by_cases hB7' : B = B7
      · subst hB7'; rw [hc7.1] at hc5; exact one_ne_zero hc5.1
      by_cases hB3' : B = B3
      · subst hB3'; rw [hc3.1] at hc5; exact one_ne_zero hc5.1
      rw [(hc1 B hB hB7' hB3').2] at hc5; exact zero_ne_one hc5.2

end ZInQ.RouteK.Rank5b.Sec3
