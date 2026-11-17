module

/- SPDX-License-Identifier: Apache-2.0
See docs/lean-applications/V15Application.LICENSE for the license text. -/

public import ZInQKernel.Contrib.V15RetainedContact
public import ZInQKernel.Contrib.V15RawRows

/-!
# The V15 trace quotient on the actual rational solution sets

Source: `trace-quotient222-116/PROOF.md` at
elliotglazer/diophantine-z-q@511529bbe9d635194f0c9d925709e77a5d3afa64.
This proves its local rational chart, without asserting independent protocol
acceptance of the packet or a defining theorem for the whole construction.

Parent operands: q=x96, Q=x98=q^2 (row 47), R2=x119=R^2 (row 68),
G=x222, Z=x223, and P=8*x4*x92. The special trace is
(x179-x181)^2+2*(x180-x182)^2. The other traces start at 165, 193 and 207.
Rows 186,196,197 are exactly the three consumers of G or Z.
The quotient uses U=Z/Q, G=R2*U, Z=Q*U, retaining coordinates 1..221.
No trace or U is inverted; zero traces and q=-1 remain in scope.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

public section

namespace V15RetainedContact

/-- One-based source coordinates, with no extra free coordinate. -/
def coord {n : ℕ} (x : Fin n → ℚ) (i : ℕ) : ℚ :=
  if h : 1 ≤ i ∧ i ≤ n then x ⟨i-1, by omega⟩ else 0

def Raw223Solution (A : ℚ) (x : Fin 223 → ℚ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ 197 → raw223Row A (coord x) i = 0

def Raw222Solution (A : ℚ) (x : Fin 222 → ℚ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ 196 → raw222Row A (coord x) i = 0

theorem raw223_retained (A : ℚ) (x : Fin 223 → ℚ) (h : Raw223Solution A x) :
    Retained A (coord x 1) (coord x 55) (coord x 92) (coord x 93)
      (coord x 94) (coord x 95) (coord x 96) (coord x 107) (coord x 108)
      (coord x 119) (coord x 120) (coord x 122) := by
  unfold Retained
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hx := h 9 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 43 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 44 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 45 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 46 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 56 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 57 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 68 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 71 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring
  · have hx := h 73 (by norm_num) (by norm_num)
    convert hx using 1 ; norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] ; ring

theorem raw223_q_nonzero (A : ℚ) (x : Fin 223 → ℚ) (hA : A ≠ 0)
    (h : Raw223Solution A x) : coord x 96 ≠ 0 :=
  (retained_nonzero _ _ _ _ _ _ _ _ _ _ _ _ _ hA (raw223_retained A x h)).2.2

theorem raw223_Q_nonzero (A : ℚ) (x : Fin 223 → ℚ) (hA : A ≠ 0)
    (h : Raw223Solution A x) : coord x 98 ≠ 0 := by
  have hq := raw223_q_nonzero A x hA h
  have h47 := h 47 (by norm_num) (by norm_num)
  norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] at h47
  intro hz
  have : coord x 96 = 0 := by nlinarith only [h47, hz, sq_nonneg (coord x 96)]
  exact hq this

/-- New U=old Z/Q; source coordinates 1..221 are fixed. -/
def to222 (x : Fin 223 → ℚ) (i : Fin 222) : ℚ :=
  if h : i.val = 221 then coord x 223 / coord x 98
  else x ⟨i.val, by omega⟩

/-- Old G=R2*U and old Z=Q*U, with literal source operands. -/
def to223 (y : Fin 222 → ℚ) (i : Fin 223) : ℚ :=
  if h : i.val = 221 then coord y 119 * coord y 222
  else if h' : i.val = 222 then coord y 98 * coord y 222
  else y ⟨i.val, by omega⟩

theorem forward_coordinates (x : Fin 223 → ℚ) (i : Fin 221) :
    to222 x i.castSucc = x i.castSucc.castSucc := by
  have hi : i.val ≠ 221 := by omega
  simp [to222, hi]
  congr 1

theorem reverse_coordinates (y : Fin 222 → ℚ) (i : Fin 221) :
    to223 y i.castSucc.castSucc = y i.castSucc := by
  have hi : i.val ≠ 221 := by omega
  have hi' : i.val ≠ 222 := by omega
  simp [to223, hi, hi']
  congr 1

/-- Every literal parent row after substitution, including the deleted zero row 186. -/
theorem row_substitution (A : ℚ) (y : Fin 222 → ℚ) (i : ℕ)
    (hlo : 1 ≤ i) (hhi : i ≤ 197) :
    raw223Row A (coord (to223 y)) i =
      if i=186 then 0 else raw222Row A (coord y) (if i<186 then i else i-1) := by
  interval_cases i <;> norm_num [raw223Row, raw222Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12, raw222RowBlock0, raw222RowBlock1, raw222RowBlock2, raw222RowBlock3, raw222RowBlock4, raw222RowBlock5, raw222RowBlock6, raw222RowBlock7, raw222RowBlock8, raw222RowBlock9, raw222RowBlock10, raw222RowBlock11, raw222RowBlock12, coord, to223] <;> ring

theorem reverse_solution (A : ℚ) (y : Fin 222 → ℚ) (hy : Raw222Solution A y) :
    Raw223Solution A (to223 y) := by
  intro i hlo hhi
  rw [row_substitution A y i hlo hhi]
  split_ifs with h h'
  · rfl
  · exact hy i hlo (by omega)
  · exact hy (i-1) (by omega) (by omega)

theorem reverse_forward (A : ℚ) (x : Fin 223 → ℚ) (hA : A ≠ 0)
    (hx : Raw223Solution A x) : to223 (to222 x) = x := by
  have hQ := raw223_Q_nonzero A x hA hx
  have ht := hx 186 (by norm_num) (by norm_num)
  norm_num [raw223Row, raw223RowBlock0, raw223RowBlock1, raw223RowBlock2, raw223RowBlock3, raw223RowBlock4, raw223RowBlock5, raw223RowBlock6, raw223RowBlock7, raw223RowBlock8, raw223RowBlock9, raw223RowBlock10, raw223RowBlock11, raw223RowBlock12] at ht
  funext i
  rcases i with ⟨i, hi⟩
  by_cases h221 : i=221
  · subst i
    norm_num [to223, to222, coord]
    norm_num [coord] at hQ ht
    field_simp [hQ]
    linear_combination -ht
  · by_cases h222 : i=222
    · subst i
      norm_num [to223, to222, coord]
      norm_num [coord] at hQ
      field_simp [hQ]
    · simp [to223,to222,h221,h222]

theorem forward_reverse (A : ℚ) (y : Fin 222 → ℚ) (hA : A ≠ 0)
    (hy : Raw222Solution A y) : to222 (to223 y) = y := by
  have hQ := raw223_Q_nonzero A (to223 y) hA (reverse_solution A y hy)
  norm_num [coord,to223] at hQ
  funext i
  rcases i with ⟨i, hi⟩
  by_cases h221 : i=221
  · subst i
    norm_num [to223,to222,coord]
    field_simp [hQ]
  · have h222 : i≠222 := by omega
    simp [to223,to222,h221,h222]

theorem forward_solution (A : ℚ) (x : Fin 223 → ℚ) (hA : A ≠ 0)
    (hx : Raw223Solution A x) : Raw222Solution A (to222 x) := by
  intro j hjlo hjhi
  by_cases hj : j<186
  · have heq := row_substitution A (to222 x) j hjlo (by omega)
    rw [reverse_forward A x hA hx] at heq
    have hj' : j≠186 := by omega
    simp only [hj', ite_false, hj, ite_true] at heq
    rw [← heq]
    exact hx j hjlo (by omega)
  · have heq := row_substitution A (to222 x) (j+1) (by omega) (by omega)
    rw [reverse_forward A x hA hx] at heq
    have hj' : j+1≠186 := by omega
    have hj'' : ¬j+1<186 := by omega
    simp only [hj', ite_false, hj'', Nat.add_sub_cancel] at heq
    rw [← heq]
    exact hx (j+1) (by omega) (by omega)

/-- The actual 197-to-196 row chart, over all rational solutions for nonzero A. -/
def solutionEquiv (A : ℚ) (hA : A ≠ 0) :
    {x : Fin 223 → ℚ // Raw223Solution A x} ≃ {y : Fin 222 → ℚ // Raw222Solution A y} where
  toFun x := ⟨to222 x.1, forward_solution A x.1 hA x.2⟩
  invFun y := ⟨to223 y.1, reverse_solution A y.1 y.2⟩
  left_inv x := Subtype.ext (reverse_forward A x.1 hA x.2)
  right_inv y := Subtype.ext (forward_reverse A y.1 hA y.2)

end V15RetainedContact
