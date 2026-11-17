import Mathlib

/-!
# Lane RC12-odd: the shell recurrence of the coefficient rules (App F, tex 9558–9617)

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-coefficient-rules`, paragraph
"Write an index as `J r m²` …" (tex 9558–9590) and "The two integral shell calculations"
(tex 9592–9617):

"Remove the phase `η(p)^s` in (O.6) and put `b_{-1} = 0, b_0 = 1, b_1 = a_p − κ,
`b_{s+1} = a_p b_s − p b_{s−1}`, `κ = (ψ/η)(p)(−D/p)`. For `p ∈ U∖J` the factor `b_s − b_{s−1}` is
odd; for `p ∈ J` the factor `b_{s+1} − b_s` is even. … For a split prime `a_p ≡ p+1 (mod 4)`. The
recurrence gives the same residue on each divided shell,
`(b_{s+1} − b_s)/2 ≡ c_p(D) := {a_p − (ψ/η)(p)(−D/p) − 1}/2 (mod 2)` (O.10)."

Here `κ = 0` exactly when `p ∣ D` and `κ = ±1` otherwise. All statements are PROVED over `ℤ`.
-/

namespace ZInQ.Manuscript.RC.Odd

/-- The shell sequence `b_s = b_s(a_p, p, κ)`: `b_0 = 1`, `b_1 = a_p − κ`,
`b_{s+2} = a_p b_{s+1} − p b_s` (tex 9564–9566). -/
def shell (ap p κ : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => ap - κ
  | (s + 2) => ap * shell ap p κ (s + 1) - p * shell ap p κ s

/-- `b_{s−1}`, with the convention `b_{−1} = 0` (tex 9564). -/
def shellPrev (ap p κ : ℤ) : ℕ → ℤ
  | 0 => 0
  | (s + 1) => shell ap p κ s

@[simp] theorem shell_zero (ap p κ : ℤ) : shell ap p κ 0 = 1 := rfl
@[simp] theorem shell_one (ap p κ : ℤ) : shell ap p κ 1 = ap - κ := rfl
theorem shell_succ_succ (ap p κ : ℤ) (s : ℕ) :
    shell ap p κ (s + 2) = ap * shell ap p κ (s + 1) - p * shell ap p κ s := rfl
@[simp] theorem shellPrev_zero (ap p κ : ℤ) : shellPrev ap p κ 0 = 0 := rfl
@[simp] theorem shellPrev_succ (ap p κ : ℤ) (s : ℕ) : shellPrev ap p κ (s + 1) = shell ap p κ s :=
  rfl

variable {ap p : ℤ}

/-- With `p` odd and `a_p ≡ p + 1 (mod 4)`, `a_p` is even. -/
theorem even_ap (hp : Odd p) (hap : ap ≡ p + 1 [ZMOD 4]) : Even ap := by
  obtain ⟨k, hk⟩ := hp
  have := Int.ModEq.dvd hap.symm
  obtain ⟨u, hu⟩ := this
  exact ⟨2 * u + k + 1, by linarith⟩

/-- Two steps of the recurrence preserve parity when `a_p` is even and `p` is odd. -/
theorem shell_add_two_emod (hp : Odd p) (hap : ap ≡ p + 1 [ZMOD 4]) (κ : ℤ) (s : ℕ) :
    shell ap p κ (s + 2) % 2 = shell ap p κ s % 2 := by
  obtain ⟨e, he⟩ := even_ap hp hap
  obtain ⟨v, hv⟩ := hp
  have h : shell ap p κ (s + 2) - shell ap p κ s =
      2 * (e * shell ap p κ (s + 1) - (v + 1) * shell ap p κ s) := by
    rw [shell_succ_succ, he, hv]; ring
  set z := e * shell ap p κ (s + 1) - (v + 1) * shell ap p κ s
  omega

/-- **PROVED (tex 9594–9597).** For `p ∣ D` (`κ = 0`): `b_{2t}` is odd and `b_{2t+1}` is even. -/
theorem shell_kappa_zero_parity (hp : Odd p) (hap : ap ≡ p + 1 [ZMOD 4]) (t : ℕ) :
    shell ap p 0 (2 * t) % 2 = 1 ∧ shell ap p 0 (2 * t + 1) % 2 = 0 := by
  induction t with
  | zero =>
    obtain ⟨e, he⟩ := even_ap hp hap
    simp only [mul_zero, shell_zero, zero_add, shell_one, sub_zero]
    omega
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, show 2 * t + 2 + 1 = (2 * t + 1) + 2 by ring,
      shell_add_two_emod hp hap, shell_add_two_emod hp hap]
    exact ih

/-- **PROVED (tex 9568, 9594–9597).** For `p ∈ U∖J` (`κ = 0`): every factor `b_s − b_{s−1}` is
odd, including `s = 0` with `b_{−1} = 0`. -/
theorem odd_shell_diff_kappa_zero (hp : Odd p) (hap : ap ≡ p + 1 [ZMOD 4]) (s : ℕ) :
    Odd (shell ap p 0 s - shellPrev ap p 0 s) := by
  rw [Int.odd_iff]
  cases s with
  | zero => simp
  | succ s =>
    rw [shellPrev_succ]
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' s
    · have h := shell_kappa_zero_parity hp hap t
      omega
    · have h1 := shell_kappa_zero_parity hp hap t
      have h2 := shell_kappa_zero_parity hp hap (t + 1)
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring] at h2
      omega

/-- **PROVED (tex 9598–9599).** For `p ∤ D` (`κ = ±1`): every `b_s` is odd. -/
theorem odd_shell_kappa_unit {κ : ℤ} (hκ : κ = 1 ∨ κ = -1) (hp : Odd p)
    (hap : ap ≡ p + 1 [ZMOD 4]) (s : ℕ) : Odd (shell ap p κ s) := by
  have key : ∀ t, shell ap p κ t % 2 = 1 ∧ shell ap p κ (t + 1) % 2 = 1 := by
    intro t
    induction t with
    | zero =>
      obtain ⟨e, he⟩ := even_ap hp hap
      simp only [shell_zero, zero_add, shell_one]
      rcases hκ with rfl | rfl <;> omega
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      rw [show t + 1 + 1 = t + 2 by ring, shell_add_two_emod hp hap]
      exact ih.1
  exact Int.odd_iff.mpr (key s).1

/-- `d_s = b_{s+1} − b_s`. -/
def shellDiff (ap p κ : ℤ) (s : ℕ) : ℤ := shell ap p κ (s + 1) - shell ap p κ s

/-- **PROVED (tex 9599–9606; (O.10)).** For `p ∤ D` (`κ = ±1`), with `p` odd and
`a_p ≡ p + 1 (mod 4)`: `d_s ≡ d_0 = a_p − κ − 1 (mod 4)` for all `s ≥ 0`; in particular every
`d_s` is even (tex 9569). -/
theorem shellDiff_modEq {κ : ℤ} (hκ : κ = 1 ∨ κ = -1) (hp : Odd p)
    (hap : ap ≡ p + 1 [ZMOD 4]) (s : ℕ) :
    shellDiff ap p κ s ≡ ap - κ - 1 [ZMOD 4] ∧ Even (shellDiff ap p κ s) := by
  have hev := even_ap hp hap
  have hκo : Odd κ := by rcases hκ with rfl | rfl <;> decide
  induction s with
  | zero =>
    refine ⟨by simp [shellDiff], ?_⟩
    simp only [shellDiff, zero_add, shell_one, shell_zero]
    have : Odd (ap - κ) := Even.sub_odd hev hκo
    exact Odd.sub_odd this odd_one
  | succ s ih =>
    obtain ⟨hmod, hevd⟩ := ih
    -- d_{s+1} - d_s = (a_p - 1 - p) b_{s+1} + (p - 1) d_s
    have hid : shellDiff ap p κ (s + 1) - shellDiff ap p κ s =
        (ap - 1 - p) * shell ap p κ (s + 1) + (p - 1) * shellDiff ap p κ s := by
      simp only [shellDiff, show s + 1 + 1 = s + 2 by ring, shell_succ_succ]; ring
    obtain ⟨u, hu⟩ := (Int.ModEq.dvd hap.symm)
    obtain ⟨v, hv⟩ := hp
    obtain ⟨w, hw⟩ := hevd
    have h4 : (4 : ℤ) ∣ shellDiff ap p κ (s + 1) - shellDiff ap p κ s := by
      refine ⟨u * shell ap p κ (s + 1) + v * w, ?_⟩
      rw [hid]
      have : ap - 1 - p = 4 * u := by linarith
      rw [this, show p - 1 = 2 * v by linarith, hw]; ring
    have hmod' : shellDiff ap p κ (s + 1) ≡ shellDiff ap p κ s [ZMOD 4] :=
      (Int.modEq_iff_dvd.mpr (by simpa [dvd_sub_comm] using h4))
    refine ⟨hmod'.trans hmod, ?_⟩
    obtain ⟨t, ht⟩ := h4
    exact ⟨w + 2 * t, by linarith⟩

/-- **PROVED ((O.10), tex 9585–9590).** With `c_p(D) = (a_p − κ − 1)/2`, every divided shell has
the same residue: `(b_{s+1} − b_s)/2 ≡ c_p(D) (mod 2)`. -/
theorem shellDiff_half_modEq {κ : ℤ} (hκ : κ = 1 ∨ κ = -1) (hp : Odd p)
    (hap : ap ≡ p + 1 [ZMOD 4]) (s : ℕ) :
    shellDiff ap p κ s / 2 ≡ (ap - κ - 1) / 2 [ZMOD 2] := by
  obtain ⟨h4, ⟨w, hw⟩⟩ := shellDiff_modEq hκ hp hap s
  have h0 := (shellDiff_modEq hκ hp hap 0).2
  simp only [shellDiff, zero_add, shell_one, shell_zero] at h0
  obtain ⟨w0, hw0⟩ := h0
  have : ap - κ - 1 = w0 + w0 := by linarith
  rw [hw, this, ← two_mul, ← two_mul, Int.mul_ediv_cancel_left _ two_ne_zero,
    Int.mul_ediv_cancel_left _ two_ne_zero]
  rw [hw, this] at h4
  obtain ⟨c, hc⟩ := Int.ModEq.dvd h4
  exact Int.modEq_iff_dvd.mpr ⟨c, by linarith⟩

end ZInQ.Manuscript.RC.Odd
