import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Comparison

/-!
# Lane RC12-odd: visibility (O.8) (App F, `ex:app-visibility`, tex 9407–9445)

"There is one constant `C_det`, independent of the actual stage and admissible `D`, for which
(O.8) holds. Explicitly, for a known simple-zero `D`, `v₂ a_M(D) ≥ min{M, j_gen(D) − C_det}`. For
every admissible `D`, the strict inequality `v₂ a_M(D) < M` implies `ord_{s=1} L(E^D, s) = 1` and
`j_gen(D) ≤ v₂ a_M(D) + C_det`. If an admissible odd-sign `D` is not a simple zero, its coefficient
vanishes modulo `2^M`."

`visibility_O8` is **PROVED** from three hypotheses, each the manuscript's own input:
* `hO7` — the comparison (O.7)/(3.8) after phase removal (tex 9112–9113, 2081–2084): at every stage
  `θ` and admissible `D`, `a_θ(D) ≡ c₀ 2^{ω(N)} ζ λ_θ(D) (mod 2^{M_θ})` with `ζ` odd and
  `λ_θ(D)` an integer lift of `λ_{M_θ}(\overline{LP_D})`;
* `hnative` — the native-index lower bound (tex 9422–9428): for a known simple zero `D`,
  `P_D = m_D G + T`, `L` kills `T`, an integral Kummer map cannot decrease `v₂(m_D)`, and the rational
  line has index `≤ 2` in the native lattice; all absorbed in one constant `C`:
  `2^k ∣ λ_θ(D)` whenever `k ≤ min(M_θ, j_gen(D) − C)` (ELLIOT/GLUE);
* `htorsion` — the height formula (Cai–Shu–Tian Thm 1.1, PRINT, stated in the project as
  `CST.CSTThm11Split`; qualitative direction only) together with `L` killing torsion
  (tex 9439–9441): an admissible `D` that is not a simple zero has torsion genus point, so
  `λ_θ(D) ≡ 0 (mod 2^{M_θ})`.

The conclusion is the shape of the skeleton's Prop `RCSteps.visibility` (lane RC0), with
`SimpleZero D` to be instantiated by `ord_{s=1} L(E^{(D)}, s) = 1` and `vZ` the 2-adic valuation
`Padic.addValuation` on `ℤ ⊂ ℚ₂` (definitionally the skeleton's `vZ`).
-/

namespace ZInQ.Manuscript.RC.Odd

/-- The 2-adic valuation of an integer, in `WithTop ℤ` (`vZ 0 = ⊤`); the same definition as the
skeleton's `vZ`. -/
noncomputable def vZ (n : ℤ) : WithTop ℤ := Padic.addValuation ((n : ℚ) : ℚ_[2])

theorem vZ_of_ne_zero {n : ℤ} (hn : n ≠ 0) : vZ n = ((padicValInt 2 n : ℤ) : WithTop ℤ) := by
  have : ((n : ℚ) : ℚ_[2]) ≠ 0 := by exact_mod_cast hn
  rw [vZ, Padic.addValuation.apply this]
  congr 1
  have h := Padic.valuation_intCast (p := 2) n
  rw [← h]; norm_cast

/-- **PROVED.** `2^k ∣ n ↔ k ≤ v₂(n)`. -/
theorem two_pow_dvd_iff_le_vZ (n : ℤ) (k : ℕ) : (2 : ℤ) ^ k ∣ n ↔ ((k : ℤ) : WithTop ℤ) ≤ vZ n := by
  by_cases hn : n = 0
  · subst hn; simp [vZ]
  · rw [vZ_of_ne_zero hn, WithTop.coe_le_coe, Int.ofNat_le]
    have := padicValInt_dvd_iff (p := 2) k n
    simp only [hn, false_or] at this
    exact_mod_cast this

/-- **(O.8), PROVED from (O.7), the native-index bound and the height formula.** -/
theorem visibility_O8 (M : ℕ → ℕ) (aθ lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop)
    (SimpleZero : ℤ → Prop) (jgen : ℤ → ℤ) (ω : ℕ) (C : ℤ)
    (hO7 : ∀ θ D, admissible θ D → ∃ ζ : ℤ, Odd ζ ∧
      (2 : ℤ) ^ M θ ∣ aθ θ D - (c0 : ℤ) * 2 ^ ω * ζ * lam θ D)
    (hnative : ∀ θ D, admissible θ D → SimpleZero D → ∀ k : ℕ, k ≤ M θ → (k : ℤ) ≤ jgen D - C →
      (2 : ℤ) ^ k ∣ lam θ D)
    (htorsion : ∀ θ D, admissible θ D → ¬ SimpleZero D → (2 : ℤ) ^ M θ ∣ lam θ D) :
    (∀ θ D, admissible θ D → SimpleZero D → ∀ k : ℕ, k ≤ M θ → (k : ℤ) ≤ jgen D - C →
        ((k : ℤ) : WithTop ℤ) ≤ vZ (aθ θ D)) ∧
    (∀ θ D, admissible θ D → ¬ SimpleZero D → ((M θ : ℤ) : WithTop ℤ) ≤ vZ (aθ θ D)) ∧
    (∃ Cdet : ℤ, ∀ θ D, admissible θ D → vZ (aθ θ D) < ((M θ : ℤ) : WithTop ℤ) →
      SimpleZero D ∧ ((jgen D : ℤ) : WithTop ℤ) ≤ vZ (aθ θ D) + (Cdet : WithTop ℤ)) := by
  -- the lower bound transfers from `λ` to `a` through (O.7)
  have transfer : ∀ θ D, admissible θ D → ∀ k : ℕ, k ≤ M θ → (2 : ℤ) ^ k ∣ lam θ D →
      (2 : ℤ) ^ k ∣ aθ θ D := by
    intro θ D hD k hk hl
    obtain ⟨ζ, -, hc⟩ := hO7 θ D hD
    have h1 : (2 : ℤ) ^ k ∣ aθ θ D - (c0 : ℤ) * 2 ^ ω * ζ * lam θ D :=
      dvd_trans (pow_dvd_pow 2 hk) hc
    have h2 : (2 : ℤ) ^ k ∣ (c0 : ℤ) * 2 ^ ω * ζ * lam θ D := dvd_mul_of_dvd_right hl _
    have := dvd_add h1 h2
    rwa [sub_add_cancel] at this
  refine ⟨?_, ?_, ⟨C, ?_⟩⟩
  · intro θ D hD hs k hk hj
    exact (two_pow_dvd_iff_le_vZ _ k).mp (transfer θ D hD k hk (hnative θ D hD hs k hk hj))
  · intro θ D hD hs
    exact (two_pow_dvd_iff_le_vZ _ _).mp (transfer θ D hD _ le_rfl (htorsion θ D hD hs))
  · intro θ D hD hlt
    have hsimple : SimpleZero D := by
      by_contra hs
      have := (two_pow_dvd_iff_le_vZ _ _).mp (transfer θ D hD _ le_rfl (htorsion θ D hD hs))
      exact absurd hlt (not_lt.mpr this)
    refine ⟨hsimple, ?_⟩
    have ha0 : aθ θ D ≠ 0 := by
      intro h0; rw [h0] at hlt; simp [vZ] at hlt
    rw [vZ_of_ne_zero ha0] at hlt ⊢
    set n := padicValInt 2 (aθ θ D)
    have hnM : n < M θ := by
      have : ((n : ℤ) : WithTop ℤ) < ((M θ : ℤ) : WithTop ℤ) := hlt
      exact_mod_cast WithTop.coe_lt_coe.mp this
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    by_contra hj
    rw [not_le] at hj
    have hk : ((n + 1 : ℕ) : ℤ) ≤ jgen D - C := by push_cast; linarith
    have hdiv := transfer θ D hD (n + 1) (by omega) (hnative θ D hD hsimple (n + 1) (by omega) hk)
    have := (two_pow_dvd_iff_le_vZ _ _).mp hdiv
    rw [vZ_of_ne_zero ha0, WithTop.coe_le_coe] at this
    push_cast at this
    omega

/-- **PROVED (tex 9391–9399, `v₂`-form).** At the fixed witness, `v₂ a_M(D_w) = c_θ + c_w`. -/
theorem witness_vZ (ω M cw : ℕ) {a ζ lam : ℤ} (hζ : Odd ζ)
    (hlam1 : (2 : ℤ) ^ cw ∣ lam) (hlam2 : ¬ (2 : ℤ) ^ (cw + 1) ∣ lam)
    (hcong : (2 : ℤ) ^ M ∣ a - (c0 : ℤ) * 2 ^ ω * ζ * lam) (hM : 9 + ω + cw < M) :
    vZ a = (((9 + ω + cw : ℕ) : ℤ) : WithTop ℤ) := by
  obtain ⟨h1, h2⟩ := witness_exact_order ω M cw hζ hlam1 hlam2 hcong hM
  have ha0 : a ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  have hle := (two_pow_dvd_iff_le_vZ a _).mp h1
  have hnle : ¬ ((((9 + ω + cw + 1 : ℕ)) : ℤ) : WithTop ℤ) ≤ vZ a :=
    fun h => h2 ((two_pow_dvd_iff_le_vZ a _).mpr h)
  rw [vZ_of_ne_zero ha0] at hle hnle ⊢
  rw [WithTop.coe_le_coe] at hle hnle
  have : padicValInt 2 a = 9 + ω + cw := by
    have h1' : ((9 + ω + cw : ℕ) : ℤ) ≤ (padicValInt 2 a : ℤ) := hle
    have h2' : ¬ ((9 + ω + cw + 1 : ℕ) : ℤ) ≤ (padicValInt 2 a : ℤ) := hnle
    omega
  rw [this]

end ZInQ.Manuscript.RC.Odd
