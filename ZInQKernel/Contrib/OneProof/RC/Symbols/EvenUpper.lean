import ZInQKernel.Contrib.OneProof.RC.Symbols.Address
import ZInQKernel.Contrib.OneProof.RC.Symbols.Forest

/-!
# Lane RC2: the partitionable even upper estimate (`ex:sec7-even-upper`, tex 2290–2341)

Two halves:
* `even_upper_cubes` (PROVED): a nonempty partitionable list has a nonzero terminal polynomial
  (`ex:sec7-seed-certificate`), so the stationary one-symbol address lemma gives, for every
  `b ≥ 1`, a binary cube based at the list, with no old vertex removed, whose other addresses are
  units (tex 2311–2322);
* `even_upper_valuation` (PROVED from stated inputs): units give (3.3a), the corank-zero central
  comparison (3.2), and the Boolean comparison of Section 9 on such cubes give (3.3b)
  (tex 2302–2310, 2322–2341; App G (F.1)–(F.2), tex 10079–10129).
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

variable {L : Type*} [AddCommGroup L]

/-- **The cubes of the even upper estimate** (tex 2311–2322). Kind: PROVED from the coefficient
rules. For a nonempty partitionable list `Γ` (a contraction certificate) and every `b ≥ 1` there
is a configuration `Γ'` extending `Γ` by primary vertices with nonzero linear activations such
that the cube is based at `Γ` (its zero address reads `Γ` itself) and every nonzero address is a
unit. -/
theorem even_upper_cubes {ε : L →+ ZMod 2} {A : Config L → ZMod 2} (hA : CoefficientRules ε A)
    (Γ : Config L) (hΓ : Γ.Compatible ε) (hpart : IsPartitionable ε A Γ) (b : ℕ) (hb : 1 ≤ b) :
    ∃ (Γ' : Config L) (act'' : ℕ → Option (Fin b → ZMod 2)),
      Γ'.Compatible ε ∧ Γ.Extends Γ' ∧ A (Γ'.at act'' 0) = A Γ ∧
      (∀ v ∈ Γ'.V, v ∉ Γ.V → Γ'.t v = 0 ∧ ∃ w, w ≠ 0 ∧ act'' v = some w) ∧
      ∀ x : Fin b → ZMod 2, x ≠ 0 → A (Γ'.at act'' x) = 1 := by
  have hT := partitionable_terminalNonzero hA hΓ hpart
  obtain ⟨Γ', act'', hc, hext, hact, hnew, hunit⟩ :=
    one_symbol_address hA Γ hΓ hpart.1 hT b hb
  refine ⟨Γ', act'', hc, hext, ?_, hnew, fun x hx => hunit x hx 0⟩
  exact one_symbol_address_base hA Γ Γ' act'' hc hext (fun v hv => hact v hv) hnew

/-- **The valuation step of the even upper estimate** (tex 2302–2310, 2322–2341; App G (F.1),
(F.2)). Kind: PROVED from the stated inputs, which are, in the manuscript:
* `h33a` (3.3a): a unit symbol at `p` gives `L_*(p) ≠ 0` and `v₂ L_*(p) ≤ 2ω(p) + C₀` (ELLIOT:
  same-filter coefficient-square formula, App E `ex:app-even-phase`);
* `hfwd`: nonzero central value gives Selmer corank zero (PRINT: the forward rank-zero theorem,
  Kato / Kolyvagin, as `lem:forward-rank`);
* `h32` (3.2): at corank-zero constituents the fixed-form Kato scalar `u` satisfies
  `u_p(0) = 0 ↔ L_*(p) = 0` and `|v₂ u_p(0) - (v₂ L_*(p) - 2ω(p) - s(p))| ≤ C_loc` (ELLIOT:
  App E `ex:app-central-calibration`, (E.8));
* `hmiss`: on the cubes of `even_upper_cubes` (based at `d₀`, units at nonzero addresses) the
  common scalar has bounded Boolean bit degrees, so for every precision `M` a large cube has a
  nonzero address `x` with `v₂(u_x(0) - u_0(0)) ≥ M - c_E` (ELLIOT: Section 9 Boolean bit-degree
  lemma and cube parity, tex 5690–5714, with the uniform clearing (E.5)).
Conclusion (3.3b): `L_*(d₀) ≠ 0` and `v₂ L_*(d₀) - 2ω(d₀) - s(d₀) ≤ C₀ + 2 C_loc`; the constant
depends only on the source. Valuations of nonzero 2-adic numbers are `Padic.valuation`. -/
theorem even_upper_valuation {P : Type*} (unit corank0 Lnz : P → Prop) (u : P → ℚ_[2])
    (Lval : P → ℤ) (ω s : P → ℕ) (C₀ Cloc cE : ℤ)
    (h33a : ∀ p, unit p → Lnz p ∧ Lval p ≤ 2 * ω p + C₀)
    (hfwd : ∀ p, Lnz p → corank0 p)
    (h32 : ∀ p, corank0 p → (u p = 0 ↔ ¬ Lnz p) ∧
      (Lnz p → |Padic.valuation (u p) - (Lval p - 2 * ω p - s p)| ≤ Cloc))
    (d₀ : P) (hd₀ : corank0 d₀)
    (hmiss : ∀ M : ℤ, ∃ x, unit x ∧ (u x = u d₀ ∨ M - cE ≤ Padic.valuation (u x - u d₀))) :
    Lnz d₀ ∧ Lval d₀ - 2 * ω d₀ - s d₀ ≤ C₀ + 2 * Cloc := by
  -- the nonzero-address bound `v₂ u_x(0) ≤ B_e`, `B_e = C₀ + C_loc`
  have hux : ∀ x, unit x → u x ≠ 0 ∧ Padic.valuation (u x) ≤ C₀ + Cloc := by
    intro x hx
    obtain ⟨hL, hle⟩ := h33a x hx
    obtain ⟨h1, h2⟩ := h32 x (hfwd x hL)
    refine ⟨fun h0 => (h1.mp h0) hL, ?_⟩
    have := (abs_le.mp (h2 hL)).2
    have hs : (0 : ℤ) ≤ s x := Int.natCast_nonneg _
    linarith
  -- the base: nonzero with `v₂ u_0(0) ≤ B_e`
  have hbase : u d₀ ≠ 0 ∧ Padic.valuation (u d₀) ≤ C₀ + Cloc := by
    by_contra hcon
    obtain ⟨x, hx, hcong⟩ := hmiss (C₀ + Cloc + cE + 1)
    obtain ⟨hx0, hxle⟩ := hux x hx
    rcases hcong with heq | hge
    · rw [heq] at hx0 hxle
      exact hcon ⟨hx0, hxle⟩
    · have hsum : (u x - u d₀) + u d₀ ≠ 0 := by rwa [sub_add_cancel]
      have hmin := Padic.le_valuation_add hsum
      rw [sub_add_cancel] at hmin
      by_cases hd : u d₀ = 0
      · rw [hd, sub_zero] at hge
        linarith
      · have hv : C₀ + Cloc < Padic.valuation (u d₀) := by
          by_contra hle
          exact hcon ⟨hd, not_lt.mp hle⟩
        have : C₀ + Cloc + 1 ≤ min (Padic.valuation (u x - u d₀)) (Padic.valuation (u d₀)) :=
          le_min (by linarith) (by linarith)
        linarith
  obtain ⟨h1, h2⟩ := h32 d₀ hd₀
  have hL : Lnz d₀ := by
    by_contra hn
    exact hbase.1 (h1.mpr hn)
  refine ⟨hL, ?_⟩
  have := (abs_le.mp (h2 hL)).1
  linarith [hbase.2]

end ZInQ.Manuscript.RC.Symbols
