import ZInQKernel.Assembly.Values
import ZInQKernel.Compiler.Translation.Rational
import ZInQKernel.Compiler.Universal.WrapperCode
import ZInQKernel.Syntax.Recipes.Literal

/-!
# The relation Close

Blueprint: `assembly/approximation/close-relation.md`.

`Rel_close(N, K, t)` of the specification (recipe `2` of `specLib`, with the constructors and
fixed constants of the specification, the program literal `c₃` and the natural precision circuit
`precisionCircuitOf c₃`) holds exactly when there are integers `n, κ, a, l` with `N = ι(n)`,
`K = ι(κ)`, `Prec(n, κ, a, l, n a)` and `|t - r(a, n a)| < ε_l`, where
`Prec(n, κ, a, l, j) = accepts(enc n, enc κ, enc a, enc l, enc j)` is the precision relation at
the signed encodings (`close_relation_iff`).

Input C is used as a chain of three equivalences: the rational translation
(`Translation.precision_rel_iff`, which needs the multiplication statement M), the semantics of
the natural precision polynomial (`Compiler.natural_polynomial_semantics'`) and `dec ∘ enc = id`
(`spec_precision_iff`).

The multiplication statement M is the explicit hypothesis `hM` throughout; it is proved from
hypotheses H, PC and 22P in `Multiplication/Top/Exact.lean` (`Mult.multiplication_exact`).
-/

namespace ZInQ.Assembly

open Syntax Translation Compiler.Precision Compiler.Natural
open Compiler.Universal (precisionCircuitOf)

/-- The fixed library of the specification: constructors and fixed constants of the
specification, program literal `c₃`, natural precision circuit `precisionCircuitOf c₃`. -/
noncomputable abbrev closeSpecLib : List ExPoly :=
  specLib specConstructors FixedConst.cstar.value FixedConst.ell.value FixedConst.T.value
    (Compiler.Universal.c3 : ℤ) (precisionCircuitOf (Compiler.Universal.c3 : ℤ))

/-- The precision relation at the signed encodings is the precision relation on the decoded
integers: `Prec(n, κ, a, l, j) ⟺ acceptsInt n κ a l j`. -/
theorem accepts_enc_iff (n κ a l j : ℤ) :
    accepts ![enc n, enc κ, enc a, enc l, enc j] ↔ acceptsInt n κ a l j := by
  show acceptsInt (dec (enc n)) (dec (enc κ)) (dec (enc a)) (dec (enc l)) (dec (enc j)) ↔ _
  simp only [dec_enc]

/-- Twenty-five rationals in five rows of five, as a list. -/
theorem ofFn_rows (E₀ E₁ E₂ E₃ E₄ : Fin 5 → ℚ) :
    List.ofFn E₀ ++ List.ofFn E₁ ++ List.ofFn E₂ ++ List.ofFn E₃ ++ List.ofFn E₄ =
      List.ofFn (fun k : Fin 25 =>
        (![E₀, E₁, E₂, E₃, E₄] : Fin 5 → Fin 5 → ℚ) ⟨k / 5, by omega⟩ ⟨k % 5, by omega⟩) := by
  rfl

/-- **Input C on the specification** (the local `precision_rel_iff`). Under M, for all
`E₀, …, E₄ ∈ ℚ⁵`, `Rel_precision(E₀, …, E₄)` holds exactly when `E_i = ι(c_i)` for some
`c ∈ ℕ⁵` accepted by the precision relation. -/
theorem spec_precision_iff
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value
      FixedConst.T.value)
    (E₀ E₁ E₂ E₃ E₄ : Fin 5 → ℚ) :
    ValRel (getEx closeSpecLib 1)
        (List.ofFn E₀ ++ List.ofFn E₁ ++ List.ofFn E₂ ++ List.ofFn E₃ ++ List.ofFn E₄) ↔
      ∃ c : Fin 5 → ℕ, (∀ i, (![E₀, E₁, E₂, E₃, E₄] : Fin 5 → Fin 5 → ℚ) i = iota (c i)) ∧
        accepts c := by
  rw [closeSpecLib, getEx_specLib _ _ _ _ _ _ (i := 1) (by decide), ofFn_rows]
  refine (valRel_ofFn_iff _ rfl _).trans ?_
  exact precision_rel_iff_accepts_of specConstructors _ _ _ rfl hM
    Compiler.natural_polynomial_semantics' _
    ⟨_, (getEx_specLib_take _ _ _ _ _ _ (i := 1) (j := 0) (by decide) (by decide)).trans
      (getEx_specLib _ _ _ _ _ _ (i := 0) (by decide))⟩ _

/-- **The relation Close.** Under M, for all `N, K ∈ ℚ⁵` and `t ∈ ℚ`, `Rel_close(N, K, t)` holds
exactly when there are `n, κ, a, l ∈ ℤ` with `N = ι(n)`, `K = ι(κ)`,
`Prec(n, κ, a, l, n a) = accepts(enc n, enc κ, enc a, enc l, enc (n a))` and
`|t - r(a, n a)| < ε_l`. -/
theorem close_relation_iff
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value
      FixedConst.T.value)
    (N K : Fin 5 → ℚ) (t : ℚ) :
    ValRel (getEx closeSpecLib 2) (List.ofFn N ++ (List.ofFn K ++ [t])) ↔
      ∃ n κ a l : ℤ, N = iota n ∧ K = iota κ ∧
        accepts ![enc n, enc κ, enc a, enc l, enc (n * a)] ∧
        |t - rRatio a (n * a)| < epsIdx l := by
  rw [closeSpecLib, spec_close_rel_iff]
  simp only [signedEncode_rel_iff hM, closeCoordinates_rel_iff]
  simp only [spec_precision_iff hM]
  constructor
  · rintro ⟨A, L, J, E₀, E₁, E₂, E₃, E₄, ⟨m₀, rfl, rfl⟩, ⟨m₁, rfl, rfl⟩, ⟨m₂, rfl, rfl⟩,
      ⟨m₃, rfl, rfl⟩, ⟨m₄, rfl, rfl⟩, ⟨c, hc, hacc⟩, ⟨a, l, j, ha, hl, hj, -, -, hw⟩⟩
    have hci : ∀ (i : Fin 5) (m : ℤ),
        (![iota (enc m₀ : ℤ), iota (enc m₁ : ℤ), iota (enc m₂ : ℤ), iota (enc m₃ : ℤ),
          iota (enc m₄ : ℤ)] : Fin 5 → Fin 5 → ℚ) i = iota (enc m : ℤ) → c i = enc m :=
      fun i m h => by
        have := iota_injective ((hc i).symm.trans h)
        exact_mod_cast this
    have hc' : c = ![enc m₀, enc m₁, enc m₂, enc m₃, enc m₄] := by
      funext i
      fin_cases i
      · exact hci 0 m₀ rfl
      · exact hci 1 m₁ rfl
      · exact hci 2 m₂ rfl
      · exact hci 3 m₃ rfl
      · exact hci 4 m₄ rfl
    rw [hc', accepts_enc_iff] at hacc
    rw [← iota_injective ha, ← iota_injective hl, ← iota_injective hj] at hw
    have h4 : m₄ = m₀ * m₂ := hacc.1.2.2.2.2
    subst h4
    exact ⟨m₀, m₁, m₂, m₃, rfl, rfl, (accepts_enc_iff _ _ _ _ _).2 hacc, hw⟩
  · rintro ⟨n, κ, a, l, rfl, rfl, hacc, hw⟩
    have hacc' := (accepts_enc_iff _ _ _ _ _).1 hacc
    obtain ⟨⟨-, -, ha, hl, -⟩, -⟩ := hacc'
    refine ⟨iota a, iota l, iota (n * a), iota (enc n : ℤ), iota (enc κ : ℤ), iota (enc a : ℤ),
      iota (enc l : ℤ), iota (enc (n * a) : ℤ), ⟨n, rfl, rfl⟩, ⟨κ, rfl, rfl⟩, ⟨a, rfl, rfl⟩,
      ⟨l, rfl, rfl⟩, ⟨n * a, rfl, rfl⟩, ⟨![enc n, enc κ, enc a, enc l, enc (n * a)], ?_, hacc⟩,
      ⟨a, l, n * a, rfl, rfl, rfl, by omega, by omega, hw⟩⟩
    intro i
    fin_cases i <;> rfl

end ZInQ.Assembly
