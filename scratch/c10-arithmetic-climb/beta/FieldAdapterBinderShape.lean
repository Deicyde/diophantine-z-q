import FieldAdapterCandidate

/-!
# The consumer's β-side binder SHAPE at `C := GlueC10.Qbar`

Added after the Expected freeze (`7210310608ec…`), in a NEW file: the candidate
(`76e846bc…`) and checks (`4eebec09…`) bytes already reported are untouched.

What this file does: writes the `c10_of_squares` β-side binder triple **verbatim from the
Link text** — `hβ`, `hβ0`, `hβ1` — with `C` instantiated by the literal `GlueC10.Qbar` and
`β`, `ε` by the field specializations, and discharges it from the candidate.

What it does NOT do, and cannot: the #62 `ZInQKernel.HDecomp.C10.Link` module is NOT in the
canonical build (the canonical tree carries only `C10/C10.lean` and `C10/Trace.lean`), so
these are the binder shapes transcribed by hand, not an ascription against the real
`c10_of_squares` telescope, and **not** an application of it. The consumer's `C`, `β`, `ε`,
`c`, `a` binders remain OPEN; `C := Qbar` stays an ascription, not a selection.
-/

noncomputable section

open ClimbBetaExpected ClimbFieldAdapterExpected ClimbFieldAdapter GlueDescent.B2Q

/-- The consumer's β-side triple, at `C := GlueC10.Qbar`, from the GIVEN units-level datum.
`hβ1` is present ONLY under the explicit `ε₀ 1 1 = 1`, exactly as the contract requires. -/
theorem c10_beta_side_shape
    (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) (hε1 : ε₀ 1 1 = 1) :
    -- hβ
    (∀ g h, betaField β₀ g * betaField β₀ h = epsField ε₀ g h * betaField β₀ (g * h)) ∧
    -- hβ0
    (∀ g, betaField β₀ g ≠ 0) ∧
    -- hβ1
    (betaField β₀ 1 = 1) :=
  ⟨fieldCochain β₀ ε₀ hco, fieldNonzero β₀, fieldNormalizedAtOne β₀ ε₀ hco hε1⟩

/-- Without the explicit `ε₀ 1 1 = 1` only the first two members are available; the third is
exactly the open `hβ1` obligation. -/
theorem c10_beta_side_shape_unnormalized
    (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) :
    (∀ g h, betaField β₀ g * betaField β₀ h = epsField ε₀ g h * betaField β₀ (g * h)) ∧
    (∀ g, betaField β₀ g ≠ 0) :=
  ⟨fieldCochain β₀ ε₀ hco, fieldNonzero β₀⟩

#print axioms c10_beta_side_shape
#print axioms c10_beta_side_shape_unnormalized
#check @c10_beta_side_shape
#check @c10_beta_side_shape_unnormalized
