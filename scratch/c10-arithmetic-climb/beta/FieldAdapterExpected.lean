import ZInQKernel.HDecomp.C10.C10
import BetaTransportExpected

/-!
# EXPECTED STATEMENTS — C10 field adapter (B-G1 lane). DEFINITIONS ONLY.

**No proofs, no candidate.** Submitted for the independent freeze, as with the a-σ lane's
V3 file. Written against the independent contract
`CONTRACT-FREEZE-FIELD-ADAPTER.md` sha256
7c1486aec489855d297d403ac5d47ade0ecf1dc1a2412ed468e0f7804a1f116d, whose §1 fixes five typed
predicates F1-F5; the scope attribution of the uncompiled MD
`C10ActualScalars-source-proposal.md` (29489 B, sha256 9cb7e93a…, read in full, provider of
nothing) is acknowledged — its `betaC`/`coe_betaC` subtype pattern is the pattern reused here,
specialized thinly to `Units.val` on `GlueC10.Qbar`, with no generic field or B2 reconstruction.

F6 is NOT in the frozen five: the parent's assignment additionally asked that the fixed-`ρ`
images of the GIVEN complex `β` and `ε` be retained through the field specialization. It is
marked separately so the reviewer can freeze or drop it without touching F1-F5.

Boundary (from the contract, copied): no new B2, `ε`, `c`, `a`, `χ`, `T` or global tuple; no
choice of the common `C` — stating results at the literal `C := GlueC10.Qbar` is an
ASCRIPTION, not an identification, and the consumer's `C`, `β`, `ε`, `c`, `a` binders stay
OPEN; no local constancy or continuity (120c 176394); no new preimage/algebraicity machinery
(the character, β and a-σ lanes own it); uncompiled MD snippets are not providers.
`hβ1` is conditional on `ε₀ 1 1 = 1` and must never be stated unconditionally.
-/

noncomputable section

namespace ClimbFieldAdapterExpected

open ClimbBetaExpected GlueDescent.B2Q

/-! ## F1 — the named `U → F` specializations -/

/-- The field-valued cochain: literally `Units.val ∘ β₀` on `GlueC10.Qbar`. -/
def betaField (β₀ : GQ → GlueC10.Qbarˣ) : GQ → GlueC10.Qbar := fun g => ((β₀ g : GlueC10.Qbar))

/-- The field-valued sign datum: literally `Units.val ∘ ε₀`. NOT the consumer's `ε`. -/
def epsField (ε₀ : GQ → GQ → GlueC10.Qbarˣ) : GQ → GQ → GlueC10.Qbar :=
  fun g h => ((ε₀ g h : GlueC10.Qbar))

/-- **F1.** The two specializations are exactly the unit coercions — no other map is
substituted, which is what keeps F3 free and the provenance checkable. -/
def FieldValuedBeta : Prop :=
  ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g, betaField β₀ g = Units.val (β₀ g)) ∧
    (∀ g h, epsField ε₀ g h = Units.val (ε₀ g h))

/-! ## F2-F5 — the consumer-shaped obligations -/

/-- **F2 (`hβ`-shaped).** The units-level cochain equation carried into the field. -/
def FieldCochain : Prop :=
  ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) →
    ∀ g h, betaField β₀ g * betaField β₀ h = epsField ε₀ g h * betaField β₀ (g * h)

/-- **F3 (`hβ0`-shaped).** Free from the `Units.val` provenance; not substantive. -/
def FieldNonzero : Prop :=
  ∀ (β₀ : GQ → GlueC10.Qbarˣ) (g : GQ), betaField β₀ g ≠ 0

/-- **F4.** The square equation against the character side, carried into the field so the
adapter cannot quietly drop it. -/
def FieldSquare : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ₀ : DirichletCharacter GlueC10.Qbar N) (β₀ : GQ → GlueC10.Qbarˣ),
    (∀ g, β₀ g ^ 2 = galCharacter χ₀ g) →
    ∀ g, (betaField β₀ g) ^ 2 = Units.val (galCharacter χ₀ g)

/-- **F5 (`hβ1`-shaped) — CONDITIONAL.** `IsSignCocycle` does not supply `ε₀ 1 1 = 1` and
`b2_of_leaves` does not return it; an unconditional form is a contract violation. -/
def FieldNormalizedAtOne : Prop :=
  ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) → ε₀ 1 1 = 1 → betaField β₀ 1 = 1

/-! ## F6 — requested by the assignment, outside the frozen five -/

/-- **F6.** The literal fixed-`ρ` images of the GIVEN complex `β` and `ε` survive the field
specialization. Same fixed place as every earlier lane; no second place. -/
def FieldPlaceImages : Prop :=
  ∀ (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ),
    (∀ g, unitPlace ρ (β₀ g) = β g) → (∀ g h, unitPlace ρ (ε₀ g h) = ε g h) →
    (∀ g, ρ (betaField β₀ g) = Units.val (β g)) ∧
    (∀ g h, ρ (epsField ε₀ g h) = Units.val (ε g h))

/-! ## Carrier identity, to be `rfl`-checked by the candidate before any call -/

/-- The C10 lane's Galois group and the B2 lane's are the same carrier. The candidate must
discharge this by `rfl`; it is stated here so the check is part of the frozen contract. -/
def GQIdentity : Prop := GlueC10.GQ = GlueDescent.B2Q.GQ

end ClimbFieldAdapterExpected

/-! ## Elaboration checks — definitions only -/

#check @ClimbFieldAdapterExpected.betaField
#check @ClimbFieldAdapterExpected.epsField
#check @ClimbFieldAdapterExpected.FieldValuedBeta
#check @ClimbFieldAdapterExpected.FieldCochain
#check @ClimbFieldAdapterExpected.FieldNonzero
#check @ClimbFieldAdapterExpected.FieldSquare
#check @ClimbFieldAdapterExpected.FieldNormalizedAtOne
#check @ClimbFieldAdapterExpected.FieldPlaceImages
#check @ClimbFieldAdapterExpected.GQIdentity
