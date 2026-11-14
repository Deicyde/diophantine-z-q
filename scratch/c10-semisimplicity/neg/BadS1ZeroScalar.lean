/-
UNCOMPILED PRIVATE NEGATIVE CONTROL (must be REJECTED).
S1 must not apply when the twisting scalar vanishes. The intended rejection is the failure of
the nonvanishing obligation `∀ g, (0 : ℚ) ≠ 0` — not an import, parser or synthesis error.
-/
import S1Twist

example {G V : Type} [Monoid G] [AddCommGroup V] [Module ℚ V]
    (ρ τ : Representation ℚ G V) (hρτ : ∀ g, ρ g = (0 : ℚ) • τ g)
    (h : τ.IsSemisimpleRepresentation) : ρ.IsSemisimpleRepresentation :=
  ScaledS1.isSemisimpleRepresentation_of_smul_twist ρ τ (fun _ => (0 : ℚ))
    (fun _ => by norm_num) hρτ h
