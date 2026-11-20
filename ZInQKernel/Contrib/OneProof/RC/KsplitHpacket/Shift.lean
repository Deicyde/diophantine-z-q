import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Operator

/-! Read the operator identity at coefficient one, using just the three
needed Fourier shifts (tex 9844–9854 and 10330). -/

noncomputable section

namespace ZInQ.Manuscript.RC.KsplitHpacket

open AddressGenuine PrintsArith O12Local
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B chiType}
variable {U : Finset ℕ} {p : ℕ} {P : O12.LocalPair p}

abbrev mulIndex (p : ℕ) (hp : p ≠ 0) (n : O12.PosIndex) : O12.PosIndex :=
  ⟨p * n.val, mul_ne_zero hp n.property⟩

abbrev powIndex {p : ℕ} (hp : p ≠ 0) (k : ℕ) : O12.PosIndex :=
  ⟨p ^ k, pow_ne_zero k hp⟩

/-- The extra shift beyond `FourierData.UpAtOne`. Only p and p² are
required; the old comparison can separately use the full Fourier action
on its two generators. -/
def UpShift (A : O12.FourierData X) (D : O12.LocalBlocks X U P) (hp : p ≠ 0) : Prop :=
  ∀ v : X.I → X.K, SupportedOn D.active v → ∀ k : ℕ, k = 1 ∨ k = 2 →
    X.coefK (D.Up v) (A.index (powIndex hp k)) =
      X.coefK v (A.index (powIndex hp (k + 1)))

/-- The trace identity read at p² in the model's characteristic-zero
Fourier coordinates. -/
theorem trace_coeff_p_sq (A : O12.FourierData X) (D : O12.LocalBlocks X U P)
    (hp : p ≠ 0) (h₁ : A.UpAtOne D hp) (hs : UpShift A D hp)
    (ha : ∀ v, SupportedOn D.active v → SupportedOn D.active (D.Up v))
    (hold : OldBlockCubic D) :
    X.coefK (tV X.ρ P.φ (X.F U)) (A.index (powIndex hp 2)) =
      X.coefK (X.F U) (A.index (powIndex hp 3)) +
        X.coefK (dV X.ρ P.φ (X.F U)) (A.index ⟨p, hp⟩) := by
  let v : X.I → X.K := X.F U
  have hv : SupportedOn D.active v := D.supported
  have ht : SupportedOn D.active (tV X.ρ P.φ v) := scalarOp_supported _ _ hv
  have hd : SupportedOn D.active (dV X.ρ P.φ v) := scalarOp_supported _ _ hv
  obtain ⟨h, hc⟩ := up_trace_identity D ha hold hv
  have e := congrArg (fun w : X.I → X.K => X.coefK w (A.index ⟨1, one_ne_zero⟩)) h
  change X.coefK (D.Up (D.Up (tV X.ρ P.φ v))) (A.index ⟨1, one_ne_zero⟩) =
    X.coefK (D.Up (D.Up (D.Up v)) + dV X.ρ P.φ (D.Up v))
      (A.index ⟨1, one_ne_zero⟩) at e
  have hindex : (⟨p, hp⟩ : O12.PosIndex) = powIndex hp 1 :=
    Subtype.ext (pow_one p).symm
  rw [map_add, Pi.add_apply, ← hc, h₁ _ (ha _ ht), h₁ _ (ha _ (ha _ hv)), h₁ _ hd] at e
  rw [hindex, hs _ ht 1 (Or.inl rfl), hs _ (ha _ hv) 1 (Or.inl rfl),
    hs _ hv 2 (Or.inr rfl), ← hindex] at e
  exact e

end ZInQ.Manuscript.RC.KsplitHpacket
