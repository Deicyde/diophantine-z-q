import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionE1a
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionFamily

/-!
# Theorem 5.3, Lane RC0: the clearing leaf over the full-condition triangle (5.6)

Proposition `ex:limits-fixed-field-clearing`, (5.9) (tex 5487–5645, with the budget of Lemma
`ex:limits-fixed-field-budget`, tex 5208–5486), over the triangle (5.6) (tex 5234–5238,
5398–5403). The leaf `PostLeaves.clearing_model` is `ClearingInputsG3Q2`: the RC53 group's
`ClearingInputsG3` (`CloudB3RC53/ClearingComplex/FullConditionE1a.lean`) with its full-condition
identification in the form `Identification3Q2`, whose new places lie over the primes of the family,
two over each prime: the two conjugate graph places of a split `q` (tex 5247, the two-place local
determinant; tex 5456–5457, the two rank-two singular differentials at the conjugate graph places).
Each new place lies over its prime, and the residue cardinality of its tame model is that prime;
so `card (S' − S) = 2 · card Q` (`Identification3Q2.card_newPlaces`).

* `Identification3Q2`, `Identification3Q2.card_newPlaces`;
* `ClearingInputsG3Q2` (the leaf);
* `clearingInputsG3_of_G3Q2` (PROVED): the RC53 group's `ClearingInputsG3` from it; it discards
  the two-place data (`below`, `lies`, `two`, `hqq`), so their faithfulness carries no weight in
  the deduction;
* `clearingTarget_of_G3Q2` (PROVED): `RCSteps.clearing` from it and height-one regularity, through
  the RC53 group's `clearingTarget_of_G3` (`κ = det(B)⁻¹`, E1a, lane RC7's (5.9)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

variable (K : Type) [Field K] [NumberField K] (S S' : Set (HeightOneSpectrum (𝓞 K)))
  (hS : S ⊆ S')

/-- **The full-condition identification with the two conjugate new places over each prime of the
family** (GLUE, additive over the RC53 group's `Identification3`; tex 5247, 5456–5457): each new
place lies over a prime of `F.Q` (`below`, `lies`), exactly two new places lie over each prime of
`F.Q` (`two`), and the residue cardinality of the tame model at a new place is the prime below it
(`hqq`; the primes of `Q` split in `K`, `Family.Admissible`). -/
structure Identification3Q2 [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
    (F : Family) (dK hK cE tK : ℕ) extends Identification3 K S S' hS F.b dK hK cE tK where
  /-- the prime of the family below a new place -/
  below : NewPlaces K S S' → F.Q
  /-- the new place lies over that prime -/
  lies : ∀ v : NewPlaces K S S', (((below v : ℕ) : ℤ) : 𝓞 K) ∈ v.1.asIdeal
  /-- two new places over each prime of the family -/
  two : ∀ q : F.Q, Fintype.card {v : NewPlaces K S S' // below v = q} = 2
  /-- the residue cardinality of the tame model at a new place is the prime below it -/
  hqq : ∀ v : NewPlaces K S S', qq v = (below v : ℕ)

variable {K S S' hS}

/-- **The number of new places is twice the number of primes of the family** (PROVED). -/
theorem Identification3Q2.card_newPlaces [Fintype (NewPlaces K S S')]
    [DecidableEq (NewPlaces K S S')] {F : Family} {dK hK cE tK : ℕ}
    (M : Identification3Q2 K S S' hS F dK hK cE tK) :
    Fintype.card (NewPlaces K S S') = 2 * F.Q.card := by
  classical
  rw [Fintype.card_congr (Equiv.sigmaFiberEquiv M.below).symm, Fintype.card_sigma]
  simp only [M.two, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  ring

/-- **The inputs of (5.9) over the full-condition triangle (5.6), with the two conjugate new places
over each prime of the family** (tex 5234–5238, 5247, 5208–5645, 3470–3499, 3877–3892, 5456–5457):
a number field `K` and the constants, and at every final family `F` a full-condition
identification `Identification3Q2` (ELLIOT for the inherited cancellation core: the lifted family
model, `B₀ = diag(A_q)`, `T₀ = 0`, the central Smith form, the budget (5.7), tex 5394–5430,
5522–5543; GLUE for the Galois comparisons; the new places, two over each prime of `F.Q`), the
actual cycle, the closed functional and the correction `η` over `𝒪[G]` (data), and the coordinate
identification `OrigCoordLink3` (ELLIOT, Elliot's E1 for the chosen model). Caveats:
`clearingInputsG3_of_G3Q2` discards the two-place data (`below`, `lies`, `two`, `hqq`), so their
faithfulness carries no weight in the deduction; the family-Selmer clause (`Mf`, `Δf`, `hfull`,
`ψf`) is met by every complex, and `M₀`, `Δ₀` are not related to `Mf`, `Δf`; the deduction
`clearingTarget_of_G3Q2` uses only the cancellation core, the derived Selmer identification and
`OrigCoordLink3` (neither `ψ0`, `ψold`, `square`, `tame` nor the PRINT `NekovarProp788ii` is in its
closure); `OrigCoordLink3` does not supply the provenance of `z`, `λ`, `η`. -/
def ClearingInputsG3Q2 {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (dK hK cE tK : ℕ),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
        (_ : DecidableEq (NewPlaces K S S')) (M : Identification3Q2 K S S' hS F dK hK cE tK)
        (z : (M.C.map (φO F.b)).D1 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
        (lam : (M.C.map (φO F.b)).D2 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
        (hz : (M.C.map (φO F.b)).toFour.d1 *ᵥ z = 0)
        (hlam : lam ᵥ* (M.C.map (φO F.b)).toFour.d1 = 0)
        (η : MonoidAlgebra OO (SignGroup F.b)),
        OrigCoordLink3 D F M.toIdentification3 z lam hz hlam η

/-- **The RC53 group's `ClearingInputsG3` from the leaf** (PROVED: forget the primes below the new
places). It discards the two-place data (`below`, `lies`, `two`, `hqq`): their faithfulness to the
text carries no weight in the deduction, which uses only `ClearingInputsG3`. -/
theorem clearingInputsG3_of_G3Q2 {ℓ : ℕ} {D : RCData ℓ} (h : ClearingInputsG3Q2 D) :
    ClearingInputsG3 D := by
  obtain ⟨K, _, _, dK, hK, cE, tK, hF⟩ := h
  refine ⟨K, inferInstance, inferInstance, dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨S, S', hS, _, _, M, z, lam, hz, hlam, η, hlink⟩ := hF Co Ce F hFam
  exact ⟨S, S', hS, inferInstance, inferInstance, M.toIdentification3, z, lam, hz, hlam, η, hlink⟩

/-- **`RCSteps.clearing` from the leaf and height-one regularity** (PROVED: the RC53 group's
`clearingTarget_of_G3`). -/
theorem clearingTarget_of_G3Q2 {ℓ : ℕ} (D : RCData ℓ) (h1 : HeightOneTarget D)
    (h : ClearingInputsG3Q2 D) : ClearingTarget D :=
  clearingTarget_of_G3 D h1 (clearingInputsG3_of_G3Q2 h)

end ZInQ.Manuscript.RC.Wiring
