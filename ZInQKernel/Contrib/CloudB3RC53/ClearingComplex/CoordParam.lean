import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.SelmerLink

/-!
# E1 with a coordinate parameter

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
L5509–5617. RC0's E1 (`ClearingCoordIdentity`) combines two different statements:

* **E1a, `CoordLink`** (the identification of the coordinate; tex 5509–5516, 5577–5584 and Lemma
  `ex:arith-common-coordinate`): where `Δ_x ≠ 0`, the corrected coordinate is
  `ũ_x = η_x κ_x 2^{-a} c_x`, with `c_x` the coordinate of `[z] ⊗ [λ]` of the remaining complex
  `D_x` in the determinant basis of the original basis (`κ` the determinant comparison factor of
  the new-local cancellation, `μ = 2^a λ_z`, `η` the universal correction);
* **E1b, `CoordComputation`** (Elliot's determinant computation, tex 5586–5617): in the rank-one
  pattern `c_x = α_x β_x T_x` (`T = ε ∏ δ_i^{(-1)^i}`), in the acyclic pattern `α_x = 0` and
  `c_x = 0`.

Here `c : Addr b → Frac 𝒪` is a PARAMETER. With `c` existential, the split adds no content beyond
E1 itself (it is equivalent to E1 when `η_x κ_x` is invertible); it fixes the interface. The
determinant-line (Knudsen–Mumford / torsion) coordinate of lane Torsion (`CloudB3RC53/Torsion/`)
instantiates `c` in `CoordE1b.lean`, where E1b is PROVED (`coordComputation_km`) and E1a is the
remaining identification.

* `coordIdentity_of_coord` (PROVED): E1a and E1b give `ClearingCoordIdentity`;
* `clearingModel_of_coord` (PROVED): RC0's `ClearingModel` from the Selmer-phrased identification,
  a coordinate `c` with E1b for the genuine generic patterns, and E1a.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks ScalarData evK uK sgnChar cleanT)

variable {O : Type} [CommRing O] [IsDomain O] [Algebra Lam O] {b : ℕ}

/-- **E1a: the corrected coordinate is the coordinate `c` of the remaining complex**, up to
`η_x κ_x 2^{-a}`, where `Δ_x ≠ 0`. -/
def CoordLink (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O)
    (κ η : MonoidAlgebra O (SignGroup b)) (a : ℕ) (e : Addr b → ℕ) (g : Addr b → Lam)
    (c : Addr b → FractionRing O) : Prop :=
  ∀ x : Addr b, evK (sgnChar x) B.Δ ≠ 0 →
    uK (e x) (g x) = evK (sgnChar x) η * evK (sgnChar x) κ * ((2 : FractionRing O) ^ a)⁻¹ * c x

/-- **E1b: Elliot's determinant computation of the coordinate** (tex 5586–5617). -/
def CoordComputation (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O) (sd : ScalarData B)
    (ε : MonoidAlgebra O (SignGroup b)) (c : Addr b → FractionRing O)
    (RankOne Acyclic : Addr b → Prop) : Prop :=
  (∀ x : Addr b, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      c x = sd.αK (evK (sgnChar x)) * sd.βK (evK (sgnChar x)) * cleanT (evK (sgnChar x)) B ε) ∧
  (∀ x : Addr b, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ c x = 0)

/-- **E1 from E1a and E1b** (PROVED). -/
theorem coordIdentity_of_coord (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O)
    (sd : ScalarData B) (κ ε η : MonoidAlgebra O (SignGroup b)) (a : ℕ) (e : Addr b → ℕ)
    (g : Addr b → Lam) (RankOne Acyclic : Addr b → Prop) (c : Addr b → FractionRing O)
    (hlink : CoordLink B κ η a e g c) (hcomp : CoordComputation B sd ε c RankOne Acyclic) :
    ClearingCoordIdentity B sd κ ε η a e g RankOne Acyclic := by
  refine ⟨fun x hΔ hR => ?_, fun x hΔ hA => ?_⟩
  · rw [hlink x hΔ, hcomp.1 x hΔ hR]
    ring
  · obtain ⟨hα, hc⟩ := hcomp.2 x hΔ hA
    exact ⟨hα, by rw [hlink x hΔ, hc, mul_zero]⟩

/-- **RC0's `ClearingModel` from the Selmer-phrased identification and a coordinate** (PROVED):
at every final family, an identification `I`, scalar data, `κ, ε, η`, and a coordinate `c` with
Elliot's computation (E1b) for the genuine generic patterns of `I.D` and the link (E1a) for every
representation of `ũ`. -/
theorem clearingModel_of_coord {ℓ : ℕ} (Dd : RCData ℓ)
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (I : SelmerIdentification F.b dK hK cE tK) (sd : ScalarData I.B)
        (κ ε η : MonoidAlgebra OO (SignGroup F.b)) (c : Addr F.b → FractionRing OO),
        CoordComputation I.B sd ε c I.D.RankOnePattern I.D.AcyclicPattern ∧
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          CoordLink I.B κ η 0 e g c) :
    ClearingModel Dd := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  exact clearingModel_of_selmer Dd ⟨dK, hK, cE, tK, fun Co Ce F hFam => by
    obtain ⟨I, sd, κ, ε, η, c, hcomp, hlink⟩ := hF Co Ce F hFam
    exact ⟨I, sd, κ, ε, η, fun e g hrep =>
      coordIdentity_of_coord _ sd κ ε η 0 e g _ _ c (hlink e g hrep) hcomp⟩⟩

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
