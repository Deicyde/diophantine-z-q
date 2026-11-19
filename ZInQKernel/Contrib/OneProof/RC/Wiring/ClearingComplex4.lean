import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.GenuineIdentification
import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1a
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex3

/-!
# Theorem 5.3, Lane RC0 round 4: determinant clearing (5.9) over the genuine Selmer complexes

Manuscript `diophantine_zq.tex`, Proposition `ex:limits-fixed-field-clearing` (tex 5487–5645), with
Lemma `ex:limits-fixed-field-budget` (tex 5394–5425), the support change (tex 3470–3499), the
class-functional coordinate (Definition `ex:arith-coordinate`, tex 3877–3892) and the corrected
coordinate of Lemma `ex:arith-common-coordinate` (tex 4219–4224).

The round-3 leaf `ClearingInputsCx D` (`ClearingComplex3.lean`) asks, at every final family, for
the Selmer-phrased identification `SelmerIdentification` (with ANY Selmer data), scalar data, a
coordinate `c`, Elliot's determinant computation E1b and the coordinate link E1a. Here it is PROVED
(`clearingInputsCx_of_G`) from the smaller leaf `ClearingInputsG D`:

* the fixed field `K` (tex 5641–5643: `d_K, t_K, h_K` are fixed after `K`) and the constants
  `d_K, h_K, c_E, t_K` before the family;
* at every final family, batch 3's `Identification2G` (GLUE; `GenuineIdentification.lean`): the
  pre-cancellation finite free family model over `Λ[G]` with one nonempty block of new local
  differentials indexed by the new places `S' − S`, `T₀ = Y₀ = 0`, the central Smith form, the
  (5.7) counts; on the Selmer side lane RC26's GENUINE continuous-cochain Selmer complexes:
  the family Selmer complex `galoisSelData K S' 𝒪[G] M Δ` (through RC26's
  `selmerIdentificationOfGenuine`), the genuine support change `galoisSupportData` (Nekovář
  7.8.8(ii); `Identification2G.support_qis` derives its quasi-isomorphy from the PRINT
  `NekovarProp788ii`; the deduction does not use it), and the
  tame model as a quasi-isomorphic model of the genuine local cochains (no degreewise
  `SupportChangeUnramified`, which genuine cochains can never satisfy);
* the actual cycle `z` of `D¹ = C¹` and the closed functional `λ` on `C² = D² ⊕ N` over `𝒪[G]`
  (tex 5513–5516), and the universal correction `η`;
* ONE identification of the coordinate (`OrigCoordLink`; ELLIOT, Elliot's E1 in the original
  basis, tex 5605–5608; definitional only for the genuine relaxed complex, which is not
  enforced): where `Δ_x ≠ 0`, the corrected
  coordinate is `ũ_x = η_x · c^{orig}_x`, with `c^{orig}_x` the coordinate of `[z] ⊗ [λ]` of the
  sign-evaluated ORIGINAL complex `C_x` in the original determinant basis (tex 5605–5608: "its
  coordinate in the original determinant basis is exactly `ũ_x = η_x κ_x …`", with
  `ũ = η u_rel`, tex 4219–4224, and `u_rel` that coordinate, tex 3877–3892).

PROVED from them (no new input): the remaining complex `D` is the new-local cancellation of `C` over
`𝒪[G]`; the determinant comparison factor is `κ = det B` (an `S`-unit, tex 5509–5513), by batch 3's
`kmCoord_preCancel`; the transported functional is `μ = λ ∘ incl` (tex 5513–5516); E1a
(`CoordLink`); the coordinate is lane Torsion's Knudsen–Mumford coordinate of `D_x` and E1b is
batch 3's `coordComputation_km`; the Smith model, the generic patterns, the entry poles, the budget
(5.7) and (5.9) by lane RC7 (`clearingTarget_of_complex`).

`OrigCoordLink` is implied by batch 3's two CoordLink inputs (`origCoordLink_of_eta_rel`:
`CorrectedIsEta` and `RelIsKM`, stated here for `Identification2G` as `RelIsKMG`), so every
discharge of that pair discharges it; it holds at a generically acyclic constituent with `ũ_x = 0`
(both sides vanish), as the text's convention `u = 0` (tex 3889–3890) requires.

* `coordLink_of_orig` (E1a, PROVED); `origCoordLink_of_eta_rel` (PROVED);
* `clearingInputsCx_of_G : ClearingInputsG D → ClearingInputsCx D` (PROVED);
* `clearingTarget_of_G : HeightOneTarget D → ClearingInputsG D → ClearingTarget D` (PROVED).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.Torsion (kmCoord)
open ZInQ.Contrib.CloudB3RC53.CoordLink (CorrectedIsEta Cev hzC hzev hlamev σPre transportFun
  hμ_cancel kmCoord_preCancel isUnit_Bev det_Bev Dev_toFour_eq transport_map kmCoord_congr)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

section Coordinate

variable {K : Type} [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  {hS : S ⊆ S'} [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- Coordinate identification at every representation where Δ_x ≠ 0. For the same actual complex,
class, functional, correction and retained basis this is the definition of the corrected coordinate
(tex 3877–3892, 4224, 5605–5615). The existential interface does not supply that provenance. -/
def OrigCoordLink {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) : Prop :=
  ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep D F e g →
    ∀ x : Addr F.b, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      uK (e x) (g x) = evK (sgnChar x) η *
        kmCoord (CoordLink.PreComplex'.toFour (Cev (M.C.map (φO F.b)) x)) (evK (sgnChar x) ∘ z)
          (evK (sgnChar x) ∘ lam) (hzev (hzC M.isUnit_B hz) x) (hlamev hlam x)
          (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N)

/-- **The relaxed coordinate is the Knudsen–Mumford coordinate of the original complex**, for the
genuine identification (GLUE; tex 3877–3892, 5513–5516): where `Δ_x ≠ 0`, `u_{rel,x}` is the
coordinate of `[z] ⊗ [λ]` of `C_x` in the original determinant basis. The body of batch 3's
`RelIsKM`, stated for `Identification2G`; with `CorrectedIsEta` it gives `OrigCoordLink`. -/
def RelIsKMG (M : Identification2G K S S' hS b dK hK cE tK) (urel : Addr b → FractionRing OO)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0) :
    Prop :=
  ∀ x : Addr b, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
    urel x = kmCoord (CoordLink.PreComplex'.toFour (Cev (M.C.map (φO b)) x))
      (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ lam) (hzev (hzC M.isUnit_B hz) x)
      (hlamev hlam x) (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N)

/-- **Batch 3's two E1a inputs give `OrigCoordLink`** (PROVED): `ũ = η u_rel` and
`u_rel = c^{orig}` where `Δ_x ≠ 0`. -/
theorem origCoordLink_of_eta_rel {ℓ : ℕ} {D : RCData ℓ} {F : Family}
    {M : Identification2G K S S' hS F.b dK hK cE tK}
    {z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b)}
    {lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b)}
    {hz : M.D.d1 *ᵥ z = 0}
    {hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0}
    {η : MonoidAlgebra OO (SignGroup F.b)} {urel : Addr F.b → FractionRing OO}
    (hη : CorrectedIsEta D F η urel) (hrel : RelIsKMG M urel z lam hz hlam) :
    OrigCoordLink D F M z lam hz hlam η := fun e g hrep x hΔ => by
  rw [hη e g hrep x, hrel x hΔ]

/-- **E1a for the genuine identification** (PROVED; the new-local cancellation, batch 3's
`kmCoord_preCancel`): from `OrigCoordLink`, `ũ_x = η_x κ_x c_x` where `Δ_x ≠ 0`, with
`κ = det B` the determinant comparison factor and `c = cOf D z μ` the Knudsen–Mumford coordinate of
the remaining complex at the transported functional `μ = λ ∘ incl`. -/
theorem coordLink_of_orig {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (h : OrigCoordLink D F M z lam hz hlam η) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep D F e g →
      CoordLink M.toIdentification.B (M.C.map (φO F.b)).B.det η 0 e g
        (cOf M.D z (transportFun (M.C.map (φO F.b)) lam) hz
          (hμ_cancel (M.C.map (φO F.b)) M.isUnit_B hlam)) := by
  intro e g hrep x hΔ
  rw [h e g hrep x hΔ, pow_zero, inv_one, mul_one]
  have key := kmCoord_preCancel (C := Cev (M.C.map (φO F.b)) x)
    (isUnit_Bev (M.C.map (φO F.b)) M.isUnit_B x) (z := evK (sgnChar x) ∘ z)
    (lam := evK (sgnChar x) ∘ lam) (hz := hzev (hzC M.isUnit_B hz) x) (hlam := hlamev hlam x)
  refine (congrArg (evK (sgnChar x) η * ·) key).trans ?_
  rw [det_Bev (M.C.map (φO F.b)) x, mul_assoc]
  congr 2
  unfold cOf
  exact (kmCoord_congr (Dev_toFour_eq (M.C.map (φO F.b)) M.isUnit_B x) rfl
    (transport_map M.isUnit_B lam x) _ _ _ _ _).symm

end Coordinate

/-- **The inputs of (5.9) over the genuine Selmer complexes** (tex 5487–5645, 5394–5425,
3470–3499, 3877–3892, 4219–4224). Fields, with tex lines, kind and owner:

| field | tex | kind | owner |
|---|---|---|---|
| `K` a number field (the fixed field) | 5641–5643 | definition | RC0 |
| `dK hK cE tK`, before the family | 5251–5267, 5641–5643 | definition | (content in (5.7)) |
| per final family `F`: `S ⊆ S'`, the new places `S' − S` finite | 5394–5403, 3483–3489 | definition | batch 3 ClearingComplex |
| `M : Identification2G K S S' hS F.b dK hK cE tK` | 5394–5463, 5486–5538, 3470–3499 | GLUE (cancellation data + genuine Selmer comparisons + `TameModelQIso`); `Identification2G.support_qis` derives the support change quasi-isomorphy from the PRINT `NekovarProp788ii`; the deduction does not use it | batch 3 ClearingComplex / RankCounts, RC26 |
| `z`, `hz`: the actual cycle of `D¹ = C¹` over `𝒪[G]` (integral, tex 5515–5516) | 5513–5516 | definition (data; its content is carried by `OrigCoordLink`) | batch 3 PairedFunctional / RC7 |
| `lam`, `hlam`: the closed paired functional on `C² = D² ⊕ N` over `𝒪[G]`, transported to `μ = λ ∘ incl` | 5513–5516, 3704–3880 | definition (data; exponent `a = 0`, tex 3864–3866; content via `OrigCoordLink`) | batch 3 PairedFunctional |
| `η`: the universal correction | 4194–4222 | definition | RC15 |
| `OrigCoordLink D F M z lam hz hlam η` (`ũ_x = η_x c^{orig}_x` where `Δ_x ≠ 0`, every representation `ũ = g/2^e`) | 5605–5608, 4219–4224, 3877–3892 | ELLIOT (Elliot's E1 in the original basis, tex 5605–5608; definitional only for the genuine relaxed complex, which is not enforced) | RC7 / RC15 / batch 3 CoordLink |

Only the cancellation part of `M` (its `toIdentification`), `z`, `λ`, `η` and `OrigCoordLink` are
consumed by the conversion; the Selmer-side fields of `M` (the genuine family model, the genuine
support change, the tame model) record the provenance of the cancellation data in the text (Lemma
`ex:limits-fixed-field-budget`) and are not used downstream.

DEPARTURE (form, weaker): the fixed field `K = ℚ(√k)` (tex 5641–5643) and the supports `S ⊆ S'`
are existential (no field pins `K` to the final companion `k`); the conversion does not use them.
-/
def ClearingInputsG {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (dK hK cE tK : ℕ),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∃ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (_ : Fintype (NewPlaces K S S'))
        (_ : DecidableEq (NewPlaces K S S')) (M : Identification2G K S S' hS F.b dK hK cE tK)
        (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
        (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
        (hz : M.D.d1 *ᵥ z = 0)
        (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
        (η : MonoidAlgebra OO (SignGroup F.b)), OrigCoordLink D F M z lam hz hlam η

/-- **The round-3 leaf `ClearingInputsCx` from the genuine leaf** (PROVED): batch 3's
`clearingInputsCx_of_kmG` (the Selmer-phrased identification over lane RC26's genuine family
Selmer complex, the scalar data read off `z, μ`, `c := kmCoord`, E1b `coordComputation_km`) with
E1a from `coordLink_of_orig` (`κ = det B`, `μ = λ ∘ incl`). -/
theorem clearingInputsCx_of_G {ℓ : ℕ} (D : RCData ℓ) (h : ClearingInputsG D) :
    ClearingInputsCx D := by
  obtain ⟨K, _, _, dK, hK, cE, tK, hF⟩ := h
  exact clearingInputsCx_of_kmG D K ⟨dK, hK, cE, tK, fun Co Ce F hFam => by
    obtain ⟨S, S', hS, _, _, M, z, lam, hz, hlam, η, hlink⟩ := hF Co Ce F hFam
    exact ⟨S, S', hS, inferInstance, inferInstance, M, z,
      transportFun (M.C.map (φO F.b)) lam, hz, hμ_cancel (M.C.map (φO F.b)) M.isUnit_B hlam,
      (M.C.map (φO F.b)).B.det, η, coordLink_of_orig D F M z lam hz hlam η hlink⟩⟩

/-- **`RCSteps.clearing` from the genuine leaf and height-one regularity** (PROVED; round 3's
`clearingTarget_of_complex`: batch 3's `clearingModel_of_coord` and lane RC7's `clearing_nodes`). -/
theorem clearingTarget_of_G {ℓ : ℕ} (D : RCData ℓ) (h1 : HeightOneTarget D)
    (h : ClearingInputsG D) : ClearingTarget D :=
  clearingTarget_of_complex D h1 (clearingInputsCx_of_G D h)

end ZInQ.Manuscript.RC.Wiring
