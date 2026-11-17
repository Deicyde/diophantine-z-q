import ZInQKernel.Contrib.OneProof.R16CoreYDS965
import ZInQKernel.Contrib.RLeaf.T40
import ZInQKernel.Contrib.OneProof.ModularEquationGeneric

/-! # igusa-drop: `r16CoreY` without Igusa's theorem

Task igusa-drop (2026-11-17), report `docs/research/igusa-drop.md`, scratch `scratch/igusa-drop/`.

aftate-fix2's `AfTateLam.r16CoreY_of_printed` (and r16-det's `AfTateLam.r16CoreY_of_ds965`, which passes the
argument through) takes `hI : X1Igusa.IgusaGL2DS` (Diamond–Shurman Thm 7.6.3) and uses it once, as
`X1Igusa.x1PointsConjugate_of_igusaGL2DS hI : R16IsJ1Dict.X1PointsConjugate`. That Prop is proved:

* `R16IsJ1Dict.X1PointsConjugate ↔ ZInQ.RLeaf.IgusaTransitive` is `Iff.rfl`
  (`X1Igusa.x1PointsConjugate_iff_igusaTransitive`);
* `ZInQ.RLeaf.IgusaTransitive ↔ ZInQ.RLeaf.X0Transitive` (`ZInQ.RLeaf.igusaTransitive_iff_x0Transitive`,
  `Contrib/RLeaf/T40.lean`, with the proved cusp lemma `ZInQ.RLeaf.tateMuN`);
* `ZInQ.RLeaf.X0Transitive` is proved (`FltCqj2.x0Transitive_proof`, `Contrib/OneProof/ModularEquationGeneric.lean`,
  from Anthropic FLT's cyclic-quotient bijection).

So the theorems below are `r16CoreY_of_printed` and `r16CoreY_of_ds965` without `hI` (proof of the former copied
verbatim with `x1PointsConjugate_proof` in place of `X1Igusa.x1PointsConjugate_of_igusaGL2DS hI`).

No `sorry`, no `axiom`, no build-time code. -/

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 40000

namespace AfTateLam

open scoped TensorProduct
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open scoped TensorProduct MatrixGroups
open IsDedekindDomain NumberField

/-- **`X1PointsConjugate`, proved** (no Igusa): `Iff.rfl` to `IgusaTransitive`, which is equivalent to the proved
`X0Transitive` (T40.lean, with the proved `tateMuN`). -/
theorem x1PointsConjugate_proof : R16IsJ1Dict.X1PointsConjugate :=
  X1Igusa.x1PointsConjugate_iff_igusaTransitive.mpr
    (ZInQ.RLeaf.igusaTransitive_iff_x0Transitive.mpr FltCqj2.x0Transitive_proof)

/-- **`r16CoreY` from the three printed leaves and Mumford, without Igusa (glue, proved).** The proof of
`r16CoreY_of_printed` with `x1PointsConjugate_proof` in place of `X1Igusa.x1PointsConjugate_of_igusaGL2DS hI`. -/
theorem r16CoreY_of_printed_x0 (h1 : HeckeJ1DS) (h2 : AfShimura) (h3 : AfTateDSLambda)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY := by
  have hT : TateModuleFree := T5Torsion.TateFree.tateModuleFree_of_torsionStructure
    (AvSplit.torsionStructure_of_mumford hM)
  intro N χ f J hN hf hJ
  rcases Nat.lt_or_ge N 2 with hN1 | hN2
  · have h1 : N = 1 := by omega
    subst h1
    exact absurd hf (AfTateOr.not_isNewform_one χ f)
  obtain ⟨X, P₀, aj, hX, hJac⟩ := hJ
  obtain ⟨hC, hInt, jX, tX, hgen, hrel⟩ :=
    AfTateOr.isX1AlgDS_of_isX1Model x1PointsConjugate_proof hN2 hX
  have hG : IsX1Gen N X jX tX := ⟨hgen, hrel⟩
  obtain ⟨tp, δ, htp, hδ⟩ := h1 N hN2 X jX tX hC hG P₀ J aj hJac
  obtain ⟨hfin, A, π, θ, hQ, hAct⟩ := h2 N χ f hN2 hf X jX tX hC hG P₀ J aj hJac tp δ htp hδ
  haveI : NumberField (coeffField f) := @NumberField.mk _ _ inferInstance hfin
  have hL := h3 N χ f hN2 hf X jX tX hC hG P₀ J aj hJac tp δ htp hδ A π θ hQ hAct
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
      Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p) := by
    intro ℓ _ emb
    haveI := finiteDimensional_V hT A ℓ
    letI := R16Used.tensorModule ℓ A θ
    haveI := liesOver_place emb
    letI := (rhoLam ℓ (place emb)).toAlgebra
    have hfrob : ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        (∀ a : coeffField f, (a : ℂ) = coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
        (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
            LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p) := by
      intro p hp hpN σ hσ
      obtain ⟨hfinL, hrk, htr, hdet⟩ := component A θ emb σ
      obtain ⟨c, hc, hcp⟩ := @hL ℓ _ (place emb) _ hfinL p hp hpN σ hσ
      obtain ⟨h2, htr', hdet'⟩ := lin_trace_det _ _ _ hcp
      refine ⟨hrk.trans h2, fun a ha => ?_, fun c' hc' => ?_⟩
      · have : a = ⟨coeff f p, coeff_mem_coeffField f p⟩ := Subtype.ext ha
        rw [htr, htr', this, τhat_algebraMap]
      · have : c' = c := Subtype.ext (hc'.trans hc.symm)
        rw [hdet, hdet', this, τhat_algebraMap, map_mul, map_natCast]
    obtain ⟨p, σ, hp, hpN, hσ⟩ := exists_frob (N * ℓ)
      (Nat.mul_ne_zero (by omega) (Fact.out : ℓ.Prime).ne_zero)
    exact ⟨(hfrob p hp hpN σ hσ).1, fun p hp hpN σ hσ => (hfrob p hp hpN σ hσ).2⟩
  refine ⟨hfin, A, π, θ, hQ.1, ?_, fun ℓ _ emb => (key ℓ emb).2⟩
  exact R16Split.dim_eq_of_rank_two hT A θ (fun emb => (key 2 emb).1)

/-- **`r16CoreY` from the printed leaves without Igusa (igusa-drop).** `HeckeJ1DS` (Diamond–Shurman §6.3, §7.9),
`AfShimura` (Shimura 1973 Thm 1), `AfCharpolyDS965` (Diamond–Shurman Thm 9.6.5 at `k = 2`) and Mumford's torsion
theorem: `r16CoreY_of_ds965` without its `X1Igusa.IgusaGL2DS` argument. -/
theorem r16CoreY_of_ds965_x0 (h1 : HeckeJ1DS) (h2 : AfShimura) (h3 : AfCharpolyDS965)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY :=
  r16CoreY_of_printed_x0 h1 h2 h3 hM

end AfTateLam

#print axioms AfTateLam.x1PointsConjugate_proof
#print axioms AfTateLam.r16CoreY_of_printed_x0
#print axioms AfTateLam.r16CoreY_of_ds965_x0
