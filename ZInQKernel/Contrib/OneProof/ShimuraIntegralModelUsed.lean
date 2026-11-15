import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard

/-!
# sir-printed: the integral model of `Y₃` in the form its consumer uses

`SGRSplit.ShimuraIntegralModelRep` (the added field `shimuraIntegralModelRep`) asserts that the
polarization-free moduli problem of level-3 QM abelian surfaces is represented over `ℤ_(p)`, `p > 324`, on
*every* locally noetherian `ℤ_(p)`-scheme. Its printed source (Lan 2013 Thm 1.4.1.11 with Thm 5.3.3.1;
Kottwitz 1992 §5) is a PEL moduli problem: its objects carry a principal polarization. Deriving the
polarization-free form on every base needs the relative Lemma P (existence and uniqueness of the principal
polarization of the fixed Rosati type over any base), which no printed source in the bundle states and which
cannot be stated in Lean today (no dual abelian scheme over a base).

Its only consumer, `SGRSplit.shimuraGoodReductionNoGuard_of_rep`, uses the universal property at two kinds of
base only: `S = Spec ℚ̄`, and `S = 𝒴` for the Hecke relabelings `twistAb 𝒜 α`, `rightMulAb 𝒜 u` of the universal
object. This file states exactly that as `ShimuraIntegralModelUsed`, and proves

* `shimuraIntegralModelUsed_of_rep : ShimuraIntegralModelRep → ShimuraIntegralModelUsed` (the new leaf is
  never stronger than the field);
* `shimuraGoodReductionNoGuard_of_used : ShimuraIntegralModelUsed → ShimuraGoodReductionNoGuard` (the consumer
  needs nothing more).

Its derivation from the printed PEL theorem needs Lemma P only over `ℚ̄` (characteristic 0; rv-qm-polar), and
the Hecke clauses come from Yoneda applied to automorphisms of the PEL functor itself, whose polarizations are
written down explicitly (`λ ↦ λ ∘ ι(ε v_α)`; rv-qm-polar §§6–7). Report: docs/research/sir-printed.md.
-/

noncomputable section

namespace SIRPrinted

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid HDec.VertWitness HDec.CurveSplitGR SGRSplit

/-- The assertion of `ShimuraIntegralModelUsed` at one prime `p`. -/
def ShimuraIntegralModelUsedAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMAbScheme 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    (∀ 𝒜' : QMAbScheme (Spec (CommRingCat.of Qbar)),
      ∃! y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, QMFamFibre 𝒜.toQMFamily y 𝒜'.toQMFamily) ∧
    (∀ α : O ≃+* O, ∃ g : 𝒴 ≅ 𝒴, QMFamFibre 𝒜.toQMFamily g.hom.left (twistAb 𝒜 α).toQMFamily) ∧
    (∀ u : Oˣ, ∃ g : 𝒴 ≅ 𝒴, QMFamFibre 𝒜.toQMFamily g.hom.left (rightMulAb 𝒜 u).toQMFamily)

/-- **LEAF (consequence of the printed PEL theorem; pending reading): the integral model of the level-3
Shimura curve of discriminant 6, at the bases its consumer uses.** For each prime `p > 324` there are a proper
smooth curve `𝒴/ℤ_(p)` and a `QMAbScheme` `𝒜` over `𝒴` (an abelian surface scheme with `ι : 𝒪 → End` and full
level-3 data `η`) such that

1. (`ℚ̄`-points) every object `𝒜'` over `Spec ℚ̄` is the pullback of `𝒜` along exactly one point
   `y : Spec ℚ̄ → 𝒴`;
2. (Hecke, `Aut 𝒪`) for each ring automorphism `α` of `𝒪`, the relabeled universal object
   `(𝒜, ι ∘ α, η ∘ α)` is the pullback of `𝒜` along an automorphism of `𝒴` over `ℤ_(p)`;
3. (Hecke, `𝒪^×`) for each `u ∈ 𝒪^×`, `(𝒜, ι, η(· u))` is the pullback of `𝒜` along an automorphism of `𝒴`
   over `ℤ_(p)`.

*Printed source* (locators UNVERIFIED, no network): K.-W. Lan, *Arithmetic compactifications of PEL-type
Shimura varieties*, LMS Monographs 36 (Princeton, 2013), Thm 1.4.1.11 (the PEL moduli problem `M_H` with neat
level `H ⊂ G(Ẑ^□)` is representable by a smooth quasi-projective scheme over `S₀ = Spec ℤ_(□)`) with
Thm 5.3.3.1 (`M_H` is proper when there are no cusps, as for the division algebra `B`), at `□ = {p}`; the
comparison with R. Kottwitz, J. AMS 5 (1992) §5 (prime-to-`p` isogeny classes) is Lan §1.4.3. PEL datum: `B =
(2, −3)`, `𝒪` its maximal order (`p ∤ disc 𝒪 = 36`), the positive involution `x† = μ⁻¹x̄μ` (`μ = 2j + k`),
`L = 𝒪` with the form `E₀(x, y) = trd(μ⁻¹xȳ)` (unimodular: rv-qm-polar `gram_det`, compiled), so `G = B^×`,
reflex field `ℚ`, `H = U^p(3) = ker(𝒪̂^{p×} → (𝒪/3𝒪)^×)` (neat; level only at `3 ≠ p`, allowed since
`H ⊂ G(Ẑ^p)`).

*Why this Lean form is a consequence, never stronger* (docs/research/sir-printed.md §3): `𝒜` is the universal
object with its polarization forgotten and `η(a) = α₃(a mod 3)`. Clause 1: an object over `ℚ̄` has exactly one
principal polarization of type `†` (Lemma P over `ℚ̄`, characteristic 0; rv-qm-polar §0), its `η` is an
`𝒪`-linear bijection `𝒪/3𝒪 ≅ A[3](ℚ̄)` (81 points) and is automatically a similitude for the Weil pairing
(every `𝒪`-linear isomorphism is, once one is: `GL_𝒪(𝒪/3) = (𝒪/3)^{op×}` acts by similitudes), and the
determinant condition is automatic over a field of characteristic 0; any polarization-free isomorphism of
objects over `ℚ̄` respects the polarizations by the uniqueness half of Lemma P over `ℚ̄`. Clauses 2–3: Yoneda for
the automorphisms `(A, λ, ι, α₃) ↦ (A, λ ∘ ι(ε v_α), ι ∘ α, α₃ ∘ α)` and `(A, λ, ι, α₃) ↦ (A, λ, ι, α₃ ∘ r_u)`
of the PEL functor on all locally noetherian `ℤ_(p)`-schemes (`v_α = μ⁻¹α(μ)`, `ε = sign trd v_α`; rv-qm-polar
`twist_type`, compiled algebra), forgetting `λ`. No relative Lemma P is used. Not the full field:
`shimuraIntegralModelUsed_of_rep` proves this from `ShimuraIntegralModelRep`. -/
def ShimuraIntegralModelUsed : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraIntegralModelUsedAt p

/-! ## The new leaf is never stronger than the field -/

/-- The automorphism of `𝒴` attached to a relabeling with an inverse relabeling, from the full universal
property over `𝒴` (as in `SGRSplit.shimuraGoodReductionNoGuard_of_rep`). -/
theorem hecke_iso_of_rep (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 𝒜₁ 𝒜₂ : QMAbScheme 𝒴.left)
    (hU : ∀ 𝒜' : QMAbScheme 𝒴.left, ∃! g : 𝒴 ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily)
    (h12 : ∀ (g g' : 𝒴 ⟶ 𝒴), QMFamFibre 𝒜.toQMFamily g.left 𝒜₁.toQMFamily →
      QMFamFibre 𝒜.toQMFamily g'.left 𝒜₂.toQMFamily → QMFamFibre 𝒜.toQMFamily (g ≫ g').left 𝒜.toQMFamily)
    (h21 : ∀ (g g' : 𝒴 ⟶ 𝒴), QMFamFibre 𝒜.toQMFamily g.left 𝒜₁.toQMFamily →
      QMFamFibre 𝒜.toQMFamily g'.left 𝒜₂.toQMFamily → QMFamFibre 𝒜.toQMFamily (g' ≫ g).left 𝒜.toQMFamily) :
    ∃ g : 𝒴 ≅ 𝒴, QMFamFibre 𝒜.toQMFamily g.hom.left 𝒜₁.toQMFamily := by
  obtain ⟨g, hg, -⟩ := hU 𝒜₁
  obtain ⟨g', hg', -⟩ := hU 𝒜₂
  obtain ⟨g0, -, h0⟩ := hU 𝒜
  have hid : QMFamFibre 𝒜.toQMFamily (CommaMorphism.left (𝟙 𝒴)) 𝒜.toQMFamily := qmFamFibre_id _
  exact ⟨⟨g, g', (h0 _ (h12 g g' hg hg')).trans (h0 _ hid).symm,
    (h0 _ (h21 g g' hg hg')).trans (h0 _ hid).symm⟩, hg⟩

/-- **`ShimuraIntegralModelUsed` follows from `ShimuraIntegralModelRep`** (compiled): the new leaf is a
specialization of the field. -/
theorem shimuraIntegralModelUsed_of_rep (hRep : ShimuraIntegralModelRep) : ShimuraIntegralModelUsed := by
  intro p _ hp
  obtain ⟨𝒴, 𝒜, hpr, hsm, hU⟩ := hRep p hp
  have hN := isLocallyNoetherian_of_smooth p 𝒴 hsm
  refine ⟨𝒴, 𝒜, hpr, hsm, fun 𝒜' => ?_, fun α => ?_, fun u => ?_⟩
  · -- `ℚ̄`-points
    obtain ⟨g, hg, hgu⟩ := hU (Over.mk (Spec.map (CommRingCat.ofHom (zlocTo p Qbar))))
      (by dsimp; infer_instance) 𝒜'
    refine ⟨g.left, hg, fun y hy => ?_⟩
    have hyy : y ≫ 𝒴.hom = Spec.map (CommRingCat.ofHom (zlocTo p Qbar)) := spec_to_Zloc_ext p _ _
    have := hgu (Over.homMk y hyy) hy
    exact congrArg CommaMorphism.left this
  · -- `Aut(𝒪)`
    refine hecke_iso_of_rep p 𝒴 𝒜 (twistAb 𝒜 α) (twistAb 𝒜 α.symm) (hU 𝒴 hN) ?_ ?_
    · rintro g g' ⟨h, hpb, hi, he⟩ ⟨h', hpb', hi', he'⟩
      exact qmFamFibre_comp 𝒜 (fun a => α a) (fun a => α a) (fun a => α.symm a) (fun a => α.symm a)
        g.left g'.left h h' hpb hpb' hi he hi' he' (fun a => by simp) (fun a => by simp)
    · rintro g g' ⟨h, hpb, hi, he⟩ ⟨h', hpb', hi', he'⟩
      exact qmFamFibre_comp 𝒜 (fun a => α.symm a) (fun a => α.symm a) (fun a => α a) (fun a => α a)
        g'.left g.left h' h hpb' hpb hi' he' hi he (fun a => by simp) (fun a => by simp)
  · -- `𝒪^×`
    refine hecke_iso_of_rep p 𝒴 𝒜 (rightMulAb 𝒜 u) (rightMulAb 𝒜 u⁻¹) (hU 𝒴 hN) ?_ ?_
    · rintro g g' ⟨h, hpb, hi, he⟩ ⟨h', hpb', hi', he'⟩
      exact qmFamFibre_comp 𝒜 (fun a : O => a) (fun a : O => a * (u : O)) (fun a : O => a)
        (fun a : O => a * ((u⁻¹ : Oˣ) : O)) g.left g'.left h h' hpb hpb' hi he hi' he' (fun a => rfl)
        (fun a => by rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one])
    · rintro g g' ⟨h, hpb, hi, he⟩ ⟨h', hpb', hi', he'⟩
      exact qmFamFibre_comp 𝒜 (fun a : O => a) (fun a : O => a * ((u⁻¹ : Oˣ) : O)) (fun a : O => a)
        (fun a : O => a * (u : O)) g'.left g.left h' h hpb' hpb hi' he' hi he (fun a => rfl)
        (fun a => by rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one])

/-! ## The consumer needs nothing more -/

/-- **`ShimuraGoodReductionNoGuard` from `ShimuraIntegralModelUsed` and the three proved glue pieces**
(compiled; the proof of `SGRSplit.shimuraGoodReductionNoGuard_of_rep` with the universal property used only
where the new leaf provides it). -/
theorem shimuraGoodReductionNoGuard_of_used_glue (hU : ShimuraIntegralModelUsed)
    (g1 : QMAbFieldFibre) (g2 : QML3AsQMAb) (g3 : FibreClassUnique) :
    ShimuraGoodReductionNoGuard := by
  intro p _ hp
  obtain ⟨𝒴, 𝒜, hpr, hsm, hQ, hA, hu⟩ := hU p hp
  refine ⟨𝒴, 𝒜.toQMFamily, hpr, hsm, fun K _ _ y => g1 _ 𝒜 K y, ?_, ?_, ?_, ?_⟩
  · -- injectivity on `ℚ̄`-points
    intro y y' P P' hP hP' hPP'
    obtain ⟨𝒜P, h𝒜P⟩ := g2 Qbar P
    obtain ⟨f⟩ := Quotient.exact hPP'
    have hP'' : IsFibreOf 𝒜.toQMFamily y' P := isFibreOf_of_iso _ f hP'
    obtain ⟨y0, -, hy0⟩ := hQ 𝒜P
    exact (hy0 y ((h𝒜P _ _ y).mp hP)).trans (hy0 y' ((h𝒜P _ _ y').mp hP'')).symm
  · -- surjectivity on `ℚ̄`-points
    intro P
    obtain ⟨𝒜P, h𝒜P⟩ := g2 Qbar P
    obtain ⟨y, hy, -⟩ := hQ 𝒜P
    exact ⟨y, (h𝒜P _ _ y).mpr hy⟩
  · -- `Aut(𝒪)`
    intro α
    obtain ⟨g, h, hpb, hi, he⟩ := hA α
    refine ⟨g, fun y P P' hP hP' => ?_⟩
    rw [M3.twist_mk]
    refine g3 _ _ _ _ _ _ hP' ?_
    obtain ⟨k, hkpb, hki, hke⟩ := hP
    refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
    · exact paste_iota _ _ _ _ _ (hki (α a)) (hi a)
    · exact paste_eta _ _ _ _ _ _ _ (hke (α a)) (he a)
  · -- `𝒪^×`
    intro u
    obtain ⟨g, h, hpb, hi, he⟩ := hu u
    refine ⟨g, fun y P P' hP hP' => ?_⟩
    change M3.mk P' = M3.mk (P.rightMul u)
    refine g3 _ _ _ _ _ _ hP' ?_
    obtain ⟨k, hkpb, hki, hke⟩ := hP
    refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
    · exact paste_iota _ _ _ _ _ (hki a) (hi a)
    · exact paste_eta _ _ _ _ _ _ _ (hke (a * u)) (he a)

/-- **`ShimuraGoodReductionNoGuard` from the new leaf alone** (compiled; standard axioms). -/
theorem shimuraGoodReductionNoGuard_of_used (hU : ShimuraIntegralModelUsed) :
    ShimuraGoodReductionNoGuard :=
  shimuraGoodReductionNoGuard_of_used_glue hU qmAbFieldFibre (qml3AsQMAb_of abVarSurfaceRelDim)
    fibreClassUnique

end SIRPrinted

end -- noncomputable section

