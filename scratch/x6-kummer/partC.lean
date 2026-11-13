
namespace X6Kummer

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3 FS5NoCM

/-! ## §E Transport of the Kummer description between witnesses -/

/-- **N2-L (leaf, new): Elkies' Kummer model of `X₆ → X₆/W ≅ P¹`, on `ℚ̄`-points of one
witness.** Some witness `(Y₃, Φ, X₆, Ψ, fY, π₆)` of the (repaired) leaf bundle has the Kummer
description of the fibres of `π₆` over rational `j₀ ∉ {0, −16/27}` (`KummerFibreEquiv`).

*Published statement* (Elkies, "Shimura curve computations", ANTS-III, LNCS 1423 (1998), §3 on
`X*(6)` and its double covers; Kurihara, J. Fac. Sci. Univ. Tokyo 25 (1979), `X₀(6,1)` as the
conic `x² + y² + 3 = 0`; locators UNVERIFIED): `X₆ = X₀(6,1)` is the smooth conic
`C : Y² + 3X² + 3Z² = 0` over `ℚ`, the Atkin–Lehner group acts by the sign changes of `X`, `Y`,
and the quotient map `X₆ → X₆/W ≅ P¹` is `t = −X²/Z²` in Elkies' coordinate `t` on `X*(6)`
(`t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`), i.e. `j = 16(t − 1)/27` in the
normalization of R2fp (`j = 0, ∞, −16/27` at `−4, −3, −24`: the Möbius map is fixed by the three
values). *Why the points form is a consequence*: over `j₀ ∈ ℚ` (`Z ≠ 0`, scale `Z = 1`) the points
of `C(ℚ̄)` are the `(X, Y) = (a, b)` with `a² = −t₀`, `b² = −3a² − 3 = 3(t₀ − 1)`; the bijection
`C(ℚ̄) ≅ X₆(ℚ̄)` of an isomorphism of `ℚ`-schemes commutes with `Aut(ℚ̄/ℚ)`. The constants `−1, 3`
are the ones of rv-h-cm §2.3, checked against González–Rotger Thm 5.12 on all 24 rational CM
points of Elkies' table by rv-nocm §1.3 Part B; the conic `Y² + 3X² + 3 = 0` and Kurihara's
`x² + y² + 3 = 0` both correspond to the quaternion algebra `(−1, −3)_ℚ`, ramified at `{3, ∞}`
(so they are isomorphic over `ℚ`; both have no real point). Existential over the witness, like
`LeafQM.AV.R1R2fp` itself: the genuine objects (Shimura–Deligne `Y₃`, the canonical model `X₆`,
Baba–Granath's `π₆`) are a witness. -/
def X6KummerModel : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ ∧ KummerFibreEquiv X π₆

/-- **Glue (new): base change of a QM pair over `ℚ̄` along `σ ∈ Aut(ℚ̄/ℚ)` is unique up to
isomorphism of QM pairs.** Two pullback squares of `P.A → Spec ℚ̄` along `Spec σ` give a
`ℚ̄`-isomorphism `Q.A ≅ Q'.A` (uniqueness of pullbacks, `IsPullback.isoIsPullback`) commuting with
`ι` (both sides agree after the pullback projections) and fixing the identity sections; a pointed
morphism of abelian varieties is a homomorphism (rigidity, Mumford §4 Cor. 1; proved in Lean by
mul-rigidity, `G0FibreSimple.rigidityHom`), so it is an isomorphism of QM pairs. -/
def PairBaseChangeUnique : Prop :=
  ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (P Q Q' : QMPair Qbar),
    IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q → IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q' →
      Nonempty (QMIso Q.q Q'.q)

/-- CM objects of the three kinds from one witness of the repaired bundle (the kernel's
`cm_objects_of_R1R2fp`). -/
theorem cm_objects_of_props {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (h : R1R2fpFullProps Y Φ X Ψ fY π₆) :
    (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q) :=
  cm_objects_of_R1R2fp ⟨Y, Φ, X, Ψ, fY, π₆, h⟩

/-- **Transport (compiled from `MobiusGlue` and `PairBaseChangeUnique`).** If one witness
`W₀` of the repaired bundle has the Kummer description, every witness `W` has it. The map
`H = Ψ₀⁻¹ ∘ Ψ : X(ℚ̄) ≃ X₀(ℚ̄)` satisfies `π₆ = π₀ ∘ H` (qm-pin's `phi_part` gives
`g : Y → Y₀` with `Φ = Φ₀ ∘ g`; `MobiusGlue` gives `π₆ ∘ fY = π₀ ∘ f₀ ∘ g`; `H ∘ fY = f₀ ∘ g` by
the forgetful clause; `fY` is onto `X(ℚ̄)`) and commutes with `Aut(ℚ̄/ℚ)` (the Galois clause of
`X6Props` on both witnesses, and `PairBaseChangeUnique`). -/
theorem kummerFibreEquiv_transport (hM : MobiusGlue) (hB : PairBaseChangeUnique)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀}
    {X₀ : Over (Spec (CommRingCat.of ℚ))} {Ψ₀ : (fieldPt Qbar ⟶ X₀) ≃ Quotient (pairSetoid Qbar)}
    {f₀ : Y₀ ⟶ X₀} {π₀ : ToP1 X₀.left} (h₀ : R1R2fpFullProps Y₀ Φ₀ X₀ Ψ₀ f₀ π₀)
    (hK₀ : KummerFibreEquiv X₀ π₀)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (h : R1R2fpFullProps Y Φ X Ψ fY π₆) :
    KummerFibreEquiv X π₆ := by
  obtain ⟨g, hg⟩ := phi_part (R1fpProps.univ h₀.1) h.1
  have hR₀ := R2fpProps_of_X6 h₀.2.2.1 h₀.2.2.2.1
  have hR := R2fpProps_of_X6 h.2.2.1 h.2.2.2.1
  have hπ := hM Y₀ Y Φ₀ Φ _ _ g h₀.1 hR₀ h.1 hR (cm_objects_of_props h₀) hg
  obtain ⟨-, -, -, hgal, -, hf⟩ := h.2.2.1
  obtain ⟨-, -, -, hgal₀, -, hf₀⟩ := h₀.2.2.1
  obtain ⟨-, hs⟩ := h.2.2.2.2.2.2.1
  let H : (fieldPt Qbar ⟶ X) ≃ (fieldPt Qbar ⟶ X₀) := Ψ.trans Ψ₀.symm
  have hH : ∀ x, Ψ₀ (H x) = Ψ x := fun x => Ψ₀.apply_symm_apply _
  have hHy : ∀ y : fieldPt Qbar ⟶ Y, H (y ≫ fY) = (y ≫ g) ≫ f₀ := by
    intro y
    apply Ψ₀.injective
    rw [hH, hf y _ ((hg Qbar y).trans (Quotient.out_eq _).symm),
      hf₀ (y ≫ g) _ (Quotient.out_eq _).symm]
  have hπH : ∀ x, π₆.val (K := Qbar) x.left = π₀.val (K := Qbar) (H x).left := by
    intro x
    obtain ⟨y, rfl⟩ := hs x
    rw [hHy y]
    calc π₆.val (K := Qbar) (y ≫ fY).left = (π₆.comp fY.left).val (K := Qbar) y.left :=
          (ToP1.val_comp_right π₆ fY.left y.left).symm
      _ = (π₀.comp f₀.left).val (K := Qbar) (y ≫ g).left := hπ y
      _ = π₀.val (K := Qbar) ((y ≫ g) ≫ f₀).left := ToP1.val_comp_right π₀ f₀.left (y ≫ g).left
  have hgalH : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      H (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ H x := by
    intro σ x
    apply Ψ₀.injective
    rw [hH]
    obtain ⟨Q, hQ, hbQ⟩ := hgal σ x (Quotient.out (Ψ x)) (Quotient.out_eq _).symm
    obtain ⟨Q', hQ', hbQ'⟩ := hgal₀ σ (H x) (Quotient.out (Ψ x))
      ((hH x).trans (Quotient.out_eq _).symm)
    rw [hQ, hQ']
    obtain ⟨i⟩ := hB σ _ Q Q' hbQ hbQ'
    exact Quotient.sound ⟨i⟩
  intro j₀ hj0 hj1
  obtain ⟨e₀, he₀⟩ := hK₀ j₀ hj0 hj1
  let F : {x : fieldPt Qbar ⟶ X //
        π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀)} ≃
      {x : fieldPt Qbar ⟶ X₀ //
        π₀.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀)} :=
    H.subtypeEquiv (fun x => by rw [hπH x])
  refine ⟨F.trans e₀, ?_⟩
  intro σ x hx hσx
  have hmem := galPt_mem_fibre π₀ σ (H x) j₀ ((hπH x).symm.trans hx)
  have h1 : F ⟨fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x, hσx⟩ =
      ⟨fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ H x, hmem⟩ := Subtype.ext (hgalH σ x)
  simp only [Equiv.trans_apply]
  rw [h1]
  exact he₀ σ (H x) _ hmem

/-- **N2′ from the leaf N2-L and glue (compiled).** -/
theorem x6KummerEquiv_of_model (hM : MobiusGlue) (hB : PairBaseChangeUnique)
    (hL : X6KummerModel) : X6KummerEquiv := by
  obtain ⟨Y₀, Φ₀, X₀, Ψ₀, f₀, π₀, h₀, hK₀⟩ := hL
  intro Y Φ X Ψ fY π₆ h
  exact kummerFibreEquiv_transport hM hB h₀ hK₀ h

/-- **N2 `X6KummerFibre` from the leaf N2-L `X6KummerModel`, the existing curve glue
`MobiusGlue` and the new glue `PairBaseChangeUnique` (compiled).** -/
theorem x6KummerFibre_of_model (hM : MobiusGlue) (hB : PairBaseChangeUnique)
    (hL : X6KummerModel) : X6KummerFibre :=
  x6KummerFibre_of_equiv (x6KummerEquiv_of_model hM hB hL)

end X6Kummer

#print axioms X6Kummer.galPt_eq_self_iff
#print axioms X6Kummer.x6KummerFibre_of_equiv
#print axioms X6Kummer.kummerFibreEquiv_transport
#print axioms X6Kummer.x6KummerFibre_of_model
