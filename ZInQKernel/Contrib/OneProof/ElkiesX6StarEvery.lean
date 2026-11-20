import ZInQKernel.Contrib.OneProof.ElkiesX6StarPrinted

/-! # elkies-print: Elkies' coordinate on `X*(6)` for every witness, without the bundled moduli witness

Task elkies-print (docs/research/elkies-print.md). The research field `elkiesX6StarFunctionField`
(`HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField`, elkies-coord) was re-rated GLUE on 2026-11-16 because it
bundles the existence of the moduli witness (a fine `Y₃` with `R1fpPropsAb` and a coarse `X₆` with `X6Props`) with
Elkies' statement about the coordinate `t`. No print states the witness; this is the shape rated composite for
`gonzalezRotgerX6Ab`.

This file separates the two, as gt-grcount did for González–Rotger Prop. 5.6 (`GRCountX6.GonzalezRotgerProp56X6`):

1. `ElkiesX6StarEvery` (new LEAF): Elkies' coordinate statement (function-field form `ℚ(X₆)^W = ℚ(t)`, the CM values
   `t = 0, 1, ∞` at discriminants `−24, −4, −3`, the charts `s² = −t`, `r² = 3(t − 1)`) for **every** witness of the
   moduli description of `X₀(6,1)`. There is no existence claim.
2. `X6WitnessAb`: a witness exists. It is not a new leaf. It is supplied by the field `gonzalezRotgerX6Ab`
   (`x6WitnessAb_of_gonzalezRotgerX6Ab`), or by any other source of the witness (task grx6ab-print's
   `GRX6AbPrint.x6ModuliWitness_of_coarse` concludes the same Prop, `GRDict.X6ModuliWitness`).
3. `elkiesX6StarFunctionField_of_every : ElkiesX6StarEvery → X6WitnessAb → ElkiesX6StarFunctionField` (the discharge).
4. **The new leaf is no stronger than the field it replaces.** `every_of_functionField : ElkiesX6StarFunctionField →
   ObjBridge.TorsionStructure → ElkiesX6StarEvery` holds because any two witnesses have compatibly isomorphic coarse
   curves. That comparison comes from the abelian-scheme fine comparison `compare_iso_ab` and the coarse comparison
   `coarse_compare_ab`. The coarse comparison uses `PairsLift` from T5, plus the kernel's proved `FactorThroughSurj`
   and `CurveBijIso`. Elkies' clauses are transported along the isomorphism (§3: comorphisms on function fields,
   conjugation of the Atkin–Lehner group, the charts). So, given a witness and T5, the leaf and the field are
   equivalent (`every_iff_functionField`).

No `sorry`; standard axioms only.
-/

set_option linter.style.longLine false

namespace HDec.QMSplit.Moduli.ElkiesPrint

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

/-! ## 1. The leaf and the discharge -/

/-- **The witness of the moduli clause lists for `X₀(6,1)` on abelian schemes** (not a leaf). A fine `Y₃` with
`R1fpPropsAb` and a coarse `X₆` with `X6Props` exist. It follows from the field `gonzalezRotgerX6Ab`
(`x6WitnessAb_of_gonzalezRotgerX6Ab`). Its body is that of `GRDict.X6ModuliWitness` (task gr-dict / grx6ab-print). -/
def X6WitnessAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY

/-- **LEAF (Elkies, *Shimura curve computations*, Algorithmic Number Theory (ANTS-III, Portland 1998), LNCS 1423,
pp. 1–47, §3 on `X*(6) = X(6)/W`; section number, display and the `0/∞` orientation UNVERIFIED, recalled without
a source), on every witness of the moduli description of `X₀(6,1)`, without the existence of the model.**

*Printed statement* (as recalled; UNVERIFIED): `t` is a coordinate on the genus-0 curve `X*(6) = X(6)/W`,
`W = {1, w₂, w₃, w₆}`, with the CM points of discriminants `−24, −4, −3` at `t = 0, 1, ∞`, and
`X(6)` is the curve `X*(6)(√−t, √(3(t − 1)))` over the `t`-line.

*Lean form*: let `(Y, Φ, X, Ψ, fY)` be any witness of the moduli description on abelian schemes (`R1fpPropsAb`:
the fine `Y₃`; `X6Props`: `X` proper and smooth of relative dimension one over `ℚ`, `Ψ : X(ℚ̄) ≃` QM pairs over
`ℚ̄` up to isomorphism, Galois-equivariant, with the twists induced by automorphisms, `fY` the forgetful map). Then
some `t : X → P¹` satisfies:
* **`t` is a coordinate on `X₆/W`**, in function fields: whenever `X` is integral and `t` is regular at its
  generic point (both follow from the charts, `ElkiesCoord.isIntegral_of_charts` and
  `ElkiesCoord.genericPoint_mem_of_charts`), the functions fixed by `W` (`ElkiesCoord.fixedByW`, with `W` given by
  its moduli action `ElkiesX6Star.atkinLehnerW`) are `ℚ(t)`;
* **the CM values** `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`;
* **the equations**: Elkies' two charts `X6Glue.ElkiesCharts X t`.

*Why the printed form, and not stronger*: the clauses are those of `ElkiesX6StarFunctionField` (elkies-coord's
function-field reading of the print). The existential over the witness is replaced by a universal, so the leaf
asserts nothing about the existence of the model. Compared with the old field it adds the transport to every
witness, and that is proved in Lean (`every_of_functionField`: any two witnesses have compatibly isomorphic coarse
curves, given T5). What it shares with every `X₆` leaf of the project: `X(6)`, its `W` and its CM points are read
through the moduli interpretation of the Shimura curve (Shimura 1967; Rotger 2004 for `w_m`; locators UNVERIFIED). -/
def ElkiesX6StarEvery : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∃ t : ToP1 X.left,
      (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
        ElkiesCoord.fixedByW Ψ =
          (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
      (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
      X6Glue.ElkiesCharts X t

theorem x6WitnessAb_of_gonzalezRotgerX6Ab (h : GonzalezRotgerX6Ab) : X6WitnessAb := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

theorem elkiesX6StarFunctionField_of_every (h : ElkiesX6StarEvery) (hW : X6WitnessAb) :
    ElkiesCoord.ElkiesX6StarFunctionField := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6⟩ := hW
  obtain ⟨t, hff, hcm, hc⟩ := h Y Φ X Ψ fY h1 h6
  exact ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hff, hcm, hc⟩

theorem elkiesX6StarFunctionField_of_every_gr (h : ElkiesX6StarEvery) (hX : GonzalezRotgerX6Ab) :
    ElkiesCoord.ElkiesX6StarFunctionField :=
  elkiesX6StarFunctionField_of_every h (x6WitnessAb_of_gonzalezRotgerX6Ab hX)

/-! ## 2. Comorphisms on function fields -/

section FFMap

theorem gen_spec {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (h : X ⟶ Z) [IsOpenImmersion h] :
    h (genericPoint X) ⤳ genericPoint Z := by
  rw [genericPoint_eq_of_isOpenImmersion h]

/-- The comorphism `h^* : ℚ(Z) → ℚ(X)` of an open immersion of integral schemes. -/
noncomputable def ffMap {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (h : X ⟶ Z) [IsOpenImmersion h] :
    Z.functionField →+* X.functionField :=
  (Z.presheaf.stalkSpecializes (gen_spec h) ≫ h.stalkMap (genericPoint X)).hom

theorem ffMap_germ {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (h : X ⟶ Z) [IsOpenImmersion h]
    (A : Z.Opens) (hA : genericPoint Z ∈ A) (hA' : genericPoint X ∈ h ⁻¹ᵁ A) (s : Γ(Z, A)) :
    ffMap h (Z.presheaf.germ A _ hA s) = X.presheaf.germ (h ⁻¹ᵁ A) _ hA' (h.app A s) := by
  unfold ffMap
  rw [CommRingCat.comp_apply, ← ConcreteCategory.comp_apply (Z.presheaf.germ A _ hA),
    TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap_apply]

theorem ffMap_ext {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] {φ ψ : Z.functionField →+* X.functionField}
    (H : ∀ (A : Z.Opens) (hA : genericPoint Z ∈ A) (s : Γ(Z, A)),
      φ (Z.presheaf.germ A _ hA s) = ψ (Z.presheaf.germ A _ hA s)) : φ = ψ := by
  ext a
  obtain ⟨A, hA, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Z.presheaf a
  exact H A hA s

theorem ffMap_comp {X Z W : Scheme.{0}} [IsIntegral X] [IsIntegral Z] [IsIntegral W]
    (h : X ⟶ Z) (g : Z ⟶ W) [IsOpenImmersion h] [IsOpenImmersion g] :
    ffMap (h ≫ g) = (ffMap h).comp (ffMap g) := by
  apply ffMap_ext
  intro A hA s
  have hA1 : genericPoint Z ∈ g ⁻¹ᵁ A := by
    show g (genericPoint Z) ∈ A
    rw [genericPoint_eq_of_isOpenImmersion g]; exact hA
  have hA2 : genericPoint X ∈ h ⁻¹ᵁ (g ⁻¹ᵁ A) := by
    show h (genericPoint X) ∈ g ⁻¹ᵁ A
    rw [genericPoint_eq_of_isOpenImmersion h]; exact hA1
  rw [RingHom.comp_apply, ffMap_germ g A hA hA1, ffMap_germ h _ hA1 hA2, ffMap_germ (h ≫ g) A hA hA2]
  rw [Scheme.Hom.comp_app]
  rfl

theorem ffMap_id {X : Scheme.{0}} [IsIntegral X] : ffMap (𝟙 X) = RingHom.id _ := by
  apply ffMap_ext
  intro A hA s
  rw [ffMap_germ (𝟙 X) A hA hA]
  rfl

theorem ffMap_congr {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] {h h' : X ⟶ Z} [IsOpenImmersion h]
    [IsOpenImmersion h'] (e : h = h') : ffMap h = ffMap h' := by
  subst e; rfl

end FFMap

/-! ## 3. Transport of Elkies' clauses along an isomorphism of coarse witnesses -/

section Transport

open X6Glue

instance isOpenImmersion_hom_left {A B : Over (Spec (CommRingCat.of ℚ))} (f : A ≅ B) :
    IsOpenImmersion f.hom.left := by
  have : IsIso f.hom.left := (inferInstance : IsIso ((Over.forget _).map f.hom))
  infer_instance

instance isOpenImmersion_inv_left {A B : Over (Spec (CommRingCat.of ℚ))} (f : A ≅ B) :
    IsOpenImmersion f.inv.left := by
  have : IsIso f.inv.left := (inferInstance : IsIso ((Over.forget _).map f.inv))
  infer_instance

variable {X X₀ : Over (Spec (CommRingCat.of ℚ))}
  {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
  {Ψ₀ : (fieldPt Qbar ⟶ X₀) ≃ Quotient (pairSetoid Qbar)}

theorem isAtkinLehner_conj (k : X ≅ X₀) (hk : ∀ x : fieldPt Qbar ⟶ X, Ψ₀ (x ≫ k.hom) = Ψ x)
    {j : Fin 4} {g : X ≅ X} (hg : ElkiesX6Star.IsAtkinLehner X Ψ j g) :
    ElkiesX6Star.IsAtkinLehner X₀ Ψ₀ j (k.symm ≪≫ g ≪≫ k) := by
  intro x₀ P hP
  have hx : Ψ (x₀ ≫ k.inv) = Quotient.mk _ P := by
    rw [← hk, Category.assoc, k.inv_hom_id, Category.comp_id]; exact hP
  have := hg (x₀ ≫ k.inv) P hx
  rw [← hk] at this
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using this

theorem isAtkinLehner_conj' (k : X ≅ X₀) (hk : ∀ x : fieldPt Qbar ⟶ X, Ψ₀ (x ≫ k.hom) = Ψ x)
    {j : Fin 4} {g₀ : X₀ ≅ X₀} (hg : ElkiesX6Star.IsAtkinLehner X₀ Ψ₀ j g₀) :
    ElkiesX6Star.IsAtkinLehner X Ψ j (k ≪≫ g₀ ≪≫ k.symm) := by
  intro x P hP
  have := hg (x ≫ k.hom) P ((hk x).trans hP)
  rw [← hk]
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using this

theorem ffPullback_eq {Z : Over (Spec (CommRingCat.of ℚ))} [IsIntegral Z.left] (g : Z ≅ Z) :
    ElkiesCoord.ffPullback (Z := Z.left) ((Over.forget _).mapIso g) = ffMap g.hom.left := rfl

/-- `ℚ(X)^W` is the image of `ℚ(X₀)^W` under the comorphism of a compatible isomorphism `k : X ≅ X₀`. -/
theorem fixedByW_eq_image [IsIntegral X.left] [IsIntegral X₀.left] (k : X ≅ X₀)
    (hk : ∀ x : fieldPt Qbar ⟶ X, Ψ₀ (x ≫ k.hom) = Ψ x) :
    ElkiesCoord.fixedByW Ψ = ffMap k.hom.left '' ElkiesCoord.fixedByW Ψ₀ := by
  have e1 : k.hom.left ≫ k.inv.left = 𝟙 _ := by rw [← Over.comp_left, k.hom_inv_id]; rfl
  have e2 : k.inv.left ≫ k.hom.left = 𝟙 _ := by rw [← Over.comp_left, k.inv_hom_id]; rfl
  have hκκ' : ∀ a, ffMap k.hom.left (ffMap k.inv.left a) = a := by
    intro a
    rw [← RingHom.comp_apply, ← ffMap_comp, ffMap_congr e1, ffMap_id]; rfl
  ext φ
  constructor
  · intro hφ
    refine ⟨ffMap k.inv.left φ, ?_, hκκ' φ⟩
    rintro g₀ ⟨j, hj⟩
    have hφg : ffMap (k ≪≫ g₀ ≪≫ k.symm).hom.left φ = φ := hφ (k ≪≫ g₀ ≪≫ k.symm) ⟨j, isAtkinLehner_conj' k hk hj⟩
    show ffMap g₀.hom.left (ffMap k.inv.left φ) = ffMap k.inv.left φ
    have m : k.inv.left ≫ (k ≪≫ g₀ ≪≫ k.symm).hom.left = g₀.hom.left ≫ k.inv.left := by
      change k.inv.left ≫ k.hom.left ≫ g₀.hom.left ≫ k.inv.left = _
      rw [reassoc_of% e2]
    calc ffMap g₀.hom.left (ffMap k.inv.left φ) = ffMap (g₀.hom.left ≫ k.inv.left) φ := by
          rw [ffMap_comp]; rfl
      _ = ffMap (k.inv.left ≫ (k ≪≫ g₀ ≪≫ k.symm).hom.left) φ := by rw [ffMap_congr m]
      _ = ffMap k.inv.left φ := by rw [ffMap_comp, RingHom.comp_apply, hφg]
  · rintro ⟨ψ, hψ, rfl⟩ g ⟨j, hj⟩
    have hψg : ffMap (k.symm ≪≫ g ≪≫ k).hom.left ψ = ψ := hψ (k.symm ≪≫ g ≪≫ k) ⟨j, isAtkinLehner_conj k hk hj⟩
    show ffMap g.hom.left (ffMap k.hom.left ψ) = ffMap k.hom.left ψ
    have m : k.hom.left ≫ (k.symm ≪≫ g ≪≫ k).hom.left = g.hom.left ≫ k.hom.left := by
      change k.hom.left ≫ k.inv.left ≫ g.hom.left ≫ k.hom.left = _
      rw [reassoc_of% e1]
    calc ffMap g.hom.left (ffMap k.hom.left ψ) = ffMap (g.hom.left ≫ k.hom.left) ψ := by
          rw [ffMap_comp]; rfl
      _ = ffMap (k.hom.left ≫ (k.symm ≪≫ g ≪≫ k).hom.left) ψ := by rw [ffMap_congr m]
      _ = ffMap k.hom.left ψ := by rw [ffMap_comp, RingHom.comp_apply, hψg]

/-- The function-field clause transported along `k`. -/
theorem ff_transport (k : X ≅ X₀) (hk : ∀ x : fieldPt Qbar ⟶ X, Ψ₀ (x ≫ k.hom) = Ψ x) (t₀ : ToP1 X₀.left)
    (hff : ∀ (_ : IsIntegral X₀.left) (hη : genericPoint X₀.left ∈ t₀.U),
      ElkiesCoord.fixedByW Ψ₀ =
        (Subfield.closure {X₀.left.presheaf.germ t₀.U _ hη t₀.f} : Set X₀.left.functionField)) :
    ∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ (t₀.comp k.hom.left).U),
      ElkiesCoord.fixedByW Ψ =
        (Subfield.closure {X.left.presheaf.germ (t₀.comp k.hom.left).U _ hη (t₀.comp k.hom.left).f} :
          Set X.left.functionField) := by
  intro hI hη
  have : Nonempty X₀.left := ⟨k.hom.left (genericPoint X.left)⟩
  have : IsIntegral X₀.left := isIntegral_of_isOpenImmersion k.inv.left
  have hη₀ : genericPoint X₀.left ∈ t₀.U := by
    have : k.hom.left (genericPoint X.left) ∈ t₀.U := hη
    rwa [genericPoint_eq_of_isOpenImmersion] at this
  rw [fixedByW_eq_image k hk, hff _ hη₀]
  rw [← Subfield.coe_map, RingHom.map_field_closure, Set.image_singleton,
    ffMap_germ k.hom.left t₀.U hη₀ hη]
  rfl

/-- The CM clause transported along `k`. -/
theorem cm_transport (k : X ≅ X₀) (hk : ∀ x : fieldPt Qbar ⟶ X, Ψ₀ (x ≫ k.hom) = Ψ x) (t₀ : ToP1 X₀.left)
    (hcm : ∀ (x : fieldPt Qbar ⟶ X₀) (P : QMPair Qbar), Ψ₀ x = Quotient.mk _ P →
        (HasCM24 P.q → t₀.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t₀.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t₀.val (K := Qbar) x.left = OnePoint.infty)) :
    ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → (t₀.comp k.hom.left).val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → (t₀.comp k.hom.left).val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → (t₀.comp k.hom.left).val (K := Qbar) x.left = OnePoint.infty) := by
  intro x P hP
  have e : (t₀.comp k.hom.left).val (K := Qbar) x.left = t₀.val (K := Qbar) (x ≫ k.hom).left :=
    ToP1.val_comp_right (K := Qbar) t₀ k.hom.left x.left
  rw [e]
  exact hcm (x ≫ k.hom) P ((hk x).trans hP)

/-- Elkies' charts transported along `k`. -/
theorem charts_transport (k : X ≅ X₀) (t₀ : ToP1 X₀.left) (hc : X6Glue.ElkiesCharts X₀ t₀) :
    X6Glue.ElkiesCharts X (t₀.comp k.hom.left) := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, hg1, hg2⟩ := hc
  have : IsIso k.hom.left := (inferInstance : IsIso ((Over.forget _).map k.hom))
  set h := k.hom.left with hh
  have nL : ∀ a : Γ(X₀.left, t₀.U),
      h.app (t₀.U ⊓ t₀.V) (X₀.left.presheaf.map (homOfLE (inf_le_left : t₀.U ⊓ t₀.V ≤ t₀.U)).op a) =
        X.left.presheaf.map (homOfLE (inf_le_left : h ⁻¹ᵁ t₀.U ⊓ h ⁻¹ᵁ t₀.V ≤ h ⁻¹ᵁ t₀.U)).op
          (h.app t₀.U a) := by
    intro a
    have n := ConcreteCategory.congr_hom
      (h.naturality (homOfLE (inf_le_left : t₀.U ⊓ t₀.V ≤ t₀.U)).op) a
    simp only [ConcreteCategory.comp_apply] at n
    exact n
  have nR : ∀ a : Γ(X₀.left, t₀.V),
      h.app (t₀.U ⊓ t₀.V) (X₀.left.presheaf.map (homOfLE (inf_le_right : t₀.U ⊓ t₀.V ≤ t₀.V)).op a) =
        X.left.presheaf.map (homOfLE (inf_le_right : h ⁻¹ᵁ t₀.U ⊓ h ⁻¹ᵁ t₀.V ≤ h ⁻¹ᵁ t₀.V)).op
          (h.app t₀.V a) := by
    intro a
    have n := ConcreteCategory.congr_hom
      (h.naturality (homOfLE (inf_le_right : t₀.U ⊓ t₀.V ≤ t₀.V)).op) a
    simp only [ConcreteCategory.comp_apply] at n
    exact n
  refine ⟨hU.preimage_of_isIso h, hV.preimage_of_isIso h,
    φU.trans (asIso (h.app t₀.U)).commRingCatIsoToRingEquiv,
    φV.trans (asIso (h.app t₀.V)).commRingCatIsoToRingEquiv, ?_, ?_, ?_, ?_⟩
  · change h.app t₀.U (φU eT) = h.app t₀.U t₀.f
    rw [hT]
  · change h.app t₀.V (φV eT) = h.app t₀.V t₀.g
    rw [hTg]
  · change X.left.presheaf.map _ (h.app t₀.U (φU eS)) * X.left.presheaf.map _ (h.app t₀.V (φV eS)) = 1
    have e := congrArg (h.app (t₀.U ⊓ t₀.V)) hg1
    rw [map_mul, map_one, nL, nR] at e
    exact e
  · change X.left.presheaf.map _ (h.app t₀.U (φU eR)) * X.left.presheaf.map _ (h.app t₀.V (φV eS)) =
      X.left.presheaf.map _ (h.app t₀.V (φV eR))
    have e := congrArg (h.app (t₀.U ⊓ t₀.V)) hg2
    rw [map_mul, nL, nR, nR] at e
    exact e

end Transport

/-! ## 4. Pinning: any two witnesses have compatibly isomorphic coarse curves -/

section Pin

open LeafQM.AV.R1UnivRigid

/-- `phi_part` (Pin.lean) for the abelian-scheme clauses. -/
theorem phi_part_ab {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univAbProps Y Φ) (h1' : R1fpPropsAb Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, -, ⟨𝒜', h𝒜'⟩, -⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜'.toQMFamily s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

/-- `compare_iso` (TailU) for the abelian-scheme clauses: two fine witnesses are compatibly isomorphic. -/
theorem compare_iso_ab {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (h : R1fpPropsAb Y Φ) (h' : R1fpPropsAb Y' Φ') :
    ∃ g : Y' ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g.hom) := by
  obtain ⟨g, hg⟩ := phi_part_ab h.2.2.2.2.2 h'
  obtain ⟨g', hg'⟩ := phi_part_ab h'.2.2.2.2.2 h
  have e1 : g' ≫ g = 𝟙 Y := eq_id_of_fieldPts h.1 h.2.1 _ fun K _ _ y => (Φ K).injective (by
    rw [← Category.assoc, ← hg K (y ≫ g'), ← hg' K y])
  have e2 : g ≫ g' = 𝟙 Y' := eq_id_of_fieldPts h'.1 h'.2.1 _ fun K _ _ y => (Φ' K).injective (by
    rw [← Category.assoc, ← hg' K (y ≫ g), ← hg K y])
  exact ⟨⟨g, g', e2, e1⟩, hg⟩

/-- **Coarse comparison over one fine witness** (abelian-scheme clauses): the kernel's `coarseFactor_of` and
`coarseCompare_of`, with `PairsLift` from T5 (`pairsLift_of_T5`), `FactorThroughSurj` and `CurveBijIso` proved. -/
theorem coarse_compare_ab (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X X' : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {Ψ' : (fieldPt Qbar ⟶ X') ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X} {fY' : Y ⟶ X'}
    (h1 : R1fpPropsAb Y Φ) (h6 : X6Props Y Φ X Ψ fY) (h6' : X6Props Y Φ X' Ψ' fY') :
    ∃ g : X ≅ X', ∀ x : fieldPt Qbar ⟶ X, Ψ' (x ≫ g.hom) = Ψ x := by
  have hL := _root_.ShimuraSplit.pairsLift_of_T5 hT
  have hval : ∀ y : fieldPt Qbar ⟶ Y, Ψ (y ≫ fY) = Ψ' (y ≫ fY') := by
    intro y
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ Qbar y)
    rw [h6.2.2.2.2.2 y P hP.symm, h6'.2.2.2.2.2 y P hP.symm]
  have hsurj : ∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x := by
    intro x
    obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Ψ x)
    obtain ⟨P, hP⟩ := hL Q
    obtain ⟨y, hy⟩ := (Φ Qbar).surjective (M3.mk P)
    refine ⟨y, Ψ.injective ?_⟩
    rw [h6.2.2.2.2.2 y P hy, hP, hQ]
  have hconst : ∀ y y' : fieldPt Qbar ⟶ Y, y ≫ fY = y' ≫ fY → y ≫ fY' = y' ≫ fY' := by
    intro y y' e
    apply Ψ'.injective
    rw [← hval, ← hval, e]
  obtain ⟨h, hh⟩ := _root_.CoarseFactorAG.factorThroughSurj Y X X' h1.1 h1.2.1 h6.1 h6.2.1 h6'.1 h6'.2.1
    fY fY' hsurj hconst
  have hcomp : ∀ x : fieldPt Qbar ⟶ X, Ψ' (x ≫ h) = Ψ x := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    rw [Category.assoc, hh, hval]
  have hbij : Function.Bijective (fun x : fieldPt Qbar ⟶ X => x ≫ h) := by
    have e : (fun x : fieldPt Qbar ⟶ X => x ≫ h) = Ψ'.symm ∘ Ψ := by
      funext x
      simp only [Function.comp]
      rw [← hcomp x, Equiv.symm_apply_apply]
    rw [e]; exact Ψ'.symm.bijective.comp Ψ.bijective
  have := HDec.HSyn.curveBijIso_lf7 X X' h6.1 h6.2.1 h6'.1 h6'.2.1 h hbij
  exact ⟨asIso h, hcomp⟩

end Pin

/-! ## 5. The new leaf is not stronger than the field it replaces -/

/-- **`ElkiesX6StarFunctionField` and T5 give `ElkiesX6StarEvery`**: Elkies' clauses on the witness of the field
transport to every witness (`compare_iso_ab`, `x6Props_transport`, `coarse_compare_ab`, and the transport lemmas of
§3). So the every-witness form asserts no more than the field, given T5 (a theorem of the build from the textbook
field `mumfordTorsionAlgClosed`). -/
theorem every_of_functionField (h : ElkiesCoord.ElkiesX6StarFunctionField) (hT : ObjBridge.TorsionStructure) :
    ElkiesX6StarEvery := by
  intro Y Φ X Ψ fY h1 h6
  obtain ⟨Y₀, Φ₀, X₀, Ψ₀, fY₀, t₀, h1₀, h6₀, hff, hcm, hc⟩ := h
  obtain ⟨g, hg⟩ := compare_iso_ab h1₀ h1
  obtain ⟨k, hk⟩ := coarse_compare_ab hT h1 h6 (x6Props_transport g hg h6₀)
  exact ⟨t₀.comp k.hom.left, ff_transport k hk t₀ hff, cm_transport k hk t₀ hcm, charts_transport k t₀ hc⟩

/-- Given a witness and T5, the new leaf and the field are equivalent. -/
theorem every_iff_functionField (hW : X6WitnessAb) (hT : ObjBridge.TorsionStructure) :
    ElkiesX6StarEvery ↔ ElkiesCoord.ElkiesX6StarFunctionField :=
  ⟨fun h => elkiesX6StarFunctionField_of_every h hW, fun h => every_of_functionField h hT⟩

end HDec.QMSplit.Moduli.ElkiesPrint
