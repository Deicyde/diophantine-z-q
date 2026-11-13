
/-! ### qm-pin's comparison: the three QM pieces reduce to one triple (task pin-apply)

`FibreSimple`, `ThetaPointOfFibre` and `ModularConstituent` quantify over every triple
`(Y, Φ, π)` satisfying `R1fpProps` and `R2fpProps`. With qm-pin's repaired `R1fpProps`
(`R1famProps`, `R1univProps`), any two such triples are compared by a morphism `g : Y' → Y` with
`Φ' = Φ ∘ g` (`LeafQM.AV.Pin.phi_part`, proved) and `π' = π ∘ g` (`LeafQM.AV.Pin.MobiusGlue`, a
named glue Prop). So each piece is equivalent to its statement for any single triple satisfying the
clauses (`fibreSimple_iff_at` etc.), for instance the leaf's own triple; the `…W` forms state the
piece for some triple. The relabeling attack of rv-g0pieces no longer applies
(`LeafQM.AV.Pin.r1fpPin_relabel_iff`). -/

/-- `FibreSimple` for one triple `(Y, Φ, π)`. -/
def FibreSimpleAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) :
    Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K.K A)

/-- `ThetaPointOfFibre` for one triple `(Y, Φ, π)`. -/
def ThetaPointOfFibreAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts (LeafAdopt.abVarEquiv K.K A) σ), ZInQ.LeafPush2.IsUniformization σ Λ Φu ∧
    ∃ Ω : Matrix (Fin 2) (Fin 2) ℂ, ZInQ.LeafPush2.IsSiegel Ω ∧ ZInQ.LeafPush2.IsPeriodMatrix Λ Ω ∧
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : ZInQ.LeafPush2.Char2 → L.K) (c : ℂ), c ≠ 0 ∧
      (∀ m, emb (z m) = c * ZInQ.LeafPush2.thetaConst Ω m) ∧
    ∃ (K' : GlueAssembly.NF) (z' : Fin 10 → K'.K),
      3779136 * (∏ i, z' i) ^ 4 / (∑ i, z' i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
      Height.logHeight z' / Module.finrank ℚ K'.K ≤ ZInQ.LeafPush2.absLogHeight z

/-- `ModularConstituent` for one triple `(Y, Φ, π)`. -/
def ModularConstituentAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : ZInQ.DefFaltings.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent (LeafAdopt.abVarEquiv L.K A)
        (LeafAdopt.abVarEquiv L.K (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K))

/-- The three pieces are their `…At` forms for every triple satisfying the clauses (definitional). -/
theorem fibreSimple_eq_forall_at : FibreSimple ↔ ∀ (Y : Over (Spec (CommRingCat.of ℚ)))
    (Φ : PtEquiv Y) (π : ToP1 Y.left), R1fpProps Y Φ → R2fpProps Y Φ π → FibreSimpleAt Y Φ π :=
  Iff.rfl

theorem thetaPointOfFibre_eq_forall_at : ThetaPointOfFibre ↔
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → ThetaPointOfFibreAt Y Φ π :=
  Iff.rfl

theorem modularConstituent_eq_forall_at : ModularConstituent ↔
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → ModularConstituentAt Y Φ π :=
  Iff.rfl

/-- `FibreOver` (an `∃`-form) transfers along a comparison morphism (qm-pin `transfer_exists`,
for `SameTripleMor`). -/
theorem fibreOver_of_sameTripleMor {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : LeafQM.AV.Pin.SameTripleMor Y Y' Φ Φ' π π') {u : ℚ} {K : GlueAssembly.NF}
    {A : ZInQ.DefFaltings.AbVar K.K} (h : FibreOver Y' Φ' π' u K A) : FibreOver Y Φ π u K A := by
  obtain ⟨g, hΦ, hπ⟩ := hS
  obtain ⟨emb, y, P, hP, hy, hiso⟩ := h
  exact ⟨emb, y ≫ g, P, (hΦ Qbar y).symm.trans hP, (hπ y).symm.trans hy, hiso⟩

/-- **The comparison from the leaves** (qm-pin `sameTripleMor_of_mobius`, CM objects from
`cm_objects_of_R1R2fp`): any two triples satisfying the repaired clause lists are compared by a
morphism, given `MobiusGlue`. -/
theorem sameTripleMor_of_leaves (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (h1' : R1fpProps Y' Φ')
    (h2' : R2fpProps Y' Φ' π') : LeafQM.AV.Pin.SameTripleMor Y Y' Φ Φ' π π' :=
  LeafQM.AV.Pin.sameTripleMor_of_mobius hM (LeafQM.AV.Pin.cm_objects_of_R1R2fp hQM) h1 h2 h1' h2'

theorem fibreSimple_of_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) (h : FibreSimpleAt Y₀ Φ₀ π₀) :
    FibreSimple :=
  fun _ _ _ h1' h2' u hu K A hF =>
    h u hu K A (fibreOver_of_sameTripleMor (sameTripleMor_of_leaves hM hQM h1 h2 h1' h2') hF)

theorem thetaPointOfFibre_of_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) (h : ThetaPointOfFibreAt Y₀ Φ₀ π₀) :
    ThetaPointOfFibre :=
  fun _ _ _ h1' h2' u hu K A hF =>
    h u hu K A (fibreOver_of_sameTripleMor (sameTripleMor_of_leaves hM hQM h1 h2 h1' h2') hF)

theorem modularConstituent_of_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) (h : ModularConstituentAt Y₀ Φ₀ π₀) :
    ModularConstituent := by
  intro Y Φ π h1' h2' u hu y P hP hy
  obtain ⟨g, hΦ, hπ⟩ := sameTripleMor_of_leaves hM hQM h1 h2 h1' h2'
  exact h u hu (y ≫ g) P ((hΦ Qbar y).symm.trans hP) ((hπ y).symm.trans hy)

/-- **`FibreSimple` is its statement for any one triple** satisfying the repaired clauses (given
`MobiusGlue`): the universal quantifier over `(Y, Φ, π)` costs nothing. -/
theorem fibreSimple_iff_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) :
    FibreSimple ↔ FibreSimpleAt Y₀ Φ₀ π₀ :=
  ⟨fun h => h Y₀ Φ₀ π₀ h1 h2, fibreSimple_of_at hM hQM h1 h2⟩

theorem thetaPointOfFibre_iff_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) :
    ThetaPointOfFibre ↔ ThetaPointOfFibreAt Y₀ Φ₀ π₀ :=
  ⟨fun h => h Y₀ Φ₀ π₀ h1 h2, thetaPointOfFibre_of_at hM hQM h1 h2⟩

theorem modularConstituent_iff_at (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) :
    ModularConstituent ↔ ModularConstituentAt Y₀ Φ₀ π₀ :=
  ⟨fun h => h Y₀ Φ₀ π₀ h1 h2, modularConstituent_of_at hM hQM h1 h2⟩

/-- `FibreSimple` for some triple satisfying the clauses. -/
def FibreSimpleW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ FibreSimpleAt Y Φ π

/-- `ThetaPointOfFibre` for some triple satisfying the clauses. -/
def ThetaPointOfFibreW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ ThetaPointOfFibreAt Y Φ π

/-- `ModularConstituent` for some triple satisfying the clauses. -/
def ModularConstituentW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ ModularConstituentAt Y Φ π

/-- **The three QM pieces are equivalent to their one-triple forms** (given the QM leaf bundle,
which supplies a triple, and `MobiusGlue`). -/
theorem qmPieces_iff_w (hM : LeafQM.AV.Pin.MobiusGlue) (hQM : LeafQM.AV.R1R2fp) :
    (FibreSimple ↔ FibreSimpleW) ∧ (ThetaPointOfFibre ↔ ThetaPointOfFibreW) ∧
      (ModularConstituent ↔ ModularConstituentW) := by
  obtain ⟨Y, Φ, π, h1, h2, -⟩ := LeafQM.AV.exists_fibre_object hQM
  refine ⟨⟨fun h => ⟨Y, Φ, π, h1, h2, h Y Φ π h1 h2⟩, ?_⟩,
    ⟨fun h => ⟨Y, Φ, π, h1, h2, h Y Φ π h1 h2⟩, ?_⟩,
    ⟨fun h => ⟨Y, Φ, π, h1, h2, h Y Φ π h1 h2⟩, ?_⟩⟩
  · rintro ⟨Y₀, Φ₀, π₀, h1₀, h2₀, h⟩; exact fibreSimple_of_at hM hQM h1₀ h2₀ h
  · rintro ⟨Y₀, Φ₀, π₀, h1₀, h2₀, h⟩; exact thetaPointOfFibre_of_at hM hQM h1₀ h2₀ h
  · rintro ⟨Y₀, Φ₀, π₀, h1₀, h2₀, h⟩; exact modularConstituent_of_at hM hQM h1₀ h2₀ h

