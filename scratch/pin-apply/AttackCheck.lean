import ZInQKernel.HDecomp.QM.Pin

/-! pin-apply, step 4: rv-g0pieces' relabeling attack against the repaired clauses.

The clause block `QMFamily … R1fpProps` and the `Pin` block are textually identical in
`ZInQKernel/HDecomp/QM/{Leaves,Pin}.lean` and `scratch/h-decomposition/Leaves.lean`
(checked by `scratch/pin-apply/check_identical.py`), so this check, run against the kernel modules,
applies to the clauses in `Leaves.lean`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace LeafQM.AV.Pin

/-- **(1) rv-g0pieces' proof of `r1fp_relabel`, verbatim (`scratch/rv-g0pieces/Exotic.lean`), no
longer proves the statement** for the repaired `R1fpProps`: `fail_if_success` succeeds. -/
example {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)}
    (h : R1fpProps Y Φ) (hτ : IsNaturalRelabel Y τ) : True := by
  fail_if_success
    have _h' : R1fpProps Y (relabel Φ τ) := by
      obtain ⟨hp, hs, hpt, hnat⟩ := h
      refine ⟨hp, hs, hpt, ?_⟩
      intro K L _ _ _ _ f y P hP
      obtain ⟨Q, hQ, hb⟩ := hnat K L f (τ K y) P hP
      refine ⟨Q, ?_, hb⟩
      show Φ L (τ L (fieldMap f ≫ y)) = _
      rw [hτ K L f y]
      exact hQ
  trivial

/-- **(2) The old proof still proves the old (naturality) part**: what the attack keeps. -/
theorem relabel_keeps_old_part {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)}
    (h : R1fpProps Y Φ) (hτ : IsNaturalRelabel Y τ) :
    IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
    (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
      (y : fieldPt K ⟶ Y) (P : QML3 K), relabel Φ τ K y = M3.mk P →
        ∃ Q : QML3 L, relabel Φ τ L (fieldMap f ≫ y) = M3.mk Q ∧
          IsBaseChangeOf (f : K →+* L) P Q) := by
  obtain ⟨hp, hs, hpt, hnat, -, -⟩ := h
  refine ⟨hp, hs, hpt, ?_⟩
  intro K L _ _ _ _ f y P hP
  obtain ⟨Q, hQ, hb⟩ := hnat K L f (τ K y) P hP
  refine ⟨Q, ?_, hb⟩
  show Φ L (τ L (fieldMap f ≫ y)) = _
  rw [hτ K L f y]
  exact hQ

/-- **(3) What a relabeling must supply now** (`r1fpPin_relabel_iff`, restated): the relabeled
triple satisfies the repaired list iff a `QMFamily` over `Y` has the class of `τ y` as its fibre at
every field point `y`, and the relabeled `Φ` classifies families. For rv-g0pieces' `relabelPt`
(a non-continuous point bijection) the first condition asks for a family whose fibres are moved
off their points, which a scheme over `Y` cannot do unless `τ` is geometric (qm-pin §3.3-3.4;
argued, not compiled: that needs R1(a)'s universal property). -/
theorem attack_needs_family {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)}
    (h : R1fpProps Y Φ) (hτ : IsNaturalRelabel Y τ) (h' : R1fpProps Y (relabel Φ τ)) :
    ∃ 𝒜' : QMFamily Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y)
      (P : QML3 K), Φ K (τ K y) = M3.mk P → IsFibreOf 𝒜' y.left P :=
  ((r1fpPin_relabel_iff h hτ).mp h').1

-- (4) `relabel_is_morphism` is now in `ZInQKernel/HDecomp/QM/Pin.lean` (and the Pin block of
-- `scratch/h-decomposition/Leaves.lean`).

/-! ### (5) rv-g0pieces' exotic relabeling is refuted (compiled)

rv-g0pieces' `relabelPt`/`relabelOver` (copied verbatim from `scratch/rv-g0pieces/Exotic.lean`):
for any bijection `s` of the points of `Y` with residue-field isomorphisms `φ`, the relabeled
`Φ` satisfied the old `R1fpProps` (`r1fp_exotic`). Against the repaired clauses, the relabeled
triple satisfies `R1fpProps` only if `s` is the map on points of a morphism `g : Y → Y`, hence
continuous. So the attack's non-continuous `s` (swapping two closed points) is excluded. -/

namespace Exotic


/-- Any two morphisms `Spec K ⟶ Spec ℚ` agree (`ℚ` is initial among fields of char. 0). -/
theorem spec_to_specQ_eq {K : Type} [Field K]
    (g h : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h]
  congr 1
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

variable {X : Scheme.{0}} (s : X ≃ X) (φ : ∀ x, X.residueField (s x) ≅ X.residueField x)

/-- The relabeled field point: `(x, ι) ↦ (s x, φ x ≫ ι)`. -/
noncomputable def relabelPt (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) :
    Spec (CommRingCat.of K) ⟶ X :=
  (Scheme.SpecToEquivOfField K X).symm
    ⟨s (Scheme.SpecToEquivOfField K X y).1, (φ _).hom ≫ (Scheme.SpecToEquivOfField K X y).2⟩

theorem relabelPt_symm (K : Type) [Field K] (p : Σ x, X.residueField x ⟶ CommRingCat.of K) :
    relabelPt s φ K ((Scheme.SpecToEquivOfField K X).symm p) =
      (Scheme.SpecToEquivOfField K X).symm ⟨s p.1, (φ p.1).hom ≫ p.2⟩ := by
  unfold relabelPt
  rw [Equiv.apply_symm_apply]

theorem relabelPt_bijective (K : Type) [Field K] : Function.Bijective (relabelPt s φ K) := by
  constructor
  · intro y₁ y₂ h
    obtain ⟨⟨x₁, ι₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y₁
    obtain ⟨⟨x₂, ι₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y₂
    rw [relabelPt_symm, relabelPt_symm] at h
    have h' := (Scheme.SpecToEquivOfField K X).symm.injective h
    simp only [Sigma.mk.inj_iff] at h'
    obtain ⟨hx, hι⟩ := h'
    have hx' : x₁ = x₂ := s.injective hx
    subst hx'
    have hι' := eq_of_heq hι
    have : ι₁ = ι₂ := (cancel_epi (φ x₁).hom).mp hι'
    rw [this]
  · intro y
    obtain ⟨⟨x', ι'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
    obtain ⟨x, rfl⟩ := s.surjective x'
    refine ⟨(Scheme.SpecToEquivOfField K X).symm ⟨x, (φ x).inv ≫ ι'⟩, ?_⟩
    rw [relabelPt_symm]
    simp

/-- Naturality: `τ(y ∘ Spec f) = τ(y) ∘ Spec f`. -/
theorem relabelPt_comp {K L : Type} [Field K] [Field L] (f : K →+* L)
    (y : Spec (CommRingCat.of K) ⟶ X) :
    relabelPt s φ L (Spec.map (CommRingCat.ofHom f) ≫ y) =
      Spec.map (CommRingCat.ofHom f) ≫ relabelPt s φ K y := by
  apply (Scheme.SpecToEquivOfField L X).injective
  have h1 : Scheme.SpecToEquivOfField K X (relabelPt s φ K y) =
      ⟨s (Scheme.SpecToEquivOfField K X y).1,
        (φ _).hom ≫ (Scheme.SpecToEquivOfField K X y).2⟩ := by
    unfold relabelPt; rw [Equiv.apply_symm_apply]
  rw [specToEquivOfField_comp f (relabelPt s φ K y), h1]
  unfold relabelPt
  rw [Equiv.apply_symm_apply, specToEquivOfField_comp f y]
  simp only [Category.assoc]

/-- The point of `τ(y)` is `s` of the point of `y`: the relabeling moves points as `s` does. -/
theorem relabelPt_point (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) :
    (Scheme.SpecToEquivOfField K X (relabelPt s φ K y)).1 =
      s (Scheme.SpecToEquivOfField K X y).1 := by
  unfold relabelPt; rw [Equiv.apply_symm_apply]

/-- The relabeling on field points of `Y` over `ℚ`. -/
noncomputable def relabelOver (Y : Over (Spec (CommRingCat.of ℚ))) (s : Y.left ≃ Y.left)
    (φ : ∀ x, Y.left.residueField (s x) ≅ Y.left.residueField x)
    (K : Type) [Field K] [Algebra ℚ K] : (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y) :=
  Equiv.ofBijective
    (fun y => Over.homMk (relabelPt s φ K y.left) (spec_to_specQ_eq _ _))
    (by
      constructor
      · intro y₁ y₂ h
        have h' := congrArg (fun g : fieldPt K ⟶ Y => g.left) h
        exact Over.OverMorphism.ext ((relabelPt_bijective s φ K).1 h')
      · intro y
        obtain ⟨z, hz⟩ := (relabelPt_bijective s φ K).2 y.left
        exact ⟨Over.homMk z (spec_to_specQ_eq _ _), Over.OverMorphism.ext hz⟩)

theorem relabelOver_natural (Y : Over (Spec (CommRingCat.of ℚ))) (s : Y.left ≃ Y.left)
    (φ : ∀ x, Y.left.residueField (s x) ≅ Y.left.residueField x) :
    IsNaturalRelabel Y (relabelOver Y s φ) := by
  intro K L _ _ _ _ f y
  apply Over.OverMorphism.ext
  exact relabelPt_comp s φ (f : K →+* L) y.left

/-- **The exotic relabeling survives only if `s` is a morphism on points.** -/
theorem exotic_relabel_morphism {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) (s : Y.left ≃ Y.left)
    (φ : ∀ x, Y.left.residueField (s x) ≅ Y.left.residueField x)
    (h' : R1fpProps Y (relabel Φ (relabelOver Y s φ))) :
    ∃ g : Y ⟶ Y, ∀ x, s x = g.left x := by
  obtain ⟨g, hg⟩ := relabel_is_morphism h h'
  refine ⟨g, fun x => ?_⟩
  let _ : Algebra ℚ (Y.left.residueField x) :=
    (Spec.preimage (Y.left.fromSpecResidueField x ≫ Y.hom)).hom.toAlgebra
  let y0 : Spec (CommRingCat.of (Y.left.residueField x)) ⟶ Y.left :=
    (Scheme.SpecToEquivOfField (Y.left.residueField x) Y.left).symm
      ⟨x, CommRingCat.ofHom (RingHom.id _)⟩
  let y : fieldPt (Y.left.residueField x) ⟶ Y := Over.homMk y0 (spec_to_specQ_eq _ _)
  have e := congrArg
    (fun z : fieldPt (Y.left.residueField x) ⟶ Y =>
      (Scheme.SpecToEquivOfField (Y.left.residueField x) Y.left z.left).1) (hg _ y)
  have e1 : (relabelOver Y s φ (Y.left.residueField x) y).left =
      relabelPt s φ (Y.left.residueField x) y0 := rfl
  have e2 : (y ≫ g).left = y0 ≫ g.left := rfl
  simp only [e1, e2] at e
  rw [relabelPt_point, specToEquivOfField_comp_right] at e
  have hx : (Scheme.SpecToEquivOfField (Y.left.residueField x) Y.left y0).1 = x :=
    congrArg Sigma.fst (Equiv.apply_symm_apply _ _)
  have e' : s (Scheme.SpecToEquivOfField (Y.left.residueField x) Y.left y0).1 =
      g.left (Scheme.SpecToEquivOfField (Y.left.residueField x) Y.left y0).1 := e
  rw [hx] at e'
  exact e'

/-- **Corollary: a non-continuous point bijection gives no triple satisfying the repaired
`R1fpProps`.** -/
theorem not_r1fp_exotic {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) (s : Y.left ≃ Y.left)
    (φ : ∀ x, Y.left.residueField (s x) ≅ Y.left.residueField x)
    (hs : ¬ Continuous s) : ¬ R1fpProps Y (relabel Φ (relabelOver Y s φ)) := by
  intro h'
  obtain ⟨g, hg⟩ := exotic_relabel_morphism h s φ h'
  have : (s : Y.left → Y.left) = fun x => g.left x := funext hg
  exact hs (this ▸ g.left.base.hom.continuous)

end Exotic

end LeafQM.AV.Pin

#print axioms LeafQM.AV.Pin.relabel_keeps_old_part
#print axioms LeafQM.AV.Pin.attack_needs_family

#print axioms LeafQM.AV.Pin.Exotic.exotic_relabel_morphism
#print axioms LeafQM.AV.Pin.Exotic.not_r1fp_exotic
