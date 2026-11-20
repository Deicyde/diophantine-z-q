import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.AbelianVariety.RationalCurves
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.LocalSections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Geometrically.Smooth
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.Finite
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Limits.Shapes.Pullback.Map
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.FiniteSet
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.Pullback
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Descent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Limits.FieldExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Limits.BaseChange
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # chevalley-free: `SemiAbelianDescendsPerfect` without Chevalley's theorem

The research field `chevalleyPerfect` (`ZInQ.SemiAbDescend.ChevalleyPerfect`, Chevalley's structure theorem over a
perfect field, semiab-descend) was used only through `semiAbelianDescendsPerfect_of_chevalley`, and there only for
the descent of a semi-abelian presentation `π' : (G⁰)_{k̄} → B'` (kernel a split torus) to `k`. This file proves
that descent outright, so `ZInQ.HeightFix.SemiAbelianDescendsPerfect` becomes a theorem
(`semiAbelianDescendsPerfect_proof`, standard axioms) and the field can be removed with no new leaf.

* **Descent** (`exists_descent`): for `q : S' → S` finite, flat, surjective, of finite presentation, an fpqc
  `π₁ : U_{S'} → X₁` whose fibres are stable under the transport of points of `U_{S'}` (`KI`), and finite sets of
  `X₁` in affine opens, `X₁` descends to `B₀` and `π₁` to `π : U → B₀`. The descent datum is
  `ψ : X₁ ×_S S' → X₁`, `(π₁(u, a), b) ↦ π₁(u, b)`, built by effective-epi descent; effectivity is the vendored
  `isEffective_of_isFinite` (CloudW07).
* **Rigidity** (`torus1_const`, `torusR_const`): a morphism from a split torus over any field `K` to an abelian
  variety over `K` is constant on `K`-points (the overlap `𝔾_m` of the vendored relative `ℙ¹`, the vendored
  valuative extension and `RationalCurves.eq_zero_comp`).
* **Transport condition** (`kbar_KI`, `algclosed_KI`, `field_KI`, `KI_of`): from rigidity, for a finite-stage model
  `(X₁, π₁, c)` of `(B', π')` over a finite subextension `k₁ ⊆ k̄` (field tests on a smooth universal source).
* **Group laws** (`exists_grpObj`, `cong_of_faithful`): a group structure through an fpqc quotient map, the
  congruence condition from a faithful monoidal base change.
* **Finite stage** (`spread`): `(B', π')` is defined over a finite subextension (vendored
  `exists_finiteSubext_isPullback`, Mathlib `exists_π_app_comp_eq_of_locallyOfFinitePresentation`).
* **Assembly** (`fsd`, `quotientDescendsPerfect_proof`, `semiAbelianDescendsPerfect_of_qd`): the last is
  semiab-descend's `semiAbelianDescendsPerfect_of_chevalley` with its step (e) replaced.

The lemmas `fieldMap_fpqc'`, `exists_commonField'`, `geometricallyIrreducible_of_field_pullback'`,
`isProper_of_field_pullback'`, `smooth_of_field_pullback'` are copies of private lemmas of the vendored
`ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Picard/FieldDescent.lean` (frenzymath/Jacobian-
Challenge, Apache-2.0, Axel Delaval, Jie Xu and Shitan Xu; see the LICENSE and NOTICE in that directory). -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry.ProjectiveLine AlgebraicGeometry.ProjectiveSpace ZInQ.SemiAbDescend
open DictModels.RaynaudOr ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ZInQ.ChevFree


section Descent

variable {S S' : Scheme.{0}} (q : S' ⟶ S) {U : Over S} {X₁ : Over S'}
  (π₁ : (Over.pullback q).obj U ⟶ X₁)

/-- `X₁ ×_S S'`. -/
abbrev PP := pullback (X₁.hom ≫ q) q

/-- `U_{S'} ×_S S'`. -/
abbrev YY := pullback (π₁.left ≫ X₁.hom ≫ q) q

/-- `π₁ × id : U_{S'} ×_S S' → X₁ ×_S S'`. -/
abbrev αα : YY q π₁ ⟶ PP q (X₁ := X₁) :=
  pullback.map (π₁.left ≫ X₁.hom ≫ q) q (X₁.hom ≫ q) q π₁.left (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem isPullback_αα :
    IsPullback (pullback.fst _ _) (αα q π₁) π₁.left (pullback.fst (X₁.hom ≫ q) q) :=
  isPullback_pullback_map_left π₁.left (X₁.hom ≫ q) q

theorem w_π₁ : π₁.left ≫ X₁.hom = pullback.snd U.hom q := Over.w π₁

/-- The `U`-coordinate of a point of `U_{S'} ×_S S'`. -/
abbrev uPart : YY q π₁ ⟶ U.left := pullback.fst _ _ ≫ pullback.fst U.hom q

theorem uPart_cond : uPart q π₁ ≫ U.hom = pullback.snd (π₁.left ≫ X₁.hom ≫ q) q ≫ q := by
  rw [Category.assoc, pullback.condition, ← w_π₁ q π₁, ← Category.assoc, ← Category.assoc]
  simp only [Category.assoc]
  exact pullback.condition

/-- `(u, a, b) ↦ π₁(u, b)`. -/
abbrev ββ : YY q π₁ ⟶ X₁.left :=
  pullback.lift (uPart q π₁) (pullback.snd _ _) (uPart_cond q π₁) ≫ π₁.left

/-- **The transport condition `KI`**: if `u, v` have the same image under `π₁` over `a`, they have the same image
over every `b` with the same image in `S`. -/
def KI : Prop :=
  ∀ (Z : Scheme.{0}) (u v : Z ⟶ U.left) (a b : Z ⟶ S') (hu : u ≫ U.hom = a ≫ q)
    (hv : v ≫ U.hom = a ≫ q) (hb : a ≫ q = b ≫ q),
    pullback.lift u a hu ≫ π₁.left = pullback.lift v a hv ≫ π₁.left →
    pullback.lift u b (hu.trans hb) ≫ π₁.left = pullback.lift v b (hv.trans hb) ≫ π₁.left

variable {q π₁}

theorem ββ_coeq (hKI : KI q π₁) {Z : Scheme.{0}} (g h : Z ⟶ YY q π₁)
    (hgh : g ≫ αα q π₁ = h ≫ αα q π₁) : g ≫ ββ q π₁ = h ≫ ββ q π₁ := by
  have h1 : g ≫ pullback.fst _ _ ≫ π₁.left = h ≫ pullback.fst _ _ ≫ π₁.left := by
    have := congrArg (· ≫ pullback.fst (X₁.hom ≫ q) q) hgh
    simpa only [Category.assoc, pullback.lift_fst] using this
  have h2 : g ≫ pullback.snd _ _ = h ≫ pullback.snd _ _ := by
    have := congrArg (· ≫ pullback.snd (X₁.hom ≫ q) q) hgh
    simpa only [Category.assoc, pullback.lift_snd, Category.comp_id] using this
  have h3 : g ≫ pullback.fst _ _ ≫ pullback.snd U.hom q = h ≫ pullback.fst _ _ ≫ pullback.snd U.hom q := by
    have := congrArg (· ≫ X₁.hom) h1
    simpa only [Category.assoc, w_π₁] using this
  set a := g ≫ pullback.fst _ _ ≫ pullback.snd U.hom q
  set b := g ≫ pullback.snd (π₁.left ≫ X₁.hom ≫ q) q
  have hu : (g ≫ uPart q π₁) ≫ U.hom = a ≫ q := by
    simp only [a, Category.assoc, pullback.condition]
  have hv : (h ≫ uPart q π₁) ≫ U.hom = a ≫ q := by
    rw [h3]; simp only [Category.assoc, pullback.condition]
  have hb : a ≫ q = b ≫ q := by
    have := congrArg (g ≫ ·) (uPart_cond q π₁)
    simp only [Category.assoc] at this
    simp only [a, b, Category.assoc]
    rw [show pullback.snd U.hom q ≫ q = pullback.fst U.hom q ≫ U.hom from pullback.condition.symm]
    exact this
  have eg : g ≫ pullback.fst _ _ = pullback.lift (g ≫ uPart q π₁) a hu := by
    apply pullback.hom_ext <;> simp [a]
  have eh : h ≫ pullback.fst _ _ = pullback.lift (h ≫ uPart q π₁) a hv := by
    apply pullback.hom_ext
    · simp
    · simp [a, h3]
  have key := hKI Z (g ≫ uPart q π₁) (h ≫ uPart q π₁) a b hu hv hb (by
    rw [← eg, ← eh]; simpa only [Category.assoc] using h1)
  have eg' : g ≫ pullback.lift (uPart q π₁) (pullback.snd _ _) (uPart_cond q π₁) =
      pullback.lift (g ≫ uPart q π₁) b (hu.trans hb) := by
    apply pullback.hom_ext <;> simp [b]
  have eh' : h ≫ pullback.lift (uPart q π₁) (pullback.snd _ _) (uPart_cond q π₁) =
      pullback.lift (h ≫ uPart q π₁) b (hv.trans hb) := by
    apply pullback.hom_ext
    · simp
    · simp [b, h2]
  simp only [ββ, ← Category.assoc, eg', eh']
  exact key

variable [Flat π₁.left] [Surjective π₁.left] [QuasiCompact π₁.left]

instance : Flat (αα q π₁) := MorphismProperty.of_isPullback (P := @Flat) (isPullback_αα q π₁) inferInstance
instance : Surjective (αα q π₁) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_αα q π₁) inferInstance
instance : QuasiCompact (αα q π₁) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_αα q π₁) inferInstance

/-- **The descent datum in universal form**: `ψ : X₁ ×_S S' → X₁`, `(π₁(u, a), b) ↦ π₁(u, b)`. -/
def ψψ (hKI : KI q π₁) : PP q (X₁ := X₁) ⟶ X₁.left :=
  EffectiveEpi.desc (αα q π₁) (ββ q π₁) (fun g h hgh => ββ_coeq hKI g h hgh)

theorem ψ_fac (hKI : KI q π₁) : αα q π₁ ≫ ψψ hKI = ββ q π₁ := EffectiveEpi.fac _ _ _

/-- The transport of `π₁(u₁)` to `c` is `π₁(u, c)`. -/
theorem ψ_π (hKI : KI q π₁) {Z : Scheme.{0}} (u₁ : Z ⟶ ((Over.pullback q).obj U).left) (c : Z ⟶ S')
    (h : (u₁ ≫ π₁.left) ≫ X₁.hom ≫ q = c ≫ q) :
    pullback.lift (u₁ ≫ π₁.left) c h ≫ ψψ hKI =
      pullback.lift (u₁ ≫ pullback.fst U.hom q) c (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, ← h, ← w_π₁ q π₁]
        simp only [Category.assoc]) ≫ π₁.left := by
  have e : pullback.lift (u₁ ≫ π₁.left) c h = pullback.lift u₁ c (by simpa only [Category.assoc] using h) ≫
      αα q π₁ := by
    apply pullback.hom_ext <;> simp
  rw [e, Category.assoc, ψ_fac]
  simp only [ββ, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

theorem ψ_snd (hKI : KI q π₁) : ψψ hKI ≫ X₁.hom = pullback.snd (X₁.hom ≫ q) q := by
  rw [← cancel_epi (αα q π₁), ← Category.assoc, ψ_fac]
  simp only [ββ, Category.assoc, w_π₁, pullback.lift_snd, Category.comp_id]

theorem ψ_unit (hKI : KI q π₁) :
    (pullback.lift (𝟙 X₁.left) X₁.hom (by simp) : X₁.left ⟶ PP q (X₁ := X₁)) ≫ ψψ hKI = 𝟙 X₁.left := by
  rw [← cancel_epi π₁.left, ← Category.assoc, Category.comp_id]
  have e : π₁.left ≫ (pullback.lift (𝟙 X₁.left) X₁.hom (by simp) : X₁.left ⟶ PP q (X₁ := X₁)) =
      pullback.lift (𝟙 _ ≫ π₁.left) (pullback.snd U.hom q)
        (by rw [Category.id_comp, reassoc_of% (w_π₁ q π₁)]) := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.lift_snd]; exact w_π₁ q π₁
  rw [e, ψ_π hKI (𝟙 _)]
  conv_rhs => rw [← Category.id_comp π₁.left]
  congr 1
  apply pullback.hom_ext <;> simp

/-- `(X₁ ×_S S') ×_S S'`. -/
abbrev TT := pullback (pullback.snd (X₁.hom ≫ q) q ≫ q) q

/-- `(U_{S'} ×_S S') ×_S S'`. -/
abbrev TU := pullback (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) q

abbrev α₃ : TU (q := q) (π₁ := π₁) ⟶ TT (q := q) (X₁ := X₁) :=
  pullback.map (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) q (pullback.snd (X₁.hom ≫ q) q ≫ q) q
    (αα q π₁) (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem isPullback_α₃ :
    IsPullback (pullback.fst _ _) (α₃ (q := q) (π₁ := π₁)) (αα q π₁) (pullback.fst _ _) :=
  isPullback_pullback_map_left (αα q π₁) (pullback.snd (X₁.hom ≫ q) q ≫ q) q

instance : Flat (α₃ (q := q) (π₁ := π₁)) :=
  MorphismProperty.of_isPullback (P := @Flat) isPullback_α₃ inferInstance
instance : Surjective (α₃ (q := q) (π₁ := π₁)) :=
  MorphismProperty.of_isPullback (P := @Surjective) isPullback_α₃ inferInstance
instance : QuasiCompact (α₃ (q := q) (π₁ := π₁)) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) isPullback_α₃ inferInstance

theorem ψ_coassoc_univ (hKI : KI q π₁) :
    pullback.lift (pullback.fst (pullback.snd (X₁.hom ≫ q) q ≫ q) q ≫ ψψ hKI)
      (pullback.snd (pullback.snd (X₁.hom ≫ q) q ≫ q) q) (by
        rw [Category.assoc, reassoc_of% (ψ_snd hKI), pullback.condition]) ≫ ψψ hKI =
    pullback.lift (pullback.fst (pullback.snd (X₁.hom ≫ q) q ≫ q) q ≫ pullback.fst (X₁.hom ≫ q) q)
      (pullback.snd (pullback.snd (X₁.hom ≫ q) q ≫ q) q) (by
        rw [Category.assoc, pullback.condition]; exact pullback.condition) ≫ ψψ hKI := by
  rw [← cancel_epi (α₃ (q := q) (π₁ := π₁))]
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
  let y := pullback.fst (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) q
  let c' := pullback.snd (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) q
  let u₁ := y ≫ pullback.lift (uPart q π₁) (pullback.snd _ _) (uPart_cond q π₁)
  have hc : y ≫ (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) = c' ≫ q := pullback.condition
  have hαs : αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q = pullback.snd (π₁.left ≫ X₁.hom ≫ q) q := by
    simp
  have hαs' : αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q =
      pullback.snd (π₁.left ≫ X₁.hom ≫ q) q ≫ q := by rw [← Category.assoc, hαs]
  have w' : π₁.left ≫ X₁.hom ≫ q = pullback.snd U.hom q ≫ q := by rw [← Category.assoc, w_π₁]
  have h1 : (u₁ ≫ π₁.left) ≫ X₁.hom ≫ q = c' ≫ q := by
    have e : (u₁ ≫ π₁.left) ≫ X₁.hom ≫ q = y ≫ (pullback.snd (π₁.left ≫ X₁.hom ≫ q) q ≫ q) := by
      simp only [u₁, Category.assoc, w', pullback.lift_snd_assoc]
    exact e.trans ((congrArg (y ≫ ·) hαs').symm.trans hc)
  have h2 : ((y ≫ pullback.fst _ _) ≫ π₁.left) ≫ X₁.hom ≫ q = c' ≫ q := by
    have e : ((y ≫ pullback.fst _ _) ≫ π₁.left) ≫ X₁.hom ≫ q =
        y ≫ (pullback.snd (π₁.left ≫ X₁.hom ≫ q) q ≫ q) := by
      simp only [Category.assoc]; exact congrArg (y ≫ ·) pullback.condition
    exact e.trans ((congrArg (y ≫ ·) hαs').symm.trans hc)
  have e1 : α₃ (q := q) (π₁ := π₁) ≫ pullback.lift (pullback.fst (pullback.snd (X₁.hom ≫ q) q ≫ q) q ≫ ψψ hKI)
      (pullback.snd (pullback.snd (X₁.hom ≫ q) q ≫ q) q) (by
        rw [Category.assoc, reassoc_of% (ψ_snd hKI), pullback.condition]) =
      pullback.lift (u₁ ≫ π₁.left) c' h1 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, u₁, y]
      rw [pullback.lift_fst_assoc, Category.assoc, ψ_fac]
    · simp [c']
  have e2 : α₃ (q := q) (π₁ := π₁) ≫ pullback.lift
      (pullback.fst (pullback.snd (X₁.hom ≫ q) q ≫ q) q ≫ pullback.fst (X₁.hom ≫ q) q)
      (pullback.snd (pullback.snd (X₁.hom ≫ q) q ≫ q) q) (by
        rw [Category.assoc, pullback.condition]; exact pullback.condition) =
      pullback.lift ((y ≫ pullback.fst _ _) ≫ π₁.left) c' h2 := by
    apply pullback.hom_ext
    · simp [y]
    · simp [c']
  rw [e1, e2, ψ_π hKI, ψ_π hKI]
  congr 2
  simp [u₁, uPart]

theorem ψ_coassoc (hKI : KI q π₁) {Z : Scheme.{0}} (x : Z ⟶ X₁.left) (b c : Z ⟶ S')
    (hb : x ≫ X₁.hom ≫ q = b ≫ q) (hc : x ≫ X₁.hom ≫ q = c ≫ q) :
    pullback.lift (pullback.lift x b hb ≫ ψψ hKI) c (by
      rw [Category.assoc, reassoc_of% (ψ_snd hKI), pullback.lift_snd_assoc, ← hb, hc]) ≫ ψψ hKI =
      pullback.lift x c hc ≫ ψψ hKI := by
  let t : Z ⟶ TT (q := q) (X₁ := X₁) := pullback.lift (pullback.lift x b hb) c (by
    rw [pullback.lift_snd_assoc, ← hb, hc])
  have := congrArg (t ≫ ·) (ψ_coassoc_univ (q := q) (π₁ := π₁) hKI)
  simp only [← Category.assoc] at this
  convert this using 2
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, t]; rw [pullback.lift_fst_assoc]
    · simp [t]
  · apply pullback.hom_ext
    · simp [t]
    · simp [t]

/-- **The descent datum on `X₁`** (transport form): a point `x` over `f₁` goes to `ψ(x, f₂)`. -/
def dd (hKI : KI q π₁) : Over.DescentDatum q X₁ where
  transport f₁ f₂ e p := Over.homMk (pullback.lift p.left f₂ (by rw [← Category.assoc, Over.w p]; exact e) ≫
    ψψ hKI) (by
      change (pullback.lift p.left f₂ _ ≫ ψψ hKI) ≫ X₁.hom = f₂
      rw [Category.assoc, ψ_snd, pullback.lift_snd])
  transport_homMk_comp c f₁ f₂ e p := by
    ext
    change pullback.lift (c ≫ p.left) (c ≫ f₂) _ ≫ ψψ hKI = c ≫ (pullback.lift p.left f₂ _ ≫ ψψ hKI)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    congr 1
    apply pullback.hom_ext <;> simp
  transport_self f p := by
    ext
    simp only [Over.homMk_left]
    have : pullback.lift p.left f (by rw [← Category.assoc, Over.w p]; rfl) =
        p.left ≫ (pullback.lift (𝟙 X₁.left) X₁.hom (by simp) : X₁.left ⟶ PP q (X₁ := X₁)) := by
      apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, pullback.lift_snd]; exact (Over.w p).symm
    rw [this, Category.assoc, ψ_unit, Category.comp_id]
  transport_transport f₁ f₂ f₃ h₁₂ h₂₃ p := by
    ext
    simp only [Over.homMk_left]
    exact ψ_coassoc hKI p.left f₂ f₃ _ _

/-- **Descent of the quotient**: with `KI`, finite sets of `X₁` in affine opens, and `q` finite flat surjective
of finite presentation, `X₁` descends to `B₀` over `S` and `π₁` to `π : U → B₀`. -/
theorem exists_descent (hKI : KI q π₁) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    (hfin : ∀ s : Set X₁.left, s.Finite → ∃ V : X₁.left.Opens, IsAffineOpen V ∧ s ⊆ V) :
    ∃ (B₀ : Over S) (d : X₁.left ⟶ B₀.left) (π : U.left ⟶ B₀.left),
      IsPullback d X₁.hom B₀.hom q ∧ pullback.fst U.hom q ≫ π = π₁.left ≫ d ∧ π ≫ B₀.hom = U.hom := by
  obtain ⟨B₀, d, hsq, hinv⟩ := (dd hKI).isEffective_of_isFinite hfin
  have hψd : ψψ hKI ≫ d = pullback.fst (X₁.hom ≫ q) q ≫ d := by
    have := hinv (pullback.fst (X₁.hom ≫ q) q ≫ X₁.hom) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition) (Over.homMk (pullback.fst _ _) rfl)
    change (pullback.lift (pullback.fst (X₁.hom ≫ q) q) (pullback.snd (X₁.hom ≫ q) q) _ ≫ ψψ hKI) ≫ d =
      pullback.fst (X₁.hom ≫ q) q ≫ d at this
    rwa [pullback.lift_fst_snd, Category.id_comp] at this
  have hcoeq : ∀ {Z : Scheme.{0}} (g h : Z ⟶ pullback U.hom q),
      g ≫ pullback.fst U.hom q = h ≫ pullback.fst U.hom q → g ≫ π₁.left ≫ d = h ≫ π₁.left ≫ d := by
    intro Z g h hgh
    have hc : (g ≫ π₁.left) ≫ X₁.hom ≫ q = (h ≫ pullback.snd U.hom q) ≫ q :=
      calc (g ≫ π₁.left) ≫ X₁.hom ≫ q = g ≫ pullback.snd U.hom q ≫ q := by
            rw [Category.assoc, ← Category.assoc π₁.left, w_π₁]
        _ = g ≫ pullback.fst U.hom q ≫ U.hom := by rw [pullback.condition]
        _ = h ≫ pullback.fst U.hom q ≫ U.hom := by rw [← Category.assoc, hgh, Category.assoc]
        _ = (h ≫ pullback.snd U.hom q) ≫ q := by rw [pullback.condition, Category.assoc]
    have e := ψ_π hKI g (h ≫ pullback.snd U.hom q) hc
    have e' : pullback.lift (g ≫ pullback.fst U.hom q) (h ≫ pullback.snd U.hom q) (by
        rw [hgh, Category.assoc, Category.assoc, pullback.condition]) = h := by
      apply pullback.hom_ext
      · simp [hgh]
      · simp
    rw [e'] at e
    rw [← Category.assoc h, ← e, Category.assoc, hψd, pullback.lift_fst_assoc, Category.assoc]
  refine ⟨B₀, d, EffectiveEpi.desc (pullback.fst U.hom q) (π₁.left ≫ d) (fun g h hgh => hcoeq g h hgh),
    hsq, EffectiveEpi.fac _ _ _, ?_⟩
  rw [← cancel_epi (pullback.fst U.hom q), ← Category.assoc, EffectiveEpi.fac, Category.assoc, hsq.w,
    ← Category.assoc, w_π₁, pullback.condition]

end Descent



section Rig

variable (K : Type) [Field K]

/-- `Spec K`. -/
abbrev PK : Scheme := Spec (CommRingCat.of K)

/-- The overlap `𝔾_m ⊆ ℙ¹_K` of the two standard charts. -/
abbrev Ov : Scheme := (relativeOverlap (PK K)).toScheme

/-- An element of `K` as a global section of `Spec K`. -/
abbrev secK (s : K) : Γ(PK K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv s

theorem mem_overlap (s : Kˣ) (x : PK K) :
    normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) x ∈ relativeOverlap (PK K) := by
  have hc : ∀ c : ULift.{0} (Fin 2),
      normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) x ∈ standardOpen (ULift.{0} (Fin 2)) (PK K) c := by
    intro c
    change x ∈ normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) ⁻¹ᵁ standardOpen (ULift.{0} (Fin 2)) (PK K) c
    rw [normalized, homOfSections_preimage_standardOpen]
    have hu : IsUnit (normalizedSections (source := PK K) ⟨1⟩ (secK K s) c) := by
      unfold normalizedSections
      split_ifs
      · exact isUnit_one
      · exact (s.isUnit.map _)
    rw [Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact ⟨hc ⟨0⟩, hc ⟨1⟩⟩

/-- The `K`-point `[s : 1]` of the overlap. -/
def ovPt (s : Kˣ) : PK K ⟶ Ov K :=
  IsOpenImmersion.lift (relativeOverlap (PK K)).ι (normalized (𝟙 (PK K)) ⟨1⟩ (secK K s)) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact mem_overlap K s x)

@[reassoc (attr := simp)]
theorem ovPt_ι (s : Kˣ) : ovPt K s ≫ (relativeOverlap (PK K)).ι = normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) :=
  IsOpenImmersion.lift_fac ..

theorem ovPt_over (s : Kˣ) : ovPt K s ≫ overlapToBase K = 𝟙 (PK K) := by
  rw [overlapToBase, ovPt_ι_assoc, normalized_over]

theorem ovPt_coordinate (s : Kˣ) : (ovPt K s).appTop (scalingCoordinate K ⟨1⟩) = secK K s := by
  have chartEquation : ovPt K s ≫ ((relativeLine (PK K))).homOfLE
      (relativeOverlap_le_standardOpen (PK K) ⟨1⟩) =
      relativeChartPoint (𝟙 (PK K)) ⟨1⟩ (secK K s) := by
    apply (cancel_mono (standardOpen (ULift.{0} (Fin 2)) (PK K) ⟨1⟩).ι).mp
    simp
  rw [scalingCoordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    chartEquation, relativeChartPoint_coordinate]

/-- `ℙ¹_K` is smooth of relative dimension one. -/
instance line_smooth : SmoothOfRelativeDimension 1 (relativeLine (PK K) ↘ PK K) := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 1) (relativeChartCover (PK K))
  intro (c : ULift.{0} (Fin 2))
  change SmoothOfRelativeDimension 1
    ((standardOpen (ULift.{0} (Fin 2)) (PK K) c).ι ≫ relativeLine (PK K) ↘ PK K)
  rw [← standardOpenIso_hom_over]
  have : Nat.card {o : ULift.{0} (Fin 2) // o ≠ c} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨c.down.rev⟩, ?_⟩⟩⟩
    · rcases a with ⟨⟨a⟩, ha⟩; rcases b with ⟨⟨b⟩, hb⟩; rcases c with ⟨c⟩
      ext; simp only [ne_eq, ULift.ext_iff] at ha hb ⊢; omega
    · rcases c with ⟨c⟩; simp only [ne_eq, ULift.ext_iff]; fin_cases c <;> decide
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension.{0} 1)]
  exact AffineSpace.smoothOfRelativeDimension_of_card_eq (n := {o : ULift.{0} (Fin 2) // o ≠ c})
    (PK K) this


variable {K}

theorem genericPoint_mem_overlap : genericPoint (relativeLine (PK K)) ∈ relativeOverlap (PK K) := by
  rw [← SetLike.mem_coe,
    (genericPoint_spec (relativeLine (PK K))).mem_open_set_iff (relativeOverlap (PK K)).isOpen]
  simpa using (Scheme.Opens.nonempty_iff _).mp (inferInstance : Nonempty (Ov K))

/-- `Spec K(ℙ¹) → 𝔾_m`. -/
abbrev ξg : Spec (relativeLine (PK K)).functionField ⟶ Ov K :=
  (relativeOverlap (PK K)).fromSpecStalkOfMem _ (genericPoint_mem_overlap (K := K))

theorem ξg_ι : ξg (K := K) ≫ (relativeOverlap (PK K)).ι = (relativeLine (PK K)).fromSpecFunctionField :=
  Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

instance : IsDominant (ξg (K := K)) := by
  constructor
  let p : Spec (relativeLine (PK K)).functionField :=
    IsLocalRing.closedPoint ((relativeLine (PK K)).functionField)
  let z := (ξg (K := K)) p
  have hz : (relativeOverlap (PK K)).ι z = genericPoint (relativeLine (PK K)) := by
    show (relativeOverlap (PK K)).ι ((ξg (K := K)) p) = _
    rw [← Scheme.Hom.comp_apply, ξg_ι]
    exact Scheme.fromSpecStalk_closedPoint
  have hd : Dense ({z} : Set (Ov K)) := by
    rw [dense_iff_closure_eq,
      (relativeOverlap (PK K)).ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hz, genericPoint_closure]
    rfl
  exact hd.mono (by rintro _ rfl; exact ⟨_, rfl⟩)

/-- Every morphism `ℙ¹_K → B` to an abelian variety takes the same value at all `K`-points
(vendored `RationalCurves.eq_zero_comp`, commutativity from Mathlib). -/
theorem line_const (B : PkgI3.AbVar K) (E : relativeLineOver K ⟶ B.X)
    (a b : 𝟙_ (Over (PK K)) ⟶ relativeLineOver K) : a ≫ E = b ≫ E := by
  letI := B.grp
  haveI := B.proper
  haveI := B.smooth
  haveI := B.geomInt
  haveI : IsCommMonObj B.X := isCommMonObj_of_isProper_of_geometricallyIntegral B.X
  let V : AlgebraicGeometry.AbelianVariety K := ⟨CommGrp.mk B.X⟩
  have hE := AlgebraicGeometry.AbelianVariety.RationalCurves.eq_zero_comp V E
  have ha : a ≫ E = ProjectiveLine.zeroPointOver K ≫ E := by
    conv_lhs => rw [hE]
    rw [← Category.assoc, ← Category.assoc, Subsingleton.elim (a ≫ toUnit _) (𝟙 _), Category.id_comp]
  have hb : b ≫ E = ProjectiveLine.zeroPointOver K ≫ E := by
    conv_lhs => rw [hE]
    rw [← Category.assoc, ← Category.assoc, Subsingleton.elim (b ≫ toUnit _) (𝟙 _), Category.id_comp]
  rw [ha, hb]

/-- **Rigidity for `𝔾_m`**: a morphism from the overlap `𝔾_m ⊆ ℙ¹_K` to an abelian variety over `K` takes
the same value at all the points `[s : 1]`. -/
theorem overlap_const (B : PkgI3.AbVar K) (h : Ov K ⟶ B.X.left) (hh : h ≫ B.X.hom = overlapToBase K)
    (s t : Kˣ) : ovPt K s ≫ h = ovPt K t ≫ h := by
  letI : (B.X.left).Over (PK K) := ⟨B.X.hom⟩
  haveI : IsProper (B.X.left ↘ PK K) := B.proper
  haveI : B.X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from B.X.hom]
    haveI : IsSeparated B.X.hom := inferInstanceAs (IsSeparated (B.X.left ↘ PK K))
    infer_instance⟩
  have hval : ∀ x, ValuationRing ((relativeLine (PK K)).presheaf.stalk x) :=
    Scheme.valuationRing_stalk (relativeLine (PK K) ↘ PK K)
  obtain ⟨E, hEo, hE⟩ := Scheme.exists_hom_of_valuationRing_stalk (base := PK K) hval (ξg ≫ h) (by
    change ξg ≫ h ≫ B.X.hom = _
    rw [hh, overlapToBase, ← Category.assoc, ξg_ι])
  have hEo' : E ≫ B.X.hom = relativeLine (PK K) ↘ PK K := hEo.comp_over
  have hagree : (relativeOverlap (PK K)).ι ≫ E = h := by
    apply ext_of_isDominant_of_isSeparated B.X.hom ?_ (ξg (K := K)) ?_
    · rw [Category.assoc, hEo', hh, overlapToBase]
    · rw [← Category.assoc, ξg_ι, hE]
  let Em : relativeLineOver K ⟶ B.X := Over.homMk E hEo'
  let pt : Kˣ → (𝟙_ (Over (PK K)) ⟶ relativeLineOver K) := fun s =>
    Over.homMk (ovPt K s ≫ (relativeOverlap (PK K)).ι) (by
      change (ovPt K s ≫ (relativeOverlap (PK K)).ι) ≫ relativeLine (PK K) ↘ PK K = 𝟙 _
      rw [Category.assoc, ← overlapToBase, ovPt_over])
  have := congrArg CommaMorphism.left (line_const B Em (pt s) (pt t))
  simp only [Over.comp_left, Over.homMk_left, Em, pt] at this
  rw [← hagree, ← Category.assoc, ← Category.assoc]
  simpa only [Category.assoc] using this

/-- The `K`-algebra structure of `Γ(𝔾_m)`. -/
@[reducible] def ovAlg : Algebra K Γ(Ov K, ⊤) :=
  ((overlapToBase K).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra

/-- The coordinate `u = X₀/X₁` of `𝔾_m`, a unit. -/
def uOv : Γ(Ov K, ⊤)ˣ :=
  ⟨scalingCoordinate K ⟨1⟩, scalingCoordinate K ⟨0⟩, scalingCoordinate_mul K ⟨1⟩ ⟨0⟩ (by decide),
    scalingCoordinate_mul K ⟨0⟩ ⟨1⟩ (by decide)⟩

/-- `𝔾_m ⊆ ℙ¹ → Spec K[x^{±1}]`, `x ↦ u`. -/
def mOv : Ov K ⟶ Spec (CommRingCat.of (TorusRing K 1)) :=
  letI := ovAlg (K := K)
  (Ov K).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (torusLift (K := K) (fun _ => uOv (K := K))).toRingHom)

theorem ovPt_mOv (s : Kˣ) :
    ovPt K s ≫ mOv = Spec.map (CommRingCat.ofHom (torusLift (K := K) (R := K) (fun _ => s)).toRingHom) := by
  letI := ovAlg (K := K)
  rw [mOv, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  apply IsLocalization.ringHom_ext (Submonoid.powers (∏ i : Fin 1, MvPolynomial.X i :
    MvPolynomial (Fin 1) K))
  apply MvPolynomial.ringHom_ext
  · intro a
    have h1 : (ovPt K s).appTop ((overlapToBase K).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv a := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ovPt_over]; rfl
    simp only [RingHom.comp_apply, CommRingCat.hom_comp, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [show (algebraMap (MvPolynomial (Fin 1) K) (TorusRing K 1)) (MvPolynomial.C a) =
      algebraMap K (TorusRing K 1) a from rfl, AlgHom.commutes, AlgHom.commutes]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((ovPt K s).appTop
      ((overlapToBase K).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))) = a
    rw [h1, ← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  · intro i
    have hi : (algebraMap (MvPolynomial (Fin 1) K) (TorusRing K 1)) (MvPolynomial.X i) =
        ((tUniv 1 i : (TorusRing K 1)ˣ) : TorusRing K 1) := by simp [tUniv]
    simp only [RingHom.comp_apply, CommRingCat.hom_comp, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [hi, torusLift_tUniv, torusLift_tUniv]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((ovPt K s).appTop (scalingCoordinate K ⟨1⟩)) = s
    rw [ovPt_coordinate, secK, ← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl

theorem mOv_over : mOv (K := K) ≫ (algPt K (TorusRing K 1)).hom = overlapToBase K := by
  letI := ovAlg (K := K)
  change ((Ov K).toSpecΓ ≫ Spec.map _) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (TorusRing K 1))) = _
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show ((torusLift (K := K) (fun _ => uOv (K := K))).toRingHom.comp (algebraMap K (TorusRing K 1))) =
    algebraMap K Γ(Ov K, ⊤) from (torusLift (K := K) (fun _ => uOv (K := K))).comp_algebraMap]
  change (Ov K).toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (overlapToBase K).appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **Rigidity for `𝔾_m`, torus form**: a morphism `Spec K[x^{±1}] → B` to an abelian variety over a field `K`
takes the same value at all `K`-points `x ↦ s`. -/
theorem torus1_const (B : PkgI3.AbVar K) (g : algPt K (TorusRing K 1) ⟶ B.X) (s : Kˣ) :
    algPtMap (torusLift (K := K) (R := K) (fun _ => s)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
  have hh : (mOv (K := K) ≫ g.left) ≫ B.X.hom = overlapToBase K := by
    rw [Category.assoc, Over.w g, mOv_over]
  have := overlap_const B (mOv ≫ g.left) hh s 1
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  rw [← Category.assoc, ovPt_mOv, ← Category.assoc, ovPt_mOv] at this
  exact this

end Rig


section TorusR

set_option maxHeartbeats 300000

variable {K : Type} [Field K]

theorem algPtMap_comp {R S T : Type} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T]
    [Algebra K T] (f : R →ₐ[K] S) (g : S →ₐ[K] T) :
    algPtMap (k := K) g ≫ algPtMap f = algPtMap (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- One coordinate of a torus point can be moved to `1`. -/
theorem torus_update_const (B : PkgI3.AbVar K) {r : ℕ} (g : algPt K (TorusRing K r) ⟶ B.X)
    (c : Fin r → Kˣ) (j : Fin r) (s : Kˣ) :
    algPtMap (torusLift (K := K) (R := K) (Function.update c j s)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (Function.update c j 1)) ≫ g := by
  let φ : TorusRing K r →ₐ[K] TorusRing K 1 := torusLift (K := K)
    (fun i => if i = j then tUniv 1 0 else Units.map (algebraMap K (TorusRing K 1) : K →* TorusRing K 1) (c i))
  have key : ∀ s' : Kˣ, (torusLift (K := K) (R := K) (fun _ => s')).comp φ =
      torusLift (K := K) (R := K) (Function.update c j s') := by
    intro s'
    apply algHom_ext_torus
    intro i
    rw [AlgHom.comp_apply, torusLift_tUniv, torusLift_tUniv]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, torusLift_tUniv, Function.update_self]
    · rw [if_neg hij, Function.update_of_ne hij]
      change (torusLift (K := K) (R := K) (fun _ => s')) (algebraMap K (TorusRing K 1) (c i : K)) = (c i : K)
      rw [AlgHom.commutes]; rfl
  have h := torus1_const B (algPtMap φ ≫ g) s
  rw [← Category.assoc, ← Category.assoc, algPtMap_comp, algPtMap_comp, key, key] at h
  exact h

/-- **Rigidity for `𝔾_m^r`**: a morphism `Spec K[x₁^{±1}, …, x_r^{±1}] → B` to an abelian variety takes the same
value at all `K`-points. -/
theorem torusR_const (B : PkgI3.AbVar K) {r : ℕ} (g : algPt K (TorusRing K r) ⟶ B.X) (t : Fin r → Kˣ) :
    algPtMap (torusLift (K := K) (R := K) t) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
  classical
  have hs : ∀ s : Finset (Fin r), algPtMap (torusLift (K := K) (R := K)
      (fun i => if i ∈ s then t i else 1)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have e1 : (fun i => if i ∈ insert j s then t i else 1) =
          Function.update (fun i => if i ∈ s then t i else 1) j (t j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij, Function.update_of_ne hij]
      have e2 : (fun i => if i ∈ s then t i else (1 : Kˣ)) =
          Function.update (fun i => if i ∈ s then t i else 1) j 1 := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [Function.update_of_ne hij]
      rw [e1, torus_update_const, ← e2, ih]
  have := hs Finset.univ
  simpa using this

end TorusR

section KbarKI

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}

/-- The base change of an abelian variety along a field extension `ρ : K → L`. -/
def abVarBC {K L : Type} [Field K] [Field L] (ρ : K →+* L) (B : PkgI3.AbVar K) : PkgI3.AbVar L :=
  letI := B.grp
  haveI := B.proper
  haveI := B.smooth
  haveI := B.geomInt
  { X := (Over.pullback (sφ ρ)).obj B.X
    grp := Functor.grpObjObj
    proper := by change IsProper (pullback.snd B.X.hom (sφ ρ)); infer_instance
    smooth := by change Smooth (pullback.snd B.X.hom (sφ ρ)); infer_instance
    geomInt := by change GeometricallyIntegral (pullback.snd B.X.hom (sφ ρ)); infer_instance }

/-- **Rigidity, raw form**: for a field `L` with `ρ : k̄ → L` and a `U`-point `W` of the torus
`Spec L[x^{±1}]` (structure through `ρ`), `π'(W, ρ)` takes the same value at all `L`-points of the torus. -/
theorem rig_raw (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X) (L : Type) [Field L]
    (ρ : AlgebraicClosure k →+* L) (r : ℕ) (W : Spec (CommRingCat.of (TorusRing L r)) ⟶ U.left)
    (hW : W ≫ U.hom = Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp ρ)) ≫ sφ (φbar k))
    (t : Fin r → Lˣ) :
    Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) t).toRingHom) ≫
        (pullback.lift W _ hW ≫ π'.left) =
      Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) (fun _ => (1 : Lˣ))).toRingHom) ≫
        (pullback.lift W _ hW ≫ π'.left) := by
  letI := B'.grp
  letI Ib0 : Algebra (AlgebraicClosure k) (TorusRing L r) := algK ρ (TorusRing L r)
  letI : GrpObj ((Over.pullback (sφ ρ)).obj B'.X) := Functor.grpObjObj
  let g : algPt (AlgebraicClosure k) (TorusRing L r) ⟶ B'.X :=
    Over.homMk (pullback.lift W _ hW ≫ π'.left) (by
      change (pullback.lift W _ hW ≫ π'.left) ≫ B'.X.hom = _
      rw [Category.assoc, Over.w π']
      exact pullback.lift_snd _ _ _)
  let g' := (Φ ρ B'.X (TorusRing L r)).symm g
  have hc := torusR_const (abVarBC ρ B') g' t
  have h2 := congrArg (Φ ρ B'.X L) hc
  rw [Φ_natural, Φ_natural, MulEquiv.apply_symm_apply] at h2
  exact congrArg (fun z => Over.Hom.left z) h2


/-- The unit of `U_{k̄}` at a `k̄`-algebra `L`, on `U`. -/
theorem one_left_fst (L : Type) [CommRing L] [Algebra (AlgebraicClosure k) L] :
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    (1 : algPt (AlgebraicClosure k) L ⟶ (Over.pullback (sφ (φbar k))).obj U).left ≫
        pullback.fst U.hom (sφ (φbar k)) =
      (algPt (AlgebraicClosure k) L).hom ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  rw [Hom.one_def, Over.comp_left, Category.assoc, CToPrinted.unit_bc_fst]
  rfl

/-- `η` of `U_{k̄}` composed with a point `ρ`, as a lift. -/
theorem lift_unit (L : Type) [CommRing L] (ρ : CommRingCat.of (AlgebraicClosure k) ⟶ CommRingCat.of L)
    (x : Spec (CommRingCat.of L) ⟶ U.left) (hx : x = Spec.map ρ ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left)
    (h : x ≫ U.hom = Spec.map ρ ≫ sφ (φbar k)) :
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    pullback.lift x (Spec.map ρ) h =
      Spec.map ρ ≫ (η[(Over.pullback (sφ (φbar k))).obj U] : 𝟙_ _ ⟶ _).left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, CToPrinted.unit_bc_fst, hx]
  · rw [pullback.lift_snd, Category.assoc]
    have := Over.w (η[(Over.pullback (sφ (φbar k))).obj U] : 𝟙_ _ ⟶ _)
    change _ ≫ pullback.snd U.hom (sφ (φbar k)) = 𝟙 _ at this
    rw [this, Category.comp_id]

/-- **Torus kernels are transport-stable**: a point of the torus `ker π'` for the `k̄`-structure `ra` on `L` maps to
the unit under `π'` for any other `k̄`-structure `rb` with the same restriction to `k` (rigidity). -/
theorem torus_kernel_transfer (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (L : Type) [Field L] (ra rb : AlgebraicClosure k →+* L) (hab : ra.comp (φbar k) = rb.comp (φbar k))
    (t : Fin r → Lˣ) :
    letI := ra.toAlgebra
    ∀ (hcond : ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
        Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)),
    pullback.lift ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) _ hcond ≫ π'.left =
      Spec.map (CommRingCat.ofHom rb) ≫ (η[B'.X] : 𝟙_ _ ⟶ B'.X).left := by
  letI Ia := ra.toAlgebra
  intro hcond
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI := B'.grp
  haveI := hπ
  letI Ia0 : Algebra (AlgebraicClosure k) (TorusRing L r) := algK ra (TorusRing L r)
  let fl : (Fin r → Lˣ) → (TorusRing L r →ₐ[AlgebraicClosure k] L) := fun t' =>
    { (torusLift (K := L) (R := L) t').toRingHom with
      commutes' := fun x => (torusLift (K := L) (R := L) t').commutes (ra x) }
  have hnat : ∀ t' : Fin r → Lˣ, e L t' = algPtMap (fl t') ≫ e (TorusRing L r) (tUniv r) := by
    intro t'
    have := he_nat (TorusRing L r) L (fl t') (tUniv r)
    have hmap : (fun i => Units.map ((fl t' : TorusRing L r →ₐ[AlgebraicClosure k] L) :
        TorusRing L r →* L) (tUniv r i)) = t' := by
      funext i; ext; exact torusLift_tUniv t' i
    rwa [hmap] at this
  let W := (e (TorusRing L r) (tUniv r)).left ≫ pullback.fst U.hom (sφ (φbar k))
  have hW : W ≫ U.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp rb)) ≫ sφ (φbar k) := by
    simp only [W, Category.assoc]
    have hw : (e (TorusRing L r) (tUniv r)).left ≫ pullback.snd U.hom (sφ (φbar k)) =
        (algPt (AlgebraicClosure k) (TorusRing L r)).hom := Over.w (e (TorusRing L r) (tUniv r))
    rw [pullback.condition, ← Category.assoc, hw]
    change Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp ra)) ≫ sφ (φbar k) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      RingHom.comp_assoc, RingHom.comp_assoc, hab]
  have hlift : ∀ (t' : Fin r → Lˣ) (h' : ((e L t').left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)),
      pullback.lift ((e L t').left ≫ pullback.fst U.hom (sφ (φbar k))) _ h' =
        Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) t').toRingHom) ≫ pullback.lift W _ hW := by
    intro t' h'
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hnat t']
      rfl
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact ((torusLift (K := L) (R := L) t').commutes (rb x)).symm
  have h1 : e L (fun _ => (1 : Lˣ)) = 1 := map_one (e L)
  have hc1 : ((e L (fun _ => (1 : Lˣ))).left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) := by
    have hw : (e L (fun _ => (1 : Lˣ))).left ≫ pullback.snd U.hom (sφ (φbar k)) =
        Spec.map (CommRingCat.ofHom ra) := Over.w (e L _)
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  rw [hlift t hcond, Category.assoc, rig_raw π' L rb r W hW t, ← Category.assoc, ← hlift _ hc1]
  have hx : (e L (fun _ => (1 : Lˣ))).left ≫ pullback.fst U.hom (sφ (φbar k)) =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left := by
    rw [h1, one_left_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    change Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  rw [lift_unit L (CommRingCat.ofHom rb) _ hx hc1, Category.assoc, ← Over.comp_left, IsMonHom.one_hom]

theorem overMk_inv_mul_left {X S : Scheme.{0}} {f g : X ⟶ S} (hfg : f = g) {V : Over S} [GrpObj V]
    (a b : X ⟶ V.left) (ha : a ≫ V.hom = f) (hb : b ≫ V.hom = f) :
    ((Over.homMk a ha : Over.mk f ⟶ V)⁻¹ * Over.homMk b hb).left =
      ((Over.homMk a (ha.trans hfg) : Over.mk g ⟶ V)⁻¹ * Over.homMk b (hb.trans hfg)).left := by
  subst hfg; rfl

theorem homEquiv_left {S S' : Scheme.{0}} (g : S' ⟶ S) (X : Over S') (V : Over S)
    (p : (Over.map g).obj X ⟶ V) :
    ((Over.mapPullbackAdj g).homEquiv X V p).left =
      pullback.lift p.left X.hom (by simpa using Over.w p) := by
  apply pullback.hom_ext
  · simp [Adjunction.homEquiv_unit]
  · simp [Adjunction.homEquiv_unit]

theorem homEquiv_inv {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (X : Over (Spec (CommRingCat.of K'))) (V : Over (Spec (CommRingCat.of K))) [GrpObj V]
    (p : (Over.map (sφ φ)).obj X ⟶ V) :
    letI : GrpObj ((Over.pullback (sφ φ)).obj V) := Functor.grpObjObj
    (Over.mapPullbackAdj (sφ φ)).homEquiv X V p⁻¹ = ((Over.mapPullbackAdj (sφ φ)).homEquiv X V p)⁻¹ := by
  letI : GrpObj ((Over.pullback (sφ φ)).obj V) := Functor.grpObjObj
  let m : ((Over.map (sφ φ)).obj X ⟶ V) →* (X ⟶ (Over.pullback (sφ φ)).obj V) :=
    MonoidHom.mk' ((Over.mapPullbackAdj (sφ φ)).homEquiv X V) (homEquiv_mul' φ X V)
  exact map_inv m p

/-- **Kernel pairs are transport-stable** (`k̄`-level form of `KI`): if two `U`-points `u, v` over a field `L` have
the same image under `π'` for the `k̄`-structure `ra`, they have the same image for every `rb` with the same
restriction to `k`. -/
theorem kbar_KI (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (L : Type) [Field L] (ra rb : AlgebraicClosure k →+* L) (hab : ra.comp (φbar k) = rb.comp (φbar k))
    (u v : Spec (CommRingCat.of L) ⟶ U.left)
    (hu : u ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k))
    (hv : v ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k))
    (hb : Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k))
    (h : pullback.lift u _ hu ≫ π'.left = pullback.lift v _ hv ≫ π'.left) :
    pullback.lift u _ (hu.trans hb) ≫ π'.left = pullback.lift v _ (hv.trans hb) ≫ π'.left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI := B'.grp
  haveI := hπ
  let Φa := (Over.mapPullbackAdj (sφ (φbar k))).homEquiv (Over.mk (Spec.map (CommRingCat.ofHom ra))) U
  let Φb := (Over.mapPullbackAdj (sφ (φbar k))).homEquiv (Over.mk (Spec.map (CommRingCat.ofHom rb))) U
  let ua : Over.mk (Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k)) ⟶ U := Over.homMk u hu
  let va : Over.mk (Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k)) ⟶ U := Over.homMk v hv
  let ub : Over.mk (Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)) ⟶ U := Over.homMk u (hu.trans hb)
  let vb : Over.mk (Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)) ⟶ U := Over.homMk v (hv.trans hb)
  -- a-side
  have ha1 : Φa ua ≫ π' = Φa va ≫ π' := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, homEquiv_left, Φa]
    exact h
  have ha2 : Φa (ua⁻¹ * va) ≫ π' = 1 := by
    rw [homEquiv_mul', homEquiv_inv, MonObj.mul_comp, GrpObj.inv_comp, ha1, _root_.inv_mul_cancel]
  letI Ia := ra.toAlgebra
  obtain ⟨t, ht⟩ := (he_ker L (Φa (ua⁻¹ * va))).mp ha2
  have hraw : (e L t).left ≫ pullback.fst U.hom (sφ (φbar k)) = (ua⁻¹ * va).left := by
    rw [ht]
    change (Φa (ua⁻¹ * va)).left ≫ _ = _
    rw [homEquiv_left, pullback.lift_fst]
  -- transfer
  have htr := torus_kernel_transfer π' hπ r e he_nat L ra rb hab t (by
    rw [hraw, Over.w (ua⁻¹ * va)]; exact hb)
  -- b-side
  have hrawb : (ua⁻¹ * va).left = (ub⁻¹ * vb).left := overMk_inv_mul_left hb u v hu hv
  have hb2 : Φb (ub⁻¹ * vb) ≫ π' = 1 := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, homEquiv_left]
    show pullback.lift (ub⁻¹ * vb).left (Spec.map (CommRingCat.ofHom rb)) (Over.w (ub⁻¹ * vb)) ≫ π'.left = _
    have e1 : pullback.lift (ub⁻¹ * vb).left (Spec.map (CommRingCat.ofHom rb)) (Over.w (ub⁻¹ * vb)) =
        pullback.lift ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) (Spec.map (CommRingCat.ofHom rb))
          (by rw [hraw, Over.w (ua⁻¹ * va)]; exact hb) := by
      congr 1; rw [hraw, hrawb]
    rw [e1, htr, Hom.one_def, Over.comp_left]
    rfl
  have hb3 : Φb ub ≫ π' = Φb vb ≫ π' := by
    rw [homEquiv_mul', homEquiv_inv, MonObj.mul_comp, GrpObj.inv_comp] at hb2
    exact (inv_mul_eq_one.mp hb2)
  have := congrArg (fun z => Over.Hom.left z) hb3
  simp only [Φb, Over.comp_left, homEquiv_left] at this
  exact this

end KbarKI

section KI1

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}
  {k₁ : Type} [Field k₁] [Algebra k k₁] [Algebra k₁ (AlgebraicClosure k)]
  [IsScalarTower k k₁ (AlgebraicClosure k)]

/-- `Spec k₁ → Spec k`. -/
abbrev qq (k k₁ : Type) [Field k] [Field k₁] [Algebra k k₁] :
    Spec (CommRingCat.of k₁) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k₁))

/-- `Spec k̄ → Spec k₁`. -/
abbrev q₂ (k k₁ : Type) [Field k] [Field k₁] [Algebra k₁ (AlgebraicClosure k)] :
    Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k₁) :=
  Spec.map (CommRingCat.ofHom (algebraMap k₁ (AlgebraicClosure k)))

omit [GrpObj U] in
theorem q₂_qq : q₂ k k₁ ≫ qq k k₁ = sφ (φbar k) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- `U_{k̄} → U_{k₁}`. -/
abbrev rr (U : Over (Spec (CommRingCat.of k))) (k₁ : Type) [Field k₁] [Algebra k k₁]
    [Algebra k₁ (AlgebraicClosure k)] [IsScalarTower k k₁ (AlgebraicClosure k)] :
    pullback U.hom (sφ (φbar k)) ⟶ pullback U.hom (qq k k₁) :=
  pullback.map U.hom (sφ (φbar k)) U.hom (qq k k₁) (𝟙 _) (q₂ k k₁) (𝟙 _) (by simp)
    (by rw [Category.comp_id, q₂_qq])

omit [GrpObj U] in
theorem exists_ext_point [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)] (L : Type) [Field L] [IsAlgClosed L]
    (a : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁)) :
    ∃ ra : AlgebraicClosure k →+* L, Spec.map (CommRingCat.ofHom ra) ≫ q₂ k k₁ = a := by
  let a' : k₁ →+* L := (Spec.preimage a).hom
  letI : Algebra k₁ L := a'.toAlgebra
  refine ⟨(IsAlgClosed.lift (R := k₁) (S := AlgebraicClosure k) (M := L)).toRingHom, ?_⟩
  rw [← Spec.map_comp]
  conv_rhs => rw [← Spec.map_preimage a]
  congr 1
  ext x
  exact (IsAlgClosed.lift (R := k₁) (S := AlgebraicClosure k) (M := L)).commutes x

/-- `KI` at points with values in an algebraically closed field. -/
theorem algclosed_KI [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)]
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left)
    (L : Type) [Field L] [IsAlgClosed L] (u v : Spec (CommRingCat.of L) ⟶ U.left)
    (a b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁))
    (hu : u ≫ U.hom = a ≫ qq k k₁) (hv : v ≫ U.hom = a ≫ qq k k₁) (hb : a ≫ qq k k₁ = b ≫ qq k k₁)
    (h : pullback.lift u a hu ≫ π₁.left = pullback.lift v a hv ≫ π₁.left) :
    pullback.lift u b (hu.trans hb) ≫ π₁.left = pullback.lift v b (hv.trans hb) ≫ π₁.left := by
  obtain ⟨ra, hra⟩ := exists_ext_point (k := k) (k₁ := k₁) L a
  obtain ⟨rb, hrb⟩ := exists_ext_point (k := k) (k₁ := k₁) L b
  have hua : u ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) := by
    rw [hu, ← hra, Category.assoc, q₂_qq]
  have hva : v ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) := by
    rw [hv, ← hra, Category.assoc, q₂_qq]
  have hbb : Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) := by
    rw [← q₂_qq (k₁ := k₁), ← Category.assoc, hra, hb, ← hrb, Category.assoc]
  have hab : ra.comp (φbar k) = rb.comp (φbar k) := by
    have := hbb
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at this
    have := Spec.map_injective this
    exact congrArg CommRingCat.Hom.hom this
  have hlift : ∀ (w : Spec (CommRingCat.of L) ⟶ U.left) (ρ : AlgebraicClosure k →+* L)
      (x : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁)) (hρ : Spec.map (CommRingCat.ofHom ρ) ≫ q₂ k k₁ = x)
      (hw : w ≫ U.hom = x ≫ qq k k₁) (hw' : w ≫ U.hom = Spec.map (CommRingCat.ofHom ρ) ≫ sφ (φbar k)),
      pullback.lift w x hw ≫ π₁.left = (pullback.lift w _ hw' ≫ π'.left) ≫ c := by
    intro w ρ x hρ hw hw'
    rw [Category.assoc, hcompat, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp
    · simp [hρ]
  have hst : ∀ (w : Spec (CommRingCat.of L) ⟶ U.left) (ρ : AlgebraicClosure k →+* L)
      (hw' : w ≫ U.hom = Spec.map (CommRingCat.ofHom ρ) ≫ sφ (φbar k)),
      (pullback.lift w _ hw' ≫ π'.left) ≫ B'.X.hom = Spec.map (CommRingCat.ofHom ρ) := by
    intro w ρ hw'
    rw [Category.assoc, Over.w π']
    exact pullback.lift_snd _ _ _
  have hk : pullback.lift u _ hua ≫ π'.left = pullback.lift v _ hva ≫ π'.left := by
    apply hc.hom_ext
    · rw [← hlift u ra a hra hu hua, ← hlift v ra a hra hv hva, h]
    · rw [hst, hst]
  have hk2 := kbar_KI π' hπ r e he_ker he_nat L ra rb hab u v hua hva hbb hk
  rw [hlift u rb b hrb (hu.trans hb) (hua.trans hbb), hlift v rb b hrb (hv.trans hb) (hva.trans hbb), hk2]

theorem fpqc_specField (L M : Type) [Field L] [Field M] [Algebra L M] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap L M))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap L M))) := by
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap L M))).mpr
    ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance)
  exact h

theorem lift_comp_left {X Y S Z' Z : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (ρ : Z' ⟶ Z) (x : Z ⟶ X) (y : Z ⟶ Y)
    (h : x ≫ f = y ≫ g) :
    pullback.lift (ρ ≫ x) (ρ ≫ y) (by rw [Category.assoc, Category.assoc, h]) = ρ ≫ pullback.lift x y h := by
  apply pullback.hom_ext <;> simp

/-- `KI` at points with values in any field (pass to an algebraic closure). -/
theorem field_KI [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)]
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left)
    (L : Type) [Field L] (u v : Spec (CommRingCat.of L) ⟶ U.left)
    (a b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁))
    (hu : u ≫ U.hom = a ≫ qq k k₁) (hv : v ≫ U.hom = a ≫ qq k k₁) (hb : a ≫ qq k k₁ = b ≫ qq k k₁)
    (h : pullback.lift u a hu ≫ π₁.left = pullback.lift v a hv ≫ π₁.left) :
    pullback.lift u b (hu.trans hb) ≫ π₁.left = pullback.lift v b (hv.trans hb) ≫ π₁.left := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))
  obtain ⟨hfl, hsu⟩ := fpqc_specField L (AlgebraicClosure L)
  haveI : Flat ρ := hfl
  haveI : Surjective ρ := hsu
  haveI : QuasiCompact ρ := inferInstance
  rw [← cancel_epi ρ, ← Category.assoc, ← Category.assoc,
    ← lift_comp_left U.hom (qq k k₁) ρ u b (hu.trans hb), ← lift_comp_left U.hom (qq k k₁) ρ v b (hv.trans hb)]
  refine algclosed_KI π' hπ r e he_ker he_nat X₁ π₁ c hc hcompat (AlgebraicClosure L) (ρ ≫ u) (ρ ≫ v)
    (ρ ≫ a) (ρ ≫ b) (by rw [Category.assoc, hu, ← Category.assoc])
    (by rw [Category.assoc, hv, ← Category.assoc]) (by rw [Category.assoc, hb, ← Category.assoc]) ?_
  rw [lift_comp_left U.hom (qq k k₁) ρ u a hu, lift_comp_left U.hom (qq k k₁) ρ v a hv, Category.assoc,
    Category.assoc, h]

/-- **`KI` for `π₁`**, from the field case, on a smooth (hence reduced) universal source. -/
theorem KI_of [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)]
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left)
    [Smooth π₁.left] [Smooth U.hom] [Smooth (qq k k₁)] [IsSeparated X₁.hom] :
    KI (qq k k₁) π₁ := by
  intro Z u v a b hu hv hb h
  -- the universal source
  let W := pullback U.hom (qq k k₁)
  let Rel := pullback π₁.left π₁.left
  let aR : Rel ⟶ Spec (CommRingCat.of k₁) := pullback.fst π₁.left π₁.left ≫ pullback.snd U.hom (qq k k₁)
  let Z₀ := pullback (aR ≫ qq k k₁) (qq k k₁)
  have haR : pullback.snd π₁.left π₁.left ≫ pullback.snd U.hom (qq k k₁) = aR := by
    have := congrArg (· ≫ X₁.hom) (pullback.condition (f := π₁.left) (g := π₁.left))
    simp only [Category.assoc, w_π₁] at this
    exact this.symm
  let u₀ : Z₀ ⟶ U.left := pullback.fst _ _ ≫ pullback.fst π₁.left π₁.left ≫ pullback.fst U.hom (qq k k₁)
  let v₀ : Z₀ ⟶ U.left := pullback.fst _ _ ≫ pullback.snd π₁.left π₁.left ≫ pullback.fst U.hom (qq k k₁)
  let a₀ : Z₀ ⟶ Spec (CommRingCat.of k₁) := pullback.fst _ _ ≫ aR
  let b₀ : Z₀ ⟶ Spec (CommRingCat.of k₁) := pullback.snd _ _
  have hWc : pullback.fst U.hom (qq k k₁) ≫ U.hom = pullback.snd U.hom (qq k k₁) ≫ qq k k₁ :=
    pullback.condition
  have hu₀ : u₀ ≫ U.hom = a₀ ≫ qq k k₁ := by
    simp only [u₀, a₀, aR, Category.assoc]; rw [hWc]
  have hv₀ : v₀ ≫ U.hom = a₀ ≫ qq k k₁ := by
    simp only [v₀, a₀, Category.assoc]; rw [hWc, ← Category.assoc (pullback.snd π₁.left π₁.left), haR]
  have hb₀ : a₀ ≫ qq k k₁ = b₀ ≫ qq k k₁ := by
    simp only [a₀, b₀, Category.assoc]; exact pullback.condition
  have h₀ : pullback.lift u₀ a₀ hu₀ ≫ π₁.left = pullback.lift v₀ a₀ hv₀ ≫ π₁.left := by
    have e1 : pullback.lift u₀ a₀ hu₀ = pullback.fst _ _ ≫ pullback.fst π₁.left π₁.left := by
      apply pullback.hom_ext <;> simp [u₀, a₀, aR]
    have e2 : pullback.lift v₀ a₀ hv₀ = pullback.fst _ _ ≫ pullback.snd π₁.left π₁.left := by
      apply pullback.hom_ext
      · simp [v₀]
      · simp only [a₀, pullback.lift_snd, Category.assoc]; rw [haR]
    rw [e1, e2]
    simp only [Category.assoc]
    exact congrArg (pullback.fst (aR ≫ qq k k₁) (qq k k₁) ≫ ·) pullback.condition
  -- reducedness of the universal source
  haveI : Smooth (pullback.fst (aR ≫ qq k k₁) (qq k k₁)) := inferInstance
  haveI : Smooth aR := inferInstance
  haveI : Smooth (b₀ ≫ qq k k₁) := by
    rw [← hb₀]; simp only [a₀]; infer_instance
  haveI : IsReduced Z₀ := Smooth.isReduced_of_field (b₀ ≫ qq k k₁)
  -- field tests
  have huniv : pullback.lift u₀ b₀ (hu₀.trans hb₀) ≫ π₁.left = pullback.lift v₀ b₀ (hv₀.trans hb₀) ≫ π₁.left := by
    let src : Over (Spec (CommRingCat.of k₁)) := Over.mk b₀
    let f₁ : src ⟶ X₁ := Over.homMk (pullback.lift u₀ b₀ (hu₀.trans hb₀) ≫ π₁.left) (by
      change (pullback.lift u₀ b₀ _ ≫ π₁.left) ≫ X₁.hom = b₀
      rw [Category.assoc, w_π₁, pullback.lift_snd])
    let f₂ : src ⟶ X₁ := Over.homMk (pullback.lift v₀ b₀ (hv₀.trans hb₀) ≫ π₁.left) (by
      change (pullback.lift v₀ b₀ _ ≫ π₁.left) ≫ X₁.hom = b₀
      rw [Category.assoc, w_π₁, pullback.lift_snd])
    haveI : IsReduced src.left := (inferInstance : IsReduced Z₀)
    have := Scheme.over_hom_eq_of_field_tests f₁ f₂ (fun L _ β p => by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, f₁, f₂, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc,
        ← lift_comp_left U.hom (qq k k₁) p.left u₀ b₀ (hu₀.trans hb₀),
        ← lift_comp_left U.hom (qq k k₁) p.left v₀ b₀ (hv₀.trans hb₀)]
      refine field_KI π' hπ r e he_ker he_nat X₁ π₁ c hc hcompat L (p.left ≫ u₀) (p.left ≫ v₀)
        (p.left ≫ a₀) (p.left ≫ b₀) (by rw [Category.assoc, hu₀, ← Category.assoc])
        (by rw [Category.assoc, hv₀, ← Category.assoc]) (by rw [Category.assoc, hb₀, ← Category.assoc]) ?_
      rw [lift_comp_left U.hom (qq k k₁) p.left u₀ a₀ hu₀, lift_comp_left U.hom (qq k k₁) p.left v₀ a₀ hv₀,
        Category.assoc, Category.assoc, h₀])
    exact congrArg (fun z => Over.Hom.left z) this
  -- specialize
  let t : Z ⟶ Z₀ := pullback.lift (pullback.lift (pullback.lift u a hu) (pullback.lift v a hv) h) b (by
    simp only [aR, Category.assoc]; rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hb])
  have := congrArg (t ≫ ·) huniv
  simp only [← Category.assoc] at this
  convert this using 2
  · apply pullback.hom_ext <;> simp [t, u₀, b₀]
  · apply pullback.hom_ext <;> simp [t, v₀, b₀]

end KI1

section Props

open scoped TensorProduct

/-! Descent of properties along field extensions (copied from the vendored CloudW07
`Picard/FieldDescent.lean`, where they are private; Apache-2.0, Axel Delaval, Jie Xu, Shitan Xu). -/

theorem fieldMap_fpqc' (baseField extensionField : Type)
    [Field baseField] [Field extensionField] [Algebra baseField extensionField] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) := by
  have faithfullyFlat :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap baseField extensionField))).mpr
        ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance)
  exact ⟨⟨faithfullyFlat.2, faithfullyFlat.1⟩, inferInstance⟩

theorem exists_commonField' (baseField firstField secondField : Type)
    [Field baseField] [Field firstField] [Field secondField]
    [Algebra baseField firstField] [Algebra baseField secondField] :
    ∃ (commonField : Type) (_ : Field commonField)
      (firstEmbedding : firstField →+* commonField)
      (secondEmbedding : secondField →+* commonField),
      firstEmbedding.comp (algebraMap baseField firstField) =
        secondEmbedding.comp (algebraMap baseField secondField) := by
  obtain ⟨maximalIdeal, maximality⟩ :=
    Ideal.exists_maximal (α := firstField ⊗[baseField] secondField)
  letI := maximality
  refine ⟨_, Ideal.Quotient.field maximalIdeal,
    (Ideal.Quotient.mk maximalIdeal).comp
      (Algebra.TensorProduct.includeLeft : firstField →ₐ[baseField]
        firstField ⊗[baseField] secondField),
    (Ideal.Quotient.mk maximalIdeal).comp
      (Algebra.TensorProduct.includeRight : secondField →ₐ[baseField]
        firstField ⊗[baseField] secondField), ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc,
    AlgHom.comp_algebraMap, AlgHom.comp_algebraMap]

theorem geometricallyIrreducible_of_field_pullback'
    {baseField extensionField : Type} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {source extendedSource : Scheme.{0}}
    {projection : source ⟶ Spec (.of baseField)}
    {extendedProjection : extendedSource ⟶ Spec (.of extensionField)}
    {comparison : extendedSource ⟶ source}
    (square : IsPullback comparison extendedProjection projection
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
    [GeometricallyIrreducible extendedProjection] : GeometricallyIrreducible projection := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing]
  intro testField _ _ fiber firstProjection secondProjection fiberSquare
  obtain ⟨commonField, _, firstEmbedding, secondEmbedding, embeddingsAgree⟩ :=
    exists_commonField' baseField testField extensionField
  let firstMap : Spec (.of commonField) ⟶ Spec (.of testField) :=
    Spec.map (CommRingCat.ofHom firstEmbedding)
  let secondMap : Spec (.of commonField) ⟶ Spec (.of extensionField) :=
    Spec.map (CommRingCat.ofHom secondEmbedding)
  have baseEquation :
      firstMap ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField testField)) =
        secondMap ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)) := by
    simp only [firstMap, secondMap, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, embeddingsAgree]
  have outer := (IsPullback.of_hasPullback secondProjection firstMap).paste_horiz fiberSquare
  rw [baseEquation] at outer
  have geometricSquare : IsPullback
      (square.lift (pullback.fst secondProjection firstMap ≫ firstProjection)
        (pullback.snd secondProjection firstMap ≫ secondMap) (by simpa using outer.w))
      (pullback.snd secondProjection firstMap) extendedProjection secondMap :=
    IsPullback.of_right (by rwa [square.lift_fst]) (square.lift_snd _ _ _) square
  haveI : IrreducibleSpace ↥(Limits.pullback secondProjection firstMap) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace
      (f := extendedProjection) secondMap _ _ geometricSquare
  letI : Algebra testField commonField := firstEmbedding.toAlgebra
  haveI : Surjective firstMap := (fieldMap_fpqc' testField commonField).1.1
  exact (pullback.fst secondProjection firstMap).surjective.irreducibleSpace
    (pullback.fst secondProjection firstMap).continuous

theorem isProper_of_field_pullback'
    {baseField extensionField : Type} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {source extendedSource : Scheme.{0}}
    {projection : source ⟶ Spec (.of baseField)}
    {extendedProjection : extendedSource ⟶ Spec (.of extensionField)}
    {comparison : extendedSource ⟶ source}
    (square : IsPullback comparison extendedProjection projection
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
    [IsProper extendedProjection] : IsProper projection := by
  letI : MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact
  letI : MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
    infer_instance
  letI : MorphismProperty.DescendsAlong (@IsProper : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    rw [isProper_eq]
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper)
    square.flip (fieldMap_fpqc' baseField extensionField) inferInstance

theorem smooth_of_field_pullback'
    {baseField extensionField : Type} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {source extendedSource : Scheme.{0}}
    {projection : source ⟶ Spec (.of baseField)}
    {extendedProjection : extendedSource ⟶ Spec (.of extensionField)}
    {comparison : extendedSource ⟶ source}
    (square : IsPullback comparison extendedProjection projection
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
    [Smooth extendedProjection] : Smooth projection :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    square.flip (fieldMap_fpqc' baseField extensionField) inferInstance

/-- An abelian variety over `K` from one over a field extension `L`, through a pullback square
(proper, smooth, geometrically integral descend). -/
theorem abVar_props_of_field_pullback {K L : Type} [Field K] [Field L] [Algebra K L]
    {X : Over (Spec (CommRingCat.of K))} (B : PkgI3.AbVar L) {c : B.X.left ⟶ X.left}
    (sq : IsPullback c B.X.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    IsProper X.hom ∧ Smooth X.hom ∧ GeometricallyIntegral X.hom := by
  haveI := B.proper
  haveI := B.smooth
  haveI := B.geomInt
  haveI : IsProper X.hom := isProper_of_field_pullback' sq
  haveI : Smooth X.hom := smooth_of_field_pullback' sq
  haveI : GeometricallyIrreducible X.hom := geometricallyIrreducible_of_field_pullback' sq
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Finite sets of a group variety lie in affine opens** (vendored projective embedding). -/
theorem finite_affine_of_grp {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) [GrpObj X]
    [IsProper X.hom] [Smooth X.hom] [GeometricallyIntegral X.hom] :
    ∀ s : Set X.left, s.Finite → ∃ V : X.left.Opens, IsAffineOpen V ∧ s ⊆ V := by
  obtain ⟨coordinates, _, embedding, immersion, overBase⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral X
  haveI := immersion
  haveI : UniversallyClosed
      (embedding ≫ ℙ(coordinates; Spec (.of K)) ↘ Spec (.of K)) := by
    rw [overBase]
    infer_instance
  haveI : UniversallyClosed embedding := UniversallyClosed.of_comp_of_isSeparated embedding
    (ℙ(coordinates; Spec (.of K)) ↘ Spec (.of K))
  haveI : IsClosedImmersion embedding :=
    IsClosedImmersion.of_isPreimmersion embedding embedding.isClosedMap.isClosed_range
  exact exists_isAffineOpen_superset_of_isClosedImmersion embedding

end Props



section GrpQuot

open ZInQ.Contrib.MilneQuasiInverse.Descent.GroupDescent.Construction GrpObj

variable {S : Scheme.{0}}

theorem tensor_left_prop {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] (hf : P f.left) (hg : P g.left) :
    P (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap hf hg (Over.w f).symm (Over.w g).symm

instance flat_tensor {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) [Flat f.left] [Flat g.left] :
    Flat (f ⊗ₘ g).left := tensor_left_prop f g @Flat inferInstance inferInstance
instance surjective_tensor {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) [Surjective f.left]
    [Surjective g.left] : Surjective (f ⊗ₘ g).left :=
  tensor_left_prop f g @Surjective inferInstance inferInstance
instance quasiCompact_tensor {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y) [QuasiCompact f.left]
    [QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left :=
  tensor_left_prop f g @QuasiCompact inferInstance inferInstance

instance flat_id (A : Over S) : Flat (Over.Hom.left (𝟙 A)) := by rw [Over.id_left]; infer_instance
instance surjective_id (A : Over S) : Surjective (Over.Hom.left (𝟙 A)) := by
  rw [Over.id_left]; infer_instance
instance quasiCompact_id (A : Over S) : QuasiCompact (Over.Hom.left (𝟙 A)) := by
  rw [Over.id_left]; infer_instance

variable {U X : Over S} [GrpObj U] (π : U ⟶ X) [Flat π.left] [Surjective π.left] [QuasiCompact π.left]

/-- The relation `π a = π b` is a congruence for the group law of `U`. -/
def Cong : Prop :=
  ∀ (T : Over S) (a b c : T ⟶ U), a ≫ π = b ≫ π →
    (a * c) ≫ π = (b * c) ≫ π ∧ (c * a) ≫ π = (c * b) ≫ π ∧ a⁻¹ ≫ π = b⁻¹ ≫ π

theorem epi_of_fpqc {A B : Over S} (f : A ⟶ B) [Flat f.left] [Surjective f.left] [QuasiCompact f.left] :
    Epi f := by
  haveI := effectiveEpi_over_of_fpqc f
  infer_instance

/-- **A group structure through an fpqc quotient map.** -/
theorem exists_grpObj (hC : Cong π) : ∃ _ : GrpObj X, IsMonHom π := by
  haveI : EffectiveEpi π := effectiveEpi_over_of_fpqc π
  haveI : EffectiveEpi (π ⊗ₘ π) := effectiveEpi_over_of_fpqc (π ⊗ₘ π)
  have hmc : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ U ⊗ U), g₁ ≫ (π ⊗ₘ π) = g₂ ≫ (π ⊗ₘ π) →
      g₁ ≫ μ ≫ π = g₂ ≫ μ ≫ π := by
    intro Z g₁ g₂ hg
    have ha : (g₁ ≫ fst U U) ≫ π = (g₂ ≫ fst U U) ≫ π := by
      have := congrArg (· ≫ fst X X) hg
      simpa only [Category.assoc, tensorHom_fst] using this
    have hb : (g₁ ≫ snd U U) ≫ π = (g₂ ≫ snd U U) ≫ π := by
      have := congrArg (· ≫ snd X X) hg
      simpa only [Category.assoc, tensorHom_snd] using this
    have e₁ : g₁ ≫ μ = (g₁ ≫ fst U U) * (g₁ ≫ snd U U) := by
      rw [Hom.mul_def]; congr 1; ext <;> simp
    have e₂ : g₂ ≫ μ = (g₂ ≫ fst U U) * (g₂ ≫ snd U U) := by
      rw [Hom.mul_def]; congr 1; ext <;> simp
    rw [← Category.assoc, ← Category.assoc, e₁, e₂, (hC _ _ _ _ ha).1, (hC _ _ _ _ hb).2.1]
  have hic : ∀ {Z : Over S} (a b : Z ⟶ U), a ≫ π = b ≫ π → a ≫ ι ≫ π = b ≫ ι ≫ π := by
    intro Z a b hab
    have := (hC _ a b a hab).2.2
    rwa [Hom.inv_def, Hom.inv_def, Category.assoc, Category.assoc] at this
  let m : X ⊗ X ⟶ X := EffectiveEpi.desc (π ⊗ₘ π) (μ ≫ π) (fun g₁ g₂ hg => hmc g₁ g₂ hg)
  let i : X ⟶ X := EffectiveEpi.desc π (ι ≫ π) (fun a b hab => hic a b hab)
  have hm : (π ⊗ₘ π) ≫ m = μ ≫ π := EffectiveEpi.fac _ _ _
  have hi : π ≫ i = ι ≫ π := EffectiveEpi.fac _ _ _
  haveI : Epi π := inferInstance
  haveI : Epi (π ⊗ₘ π) := inferInstance
  haveI : Epi ((π ⊗ₘ π) ⊗ₘ π) := epi_of_fpqc _
  haveI : Epi (𝟙 (𝟙_ (Over S)) ⊗ₘ π) := epi_of_fpqc _
  haveI : Epi (π ⊗ₘ 𝟙 (𝟙_ (Over S))) := epi_of_fpqc _
  letI G : GrpObj X :=
    { one := η ≫ π
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_epi (𝟙 (𝟙_ (Over S)) ⊗ₘ π), ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id,
          show (η ≫ π) ⊗ₘ π = (η ⊗ₘ 𝟙 U) ≫ (π ⊗ₘ π) by rw [tensorHom_comp_tensorHom, Category.id_comp],
          Category.assoc, hm, ← Category.assoc, tensorHom_id, MonObj.one_mul, id_tensorHom,
          leftUnitor_naturality]
      mul_one := by
        rw [← cancel_epi (π ⊗ₘ 𝟙 (𝟙_ (Over S))), ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id,
          show π ⊗ₘ (η ≫ π) = (𝟙 U ⊗ₘ η) ≫ (π ⊗ₘ π) by rw [tensorHom_comp_tensorHom, Category.id_comp],
          Category.assoc, hm, ← Category.assoc, id_tensorHom, MonObj.mul_one, tensorHom_id,
          rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_epi ((π ⊗ₘ π) ⊗ₘ π)]
        conv_lhs => rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id, hm,
          show (μ ≫ π) ⊗ₘ π = (μ ⊗ₘ 𝟙 U) ≫ (π ⊗ₘ π) by rw [tensorHom_comp_tensorHom, Category.id_comp],
          Category.assoc, hm, ← Category.assoc, tensorHom_id, MonObj.mul_assoc]
        conv_rhs => rw [associator_naturality_assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.comp_id, hm,
          show π ⊗ₘ (μ ≫ π) = (𝟙 U ⊗ₘ μ) ≫ (π ⊗ₘ π) by rw [tensorHom_comp_tensorHom, Category.id_comp],
          Category.assoc, hm, id_tensorHom]
        simp only [Category.assoc]
      left_inv := by
        rw [← cancel_epi π]
        rw [← Category.assoc, show π ≫ lift i (𝟙 X) = lift ι (𝟙 U) ≫ (π ⊗ₘ π) by ext <;> simp [hi]]
        rw [Category.assoc, hm, ← Category.assoc, GrpObj.left_inv]
        simp
      right_inv := by
        rw [← cancel_epi π]
        rw [← Category.assoc, show π ≫ lift (𝟙 X) i = lift (𝟙 U) ι ≫ (π ⊗ₘ π) by ext <;> simp [hi]]
        rw [Category.assoc, hm, ← Category.assoc, GrpObj.right_inv]
        simp }
  exact ⟨G, ⟨rfl, hm.symm⟩⟩

end GrpQuot


section GrpTransfer

open ZInQ.Contrib.MilneQuasiInverse.Descent.GroupDescent.Construction

theorem isMonHom_pullbackComp {S S' S'' : Scheme.{0}} (f : S'' ⟶ S') (g : S' ⟶ S) (U : Over S) [GrpObj U] :
    letI : GrpObj ((Over.pullback (f ≫ g)).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback g).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj U)) := Functor.grpObjObj
    let ε : (Over.pullback (f ≫ g)).obj U ⟶ (Over.pullback f).obj ((Over.pullback g).obj U) :=
      (Over.pullbackComp f g).hom.app U
    IsMonHom ε := by
  letI : GrpObj ((Over.pullback (f ≫ g)).obj U) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback g).obj U) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj U)) := Functor.grpObjObj
  let M : Mon (Over S) := Mon.mk U
  let A := ((Functor.mapMonNatIso (Over.pullbackComp f g)).hom.app M)
  let B := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).hom.app M)
  have h3 := (A ≫ B).isMonHom_hom
  intro ε
  convert h3 using 1 <;> (try rfl)

theorem isMonHom_pullbackEq {S S' : Scheme.{0}} (a b : S' ⟶ S) (h : a = b) (U : Over S) [GrpObj U] :
    letI : GrpObj ((Over.pullback a).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback b).obj U) := Functor.grpObjObj
    IsMonHom (Over.homMk (pullback.map U.hom a U.hom b (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]))
      (by simp) : (Over.pullback a).obj U ⟶ (Over.pullback b).obj U) := by
  subst h
  letI : GrpObj ((Over.pullback a).obj U) := Functor.grpObjObj
  convert (inferInstance : IsMonHom (𝟙 ((Over.pullback a).obj U)))
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp

/-- **The congruence condition from a faithful monoidal base change** onto a homomorphism. -/
theorem cong_of_faithful {S S' : Scheme.{0}} (G : Over S ⥤ Over S') [G.Monoidal] [G.Faithful]
    {U X : Over S} [GrpObj U] (π : U ⟶ X) {B : Over S'} [GrpObj B] (θ : G.obj X ≅ B)
    (hθ : letI : GrpObj (G.obj U) := Functor.grpObjObj; IsMonHom (G.map π ≫ θ.hom)) : Cong π := by
  letI : GrpObj (G.obj U) := Functor.grpObjObj
  haveI := hθ
  intro T a b c hab
  have hG : G.map a ≫ G.map π ≫ θ.hom = G.map b ≫ G.map π ≫ θ.hom := by
    rw [← Category.assoc, ← G.map_comp, hab, G.map_comp, Category.assoc]
  have key : ∀ x y : T ⟶ U, G.map (x ≫ π) = G.map (y ≫ π) ↔ G.map x ≫ G.map π ≫ θ.hom = G.map y ≫ G.map π ≫ θ.hom := by
    intro x y
    constructor
    · intro h; rw [← Category.assoc, ← G.map_comp, h, G.map_comp, Category.assoc]
    · intro h
      have := congrArg (· ≫ θ.inv) h
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at this
      rw [G.map_comp, G.map_comp, this]
  refine ⟨G.map_injective ((key _ _).mpr ?_), G.map_injective ((key _ _).mpr ?_),
    G.map_injective ((key _ _).mpr ?_)⟩
  · rw [Functor.map_mul, Functor.map_mul, MonObj.mul_comp, MonObj.mul_comp, hG]
  · rw [Functor.map_mul, Functor.map_mul, MonObj.mul_comp, MonObj.mul_comp, hG]
  · rw [Functor.map_inv', Functor.map_inv', GrpObj.inv_comp, GrpObj.inv_comp, hG]

end GrpTransfer

section FSD

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}
  {k₁ : Type} [Field k₁] [Algebra k k₁] [Algebra k₁ (AlgebraicClosure k)]
  [IsScalarTower k k₁ (AlgebraicClosure k)]

omit [GrpObj U] in
theorem isPullback_rr :
    IsPullback (pullback.snd U.hom (sφ (φbar k))) (rr U k₁) (q₂ k k₁) (pullback.snd U.hom (qq k k₁)) := by
  have big := IsPullback.of_hasPullback U.hom (sφ (φbar k))
  have W := IsPullback.of_hasPullback U.hom (qq k k₁)
  refine IsPullback.of_bot (h₃₁ := U.hom) (v₂₁ := pullback.fst U.hom (qq k k₁)) (v₂₂ := qq k k₁) ?_ ?_ W.flip
  · have e1 : rr U k₁ ≫ pullback.fst U.hom (qq k k₁) = pullback.fst U.hom (sφ (φbar k)) := by simp [rr]
    rw [e1, q₂_qq]; exact big.flip
  · simp [rr]

theorem isPullback_π' (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    {X₁ : Over (Spec (CommRingCat.of k₁))} (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left) :
    IsPullback π'.left (rr U k₁) c π₁.left := by
  refine IsPullback.of_right (h₁₂ := B'.X.hom) (h₂₂ := X₁.hom) (v₁₃ := q₂ k k₁) ?_ hcompat hc.flip
  rw [Over.w π', Over.w π₁]
  exact isPullback_rr

/-- `U_{k₁} ×_{k₁} k̄ → U_{k̄}`. -/
noncomputable def Ecomp (U : Over (Spec (CommRingCat.of k))) (k₁ : Type) [Field k₁] [Algebra k k₁]
    [Algebra k₁ (AlgebraicClosure k)] [IsScalarTower k k₁ (AlgebraicClosure k)] :
    (Over.pullback (q₂ k k₁)).obj ((Over.pullback (qq k k₁)).obj U) ⟶
      (Over.pullback (sφ (φbar k))).obj U :=
  (((Over.pullbackComp (q₂ k k₁) (qq k k₁)).app U).inv : (Over.pullback (q₂ k k₁)).obj
      ((Over.pullback (qq k k₁)).obj U) ⟶ (Over.pullback (q₂ k k₁ ≫ qq k k₁)).obj U) ≫
    Over.homMk (pullback.map U.hom (q₂ k k₁ ≫ qq k k₁) U.hom (sφ (φbar k)) (𝟙 _) (𝟙 _) (𝟙 _) (by simp)
      (by simp [q₂_qq])) (by simp)

theorem isMonHom_Ecomp :
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (qq k k₁)).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (q₂ k k₁)).obj ((Over.pullback (qq k k₁)).obj U)) := Functor.grpObjObj
    IsMonHom (Ecomp U k₁) := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (qq k k₁)).obj U) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (q₂ k k₁)).obj ((Over.pullback (qq k k₁)).obj U)) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (q₂ k k₁ ≫ qq k k₁)).obj U) := Functor.grpObjObj
  let iota : (Over.pullback (q₂ k k₁ ≫ qq k k₁)).obj U ≅
      (Over.pullback (q₂ k k₁)).obj ((Over.pullback (qq k k₁)).obj U) :=
    (Over.pullbackComp (q₂ k k₁) (qq k k₁)).app U
  haveI : IsMonHom iota.hom := isMonHom_pullbackComp (q₂ k k₁) (qq k k₁) U
  haveI : IsMonHom iota.inv := inferInstance
  haveI := isMonHom_pullbackEq (q₂ k k₁ ≫ qq k k₁) (sφ (φbar k)) q₂_qq U
  exact CategoryTheory.instIsMonHomComp _ _

theorem Ecomp_left_rr :
    (Ecomp U k₁).left ≫ rr U k₁ = pullback.fst (pullback.snd U.hom (qq k k₁)) (q₂ k k₁) := by
  have hv := Over.pullbackComp_hom_app_left_fst_fst (q₂ k k₁) (qq k k₁) U
  have hinv : ((Over.pullbackComp (q₂ k k₁) (qq k k₁)).app U).inv.left ≫
      pullback.fst U.hom (q₂ k k₁ ≫ qq k k₁) =
      pullback.fst (pullback.snd U.hom (qq k k₁)) (q₂ k k₁) ≫ pullback.fst U.hom (qq k k₁) := by
    rw [← hv, ← Category.assoc, ← Over.comp_left, ← Iso.app_hom, Iso.inv_hom_id]
    simp
  apply pullback.hom_ext
  · simp only [Ecomp, Over.comp_left, Category.assoc, rr, pullback.lift_fst, Over.homMk_left,
      Category.comp_id]
    exact hinv
  · simp only [Category.assoc, rr, pullback.lift_snd]
    have := Over.w (Ecomp U k₁)
    change (Ecomp U k₁).left ≫ pullback.snd U.hom (sφ (φbar k)) =
      pullback.snd (pullback.snd U.hom (qq k k₁)) (q₂ k k₁) at this
    rw [reassoc_of% this, ← pullback.condition]

omit [GrpObj U] [IsScalarTower k k₁ (AlgebraicClosure k)] in
theorem qq_props [PerfectField k] [FiniteDimensional k k₁] :
    IsFinite (qq k k₁) ∧ Flat (qq k k₁) ∧ Surjective (qq k k₁) ∧
      LocallyOfFinitePresentation (qq k k₁) ∧ Smooth (qq k k₁) := by
  have hf := fieldMap_fpqc' k k₁
  haveI : IsFinite (qq k k₁) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  haveI : Algebra.IsSeparable k k₁ := inferInstance
  haveI : Algebra.FormallyEtale k k₁ := Algebra.FormallyEtale.of_isSeparable k k₁
  haveI : Algebra.FinitePresentation k k₁ := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Smooth k k₁ := ⟨inferInstance, inferInstance⟩
  refine ⟨inferInstance, hf.1.2, hf.1.1, ?_, ?_⟩
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
        (inferInstanceAs (LocallyOfFiniteType (qq k k₁))))
  · rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    change RingHom.Smooth (algebraMap k k₁)
    rw [RingHom.smooth_algebraMap]
    infer_instance

/-- **Step F: descent of the quotient from a finite-stage model.** -/
theorem fsd [PerfectField k] [FiniteDimensional k k₁] [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)]
    (hsm : Smooth U.hom) (hqcU : QuasiCompact U.hom)
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π')
    (hfl : Flat π'.left) (hsu : Surjective π'.left) (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left) :
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X),
      letI : GrpObj ((Over.pullback (sφ (φbar k))).obj B.X) := Functor.grpObjObj
      IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
        (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
        letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
        u ≫ (Over.pullback (sφ (φbar k))).map π = 1 ↔ u ≫ π' = 1 := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI := B'.grp
  haveI := hπ
  haveI := hsm
  haveI := hqcU
  haveI := hfl
  haveI := hsu
  haveI := B'.proper
  haveI := B'.smooth
  haveI := B'.geomInt
  -- (1) `π'` is smooth
  have hker := isSmoothConnAffineKer_of_torus π' r e he_inj he_ker he_nat
  haveI : QuasiCompact π'.left := by
    haveI : QuasiCompact (π'.left ≫ B'.X.hom) := by
      rw [Over.w π']; change QuasiCompact (pullback.snd U.hom _); infer_instance
    exact QuasiCompact.of_comp π'.left B'.X.hom
  have hsmπ' : Smooth π'.left := by
    have hP := (isPullback_shear π').map (Over.forget _)
    have hfst : Smooth ((Over.forget _).map (fst ((Over.pullback (sφ (φbar k))).obj U) (kerObj π'))) := by
      haveI := hker.1
      change Smooth (pullback.fst _ (kerObj π').hom); infer_instance
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hP ⟨⟨hsu, hfl⟩, (inferInstance : QuasiCompact π'.left)⟩ hfst
  -- (2) `π₁` and `X₁`
  have sqπ := isPullback_π' π' π₁ c hc hcompat
  have hq₂ := fieldMap_fpqc' k₁ (AlgebraicClosure k)
  have hcQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) c :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hc.flip hq₂.1.1,
      MorphismProperty.of_isPullback (P := @Flat) hc.flip hq₂.1.2⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) hc.flip hq₂.2⟩
  haveI : Smooth π₁.left := MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sqπ hcQ hsmπ'
  haveI : Surjective π₁.left := MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sqπ hcQ hsu
  obtain ⟨hX₁p, hX₁s, hX₁g⟩ := abVar_props_of_field_pullback B' hc
  haveI := hX₁p
  haveI := hX₁s
  haveI := hX₁g
  haveI : QuasiCompact π₁.left := by
    haveI : QuasiCompact (π₁.left ≫ X₁.hom) := by
      rw [Over.w π₁]; change QuasiCompact (pullback.snd U.hom _); infer_instance
    exact QuasiCompact.of_comp π₁.left X₁.hom
  -- (3) group structure on `X₁`
  letI : GrpObj ((Over.pullback (qq k k₁)).obj U) := Functor.grpObjObj
  let θ₁ : (Over.pullback (q₂ k k₁)).obj X₁ ≅ B'.X := Over.isoMk hc.isoPullback.symm (by simp)
  have hθ₁eq : (Over.pullback (q₂ k k₁)).map π₁ ≫ θ₁.hom = Ecomp U k₁ ≫ π' := by
    apply Over.OverMorphism.ext
    apply hc.hom_ext
    · simp only [Over.comp_left, Category.assoc, θ₁, Over.isoMk_hom_left, Iso.symm_hom,
        IsPullback.isoPullback_inv_fst, Over.pullback_map_left, pullback.lift_fst]
      rw [hcompat, ← Category.assoc, Ecomp_left_rr]
      rfl
    · rw [Over.w, Over.w]
  have hθ₁ : letI : GrpObj ((Over.pullback (q₂ k k₁)).obj ((Over.pullback (qq k k₁)).obj U)) :=
      Functor.grpObjObj
      IsMonHom ((Over.pullback (q₂ k k₁)).map π₁ ≫ θ₁.hom) := by
    letI : GrpObj ((Over.pullback (q₂ k k₁)).obj ((Over.pullback (qq k k₁)).obj U)) := Functor.grpObjObj
    rw [hθ₁eq]
    haveI := isMonHom_Ecomp (U := U) (k₁ := k₁)
    infer_instance
  obtain ⟨GX₁, hπ₁m⟩ := exists_grpObj π₁ (cong_of_faithful (Over.pullback (q₂ k k₁)) π₁ θ₁ hθ₁)
  -- (4) `KI` and finiteness
  obtain ⟨hqfin, hqfl, hqsu, hqlfp, hqsm⟩ := qq_props (k := k) (k₁ := k₁)
  haveI := hqfin
  haveI := hqfl
  haveI := hqsu
  haveI := hqlfp
  haveI := hqsm
  have hKI := KI_of π' hπ r e he_ker he_nat X₁ π₁ c hc hcompat
  have hfin := @finite_affine_of_grp k₁ _ X₁ GX₁ _ _ _
  -- (5) descent
  obtain ⟨B₀, d, πr, hsq, hfac, hover⟩ := exists_descent hKI hfin
  let πo : U ⟶ B₀ := Over.homMk πr hover
  have sq2 : IsPullback π₁.left (pullback.fst U.hom (qq k k₁)) d πr := by
    refine IsPullback.of_right (h₁₂ := X₁.hom) (h₂₂ := B₀.hom) (v₁₃ := qq k k₁) ?_ hfac.symm hsq.flip
    rw [Over.w π₁, hover]
    exact (IsPullback.of_hasPullback U.hom (qq k k₁)).flip
  have hq := fieldMap_fpqc' k k₁
  have hdQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) d :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hq.1.1,
      MorphismProperty.of_isPullback (P := @Flat) hsq.flip hq.1.2⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hq.2⟩
  haveI : Smooth πr := MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq2 hdQ inferInstance
  haveI : Surjective πr := MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq2 hdQ inferInstance
  let X₁v : PkgI3.AbVar k₁ := @PkgI3.AbVar.mk k₁ _ X₁ GX₁ _ _ _
  obtain ⟨hBp, hBs, hBg⟩ := abVar_props_of_field_pullback (X := B₀) X₁v hsq
  haveI := hBp
  haveI := hBs
  haveI := hBg
  haveI : QuasiCompact πo.left := by
    haveI : QuasiCompact (πr ≫ B₀.hom) := by rw [hover]; infer_instance
    exact QuasiCompact.of_comp πr B₀.hom
  haveI : Flat πo.left := (inferInstance : Flat πr)
  haveI : Surjective πo.left := (inferInstance : Surjective πr)
  -- (6) comparison with `B'`
  have hpaste : IsPullback (c ≫ d) B'.X.hom B₀.hom (sφ (φbar k)) := by
    have := hc.paste_horiz hsq
    rwa [q₂_qq] at this
  let Θ : (Over.pullback (sφ (φbar k))).obj B₀ ≅ B'.X := Over.isoMk hpaste.isoPullback.symm (by simp)
  have hΘ : (Over.pullback (sφ (φbar k))).map πo ≫ Θ.hom = π' := by
    apply Over.OverMorphism.ext
    apply hpaste.hom_ext
    · simp only [Over.comp_left, Category.assoc, Θ, Over.isoMk_hom_left, Iso.symm_hom]
      rw [IsPullback.isoPullback_inv_fst, ← Category.assoc π'.left, hcompat, Category.assoc, ← hfac,
        ← Category.assoc]
      simp only [Over.pullback_map_left, pullback.lift_fst, πo, Over.homMk_left]
      congr 1
    · rw [Over.w, Over.w]
  have hθB : IsMonHom ((Over.pullback (sφ (φbar k))).map πo ≫ Θ.hom) := by rw [hΘ]; exact hπ
  obtain ⟨GB₀, hπom⟩ := exists_grpObj πo (cong_of_faithful (Over.pullback (sφ (φbar k))) πo Θ hθB)
  let B : PkgI3.AbVar k := @PkgI3.AbVar.mk k _ B₀ GB₀ _ _ _
  refine ⟨B, πo, hπom, inferInstance, inferInstance, ?_⟩
  -- (7) the kernel condition
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj B.X) := Functor.grpObjObj
  intro R _ _ u
  have h1 : (Over.pullback (sφ (φbar k))).map πo = π' ≫ Θ.inv := by
    rw [← hΘ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hη : (η[(Over.pullback (sφ (φbar k))).obj B.X] : 𝟙_ _ ⟶ _) = η[B'.X] ≫ Θ.inv := by
    haveI : IsMonHom ((Over.pullback (sφ (φbar k))).map πo) := inferInstance
    rw [← IsMonHom.one_hom ((Over.pullback (sφ (φbar k))).map πo), h1, ← Category.assoc,
      IsMonHom.one_hom π']
  have hone : (1 : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj B.X) =
      (1 : algPt (AlgebraicClosure k) R ⟶ B'.X) ≫ Θ.inv := by
    rw [Hom.one_def, Hom.one_def, Category.assoc, hη]
  rw [h1, hone, ← Category.assoc, cancel_mono]

end FSD

section Spread

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k]

theorem qq_comp_tower (k₀ k₁ : IntermediateField k (AlgebraicClosure k)) (h : k₀ ≤ k₁) :
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫ qq k k₀ = qq k k₁ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem q₂_comp_tower (k₀ k₁ : IntermediateField k (AlgebraicClosure k)) (h : k₀ ≤ k₁) :
    q₂ k k₁ ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) = q₂ k k₀ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- **Step S: spreading out** `(B', π')` to a finite subextension `k₁ ⊆ k̄`. -/
theorem spread (U : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (B' : PkgI3.AbVar (AlgebraicClosure k)) (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X) :
    ∃ (k₁ : IntermediateField k (AlgebraicClosure k)) (_ : FiniteDimensional k k₁)
      (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
      (c : B'.X.left ⟶ X₁.left),
      IsPullback c B'.X.hom X₁.hom (q₂ k k₁) ∧ π'.left ≫ c = rr U k₁ ≫ π₁.left := by
  haveI := B'.proper
  haveI := B'.smooth
  -- (1) spread `B'`
  obtain ⟨k₀, X₀, X₀m, h₁, h₂, h₃, c₀, hc₀⟩ := exists_finiteSubext_isPullback (baseField := k) B'.X.hom
  -- (2) the inverse system `U ×_k k_i`, `k_i ⊇ k₀`
  let D₀ := (IntermediateField.subextDiagram k (AlgebraicClosure k)).op ⋙ Scheme.Spec
  let C₀ := subextSpecCone k (AlgebraicClosure k)
  have hC₀ := isLimitSubextSpecCone k (AlgebraicClosure k)
  let U₀ := pullback U.hom (qq k k₀.1)
  let stageMap : U₀ ⟶ D₀.obj (Opposite.op k₀) := pullback.snd U.hom (qq k k₀.1)
  haveI : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  haveI : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  haveI : QuasiSeparatedSpace U.left := inferInstance
  haveI : CompactSpace U₀ := QuasiCompact.compactSpace_of_compactSpace (pullback.fst U.hom (qq k k₀.1))
  haveI : QuasiSeparatedSpace U₀ := quasiSeparatedSpace_of_quasiSeparated (pullback.fst U.hom (qq k k₀.1))
  haveI hD₀aff : ∀ {i j : (IntermediateField.FiniteSubext k (AlgebraicClosure k))ᵒᵖ} (f : i ⟶ j),
      IsAffineHom (D₀.map f) := fun f => isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  let D := JacobianChallenge.baseChangeDiagram D₀ stageMap
  haveI : ∀ {i j : Over (Opposite.op k₀)} (f : i ⟶ j), IsAffineHom (D.map f) := fun f => inferInstance
  let Cb := JacobianChallenge.baseChangeCone D₀ C₀ stageMap
  have hCb := isLimitBaseChangeCone D₀ C₀ stageMap hC₀
  let t := JacobianChallenge.baseChangeDiagramStructure D₀ stageMap
  have hq₀ : C₀.π.app (Opposite.op k₀) ≫ qq k k₀.1 = sφ (φbar k) := q₂_qq (k₁ := k₀.1)
  -- (3) `Cb.pt ≅ U_{k̄}`
  let ι' : Cb.pt ⟶ pullback U.hom (sφ (φbar k)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst U.hom (qq k k₀.1)) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (pullback.fst stageMap (C₀.π.app (Opposite.op k₀)) ≫ stageMap) ≫ _ = _
      rw [pullback.condition, Category.assoc, hq₀])
  let κ : pullback U.hom (sφ (φbar k)) ⟶ Cb.pt :=
    pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ C₀.π.app (Opposite.op k₀)) (by
      rw [pullback.condition, Category.assoc, hq₀])) (pullback.snd _ _) (by simp [stageMap])
  have hκι : κ ≫ ι' = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [κ, ι']
  let a : Cb.pt ⟶ X₀ := ι' ≫ π'.left ≫ c₀
  have ha : Cb.π ≫ t = (Functor.const _).map (a ≫ X₀m) := by
    ext i
    simp only [NatTrans.comp_app, Functor.const_map_app, t, Cb, a,
      JacobianChallenge.baseChangeDiagramStructure_app, JacobianChallenge.baseChangeCone_π_app,
      pullback.lift_fst_assoc, Category.id_comp]
    rw [Category.comp_id, Category.assoc, Category.assoc, hc₀.w, ← Category.assoc π'.left, Over.w π']
    change _ = ι' ≫ pullback.snd U.hom (sφ (φbar k)) ≫ _
    rw [pullback.lift_snd_assoc]
    exact pullback.condition
  obtain ⟨i, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t X₀m Cb hCb a ha
  -- (4) the finite stage `k₁`
  let k₁ := i.left.unop.1
  have hle : k₀.1 ≤ k₁ := leOfHom i.hom.unop
  let s₀₁ : Spec (CommRingCat.of k₁) ⟶ Spec (CommRingCat.of k₀.1) :=
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hle).toRingHom)
  have hD : D₀.map i.hom = s₀₁ := rfl
  have hCi : C₀.π.app i.left = q₂ k k₁ := rfl
  let X₁ : Over (Spec (CommRingCat.of k₁)) := Over.mk (pullback.snd X₀m s₀₁)
  let jU : pullback U.hom (qq k k₁) ⟶ D.obj i :=
    pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s₀₁) (by
      rw [pullback.condition, Category.assoc, qq_comp_tower _ _ hle]))
      (pullback.snd _ _) (by simp [stageMap, hD])
  have hg2' : g ≫ X₀m = pullback.fst stageMap (D₀.map i.hom) ≫ stageMap := hg2
  let π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁ :=
    Over.homMk (pullback.lift (jU ≫ g) (pullback.snd U.hom (qq k k₁)) (by
      rw [Category.assoc, hg2', ← Category.assoc]
      simp [jU, stageMap, hD])) (by simp [X₁])
  let c : B'.X.left ⟶ X₁.left := pullback.lift c₀ (B'.X.hom ≫ q₂ k k₁) (by
    rw [hc₀.w, Category.assoc, q₂_comp_tower _ _ hle])
  refine ⟨k₁, i.left.unop.2, X₁, π₁, c, ?_, ?_⟩
  · refine IsPullback.of_right (h₁₂ := pullback.fst X₀m s₀₁) (h₂₂ := s₀₁) (v₁₃ := X₀m) ?_ ?_
      (IsPullback.of_hasPullback X₀m s₀₁)
    · rw [pullback.lift_fst, q₂_comp_tower _ _ hle]; exact hc₀
    · exact pullback.lift_snd _ _ _
  · apply pullback.hom_ext
    · have e1 : rr U k₁ ≫ jU = κ ≫ Cb.π.app i := by
        apply pullback.hom_ext
        · apply pullback.hom_ext
          · simp [jU, κ, Cb, rr]
          · simp only [jU, κ, Cb, rr, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd,
              pullback.lift_fst, JacobianChallenge.baseChangeCone_π_app, pullback.lift_snd_assoc]
            rw [Category.id_comp, pullback.lift_snd, q₂_comp_tower _ _ hle]
            rfl
        · simp [jU, κ, Cb, rr, hCi]
      simp only [Category.assoc, c, pullback.lift_fst, π₁, Over.homMk_left]
      rw [← Category.assoc (rr U k₁), e1, Category.assoc, hg1]
      simp only [a, ← Category.assoc, hκι, Category.id_comp]
    · simp only [Category.assoc, c, pullback.lift_snd, π₁, Over.homMk_left, X₁]
      rw [← Category.assoc, Over.w π']
      simp [rr]

end Spread

section Asm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxHeartbeats 20000


/-- **GLUE `QuotientDescendsPerfect`** (descent of the abelian quotient of a semi-abelian group from `k̄` to a
perfect field `k`; the special case of Chevalley's theorem over a perfect field (Conrad 2002 Thm 1.1, Milne AG
8.27, numbers UNVERIFIED) that `semiAbelianDescendsPerfect_of_chevalley` uses). Let `U` be a smooth connected group
scheme of finite type over a perfect field `k`, and let `π' : U_{k̄} → B'` be a faithfully flat homomorphism onto an
abelian variety over `k̄` whose kernel is a split torus (`(Rˣ)^r ≅ ker(U_{k̄}(R) → B'(R))`, naturally in
`k̄`-algebras `R`). Then there is a faithfully flat homomorphism `π : U → B` onto an abelian variety over `k` such
that `π_{k̄}` and `π'` have the same kernel on `R`-points for every `k̄`-algebra `R`. -/
def QuotientDescendsPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (U : Over (Spec (CommRingCat.of k))) [GrpObj U],
    Smooth U.hom → QuasiCompact U.hom → ConnectedSpace U.left →
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    ∀ (B' : PkgI3.AbVar (AlgebraicClosure k)) (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X),
      IsMonHom π' → Flat π'.left → Surjective π'.left →
      ∀ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
          (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U)),
        (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R)) →
        (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
          (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
          u ≫ π' = 1 ↔ u ∈ (e R).range) →
        (∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
          [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
          e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t) →
        ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X),
          letI : GrpObj ((Over.pullback (sφ (φbar k))).obj B.X) := Functor.grpObjObj
          IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
          ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
            (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
            u ≫ (Over.pullback (sφ (φbar k))).map π = 1 ↔ u ≫ π' = 1

open CToPrinted in
theorem semiAbelianDescendsPerfect_of_qd (hQD : QuotientDescendsPerfect) :
    ZInQ.HeightFix.SemiAbelianDescendsPerfect := by
  intro k _ _ G _ _ _ hbar
  have hG : AVGlue.GeomConnOfRationalPoint := geomConnOfRationalPoint_proof
  let φ := φbar k
  let F := Over.pullback (sφ φ)
  letI : GrpObj (F.obj G) := Functor.grpObjObj
  obtain ⟨U', _, inc', hoi', hmh', hcon', B', π', hπm', hfl', hsu', r, e', he_inj', he_ker', he_nat'⟩ :=
    hbar
  haveI := hoi'
  haveI : LocallyOfFiniteType (F.obj G).hom := by
    change LocallyOfFiniteType (pullback.snd G.hom (sφ φ)); infer_instance
  haveI : QuasiCompact (F.obj G).hom := by
    change QuasiCompact (pullback.snd G.hom (sφ φ)); infer_instance
  -- (a) `G⁰` over `k`
  have hW := isSubgroupOpen_W0 G hG
  letI : GrpObj (OpenSub.G0 (W0 G)) := OpenSub.grpG0 hW
  have hinc : IsMonHom (OpenSub.incl (W0 G)) := OpenSub.isMonHom_incl hW
  let U := OpenSub.G0 (W0 G)
  let incl : U ⟶ G := OpenSub.incl (W0 G)
  haveI : IsOpenImmersion incl.left := inferInstanceAs (IsOpenImmersion (W0 G).ι)
  haveI : LocallyOfFiniteType ((W0 G).ι ≫ G.hom) := inferInstance
  haveI : QuasiCompact ((W0 G).ι ≫ G.hom) := quasiCompact_of_openImm incl
  haveI : LocallyOfFiniteType U.hom := inferInstanceAs (LocallyOfFiniteType ((W0 G).ι ≫ G.hom))
  haveI : QuasiCompact U.hom := inferInstanceAs (QuasiCompact ((W0 G).ι ≫ G.hom))
  have hconnU : ConnectedSpace U.left := connectedSpace_W0 G
  letI : GrpObj (F.obj U) := Functor.grpObjObj
  have hconnFU : ConnectedSpace (F.obj U).left :=
    connectedSpace_pullback_idComp hG G (W0 G) rfl (AlgebraicClosure k) (sφ φ)
  haveI : QuasiCompact (F.obj U).hom := by
    change QuasiCompact (pullback.snd U.hom (sφ φ)); infer_instance
  -- (b) `U' = (G⁰)_{k̄}` inside `G_{k̄}`
  let p := pullback.fst G.hom (sφ φ)
  have hsq := pbmap_isPullback (sφ φ) U G incl
  haveI hFinc : IsOpenImmersion (F.map incl).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq (inferInstanceAs (IsOpenImmersion (W0 G).ι))
  have hrangeU : Set.range (F.map incl).left = p ⁻¹' (idCompSet G) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show p ((F.map incl).left y) ∈ idCompSet G
      rw [← Scheme.Hom.comp_apply, ← hsq.w, Scheme.Hom.comp_apply]
      have : incl.left (pullback.fst U.hom (sφ φ) y) ∈ Set.range (W0 G).ι := ⟨_, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    · intro hx
      have hx' : p x ∈ Set.range (W0 G).ι := by rw [Scheme.Opens.range_ι]; exact hx
      obtain ⟨u, hu⟩ := hx'
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := incl.left) (g := p) u x hu
      refine ⟨hsq.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd, hz2]
  let pt : (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k))))).left :=
    (default : Spec (CommRingCat.of (AlgebraicClosure k)))
  let ebar := (η[F.obj G] : 𝟙_ _ ⟶ F.obj G).left pt
  have he1 : ebar ∈ Set.range inc'.left :=
    ⟨(η[U'] : 𝟙_ _ ⟶ U').left pt, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom inc']⟩
  have he2 : ebar ∈ p ⁻¹' idCompSet G := by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, unit_bc_fst, Scheme.Hom.comp_apply]
    exact idCompSet_one G _
  have hclo : IsClopen (p ⁻¹' idCompSet G) :=
    ⟨(isClosed_idCompSet G).preimage p.continuous, (isOpen_idCompSet G).preimage p.continuous⟩
  have hsub1 : Set.range inc'.left ⊆ p ⁻¹' idCompSet G :=
    (isConnected_range inc'.left.continuous).isPreconnected.subset_isClopen hclo ⟨ebar, he1, he2⟩
  have hR'clo : IsClopen (Set.range inc'.left) :=
    ⟨isClosed_range_openSubgroup inc', inc'.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (p ⁻¹' idCompSet G) := by
    rw [← hrangeU]; exact (isConnected_range (F.map incl).left.continuous).isPreconnected
  have hsub2 : p ⁻¹' idCompSet G ⊆ Set.range inc'.left :=
    hpre.subset_isClopen hR'clo ⟨ebar, he2, he1⟩
  have heq : Set.range (F.map incl).left = Set.range inc'.left := by
    rw [hrangeU]; exact hsub2.antisymm hsub1
  let isoS := IsOpenImmersion.isoOfRangeEq (F.map incl).left inc'.left heq
  have hfac : isoS.hom ≫ inc'.left = (F.map incl).left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let φU : F.obj U ≅ U' := Over.isoMk isoS (by
    have h1 : U'.hom = inc'.left ≫ (F.obj G).hom := (Over.w inc').symm
    rw [h1, ← Category.assoc, hfac]; exact Over.w (F.map incl))
  have hφU : φU.hom ≫ inc' = F.map incl := by
    apply Over.OverMorphism.ext; exact hfac
  haveI : Mono inc' := ⟨fun g h hgh => Over.OverMorphism.ext ((cancel_mono inc'.left).mp
    (by simpa using congrArg CommaMorphism.left hgh))⟩
  haveI : IsMonHom (φU.hom ≫ inc') := by rw [hφU]; infer_instance
  haveI : IsMonHom φU.hom := isMonHom_of_comp_mono φU.hom inc'
  haveI : IsMonHom (φU.inv ≫ φU.hom) := by rw [Iso.inv_hom_id]; infer_instance
  haveI : IsMonHom φU.inv := isMonHom_of_comp_mono φU.inv φU.hom
  -- (c) the kernels of `π'` and of `φU ≫ π'` are split tori
  have hkerπ' := isSmoothConnAffineKer_of_torus π' r e' he_inj' he_ker' he_nat'
  let e2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ F.obj U) :=
    fun R _ _ => (IsMonHom.monoidHom φU.inv (algPt _ R)).comp (e' R)
  have he2_apply : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] (t : Fin r → Rˣ),
      e2 R t = e' R t ≫ φU.inv := fun _ _ _ _ => rfl
  have he_inj2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      Function.Injective (e2 R) := by
    intro R _ _ t₁ t₂ h
    rw [he2_apply, he2_apply] at h
    exact he_inj' R ((cancel_mono φU.inv).mp h)
  have he_ker2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ F.obj U), u ≫ (φU.hom ≫ π') = 1 ↔ u ∈ (e2 R).range := by
    intro R _ _ u
    rw [← Category.assoc, he_ker' R (u ≫ φU.hom)]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [he2_apply, ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [he2_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  have he_nat2 : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e2 S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e2 R t := by
    intro R S _ _ _ _ f t
    rw [he2_apply, he2_apply, he_nat', Category.assoc]
  -- (d) smoothness: `U'`, `(G⁰)_{k̄}`, `G⁰`
  haveI : LocallyOfFiniteType U'.hom := by rw [← Over.w inc']; infer_instance
  haveI : QuasiCompact U'.hom := quasiCompact_of_openImm inc'
  haveI : IsLocallyNoetherian U'.left := LocallyOfFiniteType.isLocallyNoetherian U'.hom
  haveI : CompactSpace U'.left := QuasiCompact.compactSpace_of_compactSpace U'.hom
  haveI : IsNoetherian U'.left := {}
  have hsmU' : Smooth U'.hom := smooth_of_smoothKer π' hfl' hsu' inferInstance hkerπ'.1
  have hsmFU : Smooth (F.obj U).hom := by
    rw [← Over.w φU.hom]
    haveI : IsIso φU.hom.left := by change IsIso ((Over.forget _).map φU.hom); infer_instance
    infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (sφ φ) :=
    ⟨⟨⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩, inferInstance⟩, inferInstance⟩
  have hsmU : Smooth U.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := U.hom) (g := sφ φ) hQ hsmFU
  -- (e) descent of the quotient `(B', φU ≫ π')` to `k`
  haveI : IsIso φU.hom.left := by change IsIso ((Over.forget _).map φU.hom); infer_instance
  have hfl2 : Flat (φU.hom ≫ π').left := by
    haveI := hfl'; change Flat (φU.hom.left ≫ π'.left); infer_instance
  have hsu2 : Surjective (φU.hom ≫ π').left := by
    haveI := hsu'; change Surjective (φU.hom.left ≫ π'.left); infer_instance
  obtain ⟨B, π, hπm, hπfl, hπsu, huniq⟩ :=
    hQD k U hsmU inferInstance hconnU B' (φU.hom ≫ π') inferInstance hfl2 hsu2 r e2 he_inj2 he_ker2 he_nat2
  haveI := hπm
  letI : GrpObj (F.obj B.X) := Functor.grpObjObj
  -- (f) assemble
  refine ⟨U, inferInstance, incl, inferInstanceAs (IsOpenImmersion (W0 G).ι), hinc, hconnU, B, π, hπm,
    hπfl, hπsu, r, fun R _ _ => (Φ φ U R).toMonoidHom.comp (e2 R), ?_, ?_, ?_⟩
  · intro R _ _
    exact (Φ φ U R).injective.comp (he_inj2 R)
  · intro R _ _ u
    letI := algK φ R
    have h1 : u ≫ π = 1 ↔ (Φ φ U R).symm u ≫ F.map π = 1 := by
      constructor
      · intro h
        apply (Φ φ B.X R).injective
        rw [Φ_comp, MulEquiv.apply_symm_apply, h, map_one]
      · intro h
        have := congrArg (Φ φ B.X R) h
        rwa [Φ_comp, MulEquiv.apply_symm_apply, map_one] at this
    rw [h1, huniq, he_ker2]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by simp [ht]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at ht
      rw [← ht, MulEquiv.symm_apply_apply]
  · intro R S _ _ _ _ f t
    letI := algK φ R
    letI := algK φ S
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [he_nat2 R S f t, Φ_natural]


end Asm

section Final

/-- The assembly needs `CToPrinted` for the open subgroup `G⁰` (semiab-descend). -/
theorem quotientDescendsPerfect_proof : QuotientDescendsPerfect := by
  intro k _ _ U _ hsm hqc hconn B' π' hπ hfl hsu r e he_inj he_ker he_nat
  haveI := hsm
  haveI := hqc
  haveI : LocallyOfFiniteType U.hom := inferInstance
  obtain ⟨k₁, hfd, X₁, π₁, c, hc, hcompat⟩ := spread U B' π'
  haveI := hfd
  haveI : Algebra.IsAlgebraic k₁ (AlgebraicClosure k) := Algebra.IsAlgebraic.tower_top (K := k) k₁
  exact fsd hsm hqc π' hπ hfl hsu r e he_inj he_ker he_nat X₁ π₁ c hc hcompat

/-- **`SemiAbelianDescendsPerfect` is a theorem** (no Chevalley, no leaf). -/
theorem semiAbelianDescendsPerfect_proof : ZInQ.HeightFix.SemiAbelianDescendsPerfect :=
  semiAbelianDescendsPerfect_of_qd quotientDescendsPerfect_proof

open ZInQ.HeightFix in
/-- **The field `bostLowerBound`** from height-fix's printed leaf and the two textbook fields for T35, with no
`chevalleyPerfect`. -/
theorem bostLowerBound_of_printed_free (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed) :
    ZInQ.HeightSplit.BostLowerBound :=
  bostLowerBound_of_printed hB hUL hMT semiAbelianDescendsPerfect_proof

open ZInQ.HeightFix in
/-- **The field `gaudronRemondThm14`**, likewise. -/
theorem gaudronRemondThm14_of_printed_free (hGR : GaudronRemondThm14Printed)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed) :
    ZInQ.HeightSplit.GaudronRemondThm14 :=
  gaudronRemondThm14_of_printed hGR hUL hMT semiAbelianDescendsPerfect_proof

open ZInQ.HeightFix in
/-- The optional field `javanpeykarBound`, likewise. -/
theorem javanpeykarBound_of_printed_free (hJ : JavanpeykarBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed) :
    ZInQ.HeightSplit.JavanpeykarBound :=
  javanpeykarBound_of_printed hJ hUL hMT semiAbelianDescendsPerfect_proof

open ZInQ.HeightFix in
/-- The optional field `pazukiCor13Upper`, likewise. -/
theorem pazukiCor13Upper_of_printed_free (hP : PazukiCor13UpperPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed) :
    ZInQ.HeightSplit.PazukiCor13Upper :=
  pazukiCor13Upper_of_printed hP hUL hMT semiAbelianDescendsPerfect_proof

end Final

end ZInQ.ChevFree

#print axioms ZInQ.ChevFree.rig_raw
#print axioms ZInQ.ChevFree.torus_kernel_transfer
#print axioms ZInQ.ChevFree.kbar_KI
#print axioms ZInQ.ChevFree.algclosed_KI
#print axioms ZInQ.ChevFree.KI_of
#print axioms ZInQ.ChevFree.cong_of_faithful
#print axioms ZInQ.ChevFree.finite_affine_of_grp
#print axioms ZInQ.ChevFree.Ecomp_left_rr
#print axioms ZInQ.ChevFree.isMonHom_Ecomp
#print axioms ZInQ.ChevFree.isPullback_π'
#print axioms ZInQ.ChevFree.fsd
#print axioms ZInQ.ChevFree.spread
#print axioms ZInQ.ChevFree.semiAbelianDescendsPerfect_proof
#print axioms ZInQ.ChevFree.bostLowerBound_of_printed_free
#print axioms ZInQ.ChevFree.gaudronRemondThm14_of_printed_free
#print axioms ZInQ.ChevFree.torus1_const
#print axioms ZInQ.ChevFree.torusR_const
#print axioms ZInQ.ChevFree.exists_descent
#print axioms ZInQ.ChevFree.exists_grpObj
#print axioms ZInQ.ChevFree.quotientDescendsPerfect_proof
#print axioms ZInQ.ChevFree.javanpeykarBound_of_printed_free
#print axioms ZInQ.ChevFree.pazukiCor13Upper_of_printed_free
