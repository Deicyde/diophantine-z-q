import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Surjectivity

/-! Regularity criterion for rational differentials on a smooth complex curve.

A rational differential is represented by a relative differential on some nonempty open;
two representatives are identified when they agree on a nonempty open. On a coordinate
neighbourhood of local étale coordinates the differential `dt` of the coordinate is a free
generator, so a rational differential there is `h · dt` with `h` in the function field.

* `RationalDifferential.regularAt_iff`: `h · dt` is regular at `x` (for étale coordinates at
  `x`) if and only if `h` is regular at `x`, i.e. lies in the image of the local ring at `x`
  (the valuation condition `v_x(h) ≥ 0`).
* `RationalDifferential.exists_global_of_regularAt`: a rational differential that is regular at
  every closed point is the restriction of a global relative differential.

Both are specialized to the complexified modular curve. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

section General

variable {X : Over (Spec (CommRingCat.of ℂ))}

/-- Restriction of relative differentials. -/
abbrev resD {U V : X.left.Opens} (h : V ≤ U) (s : Γ(X.hom.relativeDifferentials, U)) :
    Γ(X.hom.relativeDifferentials, V) :=
  X.hom.relativeDifferentials.presheaf.map (homOfLE h).op s

/-- Restriction of regular functions. -/
abbrev resO {U V : X.left.Opens} (h : V ≤ U) (a : Γ(X.left, U)) : Γ(X.left, V) :=
  X.left.presheaf.map (homOfLE h).op a

/-- The differential `dt` of the coordinate of local étale coordinates, restricted to a
subopen of the coordinate neighbourhood. -/
abbrev coordDiff [SmoothOfRelativeDimension 1 X.hom] {x : X.left} (D : LocalEtaleCoordinates X 1 x) {V : X.left.Opens}
    (h : V ≤ D.neighborhood) : Γ(X.hom.relativeDifferentials, V) :=
  resD h (X.hom.sectionsD D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)))

theorem resD_resD {U V W : X.left.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (s : Γ(X.hom.relativeDifferentials, U)) :
    resD h₂ (resD h₁ s) = resD (h₂.trans h₁) s := by
  simp only [resD]
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

theorem resO_resO {U V W : X.left.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X.left, U)) :
    resO h₂ (resO h₁ a) = resO (h₂.trans h₁) a := by
  simp only [resO]
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

theorem resD_smul {U V : X.left.Opens} (h : V ≤ U) (a : Γ(X.left, U))
    (s : Γ(X.hom.relativeDifferentials, U)) :
    resD h (a • s) = resO h a • resD h s :=
  Scheme.Modules.map_smul _ _ _ _

variable [SmoothOfRelativeDimension 1 X.hom]

theorem resD_coordDiff {x : X.left} (D : LocalEtaleCoordinates X 1 x) {V W : X.left.Opens}
    (h : V ≤ D.neighborhood) (h' : W ≤ V) :
    resD h' (coordDiff D h) = coordDiff D (h'.trans h) :=
  resD_resD _ _ _

/-- The coordinate differential of the restricted coordinates is the restriction of `dt`. -/
theorem sectionsD_restrictBasicOpen {x y : X.left} (D : LocalEtaleCoordinates X 1 x)
    (g : Γ(X.left, D.neighborhood)) (hy : y ∈ X.left.basicOpen g) :
    X.hom.sectionsD (D.restrictBasicOpen g hy).neighborhood
        ((D.restrictBasicOpen g hy).coordinateAlgHom (MvPolynomial.X 0)) =
      coordDiff D (X.left.basicOpen_le g) :=
  X.hom.sectionsD_map (X.left.basicOpen_le g) _

/-- On a principal subopen of the coordinate neighbourhood containing a point, every
relative differential is uniquely a multiple of `dt`. -/
theorem existsUnique_smul_coordDiff_basicOpen {x y : X.left} (D : LocalEtaleCoordinates X 1 x)
    (g : Γ(X.left, D.neighborhood)) (hy : y ∈ X.left.basicOpen g)
    (ω : Γ(X.hom.relativeDifferentials, X.left.basicOpen g)) :
    ∃! b : Γ(X.left, X.left.basicOpen g), b • coordDiff D (X.left.basicOpen_le g) = ω := by
  have h := (D.restrictBasicOpen g hy).existsUnique_smul_sectionsD ω
  rw [sectionsD_restrictBasicOpen D g hy] at h
  exact h

/-- `dt` is torsion free on every subopen of the coordinate neighbourhood. -/
theorem eq_zero_of_smul_coordDiff_eq_zero {x : X.left} (D : LocalEtaleCoordinates X 1 x)
    {V : X.left.Opens} (hV : V ≤ D.neighborhood) (a : Γ(X.left, V))
    (ha : a • coordDiff D hV = 0) : a = 0 := by
  have hcov (y : V) : ∃ g : Γ(X.left, D.neighborhood),
      X.left.basicOpen g ≤ V ∧ (y : X.left) ∈ X.left.basicOpen g :=
    D.isAffine.exists_basicOpen_le y (hV y.2)
  choose g hgV hyg using hcov
  refine TopCat.Sheaf.eq_of_locally_eq' X.left.sheaf (fun y => X.left.basicOpen (g y)) V
    (fun y => homOfLE (hgV y)) (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyg ⟨y, hy⟩⟩) a 0
    fun y => ?_
  change resO (hgV y) a = resO (hgV y) 0
  have hB : resO (hgV y) a • coordDiff D (X.left.basicOpen_le (g y)) = 0 := by
    rw [← resD_coordDiff D hV (hgV y), ← resD_smul, ha]
    exact map_zero _
  have h0 : (0 : Γ(X.left, X.left.basicOpen (g y))) • coordDiff D (X.left.basicOpen_le (g y)) = 0 :=
    zero_smul _ _
  rw [show resO (hgV y) (0 : Γ(X.left, V)) = 0 from map_zero _]
  exact (existsUnique_smul_coordDiff_basicOpen D (g y) (hyg y) 0).unique hB h0

variable [IsIntegral X.left]

omit [SmoothOfRelativeDimension 1 X.hom] in
theorem genericPoint_mem {U : X.left.Opens} {x : X.left} (hx : x ∈ U) :
    genericPoint X.left ∈ U :=
  ((genericPoint_spec X.left).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

omit [SmoothOfRelativeDimension 1 X.hom] in
theorem inter_nonempty {U V : X.left.Opens} (hU : (U : Set X.left).Nonempty)
    (hV : (V : Set X.left).Nonempty) : ((U ⊓ V : X.left.Opens) : Set X.left).Nonempty :=
  nonempty_preirreducible_inter U.isOpen V.isOpen hU hV

/-- Two relative differentials on an open which agree on a nonempty subopen are equal. -/
theorem eq_of_resD_eq {U V : X.left.Opens} (hVU : V ≤ U) (hV : (V : Set X.left).Nonempty)
    (s s' : Γ(X.hom.relativeDifferentials, U)) (h : resD hVU s = resD hVU s') : s = s' := by
  have hcov (y : U) : ∃ g : Γ(X.left, (localEtaleCoordinates X 1 (y : X.left)).neighborhood),
      X.left.basicOpen g ≤ U ⊓ (localEtaleCoordinates X 1 (y : X.left)).neighborhood ∧
        (y : X.left) ∈ X.left.basicOpen g :=
    (localEtaleCoordinates X 1 (y : X.left)).isAffine.exists_basicOpen_le
      (⟨y, y.2, (localEtaleCoordinates X 1 (y : X.left)).mem⟩ :
        ↥(U ⊓ (localEtaleCoordinates X 1 (y : X.left)).neighborhood))
      (localEtaleCoordinates X 1 (y : X.left)).mem
  choose g hgU hyg using hcov
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨X.hom.relativeDifferentials.presheaf,
      X.hom.relativeDifferentials.isSheaf⟩ (fun y => X.left.basicOpen (g y)) U
    (fun y => homOfLE ((hgU y).trans inf_le_left))
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyg ⟨y, hy⟩⟩) s s' fun y => ?_
  let E := localEtaleCoordinates X 1 (y : X.left)
  let W := X.left.basicOpen (g y)
  have hWU : W ≤ U := (hgU y).trans inf_le_left
  have hWE : W ≤ E.neighborhood := X.left.basicOpen_le (g y)
  change resD hWU s = resD hWU s'
  obtain ⟨b, hb, -⟩ := existsUnique_smul_coordDiff_basicOpen E (g y) (hyg y) (resD hWU s)
  obtain ⟨b', hb', -⟩ := existsUnique_smul_coordDiff_basicOpen E (g y) (hyg y) (resD hWU s')
  -- the two coefficients agree on the nonempty open `V ⊓ W`
  have hne : ((V ⊓ W : X.left.Opens) : Set X.left).Nonempty :=
    inter_nonempty hV ⟨y, hyg y⟩
  have h₁ : V ⊓ W ≤ W := inf_le_right
  have h₂ : V ⊓ W ≤ V := inf_le_left
  have hagree : resO h₁ b = resO h₁ b' := by
    have hz : (resO h₁ b - resO h₁ b') • coordDiff E (h₁.trans hWE) = 0 := by
      rw [sub_smul, ← resD_coordDiff E hWE h₁, ← resD_smul, ← resD_smul, hb, hb',
        resD_resD, resD_resD, ← resD_resD hVU h₂, ← resD_resD hVU h₂, h, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul_coordDiff_eq_zero E (h₁.trans hWE) _ hz)
  obtain ⟨z, hz⟩ := hne
  have hbb : b = b' := by
    apply germ_injective_of_isIntegral X.left z hz.2
    have e₁ := TopCat.Presheaf.germ_res_apply X.left.presheaf (homOfLE h₁) z hz b
    have e₂ := TopCat.Presheaf.germ_res_apply X.left.presheaf (homOfLE h₁) z hz b'
    rw [← e₁, ← e₂]
    exact congrArg _ hagree
  rw [← hb, ← hb', hbb]

/-- A rational differential: a relative differential on a nonempty open. -/
structure RationalDifferential (X : Over (Spec (CommRingCat.of ℂ))) where
  /-- The open on which the representative is defined. -/
  dom : X.left.Opens
  nonempty : (dom : Set X.left).Nonempty
  /-- The representative. -/
  sec : Γ(X.hom.relativeDifferentials, dom)

/-- A rational differential is regular at `x` if near `x` it is represented by a
relative differential, agreeing with it on a nonempty open. -/
def RationalDifferential.RegularAt (ω : RationalDifferential X) (x : X.left) : Prop :=
  ∃ U : X.left.Opens, x ∈ U ∧ ∃ s : Γ(X.hom.relativeDifferentials, U),
    ∃ V : X.left.Opens, ∃ hVU : V ≤ U, ∃ hVω : V ≤ ω.dom,
      (V : Set X.left).Nonempty ∧ resD hVU s = resD hVω ω.sec

/-- An element of the function field is regular at `x` (lies in the image of the local ring
at `x`, the condition `v_x(h) ≥ 0`) if it is the generic germ of a regular function on an
open neighbourhood of `x`. -/
def IsRegularFunctionAt (h : X.left.functionField) (x : X.left) : Prop :=
  ∃ U : X.left.Opens, ∃ hx : x ∈ U, ∃ b : Γ(X.left, U),
    X.left.presheaf.germ U (genericPoint X.left) (genericPoint_mem hx) b = h

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- Regularity at `x` is membership in the image of the local ring `𝒪_{X,x}` in the
function field. -/
theorem isRegularFunctionAt_iff (h : X.left.functionField) (x : X.left) :
    IsRegularFunctionAt h x ↔
      h ∈ Set.range (algebraMap (X.left.presheaf.stalk x) X.left.functionField) := by
  have key : ∀ (U : X.left.Opens) (hx : x ∈ U) (b : Γ(X.left, U)),
      algebraMap (X.left.presheaf.stalk x) X.left.functionField (X.left.presheaf.germ U x hx b) =
        X.left.presheaf.germ U (genericPoint X.left) (genericPoint_mem hx) b := by
    intro U hx b
    change (X.left.presheaf.stalkSpecializes _) (X.left.presheaf.germ U x hx b) = _
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.left.presheaf hx _ b
  constructor
  · rintro ⟨U, hx, b, rfl⟩
    exact ⟨_, key U hx b⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨U, hx, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ s
    exact ⟨U, hx, b, (key U hx b).symm⟩

/-- The generic germ of the coefficient `a` of a rational differential `a · dt`. -/
def RationalDifferential.coeffGerm (ω : RationalDifferential X) (a : Γ(X.left, ω.dom)) :
    X.left.functionField :=
  X.left.presheaf.germ ω.dom (genericPoint X.left) (genericPoint_mem ω.nonempty.some_mem) a

/-- **K12 (local criterion).** Let `t` be the coordinate of local étale coordinates at `x`,
so that `dt` freely generates the relative differentials near `x`, and let the rational
differential `ω` be `h · dt` with `h` the generic germ of `a`. Then `ω` is regular at `x`
if and only if `h` is regular at `x`. -/
theorem RationalDifferential.regularAt_iff {x : X.left} (D : LocalEtaleCoordinates X 1 x)
    (ω : RationalDifferential X) (hω : ω.dom ≤ D.neighborhood) (a : Γ(X.left, ω.dom))
    (hωa : ω.sec = a • coordDiff D hω) :
    ω.RegularAt x ↔ IsRegularFunctionAt (ω.coeffGerm a) x := by
  constructor
  · rintro ⟨U, hxU, s, V, hVU, hVω, hVne, hsV⟩
    obtain ⟨g, hgU, hxg⟩ := D.isAffine.exists_basicOpen_le
      (⟨x, hxU, D.mem⟩ : ↥(U ⊓ D.neighborhood)) D.mem
    let W := X.left.basicOpen g
    have hWU : W ≤ U := hgU.trans inf_le_left
    have hWD : W ≤ D.neighborhood := X.left.basicOpen_le g
    obtain ⟨b, hb, -⟩ := existsUnique_smul_coordDiff_basicOpen D g hxg (resD hWU s)
    refine ⟨W, hxg, b, ?_⟩
    have hne : ((V ⊓ W : X.left.Opens) : Set X.left).Nonempty := inter_nonempty hVne ⟨x, hxg⟩
    have h₁ : V ⊓ W ≤ W := inf_le_right
    have h₂ : V ⊓ W ≤ V := inf_le_left
    have h₃ : V ⊓ W ≤ ω.dom := h₂.trans hVω
    have hagree : resO h₁ b = resO h₃ a := by
      have t₁ : resO h₁ b • coordDiff D (h₁.trans hWD) = resD (h₁.trans hWU) s := by
        rw [← resD_coordDiff D hWD h₁, ← resD_smul, hb, resD_resD]
      have t₂ : resO h₃ a • coordDiff D (h₁.trans hWD) = resD h₃ ω.sec := by
        rw [show coordDiff D (h₁.trans hWD) = coordDiff D (h₃.trans hω) from rfl,
          ← resD_coordDiff D hω h₃, ← resD_smul, ← hωa]
      have t₃ : resD (h₁.trans hWU) s = resD h₃ ω.sec := by
        rw [← resD_resD hVU h₂, hsV, resD_resD]
      have hz : (resO h₁ b - resO h₃ a) • coordDiff D (h₁.trans hWD) = 0 := by
        rw [sub_smul, t₁, t₂, t₃, sub_self]
      exact sub_eq_zero.mp (eq_zero_of_smul_coordDiff_eq_zero D (h₁.trans hWD) _ hz)
    have hg := genericPoint_mem (hne.some_mem)
    have e₁ := TopCat.Presheaf.germ_res_apply X.left.presheaf (homOfLE h₁) _ hg b
    have e₂ := TopCat.Presheaf.germ_res_apply X.left.presheaf (homOfLE h₃) _ hg a
    unfold RationalDifferential.coeffGerm
    rw [← e₁, ← e₂]
    exact congrArg _ hagree
  · rintro ⟨U, hxU, b, hb⟩
    obtain ⟨W, hgW, iU, iω, hW⟩ := TopCat.Presheaf.germ_eq X.left.presheaf (genericPoint X.left)
      (genericPoint_mem hxU) (genericPoint_mem ω.nonempty.some_mem) b a hb
    have hWU : W ≤ U ⊓ D.neighborhood := le_inf iU.le (iω.le.trans hω)
    refine ⟨U ⊓ D.neighborhood, ⟨hxU, D.mem⟩, resO (inf_le_left : U ⊓ D.neighborhood ≤ U) b •
        coordDiff D (inf_le_right : U ⊓ D.neighborhood ≤ D.neighborhood),
      W, hWU, iω.le, ⟨_, hgW⟩, ?_⟩
    rw [resD_smul, resO_resO, resD_coordDiff, hωa, resD_smul, resD_coordDiff]
    congr 1

/-- **K12 (global criterion).** A rational differential that is regular at every closed
point is the restriction of a global relative differential. -/
theorem RationalDifferential.exists_global_of_regularAt [LocallyOfFiniteType X.hom]
    (ω : RationalDifferential X) (hreg : ∀ x ∈ closedPoints X.left, ω.RegularAt x) :
    ∃ S : Γ(X.hom.relativeDifferentials, ⊤), resD le_top S = ω.sec := by
  let _ : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let ι := closedPoints X.left
  choose U hxU s V hVU hVω hVne hsV using fun x : ι => hreg x.1 x.2
  have hcov : (⊤ : X.left.Opens) ≤ iSup U := by
    intro y _
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty y).closure
      isClosed_closure.isLocallyClosed
    obtain ⟨_, hyU, rfl⟩ := mem_closure_iff.mp hx (U ⟨x, hxc⟩) (U ⟨x, hxc⟩).isOpen (hxU ⟨x, hxc⟩)
    exact Opens.mem_iSup.mpr ⟨⟨x, hxc⟩, hyU⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.hom.relativeDifferentials.presheaf U s := by
    intro i j
    have hne := inter_nonempty (hVne i) (hVne j)
    have hle : V i ⊓ V j ≤ U i ⊓ U j := inf_le_inf (hVU i) (hVU j)
    apply eq_of_resD_eq hle hne
    change resD hle (resD inf_le_left (s i)) = resD hle (resD inf_le_right (s j))
    rw [resD_resD, resD_resD, ← resD_resD (hVU i) inf_le_left, hsV i, resD_resD,
      ← resD_resD (hVU j) inf_le_right, hsV j, resD_resD]
  obtain ⟨S, hS, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨X.hom.relativeDifferentials.presheaf,
    X.hom.relativeDifferentials.isSheaf⟩ U ⊤ (fun i => homOfLE le_top) hcov s hcompat
  refine ⟨S, ?_⟩
  obtain ⟨x, -, hxc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X.left))
    isOpen_univ.isLocallyClosed
  let i : ι := ⟨x, hxc⟩
  apply eq_of_resD_eq (hVω i) (hVne i)
  rw [← hsV i, resD_resD, ← hS i]
  change _ = resD (hVU i) (resD le_top S)
  rw [resD_resD]

end General

section ModularCurve

variable (N : ℕ) [NeZero N]

/-- **K12** on the complexified modular curve: the local criterion. -/
theorem curveC_regularAt_iff {x : (curveC N).left}
    (D : LocalEtaleCoordinates (curveC N) 1 x) (ω : RationalDifferential (curveC N))
    (hω : ω.dom ≤ D.neighborhood) (a : Γ((curveC N).left, ω.dom))
    (hωa : ω.sec = a • coordDiff D hω) :
    letI := curveC_isIntegral N
    ω.RegularAt x ↔ IsRegularFunctionAt (ω.coeffGerm a) x :=
  letI := curveC_isIntegral N
  RationalDifferential.regularAt_iff D ω hω a hωa

/-- **K12** on the complexified modular curve: regular at every closed point implies global. -/
theorem curveC_exists_global_of_regularAt (ω : RationalDifferential (curveC N))
    (hreg : ∀ x ∈ closedPoints (curveC N).left, ω.RegularAt x) :
    ∃ S : Γ((curveC N).hom.relativeDifferentials, ⊤), resD le_top S = ω.sec := by
  let := curveC_isIntegral N
  have : LocallyOfFiniteType (curveC N).hom := by
    have := SmoothOfRelativeDimension.smooth 1 (curveC N).hom
    infer_instance
  exact ω.exists_global_of_regularAt hreg

end ModularCurve

end ZInQ.Manuscript.RC.CuspFormDifferentials
