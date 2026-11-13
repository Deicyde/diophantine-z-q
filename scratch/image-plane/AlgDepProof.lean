import Mathlib
import ZInQKernel.HDecomp.QM.Pairs

/-!
# image-plane, parts 1-2: (IC) `ImageClosed` and (AD) `AlgDep`

Task image-plane (2026-11-13). The Prop `ImageClosed` is copied verbatim from
`scratch/curve-glue/AlgDep.lean.part`, together with `ptOf`, `Alg.evalXY` and the value
calculus of `scratch/curve-glue/C2K.lean` §1-§2 and the `ToP1` lemmas of its §4 (verbatim).
See `docs/research/image-plane.md`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
open PkgI3

/-- The point of `X` at which a field point `p : Spec K → X` sits. -/
abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1


/-! ## §1 Values of sections at `K`-points -/

section Ev

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- Restriction of sections along `O' ≤ O`, as a ring hom. -/
abbrev res {O O' : X.Opens} (h : O' ≤ O) : Γ(X, O) →+* Γ(X, O') :=
  (X.presheaf.map (homOfLE h).op).hom

theorem res_res {O O' O'' : X.Opens} (h : O' ≤ O) (h' : O'' ≤ O') (s : Γ(X, O)) :
    res h' (res h s) = res (h'.trans h) s := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The value `s(p) ∈ K` of a section `s ∈ Γ(X, O)` at a field point `p` whose point lies in `O`
(the image of `s(x) ∈ κ(x)` under the embedding `κ(x) → K` of `p`; this is how `ToP1.val`
evaluates). -/
def ev (p : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf p ∈ O) : Γ(X, O) →+* K :=
  (X.evaluation O (ptOf p) hx ≫ (Scheme.SpecToEquivOfField K X p).2).hom

theorem ev_res (p : Spec (CommRingCat.of K) ⟶ X) {O O' : X.Opens} (h : O' ≤ O)
    (hx : ptOf p ∈ O') (s : Γ(X, O)) : ev p hx (res h s) = ev p (h hx) s := by
  simp only [ev, res, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  congr 1
  simp only [Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply (X.presheaf.map _), TopCat.Presheaf.germ_res]

theorem ev_eq_zero_iff (p : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf p ∈ O)
    (s : Γ(X, O)) : ev p hx s = 0 ↔ ptOf p ∉ X.basicOpen s := by
  rw [← X.evaluation_eq_zero_iff_notMem_basicOpen (ptOf p) hx s]
  simp only [ev, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  exact map_eq_zero_iff _ (Scheme.SpecToEquivOfField K X p).2.hom.injective

theorem ev_top (p : Spec (CommRingCat.of K) ⟶ X) (s : Γ(X, ⊤)) :
    ev p (show ptOf p ∈ (⊤ : X.Opens) from trivial) s =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (p.appTop s) := by
  have e := Scheme.germ_stalkClosedPointTo p ⊤ trivial
  have e' := congrArg (fun φ => φ.hom s) e
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e'
  simp only [ev, Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (X.residue _ ≫ X.descResidueField (Scheme.stalkClosedPointTo p)).hom
    ((X.presheaf.germ ⊤ _ trivial).hom s) = _
  rw [Scheme.residue_descResidueField, e']
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op, eqToHom_map,
    Scheme.Hom.appTop]
  rfl

/-- The constant section `a ∈ K` on `O`, through the structure morphism `f : X → Spec K`. -/
def cst (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) (a : K) : Γ(X, O) :=
  res le_top (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

theorem ev_cst (f : X ⟶ Spec (CommRingCat.of K)) (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) {O : X.Opens} (hx : ptOf p ∈ O) (a : K) : ev p hx (cst f O a) = a := by
  rw [cst, ev_res, ev_top]
  have h1 : p.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv a := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]; rfl
  rw [h1]; simp

end Ev

/-! ## §2 Closed points are `K`-points; units by values -/

section Units

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [JacobsonSpace X]

theorem exists_point_of_isLocallyClosed {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ Z := by
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne hZ
  have hy : IsClosed ({y} : Set X) := mem_closedPoints_iff.mp hyc
  refine ⟨pointOfClosedPoint f y hy, pointOfClosedPoint_comp f y hy, ?_⟩
  have e : ptOf (pointOfClosedPoint f y hy) = y := pointOfClosedPoint_apply f y hy _
  rw [e]; exact hyZ

/-- A section whose value at every `K`-point of its domain is nonzero is a unit (Jacobson). -/
theorem isUnit_of_ev_ne_zero {O : X.Opens} (s : Γ(X, O))
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O, ev p hx s ≠ 0) :
    IsUnit s := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ O s fun x hx => ?_
  rw [← X.mem_basicOpen s x hx]
  by_contra hb
  obtain ⟨p, hp, hpO, hpb⟩ := exists_point_of_isLocallyClosed f
    (Z := (O : Set X) ∩ (X.basicOpen s : Set X)ᶜ)
    (O.isOpen.isLocallyClosed.inter (X.basicOpen s).isOpen.isClosed_compl.isLocallyClosed)
    ⟨x, hx, hb⟩
  exact h p hp hpO ((ev_eq_zero_iff p hpO s).2 hpb)

end Units

section Main

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem ev_eq_of_nilpotent (f : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {s : Γ(X, W)} {c : K}
    (hN : IsNilpotent (s - cst f W c)) (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hx : ptOf p ∈ W) : ev p hx s = c := by
  have h0 := (hN.map (ev p hx)).eq_zero
  rw [map_sub, ev_cst f p hp] at h0
  exact sub_eq_zero.mp h0

theorem res_cst (f : X ⟶ Spec (CommRingCat.of K)) {O O' : X.Opens} (h : O' ≤ O) (a : K) :
    res h (cst f O a) = cst f O' a := by
  rw [cst, cst, res_res]

theorem val_of_mem (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (h : ptOf p ∈ σ.U) :
    σ.val p = OnePoint.some (ev p h σ.f) := by
  unfold ToP1.val
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem val_of_not_mem (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (h : ptOf p ∉ σ.U) :
    σ.val p = OnePoint.infty := by
  unfold ToP1.val
  split_ifs with h'
  · exact absurd h' h
  · rfl

theorem ev_f_mul_g (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (hU : ptOf p ∈ σ.U)
    (hV : ptOf p ∈ σ.V) : ev p hU σ.f * ev p hV σ.g = 1 := by
  have e := congrArg (ev p (show ptOf p ∈ σ.U ⊓ σ.V from ⟨hU, hV⟩)) σ.inv
  rw [map_mul, map_one] at e
  rw [← ev_res p (inf_le_left : σ.U ⊓ σ.V ≤ σ.U) ⟨hU, hV⟩,
    ← ev_res p (inf_le_right : σ.U ⊓ σ.V ≤ σ.V) ⟨hU, hV⟩]
  exact e

theorem ev_g_eq_zero (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (hV : ptOf p ∈ σ.V)
    (hU : ptOf p ∉ σ.U) : ev p hV σ.g = 0 := by
  rw [ev_eq_zero_iff, σ.basicOpen_g]
  exact fun h => hU h.1

theorem mem_V_of_not_mem_U (σ : ToP1 X) {x : X} (hU : x ∉ σ.U) : x ∈ σ.V := by
  have hx : x ∈ (σ.U ⊔ σ.V : X.Opens) := by rw [σ.cover]; trivial
  rcases hx with h | h
  · exact absurd h hU
  · exact h

end Main

namespace Alg

open Polynomial

variable {K : Type} [Field K]

/-- `P(t, u)` for `P ∈ K[x][y]` (outer variable `y`, coefficients in `K[x]`). -/
def evalXY (t u : K) (P : K[X][X]) : K := (P.map (evalRingHom t)).eval u

end Alg

open Polynomial in
/-- **(IC) The affine image of a connected component under `(σ, ρ)` is Zariski closed.** In the
same setting, the set of `(σ(p), ρ(p)) ∈ K²` over the `K`-points `p` of the connected component of
`p₀` with both values finite is the common zero set of some `S ⊆ K[x][y]`.

Why true (STANDARD): the component `W` is proper over `K` (open and closed in `X`), so its image
`D` under `(σ, ρ) : W → P¹ × P¹` is closed (`P¹ × P¹` separated); `D ∩ 𝔸²` is closed in `𝔸²`,
hence `V(I)` for an ideal `I` (take `S = I`), and its `K`-points are exactly the images of the
`K`-points of `W` (a fibre over a closed point is a nonempty closed set of finite type over `K`,
so it contains a closed point, a `K`-point by the Nullstellensatz). Glue (properness). -/
def ImageClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      ∃ S : Set K[X][X], ∀ t u : K,
        (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
          σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
        ∀ Q ∈ S, Alg.evalXY t u Q = 0

/-- **(C2K) Constant or onto on a connected component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8, UNVERIFIED numbering: a morphism from a complete nonsingular curve over an
algebraically closed field to a curve is constant or surjective; here applied to a connected
component of `X`, a complete nonsingular irreducible curve, and the target `P¹`, whose closed
points are its `K`-points). Textbook leaf. -/
def ConstOrOntoAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀) ∨
      (∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t)

/-- **(CI) Connected components of a proper smooth curve over a field are irreducible.** If
`X → Spec K` is proper and smooth of relative dimension 1 over a field, every connected component of
`X` is irreducible (properness is not needed, but is kept: it is where (CI) is used, and it makes
the Lean proof `componentIrreducible` in `MobiusFinal.lean` a Noetherian argument).

Why true (STANDARD; references UNVERIFIED): smooth over a field implies regular, hence normal
(Stacks, *Varieties*, smooth ⇒ normal; Hartshorne II.8 for regular local rings being domains);
a locally Noetherian normal scheme is a disjoint union of integral open subschemes (its local rings
are domains, so irreducible components are disjoint and open), so its connected components are
its irreducible components. Glue (standard commutative algebra and topology). Not in Mathlib
v4.35 as stated (task infra-smooth-dim proved that the local rings at closed points are regular of
dimension 1, `stalk_dim_of_smoothOfRelativeDimension`, which is the main input; with it, (CI) is
proved in `MobiusFinal.lean`, `componentIrreducible`). -/
def ComponentIrreducible : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), IsProper f →
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsIrreducible (connectedComponent x)

/-- **(C1b) Local rings of a smooth curve at closed points have dimension 1.** If `X → Spec K`
is smooth of relative dimension 1 over a field `K` and `x` is a closed point, then
`dim 𝒪_{X,x} = 1` (STANDARD: smooth of relative dimension `n` over a field means `dim_x X = n`
at every point, and at a closed point of a scheme locally of finite type over a field
`dim 𝒪_{X,x} = dim_x X`; e.g. Stacks, *Morphisms*, smooth morphisms and dimension of fibres,
UNVERIFIED tags). Glue (dimension theory), not in Mathlib v4.35; Mathlib has
`ringKrullDim_stalk_eq_coheight` (Stacks 02IZ), used below. -/
def SmoothStalkDimOne : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = 1

open Polynomial in
/-- **(AD) `σ` and `ρ` are algebraically dependent on a connected component.** For `X → Spec K`
proper and smooth of relative dimension 1 over `K = K̄`, `σ, ρ : X → P¹` and a `K`-point `p₀`,
some nonzero `P ∈ K[x][y]` has `P(σ(p), ρ(p)) = 0` at every `K`-point `p` of the connected
component of `p₀` where both values are finite.

Why true (STANDARD; numbering UNVERIFIED): the component `W` is an integral curve, its function
field `K(W)` has transcendence degree `dim W = 1` over `K` (Hartshorne I.1.8A and I.6), so the
rational functions `σ, ρ` satisfy a nonzero polynomial relation `P(σ, ρ) = 0` in `K(W)`; the
regular function `P(σ, ρ)` on the open set where both are finite is then zero (`W` reduced), so it
vanishes at those `K`-points. Glue. -/
def AlgDep : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      ∃ P : K[X][X], P ≠ 0 ∧
        ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0

/-! ## §IC `ImageClosed` from properness (task image-plane)

The graph of `(σ, ρ)` over the `K`-points of a closed `T ⊆ X` is cut out, inside
`X ×_K 𝔸²_K`, by the local equations `f_σ = x` (on `U_σ`), `x g_σ = 1` (on `V_σ`) and the same
for `ρ` with `y`. The resulting set is closed (the complement of a union of basic opens) and
its image under the projection to `𝔸²_K = Spec K[x][y]` is closed because `X → Spec K` is
universally closed. Closed points of the image come from `K`-points (Jacobson). -/

set_option linter.unusedSectionVars false

namespace ImagePlane

open Polynomial

section Gen

variable {K : Type} [Field K]

theorem ptOf_comp {X Y : Scheme.{0}} (q : Spec (CommRingCat.of K) ⟶ Y) (h : Y ⟶ X) :
    ptOf (q ≫ h) = h.base (ptOf q) := rfl

/-- Values commute with pullback of sections. -/
theorem ev_comp {X Y : Scheme.{0}} (q : Spec (CommRingCat.of K) ⟶ Y) (h : Y ⟶ X) {O : X.Opens}
    (hx : ptOf (q ≫ h) ∈ O) (s : Γ(X, O)) :
    ev (q ≫ h) hx s = ev q (show ptOf q ∈ h ⁻¹ᵁ O from hx) (h.app O s) := by
  simp only [ev, Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (X.residue _ ≫ X.descResidueField (Scheme.stalkClosedPointTo (q ≫ h))).hom
      ((X.presheaf.germ O _ hx).hom s) =
    (Y.residue _ ≫ Y.descResidueField (Scheme.stalkClosedPointTo q)).hom
      ((Y.presheaf.germ (h ⁻¹ᵁ O) _ hx).hom (h.app O s))
  rw [Scheme.residue_descResidueField, Scheme.residue_descResidueField,
    Scheme.stalkClosedPointTo_comp]
  have key : ∀ (y : Y) (hy : h.base y ∈ O) (φ : Y.presheaf.stalk y ⟶ CommRingCat.of K),
      (h.stalkMap y ≫ φ).hom (X.presheaf.germ O (h.base y) hy s) =
        φ.hom (Y.presheaf.germ (h ⁻¹ᵁ O) y hy (h.app O s)) := by
    intro y hy φ
    rw [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  exact key (ptOf q) hx _

/-- The value of a global function on an affine scheme at `Spec.map φ`. -/
theorem ev_spec_top {R : Type} [CommRing R] (φ : CommRingCat.of R ⟶ CommRingCat.of K) (Q : R) :
    ev (Spec.map φ) (show ptOf (Spec.map φ) ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv Q) = φ Q := by
  rw [ev_top, ← ConcreteCategory.comp_apply, Scheme.ΓSpecIso_naturality]
  simp

/-- The point of `Spec.map φ` is the kernel of `φ`. -/
theorem ptOf_spec_asIdeal {R : Type} [CommRing R] (φ : CommRingCat.of R ⟶ CommRingCat.of K) :
    (ptOf (Spec.map φ)).asIdeal = RingHom.ker φ.hom := by
  change (PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint K)).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal]
  show Ideal.comap φ.hom (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

end Gen

variable {K : Type} [Field K]

/-- `𝔸²_K = Spec K[x][y] → Spec K`. -/
def g2 (K : Type) [Field K] : Spec (CommRingCat.of K[X][X]) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K[X][X]))

instance : LocallyOfFiniteType (g2 K) := by
  rw [g2, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The coordinate functions `x = C X` and `y = X` on `𝔸²_K`. -/
def xc (K : Type) [Field K] : Γ(Spec (CommRingCat.of K[X][X]), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K[X][X])).inv (C Polynomial.X)

def yc (K : Type) [Field K] : Γ(Spec (CommRingCat.of K[X][X]), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K[X][X])).inv Polynomial.X

/-- `evalXYHom t u : K[x][y] → K`, `x ↦ t`, `y ↦ u`. -/
def eHom (t u : K) : K[X][X] →+* K := (evalRingHom u).comp (mapRingHom (evalRingHom t))

theorem eHom_apply (t u : K) (P : K[X][X]) : eHom t u P = Alg.evalXY t u P := rfl

theorem eHom_algebraMap (t u a : K) : eHom t u (algebraMap K K[X][X] a) = a := by
  simp [eHom, Polynomial.algebraMap_apply]

theorem eHom_x (t u : K) : eHom t u (C Polynomial.X) = t := by simp [eHom]

theorem eHom_y (t u : K) : eHom t u Polynomial.X = u := by simp [eHom]

/-- A ring hom `K[x][y] → K` over `K` is the evaluation at `(φ x, φ y)`; the kernel determines
the point. -/
theorem eq_of_ker_eq (φ : K[X][X] →+* K) (hφ : ∀ a : K, φ (algebraMap K K[X][X] a) = a)
    (t u : K) (hk : RingHom.ker φ = RingHom.ker (eHom t u)) :
    φ (C Polynomial.X) = t ∧ φ Polynomial.X = u := by
  have h1 : C Polynomial.X - algebraMap K K[X][X] t ∈ RingHom.ker (eHom t u) := by
    simp [RingHom.mem_ker, eHom]
  have h2 : Polynomial.X - algebraMap K K[X][X] u ∈ RingHom.ker (eHom t u) := by
    simp [RingHom.mem_ker, eHom]
  rw [← hk, RingHom.mem_ker, map_sub, hφ, sub_eq_zero] at h1 h2
  exact ⟨h1, h2⟩

section Main

variable [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

/-- `X ×_K 𝔸²_K`. -/
abbrev PB : Scheme.{0} := pullback f (g2 K)

/-- The coordinate `x` (resp. `y`) on `fst⁻¹ O ⊆ X ×_K 𝔸²`. -/
def xO (O : X.Opens) : Γ(PB f, (pullback.fst f (g2 K)) ⁻¹ᵁ O) :=
  res le_top ((pullback.snd f (g2 K)).appTop (xc K))

def yO (O : X.Opens) : Γ(PB f, (pullback.fst f (g2 K)) ⁻¹ᵁ O) :=
  res le_top ((pullback.snd f (g2 K)).appTop (yc K))

/-- The open set where the graph equations of `σ` (against the coordinate `c`) fail. -/
def bad (σ : ToP1 X) (c : ∀ O : X.Opens, Γ(PB f, (pullback.fst f (g2 K)) ⁻¹ᵁ O)) : (PB f).Opens :=
  (PB f).basicOpen ((pullback.fst f (g2 K)).app σ.U σ.f - c σ.U) ⊔
    (PB f).basicOpen (c σ.V * (pullback.fst f (g2 K)).app σ.V σ.g - 1)

/-- The graph of `(σ, ρ)` over `T`. -/
def graph (σ ρ : ToP1 X) (T : Set X) : Set (PB f) :=
  ((bad f σ (xO f) ⊔ bad f ρ (yO f) : (PB f).Opens) : Set (PB f))ᶜ ∩ (pullback.fst f (g2 K)).base ⁻¹' T

theorem isClosed_graph (σ ρ : ToP1 X) {T : Set X} (hT : IsClosed T) :
    IsClosed (graph f σ ρ T) :=
  (bad f σ (xO f) ⊔ bad f ρ (yO f)).isOpen.isClosed_compl.inter
    (hT.preimage (pullback.fst f (g2 K)).base.hom.continuous)

/-- Value of the pulled-back coordinate at a `K`-point of the fibre product. -/
theorem ev_xO (q : Spec (CommRingCat.of K) ⟶ PB f) (O : X.Opens)
    (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ O) :
    ev q hx (xO f O) = (Spec.preimage (q ≫ pullback.snd f (g2 K))).hom (C Polynomial.X) := by
  rw [xO, ev_res]
  have e := ev_comp q (pullback.snd f (g2 K)) (O := ⊤) trivial (xc K)
  rw [Scheme.Hom.appTop]
  refine e.symm.trans ?_
  conv_lhs => rw [← Spec.map_preimage (q ≫ pullback.snd f (g2 K))]
  exact ev_spec_top _ _

theorem ev_yO (q : Spec (CommRingCat.of K) ⟶ PB f) (O : X.Opens)
    (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ O) :
    ev q hx (yO f O) = (Spec.preimage (q ≫ pullback.snd f (g2 K))).hom Polynomial.X := by
  rw [yO, ev_res]
  have e := ev_comp q (pullback.snd f (g2 K)) (O := ⊤) trivial (yc K)
  rw [Scheme.Hom.appTop]
  refine e.symm.trans ?_
  conv_lhs => rw [← Spec.map_preimage (q ≫ pullback.snd f (g2 K))]
  exact ev_spec_top _ _

/-- A `K`-point of the fibre product avoids `bad σ c` iff `σ` takes the finite value `a`
there, where `a` is the value of the coordinate `c`. -/
theorem not_mem_bad_iff (σ : ToP1 X) (c : ∀ O : X.Opens, Γ(PB f, (pullback.fst f (g2 K)) ⁻¹ᵁ O))
    (a : K) (q : Spec (CommRingCat.of K) ⟶ PB f)
    (hc : ∀ (O : X.Opens) (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ O), ev q hx (c O) = a) :
    ptOf q ∉ bad f σ c ↔ σ.val (q ≫ pullback.fst f (g2 K)) = OnePoint.some a := by
  set p := q ≫ pullback.fst f (g2 K) with hpdef
  have hU : ∀ (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.U),
      ev q hx ((pullback.fst f (g2 K)).app σ.U σ.f - c σ.U) = ev p hx σ.f - a := by
    intro hx
    rw [map_sub, hc, ← ev_comp q (pullback.fst f (g2 K)) hx σ.f]
  have hV : ∀ (hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.V),
      ev q hx (c σ.V * (pullback.fst f (g2 K)).app σ.V σ.g - 1) = a * ev p hx σ.g - 1 := by
    intro hx
    rw [map_sub, map_mul, map_one, hc, ← ev_comp q (pullback.fst f (g2 K)) hx σ.g]
  constructor
  · intro hq
    by_cases hpU : ptOf p ∈ σ.U
    · rw [val_of_mem σ p hpU]
      have h0 : ptOf q ∉ (PB f).basicOpen ((pullback.fst f (g2 K)).app σ.U σ.f - c σ.U) :=
        fun h => hq (Or.inl h)
      rw [← ev_eq_zero_iff q (show ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.U from hpU), hU] at h0
      rw [sub_eq_zero.mp h0]
    · exfalso
      have hpV := mem_V_of_not_mem_U σ hpU
      have h0 : ptOf q ∉ (PB f).basicOpen (c σ.V * (pullback.fst f (g2 K)).app σ.V σ.g - 1) :=
        fun h => hq (Or.inr h)
      rw [← ev_eq_zero_iff q (show ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.V from hpV), hV,
        ev_g_eq_zero σ p hpV hpU] at h0
      simp at h0
  · intro hv hq
    have hpU : ptOf p ∈ σ.U := by
      by_contra h'
      rw [val_of_not_mem σ p h'] at hv
      exact OnePoint.infty_ne_coe a hv
    rw [val_of_mem σ p hpU] at hv
    have hfa : ev p hpU σ.f = a := OnePoint.coe_injective hv
    rcases hq with h | h
    · have hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.U := Scheme.basicOpen_le _ _ h
      refine (ev_eq_zero_iff q hx _).1 ?_ h
      rw [hU, hfa, sub_self]
    · have hx : ptOf q ∈ (pullback.fst f (g2 K)) ⁻¹ᵁ σ.V := Scheme.basicOpen_le _ _ h
      refine (ev_eq_zero_iff q hx _).1 ?_ h
      rw [hV, ← hfa, ev_f_mul_g σ p hpU hx, sub_self]

/-- **The image of the `K`-points of a closed `T` under `(σ, ρ)`, intersected with `K²`, is
Zariski closed**, for `X` proper over `K = K̄`. -/
theorem image_closed (hP : IsProper f) (σ ρ : ToP1 X) {T : Set X} (hT : IsClosed T) :
    ∃ S : Set K[X][X], ∀ t u : K,
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ T ∧
        σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ↔
      ∀ Q ∈ S, Alg.evalXY t u Q = 0 := by
  classical
  have := hP
  have : JacobsonSpace (PB f) := LocallyOfFiniteType.jacobsonSpace (pullback.fst f (g2 K) ≫ f)
  set Z := graph f σ ρ T with hZ
  let C : Set (PrimeSpectrum K[X][X]) := (pullback.snd f (g2 K)).base '' Z
  have hC : IsClosed C := (pullback.snd f (g2 K)).isClosedMap _ (isClosed_graph f σ ρ hT)
  refine ⟨(PrimeSpectrum.vanishingIdeal C : Set K[X][X]), fun t u => ?_⟩
  let φ : CommRingCat.of K[X][X] ⟶ CommRingCat.of K := CommRingCat.ofHom (eHom t u)
  let m : PrimeSpectrum K[X][X] := ptOf (Spec.map φ)
  have hmI : m.asIdeal = RingHom.ker (eHom t u) := ptOf_spec_asIdeal φ
  -- membership of `m` in `C`, algebraically
  have hmC : m ∈ C ↔ ∀ Q ∈ (PrimeSpectrum.vanishingIdeal C : Set K[X][X]),
      Alg.evalXY t u Q = 0 := by
    have e : m ∈ C ↔ m ∈ PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal C : Set K[X][X]) := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hC.closure_eq]
    rw [e, PrimeSpectrum.mem_zeroLocus, hmI]
    exact ⟨fun h Q hQ => h hQ, fun h Q hQ => h Q hQ⟩
  rw [← hmC]
  constructor
  · rintro ⟨p, hp, hpT, hσ, hρ⟩
    have w : p ≫ f = Spec.map φ ≫ g2 K := by
      rw [hp, g2, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      exact (eHom_algebraMap t u a).symm
    set q := pullback.lift p (Spec.map φ) w with hq
    have hqs : q ≫ pullback.snd f (g2 K) = Spec.map φ := pullback.lift_snd _ _ _
    have hqf : q ≫ pullback.fst f (g2 K) = p := pullback.lift_fst _ _ _
    have hpre : Spec.preimage (q ≫ pullback.snd f (g2 K)) = φ := by
      rw [hqs, Spec.preimage_map]
    refine ⟨ptOf q, ⟨?_, ?_⟩, ?_⟩
    · rintro (h | h)
      · refine ((not_mem_bad_iff f σ (xO f) t q fun O hx => ?_).2 (hqf ▸ hσ)) h
        rw [ev_xO, hpre]; exact eHom_x t u
      · refine ((not_mem_bad_iff f ρ (yO f) u q fun O hx => ?_).2 (hqf ▸ hρ)) h
        rw [ev_yO, hpre]; exact eHom_y t u
    · show ptOf (q ≫ pullback.fst f (g2 K)) ∈ T
      rw [hqf]; exact hpT
    · show ptOf (q ≫ pullback.snd f (g2 K)) = m
      rw [hqs]
  · rintro ⟨z, hzZ, hzm⟩
    have hmax : m.asIdeal.IsMaximal := by
      rw [hmI]
      exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨algebraMap K K[X][X] a, eHom_algebraMap t u a⟩
    have hmcl : IsClosed ({m} : Set (PrimeSpectrum K[X][X])) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).2 hmax
    have hYcl : IsClosed (Z ∩ (pullback.snd f (g2 K)).base ⁻¹' {m}) :=
      (isClosed_graph f σ ρ hT).inter (hmcl.preimage (pullback.snd f (g2 K)).base.hom.continuous)
    obtain ⟨q, hq, hqY⟩ := exists_point_of_isLocallyClosed (pullback.fst f (g2 K) ≫ f)
      hYcl.isLocallyClosed ⟨z, hzZ, hzm⟩
    set p := q ≫ pullback.fst f (g2 K) with hpdef
    have hp : p ≫ f = 𝟙 _ := by rw [hpdef, Category.assoc]; exact hq
    set ψ := Spec.preimage (q ≫ pullback.snd f (g2 K)) with hψ
    have hψg : ∀ a : K, ψ.hom (algebraMap K K[X][X] a) = a := by
      have e : Spec.map ψ ≫ g2 K = 𝟙 _ := by
        rw [hψ, Spec.map_preimage, Category.assoc, ← pullback.condition, ← Category.assoc]
        exact hq
      rw [g2, ← Spec.map_comp, ← Spec.map_id] at e
      have e' := Spec.map_injective e
      intro a
      exact congrArg (fun χ : CommRingCat.of K ⟶ CommRingCat.of K => χ.hom a) e'
    have hker : RingHom.ker ψ.hom = RingHom.ker (eHom t u) := by
      rw [← ptOf_spec_asIdeal ψ, ← hmI, hψ, Spec.map_preimage, ptOf_comp]
      exact congrArg PrimeSpectrum.asIdeal hqY.2
    obtain ⟨hx, hy⟩ := eq_of_ker_eq ψ.hom hψg t u hker
    refine ⟨p, hp, hqY.1.2, ?_, ?_⟩
    · refine (not_mem_bad_iff f σ (xO f) t q fun O hO => ?_).1 fun h => hqY.1.1 (Or.inl h)
      rw [ev_xO]; exact hx
    · refine (not_mem_bad_iff f ρ (yO f) u q fun O hO => ?_).1 fun h => hqY.1.1 (Or.inr h)
      rw [ev_yO]; exact hy

end Main

end ImagePlane

/-- **(IC) `ImageClosed` holds** (task image-plane): from `IsProper f` alone (Mathlib's
`UniversallyClosed`, `Scheme.Hom.isClosedMap`, Jacobson). Smoothness is not used. -/
theorem imageClosed : ImageClosed := by
  intro K _ _ X f hP _ σ ρ p₀ _
  obtain ⟨S, hS⟩ := ImagePlane.image_closed f hP σ ρ (isClosed_connectedComponent (x := ptOf p₀))
  refine ⟨S, fun t u => (Iff.trans ?_ (hS t u))⟩
  refine exists_congr fun p => and_congr_right fun _ => and_congr_left fun _ => ?_
  exact ⟨fun h => h ▸ mem_connectedComponent, fun h => (connectedComponent_eq h).symm⟩

/-! ## §AD `AlgDep` from C2K, (CI), (C1b) and the closed image (task image-plane)

If `σ` is constant on the `K`-points of the component `W`, take `P = x − c` (or `P = 1`).
Otherwise `σ` is onto (C2K); the locus `W ∩ {σ = 0} = W \ V_σ` is a proper closed subset of the
irreducible (CI) set `W`, hence finite: an irreducible closed `Y' ⊊ W` with a closed point
`x ≠ η(Y')` gives a chain `x < η(Y') < η(W)` of generizations, so `dim 𝒪_{X,x} ≥ 2`, against
(C1b). So only finitely many `u` have `(0, u)` in the affine image; for any other `u` some
`Q ∈ S` (the closed-image equations of `ImagePlane.image_closed`) has `Q(0, u) ≠ 0`, and
`P = Q`. -/

namespace ImagePlane

open Polynomial

/-- In a Noetherian scheme whose closed points have local rings of dimension `1`, a proper closed
subset of an irreducible closed set is finite. -/
theorem finite_of_closed_ssubset {X : Scheme.{0}} [TopologicalSpace.NoetherianSpace X]
    (hdim : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = 1)
    {W : Set X} (hW : IsIrreducible W) (hWc : IsClosed W) {Y : Set X} (hY : IsClosed Y)
    (hYW : Y ⊆ W) (hne : Y ≠ W) : Y.Finite := by
  classical
  -- irreducible closed proper subsets of `W` are points
  have key : ∀ Y' : Set X, IsIrreducible Y' → IsClosed Y' → Y' ⊆ W → Y' ≠ W →
      Y' ⊆ {hW.genericPoint} ∨ Y'.Subsingleton := by
    intro Y' hY' hY'c hY'W hY'ne
    right
    have hη : closure ({hY'.genericPoint} : Set X) = Y' := by
      have := hY'.isGenericPoint_genericPoint_closure
      rw [hY'c.closure_eq] at this
      exact this
    have hξ : closure ({hW.genericPoint} : Set X) = W := by
      have := hW.isGenericPoint_genericPoint_closure
      rw [hWc.closure_eq] at this
      exact this
    set η := hY'.genericPoint
    set ξ := hW.genericPoint
    -- every closed point of `Y'` is `η`
    have hcl : ∀ x ∈ Y', IsClosed ({x} : Set X) → x = η := by
      intro x hx hxc
      by_contra hxη
      have h1 : x < η := by
        have hle : x ≤ η := specializes_iff_mem_closure.mpr (hη ▸ hx)
        refine lt_of_le_not_ge hle fun hge => hxη ?_
        have hmem : η ∈ closure ({x} : Set X) := specializes_iff_mem_closure.mp hge
        rw [hxc.closure_eq] at hmem
        exact hmem.symm
      have h2 : η < ξ := by
        have hle : η ≤ ξ := specializes_iff_mem_closure.mpr (hξ ▸ hY'W (hη ▸ subset_closure rfl))
        refine lt_of_le_not_ge hle fun hge => hY'ne ?_
        have hmem : ξ ∈ closure ({η} : Set X) := specializes_iff_mem_closure.mp hge
        rw [hη] at hmem
        refine le_antisymm hY'W ?_
        rw [← hξ]
        exact closure_minimal (Set.singleton_subset_iff.2 hmem) hY'c
      have c1 := Order.coheight_add_one_le h1
      have c2 := Order.coheight_add_one_le h2
      have h3 : (2 : ℕ∞) ≤ Order.coheight x := by
        calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
          _ ≤ Order.coheight ξ + 1 + 1 := by gcongr; exact zero_le
          _ ≤ Order.coheight η + 1 := by gcongr
          _ ≤ Order.coheight x := c1
      have h4 := hdim x hxc
      rw [ringKrullDim_stalk_eq_coheight] at h4
      have h5 : Order.coheight x = 1 := by exact_mod_cast h4
      rw [h5] at h3
      exact absurd h3 (by decide)
    intro a ha b hb
    obtain ⟨x, hx, hxc⟩ := (hY'c.inter isClosed_closure : IsClosed (Y' ∩ closure {a})).exists_closed_singleton
      ⟨a, ha, subset_closure rfl⟩
    have hxη := hcl x hx.1 hxc
    have hY'x : Y' = {x} := by
      rw [← hη, ← hxη, hxc.closure_eq]
    rw [hY'x] at ha hb
    exact ha.trans hb.symm
  obtain ⟨T, hT, hTe⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨Y, hY⟩
  have hYe : Y = ⋃ k ∈ T, (k : Set X) := by
    have := congrArg (fun c : TopologicalSpace.Closeds X => (c : Set X)) hTe
    simpa [TopologicalSpace.Closeds.coe_finset_sup] using this
  rw [hYe]
  refine T.finite_toSet.biUnion fun k hk => ?_
  have hkY : (k : Set X) ⊆ Y := by rw [hYe]; exact Set.subset_biUnion_of_mem (u := fun k : TopologicalSpace.Closeds X => (k : Set X)) hk
  have hkne : (k : Set X) ≠ W := fun e => hne (le_antisymm hYW (e ▸ hkY))
  rcases key k (hT ⟨k, hk⟩) k.isClosed (hkY.trans hYW) hkne with h | h
  · exact (Set.finite_singleton _).subset h
  · exact h.finite

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- A finite value of `ρ` at a `K`-point depends only on the underlying point. -/
theorem val_eq_of_ptOf_eq (f : X ⟶ Spec (CommRingCat.of K)) (ρ : ToP1 X)
    {p p' : Spec (CommRingCat.of K) ⟶ X} (hp : p ≫ f = 𝟙 _) (hp' : p' ≫ f = 𝟙 _)
    (h : ptOf p = ptOf p') {u u' : K} (hu : ρ.val p = OnePoint.some u)
    (hu' : ρ.val p' = OnePoint.some u') : u = u' := by
  have memU : ∀ (q : Spec (CommRingCat.of K) ⟶ X) (t : K),
      ρ.val q = OnePoint.some t → ptOf q ∈ ρ.U := by
    intro q t h
    by_contra h'
    rw [val_of_not_mem ρ q h'] at h
    exact OnePoint.infty_ne_coe t h
  have hU := memU p u hu
  have hU' := memU p' u' hu'
  rw [val_of_mem ρ p hU] at hu
  rw [val_of_mem ρ p' hU'] at hu'
  have e : ev p hU (ρ.f - cst f ρ.U u) = 0 := by
    rw [map_sub, ev_cst f p hp, OnePoint.coe_injective hu, sub_self]
  rw [ev_eq_zero_iff, h] at e
  rw [← ev_eq_zero_iff p' hU', map_sub, ev_cst f p' hp', OnePoint.coe_injective hu'] at e
  exact (sub_eq_zero.mp e).symm

end ImagePlane

open Polynomial in
/-- **(AD) `AlgDep` from C1b (`SmoothStalkDimOne`, proved by infra-smooth-dim), C2K and (CI)**
(task image-plane). -/
theorem algDep_of (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed)
    (hI : ComponentIrreducible) : AlgDep := by
  classical
  intro K _ _ X f hP hS σ ρ p₀ hp₀
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  set W := connectedComponent x₀ with hWdef
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  obtain ⟨S, hSc⟩ := ImagePlane.image_closed f hP σ ρ (isClosed_connectedComponent (x := x₀))
  by_cases hcst : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀
  · induction hv : σ.val p₀ using OnePoint.rec with
    | infty =>
      refine ⟨1, one_ne_zero, fun p hp hpc t u ht _ => ?_⟩
      rw [hcst p hp hpc, hv] at ht
      exact absurd ht (OnePoint.infty_ne_coe t)
    | coe c =>
      refine ⟨C (Polynomial.X - C c), ?_, fun p hp hpc t u ht _ => ?_⟩
      · exact C_ne_zero.mpr (X_sub_C_ne_zero c)
      · rw [hcst p hp hpc, hv] at ht
        have htc : t = c := (OnePoint.coe_injective ht).symm
        simp [Alg.evalXY, htc]
  push Not at hcst
  obtain ⟨pn, hpn, hpnc, hpnv⟩ := hcst
  have honto : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t := by
    rcases h2 K X f hP hS σ p₀ hp₀ with hc | ho
    · exact absurd (hc pn hpn hpnc) hpnv
    · exact ho
  -- the zero locus `Y = W \ V_σ` of `σ` on `W` is finite
  set Y : Set X := W ∩ ((σ.V : Set X))ᶜ with hYdef
  have hYc : IsClosed Y := isClosed_connectedComponent.inter σ.V.isOpen.isClosed_compl
  obtain ⟨p₁, hp₁, hp₁c, hp₁v⟩ := honto (OnePoint.some 1)
  have hp₁U : ptOf p₁ ∈ σ.U := by
    by_contra h'
    rw [val_of_not_mem σ p₁ h'] at hp₁v
    exact OnePoint.infty_ne_coe 1 hp₁v
  have hp₁V : ptOf p₁ ∈ σ.V := by
    rw [val_of_mem σ p₁ hp₁U] at hp₁v
    have e1 : ev p₁ hp₁U σ.f ≠ 0 := by rw [OnePoint.coe_injective hp₁v]; exact one_ne_zero
    rw [Ne, ev_eq_zero_iff, not_not, σ.basicOpen_f] at e1
    exact e1.2
  have hYne : Y ≠ W := by
    intro e
    have : ptOf p₁ ∈ Y := e ▸ (memW p₁).2 hp₁c
    exact this.2 hp₁V
  have hYfin : Y.Finite := ImagePlane.finite_of_closed_ssubset
    (fun x hx => h1 K X f hS x hx) (hI K X f hP hS x₀) isClosed_connectedComponent hYc
    Set.inter_subset_left hYne
  -- only finitely many `u` with `(0, u)` in the affine image
  set Us : Set K := {u | ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ W ∧
    σ.val p = OnePoint.some 0 ∧ ρ.val p = OnePoint.some u} with hUs
  have hUsfin : Us.Finite := by
    refine (hYfin.biUnion fun x _ => (show ({u | ∃ p : Spec (CommRingCat.of K) ⟶ X,
        p ≫ f = 𝟙 _ ∧ ptOf p = x ∧ ρ.val p = OnePoint.some u} : Set K).Subsingleton from ?_).finite).subset ?_
    · rintro u ⟨p, hp, hpx, hpu⟩ u' ⟨p', hp', hpx', hpu'⟩
      exact ImagePlane.val_eq_of_ptOf_eq f ρ hp hp' (hpx.trans hpx'.symm) hpu hpu'
    · rintro u ⟨p, hp, hpW, hp0, hpu⟩
      have hpU : ptOf p ∈ σ.U := by
        by_contra h'
        rw [val_of_not_mem σ p h'] at hp0
        exact OnePoint.infty_ne_coe 0 hp0
      have hpV : ptOf p ∉ σ.V := by
        intro hpV
        rw [val_of_mem σ p hpU] at hp0
        have e0 : ev p hpU σ.f = 0 := OnePoint.coe_injective hp0
        rw [ev_eq_zero_iff, σ.basicOpen_f] at e0
        exact e0 ⟨hpU, hpV⟩
      exact Set.mem_biUnion (x := ptOf p) ⟨hpW, hpV⟩ ⟨p, hp, rfl, hpu⟩
  have : Infinite K := inferInstance
  obtain ⟨u, hu⟩ := hUsfin.infinite_compl.nonempty
  have hnot : ¬ ∀ Q ∈ S, Alg.evalXY 0 u Q = 0 := by
    intro h
    obtain ⟨p, hp, hpc, hp0, hpu⟩ := (hSc 0 u).2 h
    exact hu ⟨p, hp, hpc, hp0, hpu⟩
  push Not at hnot
  obtain ⟨Q, hQS, hQ0⟩ := hnot
  refine ⟨Q, fun e => hQ0 (by rw [e]; simp [Alg.evalXY]), fun p hp hpc t u' ht hu' => ?_⟩
  exact (hSc t u').1 ⟨p, hp, (memW p).2 hpc, ht, hu'⟩ Q hQS

/-! ## §C2K `ConstOrOntoAlgClosed` from (CI) and the closed image (task image-plane)

With `ρ = σ`, the closed image gives: the finite values of `σ` on the `K`-points of a closed `T`
form a Zariski closed subset of `K` (the diagonal section of the equations), so a finite set or
all of `K`. If finite, the loci `{σ = t}` (closed: complements of two basic opens) and
`{σ = ∞} = X \ U` cover the irreducible (CI) component `W` (Jacobson), so one of them contains
`W`: `σ` is constant. Applying this also to `1/σ` (swap the charts) gives "constant or onto".
No leaf is used (in particular not (L0)). -/

namespace ImagePlane

open Polynomial

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- The reciprocal `1/σ` (the charts swapped). -/
def inv (σ : ToP1 X) : ToP1 X where
  U := σ.V
  V := σ.U
  cover := by rw [sup_comm]; exact σ.cover
  f := σ.g
  g := σ.f
  inv := by
    have h : σ.V ⊓ σ.U ≤ σ.U ⊓ σ.V := le_of_eq (inf_comm _ _)
    have e : res h (res (inf_le_left : σ.U ⊓ σ.V ≤ σ.U) σ.f *
        res (inf_le_right : σ.U ⊓ σ.V ≤ σ.V) σ.g) = res h 1 := congrArg _ σ.inv
    rw [map_mul, map_one, res_res, res_res] at e
    change res _ σ.g * res _ σ.f = 1
    rw [mul_comm]
    exact e
  basicOpen_f := by rw [σ.basicOpen_g, inf_comm]
  basicOpen_g := by rw [σ.basicOpen_f, inf_comm]

open scoped Classical in
/-- `v ↦ 1/v` on `P¹(K)`. -/
def recip (v : OnePoint K) : OnePoint K :=
  match v with
  | none => some 0
  | some s => if s = 0 then none else some s⁻¹

theorem recip_infty : recip (OnePoint.infty : OnePoint K) = OnePoint.some 0 := rfl

open scoped Classical in
theorem recip_coe (s : K) :
    recip (OnePoint.some s) = if s = 0 then OnePoint.infty else OnePoint.some s⁻¹ := rfl

theorem val_eq_recip (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) :
    σ.val p = recip ((inv σ).val p) := by
  by_cases hU : ptOf p ∈ σ.U
  · by_cases hV : ptOf p ∈ σ.V
    · have h2 : (inv σ).val p = OnePoint.some (ev p hV σ.g) := val_of_mem (inv σ) p hV
      rw [val_of_mem σ p hU, h2, recip_coe]
      have e := ev_f_mul_g σ p hU hV
      have hg : ev p hV σ.g ≠ 0 := right_ne_zero_of_mul_eq_one e
      rw [if_neg hg]
      exact congrArg _ (eq_inv_of_mul_eq_one_left e)
    · have h2 : (inv σ).val p = OnePoint.infty := val_of_not_mem (inv σ) p hV
      rw [val_of_mem σ p hU, h2, recip_infty]
      have : ev p hU σ.f = 0 := by
        rw [ev_eq_zero_iff, σ.basicOpen_f]; exact fun h => hV h.2
      rw [this]
  · have hV := mem_V_of_not_mem_U σ hU
    have h2 : (inv σ).val p = OnePoint.some (ev p hV σ.g) := val_of_mem (inv σ) p hV
    rw [val_of_not_mem σ p hU, h2, recip_coe, ev_g_eq_zero σ p hV hU, if_pos rfl]

/-- The open set where `σ ≠ a`. -/
def badX (f : X ⟶ Spec (CommRingCat.of K)) (σ : ToP1 X) (a : K) : X.Opens :=
  X.basicOpen (σ.f - cst f σ.U a) ⊔ X.basicOpen (cst f σ.V a * σ.g - 1)

theorem not_mem_badX_iff (f : X ⟶ Spec (CommRingCat.of K)) (σ : ToP1 X) (a : K)
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ptOf p ∉ badX f σ a ↔ σ.val p = OnePoint.some a := by
  have hU : ∀ (hx : ptOf p ∈ σ.U), ev p hx (σ.f - cst f σ.U a) = ev p hx σ.f - a := by
    intro hx; rw [map_sub, ev_cst f p hp]
  have hV : ∀ (hx : ptOf p ∈ σ.V), ev p hx (cst f σ.V a * σ.g - 1) = a * ev p hx σ.g - 1 := by
    intro hx; rw [map_sub, map_mul, map_one, ev_cst f p hp]
  constructor
  · intro hq
    by_cases hpU : ptOf p ∈ σ.U
    · rw [val_of_mem σ p hpU]
      have h0 : ptOf p ∉ X.basicOpen (σ.f - cst f σ.U a) := fun h => hq (Or.inl h)
      rw [← ev_eq_zero_iff p hpU, hU] at h0
      rw [sub_eq_zero.mp h0]
    · exfalso
      have hpV := mem_V_of_not_mem_U σ hpU
      have h0 : ptOf p ∉ X.basicOpen (cst f σ.V a * σ.g - 1) := fun h => hq (Or.inr h)
      rw [← ev_eq_zero_iff p hpV, hV, ev_g_eq_zero σ p hpV hpU] at h0
      simp at h0
  · intro hv hq
    have hpU : ptOf p ∈ σ.U := by
      by_contra h'
      rw [val_of_not_mem σ p h'] at hv
      exact OnePoint.infty_ne_coe a hv
    rw [val_of_mem σ p hpU] at hv
    have hfa : ev p hpU σ.f = a := OnePoint.coe_injective hv
    rcases hq with h | h
    · have hx : ptOf p ∈ σ.U := X.basicOpen_le _ h
      refine (ev_eq_zero_iff p hx _).1 ?_ h
      rw [hU, hfa, sub_self]
    · have hx : ptOf p ∈ σ.V := X.basicOpen_le _ h
      refine (ev_eq_zero_iff p hx _).1 ?_ h
      rw [hV, ← hfa, ev_f_mul_g σ p hpU hx, sub_self]

theorem eval_diag (Q : K[X][X]) (t : K) : (Q.eval Polynomial.X).eval t = Alg.evalXY t t Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add, hp, hq, Alg.evalXY, Polynomial.map_add]
  | monomial n a => simp [Alg.evalXY]

/-- The finite values of `σ` on the `K`-points of a closed `T` form a finite set or all of `K`. -/
theorem image_finite_or_univ [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K)) (hP : IsProper f)
    (σ : ToP1 X) {T : Set X} (hT : IsClosed T) :
    {t : K | ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ T ∧
      σ.val p = OnePoint.some t}.Finite ∨
    ∀ t : K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ T ∧
      σ.val p = OnePoint.some t := by
  classical
  obtain ⟨S, hS⟩ := image_closed f hP σ σ hT
  have hdiag : ∀ t : K, (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ T ∧
      σ.val p = OnePoint.some t) ↔ ∀ Q ∈ S, (Q.eval Polynomial.X).eval t = 0 := by
    intro t
    simp_rw [eval_diag]
    rw [← hS t t]
    exact ⟨fun ⟨p, hp, hpT, h⟩ => ⟨p, hp, hpT, h, h⟩, fun ⟨p, hp, hpT, h, _⟩ => ⟨p, hp, hpT, h⟩⟩
  by_cases h : ∀ Q ∈ S, Q.eval Polynomial.X = 0
  · right
    intro t
    exact (hdiag t).2 fun Q hQ => by rw [h Q hQ, eval_zero]
  · left
    push Not at h
    obtain ⟨Q, hQ, hQ0⟩ := h
    refine (Q.eval Polynomial.X).roots.toFinset.finite_toSet.subset fun t ht => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def]
    exact (hdiag t).1 ht Q hQ

/-- Finitely many finite values on an irreducible closed set force a constant value. -/
theorem const_of_finite [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [JacobsonSpace X] (σ : ToP1 X) {W : Set X} (hW : IsIrreducible W) (hWc : IsClosed W)
    (hfin : {t : K | ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ W ∧
      σ.val p = OnePoint.some t}.Finite) :
    ∃ v : OnePoint K, ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W →
      σ.val p = v := by
  classical
  set Fs := hfin.toFinset with hFs
  let fam : Finset (Set X) :=
    insert ((σ.U : Set X)ᶜ) (Fs.image fun t => ((badX f σ t : X.Opens) : Set X)ᶜ)
  have hcl : ∀ z ∈ fam, IsClosed z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact σ.U.isOpen.isClosed_compl
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hz
      exact (badX f σ t).isOpen.isClosed_compl
  have hmem : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W →
      ∃ z ∈ fam, ptOf p ∈ z := by
    intro p hp hpW
    induction hv : σ.val p using OnePoint.rec with
    | infty =>
      refine ⟨(σ.U : Set X)ᶜ, Finset.mem_insert_self _ _, fun hU => ?_⟩
      rw [val_of_mem σ p hU] at hv
      exact OnePoint.coe_ne_infty _ hv
    | coe t =>
      refine ⟨((badX f σ t : X.Opens) : Set X)ᶜ, Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨p, hp, hpW, hv⟩)), ?_⟩
      exact (not_mem_badX_iff f σ t p hp).2 hv
  have hcov : W ⊆ ⋃₀ ↑fam := by
    intro x hx
    by_contra hnot
    let Y : Set X := W ∩ ⋂ z ∈ fam, zᶜ
    have hYo : IsLocallyClosed Y :=
      hWc.isLocallyClosed.inter (isOpen_biInter_finset fun z hz => (hcl z hz).isOpen_compl).isLocallyClosed
    have hxY : x ∈ Y := by
      refine ⟨hx, Set.mem_iInter₂.2 fun z hz hxz => hnot ⟨z, hz, hxz⟩⟩
    obtain ⟨p, hp, hpY⟩ := exists_point_of_isLocallyClosed f hYo ⟨x, hxY⟩
    obtain ⟨z, hz, hpz⟩ := hmem p hp hpY.1
    exact Set.mem_iInter₂.1 hpY.2 z hz hpz
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hW) fam hcl hcov
  rcases Finset.mem_insert.1 hz with rfl | hz
  · refine ⟨OnePoint.infty, fun p _ hpW => val_of_not_mem σ p (hWz hpW)⟩
  · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨OnePoint.some t, fun p hp hpW => (not_mem_badX_iff f σ t p hp).1 (hWz hpW)⟩

end ImagePlane

/-- **C2K `ConstOrOntoAlgClosed` from (CI) alone** (task image-plane; (CI) is proved by
curve-glue's `componentIrreducible`). No leaf: properness enters through Mathlib's
`UniversallyClosed`. -/
theorem constOrOntoAlgClosed_of_CI (hI : ComponentIrreducible) : ConstOrOntoAlgClosed := by
  classical
  intro K _ _ X f hP hS σ p₀ hp₀
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  set x₀ := ptOf p₀ with hx₀
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ connectedComponent x₀ ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by rw [← h]; exact mem_connectedComponent⟩
  have hWi := hI K X f hP hS x₀
  have hWc : IsClosed (connectedComponent x₀) := isClosed_connectedComponent
  have hconst : ∀ v : OnePoint K, (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      ptOf p ∈ connectedComponent x₀ → σ.val p = v) →
      ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀ := by
    intro v hv p hp hpc
    rw [hv p hp ((memW p).2 hpc), hv p₀ hp₀ mem_connectedComponent]
  rcases ImagePlane.image_finite_or_univ f hP σ hWc with hfin | hall
  · obtain ⟨v, hv⟩ := ImagePlane.const_of_finite f σ hWi hWc hfin
    exact Or.inl (hconst v hv)
  rcases ImagePlane.image_finite_or_univ f hP (ImagePlane.inv σ) hWc with hfin' | hall'
  · obtain ⟨v, hv⟩ := ImagePlane.const_of_finite f (ImagePlane.inv σ) hWi hWc hfin'
    refine Or.inl (hconst (ImagePlane.recip v) fun p hp hpW => ?_)
    rw [ImagePlane.val_eq_recip σ p, hv p hp hpW]
  · right
    intro t
    induction t using OnePoint.rec with
    | infty =>
      obtain ⟨p, hp, hpW, h0⟩ := hall' 0
      refine ⟨p, hp, (memW p).1 hpW, ?_⟩
      rw [ImagePlane.val_eq_recip σ p, h0, ImagePlane.recip_coe, if_pos rfl]
    | coe t =>
      obtain ⟨p, hp, hpW, ht⟩ := hall t
      exact ⟨p, hp, (memW p).1 hpW, ht⟩

/-- **(AD) from C1b and (CI) alone.** -/
theorem algDep_of_CI (h1 : SmoothStalkDimOne) (hI : ComponentIrreducible) : AlgDep :=
  algDep_of h1 (constOrOntoAlgClosed_of_CI hI) hI

end Pin

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.imageClosed
#print axioms LeafQM.AV.Pin.algDep_of
#print axioms LeafQM.AV.Pin.constOrOntoAlgClosed_of_CI
#print axioms LeafQM.AV.Pin.algDep_of_CI
