import Mathlib
import ZInQKernel.HDecomp.QM.Pairs

/-!
# image-plane, part 1: (IC) `ImageClosed` is a theorem

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

end Pin

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.imageClosed
