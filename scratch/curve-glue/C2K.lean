import ZInQKernel.HDecomp.QM.Pairs

/-!
# curve-glue, part 2: C2K `ConstOrOntoAlgClosed` from "global functions are constant"

Task curve-glue (2026-11-13). `ConstOrOntoAlgClosed` (C2K) and `RatFactorAlgClosed` (C3K) are
copied verbatim from `scratch/curve-facts/CurveFacts.lean` (§7 there), with `ptOf`,
`Mob.ratEval` and `isOpen_connectedComponent_of_noetherian` (proved there). See
`docs/research/curve-glue.md`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
open PkgI3

/-! ## §0 Copied verbatim from `scratch/curve-facts/CurveFacts.lean` -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]

open scoped Classical in
/-- The value at a finite point `t` of the rational map `[F : G] : P¹ → P¹`. -/
def ratEval (F G : K[X]) (t : K) : OnePoint K :=
  if G.eval t = 0 then OnePoint.infty else OnePoint.some (F.eval t / G.eval t)

end Mob

/-- The point of `X` at which a field point `p : Spec K → X` sits. -/
abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1

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

open Polynomial in
/-- **(C3K) Factorization on a connected component where `σ` is nonconstant**, over an
algebraically closed field of characteristic 0 (in characteristic `p` the Frobenius
`σ = ρ^p` is a counterexample). Glue (a standard consequence of textbook results, see
`docs/research/curve-facts.md` §3). -/
def RatFactorAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p₁ p₂ : Spec (CommRingCat.of K) ⟶ X, p₁ ≫ f = 𝟙 _ → p₂ ≫ f = 𝟙 _ →
        connectedComponent (ptOf p₁) = connectedComponent (ptOf p₀) →
        connectedComponent (ptOf p₂) = connectedComponent (ptOf p₀) →
        σ.val p₁ = σ.val p₂ → ρ.val p₁ = ρ.val p₂) →
      ∃ F G : K[X], IsCoprime F G ∧ ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
        σ.val p = OnePoint.some t → ρ.val p = Mob.ratEval F G t

/-- In a Noetherian space, connected components are open. -/
theorem isOpen_connectedComponent_of_noetherian {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
  have hc : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      exact ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z,
        fun h => hz (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZC⟩, hzZ⟩ hzC
      apply hZC
      have : Z ⊆ connectedComponent z := hZ.1.isConnected.subset_connectedComponent hzZ
      rwa [← connectedComponent_eq hzC] at this
  rw [← isClosed_compl_iff, hc]
  exact (hfin.subset fun Z hZ => hZ.1).isClosed_biUnion fun Z hZ =>
    isClosed_of_mem_irreducibleComponents Z hZ.1


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

/-! ## §3 The leaf: global functions on a connected component are constant -/

/-- **(L) "Liouville": regular functions on a connected component of a proper smooth curve over
an algebraically closed field are constant** (up to nilpotents, which is weaker than the printed
statement). `X → Spec K` proper and smooth of relative dimension 1, `K` algebraically closed,
`W ⊆ X` open, closed and (pre)connected, `s ∈ Γ(W, 𝒪_X)`: then `s − c` is nilpotent for some
constant `c ∈ K` (the image of `c` under `K = Γ(Spec K) → Γ(X) → Γ(W)`).

Source (textbook leaf, STANDARD; numbering UNVERIFIED, recalled without network): `W` is a
proper connected `K`-scheme (an open and closed subscheme of a proper one), so `Γ(W, 𝒪_W)` is a
finite-dimensional `K`-algebra (finiteness of coherent cohomology for proper morphisms, EGA III
3.2.1; Hartshorne III.5.2 in the projective case) without nontrivial idempotents (`W`
connected), hence local Artinian with residue field `K` (`K` algebraically closed): every element
is a constant plus a nilpotent. With `W` reduced (smooth ⇒ reduced) this is the printed form
"`Γ(W, 𝒪_W) = K` for `W` proper, connected and reduced over `K = K̄`" (Stacks, Varieties, lemma
on `Γ` of a proper reduced connected scheme; Hartshorne Ex. II.4.5(d) for integral `W`; I.3.4
for projective varieties). Smoothness and dimension 1 are not needed; they are kept so that the
leaf is applied exactly where C2K is. Not in Mathlib v4.35 (no finiteness theorem for proper
morphisms). -/
def GlobalFunctionsConst : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ W : X.Opens, IsClopen (W : Set X) → _root_.IsPreconnected (W : Set X) →
      ∀ s : Γ(X, W), ∃ c : K, IsNilpotent (s - cst f W c)

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

/-! ## §4 C2K from the leaf (L) -/

/-- **The missed-value lemma.** If `σ` misses a value `t ∈ P¹(K)` on the `K`-points of a
connected component `W`, it is constant on them. For `t = ∞`, `W ⊆ U` (Jacobson) and `f|_W` is
constant by (L). For `t = a ∈ K`, `f − a` is a unit on `W ∩ U` and `1 − a g` on `W ∩ V`, and
`1/(f − a)`, `g/(1 − a g)` glue to `h ∈ Γ(W)`, constant `= c` by (L); `c ≠ 0` if `W ∩ U` has a
`K`-point, which forces `W ⊆ U` (`g = 0` off `U`) and `σ = a + 1/c` on `W`. -/
theorem constant_of_missed (hL : GlobalFunctionsConst) {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (hP : IsProper f)
    (hS : SmoothOfRelativeDimension 1 f) [JacobsonSpace X] (σ : ToP1 X) (W : X.Opens)
    (hWc : IsClopen (W : Set X)) (hWp : _root_.IsPreconnected (W : Set X)) (t : OnePoint K)
    (ht : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W → σ.val p ≠ t) :
    ∃ v : OnePoint K, ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W →
      σ.val p = v := by
  have : LocallyOfFiniteType f := inferInstance
  induction t using OnePoint.rec with
  | infty =>
    have hWU : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ptOf p ∈ W → ptOf p ∈ σ.U :=
      fun p hp hW => by
        by_contra h
        exact ht p hp hW (val_of_not_mem σ p h)
    have hle : W ≤ σ.U := by
      intro x hx
      by_contra hxU
      obtain ⟨p, hp, hpW, hpU⟩ := exists_point_of_isLocallyClosed f
        (Z := (W : Set X) ∩ (σ.U : Set X)ᶜ)
        (W.isOpen.isLocallyClosed.inter σ.U.isOpen.isClosed_compl.isLocallyClosed) ⟨x, hx, hxU⟩
      exact hpU (hWU p hp hpW)
    obtain ⟨c, hc⟩ := hL K X f hP hS W hWc hWp (res hle σ.f)
    refine ⟨OnePoint.some c, fun p hp hpW => ?_⟩
    rw [val_of_mem σ p (hle hpW), ← ev_res p hle hpW, ev_eq_of_nilpotent f hc p hp hpW]
  | coe a =>
    have hmiss : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ (hW : ptOf p ∈ W)
        (hU : ptOf p ∈ σ.U), ev p hU σ.f ≠ a := fun p hp hW hU e =>
      ht p hp hW (by rw [val_of_mem σ p hU, e])
    let O₁ : X.Opens := W ⊓ σ.U
    let O₂ : X.Opens := W ⊓ σ.V
    let u₁ : Γ(X, O₁) := res inf_le_right σ.f - cst f O₁ a
    let u₂ : Γ(X, O₂) := 1 - cst f O₂ a * res inf_le_right σ.g
    have hu₁ev : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₁,
        ev p hx u₁ = ev p hx.2 σ.f - a := by
      intro p hp hx
      simp only [u₁, map_sub, ev_res, ev_cst f p hp]
    have hu₂ev : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₂,
        ev p hx u₂ = 1 - a * ev p hx.2 σ.g := by
      intro p hp hx
      simp only [u₂, map_sub, map_one, map_mul, ev_res, ev_cst f p hp]
    have hu₁ : IsUnit u₁ := isUnit_of_ev_ne_zero f u₁ fun p hp hx => by
      rw [hu₁ev p hp hx]
      exact sub_ne_zero.mpr (hmiss p hp hx.1 hx.2)
    have hu₂ : IsUnit u₂ := isUnit_of_ev_ne_zero f u₂ fun p hp hx => by
      rw [hu₂ev p hp hx]
      by_cases hU : ptOf p ∈ σ.U
      · have e := ev_f_mul_g σ p hU hx.2
        have hne := hmiss p hp hx.1 hU
        intro h0
        have h1 : ev p hx.2 σ.g * (ev p hU σ.f - a) = 0 := by linear_combination h0 + e
        rcases mul_eq_zero.mp h1 with h | h
        · rw [h, mul_zero] at e; exact zero_ne_one e
        · exact hne (sub_eq_zero.mp h)
      · rw [ev_g_eq_zero σ p hx.2 hU, mul_zero, sub_zero]; exact one_ne_zero
    obtain ⟨i₁, hi₁⟩ := hu₁.exists_left_inv
    obtain ⟨i₂, hi₂⟩ := hu₂.exists_left_inv
    let s₂ : Γ(X, O₂) := res inf_le_right σ.g * i₂
    have hfg : res (show O₁ ⊓ O₂ ≤ σ.U from fun x hx => hx.1.2) σ.f *
        res (show O₁ ⊓ O₂ ≤ σ.V from fun x hx => hx.2.2) σ.g = 1 := by
      have e := congrArg (res (show O₁ ⊓ O₂ ≤ σ.U ⊓ σ.V from fun x hx => ⟨hx.1.2, hx.2.2⟩)) σ.inv
      rw [map_mul, map_one] at e
      rw [← e]
      simp only [res_res]
    have hcomp : res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ := by
      have A : res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁ = 1 := by
        rw [← map_mul, hi₁, map_one]
      have C : res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) i₂ * res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) u₂ = 1 := by
        rw [← map_mul, hi₂, map_one]
      have B : res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁ = 1 := by
        simp only [s₂, u₁, u₂, map_mul, map_sub, map_one, res_res, res_cst] at C hfg ⊢
        linear_combination C + res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) i₂ * hfg
      calc res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁
          = res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ *
              (res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁) := by
            rw [B, mul_one]
        _ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ *
              (res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) i₁ * res (inf_le_left : O₁ ⊓ O₂ ≤ O₁) u₁) := by
            ring
        _ = res (inf_le_right : O₁ ⊓ O₂ ≤ O₂) s₂ := by rw [A, mul_one]
    -- glue `i₁` and `s₂` to a section on `O₁ ⊔ O₂`
    let h : Γ(X, O₁ ⊔ O₂) := (X.sheaf.objSupIsoProdEqLocus O₁ O₂).inv ⟨(i₁, s₂), hcomp⟩
    have hh₁ : res (le_sup_left : O₁ ≤ O₁ ⊔ O₂) h = i₁ :=
      X.sheaf.objSupIsoProdEqLocus_inv_fst O₁ O₂ _
    have hh₂ : res (le_sup_right : O₂ ≤ O₁ ⊔ O₂) h = s₂ :=
      X.sheaf.objSupIsoProdEqLocus_inv_snd O₁ O₂ _
    have hW'eq : ((O₁ ⊔ O₂ : X.Opens) : Set X) = W := by
      ext x
      simp only [O₁, O₂, Opens.coe_sup, Opens.coe_inf, Set.mem_union, Set.mem_inter_iff,
        SetLike.mem_coe]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        by_cases hU : x ∈ σ.U
        · exact Or.inl ⟨hx, hU⟩
        · exact Or.inr ⟨hx, mem_V_of_not_mem_U σ hU⟩
    obtain ⟨c, hc⟩ := hL K X f hP hS (O₁ ⊔ O₂) (hW'eq ▸ hWc) (hW'eq ▸ hWp) h
    have hv₁ : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₁,
        ev p hx i₁ = c := by
      intro p hp hx
      rw [← hh₁, ev_res]; exact ev_eq_of_nilpotent f hc p hp _
    have hv₂ : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O₂,
        ev p hx s₂ = c := by
      intro p hp hx
      rw [← hh₂, ev_res]; exact ev_eq_of_nilpotent f hc p hp _
    by_cases hex : ∃ q : Spec (CommRingCat.of K) ⟶ X, q ≫ f = 𝟙 _ ∧ ptOf q ∈ W ∧ ptOf q ∈ σ.U
    · obtain ⟨q, hq, hqW, hqU⟩ := hex
      have hc0 : c ≠ 0 := by
        intro hc0
        have e := congrArg (ev q (show ptOf q ∈ O₁ from ⟨hqW, hqU⟩)) hi₁
        rw [map_mul, map_one, hv₁ q hq, hc0, zero_mul] at e
        exact zero_ne_one e
      refine ⟨OnePoint.some (a + c⁻¹), fun p hp hpW => ?_⟩
      have hpU : ptOf p ∈ σ.U := by
        by_contra hpU
        have hpV := mem_V_of_not_mem_U σ hpU
        have e := hv₂ p hp (show ptOf p ∈ O₂ from ⟨hpW, hpV⟩)
        simp only [s₂, map_mul] at e
        rw [ev_res, ev_g_eq_zero σ p hpV hpU, zero_mul] at e
        exact hc0 e.symm
      rw [val_of_mem σ p hpU]
      congr 1
      have e1 := congrArg (ev p (show ptOf p ∈ O₁ from ⟨hpW, hpU⟩)) hi₁
      rw [map_mul, map_one, hv₁ p hp, hu₁ev p hp] at e1
      have e2 := eq_inv_of_mul_eq_one_right e1
      linear_combination e2
    · push Not at hex
      exact ⟨OnePoint.infty, fun p hp hpW => val_of_not_mem σ p (hex p hp hpW)⟩

/-- **C2K from the leaf (L).** -/
theorem constOrOntoAlgClosed_of (hL : GlobalFunctionsConst) : ConstOrOntoAlgClosed := by
  intro K _ _ X f hP hS σ p₀ hp₀
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  set x₀ := ptOf p₀ with hx₀
  let W : X.Opens := ⟨connectedComponent x₀, isOpen_connectedComponent_of_noetherian x₀⟩
  have hWc : IsClopen (W : Set X) := ⟨isClosed_connectedComponent, W.isOpen⟩
  have hWp : _root_.IsPreconnected (W : Set X) := isPreconnected_connectedComponent
  have memW : ∀ p : Spec (CommRingCat.of K) ⟶ X, ptOf p ∈ W ↔
      connectedComponent (ptOf p) = connectedComponent x₀ :=
    fun p => ⟨fun h => (connectedComponent_eq h).symm,
      fun h => by
        show ptOf p ∈ connectedComponent x₀
        rw [← h]; exact mem_connectedComponent⟩
  by_cases ho : ∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
      connectedComponent (ptOf p) = connectedComponent x₀ ∧ σ.val p = t
  · exact Or.inr ho
  · left
    push Not at ho
    obtain ⟨t, ht⟩ := ho
    obtain ⟨v, hv⟩ := constant_of_missed hL f hP hS σ W hWc hWp t
      (fun p hp hpW => ht p hp ((memW p).1 hpW))
    intro p hp hpc
    rw [hv p hp ((memW p).2 hpc), hv p₀ hp₀ (mem_connectedComponent : x₀ ∈ connectedComponent x₀)]

end Pin

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.constOrOntoAlgClosed_of
