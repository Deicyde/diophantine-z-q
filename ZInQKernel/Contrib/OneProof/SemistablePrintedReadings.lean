import ZInQKernel.Contrib.OneProof.AnalyticStableHeight
import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect

/-! # semistab-assembly: the semistability clause of the height leaves under the geometric and `k(s)` readings

The leaves `ZInQ.R3Residual.BostLowerBoundAn` and `ZInQ.R3Residual.GaudronRemondThm14An` quantify over
`IsAnStableHeight A x`, whose semistability clause is `ZInQ.HeightFix.IsSemistableRes 𝒩` (at every maximal ideal
`𝔭`, an open connected subgroup `U` of the special fibre `𝒩 ×_{𝓞_L} k(𝔭)` is an extension of an abelian variety by
a torus). The clause sits in hypothesis position, so for the leaves to be consequences of the print, Lean's clause
must imply the print's. The print says "the identity component of the special fibre is semi-abelian"; whether
over `k(𝔭)` or over an algebraic closure is an open reading. This file proves both implications:

* §1 an open subgroup scheme of a group scheme locally of finite type over **any** field is closed
  (`isClosed_range_openSubgroup_field`: base change to `k̄`, where it is semiab-descend's
  `isClosed_range_openSubgroup`; the projection `G_{k̄} → G` is integral, hence closed, and surjective);
  so an open connected subgroup is the identity component (`range_eq_connectedComponent`);
* §2 the printed forms `HasSemiAbelianG0` (over `k`, split torus; applied over `k̄`) and `HasSemiAbelianG0Torus`
  (over `k`, torus split over `k̄`): `HasSemiAbelianIdentityComponent` / `HasSemiAbelianIdCompTorus` with
  "`U` connected" replaced by "`U` is the identity component" (its image is the connected component of the unit);
* §3 the bridges: `IsSemistableRes 𝒩` gives the geometric reading (`isSemistableGeomPrinted_of_res`, one lemma)
  and the `k(𝔭)` reading (`isSemistableResPrinted_of_res`);
* §4 the two leaves restated over the printed semistability (both readings at once, so they are consequences of
  the print under either), and the fields `bostLowerBoundAn`, `gaudronRemondThm14An` from them.

The third reading (SGA 7 IX 2.1.5 / 3.4 read as "no `𝔾_a` in `(G⁰)_{k̄}`") needs rigidity of tori and is not
treated here (task ga-rigidity). No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open DictModels.RaynaudOr ZInQ.HeightSplit ZInQ.HeightFix ZInQ.R3Residual
open ZInQ.DefFaltings ZInQ.HeightGlue ZInQ.HeightDict
open scoped NumberField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.SemistabAssembly

/-! ## §1. Open subgroups over an arbitrary field are closed -/

section OpenClosed

variable {k : Type} [Field k]

/-- The unit point `e ∈ G` of a group scheme over a field. -/
abbrev unitPt (G : Over (Spec (CommRingCat.of k))) [GrpObj G] : G.left :=
  (η[G] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G).left (default : Spec (CommRingCat.of k))

/-- `Spec k̄ → Spec k` is integral. -/
instance isIntegralHom_sφbar : IsIntegralHom (sφ (φbar k)) :=
  IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)

/-- `Spec k̄ → Spec k` is surjective. -/
instance surjective_sφbar : Surjective (sφ (φbar k)) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

/-- **An open subgroup scheme of a group scheme locally of finite type over any field is closed.** Base change
to `k̄`: the base change of `U` is an open subgroup of `G_{k̄}`, closed by `isClosed_range_openSubgroup`; it is
the preimage of `U` under the projection `p : G_{k̄} → G`, which is closed (integral) and surjective, so
`U = p(p⁻¹ U)` is closed. -/
theorem isClosed_range_openSubgroup_field {X Y : Over (Spec (CommRingCat.of k))} [GrpObj X] [GrpObj Y]
    [LocallyOfFiniteType X.hom] (i : Y ⟶ X) [IsOpenImmersion i.left] [IsMonHom i] :
    IsClosed (Set.range i.left) := by
  let φ := φbar k
  let F := Over.pullback (sφ φ)
  letI : GrpObj (F.obj X) := Functor.grpObjObj
  letI : GrpObj (F.obj Y) := Functor.grpObjObj
  haveI : LocallyOfFiniteType (F.obj X).hom := by
    change LocallyOfFiniteType (pullback.snd X.hom (sφ φ)); infer_instance
  have hsq := pbmap_isPullback (sφ φ) Y X i
  haveI : IsOpenImmersion (F.map i).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq (inferInstanceAs (IsOpenImmersion i.left))
  haveI : IsMonHom (F.map i) := inferInstance
  have hcl : IsClosed (Set.range (F.map i).left) :=
    ZInQ.SemiAbDescend.isClosed_range_openSubgroup (F.map i)
  let p := pullback.fst X.hom (sφ φ)
  have hrange : Set.range (F.map i).left = p ⁻¹' Set.range i.left := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show p ((F.map i).left y) ∈ Set.range i.left
      rw [← Scheme.Hom.comp_apply, ← hsq.w, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    · rintro ⟨u, hu⟩
      obtain ⟨z, -, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := i.left) (g := p) u x hu
      refine ⟨hsq.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd, hz2]
  have hps : Function.Surjective p := p.surjective
  rw [← Set.image_preimage_eq (Set.range i.left) hps, ← hrange]
  exact p.isClosedMap _ hcl

/-- **An open connected subgroup scheme is the identity component**: its image is the connected component of
the unit (it is clopen by §1 and connected). -/
theorem range_eq_connectedComponent {X Y : Over (Spec (CommRingCat.of k))} [GrpObj X] [GrpObj Y]
    [LocallyOfFiniteType X.hom] (i : Y ⟶ X) [IsOpenImmersion i.left] [IsMonHom i]
    [ConnectedSpace Y.left] : Set.range i.left = connectedComponent (unitPt X) := by
  have he : unitPt X ∈ Set.range i.left :=
    ⟨(η[Y] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y).left (default : Spec (CommRingCat.of k)), by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom i]⟩
  have hclo : IsClopen (Set.range i.left) :=
    ⟨isClosed_range_openSubgroup_field i, i.left.isOpenEmbedding.isOpen_range⟩
  exact subset_antisymm
    ((isConnected_range i.left.continuous).isPreconnected.subset_connectedComponent he)
    (hclo.connectedComponent_subset he)

end OpenClosed

/-! ## §2. The printed forms: the identity component is semi-abelian -/

section Printed

/-- **The identity component `G⁰` is an extension of an abelian variety by a split torus** (SGA 7 IX Déf. 2.2,
3.1 for `G⁰`, as printed; locators UNVERIFIED): there is an open subgroup scheme `U ⊆ G` whose image is the
connected component of the unit (so `U ≅ G⁰`) and a faithfully flat homomorphism `π : U → B` onto an abelian
variety `B` whose kernel is `𝔾_m^r` in the functor of points. `HasSemiAbelianIdentityComponent` verbatim, with
"`U` connected" replaced by "`U` is `G⁰`". Applied below over `k̄`. -/
def HasSemiAbelianG0 {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G),
    IsOpenImmersion inc.left ∧ IsMonHom inc ∧ Set.range inc.left = connectedComponent (unitPt G) ∧
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X), IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
    ∃ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)),
      (∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
        u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
        (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)

/-- **The identity component `G⁰` over `k` is an extension of an abelian variety over `k` by a torus** (a group
with `T_{k̄} ≅ 𝔾_m^r`; SGA 7 IX Déf. 2.2 read over `k`; locators UNVERIFIED). `HasSemiAbelianIdCompTorus`
verbatim, with "`U` connected" replaced by "`U` is `G⁰`". -/
def HasSemiAbelianG0Torus {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G),
    IsOpenImmersion inc.left ∧ IsMonHom inc ∧ Set.range inc.left = connectedComponent (unitPt G) ∧
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X), IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
    ∃ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
        letI := algK (φbar k) R
        (Fin r → Rˣ) →* (algPt k R ⟶ U)),
      (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
        letI := algK (φbar k) R
        ∀ u : algPt k R ⟶ U, u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
        [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
        letI := algK (φbar k) R
        letI := algK (φbar k) S
        e S (fun i => Units.map (f : R →* S) (t i)) =
          algPtMap (k := k) ({ (f : R →+* S) with commutes' := fun a => f.commutes (φbar k a) } :
            R →ₐ[k] S) ≫ e R t)

variable {k : Type} [Field k]

/-- The split form with a connected `U` is the printed `G⁰` form (any field, `G` locally of finite type). -/
theorem hasSemiAbelianG0_of (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]
    (h : HasSemiAbelianIdentityComponent G) : HasSemiAbelianG0 G := by
  obtain ⟨U, hU, inc, hoi, hmh, hcon, rest⟩ := h
  haveI := hoi
  haveI := hcon
  exact ⟨U, hU, inc, hoi, hmh, range_eq_connectedComponent inc, rest⟩

/-- The torus form with a connected `U` is the printed `G⁰` form over `k` (any field, `G` locally of finite
type). -/
theorem hasSemiAbelianG0Torus_of (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]
    (h : HasSemiAbelianIdCompTorus G) : HasSemiAbelianG0Torus G := by
  obtain ⟨U, hU, inc, hoi, hmh, hcon, rest⟩ := h
  haveI := hoi
  haveI := hcon
  exact ⟨U, hU, inc, hoi, hmh, range_eq_connectedComponent inc, rest⟩

end Printed

/-! ## §3. The bridges from `IsSemistableRes` -/

section Bridges

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **Semistable reduction everywhere, geometric reading** (SGA 7 IX Déf. 3.4 read over `κ̄(𝔭)`; locators
UNVERIFIED): at every maximal ideal `𝔭` of `𝓞_L`, the identity component of the geometric special fibre
`𝒢 ×_{𝓞_L} κ̄(𝔭)` is an extension of an abelian variety by a torus. -/
def IsSemistableGeomPrinted (𝒢 : GroupModel A L) : Prop :=
  ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], HasSemiAbelianG0 (geomFibre 𝒢 𝔭)

/-- **Semistable reduction everywhere, `k(s)` reading** (SGA 7 IX Déf. 3.4 read over `k(𝔭)`; locators
UNVERIFIED): at every maximal ideal `𝔭`, the identity component of the special fibre `𝒢 ×_{𝓞_L} k(𝔭)` is an
extension of an abelian variety over `k(𝔭)` by a torus. -/
def IsSemistableResPrinted (𝒢 : GroupModel A L) : Prop :=
  ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], HasSemiAbelianG0Torus (resFibre 𝒢 𝔭)

/-- **Semistable reduction, both readings at once.** -/
def IsSemistablePrinted (𝒢 : GroupModel A L) : Prop :=
  IsSemistableGeomPrinted 𝒢 ∧ IsSemistableResPrinted 𝒢

/-- **(1) Geometric reading.** From the leaves' `IsSemistableRes`: over an algebraic closure of each residue
field, the identity component of the special fibre is semi-abelian (`isSemistable_of_res` with Stacks 04KV
proved, then §1-§2 over `κ̄(𝔭)`). -/
theorem isSemistableGeomPrinted_of_res (𝒢 : GroupModel A L) (h : IsSemistableRes 𝒢) :
    IsSemistableGeomPrinted 𝒢 := by
  intro 𝔭 _
  haveI : LocallyOfFiniteType (geomFibre 𝒢 𝔭).hom := by
    change LocallyOfFiniteType (Limits.pullback.snd 𝒢.G.hom _); infer_instance
  exact hasSemiAbelianG0_of _ (isSemistable_of_res geomConnOfRationalPoint_proof 𝒢 h 𝔭)

/-- **(2) `k(s)` reading.** From `IsSemistableRes`: over `k(𝔭)` itself, the open connected subgroup is the
identity component of the special fibre (§1 over the arbitrary field `k(𝔭)`). -/
theorem isSemistableResPrinted_of_res (𝒢 : GroupModel A L) (h : IsSemistableRes 𝒢) :
    IsSemistableResPrinted 𝒢 := by
  intro 𝔭 _
  haveI : LocallyOfFiniteType (resFibre 𝒢 𝔭).hom := by
    change LocallyOfFiniteType (Limits.pullback.snd 𝒢.G.hom (sResP 𝔭)); infer_instance
  exact hasSemiAbelianG0Torus_of _ (h 𝔭)

/-- **(3) Both readings.** -/
theorem isSemistablePrinted_of_res (𝒢 : GroupModel A L) (h : IsSemistableRes 𝒢) :
    IsSemistablePrinted 𝒢 :=
  ⟨isSemistableGeomPrinted_of_res 𝒢 h, isSemistableResPrinted_of_res 𝒢 h⟩

end Bridges

/-! ## §4. The leaves over the printed semistability -/

section Leaves

/-- **Faltings' stable height, metric on `A_τ(ℂ)^an`, semistability as printed** (either reading):
`ZInQ.R3Residual.IsAnStableHeight` verbatim with `IsSemistableRes 𝒩` replaced by `IsSemistablePrinted 𝒩`. -/
def IsAnStableHeightSS {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L) (g : ℕ),
    𝒩.IsNeronModel ∧ IsSemistablePrinted 𝒩 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ printedDetLattice 𝒩 g, eta ≠ 0 ∧ secIndex (printedDetLattice 𝒩 g) eta ≠ 0 ∧
      ∃ r : (L →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒩 τ eta (r τ)) ∧
        x = (Real.log (secIndex (printedDetLattice 𝒩 g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L

/-- `IsAnStableHeight` gives `IsAnStableHeightSS` (§3). -/
theorem isAnStableHeightSS_of {K : Type} [Field K] {A : PkgI3.AbVar K} {x : ℝ}
    (hx : IsAnStableHeight A x) : IsAnStableHeightSS A x := by
  obtain ⟨L, iF, iN, iA, 𝒩, g, hN, hS, rest⟩ := hx
  exact ⟨L, iF, iN, iA, 𝒩, g, hN, isSemistablePrinted_of_res 𝒩 hS, rest⟩

/-- **Leaf R21-Bost over the printed semistability** (J.-B. Bost, Sém. Bourbaki 795 (1994/95), Astérisque
237 (1996); display UNVERIFIED): `ZInQ.R3Residual.BostLowerBoundAn` verbatim with `IsAnStableHeight` replaced
by `IsAnStableHeightSS` (semistable reduction as printed, in the geometric and the `k(𝔭)` reading at once). -/
def BostLowerBoundAnSS : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsAnStableHeightSS A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi

/-- **Leaf R19-GR over the printed semistability** (Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4,
p. 2060; `κ` p. 2058; read by the locator audit): `ZInQ.R3Residual.GaudronRemondThm14An` verbatim with
`IsAnStableHeight` replaced by `IsAnStableHeightSS`. -/
def GaudronRemondThm14AnSS : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsAnStableHeightSS A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **The field `bostLowerBoundAn`** from the leaf over the printed semistability. -/
theorem bostLowerBoundAn_of_ss (h : BostLowerBoundAnSS) : BostLowerBoundAn :=
  fun K _ _ A g hg x hx => h K A g hg x (isAnStableHeightSS_of hx)

/-- **The field `gaudronRemondThm14An`** from the leaf over the printed semistability. -/
theorem gaudronRemondThm14An_of_ss (h : GaudronRemondThm14AnSS) : GaudronRemondThm14An :=
  fun K _ _ A B g x hg hx hiso => h K A B g x hg (isAnStableHeightSS_of hx) hiso

end Leaves

end ZInQ.SemistabAssembly
