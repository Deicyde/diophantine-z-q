import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.Contrib.HeightBC.Main

/-!
# height-split: the Faltings-height rows H-14 (R18), H-16 (R20), H-17 (R21), H-18 (R22) and
H-19 (`StableHeightFinite`) split into published-form leaves and glue

Task height-split (2026-11-14). The rows are the kernel's Props (imported, never restated):
`ZInQ.LeafPush2.R18_Javanpeykar`, `ZInQ.DefFaltings.R20_FaltingsLemma5`,
`ZInQ.DefFaltings.R21_Bost`, `ZInQ.LeafPush2.R22_Pazuki`, `ZInQ.DefFaltings.StableHeightFinite`.

Every row is stated over the project's `stableFaltingsHeight` (an infimum over all number fields
`L ⊇ K` and all metrized smooth group models, in `EReal`). The printed theorems are about
Faltings' stable height: the height of the Néron model over a field where the abelian variety
has semistable reduction. This file

* §A defines semistable reduction of a Néron model (identity component of every geometric special
  fibre an extension of an abelian variety by a split torus) and the predicate
  `IsStableFaltingsHeight A x` ("`x` is Faltings' stable height of `A`, original normalization"),
  over the kernel's objects;
* §B states the two SGA 7 IX leaves (semistable reduction theorem, base change of the identity
  component) and proves the identification `stableFaltingsHeight A = x ↔ IsStableFaltingsHeight A x`
  from them, the kernel leaf N1 and the kernel's proved glue (and N2 as a corollary);
* §C-§G state the printed theorems over `IsStableFaltingsHeight` and prove the rows.

No `sorry`, no `axiom`.
-/

namespace ZInQ.HeightSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.H5Neron


/-! ## §A. Semistable reduction and the published stable height -/

section Points

variable (k : Type) [Field k]

/-- `Spec R` as a `k`-scheme, for a `k`-algebra `R` (its morphisms to `G` are the `R`-points). -/
noncomputable def algPt (R : Type) [CommRing R] [Algebra k R] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))

variable {k}

/-- `Spec S → Spec R` over `k` for a `k`-algebra map `f : R → S`. -/
noncomputable def algPtMap {R S : Type} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) : algPt k S ⟶ algPt k R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (f : R →+* S))) (by
    simp only [algPt, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

end Points

/-- **Semi-abelian identity component** of a group scheme `G` over a field `k` (applied below with
`k` algebraically closed): there is an open connected subgroup scheme `U ⊆ G` (necessarily the
identity component `G⁰`, an open and closed subgroup) and a faithfully flat homomorphism
`π : U → B` onto an abelian variety `B` whose kernel is a split torus `𝔾_m^r`, in the functor of
points: for every `k`-algebra `R` a group isomorphism `(Rˣ)^r ≅ ker(U(R) → B(R))`, natural in `R`
(by Yoneda, `ker π ≅ 𝔾_m^r` as group schemes). This is "`G⁰` is an extension of an abelian variety
by a torus" (SGA 7 IX Déf. 2.2 / 3.1, BLR 7.4, UNVERIFIED locators; over `k̄` every torus is split). -/
def HasSemiAbelianIdentityComponent {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G),
    IsOpenImmersion inc.left ∧ IsMonHom inc ∧ ConnectedSpace U.left ∧
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X), IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
    ∃ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)),
      (∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
        u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
        (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)

section Fibres

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `κ̄(𝔭)`, an algebraic closure of the residue field of `𝓞_L` at `𝔭`. -/
abbrev ResBar (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] : Type := AlgebraicClosure 𝔭.ResidueField

/-- The geometric fibre `𝒢 ×_{𝓞_L} κ̄(𝔭)` of a group model at `𝔭`, a group scheme over `κ̄(𝔭)`. -/
noncomputable def geomFibre (𝒢 : GroupModel A L) (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    Over (Spec (CommRingCat.of (ResBar 𝔭))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (ResBar 𝔭))))).obj 𝒢.G

noncomputable instance (𝒢 : GroupModel A L) (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    GrpObj (geomFibre 𝒢 𝔭) :=
  Functor.grpObjObj

/-- **Semistable reduction everywhere** (applied to a Néron model `𝒩` of `A_L`): at every maximal
ideal `𝔭` of `𝓞_L`, the identity component of the geometric special fibre `𝒩_{κ̄(𝔭)}` is
semi-abelian. (SGA 7 IX Déf. 3.1/3.2, UNVERIFIED locators; the special fibre of the global Néron
model at `𝔭` is that of the Néron model over `𝓞_{L,𝔭}`, BLR 1.2/2, UNVERIFIED.) -/
def IsSemistable (𝒢 : GroupModel A L) : Prop :=
  ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], HasSemiAbelianIdentityComponent (geomFibre 𝒢 𝔭)

end Fibres

/-- **Faltings' stable height (original normalization `(i/2)^g`), the published definition**:
`x` is the height of the Néron model of `A_L` for some number field `L ⊇ K` over which `A` has
semistable reduction everywhere (Faltings 1983 §1; Deligne, Sém. Bourbaki 616, §1; UNVERIFIED
locators). The height of a group model `𝒩.height` is the kernel's (the metrized Hodge line
`⋀^g ω_𝒩`, `‖η‖²_σ = (i/2)^g ∫ η ∧ η̄`; one value for all metrizations given the uniqueness
half of AN3, `MetrizedModel.modelHeight_eq_of_model_eq`). Independence of `L` is
`isStableFaltingsHeight_unique` below (from SGA 7 IX 3.3). -/
def IsStableFaltingsHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L),
    𝒩.IsNeronModel ∧ IsSemistable 𝒩 ∧ 𝒩.height = (x : EReal)

/-! ## §B. The two SGA 7 IX leaves and the identification with the kernel's height -/

/-- **Leaf SS1. Grothendieck's semistable reduction theorem**, global form (SGA 7 I, Exp. IX,
Thm 3.6, UNVERIFIED number): an abelian variety over a number field `K` acquires semistable
reduction everywhere over some finite extension `L₀` (every Néron model of `A_{L₀}` is semistable).
SGA 7 states it over a discrete valuation ring; the global form follows because `A` has good
reduction outside finitely many primes and semistability is preserved by further finite extension
(SGA 7 IX 3.3); it is the form used to define the stable height (Faltings 1983 §1, Deligne,
Sém. Bourbaki 616, UNVERIFIED locators). -/
def SemistableReductionThm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K),
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀),
      ∀ 𝒩 : GroupModel A L₀, 𝒩.IsNeronModel → IsSemistable 𝒩

/-- **Leaf SS2. Base change of the identity component in the semistable case** (SGA 7 I, Exp. IX,
Prop. 3.3 / Cor. 3.3.1, UNVERIFIED numbers): if `A_L` has semistable reduction, then for every finite
extension `L'/L` the identity component of the Néron model of `A_{L'}` is the base change of the
identity component of the Néron model of `A_L`. Stated with the kernel's `IsBaseChangeOf` and
`IsOpenSubgroupModel` exactly as the kernel's N2 (`SemistableNeronIdentityComponent`) does:
`𝒰 = 𝒩'⁰ ≅ 𝒩⁰ ×_{𝓞_L} 𝓞_{L'}`, an open subgroup of `𝒩'` and of `𝒱 = 𝒩 ×_{𝓞_L} 𝓞_{L'}` (the
identity component is an open subgroup scheme, SGA 3 VI_B 3.10, UNVERIFIED). -/
def SemistableNeronBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (𝒩 : GroupModel A L), 𝒩.IsNeronModel → IsSemistable 𝒩 →
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
      (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
      ∃ 𝒰 𝒱 : GroupModel A L', IsBaseChangeOf 𝒱 𝒩 ∧ IsOpenSubgroupModel 𝒰 𝒩' ∧
        IsOpenSubgroupModel 𝒰 𝒱

section Identification

variable (hN1 : NeronModelExists) (hSS1 : SemistableReductionThm)
  (hSS2 : SemistableNeronBaseChange)

include hN1 hSS2 in
/-- **The kernel's stable height is the height of any semistable Néron model** (from N1, SS2 and
the kernel's proved glue H4a, H4b, M6 and `NeronModelMinimal`; the argument of
`H5Neron.stableFaltingsHeight_eq_neron_all`). -/
theorem stableFaltingsHeight_eq_of_semistable {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) {L₀ : Type} [Field L₀] [NumberField L₀] [Algebra K L₀]
    (𝒩₀ : GroupModel A L₀) (h𝒩₀ : 𝒩₀.IsNeronModel) (hss : IsSemistable 𝒩₀) :
    stableFaltingsHeight A = 𝒩₀.height := by
  rw [stableFaltingsHeight_eq_iInf_height]
  refine le_antisymm (iInf_le_of_le (FinExt.mk L₀) (iInf_le_of_le 𝒩₀ le_rfl)) ?_
  refine le_iInf fun E => le_iInf fun 𝒢 => ?_
  obtain ⟨L', j1, j2, j3, j4, j5, t1, t2⟩ := compositum K E.L L₀
  obtain ⟨𝒢', h𝒢'⟩ := groupModelBaseChangeExists K A E.L L' 𝒢
  obtain ⟨𝒩', h𝒩'⟩ := hN1 K A L'
  obtain ⟨𝒰, 𝒱, h𝒱, h𝒰𝒩, h𝒰𝒱⟩ := hSS2 K A L₀ 𝒩₀ h𝒩₀ hss L' 𝒩' h𝒩'
  calc 𝒩₀.height = 𝒱.height :=
        (Contrib.HeightBC.modelHeightBaseChange K A L₀ L' 𝒩₀ 𝒱 h𝒱).symm
    _ = 𝒰.height := (Contrib.HeightBC.openSubgroupHeight K A L' 𝒰 𝒱 h𝒰𝒱).symm
    _ = 𝒩'.height := Contrib.HeightBC.openSubgroupHeight K A L' 𝒰 𝒩' h𝒰𝒩
    _ ≤ 𝒢'.height := Contrib.HeightBC.neronModelMinimal K A L' 𝒩' 𝒢' h𝒩'
    _ = 𝒢.height := Contrib.HeightBC.modelHeightBaseChange K A E.L L' 𝒢 𝒢' h𝒢'

include hN1 hSS2 in
/-- Published height ⇒ kernel height. -/
theorem stableFaltingsHeight_eq_of_isStableFaltingsHeight {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {x : ℝ} (h : IsStableFaltingsHeight A x) :
    stableFaltingsHeight A = (x : EReal) := by
  obtain ⟨L, i1, i2, i3, 𝒩, h𝒩, hss, hx⟩ := h
  rw [stableFaltingsHeight_eq_of_semistable hN1 hSS2 A 𝒩 h𝒩 hss, hx]

include hN1 hSS2 in
/-- **Independence of the field** (the published definition is well posed). -/
theorem isStableFaltingsHeight_unique {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {x y : ℝ} (hx : IsStableFaltingsHeight A x) (hy : IsStableFaltingsHeight A y) : x = y := by
  have := (stableFaltingsHeight_eq_of_isStableFaltingsHeight hN1 hSS2 hx).symm.trans
    (stableFaltingsHeight_eq_of_isStableFaltingsHeight hN1 hSS2 hy)
  exact_mod_cast this

include hN1 hSS1 hSS2 in
/-- A semistable Néron model over some field, whose height is the kernel's stable height. -/
theorem exists_semistable_neron {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ IsSemistable 𝒩₀ ∧ stableFaltingsHeight A = 𝒩₀.height := by
  obtain ⟨L₀, i1, i2, i3, hL₀⟩ := hSS1 K A
  obtain ⟨𝒩₀, h𝒩₀⟩ := hN1 K A L₀
  exact ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hL₀ 𝒩₀ h𝒩₀,
    stableFaltingsHeight_eq_of_semistable hN1 hSS2 A 𝒩₀ h𝒩₀ (hL₀ 𝒩₀ h𝒩₀)⟩

include hN1 hSS1 hSS2 in
/-- **H5 identification**: for a real `x`, the kernel's `stableFaltingsHeight A = x` iff `x` is
Faltings' (published) stable height of `A`. -/
theorem isStableFaltingsHeight_iff {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (x : ℝ) : IsStableFaltingsHeight A x ↔ stableFaltingsHeight A = (x : EReal) := by
  refine ⟨stableFaltingsHeight_eq_of_isStableFaltingsHeight hN1 hSS2, fun hx => ?_⟩
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hss, he⟩ := exists_semistable_neron hN1 hSS1 hSS2 A
  exact ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hss, he.symm.trans hx⟩

include hN1 hSS1 hSS2 in
/-- **The kernel leaf N2 from N1, SS1 and SS2.** -/
theorem semistableNeronIdentityComponent_of : SemistableNeronIdentityComponent := by
  intro K _ _ A
  obtain ⟨L₀, i1, i2, i3, hL₀⟩ := hSS1 K A
  obtain ⟨𝒩₀, h𝒩₀⟩ := hN1 K A L₀
  exact ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, fun L' _ _ _ _ _ 𝒩' h𝒩' =>
    hSS2 K A L₀ 𝒩₀ h𝒩₀ (hL₀ 𝒩₀ h𝒩₀) L' 𝒩' h𝒩'⟩

end Identification

/-! ## §F. H-19 `StableHeightFinite`: the two halves

`≠ ⊤` needs one metrized model (glue `NeronMetrizable`); `≠ ⊥` needs that all metrizations of the
semistable Néron model have one height: the kernel's `AnalyticUniformizationUnique` (AN3, uniqueness
half; project Prop, open) and `MetrizedDimUnique` (glue). -/

/-- **Glue `NeronMetrizable`.** The Néron model of `A_L` carries a metrization: a `g`, the Hodge
lattice `⋀^g ω_𝒩` and, at every `τ : L → ℂ`, an analytic uniformization with the coefficient map
`η ↦ c`, `η ⊗_τ 1 = c·dz₁∧⋯∧dz_g`. Needs: AN3 existence (the kernel's
`AnalyticUniformizationExists`, the uniformization theorem `A_τ(ℂ) ≅ ℂ^g/Λ`, Mumford AV §1), the
kernel's `HodgeLatticeTheorem` (proved: `ZInQ.Contrib.Dim.hodgeLatticeTheorem`) with `g = dim A` equal
to the dimension of the uniformization, and the construction of the coefficient map from the
differential at `0` of germs along `Φ` (well defined on `𝔪/𝔪²`, nonzero on the Hodge line). -/
def NeronMetrizable : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (𝒩 : GroupModel A L), 𝒩.IsNeronModel →
    ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒩

/-- **Glue `MetrizedDimUnique`.** Two metrizations of the same group model have the same `g`.
Needs: for `τ : L → ℂ`, `Φ : ℂ^g → 𝒢(ℂ)_τ` is a surjective homomorphism with kernel a full lattice
`Λ` (`IsZLattice ℝ`, rank `2g`), so `#𝒢(ℂ)_τ[2] = #(½Λ/Λ) = 2^{2g}`; the same count for `g'` gives
`g = g'` (elementary; not compiled here). -/
def MetrizedDimUnique : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model → g = g'

section Finite

variable {K : Type} [Field K]

/-- With AN3 uniqueness and `MetrizedDimUnique`, the height of a metrizable group model is the
height of any of its metrizations. -/
theorem groupModel_height_eq (hU : AnalyticUniformizationUnique) (hD : MetrizedDimUnique)
    {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ}
    (M : MetrizedModel A L g) : M.model.height = (M.hodge.modelHeight : EReal) := by
  refine le_antisymm (iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le rfl le_rfl))) ?_
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  obtain rfl := hD K A L g g' M M' hM'.symm
  rw [MetrizedModel.modelHeight_eq_of_model_eq hU M M' hM'.symm]

/-- **`stableFaltingsHeight A ≠ ⊤`** from N1 and `NeronMetrizable`. -/
theorem stableFaltingsHeight_ne_top (hN1 : NeronModelExists) (hMet : NeronMetrizable)
    [NumberField K] (A : PkgI3.AbVar K) : stableFaltingsHeight A ≠ ⊤ := by
  obtain ⟨𝒩, h𝒩⟩ := hN1 K A K
  obtain ⟨g, M, -⟩ := hMet K A K 𝒩 h𝒩
  intro htop
  have := stableFaltingsHeight_le A M
  rw [htop, top_le_iff] at this
  exact EReal.coe_ne_top _ this

/-- **`stableFaltingsHeight A ≠ ⊥`** from N1, SS1, SS2, AN3 uniqueness and `MetrizedDimUnique`. -/
theorem stableFaltingsHeight_ne_bot (hN1 : NeronModelExists) (hSS1 : SemistableReductionThm)
    (hSS2 : SemistableNeronBaseChange) (hU : AnalyticUniformizationUnique)
    (hD : MetrizedDimUnique) [NumberField K] (A : PkgI3.AbVar K) : stableFaltingsHeight A ≠ ⊥ := by
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, -, -, he⟩ := exists_semistable_neron hN1 hSS1 hSS2 A
  rw [he]
  by_cases hM : ∃ (g : ℕ) (M : MetrizedModel A L₀ g), M.model = 𝒩₀
  · obtain ⟨g, M, rfl⟩ := hM
    rw [groupModel_height_eq hU hD M]
    exact EReal.coe_ne_bot _
  · push Not at hM
    have htop : 𝒩₀.height = ⊤ :=
      le_antisymm le_top (le_iInf fun g => le_iInf fun M => le_iInf fun h => absurd h (hM g M))
    rw [htop]
    exact top_ne_bot

/-- **H-19: `StableHeightFinite` from the leaves N1, SS1, SS2 and the glue `NeronMetrizable`,
`AnalyticUniformizationUnique`, `MetrizedDimUnique`.** -/
theorem stableHeightFinite_of (hN1 : NeronModelExists) (hSS1 : SemistableReductionThm)
    (hSS2 : SemistableNeronBaseChange) (hMet : NeronMetrizable)
    (hU : AnalyticUniformizationUnique) (hD : MetrizedDimUnique) : StableHeightFinite :=
  fun _ _ _ A => ⟨stableFaltingsHeight_ne_top hN1 hMet A,
    stableFaltingsHeight_ne_bot hN1 hSS1 hSS2 hU hD A⟩

end Finite

/-! ## §C. H-17, R21 (Bost) -/

/-- **Leaf R21-Bost. Bost's lower bound** (J.-B. Bost, *Périodes et isogénies des variétés abéliennes
sur les corps de nombres*, Sém. Bourbaki 795 (1994/95), Astérisque 237 (1996); the display is
UNVERIFIED: locators.md could not read it). Recalled display: `h(A) ≥ −(g/2) log(2π)` for every
abelian variety of dimension `g` over a number field, `h` the stable height in Deligne's
normalization `(i/2π)^g`, `h_D = h_F + (g/2) log π`. Stated in Deligne's normalization, the weaker of
the two readings (a Faltings-normalized display `h_F ≥ −(g/2) log 2π` implies it, as `h_D ≥ h_F`; the
Faltings-normalized reading is false for `E` with `j = 0`, `h_F ≈ −1.32`, so Deligne's is the one
meant). -/
def BostLowerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi

/-- **The form printed by Gaudron–Rémond** (Duke Math. J. 163 (2014), §9, proof of Lemma 9.1,
p. 2098, read by the locator audit; referred there to Bost and to GR's earlier Cor. 8.4):
`h_F(A) ≥ −(3/2) dim A`, Faltings' normalization. A consequence of `BostLowerBound`
(`grBostBound_of_bost`). -/
def GRBostBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x → -(3 / 2) * (g : ℝ) ≤ x

/-- `log(2π) + log π = log(2π²) < 3` (`2π² < 19.9 < e³`). -/
theorem log_two_pi_add_log_pi_lt_three : Real.log (2 * Real.pi) + Real.log Real.pi < 3 := by
  have hpi := Real.pi_pos
  rw [← Real.log_mul (by positivity) hpi.ne', Real.log_lt_iff_lt_exp (by positivity)]
  have he := Real.exp_one_gt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have hp := Real.pi_lt_d2
  have h1 : 2 * Real.pi * Real.pi < 19.9 := by nlinarith
  have h2 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have h4 : (19.9 : ℝ) < 2.7182818283 ^ 3 := by norm_num
  linarith

theorem grBostBound_of_bost (h : BostLowerBound) : GRBostBound := by
  intro K _ _ A g hg x hx
  have h1 := h K A g hg x hx
  have h2 := log_two_pi_add_log_pi_lt_three
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  nlinarith

/-- Lifting an `EReal` that is neither `⊤` nor `⊥`. -/
theorem exists_real_of_ne (e : EReal) (ht : e ≠ ⊤) (hb : e ≠ ⊥) : ∃ x : ℝ, e = x :=
  ⟨e.toReal, (EReal.coe_toReal ht hb).symm⟩

/-- **H-17: R21 from Bost's printed bound**, the leaves N1, SS1, SS2 (identification) and the `≠ ⊥`
half of H-19 (glue `AnalyticUniformizationUnique`, `MetrizedDimUnique`). -/
theorem r21_of_leaves (hB : BostLowerBound) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange)
    (hU : AnalyticUniformizationUnique) (hD : MetrizedDimUnique) : R21_Bost := by
  intro K _ _ A g hg
  by_cases ht : stableFaltingsHeight A = ⊤
  · rw [ht]; exact le_top
  obtain ⟨x, hx⟩ := exists_real_of_ne _ ht (stableFaltingsHeight_ne_bot hN1 hSS1 hSS2 hU hD A)
  rw [hx]
  exact EReal.coe_le_coe_iff.mpr (by
    have := grBostBound_of_bost hB K A g hg x ((isStableFaltingsHeight_iff hN1 hSS1 hSS2 A x).mpr hx)
    linarith)

end ZInQ.HeightSplit
