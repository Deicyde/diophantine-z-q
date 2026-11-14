import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.Contrib.HeightBC.Main
import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.Contrib.Dim.HodgeLattice
import ZInQKernel.HDecomp.Faltings.H5Neron

/-! # height-glue: the six height rows from height-split's leaves and T35.
Assembled by `build_rows.py` (see its docstring for the verbatim sources). -/


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

/-- **Glue `UniformizationDim`.** The dimension `g` of an analytic uniformization `ℂ^g → 𝒢(ℂ)_τ` of
a group model of `A_L` with kernel a full lattice is `dim A` (the complex Lie group `A_τ(ℂ)` has
complex dimension `dim A`; `Φ` induces a continuous bijection from the compact torus `ℂ^g/Λ`).
The lattice hypotheses are needed: without them `Φ₀ ∘ pr : ℂ^{g+1} → 𝒢(ℂ)_τ` would be a
uniformization with kernel `Λ₀ × ℂ`. Needs: the analytic topology on `𝒢(ℂ)_τ` and its manifold
structure from regular functions (smoothness of relative dimension `dim A`, Jacobian criterion) and
invariance of domain. -/
def UniformizationDim : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), ∀ _ : DiscreteTopology Λ, IsZLattice ℝ Λ →
    𝒢.IsAnalyticUniformization τ Λ Φ → A.dim = (g : WithBot ℕ∞)

/-- **Glue `MetrizationOfUniformization`.** A group model of `A_L` with an analytic uniformization of
dimension `g = dim A` (lattice a full `ℤ`-lattice) at every `τ` carries a metrization of dimension
`g`. Needs: the kernel's `HodgeLatticeTheorem` (proved, `ZInQ.Contrib.Dim.hodgeLatticeTheorem`) for
the lattice `⋀^g ω_𝒢`; the coefficient map `coeff_τ : L ⊗ ⋀^g(𝔪/𝔪²) → ℂ`, `τ`-semilinear, from
`f ↦ d(f ∘ Φ)_0` (independent of the representative of the germ, `𝓞_L`-linear through `τ`, zero on
`𝔪²` by the product rule since `f(Φ(0)) = 0`), whose `g`-th exterior power is `jacDet Φ`; and
`coeff_τ ≠ 0` (regular functions with independent differentials are local coordinates, so the
Jacobian at `0` is invertible). -/
def MetrizationOfUniformization : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (𝒢 : GroupModel A L) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    (∀ τ : L →+* ℂ, ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ) →
    ∃ M : MetrizedModel A L g, M.model = 𝒢

/-- **`NeronMetrizable` from the kernel's AN3 existence and the two construction glues.** In fact
every group model is metrizable (the Néron property is not used). -/
theorem neronMetrizable_of (hE : AnalyticUniformizationExists) (hD : UniformizationDim)
    (hM : MetrizationOfUniformization) : NeronMetrizable := by
  intro K _ _ A L _ _ _ 𝒩 _
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨g, Λ₀, Φ₀, hd₀, hz₀, hΦ₀⟩ := hE K A L 𝒩 τ₀
  have hg : A.dim = (g : WithBot ℕ∞) := hD K A L 𝒩 τ₀ g Λ₀ Φ₀ hd₀ hz₀ hΦ₀
  obtain ⟨M, hM'⟩ := hM K A L 𝒩 g hg (fun τ => by
    obtain ⟨g', Λ, Φ, hd, hz, hΦ⟩ := hE K A L 𝒩 τ
    have hg' : g' = g := by
      have := (hD K A L 𝒩 τ g' Λ Φ hd hz hΦ).symm.trans hg
      exact_mod_cast this
    subst hg'
    exact ⟨Λ, Φ, hd, hz, hΦ⟩)
  exact ⟨g, M, hM'⟩

/-- **Glue `MetrizedDimUnique`.** Two metrizations of the same group model have the same `g`.
Needs: for `τ : L → ℂ`, `Φ : ℂ^g → 𝒢(ℂ)_τ` is a surjective homomorphism with kernel a full lattice
`Λ` (`IsZLattice ℝ`, rank `2g`), so `#𝒢(ℂ)_τ[2] = #(½Λ/Λ) = 2^{2g}`; the same count for `g'` gives
`g = g'`. Proved below (`metrizedDimUnique`). -/
def MetrizedDimUnique : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model → g = g'

/-- **2-torsion of a uniformized group.** If `Φ : ℂ^g → P` is a surjective homomorphism onto a group
with kernel a full lattice `Λ`, then `P` has exactly `2^{2g}` elements with `p² = 1`. -/
theorem card_sq_eq_one_of_uniformization {g : ℕ} {P : Type*} [Group P]
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (Φ : (Fin g → ℂ) → P) (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w)
    (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ) (hsurj : Function.Surjective Φ) :
    Nat.card {p : P // p * p = 1} = 2 ^ (2 * g) := by
  classical
  have hhalf : ∀ z : Fin g → ℂ, (2 : ℂ)⁻¹ • z + (2 : ℂ)⁻¹ • z = z := by
    intro z; rw [← add_smul]; norm_num
  have hhalf' : ∀ z : Fin g → ℂ, (2 : ℂ)⁻¹ • (z + z) = z := by
    intro z; rw [← two_smul ℂ z, smul_smul]; norm_num
  let F : Λ → {p : P // p * p = 1} := fun a => ⟨Φ ((2 : ℂ)⁻¹ • (a : Fin g → ℂ)), by
    rw [← hadd, hhalf]; exact (hker _).mpr a.2⟩
  have hF : Function.Surjective F := by
    rintro ⟨p, hp⟩
    obtain ⟨z, rfl⟩ := hsurj p
    have hz : z + z ∈ Λ := (hker _).mp (by rw [hadd]; exact hp)
    exact ⟨⟨z + z, hz⟩, Subtype.ext (by simp only [F]; rw [hhalf'])⟩
  let H : AddSubgroup Λ := (nsmulAddMonoidHom (α := Λ) 2).range
  have hrel : ∀ a b : Λ, F a = F b ↔ -a + b ∈ H := by
    intro a b
    have hsplit : (2 : ℂ)⁻¹ • (b : Fin g → ℂ) =
        (2 : ℂ)⁻¹ • (a : Fin g → ℂ) + (2 : ℂ)⁻¹ • ((-a + b : Λ) : Fin g → ℂ) := by
      simp only [Submodule.coe_add, Submodule.coe_neg, smul_add, smul_neg]; abel
    have h1 : F a = F b ↔ Φ ((2 : ℂ)⁻¹ • ((-a + b : Λ) : Fin g → ℂ)) = 1 := by
      rw [Subtype.ext_iff]
      simp only [F]
      rw [hsplit, hadd]
      constructor
      · intro h
        have := congrArg (fun q => (Φ ((2 : ℂ)⁻¹ • (a : Fin g → ℂ)))⁻¹ * q) h
        simpa using this.symm
      · intro h; rw [h, _root_.mul_one]
    rw [h1, hker]
    constructor
    · intro h
      refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
      simp only [nsmulAddMonoidHom_apply, Submodule.coe_smul_of_tower]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]; norm_num
    · rintro ⟨c, hc⟩
      have hc' : ((-a + b : Λ) : Fin g → ℂ) = (2 : ℂ) • (c : Fin g → ℂ) := by
        rw [← hc]
        simp only [nsmulAddMonoidHom_apply, Submodule.coe_smul_of_tower]
        rw [← Nat.cast_smul_eq_nsmul ℂ]; norm_num
      rw [hc', smul_smul]; norm_num
  have e : {p : P // p * p = 1} ≃ Λ ⧸ H :=
    (Setoid.quotientKerEquivOfSurjective F hF).symm.trans
      (Quotient.congrRight fun a b => by
        rw [QuotientAddGroup.leftRel_apply]; exact hrel a b)
  have := ZLattice.module_free ℝ Λ
  have := ZLattice.module_finite ℝ Λ
  rw [Nat.card_congr e, ← AddSubgroup.index, AddSubgroup.index_range_nsmul, ZLattice.rank ℝ Λ]
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/-- **`MetrizedDimUnique` is a theorem** (the 2-torsion count: `2^{2g} = #𝒢(ℂ)_τ[2] = 2^{2g'}`). -/
theorem metrizedDimUnique : MetrizedDimUnique := by
  intro K _ A L _ _ _ g g' M M' hMM
  obtain ⟨𝒢, D, hl, ha⟩ := M
  obtain ⟨𝒢', D', hl', ha'⟩ := M'
  dsimp only at hMM
  subst hMM
  obtain ⟨τ⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨Φ, hΦ, -⟩ := ha τ
  obtain ⟨Φ', hΦ', -⟩ := ha' τ
  have := D.periods_discrete τ
  have := D.periods_isZLattice τ
  have := D'.periods_discrete τ
  have := D'.periods_isZLattice τ
  have h1 := card_sq_eq_one_of_uniformization (D.periods τ) Φ hΦ.1 hΦ.2.1 hΦ.2.2.1
  have h2 := card_sq_eq_one_of_uniformization (D'.periods τ) Φ' hΦ'.1 hΦ'.2.1 hΦ'.2.2.1
  rw [h1] at h2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega


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

/-- **H-19 with `MetrizedDimUnique` discharged**: `StableHeightFinite` from N1, SS1, SS2,
`NeronMetrizable` and the kernel's `AnalyticUniformizationUnique`. -/
theorem stableHeightFinite_of' (hN1 : NeronModelExists) (hSS1 : SemistableReductionThm)
    (hSS2 : SemistableNeronBaseChange) (hMet : NeronMetrizable)
    (hU : AnalyticUniformizationUnique) : StableHeightFinite :=
  stableHeightFinite_of hN1 hSS1 hSS2 hMet hU metrizedDimUnique

end Finite

/-! ## §C. H-17, R21 (Bost) -/

/-- **Leaf R21-Bost. Bost's lower bound** (J.-B. Bost, *Périodes et isogénies des variétés abéliennes
sur les corps de nombres*, Sém. Bourbaki 795 (1994/95), Astérisque 237 (1996); the display is
UNVERIFIED: locators.md could not read it). Recalled display: `h(A) ≥ −(g/2) log(2π)` for every
abelian variety of dimension `g` over a number field, `h` the stable height in Deligne's
normalization `(i/2π)^g`, `h_D = h_F + (g/2) log π`. Stated in Deligne's normalization, the weaker of
the two readings (a Faltings-normalized display `h_F ≥ −(g/2) log 2π` implies it, as `h_D ≥ h_F`; the
Faltings-normalized reading is false for `E` with `j = 0`, `h_F ≈ −1.32`, so Deligne's is the one
meant). Residual risk: if Bost printed in a third normalization giving larger heights, e.g.
`(i/4π)^g`, this leaf would be stronger than the print; R21 itself needs only `h_F ≥ −(3/2)g`. -/
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

/-- **H-17 with `MetrizedDimUnique` discharged**: R21 from Bost, N1, SS1, SS2 and the kernel's
`AnalyticUniformizationUnique`. -/
theorem r21_of_leaves' (hB : BostLowerBound) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange)
    (hU : AnalyticUniformizationUnique) : R21_Bost :=
  r21_of_leaves hB hN1 hSS1 hSS2 hU metrizedDimUnique

/-! ## §D. H-14, R18 (Javanpeykar) -/

section R18Sec

open LeafModCurves (IsCurve IsJacobian IsBelyiFunction)
open LeafPush2 (ffAlgebra javanpeykarBound)

/-- **Leaf R18-Javanpeykar** (A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi
curves*, Algebra Number Theory 8 (2014), Thm 1.1.1, p. 90; arXiv:1403.6404v1 p. 1; height
identification p. 98 / arXiv §2.3 p. 9; read by the locator audit, docs/research/locators.md).
Printed: for a smooth projective connected curve `X/ℚ̄` of genus `g ≥ 1`,
`h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`, `h_Fal(X)` the stable Faltings height of `Jac X`.

Specialization stated: `X` defined over a number field `K` (smooth proper geometrically connected
integral, a `K`-point `P₀`), `J` its Jacobian over `K` (the kernel's Albanese predicate), `g = dim J`
(= genus), a Belyi function `t ∈ K(X)` with `d = [K(X) : K(t)]` (so `deg_B(X_ℚ̄) ≤ d`), and `x` the
published stable height of `J` (`IsStableFaltingsHeight`: computed on a Néron model over a field of
semistable reduction; it is that of `J_ℚ̄ = Jac(X_ℚ̄)`, the stable height being invariant under field
extension). Faltings' normalization: the weaker reading if the paper used Deligne's (`h_D ≥ h_F`). -/
def JavanpeykarBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    [IsIntegral X.left] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : PkgI3.AbVar K)
    (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ t : X.left.functionField,
      letI := ffAlgebra X
      IsBelyiFunction K X.left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
      ∀ x : ℝ, IsStableFaltingsHeight J x → x ≤ javanpeykarBound g d

/-- **H-14: R18 from Javanpeykar's printed bound**, N1, SS1, SS2 (identification) and the `≠ ⊤`
half of H-19 (glue `NeronMetrizable`). -/
theorem r18_of_leaves (hJ : JavanpeykarBound) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange)
    (hMet : NeronMetrizable) : LeafPush2.R18_Javanpeykar := by
  intro K _ _ X _ _ P₀ J aj hJac g hg hg1 t ht d hd hd0
  by_cases hb : stableFaltingsHeight J = ⊥
  · rw [hb]; exact bot_le
  obtain ⟨x, hx⟩ := exists_real_of_ne _ (stableFaltingsHeight_ne_top hN1 hMet J) hb
  rw [hx]
  exact EReal.coe_le_coe_iff.mpr (hJ K X P₀ J aj hJac g hg hg1 t ht d hd hd0 x
    ((isStableFaltingsHeight_iff hN1 hSS1 hSS2 J x).mpr hx))

end R18Sec

/-! ## §E. H-16, R20 (Faltings' Lemma 5) -/

/-- **Leaf R20-Faltings (Lemma 5), semistable form** (G. Faltings, *Endlichkeitssätze für abelsche
Varietäten über Zahlkörpern*, Invent. Math. 73 (1983), Lemma 5, p. 358; Raynaud, Astérisque 127
(1985), Exp. VII, Cor. 2.1.3; the lemma is UNVERIFIED: locators.md could not read it, and the
inequality is the form Pazuki 2012 Remark 2.3 attributes to it). Classification: a consequence,
not the literal print. Lemma 5 is printed as an identity with a correction term, and the inequality
also needs Raynaud's bound `0 ≤ [K:ℚ]⁻¹ log #s*Ω¹_G ≤ log deg φ` (the kernel `G` is only quasi-finite
in the multiplicative case), so Raynaud's Exp. VII Cor. 2.1.3 (UNVERIFIED) is the operative source.
For an isogeny `φ : A → B` of
abelian varieties over a number field `K`, both with semistable reduction everywhere (Néron models
`𝒩_A`, `𝒩_B` over `𝓞_K`): `|h(A) − h(B)| ≤ ½ log deg φ`. (Faltings' formula
`h(B) = h(A) + ½ log deg φ − [K:ℚ]⁻¹ log #s*Ω¹_{G/𝓞_K}` with `0 ≤ [K:ℚ]⁻¹ log # ≤ log deg φ`.) -/
def FaltingsLemma5 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y → |x - y| ≤ (1 / 2) * Real.log (isogDeg φ)

/-- **Glue `IsogenySemistableBaseChange`.** Given an isogeny `φ : A → B` over `K` with published
stable heights `x`, `y`, there are a number field `L` and an isogeny `φ' : A' → B'` over `L` of the
same degree whose Néron models over `𝓞_L` are semistable with heights `x`, `y`. Intended witness:
`L` a common field of semistable reduction (compositum of the two fields in the hypotheses),
`A' = A_L`, `B' = B_L`, `φ' = φ_L`. Needs: base change of isogenies (finite, surjective, homomorphism:
stable under base change) and `#ker φ(K̄) = #ker φ_L(L̄)` (both the degree, characteristic `0`);
semistability of `A_L`, `B_L` (SGA 7 IX 3.3, semistability persists under extension); the transport
of group models along `(A_L)_L ≅ A_L` (`GroupModel A L` vs `GroupModel (A.baseChange L) L`) preserving
the Néron property and the height; and `isStableFaltingsHeight_unique`. -/
def IsogenySemistableBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ x y : ℝ, IsStableFaltingsHeight A x → IsStableFaltingsHeight B y →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (A' B' : PkgI3.AbVar L) (φ' : A'.X ⟶ B'.X)
      (𝒩A : GroupModel A' L) (𝒩B : GroupModel B' L), IsIsogeny φ' ∧ isogDeg φ' = isogDeg φ ∧
      𝒩A.IsNeronModel ∧ 𝒩B.IsNeronModel ∧ IsSemistable 𝒩A ∧ IsSemistable 𝒩B ∧
      𝒩A.height = x ∧ 𝒩B.height = y

/-- **H-16: R20 from Faltings' Lemma 5 (semistable form)**, the glue `IsogenySemistableBaseChange`
and N1, SS1, SS2 (identification). -/
theorem r20_of_leaves (hF : FaltingsLemma5) (hG : IsogenySemistableBaseChange)
    (hN1 : NeronModelExists) (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange) :
    R20_FaltingsLemma5 := by
  intro K _ _ A B φ hφ x y hx hy
  obtain ⟨L, i1, i2, A', B', φ', 𝒩A, 𝒩B, hφ', hdeg, hA, hB, sA, sB, hxA, hyB⟩ :=
    hG K A B φ hφ x y ((isStableFaltingsHeight_iff hN1 hSS1 hSS2 A x).mpr hx)
      ((isStableFaltingsHeight_iff hN1 hSS1 hSS2 B y).mpr hy)
  rw [← hdeg]
  exact hF L A' B' φ' hφ' 𝒩A 𝒩B hA hB sA sB x y hxA hyB

/-- **Leaf SS3. Semistability persists under finite extension** (SGA 7 I, Exp. IX, 3.3, UNVERIFIED
number; the same proposition as SS2: if `A_L` is semistable, so is `A_{L'}` for `L'/L` finite). -/
def SemistablePersists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (𝒩 : GroupModel A L), 𝒩.IsNeronModel → IsSemistable 𝒩 →
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
      (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel → IsSemistable 𝒩'

/-- **Leaf R20-Faltings (Lemma 5) for base changes.** Faltings' Lemma 5 (as in `FaltingsLemma5`)
applied over a number field `L ⊇ K` to `A_L`, `B_L` and `φ_L`, in the kernel's encoding of base
change: Néron models of `A_L`, `B_L` are `GroupModel A L`, `GroupModel B L`, and
`deg φ_L = deg φ = #ker φ(K̄)` (characteristic `0`). The printed lemma is stated for abelian varieties
over an arbitrary number field, so this is an instance of it, not a consequence needing an argument;
`FaltingsLemma5` is its case `L = K`. -/
def FaltingsLemma5BC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L]
      (𝒩A : GroupModel A L) (𝒩B : GroupModel B L), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y → |x - y| ≤ (1 / 2) * Real.log (isogDeg φ)

/-- **H-16 without glue: R20 from Faltings' Lemma 5 (for base changes)** and the leaves N1, SS1,
SS2, SS3: both heights are computed on Néron models over a common field of semistable reduction
(the compositum of the two fields given by SS1). -/
theorem r20_of_leaves' (hF : FaltingsLemma5BC) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange)
    (hSS3 : SemistablePersists) : R20_FaltingsLemma5 := by
  intro K _ _ A B φ hφ x y hx hy
  obtain ⟨L₁, i1, i2, i3, hL₁⟩ := hSS1 K A
  obtain ⟨L₂, j1, j2, j3, hL₂⟩ := hSS1 K B
  obtain ⟨L, k1, k2, k3, k4, k5, t1, t2⟩ := compositum K L₁ L₂
  obtain ⟨𝒩A₁, hA₁⟩ := hN1 K A L₁
  obtain ⟨𝒩B₂, hB₂⟩ := hN1 K B L₂
  obtain ⟨𝒩A, hA⟩ := hN1 K A L
  obtain ⟨𝒩B, hB⟩ := hN1 K B L
  have sA : IsSemistable 𝒩A := hSS3 K A L₁ 𝒩A₁ hA₁ (hL₁ 𝒩A₁ hA₁) L 𝒩A hA
  have sB : IsSemistable 𝒩B := hSS3 K B L₂ 𝒩B₂ hB₂ (hL₂ 𝒩B₂ hB₂) L 𝒩B hB
  have hxA : 𝒩A.height = x := (stableFaltingsHeight_eq_of_semistable hN1 hSS2 A 𝒩A hA sA).symm.trans hx
  have hyB : 𝒩B.height = y := (stableFaltingsHeight_eq_of_semistable hN1 hSS2 B 𝒩B hB sB).symm.trans hy
  exact hF K A B φ hφ L 𝒩A 𝒩B hA hB sA sB x y hxA hyB

/-- The literal-over-`K` form is the case `L = K` of the base-change form. -/
theorem faltingsLemma5_of_BC (h : FaltingsLemma5BC) : FaltingsLemma5 :=
  fun K _ _ A B φ hφ 𝒩A 𝒩B hA hB sA sB x y hx hy => h K A B φ hφ K 𝒩A 𝒩B hA hB sA sB x y hx hy

/-! ## §G. H-18, R22 (Pazuki) -/

section R22Sec

open LeafPush2 (CPts IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight
  pazukiC2)

variable {F : Type*} [Field F] [NumberField F] {Idx : Type*} [Fintype Idx]

/-- The multiplicative height of a point of `ℙ(F^ι)` with **Euclidean (`ℓ²`) norms at the
archimedean places** and max norms at the finite ones:
`∏_{v | ∞} (∑_i |z_i|_v²)^{n_v/2} · ∏_{v ∤ ∞} max_i |z_i|_v` (Mathlib's admissible absolute values of
a number field: the archimedean ones with multiplicity `n_v`, the finite ones normalized; the
same data as Mathlib's `Height.mulHeight`, whose archimedean factor is `max_i |z_i|_v`). Junk value
`1` at `z = 0`. -/
noncomputable def mulHeightL2 (z : Idx → F) : ℝ :=
  haveI : Decidable (z = 0) := Classical.propDecidable _
  if z = 0 then 1 else
    (Height.AdmissibleAbsValues.archAbsVal.map fun v ↦ Real.sqrt (∑ i, v (z i) ^ 2)).prod *
      ∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal, ⨆ i, v.val (z i)

/-- The absolute logarithmic `ℓ²`-height `h₂(z) = log(mulHeightL2 z)/[F : ℚ]` (Pazuki's theta height
uses this archimedean normalization, the Fubini–Study / Euclidean one, locators.md item 5). -/
noncomputable def absLogHeightL2 (z : Idx → F) : ℝ :=
  Real.log (mulHeightL2 z) / Module.finrank ℚ F

theorem mulHeight_le_mulHeightL2 [Nonempty Idx] (z : Idx → F) :
    Height.mulHeight z ≤ mulHeightL2 z := by
  by_cases hz : z = 0
  · simp [mulHeightL2, hz]
  rw [Height.mulHeight_eq hz]
  simp only [mulHeightL2, hz, ite_false]
  have hfin : 0 ≤ ∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := F), ⨆ i, v.val (z i) :=
    finprod_nonneg fun v => le_ciSup_of_le (Finite.bddAbove_range _) (Classical.arbitrary Idx)
      (v.val.nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ hfin
  refine Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => ?_) (fun v _ => ?_)
  · exact le_ciSup_of_le (Finite.bddAbove_range _) (Classical.arbitrary Idx) (v.nonneg _)
  · refine ciSup_le fun i => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun j => v (z j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)

/-- The sup-norm height (the kernel's `absLogHeight`, through Mathlib's `Height.logHeight`) is at
most the `ℓ²`-height. -/
theorem absLogHeight_le_absLogHeightL2 [Nonempty Idx] (z : Idx → F) :
    absLogHeight z ≤ absLogHeightL2 z := by
  unfold absLogHeight absLogHeightL2 Height.logHeight
  have hd : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
  gcongr
  exact mulHeight_le_mulHeightL2 z

/-- **Leaf R22-Pazuki, Cor. 1.3(2) in its printed two-sided form** (F. Pazuki, *Theta height and
Faltings height*, Bull. SMF 140 (2012), Cor. 1.3(2), pp. 21-22, `g = r = 2`; Deligne's metric p. 26;
theta height p. 30; arXiv:0907.1458v2 Cor. 1.3(2) p. 3, Def. 2.1 pp. 6-7, Def. 2.6 p. 9; read by
the locator audit, docs/research/locators.md item 5): for a principally polarized abelian surface
`(A, L)` over `ℚ̄` with `H_Θ = max(1, h_Θ(A, L))`, `H_D = max(1, h_D(A))`:
`|H_Θ − H_D/2| ≤ C₂(2,2) log(min(H_Θ, H_D) + 2)`, `C₂(2,2) = 1000·2⁴·(log 2⁴)⁵`.

Lean reading: `A` an abelian surface over a number field `K` (a specialization: `A_ℚ̄` via any
embedding), `x` its published stable height (Faltings' normalization), so `h_D = x + log π`
(Deligne's metric, `g = 2`, locators.md); the principal polarization with a symplectic basis is a
Siegel matrix `Ω` that is a period matrix of the lattice of a uniformization of `A(ℂ)_σ` (the
kernel's `IsPeriodMatrix`: `ℂ²/Λ ≅ ℂ²/(Ωℤ²+ℤ²)` carries `(Im Ω)⁻¹`); `h_Θ` is the `ℓ²`-height of the
theta-null point `[θ[a;b](0, Ω)]_{a,b ∈ {0,½}²}` (any algebraic representative `z`). The
identification of Pazuki's level-2 theta coordinates (Def. 2.6) with the classical `θ[a;b](0, Ω)`
is UNVERIFIED (locators.md, leaf-review-b premise 3), as is the algebraicity over `ℚ̄` of every
analytic principal polarization (Riemann/Lefschetz; standard). Risk (review, 11-14): if Pazuki's
coordinates are the second-order constants `θ[a;0](0, 2Ω)`, then Riemann's quadratic relation gives
only `h(classical) ≤ h_Θ + log 4`. In that case this leaf, and the kernel's row `R22_Pazuki` itself,
would overstate the print by about `log 4`; the hardened `R22_plus3` slack (`3 − log π`, halved) does
not cover it. -/
def PazukiCor13 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∀ (F : Type) [Field F] [NumberField F] (emb : F →+* ℂ) (z : Char2 → F) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      |max 1 (absLogHeightL2 z) - max 1 (x + Real.log Real.pi) / 2| ≤
        pazukiC2 * Real.log (min (max 1 (absLogHeightL2 z)) (max 1 (x + Real.log Real.pi)) + 2)

theorem pazukiC2_nonneg : 0 ≤ pazukiC2 := by
  unfold pazukiC2
  have : 0 < Real.log (2 ^ 4) := Real.log_pos (by norm_num)
  positivity

/-- **Leaf R22-Pazuki, upper half** (read off the same display as `PazukiCor13`, the side of the
absolute value that bounds `H_Θ` from above): `H_Θ − H_D/2 ≤ C₂ log(min(H_Θ, H_D) + 2)`. The row
needs only this half. -/
def PazukiCor13Upper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∀ (F : Type) [Field F] [NumberField F] (emb : F →+* ℂ) (z : Char2 → F) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      max 1 (absLogHeightL2 z) - max 1 (x + Real.log Real.pi) / 2 ≤
        pazukiC2 * Real.log (min (max 1 (absLogHeightL2 z)) (max 1 (x + Real.log Real.pi)) + 2)

theorem pazukiCor13Upper_of (h : PazukiCor13) : PazukiCor13Upper :=
  fun K _ _ A hA x hx σ Λ Φ hΦ Ω hΩ hPer F _ _ emb z c hc hz =>
    (abs_le.mp (h K A hA x hx σ Λ Φ hΦ Ω hΩ hPer F emb z c hc hz)).2

/-- **The algebra from the upper half to the row's bound** (bound the minimum by `H_D ≤ X`, and
`h ≤ H_Θ`). -/
theorem pazuki_upper_of_upper {hΘ hD X C : ℝ} (hC : 0 ≤ C) (hX : max 1 hD ≤ X)
    (h1 : max 1 hΘ - max 1 hD / 2 ≤ C * Real.log (min (max 1 hΘ) (max 1 hD) + 2)) :
    hΘ ≤ X / 2 + C * Real.log (X + 2) := by
  have hmin : min (max 1 hΘ) (max 1 hD) ≤ X := (min_le_right _ _).trans hX
  have hpos : 0 < min (max 1 hΘ) (max 1 hD) + 2 := by
    have : (1 : ℝ) ≤ min (max 1 hΘ) (max 1 hD) := le_min (le_max_left _ _) (le_max_left _ _)
    linarith
  have hlog : Real.log (min (max 1 hΘ) (max 1 hD) + 2) ≤ Real.log (X + 2) :=
    Real.log_le_log hpos (by linarith)
  have h2 : C * Real.log (min (max 1 hΘ) (max 1 hD) + 2) ≤ C * Real.log (X + 2) :=
    mul_le_mul_of_nonneg_left hlog hC
  have h3 : hΘ ≤ max 1 hΘ := le_max_right _ _
  linarith

/-- **H-18: R22 from the upper half of Pazuki's printed corollary** (`ℓ²` theta height, Deligne's
`h_D`), N1, SS1, SS2 (identification), the comparison sup-norm height `≤` `ℓ²`-height and the algebra.
No glue beyond the identification leaves. -/
theorem r22_of_upper (hP : PazukiCor13Upper) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange) :
    LeafPush2.R22_Pazuki := by
  intro K _ _ A hA x hx X hX σ Λ Φ hΦ Ω hΩ hPer F _ _ emb z c hc hz
  have h := hP K A hA x ((isStableFaltingsHeight_iff hN1 hSS1 hSS2 A x).mpr hx) σ Λ Φ hΦ Ω hΩ hPer
    F emb z c hc hz
  exact (absLogHeight_le_absLogHeightL2 z).trans (pazuki_upper_of_upper pazukiC2_nonneg hX h)

/-- **H-18 from the two-sided printed corollary.** -/
theorem r22_of_leaves (hP : PazukiCor13) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange) :
    LeafPush2.R22_Pazuki :=
  r22_of_upper (pazukiCor13Upper_of hP) hN1 hSS1 hSS2

end R22Sec

/-! ## §H. Bonus: H-15, R19 (Gaudron–Rémond), the same identification -/

/-- **Leaf R19-GR over the published height** (Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4,
p. 2060; `κ` and `α(g) = 1024g³`, p. 2058; read by the locator audit): the kernel's
`R19_GaudronRemond` with `stableFaltingsHeight A = x` replaced by `IsStableFaltingsHeight A x`
(GR use the stable height in Faltings' original normalization). -/
def GaudronRemondThm14 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsStableFaltingsHeight A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **H-15: R19 from Gaudron–Rémond over the published height and N1, SS1, SS2.** -/
theorem r19_of_leaves (hGR : GaudronRemondThm14) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange) : R19_GaudronRemond :=
  fun K _ _ A B g x hg hx hiso =>
    hGR K A B g x hg ((isStableFaltingsHeight_iff hN1 hSS1 hSS2 A x).mpr hx) hiso

/-! ## §J. One bundle: the six height rows from the published-form leaves and the remaining glue -/

/-- **The published-form leaves of this file** (with the kernel's N1). -/
structure HeightLeaves : Prop where
  n1 : NeronModelExists
  ss1 : SemistableReductionThm
  ss2 : SemistableNeronBaseChange
  ss3 : SemistablePersists
  bost : BostLowerBound
  javanpeykar : JavanpeykarBound
  faltings5 : FaltingsLemma5BC
  pazuki : PazukiCor13Upper
  gaudronRemond : GaudronRemondThm14

/-- **The remaining glue**: the kernel's two halves of AN3 and the two construction glues. -/
structure HeightGlue : Prop where
  an3Exists : AnalyticUniformizationExists
  an3Unique : AnalyticUniformizationUnique
  unifDim : UniformizationDim
  metrize : MetrizationOfUniformization

/-- **H-14, H-15, H-16, H-17, H-18, H-19 from the leaves and the glue.** R19, R20 and R22 use the
leaves only. -/
theorem heightRows_of (l : HeightLeaves) (gl : HeightGlue) :
    LeafPush2.R18_Javanpeykar ∧ R19_GaudronRemond ∧ R20_FaltingsLemma5 ∧ R21_Bost ∧
      LeafPush2.R22_Pazuki ∧ StableHeightFinite :=
  have hMet := neronMetrizable_of gl.an3Exists gl.unifDim gl.metrize
  ⟨r18_of_leaves l.javanpeykar l.n1 l.ss1 l.ss2 hMet,
    r19_of_leaves l.gaudronRemond l.n1 l.ss1 l.ss2,
    r20_of_leaves' l.faltings5 l.n1 l.ss1 l.ss2 l.ss3,
    r21_of_leaves' l.bost l.n1 l.ss1 l.ss2 gl.an3Unique,
    r22_of_upper l.pazuki l.n1 l.ss1 l.ss2,
    stableHeightFinite_of' l.n1 l.ss1 l.ss2 hMet gl.an3Unique⟩

/-- The three rows that need no glue. -/
theorem heightRows_leavesOnly (l : HeightLeaves) :
    R19_GaudronRemond ∧ R20_FaltingsLemma5 ∧ LeafPush2.R22_Pazuki :=
  ⟨r19_of_leaves l.gaudronRemond l.n1 l.ss1 l.ss2,
    r20_of_leaves' l.faltings5 l.n1 l.ss1 l.ss2 l.ss3,
    r22_of_upper l.pazuki l.n1 l.ss1 l.ss2⟩

/-! ## §I. Consistency: the new definitions and leaves at the zero abelian variety

The only abelian variety Mathlib can construct is `AbVar.zero K` (`Spec K`). There, every
geometric fibre of every Néron model is the trivial group scheme, which is semi-abelian (`U = G`,
`B = 0`, `r = 0`), so `IsSemistable` holds, the leaves SS1, SS2, SS3 hold, and `0` is the published
stable height. This checks that `HasSemiAbelianIdentityComponent` and `IsStableFaltingsHeight` are
satisfiable as written (it does not exercise the torus or abelian part). -/

section ZeroAV

/-- The trivial group scheme over a field is semi-abelian. -/
theorem hasSemiAbelianIdentityComponent_of_iso_unit {k : Type} [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (i : G ≅ 𝟙_ _) :
    HasSemiAbelianIdentityComponent G := by
  have hiso : IsIso i.hom.left := by
    have : IsIso ((Over.forget _).map i.hom) := inferInstance
    exact this
  refine ⟨G, inferInstance, 𝟙 G, ?_, inferInstance, ?_, PkgI3.AbVar.zero k, i.hom,
    isMonHom_of_iso_unit (Iso.refl _) _, ?_, ?_, 0, fun R _ _ => 1, fun R _ _ => ?_,
    fun R _ _ u => ?_, fun R S _ _ _ _ f t => hom_ext_of_iso_unit i _ _⟩
  · rw [Over.id_left]; infer_instance
  · -- `G.left ≅ Spec k`, the spectrum of a field, is connected
    have hc : ConnectedSpace ((𝟙_ (Over (Spec (CommRingCat.of k)))).left) :=
      (inferInstance : ConnectedSpace (Spec (CommRingCat.of k)))
    have hsurj : Function.Surjective
        (i.inv.left.base : (𝟙_ (Over (Spec (CommRingCat.of k)))).left → G.left) := by
      have : IsIso i.inv.left := by
        have : IsIso ((Over.forget _).map i.inv) := inferInstance
        exact this
      exact (Scheme.homeoOfIso (asIso i.inv.left)).surjective
    exact hsurj.connectedSpace i.inv.left.base.hom.continuous
  · exact (inferInstance : Flat i.hom.left)
  · exact (inferInstance : Surjective i.hom.left)
  · intro a b _
    exact Subsingleton.elim a b
  · constructor
    · intro _
      rw [hom_ext_of_iso_unit i u 1]
      exact one_mem _
    · intro _
      exact hom_ext_of_iso_unit (Iso.refl _) _ _

variable (K : Type) [Field K]

/-- Every Néron model of the zero abelian variety is semistable. -/
theorem isSemistable_zero {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel (PkgI3.AbVar.zero K) L) (h : 𝒩.IsNeronModel) : IsSemistable 𝒩 := by
  intro 𝔭 _
  obtain ⟨i⟩ := neron_zero_iso_unit K L 𝒩 h
  exact hasSemiAbelianIdentityComponent_of_iso_unit _
    ((Over.pullback _).mapIso i ≪≫ (Functor.Monoidal.εIso (Over.pullback _)).symm)

/-- `0` is the published stable height of the zero abelian variety. -/
theorem isStableFaltingsHeight_zero [NumberField K] :
    IsStableFaltingsHeight (PkgI3.AbVar.zero K) 0 :=
  ⟨K, inferInstance, inferInstance, inferInstance, trivModel K K, trivModel_isNeronModel K K,
    isSemistable_zero K _ (trivModel_isNeronModel K K), by
      rw [groupModel_height_zero, EReal.coe_zero]⟩

/-- SS1 at the zero abelian variety (`L₀ = K`). -/
theorem semistableReductionThm_zero [NumberField K] :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀),
      ∀ 𝒩 : GroupModel (PkgI3.AbVar.zero K) L₀, 𝒩.IsNeronModel → IsSemistable 𝒩 :=
  ⟨K, inferInstance, inferInstance, inferInstance, fun 𝒩 h => isSemistable_zero K 𝒩 h⟩

/-- SS3 at the zero abelian variety. -/
theorem semistablePersists_zero (L' : Type) [Field L'] [NumberField L'] [Algebra K L']
    (𝒩' : GroupModel (PkgI3.AbVar.zero K) L') (h : 𝒩'.IsNeronModel) : IsSemistable 𝒩' :=
  isSemistable_zero K 𝒩' h

/-- SS2 at the zero abelian variety (the kernel's proof of N2 there:
`semistableNeronIdentityComponent_zero`, with `L₀ = K`; here for any `L`). -/
theorem semistableNeronBaseChange_zero (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel (PkgI3.AbVar.zero K) L) (h𝒩 : 𝒩.IsNeronModel)
    (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒩' : GroupModel (PkgI3.AbVar.zero K) L') (h𝒩' : 𝒩'.IsNeronModel) :
    ∃ 𝒰 𝒱 : GroupModel (PkgI3.AbVar.zero K) L', IsBaseChangeOf 𝒱 𝒩 ∧ IsOpenSubgroupModel 𝒰 𝒩' ∧
      IsOpenSubgroupModel 𝒰 𝒱 := by
  obtain ⟨i⟩ := neron_zero_iso_unit K L' 𝒩' h𝒩'
  obtain ⟨j⟩ := neron_zero_iso_unit K L 𝒩 h𝒩
  refine ⟨trivModel K L', trivModel K L', ?_, ?_, ?_⟩
  · unfold IsBaseChangeOf
    exact ⟨(Functor.Monoidal.εIso _) ≪≫ ((Over.pullback _).mapIso j).symm,
      isMonHom_of_iso_unit ((Over.pullback _).mapIso j ≪≫ (Functor.Monoidal.εIso _).symm) _⟩
  · refine ⟨i.inv, ?_, ⟨hom_ext_of_iso_unit i _ _, hom_ext_of_iso_unit i _ _⟩⟩
    show IsOpenImmersion ((Over.forget _).map i.inv)
    infer_instance
  · refine ⟨𝟙 _, ?_, inferInstance⟩
    rw [Over.id_left]; infer_instance

end ZeroAV

end ZInQ.HeightSplit


/-! ## g0-dim: `DimFinite` and `DimBaseChange` proved (task g0-dim; body of `scratch/g0-dim/Dim.lean` §1-§2) -/

section G0DimSec

set_option linter.style.haveILetI false

open Order TensorProduct

namespace G0Dim

/-! ## §1. Commutative algebra -/


/-- Integral injective extensions have the same Krull dimension (going up + incomparability;
Stacks 00OK, Matsumura Thm 9.4 — STANDARD). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- **Stacks 00P4 (affine case), proved.** For a finitely generated algebra `R` over a field `K`
and any field extension `L/K`, `dim (R ⊗_K L) = dim R`. Proof: Noether normalization
`K[X_1..X_s] → R` (finite, injective) base-changes to `L[X_1..X_s] → R ⊗ L` (finite, injective
since `L` is flat over `K`). -/
theorem ringKrullDim_tensor_field (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (L : Type*) [Field L] [Algebra K L] :
    ringKrullDim (R ⊗[K] L) = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with h | h
  · haveI : Subsingleton (R ⊗[K] L) := by
      have h1 : (1 : R ⊗[K] L) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, TensorProduct.zero_tmul]
      exact subsingleton_of_zero_eq_one h1.symm
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    have hR : ringKrullDim R = s := by
      letI := g.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
      rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
        ringKrullDim_mvPolynomial_field]
    let g' := Algebra.TensorProduct.map g (AlgHom.id K L)
    have g'inj : Function.Injective g' :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) g.toLinearMap ginj
    have g'fin : g'.toRingHom.Finite := RingHom.Finite.tensorProductMap gfin (by exact RingHom.Finite.id L)
    have hP : ringKrullDim (MvPolynomial (Fin s) K ⊗[K] L) = s := by
      rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv), ringKrullDim_mvPolynomial_field]
    rw [hR, ← hP]
    letI := g'.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K ⊗[K] L) (R ⊗[K] L) := ⟨g'fin.to_isIntegral⟩
    exact ringKrullDim_eq_of_isIntegral_of_injective g'inj

/-- A finitely generated algebra over a field has finite Krull dimension (or is zero). -/
theorem ringKrullDim_le_of_finiteType (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] : ∃ n : ℕ, ringKrullDim R ≤ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
    refine ⟨s, le_of_eq ?_⟩
    rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; STANDARD). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

open AlgebraicGeometry CategoryTheory Limits

theorem scheme_dim_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_openEmbedding (fun i => 𝒰.f i) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


/-- **Stacks 00P4, affine piece over `Spec K`.** For `m : Spec R → Spec K` locally of finite
type, `Spec R ×_K Spec L ≅ Spec (R ⊗_K L)` has the dimension of `Spec R`. -/
theorem dim_pullback_spec {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType m] :
    topologicalKrullDim (pullback m (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim (Spec R) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  have e := scheme_dim_eq_of_iso (pullbackSpecIso K R L)
  refine e.trans ?_
  rw [spec_dim, spec_dim]
  exact ringKrullDim_tensor_field K R L

/-- A scheme of finite type over a field: each affine piece `Spec R → Spec K` has bounded
dimension. -/
theorem dim_spec_le {K : Type} [Field K] (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType m] : ∃ n : ℕ, topologicalKrullDim (Spec R) ≤ n := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [spec_dim]
  exact ringKrullDim_le_of_finiteType K R

/-- **Dimension is invariant under field base change** (Stacks 00P4 globalized; proved). For a
scheme `X` locally of finite type over a field `K` and any field extension `L/K`,
`dim (X ×_K L) = dim X`. -/
theorem dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 := X.affineCover
  rw [scheme_dim_eq_iSup_cover 𝒰, scheme_dim_eq_iSup_cover (𝒰.pullback₁ (pullback.fst h g))]
  refine iSup_congr fun i => ?_
  have e : (𝒰.pullback₁ (pullback.fst h g)).X i ≅ pullback (𝒰.f i ≫ h) g :=
    (pullbackSymmetry _ _).trans (pullbackRightPullbackFstIso h g (𝒰.f i))
  rw [scheme_dim_eq_of_iso e]
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
  exact @dim_pullback_spec K _ L _ _ _ (𝒰.f i ≫ h) hc

theorem exists_nat_of_le (x : WithBot ℕ∞) (h0 : x ≠ ⊥) (N : ℕ) (h : x ≤ N) :
    ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.mp h') (by simp)
    | coe n => exact ⟨n, rfl⟩

/-- **A nonempty scheme of finite type over a field has finite dimension** (proved). -/
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  let 𝒰 := X.affineCover.finiteSubcover
  have hb : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := fun i => by
    haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
    exact @dim_spec_le K _ _ (𝒰.f i ≫ h) hc
  choose n hn using hb
  have hle : topologicalKrullDim X ≤ ((∑ i, n i : ℕ) : WithBot ℕ∞) := by
    rw [scheme_dim_eq_iSup_cover 𝒰]
    refine iSup_le fun i => (hn i).trans ?_
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hne : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    haveI : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  exact exists_nat_of_le _ hne _ hle

end G0Dim

end G0DimSec

namespace ZInQ.Metrization
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)
/-- **Leaf (AN3 with its dimension: the uniformization theorem).** For every smooth group model
`𝒢` of `A_L`, every `τ : L → ℂ` and `g = dim A`, there are a full lattice `Λ ⊂ ℂ^g` and an analytic
uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ`. This is def-faltings'
`AnalyticUniformizationExists` with the dimension pinned to `dim A` (`𝒢(ℂ)_τ = A_τ(ℂ)` is a compact
connected complex Lie group of dimension `dim A`, hence `≅ ℂ^g/Λ`: Mumford, *Abelian varieties*,
§1 and §4 (UNVERIFIED locators), with Serre's GAGA for the analytic structure of `A_τ(ℂ)`).
Implies `AnalyticUniformizationExists` (`analyticUniformizationExists_of`). -/
def AnalyticUniformizationOfDim : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ

/-- **Glue (the Jacobian descends to the Hodge line).** For an analytic uniformization `Φ` of
`𝒢(ℂ)_τ`, the Jacobian determinant `jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` depends only on the
classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`, is `𝓞_L`-multilinear (through `τ`) and alternating in them, hence is
the value on `1 ⊗ df₁ ∧ ⋯ ∧ df_g` of a `τ`-semilinear map `hodgeSpace g → ℂ`. Why true: `Φ 0 = 1`
lies over `ξ`; the germ `f ∘ Φ` at `0` is independent of the representative of `f` (`dom Φ U`
open); evaluation at a complex point is a ring map, so `(f f') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)` near `0`,
and for `f, f' ∈ 𝔪_ξ` both vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz); a function from
`𝓞_L` acts by the constant `τ(a)`. Then `⋀^g` (universal property) and `L ⊗_{𝓞_L} -` (extension
of scalars along `τ`) give the map. Elementary calculus plus Mathlib's scheme API; unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

/-- **Glue (local parameters are analytic coordinates).** For `g = dim A` and an analytic
uniformization `Φ` of `𝒢(ℂ)_τ` with a full lattice as kernel, some `f₁, …, f_g ∈ 𝔪_ξ` have
`jacDet Φ f ≠ 0`. Why true (STANDARD): `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}` is regular of dimension `g`
(smoothness); a regular system of parameters `f₁, …, f_g` gives holomorphic coordinates of the
complex manifold `A_τ(ℂ)` at `0` (Serre, GAGA, or the holomorphic implicit function theorem),
and `Φ` is a local biholomorphism at `0`, so `(f_i ∘ Φ)` has invertible Jacobian at `0`.
Unproved (needs the analytic structure of `A_τ(ℂ)`). -/
def JacDetNondegenerate : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      IsZLattice ℝ Λ → 𝒢.IsAnalyticUniformization τ Λ Φ →
      ∃ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk, 𝒢.jacDet Φ f ≠ 0
/-- **Glue (local product structure of `𝒢₁ ×_{𝓞_L} 𝒢₂` at complex points).** For
`e : 𝒢P ≅ 𝒢₁ × 𝒢₂`, an open `U ⊂ 𝒢P`, `s ∈ Γ(U)` and complex points `p₁`, `p₂` with
`e⁻¹(p₁, p₂) ∈ U(ℂ)`, there are opens `V₁ ∋ p₁`, `V₂ ∋ p₂` and regular functions
`a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that `H = Σ c_k ⊗ d_k` does not vanish at `(p₁, p₂)`,
and at every `(p₁', p₂') ∈ V₁(ℂ) × V₂(ℂ)` with `H(p₁', p₂') ≠ 0`: `e⁻¹(p₁', p₂') ∈ U(ℂ)` and
`s(e⁻¹(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`. Why true (STANDARD): take affine
`V₁ = Spec R₁`, `V₂ = Spec R₂` (over the affine `Spec 𝓞_L`), so `V₁ ×_{𝓞_L} V₂ = Spec(R₁ ⊗ R₂)`
is open in the product; choose a basic open `D(h)` of it with `(p₁, p₂) ∈ D(h) ⊆ e(U)`,
`h ∈ R₁ ⊗ R₂`; on `D(h)`, `s = a/h^m` with `a ∈ R₁ ⊗ R₂`; take `H = h^m` and expand `H` and `a`
as sums of pure tensors; a pure tensor `c ⊗ d` evaluates at `(p₁', p₂')` to `c(p₁') d(p₂')`.
Unproved (needs Mathlib's affine opens of pullbacks and sections on basic opens). -/
def ProductLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (τ : L →+* ℂ) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ e.inv).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ e.inv).left ⁻¹ᵁ U ∧
        𝒢P.evalAt (lift p₁' p₂' ≫ e.inv) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)
end ZInQ.Metrization


/-! ## metrization: two of the four clauses of `JacDetMultilinear`, proved

`Φ 0 = 1` lies over `ξ` (`zero_mem_dom`); `germAlong Φ t` agrees near `0` with `z ↦ evalAt (Φ z) U s`
for every representative `(U, s)` of `t` (`germAlong_eventuallyEq`); hence slot additivity
(`jacDet_update_add`). Vanishing on equal slots is immediate (`jacDet_eq_zero_of_eq`). What
remains is `JacDetClassScalar` (clauses (i) and (iii)). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

section Germ

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec ℂ → Spec 𝓞_L` (via `τ`) hits the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  haveI : x.asIdeal.IsPrime := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
  apply PrimeSpectrum.ext
  show Ideal.comap (τ.comp (algebraMap (𝓞 L) L)) x.asIdeal = ⊥
  rw [hx]
  exact Ideal.comap_bot_of_injective _
    (τ.injective.comp (IsFractionRing.injective (𝓞 L) L))

/-- The identity complex point lies over `ξ`. -/
theorem one_left_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (1 : 𝒢.Pts τ).left x = 𝒢.genericUnit := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x = 𝒢.unitSection (genericPt L)
  rw [Over.comp_left]
  change (η[𝒢.G]).left ((toUnit (GroupModel.ptC (L := L) τ)).left x) = _
  rw [hw, ptC_hom_apply]
  rfl

/-- For an analytic uniformization, `0 ∈ dom Φ U` whenever `ξ ∈ U`. -/
theorem zero_mem_dom {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := by
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
  rw [h1]
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ U
  erw [one_left_apply]
  exact m

/-- `evalAt` is compatible with restriction. -/
theorem evalAt_res {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens} (i : W ⟶ U)
    (hW : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) = 𝒢.evalAt p U s := by
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hW.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  unfold GroupModel.evalAt
  rw [dif_pos hW, dif_pos hU, ← Scheme.Hom.map_appLE p.left hW i.op]
  rfl

/-- `evalAt` is additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s + s') = 𝒢.evalAt p U s + 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- **`germAlong Φ t` is, near `0`, the function of any representative of `t`.** -/
theorem germAlong_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) (s : Γ(𝒢.G.left, U)) :
    𝒢.germAlong Φ (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s) =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) U s := by
  unfold GroupModel.germAlong
  obtain ⟨W, mW, i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit _ m _ s
    (𝒢.exists_rep (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s)).choose_spec.choose_spec.choose_spec
  filter_upwards [(hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz
  rw [← evalAt_res 𝒢 (Φ z) i₁ hz, ← evalAt_res 𝒢 (Φ z) i₂ hz s, hW]

/-- `germAlong Φ t` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep t
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) U s) 0 :=
    (hΦ.2.2.2.2 U s).differentiableAt ((hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m))
  exact hd.congr_of_eventuallyEq (germAlong_eventuallyEq 𝒢 hΦ U m s)

/-- `germAlong Φ (x + y) = germAlong Φ x + germAlong Φ y` near `0`. -/
theorem germAlong_add_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x + y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x + 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hsum : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s +
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s +
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_add, TopCat.Presheaf.germ_res_apply]
  rw [hsum]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.add_apply, h1, h2, h3, evalAt_add, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- **Clause (ii) of `JacDetMultilinear`, proved: slot additivity.** -/
theorem jacDet_update_add {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
    (x y : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (x + y)) =
      𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((x + y : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      row (x : 𝒢.genStalk) + row (y : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_add, Pi.add_apply]
    rw [(germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, e, hrow, Matrix.det_updateRow_add]

/-- **Clause (iv) of `JacDetMultilinear`, proved: equal slots give `0`.** -/
theorem jacDet_eq_zero_of_eq {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g) (h : f i = f j)
    (hij : i ≠ j) : 𝒢.jacDet Φ f = 0 := by
  unfold GroupModel.jacDet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [h]

end Germ
section Scalar0
variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)
/-- `evalAt` is multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s * s') = 𝒢.evalAt p U s * 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

end Scalar0
end ZInQ.Metrization

/-! ## metrization2: `JacDetNondegenerate` from the local structure of morphisms out of a product

Step 1 (linear algebra): if every `jacDet Φ f` vanishes, some `v ≠ 0` is killed by
`d(germAlong Φ t)(0)` for every `t ∈ 𝔪_ξ`. Step 2: then by every regular function near `ξ`
(subtract the pull-back along `𝒢 → Spec 𝓞_L` of its restriction to the unit section). -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology
open PkgI3 (AbVar)

/-- Step 1 (pure linear algebra). If every `g × g` matrix whose rows are taken from a family
`F` of vectors of `ℂ^g` has determinant `0`, a nonzero vector is orthogonal (for the bilinear
pairing `Σ_j x_j y_j`) to every member of the family. -/
theorem exists_null_of_det_eq_zero {J : Type*} {g : ℕ} (F : J → (Fin g → ℂ))
    (h : ∀ f : Fin g → J, (Matrix.of fun i j => F (f i) j).det = 0) :
    ∃ v : Fin g → ℂ, v ≠ 0 ∧ ∀ i, ∑ j, F i j * v j = 0 := by
  by_cases hW : Submodule.span ℂ (Set.range F) = ⊤
  · exfalso
    obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ F
    rw [hW] at hspan
    have : Finite κ := hli.finite
    haveI := Fintype.ofFinite κ
    have hcard : Fintype.card κ = g := by
      rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hspan, finrank_top,
        Module.finrank_fin_fun]
    let eqv : Fin g ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent ℂ ((F ∘ a) ∘ eqv) := hli.comp eqv eqv.injective
    have hU : IsUnit (Matrix.of fun i j => F (a (eqv i)) j) :=
      Matrix.linearIndependent_row_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero (h (a ∘ eqv))
  · obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
    refine ⟨fun j => φ (fun k => if j = k then 1 else 0), ?_, ?_⟩
    · intro hv
      apply hφ0
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp only [LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrFun hv j
      simp only [Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro i
      have h1 := hle (Submodule.subset_span ⟨i, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [smul_eq_mul] using h1

section Eval

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- The value at the complex point `Spec ℂ → Spec 𝓞_L` (via `τ`) of a function on an open of
`Spec 𝓞_L` (`0` off the open). -/
noncomputable def baseVal (τ : L →+* ℂ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) : ℂ := by
  classical
  exact if h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x)
  else 0

/-- A function pulled back from `Spec 𝓞_L` takes the same value at every complex point. -/
theorem evalAt_pullback_base {τ : L →+* ℂ} (p : 𝒢.Pts τ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) :
    𝒢.evalAt p (𝒢.G.hom ⁻¹ᵁ O) (𝒢.G.hom.app O x) = baseVal τ O x := by
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have hpre : p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O := by
    rw [← hw]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (f : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (𝓞 L)))
        (hf : f = (GroupModel.ptC (L := L) τ).hom) (e : ⊤ ≤ f ⁻¹ᵁ O),
        f.appLE O ⊤ e x = (GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x := by
      rintro f rfl e; rfl
    have h'' : ⊤ ≤ (p.left ≫ 𝒢.G.hom) ⁻¹ᵁ O := h'
    refine Eq.trans ?_ (key _ hw h'')
    have hc := Scheme.Hom.comp_appLE p.left 𝒢.G.hom O ⊤ h''
    exact congrArg (fun φ => (ConcreteCategory.hom φ) x) hc.symm
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- A complex point factoring as `Spec ℂ → Spec 𝓞_L → 𝒢` evaluates through the section. -/
theorem evalAt_of_left_eq {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    (f : Spec (CommRingCat.of (𝓞 L)) ⟶ 𝒢.G.left) (hp : p.left = (GroupModel.ptC τ).hom ≫ f)
    (V : 𝒢.G.left.Opens) (b : Γ(𝒢.G.left, V)) :
    𝒢.evalAt p V b = baseVal τ (f ⁻¹ᵁ V) (f.app V b) := by
  have hpre : p.left ⁻¹ᵁ V = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [hp]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ V := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (q : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left)
        (hq : q = (GroupModel.ptC (L := L) τ).hom ≫ f) (e : ⊤ ≤ q ⁻¹ᵁ V),
        q.appLE V ⊤ e b = ((GroupModel.ptC (L := L) τ).hom ≫ f).appLE V ⊤ h b := by
      rintro q rfl e; rfl
    refine (key _ hp h').trans ?_
    have hc := Scheme.Hom.comp_appLE (GroupModel.ptC (L := L) τ).hom f V ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) b) hc
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ V := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- `(1 : 𝒢(ℂ)_τ)` is `Spec ℂ → Spec 𝓞_L → 𝒢` through the unit section. -/
theorem one_left_eq (τ : L →+* ℂ) :
    (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left = _
  rw [Over.comp_left, hw]
  rfl

/-- The unit section is a section of the structure map. -/
theorem unitSection_comp_hom : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  show (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left ≫ 𝒢.G.hom = 𝟙 _
  rw [Over.w]
  rfl

theorem one_mem_dom (τ : L →+* ℂ) (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W) :
    ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ W
  erw [one_left_apply]
  exact m

theorem evalAt_sub {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s - s') = 𝒢.evalAt p U s - 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_sub]
    exact map_sub (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem evalAt_one_sec {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (h : ⊤ ≤ p.left ⁻¹ᵁ U) :
    𝒢.evalAt p U 1 = 1 := by
  unfold GroupModel.evalAt
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

/-- A section vanishing at the identity complex point has its germ at `ξ` in `𝔪_ξ`. -/
theorem germ_mem_of_evalAt_one {τ : L →+* ℂ} (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W)
    (s : Γ(𝒢.G.left, W)) (h : 𝒢.evalAt (1 : 𝒢.Pts τ) W s = 0) :
    𝒢.G.left.presheaf.germ W 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  by_contra hn
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal.mp hn).exists_right_inv
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep u
  have mm : 𝒢.genericUnit ∈ W ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hg : 𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm
      (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
        𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') =
      𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm 1 := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hu, map_one]
  obtain ⟨W'', m'', i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit mm mm _ _ hg
  have hd := one_mem_dom 𝒢 τ W'' m''
  have e1 := congrArg (𝒢.evalAt (1 : 𝒢.Pts τ) W'') hW
  rw [map_mul, map_one, evalAt_mul, evalAt_one_sec 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
    evalAt_res 𝒢 _ _ hd] at e1
  rw [evalAt_res 𝒢 (1 : 𝒢.Pts τ) (homOfLE inf_le_left)
    ((one_mem_dom 𝒢 τ _ mm)) s, h, zero_mul] at e1
  exact zero_ne_one e1

end Eval

end ZInQ.Metrization2
/-! ## metrization2: the glue Prop, step 2 (all regular functions) and step 3 (translation) -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology
open PkgI3 (AbVar)

/-- **Glue (local structure of a morphism out of a fibre product, at complex points).** For group
models `𝒢₁`, `𝒢₂`, `ℋ` over `𝓞_L`, a morphism `m : 𝒢₁ ×_{𝓞_L} 𝒢₂ → ℋ` of `𝓞_L`-schemes, an open
`U ⊆ ℋ`, `s ∈ Γ(U, 𝒪_ℋ)` and complex points `p₁`, `p₂` with `m(p₁, p₂) ∈ U(ℂ)`: there are opens
`Vᵢ ∋ pᵢ` and regular functions `a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that
`H = Σ c_k(·) d_k(·)` is nonzero at `(p₁, p₂)` and, wherever `H(p₁', p₂') ≠ 0` on
`V₁(ℂ) × V₂(ℂ)`, `m(p₁', p₂') ∈ U(ℂ)` and `s(m(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`.
Why true (STANDARD; pure scheme theory, no analysis): take affine opens `Vᵢ = Spec Rᵢ ∋ pᵢ`;
`V₁ ×_{𝓞_L} V₂ = Spec (R₁ ⊗_{𝓞_L} R₂)` is an open of the product (Mathlib: `pullbackSpecIso`);
choose a basic open `D(h) ∋ (p₁, p₂)` inside `m⁻¹(U) ∩ (V₁ × V₂)`; on it `m^*s = a / h^N`; write
`h^N = Σ c_k ⊗ d_k`, `a = Σ a_k ⊗ b_k`; a complex point `(p₁', p₂')` of `V₁ × V₂` is the ring map
`r₁ ⊗ r₂ ↦ r₁(p₁') r₂(p₂')`, and it lies in `D(h)` iff `h^N(p₁', p₂') ≠ 0`.
Special cases: `m = e.inv` for `e : 𝒢P ≅ 𝒢₁ × 𝒢₂` is metrization's `ProductLocalStructure`
(`productLocalStructure_of`); `m = μ` (the group law) gives `JacDetNondegenerate`
(`jacDetNondegenerate_of`). -/
def ProductMapLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (ℋ : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (m : 𝒢₁.G ⊗ 𝒢₂.G ⟶ ℋ.G) (τ : L →+* ℂ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ m).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ m).left ⁻¹ᵁ U ∧
        ℋ.evalAt (lift p₁' p₂' ≫ m) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

/-- `ProductMapLocalStructure` contains metrization's `ProductLocalStructure` (`m = e.inv`). -/
theorem productLocalStructure_of (h : ProductMapLocalStructure) :
    ZInQ.Metrization.ProductLocalStructure := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e τ U s p₁ p₂ hp
  exact h K A B C L 𝒢P 𝒢₁ 𝒢₂ e.inv τ U s p₁ p₂ hp

section Steps

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem hom_genericUnit : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  show 𝒢.G.hom (𝒢.unitSection (genericPt L)) = genericPt L
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

/-- Step 2. If `d(germAlong Φ t)(0)` kills `v` for every `t ∈ 𝔪_ξ`, then the differential at `0`
of `z ↦ b(Φ z)` kills `v` for every regular function `b` near `ξ`. -/
theorem fderiv_evalAt_apply_eq_zero {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0)
    (V : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)) :
    fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0 := by
  set O := 𝒢.unitSection ⁻¹ᵁ V with hO
  set c : Γ(𝒢.G.left, 𝒢.G.hom ⁻¹ᵁ O) := 𝒢.G.hom.app O (𝒢.unitSection.app V b) with hc
  have mO : 𝒢.genericUnit ∈ 𝒢.G.hom ⁻¹ᵁ O := by
    show 𝒢.unitSection (𝒢.G.hom 𝒢.genericUnit) ∈ V
    rw [hom_genericUnit]
    exact m
  set W := V ⊓ 𝒢.G.hom ⁻¹ᵁ O with hW
  have mW : 𝒢.genericUnit ∈ W := TopologicalSpace.Opens.mem_inf.mpr ⟨m, mO⟩
  set b' : Γ(𝒢.G.left, W) := 𝒢.G.left.presheaf.map (homOfLE inf_le_left).op b -
    𝒢.G.left.presheaf.map (homOfLE inf_le_right).op c with hb'
  have h1 : 𝒢.evalAt (1 : 𝒢.Pts τ) W b' = 0 := by
    have hd := one_mem_dom 𝒢 τ W mW
    rw [hb', evalAt_sub, evalAt_res 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
      evalAt_of_left_eq 𝒢 1 𝒢.unitSection (one_left_eq 𝒢 τ) V b, hc, evalAt_pullback_base,
      sub_self]
  have hgerm := germ_mem_of_evalAt_one 𝒢 W mW b' h1
  have hv' := hv ⟨_, hgerm⟩
  have heq : 𝒢.germAlong Φ (𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW b') =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) V b - baseVal τ O (𝒢.unitSection.app V b) := by
    filter_upwards [germAlong_eventuallyEq 𝒢 hΦ W mW b',
      (hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz1 hz
    rw [hz1, hb', evalAt_sub, evalAt_res 𝒢 _ _ hz, evalAt_res 𝒢 _ _ hz, hc,
      evalAt_pullback_base]
  simp only at hv'
  rw [heq.fderiv_eq, fderiv_sub_const] at hv'
  exact hv'

/-- Step 3 (translation). If every regular function near `ξ` has `d(b ∘ Φ)(0) v = 0`, then for
every regular function `s` on `U` and every `w ∈ Φ⁻¹(U(ℂ))`, `t ↦ s(Φ(w + t v))` has derivative
`0` at `t = 0`: near `0`, `s(Φ w · Φ z) = N(z)/D(z)` with `N`, `D` combinations of regular
functions near `ξ` along `Φ` (`ProductMapLocalStructure` for the group law `μ`). -/
theorem hasDerivAt_line_zero (hML : ProductMapLocalStructure) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv2 : ∀ (V : 𝒢.G.left.Opens) (_ : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)),
      fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0)
    (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) (w : Fin g → ℂ) (hw : w ∈ 𝒢.dom Φ U) :
    HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (w + t • v)) U s) 0 0 := by
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmul : ∀ z, lift (Φ w) (Φ z) ≫ μ[𝒢.G] = Φ (w + z) := fun z => (hΦ.1 w z).symm
  have hU' : ⊤ ≤ (lift (Φ w) (Φ 0) ≫ μ[𝒢.G]).left ⁻¹ᵁ U := by
    rw [hmul, add_zero]; exact hw
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hML K A A A L 𝒢 𝒢 𝒢 μ[𝒢.G] τ U s (Φ w) (Φ 0) hU'
  have mV₂ : 𝒢.genericUnit ∈ V₂ := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
    have hx := hV₂ (show x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
    change (Φ 0).left x ∈ V₂ at hx
    rw [h0] at hx
    erw [one_left_apply] at hx
    exact hx
  set Nf : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (a k) * 𝒢.evalAt (Φ z) V₂ (b k) with hNf
  set Df : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (c k) * 𝒢.evalAt (Φ z) V₂ (d k) with hDf
  have hdom2 : IsOpen (𝒢.dom Φ V₂) := hΦ.2.2.2.1 V₂
  have h0dom : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V₂ := hV₂
  have hDcont : ContinuousOn Df (𝒢.dom Φ V₂) := by
    have : DifferentiableOn ℂ Df (𝒢.dom Φ V₂) := by
      simp only [hDf]
      exact DifferentiableOn.fun_sum fun k _ =>
        (hΦ.2.2.2.2 V₂ (d k)).const_mul _
    exact this.continuousOn
  set O := 𝒢.dom Φ V₂ ∩ Df ⁻¹' {0}ᶜ with hO
  have hOopen : IsOpen O := hDcont.isOpen_inter_preimage hdom2 isOpen_compl_singleton
  have hD0 : Df 0 ≠ 0 := hne
  have h0O : (0 : Fin g → ℂ) ∈ O := ⟨h0dom, hD0⟩
  -- derivative along the line of each regular function near `ξ`
  have hline : ∀ (bb : Γ(𝒢.G.left, V₂)),
      HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) V₂ bb) 0 0 := by
    intro bb
    have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0 :=
      (hΦ.2.2.2.2 V₂ bb).differentiableAt (hdom2.mem_nhds h0dom)
    have hF : HasFDerivAt (fun z => 𝒢.evalAt (Φ z) V₂ bb)
        (fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0) ((0 : ℂ) • v) := by
      rw [zero_smul]; exact hd.hasFDerivAt
    have := hF.comp_hasDerivAt (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).smul_const v)
    simp only [one_smul, hv2 V₂ mV₂ bb] at this
    exact this
  have hN : HasDerivAt (fun t : ℂ => Nf (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (b k)).const_mul (𝒢.evalAt (Φ w) V₁ (a k))
    simpa [hNf] using this
  have hD : HasDerivAt (fun t : ℂ => Df (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (d k)).const_mul (𝒢.evalAt (Φ w) V₁ (c k))
    simpa [hDf] using this
  have hD0' : Df ((0 : ℂ) • v) ≠ 0 := by rw [zero_smul]; exact hD0
  have hq := hN.div hD hD0'
  simp only [zero_mul, mul_zero, sub_zero, zero_div] at hq
  refine hq.congr_of_eventuallyEq ?_
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ O :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hOopen.mem_nhds h0O)
  filter_upwards [hev] with t ht
  obtain ⟨-, heq⟩ := hall (Φ w) (Φ (t • v)) hV₁ ht.1 ht.2
  rw [hmul] at heq
  exact eq_div_of_mul_eq ht.2 heq

end Steps

end ZInQ.Metrization2
/-! ## metrization2: points are determined by their values on an affine open; the assembly -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology
open PkgI3 (AbVar)

section Final

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- Two complex points in `U(ℂ)`, `U` affine, with the same values on `Γ(U, 𝒪)` are equal. -/
theorem pts_eq_of_evalAt {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (hU : IsAffineOpen U)
    (p q : 𝒢.Pts τ) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) (hq : ⊤ ≤ q.left ⁻¹ᵁ U)
    (h : ∀ s : Γ(𝒢.G.left, U), 𝒢.evalAt p U s = 𝒢.evalAt q U s) : p = q := by
  have hTop : IsAffineOpen (⊤ : (Spec (CommRingCat.of ℂ)).Opens) :=
    isAffineOpen_top (Spec (CommRingCat.of ℂ))
  have happ : p.left.appLE U ⊤ hp = q.left.appLE U ⊤ hq := by
    ext s
    have hs := h s
    unfold GroupModel.evalAt at hs
    rw [dif_pos hp, dif_pos hq] at hs
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective hs
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec p.left hU hTop hp
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec q.left hU hTop hq
  have e3 : hTop.fromSpec ≫ p.left = hTop.fromSpec ≫ q.left :=
    e1.symm.trans ((congrArg (fun φ => Spec.map φ ≫ hU.fromSpec) happ).trans e2)
  have hiso : IsIso hTop.fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  apply Over.OverMorphism.ext
  exact (cancel_epi hTop.fromSpec).mp e3

end Final

/-- **`JacDetNondegenerate` from `ProductMapLocalStructure` (proved).** If every `jacDet Φ f`
vanished, some `v ≠ 0` would be killed by the differential at `0` of every regular function near
`ξ` along `Φ` (steps 1 and 2), hence, by translation, by the differential at every point
(step 3); so on an affine `U ∋ ξ` every regular function is constant along `t ↦ Φ(t v)` for small
`t`, so `Φ(t v) = Φ 0 = 1` (points of an affine scheme are determined by their values), so
`t v ∈ Λ` for all small `t`, contradicting the discreteness of `Λ`. Neither `A.dim = g` nor
`IsZLattice ℝ Λ` is used. -/
theorem jacDetNondegenerate_of (hML : ProductMapLocalStructure) :
    ZInQ.Metrization.JacDetNondegenerate := by
  intro K _ A L _ _ _ 𝒢 τ g _ Λ hdisc Φ _ hΦ
  by_contra hcon
  push_neg at hcon
  -- step 1
  obtain ⟨v, hv0, hv⟩ := exists_null_of_det_eq_zero
    (fun t : IsLocalRing.maximalIdeal 𝒢.genStalk => fun j =>
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1)) (fun f => hcon f)
  have hsingle : ∀ j : Fin g, (fun k => if j = k then (1 : ℂ) else 0) = Pi.single j 1 := by
    intro j; ext k; simp [Pi.single_apply, eq_comm]
  have hv1 : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0 := by
    intro t
    rw [pi_eq_sum_univ v, map_sum]
    simp only [hsingle, map_smul, smul_eq_mul]
    rw [← hv t]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- step 2
  have hv2 := fderiv_evalAt_apply_eq_zero 𝒢 hΦ v hv1
  -- an affine open around `ξ`
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hdomU : IsOpen (𝒢.dom Φ U) := hΦ.2.2.2.1 U
  have h0U : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := zero_mem_dom 𝒢 hΦ U mU
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hBopen : IsOpen {t : ℂ | t • v ∈ 𝒢.dom Φ U} := hdomU.preimage hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBopen 0 (by simp [h0U])
  -- steps 3-4: every regular function on `U` is constant along the line on the ball
  have hconst : ∀ t ∈ Metric.ball (0 : ℂ) r, Φ (t • v) = Φ 0 := by
    intro t ht
    have hderiv : ∀ (s : Γ(𝒢.G.left, U)), ∀ t₀ ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) U s) 0 t₀ := by
      intro s t₀ ht₀
      have h3 := hasDerivAt_line_zero 𝒢 hML hΦ v hv2 U s (t₀ • v) (hball ht₀)
      have h4 : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + (t - t₀) • v)) U s) 0 t₀ := by
        have h3' : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + t • v)) U s) 0 (t₀ - t₀) := by
          rw [sub_self]; exact h3
        exact h3'.comp_sub_const t₀ t₀
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [← add_smul, add_sub_cancel]
    apply pts_eq_of_evalAt 𝒢 U hU _ _ (hball ht) h0U
    intro s
    have := (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).differentiableAt.differentiableWithinAt)
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).deriv) ht (Metric.mem_ball_self hr)
    simpa using this
  -- step 5: discreteness of `Λ`
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • v ∈ Λ := fun t ht =>
    (hΦ.2.1 _).mp ((hconst t ht).trans h0)
  obtain ⟨u, hu, hpre⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set Λ))
  have hu0 : (0 : Fin g → ℂ) ∈ u := by
    have : (0 : Λ) ∈ ({0} : Set Λ) := rfl
    rw [← hpre] at this
    exact this
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ u :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hu.mem_nhds hu0)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ Metric.ball (0 : ℂ) r := Metric.ball_mem_nhds 0 hr
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • v ∈ u ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (hev1.and hev2)
  obtain ⟨t, ⟨htu, htb⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hin : (⟨t • v, hmem t htb⟩ : Λ) ∈ Subtype.val ⁻¹' u := htu
  rw [hpre] at hin
  have : t • v = 0 := congrArg Subtype.val hin
  rcases smul_eq_zero.mp this with h | h
  · exact ht0 h
  · exact hv0 h


end ZInQ.Metrization2

/-! ## metrization2: complex points of a group model are complex points of `A_L`

For a group model `𝒢` of `A_L` and `τ : L → ℂ`, `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`,
`q ↦ (Spec ℂ → A_L ≅ 𝒢_L → 𝒢)`, is a group isomorphism (inverse `χ`, built from the monoidal
functor `Over.pullback (Spec L → Spec 𝓞_L)`), and evaluation of `s ∈ Γ(U, 𝒪_𝒢)` at `θ q` is
evaluation of the pulled-back section at `q`. So a uniformization of `A_L(ℂ)_τ` in leaf-push2's
sense gives one of `𝒢(ℂ)_τ` in def-faltings' sense. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.LeafPush2
open PkgI3 (AbVar)
open scoped Obj

section Transport

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jO (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

theorem cpt_comp_jO (τ : L →+* ℂ) :
    (cptObj τ).hom ≫ jO L = (GroupModel.ptC (L := L) τ).hom := by
  show Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) =
    Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L)))
  rw [← Spec.map_comp]
  rfl

/-- The projection `𝒢_L → 𝒢`. -/
noncomputable def fstG : (genericFibre L 𝒢.G).left ⟶ 𝒢.G.left := pullback.fst 𝒢.G.hom (jO L)

theorem fstG_comp_hom : fstG 𝒢 ≫ 𝒢.G.hom = (genericFibre L 𝒢.G).hom ≫ jO L :=
  pullback.condition

/-- The morphism `A_L → 𝒢` (through `gen⁻¹ : A_L ≅ 𝒢_L` and the projection `𝒢_L → 𝒢`). -/
noncomputable def toModel : (A.baseChange L).X.left ⟶ 𝒢.G.left := 𝒢.gen.inv.left ≫ fstG 𝒢

theorem toModel_comp_hom :
    (toModel 𝒢) ≫ 𝒢.G.hom = (A.baseChange L).X.hom ≫ jO L := by
  unfold toModel
  rw [Category.assoc, fstG_comp_hom, ← Category.assoc, Over.w 𝒢.gen.inv]

/-- `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`. -/
noncomputable def theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : 𝒢.Pts τ :=
  Over.homMk (q.left ≫ (toModel 𝒢))
    ((Category.assoc _ _ _).trans ((congrArg (q.left ≫ ·) (toModel_comp_hom 𝒢)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jO L) (Over.w q)).trans
        (cpt_comp_jO τ)))))

theorem theta_left {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) :
    ((theta 𝒢) q).left = q.left ≫ (toModel 𝒢) := rfl

/-- The base change `(Spec ℂ)_L` of `ptC τ`. -/
noncomputable abbrev ptCL (τ : L →+* ℂ) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (jO L)).obj (GroupModel.ptC (L := L) τ)

/-- Its projection to `Spec ℂ` (`ptC τ`'s underlying scheme). -/
noncomputable def fstC (τ : L →+* ℂ) : (ptCL τ).left ⟶ (GroupModel.ptC (L := L) τ).left :=
  pullback.fst (GroupModel.ptC (L := L) τ).hom (jO L)

/-- The section `Spec ℂ → (Spec ℂ)_L` of the base change of `ptC τ`. -/
noncomputable def secC (τ : L →+* ℂ) : cptObj τ ⟶ ptCL τ :=
  Over.homMk (pullback.lift (𝟙 (Spec (CommRingCat.of ℂ))) (cptObj τ).hom
    ((Category.id_comp _).trans (cpt_comp_jO τ).symm))
    (pullback.lift_snd _ _ _)

theorem secC_fstC (τ : L →+* ℂ) : (secC τ).left ≫ fstC τ = 𝟙 _ :=
  pullback.lift_fst _ _ _

theorem secC_snd (τ : L →+* ℂ) : (secC τ).left ≫ (ptCL τ).hom = (cptObj τ).hom :=
  pullback.lift_snd _ _ _

/-- The base change of a complex point `p` of `𝒢`, as a map to `𝒢_L`. -/
noncomputable def mapG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : ptCL τ ⟶ genericFibre L 𝒢.G :=
  (Over.pullback (jO L)).map p

theorem mapG_fstG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (mapG 𝒢 p).left ≫ fstG 𝒢 = fstC τ ≫ p.left :=
  pullback.lift_fst _ _ _

theorem mapG_snd {τ : L →+* ℂ} (p : 𝒢.Pts τ) :
    (mapG 𝒢 p).left ≫ (genericFibre L 𝒢.G).hom = (ptCL τ).hom :=
  pullback.lift_snd _ _ _

/-- `χ : 𝒢(ℂ)_τ → A_L(ℂ)_τ`. -/
noncomputable def chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : CPts (A.baseChange L) τ :=
  secC τ ≫ mapG 𝒢 p ≫ 𝒢.gen.hom

theorem chi_mul {τ : L →+* ℂ} (p₁ p₂ : 𝒢.Pts τ) : (chi 𝒢) (p₁ * p₂) = (chi 𝒢) p₁ * (chi 𝒢) p₂ := by
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  haveI : IsMonHom 𝒢.gen.hom := 𝒢.gen_hom
  have hm : mapG 𝒢 (p₁ * p₂) = mapG 𝒢 p₁ * mapG 𝒢 p₂ := Functor.map_mul _ _ _
  unfold chi
  rw [hm, MonObj.mul_comp, MonObj.comp_mul]

theorem gen_hom_inv_left : 𝒢.gen.hom.left ≫ 𝒢.gen.inv.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]

theorem gen_inv_hom_left : 𝒢.gen.inv.left ≫ 𝒢.gen.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]

theorem theta_chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (theta 𝒢) ((chi 𝒢) p) = p := by
  apply Over.OverMorphism.ext
  rw [theta_left]
  unfold chi toModel
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc 𝒢.gen.hom.left, gen_hom_inv_left, Category.id_comp, mapG_fstG]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p.left) (secC_fstC τ)).trans
    (Category.id_comp _))

theorem chi_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : (chi 𝒢) ((theta 𝒢) q) = q := by
  apply Over.OverMorphism.ext
  have key : (secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left = q.left ≫ 𝒢.gen.inv.left := by
    apply pullback.hom_ext
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ fstG 𝒢 =
        (q.left ≫ 𝒢.gen.inv.left) ≫ fstG 𝒢
      rw [Category.assoc, mapG_fstG]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((theta 𝒢) q).left)
        (secC_fstC τ)).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm))
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ (genericFibre L 𝒢.G).hom =
        (q.left ≫ 𝒢.gen.inv.left) ≫ (genericFibre L 𝒢.G).hom
      rw [Category.assoc, mapG_snd, secC_snd, Category.assoc, Over.w 𝒢.gen.inv, Over.w q]
  unfold chi
  simp only [Over.comp_left]
  rw [← Category.assoc, key, Category.assoc, gen_inv_hom_left, Category.comp_id]

theorem theta_mul {τ : L →+* ℂ} (q₁ q₂ : CPts (A.baseChange L) τ) :
    (theta 𝒢) (q₁ * q₂) = (theta 𝒢) q₁ * (theta 𝒢) q₂ := by
  conv_lhs => rw [← (chi_theta 𝒢) q₁, ← (chi_theta 𝒢) q₂, ← chi_mul, theta_chi]

theorem theta_injective {τ : L →+* ℂ} : Function.Injective (theta 𝒢 (τ := τ)) := fun a b h => by
  rw [← (chi_theta 𝒢) a, ← (chi_theta 𝒢) b, h]

theorem theta_surjective {τ : L →+* ℂ} : Function.Surjective (theta 𝒢 (τ := τ)) :=
  fun p => ⟨(chi 𝒢) p, (theta_chi 𝒢) p⟩

theorem theta_one {τ : L →+* ℂ} : (theta 𝒢) (1 : CPts (A.baseChange L) τ) = 1 := by
  have h := theta_mul 𝒢 (τ := τ) 1 1
  rw [_root_.mul_one] at h
  exact mul_left_cancel (a := (theta 𝒢) 1) (by rw [_root_.mul_one]; exact h.symm)

theorem evalAt_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt ((theta 𝒢) q) U s = cEvalAt q ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s) := by
  unfold GroupModel.evalAt cEvalAt
  by_cases h : ⊤ ≤ q.left ⁻¹ᵁ ((toModel 𝒢) ⁻¹ᵁ U)
  · have h' : ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

end Transport

/-- **`AnalyticUniformizationOfDim` follows from leaf-push2's leaf `UniformizationExists`
(T35), proved.** Apply T35 to `A_L` over `L` at `σ = τ` (`dim A_L = dim A` by g0-dim's
`G0Dim.dim_baseChange`) and transport along `θ`. -/
theorem analyticUniformizationOfDim_of_uniformizationExists
    (hT : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.AnalyticUniformizationOfDim := by
  intro K _ A L _ _ _ 𝒢 τ g hg
  have hgL : (A.baseChange L).dim = (g : WithBot ℕ∞) := by
    rw [← hg]
    exact G0Dim.dim_baseChange L A.X.left A.X.hom
  obtain ⟨Λ, Φ₀, hd, hZ, hmul, hker, hsurj, hopen, hdiff⟩ := hT L (A.baseChange L) τ g hgL
  refine ⟨Λ, fun z => (theta 𝒢) (Φ₀ z), hd, hZ, fun z w => ?_, fun z => ?_, ?_, fun U => ?_,
    fun U s => ?_⟩
  · simp only [hmul, theta_mul]
  · rw [← hker z, ← theta_one 𝒢 (τ := τ)]
    exact (theta_injective 𝒢).eq_iff
  · exact (theta_surjective 𝒢).comp hsurj
  · exact hopen ((toModel 𝒢) ⁻¹ᵁ U)
  · have := hdiff ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s)
    refine this.congr fun z _ => ?_
    exact (evalAt_theta 𝒢) (Φ₀ z) U s

end ZInQ.Metrization2

/-! ## metrization2: toward `ProductMapLocalStructure` — evaluation at complex points of schemes,
and sums of products in a pushout of commutative rings -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

/-- The value at a complex point `q : Spec ℂ → X` of `s ∈ Γ(X, U)` (`0` if `q ∉ U(ℂ)`). Same
formula as def-faltings' `GroupModel.evalAt` (which is `ev p.left`). -/
noncomputable def ev {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (s : Γ(X, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ q ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ h s)
    else 0

section Ev

variable {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X)

theorem ev_comp (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    ev (q ≫ f) U s = ev q (f ⁻¹ᵁ U) (f.app U s) := by
  unfold ev
  by_cases h : ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem ev_res {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ q ⁻¹ᵁ V) (s : Γ(X, U)) :
    ev q V (X.presheaf.map i.op s) = ev q U s := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := hV.trans ((TopologicalSpace.Opens.map q.base).map i).le
  unfold ev
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE q hV i.op]
  rfl

theorem ev_add (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s + s') = ev q U s + ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_mul (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s * s') = ev q U s * ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_zero (U : X.Opens) : ev q U 0 = 0 := by
  unfold ev
  split_ifs with h
  · rw [map_zero]
    exact map_zero (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
  · rfl

theorem ev_one (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) : ev q U 1 = 1 := by
  unfold ev
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

theorem ev_pow (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) :
    ev q U (s ^ n) = ev q U s ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ev_one q U h]
  | succ n ih => rw [pow_succ, pow_succ, ev_mul, ih]

theorem ev_sum (U : X.Opens) {n : ℕ} (s : Fin n → Γ(X, U)) :
    ev q U (∑ k, s k) = ∑ k, ev q U (s k) := by
  induction n with
  | zero => simp [ev_zero]
  | succ n ih => rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ev_add, ih]

/-- A complex point in `X.basicOpen s` gives `s` a nonzero value. -/
theorem ev_ne_zero_of_mem {U : X.Opens} (s : Γ(X, U)) (h : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s) :
    ev q U s ≠ 0 := by
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s) :=
    X.toRingedSpace.isUnit_res_basicOpen s
  rw [← ev_res q (homOfLE (X.basicOpen_le s)) h]
  obtain ⟨u, hu'⟩ := hu
  intro h0
  have h1 := congrArg (ev q (X.basicOpen s)) u.mul_inv
  rw [ev_mul, ev_one q _ h, hu', h0, zero_mul] at h1
  exact zero_ne_one h1

/-- A complex point of `U` at which `s` has a nonzero value lies in `X.basicOpen s`. -/
theorem mem_basicOpen_of_ev_ne_zero {U : X.Opens} (s : Γ(X, U)) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (h : ev q U s ≠ 0) : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s := by
  unfold ev at h
  rw [dif_pos hU] at h
  have hu : IsUnit (q.appLE U ⊤ hU s) := by
    have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ hU s)) :=
      isUnit_iff_ne_zero.mpr h
    have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using this
  have hb := (Spec (CommRingCat.of ℂ)).basicOpen_of_isUnit hu
  rw [Scheme.Hom.preimage_basicOpen]
  have he : q.appLE U ⊤ hU s = (Spec (CommRingCat.of ℂ)).presheaf.map (homOfLE hU).op
      (q.app U s) := rfl
  rw [he, Scheme.basicOpen_res] at hb
  rw [← hb]
  exact inf_le_right

end Ev

/-- Finite sums of products `inl(α) · inr(β)`. -/
def IsSumProd {B C P : Type} [CommRing B] [CommRing C] [CommRing P] (inl : B →+* P)
    (inr : C →+* P) (r : P) : Prop :=
  ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k)

theorem isSumProd_add {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r + r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n + m, Fin.append α α', Fin.append β β', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isSumProd_mul {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r * r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n * m, fun k => α (finProdFinEquiv.symm k).1 * α' (finProdFinEquiv.symm k).2,
    fun k => β (finProdFinEquiv.symm k).1 * β' (finProdFinEquiv.symm k).2, ?_⟩
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  show _ = ∑ k, (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))
    (finProdFinEquiv.symm k)
  refine Eq.trans ?_ (Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))).symm
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_mul]
  ring

theorem isSumProd_neg {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r : P} (h : IsSumProd inl inr r) : IsSumProd inl inr (-r) := by
  obtain ⟨n, α, β, rfl⟩ := h
  exact ⟨n, fun k => -α k, β, by simp [Finset.sum_neg_distrib]⟩

/-- In a pushout square of commutative rings, every element of the pushout is a finite sum of
products `inl(α) · inr(β)`. -/
theorem exists_sum_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (r : P) :
    ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k) := by
  let T : Subring P := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom)
  have hT : ∀ x ∈ T, IsSumProd inl.hom inr.hom x := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · exact ⟨1, fun _ => b, fun _ => 1, by simp⟩
      · exact ⟨1, fun _ => 1, fun _ => c, by simp⟩
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
    | add x y _ _ hx hy => exact isSumProd_add hx hy
    | neg x _ hx => exact isSumProd_neg hx
    | mul x y _ _ hx hy => exact isSumProd_mul hx hy
  let jl : B ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inl.hom.codRestrict T fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let jr : C ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inr.hom.codRestrict T fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ jl = g ≫ jr := by
    ext a
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) h.w
  let ι : CommRingCat.of T ⟶ P := CommRingCat.ofHom T.subtype
  have hid : h.desc jl jr w ≫ ι = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc, Category.comp_id]; rfl
    · rw [h.inr_desc_assoc, Category.comp_id]; rfl
  have hr : r ∈ T := by
    have : ι (h.desc jl jr w r) = r := by rw [← ConcreteCategory.comp_apply, hid]; rfl
    rw [← this]
    exact ((h.desc jl jr w) r).2
  exact hT r hr

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, proved

The local structure of a fibre product of schemes over an affine base at complex points
(`core_local`): affine opens `Vᵢ`, the affine scheme `Q = V₁ ×_S V₂` (an open of the product
through `j`), whose ring is the pushout `Γ(V₁) ⊗_{Γ(S)} Γ(V₂)` (`isPushout_appTop_of_isPullback`),
a basic open `D(h) ⊆ j⁻¹W` of `Q` and a fraction `t = a/h^N` on it. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

theorem specC_eq (z w : Spec (CommRingCat.of ℂ)) : z = w := by
  have hz : z.asIdeal = ⊥ := by
    haveI := z.isPrime; exact Ideal.eq_bot_of_prime _
  have hw : w.asIdeal = ⊥ := by
    haveI := w.isPrime; exact Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext (hz.trans hw.symm)

theorem top_le_of_mem {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (pt : Spec (CommRingCat.of ℂ)) (h : q pt ∈ U) : ⊤ ≤ q ⁻¹ᵁ U := by
  intro z _
  rw [specC_eq z pt]
  exact h

/-- The section of `X` on `U` corresponding to a global section of `U.toScheme`. -/
noncomputable def secOf {X : Scheme.{0}} (U : X.Opens) (α : Γ(U.toScheme, ⊤)) : Γ(X, U) :=
  (inv (U.ι.appLE U ⊤ U.ι_preimage_self.ge)) α

theorem ev_secOf {X : Scheme.{0}} (U : X.Opens) (y : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (α : Γ(U.toScheme, ⊤)) : ev (y ≫ U.ι) U (secOf U α) = ev y ⊤ α := by
  have h1 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by
    intro z _
    show U.ι (y z) ∈ U
    exact (y z).2
  have h2 : ⊤ ≤ y ⁻¹ᵁ (⊤ : U.toScheme.Opens) := fun _ _ => trivial
  unfold ev
  rw [dif_pos h1, dif_pos h2]
  congr 1
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ U.ι_preimage_self.ge h2]
  unfold secOf
  rw [← ConcreteCategory.comp_apply, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem ev_comp_top {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : ev (q ≫ f) ⊤ s = ev q ⊤ (f.appTop s) :=
  ev_comp q f ⊤ s

section Core

variable {S X₁ X₂ : Scheme.{0}} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)

/-- **The local structure of a fibre product over an affine base, at complex points.** -/
theorem core_local [IsAffine S] (W : (pullback f₁ f₂).Opens) (t : Γ(pullback f₁ f₂, W))
    (x₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (x₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
    (hx12 : x₁ ≫ f₁ = x₂ ≫ f₂) (hx : ⊤ ≤ (pullback.lift x₁ x₂ hx12) ⁻¹ᵁ W) :
    ∃ (V₁ : X₁.Opens) (V₂ : X₂.Opens) (n : ℕ) (a c : Fin n → Γ(X₁, V₁))
      (b d : Fin n → Γ(X₂, V₂)),
      ⊤ ≤ x₁ ⁻¹ᵁ V₁ ∧ ⊤ ≤ x₂ ⁻¹ᵁ V₂ ∧
      (∑ k, ev x₁ V₁ (c k) * ev x₂ V₂ (d k)) ≠ 0 ∧
      ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
        (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
        (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) ≠ 0 →
        ⊤ ≤ (pullback.lift y₁ y₂ hy) ⁻¹ᵁ W ∧
        ev (pullback.lift y₁ y₂ hy) W t * (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) =
          ∑ k, ev y₁ V₁ (a k) * ev y₂ V₂ (b k) := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
  have hpt : pt ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := trivial
  obtain ⟨V₁, hV₁, m₁, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₁ pt ∈ (⊤ : X₁.Opens) from trivial)
  obtain ⟨V₂, hV₂, m₂, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₂ pt ∈ (⊤ : X₂.Opens) from trivial)
  haveI : IsAffine V₁.toScheme := hV₁
  haveI : IsAffine V₂.toScheme := hV₂
  set g₁ := V₁.ι ≫ f₁ with hg₁
  set g₂ := V₂.ι ≫ f₂ with hg₂
  let j : pullback g₁ g₂ ⟶ pullback f₁ f₂ :=
    pullback.map g₁ g₂ f₁ f₂ V₁.ι V₂.ι (𝟙 S) (by simp [hg₁]) (by simp [hg₂])
  have hj1 : j ≫ pullback.fst f₁ f₂ = pullback.fst g₁ g₂ ≫ V₁.ι := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd f₁ f₂ = pullback.snd g₁ g₂ ≫ V₂.ι := pullback.lift_snd _ _ _
  -- complex points of `V₁ × V₂` lift to `Q`
  have lift_pt : ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
      (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
      ∃ yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂, yQ ≫ j = pullback.lift y₁ y₂ hy ∧
        yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι = y₁ ∧ yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι = y₂ := by
    intro y₁ y₂ hy h1 h2
    have r1 : Set.range y₁ ⊆ Set.range V₁.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h1 (show z ∈ ⊤ from trivial)
    have r2 : Set.range y₂ ⊆ Set.range V₂.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h2 (show z ∈ ⊤ from trivial)
    let z₁ := IsOpenImmersion.lift V₁.ι y₁ r1
    let z₂ := IsOpenImmersion.lift V₂.ι y₂ r2
    have hz₁ : z₁ ≫ V₁.ι = y₁ := IsOpenImmersion.lift_fac _ _ _
    have hz₂ : z₂ ≫ V₂.ι = y₂ := IsOpenImmersion.lift_fac _ _ _
    have hc : z₁ ≫ g₁ = z₂ ≫ g₂ := by
      rw [hg₁, hg₂, ← Category.assoc, hz₁, ← Category.assoc, hz₂, hy]
    refine ⟨pullback.lift z₁ z₂ hc, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hj1, pullback.lift_fst, pullback.lift_fst_assoc, hz₁]
      · rw [Category.assoc, hj2, pullback.lift_snd, pullback.lift_snd_assoc, hz₂]
    · rw [pullback.lift_fst_assoc, hz₁]
    · rw [pullback.lift_snd_assoc, hz₂]
  obtain ⟨xQ, hxQ, -, -⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
    (top_le_of_mem _ _ pt m₂)
  have hxQW : xQ pt ∈ j ⁻¹ᵁ W := by
    have := hx hpt
    rw [← hxQ] at this
    exact this
  obtain ⟨h, hhW, hhx⟩ := (isAffineOpen_top (pullback g₁ g₂)).exists_basicOpen_le
    (V := j ⁻¹ᵁ W) ⟨xQ pt, hxQW⟩ trivial
  -- the fraction
  set tQ : Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) :=
    (pullback g₁ g₂).presheaf.map (homOfLE hhW).op (j.app W t) with htQ
  obtain ⟨⟨a0, ⟨_, N, rfl⟩⟩, heq⟩ := IsLocalization.surj (Submonoid.powers h) tQ
  have hal : ∀ r : Γ(pullback g₁ g₂, ⊤),
      algebraMap Γ(pullback g₁ g₂, ⊤) Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) r =
        (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op r :=
    fun _ => rfl
  have heq' : tQ * (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op
      (h ^ (N + 1)) = (pullback g₁ g₂).presheaf.map
        (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op (a0 * h) := by
    simp only at heq
    rw [← hal, ← hal, pow_succ, map_mul, map_mul, ← mul_assoc, heq]
  -- sums of products
  have hpo := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g₁ g₂)
  obtain ⟨n₁, α, β, hα⟩ := exists_sum_of_isPushout hpo (a0 * h)
  obtain ⟨n₂, γ, δ, hγ⟩ := exists_sum_of_isPushout hpo (h ^ (N + 1))
  -- evaluation of a sum of products at a lifted point
  have key : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂) {m : ℕ}
      (u : Fin m → Γ(V₁.toScheme, ⊤)) (v : Fin m → Γ(V₂.toScheme, ⊤)),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (secOf V₁ (u k)) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (secOf V₂ (v k))) =
      ev yQ ⊤ (∑ k, (pullback.fst g₁ g₂).appTop (u k) * (pullback.snd g₁ g₂).appTop (v k)) := by
    intro yQ m u v
    rw [ev_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev_mul, ← Category.assoc, ev_secOf, ← Category.assoc, ev_secOf, ev_comp_top,
      ev_comp_top]
  let a : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append (fun k => secOf V₁ (α k)) 0
  let b : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append (fun k => secOf V₂ (β k)) 0
  let c : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append 0 (fun k => secOf V₁ (γ k))
  let d : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append 0 (fun k => secOf V₂ (δ k))
  have hA : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (a k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (b k)) = ev yQ ⊤ (a0 * h) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [a, b, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [key, hα]
  have hH : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (c k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (d k)) = ev yQ ⊤ h ^ (N + 1) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [c, d, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, zero_mul,
      Finset.sum_const_zero, zero_add]
    rw [key, ← hγ, ev_pow yQ ⊤ (fun _ _ => trivial)]
  refine ⟨V₁, V₂, n₁ + n₂, a, c, b, d, top_le_of_mem _ _ pt m₁, top_le_of_mem _ _ pt m₂, ?_, ?_⟩
  · obtain ⟨xQ', hxQ', e1, e2⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
      (top_le_of_mem _ _ pt m₂)
    have hxQ'h : ⊤ ≤ xQ' ⁻¹ᵁ (pullback g₁ g₂).basicOpen h := by
      have hjinj : xQ' = xQ := by
        apply pullback.hom_ext
        · apply (cancel_mono V₁.ι).mp
          rw [Category.assoc, Category.assoc, e1, ← hj1, ← Category.assoc, hxQ,
            pullback.lift_fst]
        · apply (cancel_mono V₂.ι).mp
          rw [Category.assoc, Category.assoc, e2, ← hj2, ← Category.assoc, hxQ,
            pullback.lift_snd]
      rw [hjinj]
      exact top_le_of_mem _ _ pt hhx
    rw [← e1, ← e2, hH]
    exact pow_ne_zero _ (ev_ne_zero_of_mem xQ' h hxQ'h)
  · intro y₁ y₂ hy h1 h2 hne
    obtain ⟨yQ, hyQ, e1, e2⟩ := lift_pt y₁ y₂ hy h1 h2
    subst e1 e2
    rw [hH] at hne ⊢
    rw [hA]
    have hev : ev yQ ⊤ h ≠ 0 := fun h0 => hne (by rw [h0, zero_pow (Nat.succ_ne_zero N)])
    have hmem : ⊤ ≤ yQ ⁻¹ᵁ (pullback g₁ g₂).basicOpen h :=
      mem_basicOpen_of_ev_ne_zero yQ h (fun _ _ => trivial) hev
    have hW : ⊤ ≤ yQ ⁻¹ᵁ (j ⁻¹ᵁ W) := hmem.trans ((TopologicalSpace.Opens.map yQ.base).map
      (homOfLE hhW)).le
    refine ⟨?_, ?_⟩
    · rw [← hyQ]; exact hW
    · rw [← hyQ, ev_comp, ← ev_res yQ (homOfLE hhW) hmem, ← htQ,
        ← ev_pow yQ ⊤ (fun _ _ => trivial),
        ← ev_res yQ (homOfLE ((pullback g₁ g₂).basicOpen_le h)) hmem (h ^ (N + 1)),
        ← ev_mul, heq', ev_res yQ _ hmem]

end Core

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, hence `JacDetNondegenerate` and
`ProductLocalStructure`, proved -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

/-- **`ProductMapLocalStructure`, proved** (from `core_local` with `S = Spec 𝓞_L`,
`W = m⁻¹(U)`, `t = m^*s`). -/
theorem productMapLocalStructure : ProductMapLocalStructure := by
  intro K _ A B C L _ _ _ ℋ 𝒢₁ 𝒢₂ m τ U s p₁ p₂ hp
  have hw : ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), p₁'.left ≫ 𝒢₁.G.hom = p₂'.left ≫ 𝒢₂.G.hom :=
    fun p₁' p₂' => (Over.w p₁').trans (Over.w p₂').symm
  obtain ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, hall⟩ :=
    core_local 𝒢₁.G.hom 𝒢₂.G.hom (m.left ⁻¹ᵁ U) (m.left.app U s) p₁.left p₂.left (hw p₁ p₂) hp
  refine ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, fun p₁' p₂' h1' h2' hne' => ?_⟩
  obtain ⟨hmem, heq⟩ := hall p₁'.left p₂'.left (hw p₁' p₂') h1' h2' hne'
  refine ⟨hmem, ?_⟩
  have hev : ℋ.evalAt (lift p₁' p₂' ≫ m) U s =
      ev (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) (m.left ⁻¹ᵁ U) (m.left.app U s) :=
    ev_comp (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) m.left U s
  rw [hev]
  exact heq

/-- **`JacDetNondegenerate`, proved** (no hypotheses). -/
theorem jacDetNondegenerate : ZInQ.Metrization.JacDetNondegenerate :=
  jacDetNondegenerate_of productMapLocalStructure

/-- **metrization's `ProductLocalStructure`, proved** (no hypotheses). -/
theorem productLocalStructure : ZInQ.Metrization.ProductLocalStructure :=
  productLocalStructure_of productMapLocalStructure

end ZInQ.Metrization2



/-! ## height-glue copy: metrization's `JacDetDescends` chain over the kernel's types, from
`scratch/unif-dims/Combined.lean` (task unif-dims) lines 1615-1752, 1907-1933, 1937-2190, verbatim except that the
Germ section and `evalAt_mul`, already in metrization2's `Kernel.lean` above, are omitted. -/
/-! ## metrization: `JacDetDescends` reduced to four calculus properties of `jacDet`

The algebra (universal property of `⋀^g`, extension of scalars `L ⊗_{𝓞_L} -` along `τ`) is
proved; what remains (`JacDetMultilinear`) are four statements about the derivative at `0` of
germs composed with `Φ`. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

/-- **Glue (calculus of `jacDet`).** For an analytic uniformization `Φ` of `𝒢(ℂ)_τ`, the map
`f ↦ jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` on `g`-tuples of germs in `𝔪_ξ`
(i) depends only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`;
(ii) is additive in each slot;
(iii) scales by `τ(a)` when slot `i` is multiplied by the image of `a ∈ 𝓞_L`;
(iv) vanishes when two slots are equal.
Why true: `Φ 0 = 1` lies over `ξ`, and `dom Φ U` is open, so the germ at `0` of `f ∘ Φ` does not
depend on the representative of `f`, and `(f + f') ∘ Φ = f ∘ Φ + f' ∘ Φ`, `(ff') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)`
and `a ∘ Φ = τ(a)` near `0` (evaluation at a complex point is a ring map); for `f, f' ∈ 𝔪_ξ`,
`f ∘ Φ` and `f' ∘ Φ` vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz), which gives (i); (ii)-(iv)
are row operations on the determinant. Elementary, unproved (needs the compatibility of
`evalAt` with restriction, sums, products and stalks in Mathlib's scheme API). -/
def JacDetMultilinear : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
      (x y : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (x + y)) =
        𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g), f i = f j → i ≠ j →
      𝒢.jacDet Φ f = 0)

/-- **`JacDetDescends` from `JacDetMultilinear` (proved).** -/
theorem jacDetDescends_of (h : JacDetMultilinear) : JacDetDescends := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨hcls, hadd, hsmul, halt⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  classical
  letI : Module (𝓞 L) ℂ := Module.compHom ℂ (τ.comp (algebraMap (𝓞 L) L))
  have hsm : ∀ (a : 𝓞 L) (z : ℂ), a • z = τ (algebraMap (𝓞 L) L a) * z := fun _ _ => rfl
  let lift : 𝒢.cotangent → IsLocalRing.maximalIdeal 𝒢.genStalk :=
    Function.surjInv (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective
  have hlift : ∀ v, 𝒢.dCls (lift v) = v := fun v =>
    Function.surjInv_eq (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective v
  have hdadd : ∀ x y, 𝒢.dCls (x + y) = 𝒢.dCls x + 𝒢.dCls y := fun x y =>
    map_add (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent x y
  have hdsmul : ∀ (a : 𝓞 L) x, 𝒢.dCls (𝒢.structMap a • x) = a • 𝒢.dCls x := fun a x =>
    map_smul (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent (𝒢.structMap a) x
  let ψ : 𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] ℂ :=
    { toFun := fun v => 𝒢.jacDet Φ (fun i => lift (v i))
      map_update_add' := by
        intro _ v i x y
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x + lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdadd]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        have e2 : 𝒢.jacDet Φ (fun j => lift (Function.update v i y j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
          𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) +
            𝒢.jacDet Φ (fun j => lift (Function.update v i y j))
        rw [e0, e1, e2]
        convert hadd (fun j => lift (v j)) i (lift x) (lift y)
      map_update_smul' := by
        intro _ v i a x
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (𝒢.structMap a • lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdsmul]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
          a • 𝒢.jacDet Φ (fun j => lift (Function.update v i x j))
        rw [e0, e1, hsm]
        convert hsmul (fun j => lift (v j)) i a (lift x)
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact halt (fun k => lift (v k)) i j (by simp only [hv]) hij }
  let Ψ : ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ := exteriorPower.alternatingMapLinearEquiv ψ
  let B : L →ₗ[𝓞 L] ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ :=
    LinearMap.mk₂ (𝓞 L) (fun x w => τ x * Ψ w)
      (fun x y w => by rw [map_add, add_mul])
      (fun a x w => by
        rw [hsm, Algebra.smul_def, map_mul, _root_.mul_assoc])
      (fun x w w' => by rw [map_add, mul_add])
      (fun a x w => by
        rw [map_smul, hsm, hsm, mul_left_comm])
  let T : 𝒢.hodgeSpace g →ₗ[𝓞 L] ℂ := TensorProduct.lift B
  have hT : ∀ x w, T (x ⊗ₜ[𝓞 L] w) = τ x * Ψ w := fun x w => rfl
  let c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := by
        intro y t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x w =>
          rw [TensorProduct.smul_tmul', hT, hT, smul_eq_mul, map_mul, _root_.mul_assoc]
          rfl
        | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, mul_add] }
  refine ⟨c, fun f => ?_⟩
  show T ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i))) = 𝒢.jacDet Φ f
  rw [hT, map_one, _root_.one_mul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact hcls _ _ fun i => hlift _

end ZInQ.Metrization

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

/-- **Glue (the two remaining clauses of `JacDetMultilinear`).** (i) `jacDet Φ f` depends only on
the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`; (iii) multiplying slot `i` by the image of `a ∈ 𝓞_L` multiplies
`jacDet` by `τ(a)`. Why true: by `germAlong_eventuallyEq` it suffices that for `f ∈ 𝔪_ξ²` the
function `evalAt (Φ z) U s` of a representative has derivative `0` at `0` (it is a sum of products
of functions vanishing at `0`, as evaluation at a complex point over `ξ` kills `𝔪_ξ`: the induced
map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ` is local), and that the image of `a` evaluates to `τ(a)` (the point
lies over `Spec 𝓞_L` through `τ`). Unproved: needs `evalAt` through `Scheme.Hom.stalkMap` and
`ΓSpecIso`. -/
def JacDetClassScalar : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x))

/-- **`JacDetMultilinear` from `JacDetClassScalar` (proved).** -/
theorem jacDetMultilinear_of (h : JacDetClassScalar) : JacDetMultilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨h1, h3⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  exact ⟨h1, fun f i x y => jacDet_update_add 𝒢 hΦ f i x y, h3,
    fun f i j hij hne => jacDet_eq_zero_of_eq 𝒢 Φ f i j hij hne⟩

end ZInQ.Metrization
/-! ## metrization: clause (iii) of `JacDetMultilinear` (scaling by `τ(a)`), proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

section Scalar

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- A function from `𝓞_L` evaluates to `τ(a)` at every complex point. -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (a : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      τ (algebraMap (𝓞 L) L a) := by
  have htop : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  unfold GroupModel.evalAt
  rw [dif_pos htop]
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have h1 : p.left.appLE ⊤ ⊤ htop = p.left.appTop := Scheme.Hom.appLE_eq_app p.left
  have h2 : (p.left.appTop) (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      ((p.left ≫ 𝒢.G.hom).appTop) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1, h2, hw]
  have h3 := congrArg (fun f => f ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  simp only [ConcreteCategory.comp_apply] at h3
  refine h3.trans ?_
  simp

/-- `germAlong Φ (structMap a * x) = τ(a) · germAlong Φ x` near `0`. -/
theorem germAlong_structMap_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (a : 𝓞 L)
    (x : 𝒢.genStalk) :
    𝒢.germAlong Φ (𝒢.structMap a * x) =ᶠ[𝓝 0]
      fun z => τ (algebraMap (𝓞 L) L a) * 𝒢.germAlong Φ x z := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  set σa : Γ(𝒢.G.left, ⊤) :=
    𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) with hσa
  have hprod : 𝒢.structMap a * 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ U 𝒢.genericUnit m
        (𝒢.G.left.presheaf.map (homOfLE le_top).op σa * s) := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply]
    rfl
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ U m _, germAlong_eventuallyEq 𝒢 hΦ U m s,
    (hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m)] with z h1 h2 hz
  rw [h1, h2, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz, hσa, evalAt_structSection]

/-- **Clause (iii) of `JacDetMultilinear`, proved: scaling by `τ(a)`.** -/
theorem jacDet_update_smul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
    (x : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
      τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((𝒢.structMap a • x : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      τ (algebraMap (𝓞 L) L a) • row (x : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_smul, smul_eq_mul, Pi.smul_apply]
    rw [(germAlong_structMap_mul_eventuallyEq 𝒢 hΦ a _).fderiv_eq,
      fderiv_const_mul (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, hrow, Matrix.det_updateRow_smul]

end Scalar

/-- **Glue (the last clause of `JacDetMultilinear`: class invariance).** `jacDet Φ f` depends
only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`. Why true: by `germAlong_eventuallyEq` and
`germAlong_add_eventuallyEq` it suffices that `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`, a sum of
products `uv` with `u, v ∈ 𝔪_ξ`; `germAlong Φ (uv) = (germAlong Φ u)(germAlong Φ v)` near `0` (as
for sums, with `evalAt_mul`), and `germAlong Φ u` vanishes at `0` because the identity point
`Spec ℂ → 𝒢` lies over `ξ` (`one_left_apply`) and induces a local map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ`,
which kills `𝔪_ξ`; then Leibniz. Unproved (needs `evalAt` through `Scheme.Hom.stalkMap` at the
identity point). -/
def JacDetClassInvariant : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f'

/-- **`JacDetClassScalar` from `JacDetClassInvariant` (proved).** -/
theorem jacDetClassScalar_of (h : JacDetClassInvariant) : JacDetClassScalar := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  exact ⟨h K A L 𝒢 τ g Λ Φ hΦ, fun f i a x => jacDet_update_smul 𝒢 hΦ f i a x⟩

end ZInQ.Metrization



/-! ## metrization: clause (i) of `JacDetMultilinear` (class invariance), proved

So `JacDetMultilinear`, hence `JacDetDescends`, is a theorem. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

section ClassInv

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- A section whose germ at `ξ` lies in `𝔪_ξ` vanishes at the identity complex point. -/
theorem evalAt_one_eq_zero {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  set q := (1 : 𝒢.Pts τ).left with hqdef
  have hq : ∀ x, q x = 𝒢.genericUnit := fun x => by
    rw [hqdef]
    erw [one_left_apply]
  have h : ⊤ ≤ q ⁻¹ᵁ U := by
    intro x _
    show q x ∈ U
    rw [hq]
    exact m
  unfold GroupModel.evalAt
  rw [dif_pos h]
  let q' : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := q
  have h' : ⊤ ≤ q' ⁻¹ᵁ U := h
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q'.appLE U ⊤ h' s) = 0
  let x : Spec (CommRingCat.of ℂ) := genericPoint (Spec (CommRingCat.of ℂ))
  have hxt : x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := by simp
  have hx : q' x ∈ U := h' hxt
  have key : q'.appLE U ⊤ h' ≫ (Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt =
      𝒢.G.left.presheaf.germ U (q' x) hx ≫ q'.stalkMap x := by
    simp only [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.germ_stalkMap]
    rw [TopCat.Presheaf.germ_res]
  have hmem : ∀ (y : 𝒢.G.left) (hy : y ∈ U), y = 𝒢.genericUnit →
      𝒢.G.left.presheaf.germ U y hy s ∈
        IsLocalRing.maximalIdeal (𝒢.G.left.presheaf.stalk y) := by
    rintro y hy rfl
    exact hs
  have h1 := hmem (q' x) hx (hq x)
  have h2 : (q'.stalkMap x).hom (𝒢.G.left.presheaf.germ U (q' x) hx s) ∈
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) :=
    map_nonunit _ _ ((IsLocalRing.mem_maximalIdeal _).mp h1)
  have hfield : IsField ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) := Field.toIsField _
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at h2
  have h4 : ((Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt) (q'.appLE U ⊤ h' s) =
      (q'.stalkMap x) (𝒢.G.left.presheaf.germ U (q' x) hx s) := by
    rw [← ConcreteCategory.comp_apply, key, ConcreteCategory.comp_apply]
  have h5 : q'.appLE U ⊤ h' s = 0 := by
    apply germ_injective_of_isIntegral (U := ⊤) _ x hxt
    rw [map_zero]
    exact h4.trans h2
  rw [h5, map_zero]

/-- `germAlong Φ u` vanishes at `0` for `u ∈ 𝔪_ξ`. -/
theorem germAlong_zero_of_mem {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (u : 𝒢.genStalk)
    (hu : u ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ u 0 = 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep u
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  rw [(germAlong_eventuallyEq 𝒢 hΦ U m s).eq_of_nhds, h1]
  exact evalAt_one_eq_zero 𝒢 U m s hu

/-- `germAlong Φ (x * y) = germAlong Φ x * germAlong Φ y` near `0`. -/
theorem germAlong_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x * y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x * 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hprod : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s *
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_mul, TopCat.Presheaf.germ_res_apply]
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.mul_apply, h1, h2, h3, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`. -/
theorem fderiv_germAlong_eq_zero_of_mem_sq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) :
    fderiv ℂ (𝒢.germAlong Φ t) 0 = 0 := by
  rw [pow_two] at ht
  refine Submodule.mul_induction_on ht (fun u hu v hv => ?_) (fun a b ha hb => ?_)
  · rw [(germAlong_mul_eventuallyEq 𝒢 hΦ u v).fderiv_eq,
      fderiv_mul (germAlong_differentiableAt 𝒢 hΦ u) (germAlong_differentiableAt 𝒢 hΦ v),
      germAlong_zero_of_mem 𝒢 hΦ u hu, germAlong_zero_of_mem 𝒢 hΦ v hv]
    ext v
    simp
  · rw [(germAlong_add_eventuallyEq 𝒢 hΦ a b).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ a) (germAlong_differentiableAt 𝒢 hΦ b), ha, hb,
      add_zero]

/-- **Clause (i) of `JacDetMultilinear`, proved: `jacDet` depends only on the classes `df_i`.** -/
theorem jacDet_congr_dCls {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk)
    (h : ∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) : 𝒢.jacDet Φ f = 𝒢.jacDet Φ f' := by
  have hrow : ∀ i, fderiv ℂ (𝒢.germAlong Φ (f i : 𝒢.genStalk)) 0 =
      fderiv ℂ (𝒢.germAlong Φ (f' i : 𝒢.genStalk)) 0 := by
    intro i
    have hsq : ((f i : 𝒢.genStalk) - f' i) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2 :=
      (Ideal.toCotangent_eq (IsLocalRing.maximalIdeal 𝒢.genStalk)).mp (h i)
    have hdecomp : (f i : 𝒢.genStalk) = f' i + ((f i : 𝒢.genStalk) - f' i) := by ring
    rw [hdecomp, (germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _),
      fderiv_germAlong_eq_zero_of_mem_sq 𝒢 hΦ _ hsq, add_zero]
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply, hrow i]

end ClassInv

/-- **`JacDetClassInvariant`, proved.** -/
theorem jacDetClassInvariant : JacDetClassInvariant := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ f f' h
  exact jacDet_congr_dCls 𝒢 hΦ f f' h

/-- **`JacDetDescends`, proved** (no hypotheses). -/
theorem jacDetDescends : JacDetDescends :=
  jacDetDescends_of (jacDetMultilinear_of (jacDetClassScalar_of jacDetClassInvariant))

end ZInQ.Metrization


/-! # height-glue: `AnalyticUniformizationUnique` from the uniformization theorem

The kernel Prop `ZInQ.DefFaltings.AnalyticUniformizationUnique` (imported, never restated) is
proved here from two Props:

* `ImmersiveUniformizationExists` (LEAF, consequence of the uniformization theorem
  `A(ℂ)^an ≅ ℂ^g/Λ` as complex Lie groups, Mumford *Abelian varieties* §1, with the analytic
  structure of `A(ℂ)` given by regular functions): some analytic uniformization with a full
  lattice is an immersion at `0` for the regular functions.
* `AnalyticPointsT2` (LEAF, SGA 1 XII 3.1 / Serre GAGA: the analytic space of a separated scheme
  of finite type over `ℂ` is Hausdorff): the analytic topology `anTop` on `𝒢(ℂ)_τ` is Hausdorff.

The rest is proved: continuity of every analytic uniformization for `anTop`, the homeomorphism
`ℂ^{g₀}/Λ₀ ≃ₜ 𝒢(ℂ)_τ` (compact to Hausdorff), the lift of any analytic uniformization through the
covering `ℂ^{g₀} → ℂ^{g₀}/Λ₀`, its additivity, `ℝ`- then `ℂ`-linearity, surjectivity (Baire), and
the linear algebra producing `T`. -/

namespace ZInQ.HeightGlue

open ZInQ.DefFaltings CategoryTheory AlgebraicGeometry Topology MonObj

set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
open PkgI3 (AbVar)

section Defs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **The analytic topology on `𝒢(ℂ)_τ`.** Generated by the sets `{p ∈ U(ℂ) | s(p) ∈ V}` for
`U ⊆ 𝒢` Zariski open, `s ∈ Γ(U, 𝒪_𝒢)` and `V ⊆ ℂ` open (`V = ℂ` gives `U(ℂ)` itself). On an
affine open `U = Spec R` (`R` of finite type over `𝓞_L`) this is the topology of `U(ℂ)_τ ⊆ ℂ^n`
given by generators of `R`, i.e. the usual analytic topology of `(𝒢 ×_{𝓞_L,τ} ℂ)(ℂ)`. -/
def anTop (𝒢 : GroupModel A L) (τ : L →+* ℂ) : TopologicalSpace (𝒢.Pts τ) :=
  TopologicalSpace.generateFrom {S | ∃ (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) (V : Set ℂ),
    IsOpen V ∧ S = {p | ⊤ ≤ p.left ⁻¹ᵁ U ∧ 𝒢.evalAt p U s ∈ V}}

/-- `Φ : ℂ^g → 𝒢(ℂ)_τ` is an immersion at `0` for the regular functions: every nonzero tangent
vector at `0` is detected by the differential of some regular function defined near `Φ(0)`. -/
def IsImmersiveAtZero (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) : Prop :=
  ∀ v : Fin g → ℂ, v ≠ 0 → ∃ (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)),
    (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U ∧ fderiv ℂ (fun z => 𝒢.evalAt (Φ z) U s) 0 v ≠ 0

end Defs

/-- **LEAF `AnalyticPointsT2`** (SGA 1 Exp. XII Prop. 3.1, or Serre, GAGA §2; locators
UNVERIFIED): for a separated scheme `X` locally of finite type over `ℂ`, `X(ℂ)` with the analytic
topology is Hausdorff. Applied to `X = 𝒢 ×_{𝓞_L,τ} Spec ℂ` (separated, smooth over `ℂ`), whose
`ℂ`-points are `𝒢.Pts τ` and whose analytic topology is `anTop 𝒢 τ`. -/
def AnalyticPointsT2 : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ), @T2Space (𝒢.Pts τ) (anTop 𝒢 τ)

/-- **LEAF `ImmersiveUniformizationExists`** (the uniformization theorem, Mumford, *Abelian
varieties*, §1, Thm. on p. 2 (UNVERIFIED locator): the compact connected complex Lie group
`A_τ(ℂ)^an` is `ℂ^g/Λ` for a full lattice `Λ`, the isomorphism being biholomorphic, where the
complex structure of `A_τ(ℂ)^an` has local coordinates given by regular functions (Jacobian
criterion, `A` smooth)). The biholomorphism `ℂ^g → ℂ^g/Λ ≅ A_τ(ℂ)` is an analytic uniformization
whose regular-function differentials at `0` span the cotangent space, i.e. which is immersive at
`0`. Strengthens the kernel's `AnalyticUniformizationExists` only by the immersion clause
(`analyticUniformizationExists_of_immersive`). -/
def ImmersiveUniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ), ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
      (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ ∧
        IsImmersiveAtZero 𝒢 τ Φ

theorem analyticUniformizationExists_of_immersive (h : ImmersiveUniformizationExists) :
    AnalyticUniformizationExists := by
  intro K _ A L _ _ _ 𝒢 τ
  obtain ⟨g, Λ, Φ, hd, hl, hu, -⟩ := h K A L 𝒢 τ
  exact ⟨g, Λ, Φ, hd, hl, hu⟩

section Proofs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L) (τ : L →+* ℂ)

/-- Every analytic uniformization is continuous for the analytic topology. -/
theorem continuous_of_isAnalyticUniformization {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (h : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    @Continuous _ _ _ (anTop 𝒢 τ) Φ := by
  letI := anTop 𝒢 τ
  unfold anTop
  rw [continuous_generateFrom_iff]
  rintro S ⟨U, s, V, hV, rfl⟩
  have hc : ContinuousOn (fun z => 𝒢.evalAt (Φ z) U s) (𝒢.dom Φ U) := (h.2.2.2.2 U s).continuousOn
  exact hc.isOpen_inter_preimage (h.2.2.2.1 U) hV

variable {𝒢 τ}

theorem au_map_zero {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (h : 𝒢.IsAnalyticUniformization τ Λ Φ) : Φ 0 = 1 :=
  (h.2.1 0).2 Λ.zero_mem

theorem au_map_neg {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (h : 𝒢.IsAnalyticUniformization τ Λ Φ) (z : Fin g → ℂ) :
    Φ (-z) = (Φ z)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← h.1, neg_add_cancel, au_map_zero h]

theorem au_eq_iff {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (h : 𝒢.IsAnalyticUniformization τ Λ Φ) (a b : Fin g → ℂ) :
    Φ a = Φ b ↔ a - b ∈ Λ := by
  rw [← h.2.1, sub_eq_add_neg, h.1, au_map_neg h, mul_inv_eq_one]

end Proofs

/-! ## Linear algebra: two surjections differ by an automorphism -/

theorem exists_linearEquiv_comp_eq {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (L₁ L₂ : V →ₗ[ℂ] W) (h₁ : Function.Surjective L₁) (h₂ : Function.Surjective L₂) :
    ∃ T : V ≃ₗ[ℂ] V, ∀ v, L₁ (T v) = L₂ v := by
  obtain ⟨C₁, hC₁⟩ := Submodule.exists_isCompl (LinearMap.ker L₁)
  obtain ⟨C₂, hC₂⟩ := Submodule.exists_isCompl (LinearMap.ker L₂)
  let e₁ : C₁ ≃ₗ[ℂ] W := (Submodule.quotientEquivOfIsCompl _ _ hC₁).symm.trans
    (L₁.quotKerEquivOfSurjective h₁)
  let e₂ : C₂ ≃ₗ[ℂ] W := (Submodule.quotientEquivOfIsCompl _ _ hC₂).symm.trans
    (L₂.quotKerEquivOfSurjective h₂)
  have he₁ : ∀ c : C₁, e₁ c = L₁ c := fun c => by
    simp [e₁, Submodule.quotientEquivOfIsCompl, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have he₂ : ∀ c : C₂, e₂ c = L₂ c := fun c => by
    simp [e₂, Submodule.quotientEquivOfIsCompl, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have hrk : Module.finrank ℂ (LinearMap.ker L₂) = Module.finrank ℂ (LinearMap.ker L₁) := by
    have a := L₁.finrank_range_add_finrank_ker
    have b := L₂.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr h₁, finrank_top] at a
    rw [LinearMap.range_eq_top.mpr h₂, finrank_top] at b
    omega
  let k : LinearMap.ker L₂ ≃ₗ[ℂ] LinearMap.ker L₁ := LinearEquiv.ofFinrankEq _ _ hrk
  let T : V ≃ₗ[ℂ] V := (Submodule.prodEquivOfIsCompl _ _ hC₂).symm.trans
    ((LinearEquiv.prodCongr k (e₂.trans e₁.symm)).trans (Submodule.prodEquivOfIsCompl _ _ hC₁))
  refine ⟨T, fun v => ?_⟩
  obtain ⟨⟨a, c⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ hC₂).surjective v
  have hT : T ((Submodule.prodEquivOfIsCompl _ _ hC₂) (a, c)) =
      (Submodule.prodEquivOfIsCompl _ _ hC₁) (k a, e₁.symm (e₂ c)) := by
    simp only [T, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  rw [hT, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add, map_add,
    LinearMap.mem_ker.mp (k a).2, LinearMap.mem_ker.mp a.2, ← he₁, LinearEquiv.apply_symm_apply,
    he₂]

/-! ## Every analytic uniformization factors linearly through a full-lattice one -/

section Factor

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable {𝒢 : GroupModel A L} {τ : L →+* ℂ}

/-- **Factorization.** If `anTop` is Hausdorff and `Φ₀` is an analytic uniformization with a full
lattice `Λ₀` that is immersive at `0`, then every analytic uniformization `Φ` (of any dimension
`g`, no lattice hypothesis) is `Φ₀ ∘ M` for a surjective `ℂ`-linear `M : ℂ^g → ℂ^{g₀}`. -/
theorem exists_linear_factor (hT2 : @T2Space (𝒢.Pts τ) (anTop 𝒢 τ)) {g₀ : ℕ}
    (Λ₀ : Submodule ℤ (Fin g₀ → ℂ)) [DiscreteTopology Λ₀] [IsZLattice ℝ Λ₀]
    {Φ₀ : (Fin g₀ → ℂ) → 𝒢.Pts τ} (h₀ : 𝒢.IsAnalyticUniformization τ Λ₀ Φ₀)
    (him : IsImmersiveAtZero 𝒢 τ Φ₀) {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (h : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g₀ → ℂ), Function.Surjective M ∧ ∀ z, Φ z = Φ₀ (M z) := by
  letI := anTop 𝒢 τ
  let S : AddSubgroup (Fin g₀ → ℂ) := Λ₀.toAddSubgroup
  have hS : IsDiscrete (S : Set (Fin g₀ → ℂ)) :=
    isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology Λ₀›
  have hcov : IsCoveringMap (QuotientAddGroup.mk : (Fin g₀ → ℂ) → (Fin g₀ → ℂ) ⧸ S) :=
    (AddSubgroup.isAddQuotientCoveringMap_of_comm S hS).isCoveringMap
  have hcpt : CompactSpace ((Fin g₀ → ℂ) ⧸ S) := by
    have := IsZLattice.isCompact_range_of_periodic Λ₀
      (QuotientAddGroup.mk : (Fin g₀ → ℂ) → (Fin g₀ → ℂ) ⧸ S) continuous_quot_mk
      (fun z w hw => QuotientAddGroup.eq.mpr (by
        rw [neg_add_rev, add_assoc, neg_add_cancel, add_zero]; exact S.neg_mem hw))
    rw [QuotientAddGroup.mk_surjective.range_eq] at this
    exact isCompact_univ_iff.mp this
  -- the induced bijection `ℂ^{g₀}/Λ₀ → 𝒢(ℂ)_τ`
  let φ : (Fin g₀ → ℂ) ⧸ S → 𝒢.Pts τ := Quotient.lift (s := QuotientAddGroup.leftRel S) Φ₀
    (fun a b hab => by
      rw [au_eq_iff h₀]
      have := QuotientAddGroup.leftRel_apply.mp hab
      rw [← neg_neg (a - b), neg_sub, ← neg_add_eq_sub]
      exact Λ₀.neg_mem this)
  have hφc : Continuous φ := (continuous_of_isAnalyticUniformization 𝒢 τ h₀).quotient_lift _
  have hφi : Function.Injective φ := by
    intro x y hxy
    induction x using Quotient.inductionOn with | h a => ?_
    induction y using Quotient.inductionOn with | h b => ?_
    apply Quotient.sound
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    rw [neg_add_eq_sub]
    exact (au_eq_iff h₀ b a).mp hxy.symm
  have hφs : Function.Surjective φ := fun p => by
    obtain ⟨a, ha⟩ := h₀.2.2.1 p
    exact ⟨QuotientAddGroup.mk a, ha⟩
  let e : (Fin g₀ → ℂ) ⧸ S ≃ₜ 𝒢.Pts τ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ ⟨hφi, hφs⟩) hφc
  have he : ∀ x, e (QuotientAddGroup.mk x) = Φ₀ x := fun x => rfl
  -- lift `Φ` through the covering
  let ψ : C(Fin g → ℂ, (Fin g₀ → ℂ) ⧸ S) :=
    ⟨fun z => e.symm (Φ z), e.symm.continuous.comp (continuous_of_isAnalyticUniformization 𝒢 τ h)⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts ψ 0 0 (by
    show (QuotientAddGroup.mk 0 : (Fin g₀ → ℂ) ⧸ S) = e.symm (Φ 0)
    rw [Homeomorph.eq_symm_apply, he, au_map_zero h₀, au_map_zero h])
  have hΦF : ∀ z, Φ z = Φ₀ (F z) := by
    intro z
    have h1 : (QuotientAddGroup.mk (F z) : (Fin g₀ → ℂ) ⧸ S) = e.symm (Φ z) := congrFun hF z
    rw [← he, h1, e.apply_symm_apply]
  -- additivity
  have hmem : ∀ z w, F (z + w) - (F z + F w) ∈ Λ₀ := fun z w =>
    (au_eq_iff h₀ _ _).1 (by rw [← hΦF, h.1, hΦF, hΦF, ← h₀.1])
  let D : (Fin g → ℂ) × (Fin g → ℂ) → Λ₀ := fun p => ⟨_, hmem p.1 p.2⟩
  have hD : Continuous D := Continuous.subtype_mk
    ((F.continuous.comp (continuous_fst.add continuous_snd)).sub
      ((F.continuous.comp continuous_fst).add (F.continuous.comp continuous_snd))) _
  have hadd : ∀ z w, F (z + w) = F z + F w := by
    intro z w
    have h2 := congrArg Subtype.val
      (PreconnectedSpace.constant inferInstance hD (x := (z, w)) (y := (0, 0)))
    simp only [D, add_zero, hF0, sub_zero] at h2
    exact sub_eq_zero.mp h2
  let Fp : (Fin g → ℂ) →+ (Fin g₀ → ℂ) := AddMonoidHom.mk' F hadd
  let M₀ : (Fin g → ℂ) →L[ℝ] (Fin g₀ → ℂ) := Fp.toRealLinearMap F.continuous
  have hM₀ : ∀ z, M₀ z = F z := fun z => rfl
  have hr : ∀ (r : ℝ) x, F (r • x) = r • F x := fun r x => map_real_smul Fp F.continuous r x
  -- `ℂ`-linearity from the immersion at `0`
  have hI : ∀ v, F (Complex.I • v) = Complex.I • F v := by
    intro v
    by_contra hne
    obtain ⟨U, s, h0U, hd⟩ := him _ (sub_ne_zero.mpr hne)
    set F₀ := fun x => 𝒢.evalAt (Φ₀ x) U s with hF₀
    set G := fun z => 𝒢.evalAt (Φ z) U s with hG
    have hdiff₀ : DifferentiableAt ℂ F₀ 0 :=
      ((h₀.2.2.2.2 U s) 0 h0U).differentiableAt ((h₀.2.2.2.1 U).mem_nhds h0U)
    have h0U' : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := by
      show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
      rw [hΦF, hF0]; exact h0U
    have hdiff : DifferentiableAt ℂ G 0 :=
      ((h.2.2.2.2 U s) 0 h0U').differentiableAt ((h.2.2.2.1 U).mem_nhds h0U')
    have e1 : HasFDerivAt G ((fderiv ℂ G 0).restrictScalars ℝ) 0 :=
      hdiff.hasFDerivAt.restrictScalars ℝ
    have e2 : HasFDerivAt G (((fderiv ℂ F₀ 0).restrictScalars ℝ).comp M₀) 0 := by
      have hf : G = F₀ ∘ M₀ := funext fun z => by simp only [hG, hF₀, Function.comp_apply, hM₀, hΦF]
      rw [hf]
      have : HasFDerivAt F₀ ((fderiv ℂ F₀ 0).restrictScalars ℝ) (M₀ 0) := by
        rw [hM₀, hF0]; exact hdiff₀.hasFDerivAt.restrictScalars ℝ
      exact this.comp 0 M₀.hasFDerivAt
    have heq := e1.unique e2
    have k1 := congrArg (fun T => T (Complex.I • v)) heq
    have k2 := congrArg (fun T => T v) heq
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_comp,
      Function.comp_apply, hM₀] at k1 k2
    apply hd
    rw [map_sub, ← k1, map_smul (fderiv ℂ F₀ 0), ← k2, ← map_smul (fderiv ℂ G 0), sub_self]
  have hsmul : ∀ (c : ℂ) z, F (c • z) = c • F z := by
    intro c z
    have hc : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (y : V),
        c • y = (c.re : ℝ) • y + (c.im : ℝ) • (Complex.I • y) := by
      intro V _ _ y
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [hc z, hadd, hr, hr, hI, ← hc]
  let M : (Fin g → ℂ) →ₗ[ℂ] (Fin g₀ → ℂ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  have hMF : ∀ z, M z = F z := fun z => rfl
  refine ⟨M, ?_, fun z => by rw [hMF, hΦF]⟩
  -- surjectivity (Baire)
  have hrange : ∀ x, ∃ z, x - M z ∈ Λ₀ := fun x => by
    obtain ⟨z, hz⟩ := h.2.2.1 (Φ₀ x)
    exact ⟨z, (au_eq_iff h₀ _ _).1 (by rw [hMF, ← hΦF, hz])⟩
  rw [← LinearMap.range_eq_top]
  let W := LinearMap.range M
  have hWc : IsClosed (W : Set (Fin g₀ → ℂ)) := W.closed_of_finiteDimensional
  haveI : Countable Λ₀ := countable_of_Lindelof_of_discrete
  let f : Λ₀ → Set (Fin g₀ → ℂ) := fun l => Homeomorph.addLeft (l : Fin g₀ → ℂ) '' (W : Set _)
  have hfc : ∀ l, IsClosed (f l) := fun l => (Homeomorph.addLeft _).isClosedMap _ hWc
  have hfU : ⋃ l, f l = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨z, hz⟩ := hrange x
    exact Set.mem_iUnion.mpr ⟨⟨_, hz⟩, M z, LinearMap.mem_range_self M z, by
      simp [Homeomorph.coe_addLeft]⟩
  obtain ⟨l, hl⟩ := nonempty_interior_of_iUnion_of_closed hfc hfU
  rw [← Homeomorph.image_interior] at hl
  exact (W.restrictScalars ℝ).eq_top_of_nonempty_interior' (hl.of_image) |>
    fun h => by
      rw [eq_top_iff] at h ⊢
      exact fun x _ => h (Submodule.mem_top (x := x))

end Factor

/-! ## The kernel Prop -/

/-- **`AnalyticUniformizationUnique` (kernel AN3U) from the two leaves.** -/
theorem analyticUniformizationUnique_of (hE : ImmersiveUniformizationExists)
    (hT : AnalyticPointsT2) : AnalyticUniformizationUnique := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Λ' Φ Φ' h h'
  obtain ⟨g₀, Λ₀, Φ₀, hd, hl, h₀, him⟩ := hE K A L 𝒢 τ
  obtain ⟨M, hMs, hM⟩ := exists_linear_factor (hT K A L 𝒢 τ) Λ₀ h₀ him h
  obtain ⟨M', hMs', hM'⟩ := exists_linear_factor (hT K A L 𝒢 τ) Λ₀ h₀ him h'
  obtain ⟨T, hT⟩ := exists_linearEquiv_comp_eq M M' hMs hMs'
  have hΦ : ∀ z, Φ' z = Φ (T z) := fun z => by rw [hM', hM, hT]
  refine ⟨T, hΦ, fun z => ?_⟩
  rw [← h'.2.1, ← h.2.1, hΦ]

/-- **Corollary: every full-lattice analytic uniformization is immersive at `0`** (from the same
two leaves): uniqueness transports the immersion clause along `T`. -/
theorem isImmersiveAtZero_of (hE : ImmersiveUniformizationExists) (hT : AnalyticPointsT2)
    {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h : 𝒢.IsAnalyticUniformization τ Λ Φ) : IsImmersiveAtZero 𝒢 τ Φ := by
  obtain ⟨g₀, Λ₀, Φ₀, hd, hl, h₀, him⟩ := hE K A L 𝒢 τ
  obtain ⟨M, hMs, hM⟩ := exists_linear_factor (hT K A L 𝒢 τ) Λ₀ h₀ him h
  -- `M` is injective: its kernel lies in the discrete `Λ` and is a `ℂ`-subspace
  have hMi : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hsub : ∀ t : ℝ, (t : ℂ) • v ∈ Λ := fun t => by
      rw [← h.2.1, hM, map_smul, LinearMap.mem_ker.mp hv, smul_zero, au_map_zero h₀]
    by_contra hv0
    -- the image of `ℝ` in the discrete `Λ` is a connected subset, hence a point
    let c : ℝ → Λ := fun t => ⟨(t : ℂ) • v, hsub t⟩
    have hc : Continuous c := Continuous.subtype_mk
      ((Complex.continuous_ofReal).smul continuous_const) _
    have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0))
    simp [c] at this
    exact hv0 this
  intro v hv
  obtain ⟨U, s, h0U, hd'⟩ := him (M v) (fun h0 => hv (hMi (by rw [h0, map_zero])))
  have h0U' : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := by
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
    rw [hM, map_zero]; exact h0U
  refine ⟨U, s, h0U', ?_⟩
  have hdiff₀ : DifferentiableAt ℂ (fun x => 𝒢.evalAt (Φ₀ x) U s) (M 0) := by
    rw [map_zero]
    exact ((h₀.2.2.2.2 U s) 0 h0U).differentiableAt ((h₀.2.2.2.1 U).mem_nhds h0U)
  have hcomp : (fun z => 𝒢.evalAt (Φ z) U s) = (fun x => 𝒢.evalAt (Φ₀ x) U s) ∘
      (LinearMap.toContinuousLinearMap M) := funext fun z => by simp [hM]
  rw [hcomp, fderiv_comp 0 (by simpa using hdiff₀)
    (LinearMap.toContinuousLinearMap M).differentiableAt, ContinuousLinearMap.fderiv, map_zero]
  exact hd'



/-! ## The two leaves of §1 proved: Hausdorffness and immersion

`AnalyticPointsT2` is proved from metrization2's `productMapLocalStructure` (the local structure
of `𝒢 ×_{𝓞_L} 𝒢` at complex points) applied to the division morphism `(x, y) ↦ x y⁻¹`, and from
`pts_eq_of_evalAt` (a complex point of an affine open is determined by its values).

`IsImmersiveAtZero` is proved for **every** analytic uniformization with a discrete kernel, by
metrization2's argument for `jacDetNondegenerate_of` (steps 2-5: translation through
`productMapLocalStructure`, constancy along a line, discreteness). -/

section T2

open ZInQ.Metrization ZInQ.Metrization2 MonoidalCategory CartesianMonoidalCategory

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L) (τ : L →+* ℂ)

theorem isOpen_evalSet (V : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, V)) (t : Set ℂ) (ht : IsOpen t) :
    @IsOpen _ (anTop 𝒢 τ) {p : 𝒢.Pts τ | ⊤ ≤ p.left ⁻¹ᵁ V ∧ 𝒢.evalAt p V s ∈ t} :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨V, s, t, ht, rfl⟩

theorem isOpen_ptsIn (V : 𝒢.G.left.Opens) :
    @IsOpen _ (anTop 𝒢 τ) {p : 𝒢.Pts τ | ⊤ ≤ p.left ⁻¹ᵁ V} := by
  have := isOpen_evalSet 𝒢 τ V 0 Set.univ isOpen_univ
  simpa using this

theorem continuousOn_evalAt (V : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, V)) :
    @ContinuousOn _ _ (anTop 𝒢 τ) _ (fun p => 𝒢.evalAt p V s) {p | ⊤ ≤ p.left ⁻¹ᵁ V} := by
  letI := anTop 𝒢 τ
  rw [continuousOn_iff']
  intro t ht
  refine ⟨_, isOpen_evalSet 𝒢 τ V s t ht, ?_⟩
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  tauto

/-- The division morphism `(x, y) ↦ x y⁻¹` of the group scheme `𝒢`. -/
noncomputable def divMor : 𝒢.G ⊗ 𝒢.G ⟶ 𝒢.G := (𝒢.G ◁ GrpObj.inv (X := 𝒢.G)) ≫ μ[𝒢.G]

theorem lift_divMor (x y : 𝒢.Pts τ) : lift x y ≫ divMor 𝒢 = x * y⁻¹ := by
  rw [divMor, ← Category.assoc, lift_whiskerLeft]
  rfl

/-- **`AnalyticPointsT2`, proved** (no hypotheses): the analytic topology on `𝒢(ℂ)_τ` is
Hausdorff. -/
theorem analyticPointsT2 : AnalyticPointsT2 := by
  intro K _ A L _ _ _ 𝒢 τ
  letI := anTop 𝒢 τ
  refine ⟨fun p q hpq => ?_⟩
  set r : 𝒢.Pts τ := lift p q ≫ divMor 𝒢 with hr
  have hr1 : r ≠ 1 := by
    rw [hr, lift_divMor]
    intro h
    exact hpq (mul_inv_eq_one.mp h)
  let pt : Spec (CommRingCat.of ℂ) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show r.left pt ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hrU : ⊤ ≤ r.left ⁻¹ᵁ U := top_le_of_mem r.left U pt mU
  -- a section `s` and a radius `δ` separating `r` from `1` (if `1 ∈ U(ℂ)`)
  obtain ⟨s, δ, hδ, hsep⟩ : ∃ (s : Γ(𝒢.G.left, U)) (δ : ℝ), 0 < δ ∧
      (⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U → δ ≤ ‖𝒢.evalAt r U s - 𝒢.evalAt (1 : 𝒢.Pts τ) U s‖) := by
    by_cases h1 : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U
    · have : ∃ s : Γ(𝒢.G.left, U), 𝒢.evalAt r U s ≠ 𝒢.evalAt (1 : 𝒢.Pts τ) U s := by
        by_contra hcon
        push_neg at hcon
        exact hr1 (pts_eq_of_evalAt 𝒢 U hU r 1 hrU h1 hcon)
      obtain ⟨s, hs⟩ := this
      exact ⟨s, _, norm_pos_iff.mpr (sub_ne_zero.mpr hs), fun _ => le_rfl⟩
    · exact ⟨0, 1, one_pos, fun h => absurd h h1⟩
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    productMapLocalStructure K A A A L 𝒢 𝒢 𝒢 (divMor 𝒢) τ U s p q hrU
  -- the functions `H = Σ c ⊗ d` and `N = Σ a ⊗ b` on `V₁(ℂ) × V₂(ℂ)`
  set S : Set (𝒢.Pts τ × 𝒢.Pts τ) :=
    {p | ⊤ ≤ p.left ⁻¹ᵁ V₁} ×ˢ {p | ⊤ ≤ p.left ⁻¹ᵁ V₂} with hS
  let H : 𝒢.Pts τ × 𝒢.Pts τ → ℂ := fun z =>
    ∑ k, 𝒢.evalAt z.1 V₁ (c k) * 𝒢.evalAt z.2 V₂ (d k)
  let N : 𝒢.Pts τ × 𝒢.Pts τ → ℂ := fun z =>
    ∑ k, 𝒢.evalAt z.1 V₁ (a k) * 𝒢.evalAt z.2 V₂ (b k)
  have hS_open : IsOpen S := (isOpen_ptsIn 𝒢 τ V₁).prod (isOpen_ptsIn 𝒢 τ V₂)
  have hc1 : ∀ s₁ : Γ(𝒢.G.left, V₁), ContinuousOn (fun z : 𝒢.Pts τ × 𝒢.Pts τ =>
      𝒢.evalAt z.1 V₁ s₁) S := fun s₁ =>
    (continuousOn_evalAt 𝒢 τ V₁ s₁).comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hc2 : ∀ s₂ : Γ(𝒢.G.left, V₂), ContinuousOn (fun z : 𝒢.Pts τ × 𝒢.Pts τ =>
      𝒢.evalAt z.2 V₂ s₂) S := fun s₂ =>
    (continuousOn_evalAt 𝒢 τ V₂ s₂).comp continuous_snd.continuousOn (fun z hz => hz.2)
  have hH : ContinuousOn H S :=
    continuousOn_finset_sum _ fun k _ => (hc1 (c k)).mul (hc2 (d k))
  have hN : ContinuousOn N S :=
    continuousOn_finset_sum _ fun k _ => (hc1 (a k)).mul (hc2 (b k))
  -- the open set `W ∋ (p, q)`
  set W : Set (𝒢.Pts τ × 𝒢.Pts τ) := S ∩ (fun z => (H z, N z)) ⁻¹'
    {w : ℂ × ℂ | w.1 ≠ 0 ∧ ‖w.2 / w.1 - 𝒢.evalAt r U s‖ < δ / 2} with hW
  have hW_open : IsOpen W := by
    refine (hH.prodMk hN).isOpen_inter_preimage hS_open ?_
    have : IsOpen {w : ℂ × ℂ | w.1 ≠ 0} := isOpen_ne_fun continuous_fst continuous_const
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨hw1, hw2⟩
    have hcont : ContinuousAt (fun w : ℂ × ℂ => ‖w.2 / w.1 - 𝒢.evalAt r U s‖) w :=
      ((continuous_snd.continuousAt.div continuous_fst.continuousAt hw1).sub
        continuousAt_const).norm
    exact Filter.inter_mem (this.mem_nhds hw1)
      (hcont.preimage_mem_nhds (Iio_mem_nhds hw2))
  have hpqW : (p, q) ∈ W := by
    refine ⟨⟨hV₁, hV₂⟩, hne, ?_⟩
    obtain ⟨-, heq⟩ := hall p q hV₁ hV₂ hne
    show ‖N (p, q) / H (p, q) - 𝒢.evalAt r U s‖ < δ / 2
    have : N (p, q) / H (p, q) = 𝒢.evalAt r U s := by
      rw [div_eq_iff hne]; exact heq.symm
    rw [this, sub_self, norm_zero]
    linarith
  obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ := isOpen_prod_iff.mp hW_open p q hpqW
  refine ⟨u, v, hu, hv, hpu, hqv, Set.disjoint_left.mpr fun x hxu hxv => ?_⟩
  obtain ⟨⟨hx1, hx2⟩, hxH, hxN⟩ := huv (show (x, x) ∈ u ×ˢ v from ⟨hxu, hxv⟩)
  obtain ⟨hmem, heq⟩ := hall x x hx1 hx2 hxH
  have hxx : lift x x ≫ divMor 𝒢 = 1 := by rw [lift_divMor, mul_inv_cancel]
  rw [hxx] at hmem heq
  have hval : N (x, x) / H (x, x) = 𝒢.evalAt (1 : 𝒢.Pts τ) U s := by
    rw [div_eq_iff hxH]; exact heq.symm
  have hlt : ‖𝒢.evalAt (1 : 𝒢.Pts τ) U s - 𝒢.evalAt r U s‖ < δ / 2 := by
    have := hxN; simp only [Set.mem_setOf_eq] at this; rwa [hval] at this
  have hge := hsep hmem
  rw [norm_sub_rev] at hge
  linarith

end T2

section Immersion

open ZInQ.Metrization ZInQ.Metrization2

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **Every analytic uniformization with a discrete kernel is immersive at `0`** (proved, no
hypotheses; no lattice condition, no `g = dim A`). Steps 2-5 of metrization2's
`jacDetNondegenerate_of`, copied with the hypothesis "every regular function near `ξ` kills `v`"
in place of step 1. -/
theorem isImmersiveAtZero_of_discrete (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [hdisc : DiscreteTopology Λ] {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) : IsImmersiveAtZero 𝒢 τ Φ := by
  intro v hv0
  by_contra hcon
  push_neg at hcon
  have hv2 : ∀ (V : 𝒢.G.left.Opens) (_ : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)),
      fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0 :=
    fun V m b => hcon V b (zero_mem_dom 𝒢 hΦ V m)
  -- an affine open around `ξ`
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hdomU : IsOpen (𝒢.dom Φ U) := hΦ.2.2.2.1 U
  have h0U : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := zero_mem_dom 𝒢 hΦ U mU
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hBopen : IsOpen {t : ℂ | t • v ∈ 𝒢.dom Φ U} := hdomU.preimage hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBopen 0 (by simp [h0U])
  have hconst : ∀ t ∈ Metric.ball (0 : ℂ) r, Φ (t • v) = Φ 0 := by
    intro t ht
    have hderiv : ∀ (s : Γ(𝒢.G.left, U)), ∀ t₀ ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) U s) 0 t₀ := by
      intro s t₀ ht₀
      have h3 := hasDerivAt_line_zero 𝒢 productMapLocalStructure hΦ v hv2 U s (t₀ • v)
        (hball ht₀)
      have h4 : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + (t - t₀) • v)) U s) 0 t₀ := by
        have h3' : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + t • v)) U s) 0 (t₀ - t₀) := by
          rw [sub_self]; exact h3
        exact h3'.comp_sub_const t₀ t₀
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [← add_smul, add_sub_cancel]
    apply pts_eq_of_evalAt 𝒢 U hU _ _ (hball ht) h0U
    intro s
    have := (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).differentiableAt.differentiableWithinAt)
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).deriv) ht (Metric.mem_ball_self hr)
    simpa using this
  have h0 : Φ 0 = 1 := au_map_zero hΦ
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • v ∈ Λ := fun t ht =>
    (hΦ.2.1 _).mp ((hconst t ht).trans h0)
  obtain ⟨u, hu, hpre⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set Λ))
  have hu0 : (0 : Fin g → ℂ) ∈ u := by
    have : (0 : Λ) ∈ ({0} : Set Λ) := rfl
    rw [← hpre] at this
    exact this
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ u :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hu.mem_nhds hu0)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ Metric.ball (0 : ℂ) r := Metric.ball_mem_nhds 0 hr
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • v ∈ u ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (hev1.and hev2)
  obtain ⟨t, ⟨htu, htb⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hin : (⟨t • v, hmem t htb⟩ : Λ) ∈ Subtype.val ⁻¹' u := htu
  rw [hpre] at hin
  have : t • v = 0 := congrArg Subtype.val hin
  rcases smul_eq_zero.mp this with h | h
  · exact ht0 h
  · exact hv0 h

/-- **`ImmersiveUniformizationExists` is equivalent to the kernel's
`AnalyticUniformizationExists`** (proved). -/
theorem immersiveUniformizationExists_of (hE : AnalyticUniformizationExists) :
    ImmersiveUniformizationExists := by
  intro K _ A L _ _ _ 𝒢 τ
  obtain ⟨g, Λ, Φ, hd, hl, hu⟩ := hE K A L 𝒢 τ
  exact ⟨g, Λ, Φ, hd, hl, hu, isImmersiveAtZero_of_discrete 𝒢 τ hu⟩

end Immersion

/-! ## Main results -/

/-- **`AnalyticUniformizationUnique` (kernel AN3U) from the kernel's `AnalyticUniformizationExists`
(AN3) alone.** -/
theorem analyticUniformizationUnique_of_exists (hE : AnalyticUniformizationExists) :
    AnalyticUniformizationUnique :=
  analyticUniformizationUnique_of (immersiveUniformizationExists_of hE) analyticPointsT2

/-- An abelian variety has finite dimension (copied from unif-dims' copy of metrization's
`abVar_dim_finite`, `scratch/unif-dims/Combined.lean` l. 4559). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : PkgI3.AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- The kernel's `AnalyticUniformizationExists` from the textbook leaf T35
(`ZInQ.LeafPush2.UniformizationExists` = `TextbookLeaves.t35`), via metrization2's transport. -/
theorem analyticUniformizationExists_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    AnalyticUniformizationExists := by
  intro K _ A L _ _ _ 𝒢 τ
  obtain ⟨g, hg⟩ := abVar_dim_finite K A
  exact ⟨g, ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35
    K A L 𝒢 τ g hg⟩

/-- **`AnalyticUniformizationUnique` from the textbook leaf T35.** -/
theorem analyticUniformizationUnique_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    AnalyticUniformizationUnique :=
  analyticUniformizationUnique_of_exists (analyticUniformizationExists_of_t35 hT35)



open ZInQ.HeightSplit


/-- **`UniformizationDim`, from the textbook leaf T35** (proved). T35 (through metrization2's
transport) gives a full-lattice analytic uniformization `Φ'` of dimension `dim A`; a full-lattice
`Φ` of dimension `g` and `Φ'` factor through each other by surjective `ℂ`-linear maps
(`exists_linear_factor`, with `analyticPointsT2` and `isImmersiveAtZero_of_discrete`), so
`g = dim A`. -/
theorem uniformizationDim_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    UniformizationDim := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hd hz hΦ
  obtain ⟨g', hg'⟩ := abVar_dim_finite K A
  obtain ⟨Λ', Φ', hd', hz', hΦ'⟩ :=
    ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35 K A L 𝒢 τ g' hg'
  haveI := hd; haveI := hd'; haveI := hz; haveI := hz'
  have hT2 := analyticPointsT2 K A L 𝒢 τ
  obtain ⟨M, hM, -⟩ :=
    exists_linear_factor hT2 Λ' hΦ' (isImmersiveAtZero_of_discrete 𝒢 τ hΦ') hΦ
  obtain ⟨M', hM', -⟩ :=
    exists_linear_factor hT2 Λ hΦ (isImmersiveAtZero_of_discrete 𝒢 τ hΦ) hΦ'
  have h1 := M.finrank_range_le
  have h2 := M'.finrank_range_le
  rw [LinearMap.range_eq_top.mpr hM, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h1
  rw [LinearMap.range_eq_top.mpr hM', finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h2
  rw [hg', le_antisymm h1 h2]

/-- **`MetrizationOfUniformization`, proved** (no hypotheses): the lattice and line from
`ZInQ.Contrib.Dim.hodgeLatticeTheorem` (in the build), the coefficient maps from metrization's
`jacDetDescends` (proved, unif-dims' kernel-type copy), nonvanishing from metrization2's
`jacDetNondegenerate` (proved); the assembly is metrization's `exists_metrization_of_dim` with the
given uniformizations in place of `AnalyticUniformizationOfDim`. -/
theorem metrizationOfUniformization : MetrizationOfUniformization := by
  intro K _ _ A L _ _ _ 𝒢 g hg hU
  obtain ⟨hfr, hlat⟩ := ZInQ.Contrib.Dim.hodgeLatticeTheorem K A L 𝒢 g hg
  choose Λ Φ hdisc hZ hΦ using hU
  choose c hc using fun τ => ZInQ.Metrization.jacDetDescends K A L 𝒢 τ g (Λ τ) (Φ τ) (hΦ τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    haveI := hdisc τ
    obtain ⟨f, hf⟩ :=
      ZInQ.Metrization2.jacDetNondegenerate K A L 𝒢 τ g hg (Λ τ) (Φ τ) (hZ τ) (hΦ τ)
    apply hf
    rw [← hc τ f, h0]
    rfl
  exact ⟨{ model := 𝒢
           hodge :=
            { lattice := 𝒢.detLattice g
              finrank_eq_one := hfr
              isLattice := hlat
              periods := Λ
              periods_discrete := hdisc
              periods_isZLattice := hZ
              coeff := c
              coeff_ne_zero := hc0 }
           lattice_eq := rfl
           arch := fun τ => ⟨Φ τ, hΦ τ, hc τ⟩ }, rfl⟩

/-- **`NeronMetrizable` from the textbook leaf T35** (proved). -/
theorem neronMetrizable_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    NeronMetrizable :=
  neronMetrizable_of (analyticUniformizationExists_of_t35 hT35) (uniformizationDim_of_t35 hT35)
    metrizationOfUniformization

/-- **height-split's whole `HeightGlue` bundle from the textbook leaf T35** (proved). -/
theorem heightGlue_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) : HeightGlue :=
  ⟨analyticUniformizationExists_of_t35 hT35, analyticUniformizationUnique_of_t35 hT35,
    uniformizationDim_of_t35 hT35, metrizationOfUniformization⟩

/-- The same bundle from the kernel's own Prop `AnalyticUniformizationExists` plus
`UniformizationDim` (T35 is used only for `UniformizationDim`). -/
theorem heightGlue_of_exists_dim (hE : AnalyticUniformizationExists) (hD : UniformizationDim) :
    HeightGlue :=
  ⟨hE, analyticUniformizationUnique_of_exists hE, hD, metrizationOfUniformization⟩

/-- **The six height rows (H-14 to H-19) from height-split's nine published-form leaves and the
textbook leaf T35 alone** (proved): height-split's `heightRows_of` with its glue bundle
`HeightGlue` supplied by `heightGlue_of_t35`. -/
theorem heightRows_of_t35 (l : ZInQ.HeightSplit.HeightLeaves)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.LeafPush2.R18_Javanpeykar ∧ ZInQ.DefFaltings.R19_GaudronRemond ∧
      ZInQ.DefFaltings.R20_FaltingsLemma5 ∧ ZInQ.DefFaltings.R21_Bost ∧
      ZInQ.LeafPush2.R22_Pazuki ∧ ZInQ.DefFaltings.StableHeightFinite :=
  ZInQ.HeightSplit.heightRows_of l (heightGlue_of_t35 hT35)

end ZInQ.HeightGlue

#print axioms ZInQ.HeightGlue.heightRows_of_t35
#print axioms ZInQ.HeightGlue.heightGlue_of_t35
