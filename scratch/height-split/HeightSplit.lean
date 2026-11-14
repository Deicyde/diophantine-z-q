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
inequality is the form Pazuki 2012 Remark 2.3 attributes to it). For an isogeny `φ : A → B` of
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
analytic principal polarization (Riemann/Lefschetz; standard). -/
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

end ZInQ.HeightSplit

/-! ## Axiom checks -/
#print axioms ZInQ.HeightSplit.stableFaltingsHeight_eq_of_semistable
#print axioms ZInQ.HeightSplit.isStableFaltingsHeight_iff
#print axioms ZInQ.HeightSplit.isStableFaltingsHeight_unique
#print axioms ZInQ.HeightSplit.semistableNeronIdentityComponent_of
#print axioms ZInQ.HeightSplit.stableHeightFinite_of
#print axioms ZInQ.HeightSplit.metrizedDimUnique
#print axioms ZInQ.HeightSplit.stableHeightFinite_of'
#print axioms ZInQ.HeightSplit.r21_of_leaves'
#print axioms ZInQ.HeightSplit.r21_of_leaves
#print axioms ZInQ.HeightSplit.grBostBound_of_bost
#print axioms ZInQ.HeightSplit.r18_of_leaves
#print axioms ZInQ.HeightSplit.r20_of_leaves
#print axioms ZInQ.HeightSplit.r20_of_leaves'
#print axioms ZInQ.HeightSplit.r22_of_leaves
#print axioms ZInQ.HeightSplit.r22_of_upper
#print axioms ZInQ.HeightSplit.r19_of_leaves
