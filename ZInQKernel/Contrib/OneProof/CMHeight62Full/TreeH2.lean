import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeH1
import ZInQKernel.Contrib.OneProof.CMHeight62.ShortModel
import ZInQKernel.HDecomp.Faltings.HodgeLattice

/-!
# cmHeight62 (finite place), tree wiring: the generic place and its function field (H2)

The tree part of the special-fibre bridge. For a group model `𝒢` of a dimension-one `E` and any
fraction field `Ω` of the generic stalk `𝒪_{𝒢,ξ}`:

* `Ψ = omegaEquiv 𝒢 Ω : Ω ≅ K(E_L)` is the fraction-field map of `originStalkEquiv`, and
  `omegaAlgebra` / `omegaAlgEquiv` make it an isomorphism of `L`-algebras;
* `P = identityPlace L hdim` is the identity place of `E_L` (degree one, `dim L(nP) = n`, every
  `L(nP)` finite-dimensional);
* the generic stalk matches the valuation ring of `P`: `v_P (Ψ g) ≤ 1 ↔ g ∈ 𝒪_{𝒢,ξ}`
  (`valuation_omegaEquiv_le_one_iff`), and in the form `∃ r s, s ∉ 𝔮, s g = r` when `𝒪_{𝒢,ξ}` is
  presented as a localization `A_𝔮` (`valuation_omegaEquiv_le_one_iff_of_isLocalization`);
* a generator `τ` of the maximal ideal of `𝒪_{𝒢,ξ}` has `ord_P (Ψ τ) = 1`
  (`valuation_omegaEquiv_eq_of_span_eq`);
* `Ψ` is `L`-linear for the structure maps: the germ of `c ∈ 𝓞_L` goes to `c ∈ L`
  (`omegaEquiv_structMap`, from `originStalkEquivAt_structMap`);
* `Ψ` sends the germ `t_G` of `−x/y` to the image of `t_L` (`omegaEquiv_tG`).

The abstract cores (`fracEquiv`, the valuation lemmas, the localization glue and the structure
germ lemmas) use only Mathlib, Tau Ceti places and the Hodge-lattice development of the group
model.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open HDec.CMBranch.CMjBridges (AbVarFunctionField abVarIdentity)
open ZInQ.Contrib.RC53Assist.HodgeLineBinding (originStalkEquiv gen_genericFibreUnit_eq)

/-! ## Abstract core: moving a place along an isomorphism of fraction fields -/

section H2Core

variable {k F S : Type*} [Field k] [Field F] [Algebra k F] [CommRing S] [Algebra S F]
  [IsFractionRing S F]
variable {B Ω : Type*} [CommRing B] [Field Ω] [Algebra B Ω] [IsFractionRing B Ω]

variable (F Ω) in
/-- The isomorphism of fraction fields induced by a ring isomorphism `e : B ≅ S`. -/
def fracEquiv (e : B ≃+* S) : Ω ≃+* F :=
  IsFractionRing.ringEquivOfRingEquiv e

theorem fracEquiv_algebraMap (e : B ≃+* S) (b : B) :
    fracEquiv F Ω e (algebraMap B Ω b) = algebraMap S F (e b) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap e b

variable (k F Ω) in
/-- The `k`-algebra structure on `Ω` carried over from `F` along `fracEquiv`. -/
abbrev fracAlgebra (e : B ≃+* S) : Algebra k Ω :=
  ((fracEquiv F Ω e).symm.toRingHom.comp (algebraMap k F)).toAlgebra

variable (k F Ω) in
/-- `fracEquiv` as an isomorphism of `k`-algebras, for `fracAlgebra`. -/
def fracAlgEquiv (e : B ≃+* S) :
    letI := fracAlgebra k F Ω e
    Ω ≃ₐ[k] F :=
  letI := fracAlgebra k F Ω e
  { fracEquiv F Ω e with
    commutes' := fun r => (fracEquiv F Ω e).apply_symm_apply (algebraMap k F r) }

theorem fracAlgEquiv_apply (e : B ≃+* S) (g : Ω) :
    letI := fracAlgebra k F Ω e
    fracAlgEquiv k F Ω e g = fracEquiv F Ω e g :=
  rfl

/-- **The valuation ring of `P`, pulled back to `Ω`, is the image of `B`.** -/
theorem valuation_fracEquiv_le_one_iff (e : B ≃+* S) (P : TauCeti.Place k F)
    (hP : (algebraMap S F).range = P.integers.toSubring) (g : Ω) :
    P.valuation (fracEquiv F Ω e g) ≤ 1 ↔ g ∈ (algebraMap B Ω).range := by
  rw [← TauCeti.Place.mem_integers_iff]
  constructor
  · intro h
    have h' : fracEquiv F Ω e g ∈ (algebraMap S F).range := by
      rw [hP]
      exact h
    obtain ⟨x, hx⟩ := h'
    refine ⟨e.symm x, (fracEquiv F Ω e).injective ?_⟩
    rw [fracEquiv_algebraMap, RingEquiv.apply_symm_apply, hx]
  · rintro ⟨b, rfl⟩
    have h : algebraMap S F (e b) ∈ (algebraMap S F).range := ⟨e b, rfl⟩
    rw [hP] at h
    rw [fracEquiv_algebraMap]
    exact h

/-- **A generator of the maximal ideal of `B` has order one at `P`.** -/
theorem ord_fracEquiv_eq_one_of_span_eq (e : B ≃+* S) (P : TauCeti.Place k F)
    (hP : (algebraMap S F).range = P.integers.toSubring) [IsLocalRing B] {τ : B}
    (hτ : maximalIdeal B = Ideal.span {τ}) :
    fracEquiv F Ω e (algebraMap B Ω τ) ≠ 0 ∧ P.ord (fracEquiv F Ω e (algebraMap B Ω τ)) = 1 := by
  let ε : B ≃+* P.integers := e.trans (ringEquivIntegersOfRangeEq P hP)
  have hu : ((ε τ : P.integers) : F) = fracEquiv F Ω e (algebraMap B Ω τ) := by
    rw [fracEquiv_algebraMap]
    rfl
  rw [← hu]
  have hmax : maximalIdeal P.integers = Ideal.span {ε τ} := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal ε, hτ, Ideal.map_span, Set.image_singleton]
  have hu0 : ε τ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field P.integers
    rw [hmax, h0, Ideal.span_singleton_eq_bot]
  have hu0' : ((ε τ : P.integers) : F) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hum : ε τ ∈ maximalIdeal P.integers := by
    rw [hmax]
    exact Ideal.mem_span_singleton_self _
  have hpos : 0 < P.ord ((ε τ : P.integers) : F) :=
    (P.mem_maximalIdeal_iff_ord_pos hu0').mp hum
  obtain ⟨π, hπ⟩ := P.exists_isUniformizer
  have hπ1 : P.ord π = 1 := P.isUniformizer_iff_ord_eq_one.mp hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [P.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hπI : π ∈ P.integers := by
    rw [P.mem_integers_iff_ord_nonneg, hπ1]
    exact zero_le_one
  have hπm : (⟨π, hπI⟩ : P.integers) ∈ maximalIdeal P.integers := by
    rw [P.mem_maximalIdeal_iff_ord_pos hπ0]
    rw [hπ1]
    exact zero_lt_one
  rw [hmax, Ideal.mem_span_singleton'] at hπm
  obtain ⟨a, ha⟩ := hπm
  have ha' : (a : F) * ((ε τ : P.integers) : F) = π := congrArg Subtype.val ha
  have ha0 : (a : F) ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha'
    exact hπ0 ha'.symm
  have hord := P.ord_mul ha0 hu0'
  rw [ha', hπ1] at hord
  have hanonneg : 0 ≤ P.ord (a : F) := P.mem_integers_iff_ord_nonneg.mp a.2
  exact ⟨hu0', by omega⟩

/-- The same, as a value of the valuation: `v_P (Ψ τ) = exp (-1)`. -/
theorem valuation_fracEquiv_eq_of_span_eq (e : B ≃+* S) (P : TauCeti.Place k F)
    (hP : (algebraMap S F).range = P.integers.toSubring) [IsLocalRing B] {τ : B}
    (hτ : maximalIdeal B = Ideal.span {τ}) :
    P.valuation (fracEquiv F Ω e (algebraMap B Ω τ)) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨h0, h1⟩ := ord_fracEquiv_eq_one_of_span_eq (F := F) (Ω := Ω) e P hP hτ
  exact (P.ord_eq_iff_valuation_eq_exp_neg h0).mp h1

end H2Core

/-! ## Local glue: the image of a localization at a prime in a fraction field -/

section LocalizationGlue

variable {A C Ω : Type*} [CommRing A] [CommRing C] [Field Ω] [Algebra A C] [Algebra A Ω]
  [Algebra C Ω] [IsScalarTower A C Ω]

/-- For `C = A_𝔮` mapping to a field `Ω` compatibly with `A`, the image of `C` is the set of
`g` with `s g = r` for some `r, s ∈ A`, `s ∉ 𝔮`. This turns the generic-stalk form of the
valuation ring of `P` into the form used by the pole-bound nodes. -/
theorem mem_range_algebraMap_iff_of_isLocalization (𝔮 : Ideal A) [𝔮.IsPrime]
    [IsLocalization.AtPrime C 𝔮] (g : Ω) :
    g ∈ (algebraMap C Ω).range ↔
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨⟨r, s⟩, hc⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl c
    refine ⟨r, s, s.2, ?_⟩
    have h := IsLocalization.mk'_spec C r s
    rw [IsScalarTower.algebraMap_apply A C Ω, IsScalarTower.algebraMap_apply A C Ω, ← h,
      ← hc, map_mul, mul_comm]
  · rintro ⟨r, s, hs, h⟩
    refine ⟨IsLocalization.mk' C r (⟨s, hs⟩ : 𝔮.primeCompl), ?_⟩
    have hu : IsUnit (algebraMap A C s) :=
      IsLocalization.map_units C (⟨s, hs⟩ : 𝔮.primeCompl)
    have hu' : IsUnit (algebraMap A Ω s) := by
      rw [IsScalarTower.algebraMap_apply A C Ω]
      exact hu.map _
    have hspec := IsLocalization.mk'_spec C r (⟨s, hs⟩ : 𝔮.primeCompl)
    apply hu'.mul_left_cancel
    rw [h, mul_comm, IsScalarTower.algebraMap_apply A C Ω,
      IsScalarTower.algebraMap_apply A C Ω r, ← map_mul, hspec]

end LocalizationGlue

/-! ## The structure germ of a scheme over an affine base -/

section StructGerm

/-- The structure map `R → 𝒪_{X,x}` of a scheme over `Spec R`, at a point `x`. -/
def structGermHom {R : CommRingCat} {X : Scheme} (g : X ⟶ Spec R) (x : X) :
    R ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial

theorem structGermHom_stalkMap {R : CommRingCat} {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec R)
    (x : X) : structGermHom g (f x) ≫ f.stalkMap x = structGermHom (f ≫ g) x := by
  simp only [structGermHom, Category.assoc]
  rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial, Scheme.Hom.comp_appTop, Category.assoc]
  rfl

theorem structGermHom_stalkSpecializes {R : CommRingCat} {X : Scheme} (g : X ⟶ Spec R)
    {x y : X} (h : x ⤳ y) :
    structGermHom g y ≫ X.presheaf.stalkSpecializes h = structGermHom g x := by
  simp only [structGermHom, Category.assoc]
  exact congrArg (fun k => (Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ k)
    (TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := ⊤) (y := y) trivial h)

theorem structGermHom_comp_specMap {R S : CommRingCat} {X : Scheme} (g : X ⟶ Spec S)
    (φ : R ⟶ S) (x : X) : structGermHom (g ≫ Spec.map φ) x = φ ≫ structGermHom g x := by
  simp only [structGermHom, Scheme.Hom.comp_appTop, ← Category.assoc,
    Scheme.ΓSpecIso_inv_naturality]

end StructGerm

/-! ## `originStalkEquiv` with its target point as a parameter -/

section OriginAt

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- `𝒪_{𝒢,ξ} ≅ 𝒪_{𝒢_L,ξ_L}`: the first half of `originStalkEquiv`. -/
def originIso₁ (G : GroupModel E L) :
    G.genStalk ≅ (genericFibre L G.G).left.presheaf.stalk (genericFibreUnit G) :=
  haveI hp : IsIso ((pullback.fst G.G.hom (toGeneric L)).stalkMap (genericFibreUnit G)) :=
    genericFibreStalkIso L G.G _
  G.G.left.presheaf.stalkCongr (Inseparable.of_eq (fst_genericFibreUnit G).symm) ≪≫
    @asIso _ _ _ _ _ hp

/-- `𝒪_{A_L,p} ≅ 𝒪_{𝒢_L,ξ_L}` for `p` the image of `ξ_L` under `𝒢.gen`: the second half. -/
def originIso₂ (G : GroupModel E L) (p : (E.baseChange L).X.left)
    (hp : G.gen.hom.left (genericFibreUnit G) = p) :
    (E.baseChange L).X.left.presheaf.stalk p ≅
      (genericFibre L G.G).left.presheaf.stalk (genericFibreUnit G) :=
  haveI hφ : IsOpenImmersion ((Over.forget _).mapIso G.gen).hom := inferInstance
  haveI hφs : IsIso (((Over.forget _).mapIso G.gen).hom.stalkMap (genericFibreUnit G)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hφ).2 _
  (E.baseChange L).X.left.presheaf.stalkCongr (Inseparable.of_eq hp.symm) ≪≫
    @asIso _ _ _ _ _ hφs

/-- The body of `originStalkEquiv`, for any name `p` of the image of `ξ_L`. -/
def originStalkEquivAt (G : GroupModel E L) (p : (E.baseChange L).X.left)
    (hp : G.gen.hom.left (genericFibreUnit G) = p) :
    G.genStalk ≃+* (E.baseChange L).X.left.presheaf.stalk p :=
  (originIso₁ G ≪≫ (originIso₂ G p hp).symm).commRingCatIsoToRingEquiv

theorem structGermHom_originIso₁ (G : GroupModel E L) :
    structGermHom G.G.hom G.genericUnit ≫ (originIso₁ G).hom =
      CommRingCat.ofHom (algebraMap (𝓞 L) L) ≫
        structGermHom (genericFibre L G.G).hom (genericFibreUnit G) := by
  have h1 := structGermHom_stalkSpecializes G.G.hom
    (Inseparable.of_eq (fst_genericFibreUnit G)).specializes
  have h2 := structGermHom_stalkMap (pullback.fst G.G.hom (toGeneric L)) G.G.hom
    (genericFibreUnit G)
  have h3 := structGermHom_comp_specMap (genericFibre L G.G).hom
    (CommRingCat.ofHom (algebraMap (𝓞 L) L)) (genericFibreUnit G)
  have hc : pullback.fst G.G.hom (toGeneric L) ≫ G.G.hom =
      (genericFibre L G.G).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) :=
    pullback.condition
  simp only [originIso₁, Iso.trans_hom, TopCat.Presheaf.stalkCongr_hom]
  change (structGermHom G.G.hom G.genericUnit ≫ G.G.left.presheaf.stalkSpecializes _) ≫
    (pullback.fst G.G.hom (toGeneric L)).stalkMap (genericFibreUnit G) = _
  refine (congrArg (· ≫ (pullback.fst G.G.hom (toGeneric L)).stalkMap (genericFibreUnit G))
    h1).trans ?_
  refine h2.trans ?_
  refine (congrArg (fun f => structGermHom f (genericFibreUnit G)) hc).trans ?_
  exact h3

theorem structGermHom_originIso₂ (G : GroupModel E L) (p : (E.baseChange L).X.left)
    (hp : G.gen.hom.left (genericFibreUnit G) = p) :
    structGermHom (E.baseChange L).X.hom p ≫ (originIso₂ G p hp).hom =
      structGermHom (genericFibre L G.G).hom (genericFibreUnit G) := by
  subst hp
  have h1 := structGermHom_stalkSpecializes (E.baseChange L).X.hom
    (Inseparable.of_eq (rfl : G.gen.hom.left (genericFibreUnit G) =
      G.gen.hom.left (genericFibreUnit G)).symm).specializes
  have h2 := structGermHom_stalkMap G.gen.hom.left (E.baseChange L).X.hom (genericFibreUnit G)
  have hw : G.gen.hom.left ≫ (E.baseChange L).X.hom = (genericFibre L G.G).hom :=
    Over.w G.gen.hom
  simp only [originIso₂, Iso.trans_hom, TopCat.Presheaf.stalkCongr_hom]
  change (structGermHom (E.baseChange L).X.hom _ ≫ _) ≫
    G.gen.hom.left.stalkMap (genericFibreUnit G) = _
  refine (congrArg (· ≫ G.gen.hom.left.stalkMap (genericFibreUnit G)) h1).trans ?_
  refine h2.trans ?_
  exact congrArg (fun f => structGermHom f (genericFibreUnit G)) hw

/-- **`originStalkEquiv` respects the structure maps**: the germ of `c ∈ 𝓞_L` at `ξ` goes to the
germ at `p` of its image in `L`. -/
theorem originStalkEquivAt_structMap (G : GroupModel E L) (p : (E.baseChange L).X.left)
    (hp : G.gen.hom.left (genericFibreUnit G) = p) (c : 𝓞 L) :
    originStalkEquivAt G p hp (G.structMap c) =
      (structGermHom (E.baseChange L).X.hom p).hom (algebraMap (𝓞 L) L c) := by
  have h := congrArg (fun f => f ≫ (originIso₂ G p hp).inv)
    ((structGermHom_originIso₁ G).trans
      (congrArg (fun f => CommRingCat.ofHom (algebraMap (𝓞 L) L) ≫ f)
        (structGermHom_originIso₂ G p hp).symm))
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  have h' := congrArg (fun f => f.hom c) h
  simp only at h'
  exact h'

end OriginAt

/-! ## The tree instance: `Ψ`, `P`, the generic stalk and the parameter -/

section Tree

attribute [local instance] HDec.CMBranch.CMjBridges.abVar_isIntegral
  HDec.CMBranch.CMjBridges.abVarFunctionFieldAlgebra

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- `originStalkEquiv` is `originStalkEquivAt` at the identity of `E_L`. -/
theorem originEquiv_eq_originStalkEquivAt (𝒢 : GroupModel E L) (x : 𝒢.genStalk) :
    originEquiv 𝒢 x =
      originStalkEquivAt 𝒢 (abVarIdentity (E.baseChange L)) (gen_genericFibreUnit_eq 𝒢) x :=
  rfl

/-- **`Ψ : Ω ≅ K(E_L)`**, the fraction-field map of `originStalkEquiv`, for any fraction field
`Ω` of `𝒪_{𝒢,ξ}`. -/
def omegaEquiv (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω] [Algebra 𝒢.genStalk Ω]
    [IsFractionRing 𝒢.genStalk Ω] : Ω ≃+* AbVarFunctionField (E.baseChange L) :=
  fracEquiv (AbVarFunctionField (E.baseChange L)) Ω (originEquiv 𝒢)

/-- The `L`-algebra structure on `Ω` carried from `K(E_L)` along `Ψ`. -/
abbrev omegaAlgebra (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω] [Algebra 𝒢.genStalk Ω]
    [IsFractionRing 𝒢.genStalk Ω] : Algebra L Ω :=
  fracAlgebra L (AbVarFunctionField (E.baseChange L)) Ω (originEquiv 𝒢)

/-- `Ψ` as an isomorphism of `L`-algebras. -/
def omegaAlgEquiv (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω] [Algebra 𝒢.genStalk Ω]
    [IsFractionRing 𝒢.genStalk Ω] :
    letI := omegaAlgebra 𝒢 Ω
    Ω ≃ₐ[L] AbVarFunctionField (E.baseChange L) :=
  fracAlgEquiv L (AbVarFunctionField (E.baseChange L)) Ω (originEquiv 𝒢)

theorem omegaAlgEquiv_apply (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω]
    [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω] (g : Ω) :
    letI := omegaAlgebra 𝒢 Ω
    omegaAlgEquiv 𝒢 Ω g = omegaEquiv 𝒢 Ω g :=
  rfl

/-- `Ψ` restricted to `𝒪_{𝒢,ξ}` is `originStalkEquiv` followed by `𝒪_{E_L,0} → K(E_L)`. -/
theorem omegaEquiv_algebraMap (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω]
    [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω] (x : 𝒢.genStalk) :
    omegaEquiv 𝒢 Ω (algebraMap 𝒢.genStalk Ω x) =
      algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
        (AbVarFunctionField (E.baseChange L)) (originEquiv 𝒢 x) :=
  fracEquiv_algebraMap (originEquiv 𝒢) x

/-- **The generic stalk matches the valuation ring of `P`.** -/
theorem valuation_omegaEquiv_le_one_iff (hdim : E.dim = 1) (𝒢 : GroupModel E L) (Ω : Type*)
    [Field Ω] [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω] (g : Ω) :
    (identityPlace L hdim).valuation (omegaEquiv 𝒢 Ω g) ≤ 1 ↔
      g ∈ (algebraMap 𝒢.genStalk Ω).range :=
  valuation_fracEquiv_le_one_iff (originEquiv 𝒢) (identityPlace L hdim)
    (identityPlace_spec hdim).2.1 g

/-- The same, for `𝒪_{𝒢,ξ}` presented as a localization `A_𝔮` compatibly with `Ω`. -/
theorem valuation_omegaEquiv_le_one_iff_of_isLocalization (hdim : E.dim = 1)
    (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω] [Algebra 𝒢.genStalk Ω]
    [IsFractionRing 𝒢.genStalk Ω] {A : Type*} [CommRing A] [Algebra A 𝒢.genStalk]
    [Algebra A Ω] [IsScalarTower A 𝒢.genStalk Ω] (𝔮 : Ideal A) [𝔮.IsPrime]
    [IsLocalization.AtPrime 𝒢.genStalk 𝔮] (g : Ω) :
    (identityPlace L hdim).valuation (omegaEquiv 𝒢 Ω g) ≤ 1 ↔
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r :=
  (valuation_omegaEquiv_le_one_iff hdim 𝒢 Ω g).trans
    (mem_range_algebraMap_iff_of_isLocalization 𝔮 g)

/-- **A generator of the maximal ideal of `𝒪_{𝒢,ξ}` has order one at `P`.** -/
theorem valuation_omegaEquiv_eq_of_span_eq (hdim : E.dim = 1) (𝒢 : GroupModel E L)
    (Ω : Type*) [Field Ω] [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω]
    {τ : 𝒢.genStalk} (hτ : maximalIdeal 𝒢.genStalk = Ideal.span {τ}) :
    (identityPlace L hdim).valuation (omegaEquiv 𝒢 Ω (algebraMap 𝒢.genStalk Ω τ)) =
      WithZero.exp (-1 : ℤ) :=
  valuation_fracEquiv_eq_of_span_eq (originEquiv 𝒢) (identityPlace L hdim)
    (identityPlace_spec hdim).2.1 hτ

theorem ord_omegaEquiv_eq_one_of_span_eq (hdim : E.dim = 1) (𝒢 : GroupModel E L)
    (Ω : Type*) [Field Ω] [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω]
    {τ : 𝒢.genStalk} (hτ : maximalIdeal 𝒢.genStalk = Ideal.span {τ}) :
    (identityPlace L hdim).ord (omegaEquiv 𝒢 Ω (algebraMap 𝒢.genStalk Ω τ)) = 1 :=
  (ord_fracEquiv_eq_one_of_span_eq (originEquiv 𝒢) (identityPlace L hdim)
    (identityPlace_spec hdim).2.1 hτ).2

/-- Every `L(nP)` is finite-dimensional. -/
theorem finiteDimensional_poleSpace_identityPlace (hdim : E.dim = 1) (n : ℕ) :
    FiniteDimensional L (poleSpace (identityPlace L hdim) n) :=
  TauCeti.finiteDimensional_riemannRochSpace
    (HDec.CMBranch.CMjBridges.abVar_isFunctionField (E.baseChange L)
      (dim_baseChange_eq_one hdim)) _

/-- **`Ψ` is `L`-linear for the structure maps**: the germ at `ξ` of `c ∈ 𝓞_L` goes to `c`. -/
theorem omegaEquiv_structMap (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω]
    [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω] (c : 𝓞 L) :
    omegaEquiv 𝒢 Ω (algebraMap 𝒢.genStalk Ω (𝒢.structMap c)) =
      algebraMap L (AbVarFunctionField (E.baseChange L)) (algebraMap (𝓞 L) L c) := by
  rw [omegaEquiv_algebraMap, originEquiv_eq_originStalkEquivAt, originStalkEquivAt_structMap]
  open P2MW.S_AlgebraicCurve_exists_place_range_stalk_eq in
  exact (AlgebraicCurve.baseToFunctionField_apply_eq_algebraMap_stalk (E.baseChange L).X.hom
    (abVarIdentity (E.baseChange L)) (algebraMap (𝓞 L) L c)).symm

/-- The same for `omegaAlgebra`: `𝓞_L → 𝒪_{𝒢,ξ} → Ω` is `𝓞_L → L → Ω`. -/
theorem algebraMap_structMap_omega (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω]
    [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω] (c : 𝓞 L) :
    letI := omegaAlgebra 𝒢 Ω
    algebraMap 𝒢.genStalk Ω (𝒢.structMap c) = algebraMap L Ω (algebraMap (𝓞 L) L c) := by
  letI := omegaAlgebra 𝒢 Ω
  apply (omegaEquiv 𝒢 Ω).injective
  rw [omegaEquiv_structMap]
  exact ((omegaEquiv 𝒢 Ω).apply_symm_apply _).symm

/-- `Ψ` sends the germ `t_G` of `−x/y` at `ξ` to the image of `t_L` in `K(E_L)`. -/
theorem omegaEquiv_tG (D : ZInQ.Contrib.CMHeight62.ShortData E) (𝒢 : GroupModel E L)
    (Ω : Type*) [Field Ω] [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω] :
    omegaEquiv 𝒢 Ω (algebraMap 𝒢.genStalk Ω (D.tG 𝒢 : 𝒢.genStalk)) =
      algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
        (AbVarFunctionField (E.baseChange L)) (D.tL (L := L)) := by
  rw [omegaEquiv_algebraMap]
  exact congrArg (algebraMap _ _) ((originStalkEquiv 𝒢).apply_symm_apply (D.tL (L := L)))

/-- **H2, bundled.** For any fraction field `Ω` of `𝒪_{𝒢,ξ}`, with `Ψ = omegaAlgEquiv 𝒢 Ω` and
`P = identityPlace L hdim`: `P` has degree one and the pole-space ladder, `Ψ` restricts to
`originStalkEquiv` on `𝒪_{𝒢,ξ}` and respects the structure maps, the valuation ring of `P`
pulls back to `𝒪_{𝒢,ξ}`, and a generator of `𝔪_ξ` has `v_P = exp (-1)`. -/
theorem treeH2 (hdim : E.dim = 1) (𝒢 : GroupModel E L) (Ω : Type*) [Field Ω]
    [Algebra 𝒢.genStalk Ω] [IsFractionRing 𝒢.genStalk Ω] :
    letI := omegaAlgebra 𝒢 Ω
    (identityPlace L hdim).degree = 1 ∧
      (∀ n : ℕ, 1 ≤ n →
        TauCeti.Divisor.dim (Finsupp.single (identityPlace L hdim) (n : ℤ) :
          TauCeti.Divisor L (AbVarFunctionField (E.baseChange L))) = n) ∧
      (∀ n : ℕ, FiniteDimensional L (poleSpace (identityPlace L hdim) n)) ∧
      (∀ x : 𝒢.genStalk, omegaAlgEquiv 𝒢 Ω (algebraMap 𝒢.genStalk Ω x) =
        algebraMap ((E.baseChange L).X.left.presheaf.stalk (abVarIdentity (E.baseChange L)))
          (AbVarFunctionField (E.baseChange L)) (originStalkEquiv 𝒢 x)) ∧
      (∀ g : Ω, (identityPlace L hdim).valuation (omegaAlgEquiv 𝒢 Ω g) ≤ 1 ↔
        g ∈ (algebraMap 𝒢.genStalk Ω).range) ∧
      (∀ τ : 𝒢.genStalk, maximalIdeal 𝒢.genStalk = Ideal.span {τ} →
        (identityPlace L hdim).valuation (omegaAlgEquiv 𝒢 Ω (algebraMap 𝒢.genStalk Ω τ)) =
          WithZero.exp (-1 : ℤ)) ∧
      (∀ c : 𝓞 L, algebraMap 𝒢.genStalk Ω (𝒢.structMap c) =
        algebraMap L Ω (algebraMap (𝓞 L) L c)) :=
  ⟨(identityPlace_spec hdim).1, (identityPlace_spec hdim).2.2,
    finiteDimensional_poleSpace_identityPlace hdim, omegaEquiv_algebraMap 𝒢 Ω,
    valuation_omegaEquiv_le_one_iff hdim 𝒢 Ω,
    fun _ hτ => valuation_omegaEquiv_eq_of_span_eq hdim 𝒢 Ω hτ,
    algebraMap_structMap_omega 𝒢 Ω⟩

end Tree

end ZInQ.Contrib.CMHeight62Full
