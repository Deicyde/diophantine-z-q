import ZInQKernel.Contrib.OneProof.HeightModelM.GR1Height

/-!
# The two height reading steps of the Gaudron–Rémond rows

The adversarial readings of the rows `GaudronRemondSec9LowerGR1Weak` and `GaudronRemondThm14GR1`
(the item-M reading record, §3 and §6) left two steps of the reading of the height predicate
`IsGR1StableHeightOriginal` as arguments, not Lean theorems. This file proves both.

**(R1) Commutativity of the model.** `GroupModel` does not state that the group scheme `𝒜` is
commutative. `groupModel_isCommMonObj`: every `𝒜 : GroupModel A L` is commutative, in the form the
tree uses for commutative group objects (`IsCommMonObj 𝒜.G`, i.e. `β ≫ μ = μ` for the braiding of
the cartesian monoidal structure of `Over (Spec 𝓞_L)`). No hypothesis is added: commutativity of
`A_L` is the instance `IsCommMonObj` that `PkgI3.AbVar` carries (proved from Mathlib's
`isCommMonObj_of_isProper_of_geometricallyIntegral`). The proof is the reading's argument: `μ` and
`β ≫ μ` agree after base change to the generic fibre, because `𝒜.gen` is a monoid isomorphism onto
the commutative `A_L` and base change is a braided monoidal functor; `𝒜 ×_S 𝒜` is flat over
`S = Spec 𝓞_L` (smooth), so its generic fibre is scheme-theoretically dominant, and `𝒜` is
separated, so base change to the generic fibre is injective on morphisms `𝒜 ×_S 𝒜 → 𝒜`
(`ZInQ.Contrib.NeronC.pullback_map_injective`). `isGR1StableHeightOriginal_iff_comm`: adding
commutativity of the model to the height predicate changes nothing.

**(R2) Stalks and global sections.** The lattice of the height is built from
`Conormal.printedOmegaAt 𝒢 s`, the image in the generic stalk
`V = 𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]` of the stalk `(e*Ω¹)_s = 𝒪_{S,s} ⊗ Ω[𝒪_{𝒢,e(s)}/𝓞_L]`, as
`printedOmega = θ⁻¹(⋂_s printedOmegaAt s)`, and `printedDetLattice 𝒢 g`, the span of the wedges
of `g` elements of `printedOmega`. The reading identified this intersection with the
`𝓞_L`-module of global sections of `e*Ω¹`, and its top wedge with that of `ε*Ω^g`, by the standard
fact for a quasi-coherent torsion-free sheaf `F = N~` on `Spec 𝓞_L`: inside the generic stalk, the
stalk `F_s` is the localization `N_s = {x | u • x ∈ N for some u ∉ s}` (`locIn`), and
`N = ⋂_s N_s`. The tree has a sheaf of relative differentials
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`) and Mathlib has the pullback
`Scheme.Modules.pullback`, so `e*Ω¹` can be written down; but nothing in the tree computes the
stalks of that pullback as the modules `𝒪_{S,s} ⊗ Ω[𝒪_{𝒢,e(s)}/𝓞_L]` from which `printedOmegaAt`
is built, so its global sections cannot be compared with `printedOmega` directly. The step from the
stalks to the global sections is proved here in module form:

* `eq_iInf_locIn`: an `R`-submodule is the intersection of its localizations at the maximal ideals
  (any commutative ring `R`, any module);
* `locIn_iInf_printedOmegaAt`: the localization at every point `s` of `Spec 𝓞_L` of
  `⋂_t printedOmegaAt t` is `printedOmegaAt s`, i.e. the stalk lattices are the stalks of one
  quasi-coherent sheaf (proved from the germs of `𝒢`, an affine open around each `e(t)`, and the
  discrete valuation rings `𝓞_{L,t}`);
* `printedOmega_eq_globalSections`: `θ(printedOmega)` is the unique `𝓞_L`-submodule of the generic
  stalk whose localization at every point `s` is the stalk `(e*Ω¹)_s`, so it is the module of global
  sections of the quasi-coherent sheaf with these stalks, i.e. `Γ(S, e*Ω¹)`; `printedOmega_unique`
  is the same statement inside `ω_{A_L} = 𝔪_ξ/𝔪_ξ²`;
* `printedDetLattice_eq_globalSections`: `printedDetLattice 𝒢 g` is the unique `𝓞_L`-submodule of
  the Hodge line whose localization at every point `s` is the stalk
  `(ε*Ω^g)_s = 𝒪_{S,s} · ⋀^g (e*Ω¹)_s`, i.e. `Γ(S, ε*Ω^g)`.

The identification of the stalk `(e*Ω¹)_s` with `𝒪_{S,s} ⊗ Ω[𝒪_{𝒢,e(s)}/𝓞_L]` is the reading at the
stalks that `Conormal` takes as the definition of `printedOmegaAt`; it is not part of this step.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonoidalCategory CartesianMonoidalCategory
  MonObj
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightDict.Conormal ZInQ.R3Residual KaehlerDifferential
open scoped NumberField TensorProduct

set_option warn.classDefReducibility false

namespace ZInQ.HeightModelM.ReadingSteps

/-! ## (R1) The group scheme of a group model is commutative -/

section R1

/-- A monoid object isomorphic, by a monoid isomorphism, to a commutative one is commutative.
(Used for reading step (R1).) -/
theorem isCommMonObj_of_monIso {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {X Y : C} [MonObj X] [MonObj Y] [IsCommMonObj Y] (e : X ≅ Y) [IsMonHom e.hom] :
    IsCommMonObj X := by
  have h : μ[X] = (e.hom ⊗ₘ e.hom) ≫ μ[Y] ≫ e.inv := by
    rw [← IsMonHom.mul_hom_assoc, Iso.hom_inv_id, Category.comp_id]
  constructor
  rw [h, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- **Reading step (R1), generic fibre.** The generic fibre `𝒜_L` of a group model, with the group
structure transported by base change, is commutative: `𝒜.gen` is a monoid isomorphism onto `A_L`,
which is commutative (`PkgI3.AbVar` carries `IsCommMonObj`). -/
theorem genericFibre_isCommMonObj (𝒜 : GroupModel A L) :
    letI : GrpObj (genericFibre L 𝒜.G) := Functor.grpObjObj
    IsCommMonObj (genericFibre L 𝒜.G) := by
  let _ : GrpObj (genericFibre L 𝒜.G) := Functor.grpObjObj
  have : IsMonHom 𝒜.gen.hom := 𝒜.gen_hom
  exact isCommMonObj_of_monIso 𝒜.gen

/-- **Reading step (R1), closed.** Every group model `𝒜 : GroupModel A L` is commutative:
`β ≫ μ = μ` on `𝒜 ×_{𝓞_L} 𝒜` (`IsCommMonObj 𝒜.G`). The two multiplications agree on the generic
fibre (`genericFibre_isCommMonObj`, through the braided monoidal functor `Over.pullback`); the
generic fibre of the flat `𝒜 ×_{𝓞_L} 𝒜` is scheme-theoretically dominant and `𝒜` is separated, so
they agree. Commutativity of `A` is not a hypothesis: it is the instance `IsCommMonObj` of
`PkgI3.AbVar` (Mathlib's `isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
theorem groupModel_isCommMonObj (𝒜 : GroupModel A L) : IsCommMonObj 𝒜.G := by
  have hc := genericFibre_isCommMonObj 𝒜
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))) :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _
      (FaithfulSMul.algebraMap_injective (𝓞 L) L)
  have key : (β_ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj 𝒜.G)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj 𝒜.G)).hom ≫
      Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))))
        𝒜.G 𝒜.G ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map μ[𝒜.G] =
      Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))))
        𝒜.G 𝒜.G ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map μ[𝒜.G] :=
    hc.mul_comm
  constructor
  apply ZInQ.Contrib.NeronC.pullback_map_injective
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))) (𝒜.G ⊗ 𝒜.G) 𝒜.G
  show (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map
      ((β_ 𝒜.G 𝒜.G).hom ≫ μ) =
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map μ
  rw [Functor.map_comp, Functor.map_braiding_assoc, key, Functor.Monoidal.δ_μ_assoc]

/-- **Reading step (R1), multiplication form**: `β ≫ μ = μ` on `𝒜 ×_{𝓞_L} 𝒜`. -/
theorem groupModel_mul_comm (𝒜 : GroupModel A L) : (β_ 𝒜.G 𝒜.G).hom ≫ μ[𝒜.G] = μ[𝒜.G] :=
  (groupModel_isCommMonObj 𝒜).mul_comm

/-- **Reading step (R1), effect on the height predicate.** Asking in addition that the semi-abelian
model be commutative does not change `IsGR1StableHeightOriginal`. -/
theorem isGR1StableHeightOriginal_iff_comm {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) :
    IsGR1StableHeightOriginal A x ↔
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (𝒜 : GroupModel A K')
        (g : ℕ), IsCommMonObj 𝒜.G ∧ IsSemiAbelianModel 𝒜 ∧ A.dim = (g : WithBot ℕ∞) ∧
        ∃ eta ∈ printedDetLattice 𝒜 g, eta ≠ 0 ∧ secIndex (printedDetLattice 𝒜 g) eta ≠ 0 ∧
          ∃ r : (K' →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒜 τ eta (r τ)) ∧
            x = (Real.log (secIndex (printedDetLattice 𝒜 g) eta) -
              (1 / 2) * ∑ τ : K' →+* ℂ, Real.log (r τ)) / Module.finrank ℚ K' := by
  constructor
  · rintro ⟨K', i1, i2, i3, 𝒜, g, h⟩
    exact ⟨K', i1, i2, i3, 𝒜, g, groupModel_isCommMonObj 𝒜, h⟩
  · rintro ⟨K', i1, i2, i3, 𝒜, g, -, h⟩
    exact ⟨K', i1, i2, i3, 𝒜, g, h⟩

end R1

/-! ## (R2) Stalks and global sections -/

section Localization

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The localization `S⁻¹N` of a submodule `N` computed inside `M`: the `x` with `u • x ∈ N` for
some `u ∈ S`. For `M` a vector space over the fraction field of a domain `R`, this is the image of
`S⁻¹R ⊗_R N` in `M`; for `S = R ∖ s` it is the stalk at `s` of the quasi-coherent sheaf `N~`.
(Used for reading step (R2).) -/
def locIn (N : Submodule R M) (S : Submonoid R) : Submodule R M where
  carrier := {x | ∃ u ∈ S, u • x ∈ N}
  add_mem' := by
    rintro x y ⟨u, hu, hx⟩ ⟨v, hv, hy⟩
    refine ⟨u * v, S.mul_mem hu hv, ?_⟩
    have h : (u * v) • (x + y) = v • (u • x) + u • (v • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm u v x]
    rw [h]
    exact N.add_mem (N.smul_mem v hx) (N.smul_mem u hy)
  zero_mem' := ⟨1, S.one_mem, by rw [smul_zero]; exact N.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨u, hu, hx⟩
    exact ⟨u, hu, by rw [smul_comm]; exact N.smul_mem c hx⟩

/-- Membership in the localization. (Used for reading step (R2).) -/
theorem mem_locIn {N : Submodule R M} {S : Submonoid R} {x : M} :
    x ∈ locIn N S ↔ ∃ u ∈ S, u • x ∈ N := Iff.rfl

/-- A submodule lies in its localization. (Used for reading step (R2).) -/
theorem le_locIn (N : Submodule R M) (S : Submonoid R) : N ≤ locIn N S :=
  fun _ hx => ⟨1, S.one_mem, by rwa [one_smul]⟩

/-- Localization is monotone. (Used for reading step (R2).) -/
theorem locIn_mono {N N' : Submodule R M} (h : N ≤ N') (S : Submonoid R) :
    locIn N S ≤ locIn N' S :=
  fun _ ⟨u, hu, hx⟩ => ⟨u, hu, h hx⟩

/-- Localization is idempotent. (Used for reading step (R2).) -/
theorem locIn_locIn (N : Submodule R M) (S : Submonoid R) : locIn (locIn N S) S = locIn N S := by
  apply le_antisymm
  · rintro x ⟨u, hu, v, hv, hx⟩
    exact ⟨v * u, S.mul_mem hv hu, by rwa [mul_smul]⟩
  · exact le_locIn _ S

/-- **Reading step (R2), the algebra.** An element that lies in the localization of `N` at every
maximal ideal lies in `N`. -/
theorem mem_of_forall_mem_locIn {N : Submodule R M} {x : M}
    (h : ∀ s : PrimeSpectrum R, s.asIdeal.IsMaximal → x ∈ locIn N s.asIdeal.primeCompl) :
    x ∈ N := by
  let J : Ideal R := N.comap (LinearMap.toSpanSingleton R M x)
  have hJ : J = ⊤ := by
    by_contra hJ
    obtain ⟨𝔪, h𝔪, hJ𝔪⟩ := Ideal.exists_le_maximal J hJ
    obtain ⟨u, hu, hux⟩ := h ⟨𝔪, h𝔪.isPrime⟩ h𝔪
    exact hu (hJ𝔪 (by simpa [J] using hux))
  have h1 : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
  simpa [J] using h1

/-- **Reading step (R2), the algebra**: a submodule is the intersection of its localizations at the
points of `Spec R` (and already at the maximal ideals, `mem_of_forall_mem_locIn`). -/
theorem eq_iInf_locIn (N : Submodule R M) :
    N = ⨅ s : PrimeSpectrum R, locIn N s.asIdeal.primeCompl := by
  apply le_antisymm
  · exact le_iInf fun s => le_locIn N _
  · intro x hx
    exact mem_of_forall_mem_locIn fun s _ => (Submodule.mem_iInf _).mp hx s

end Localization

section Dedekind

variable {L : Type} [Field L] [NumberField L]

/-- In the discrete valuation ring `𝓞_{L,t}`: if `f ∈ t` and `c ≠ 0`, a power of `f` is a multiple
of `c` up to a unit at `t`. (Used for reading step (R2).) -/
theorem exists_mul_pow_eq_mul {t : Ideal (𝓞 L)} [t.IsPrime] (ht : t ≠ ⊥) {f c : 𝓞 L}
    (hf : f ∈ t) (hc : c ≠ 0) : ∃ (n : ℕ) (u d : 𝓞 L), u ∉ t ∧ u * f ^ n = c * d := by
  have : IsDomain (Localization.AtPrime t) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors t)
  have : IsDiscreteValuationRing (Localization.AtPrime t) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) ht _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime t)
  have hinj : Function.Injective (algebraMap (𝓞 L) (Localization.AtPrime t)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors t)
  have hc' : Ideal.span {algebraMap (𝓞 L) (Localization.AtPrime t) c} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hc (hinj (by rw [h, map_zero]))
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hc' hϖ
  have hfm : algebraMap (𝓞 L) (Localization.AtPrime t) f ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime t) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ t f).mpr hf
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton] at hfm
  have hmem : algebraMap (𝓞 L) (Localization.AtPrime t) (f ^ n) ∈
      Ideal.span {algebraMap (𝓞 L) (Localization.AtPrime t) c} := by
    rw [hn, Ideal.mem_span_singleton, map_pow]
    exact pow_dvd_pow_of_dvd hfm n
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨du, hdu⟩ := IsLocalization.surj t.primeCompl z
  refine ⟨n, du.2, du.1, du.2.2, hinj ?_⟩
  rw [map_mul, map_mul, ← hz, ← _root_.mul_assoc,
    _root_.mul_comm (algebraMap _ _ (du.2 : 𝓞 L)) z, hdu, _root_.mul_comm]

/-- A nonzero element of `𝓞_L` lies in finitely many primes. (Used for reading step (R2).) -/
theorem finite_setOf_mem_asIdeal {f : 𝓞 L} (hf : f ≠ 0) :
    {t : Spec (CommRingCat.of (𝓞 L)) | f ∈ t.asIdeal}.Finite := by
  have hI : Ideal.span {f} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine ((Ideal.finite_factors hI).image fun v =>
    (⟨v.asIdeal, v.isPrime⟩ : PrimeSpectrum (𝓞 L))).subset ?_
  intro t ht
  have ht' : f ∈ t.asIdeal := ht
  have ht0 : t.asIdeal ≠ ⊥ := fun h => hf (by rw [h] at ht'; exact (Submodule.mem_bot _).mp ht')
  refine ⟨⟨t.asIdeal, t.isPrime, ht0⟩, ?_, rfl⟩
  show t.asIdeal ∣ Ideal.span {f}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact ht'

end Dedekind

section R2

attribute [local instance] algXi algEta algXiEta

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- An element of `𝓞_L` outside `t` is a unit of `𝒪_{𝒢,e(t)}`. (Used for reading step (R2).) -/
theorem isUnit_stalkAlg (t : Spec (CommRingCat.of (𝓞 L))) (u : 𝓞 L) (hu : u ∉ t.asIdeal) :
    IsUnit (stalkAlg 𝒢 (𝒢.unitSection t) u) := by
  have : t.asIdeal.IsPrime := t.isPrime
  let _ : Algebra (𝓞 L) ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk t) :=
    (baseStalk t).toAlgebra
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk t) t.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) t
  have h1 : IsUnit (unitStalk 𝒢 t (stalkAlg 𝒢 (𝒢.unitSection t) u)) := by
    rw [unitStalk_stalkAlg]
    exact IsLocalization.map_units ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk t)
      (⟨u, hu⟩ : t.asIdeal.primeCompl)
  exact isUnit_of_map_unit (unitStalk 𝒢 t) _ h1

/-- The stalk lattice at `t` is stable under multiplication by the germs `w ∈ 𝒪_{𝒢,e(t)}` with
`d(w|_ξ) = 0`. (Used for reading step (R2).) -/
theorem smul_mem_printedOmegaAt (t : Spec (CommRingCat.of (𝓞 L)))
    (w : 𝒢.G.left.presheaf.stalk (𝒢.unitSection t))
    (hw : D (𝓞 L) 𝒢.genStalk (specMap 𝒢 t w) = 0)
    {y : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]}
    (hy : y ∈ printedOmegaAt 𝒢 t) : specMap 𝒢 t w • y ∈ printedOmegaAt 𝒢 t := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, rfl⟩
    have e : specMap 𝒢 t w • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 t b)) =
        (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 t (w * b)) := by
      rw [← TensorProduct.tmul_smul, map_mul, Derivation.leibniz, hw, smul_zero, add_zero]
    rw [e]
    exact Submodule.subset_span ⟨w * b, rfl⟩
  · rw [smul_zero]; exact zero_mem _
  · intro x y _ _ hx hy
    rw [smul_add]; exact add_mem hx hy
  · intro a x _ hx
    rw [smul_comm]; exact Submodule.smul_mem _ a hx

/-- **The stalk lattice at `t` is an `𝒪_{S,t}`-module**: if `u ∉ t` and `u • y` lies in it, so
does `y`. (Used for reading step (R2).) -/
theorem mem_printedOmegaAt_of_smul_mem (t : Spec (CommRingCat.of (𝓞 L))) (u : 𝓞 L)
    (hu : u ∉ t.asIdeal) {y : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]}
    (hy : u • y ∈ printedOmegaAt 𝒢 t) : y ∈ printedOmegaAt 𝒢 t := by
  have hv := isUnit_stalkAlg 𝒢 t u hu
  have hinv : specMap 𝒢 t (↑hv.unit⁻¹ : 𝒢.G.left.presheaf.stalk (𝒢.unitSection t)) *
      algebraMap (𝓞 L) 𝒢.genStalk u = 1 := by
    rw [show algebraMap (𝓞 L) 𝒢.genStalk u = 𝒢.structMap u from rfl, ← specMap_stalkAlg 𝒢 t u,
      ← map_mul, hv.val_inv_mul, map_one]
  have hD : D (𝓞 L) 𝒢.genStalk
      (specMap 𝒢 t (↑hv.unit⁻¹ : 𝒢.G.left.presheaf.stalk (𝒢.unitSection t))) = 0 := by
    rw [(D (𝓞 L) 𝒢.genStalk).leibniz_of_mul_eq_one hinv, Derivation.map_algebraMap, smul_zero]
  have key := smul_mem_printedOmegaAt 𝒢 t _ hD hy
  rwa [← algebraMap_smul 𝒢.genStalk u y, smul_smul, hinv, one_smul] at key

/-- **The stalk lattices form a sheaf, near a point**: a generator `1 ⊗ d(b|_ξ)` of the stalk
lattice at `s` lies in the stalk lattice at every point near `s` (`b` is defined on a neighbourhood
`W` of `e(s)`, and its germs at the points of `e⁻¹(W)` have the same image at `ξ`). (Used for
reading step (R2).) -/
theorem eventually_mem_printedOmegaAt (s : Spec (CommRingCat.of (𝓞 L)))
    (b : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) :
    ∀ᶠ t in 𝓝 s, (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s b) ∈
      printedOmegaAt 𝒢 t := by
  obtain ⟨W, hW, b', rfl⟩ := TopCat.Presheaf.exists_germ_eq 𝒢.G.left.presheaf b
  have hξ : 𝒢.genericUnit ∈ W := (𝒢.specializes_genericUnit s).mem_open W.isOpen hW
  have e0 : ∀ (t : Spec (CommRingCat.of (𝓞 L))) (ht : 𝒢.unitSection t ∈ W),
      specMap 𝒢 t (𝒢.G.left.presheaf.germ W (𝒢.unitSection t) ht b') =
        𝒢.G.left.presheaf.germ W 𝒢.genericUnit hξ b' := by
    intro t ht
    unfold specMap
    erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  filter_upwards [(𝒢.unitSection ⁻¹ᵁ W).isOpen.mem_nhds hW] with t ht
  rw [e0 s hW, ← e0 t ht]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- Every element of the stalk lattice at `s` lies in the stalk lattice at every point near `s`.
(Used for reading step (R2).) -/
theorem eventually_mem_of_mem_printedOmegaAt (s : Spec (CommRingCat.of (𝓞 L)))
    {x : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]} (hx : x ∈ printedOmegaAt 𝒢 s) :
    ∀ᶠ t in 𝓝 s, x ∈ printedOmegaAt 𝒢 t := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩
    exact eventually_mem_printedOmegaAt 𝒢 s b
  · exact Filter.Eventually.of_forall fun t => zero_mem _
  · intro x y _ _ hx hy
    filter_upwards [hx, hy] with t h1 h2
    exact add_mem h1 h2
  · intro a x _ hx
    filter_upwards [hx] with t h
    exact Submodule.smul_mem _ a h

/-- **The stalk lattices are full**: for every point `t` and every `β ∈ 𝒪_{𝒢,ξ}`, a nonzero
multiple of `1 ⊗ dβ` lies in the stalk lattice at `t` (`𝒪_{𝒢,ξ}` is a localization of the ring of
an affine open around `e(t)`). (Used for reading step (R2).) -/
theorem exists_smul_mem_printedOmegaAt (t : Spec (CommRingCat.of (𝓞 L))) (β : 𝒢.genStalk) :
    ∃ c : 𝓞 L, c ≠ 0 ∧
      c • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk β) ∈ printedOmegaAt 𝒢 t := by
  obtain ⟨U, hU, htU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    𝒢.G.left.isBasis_affineOpens) (TopologicalSpace.Opens.mem_top (𝒢.unitSection t))
  have hξ : 𝒢.genericUnit ∈ U := (𝒢.specializes_genericUnit t).mem_open U.isOpen htU
  let _ : Algebra Γ(𝒢.G.left, U) 𝒢.genStalk :=
    TopCat.Presheaf.algebra_section_stalk 𝒢.G.left.presheaf ⟨𝒢.genericUnit, hξ⟩
  have hloc := (show IsAffineOpen U from hU).isLocalization_stalk ⟨𝒢.genericUnit, hξ⟩
  obtain ⟨ab, hab⟩ := IsLocalization.surj
    ((show IsAffineOpen U from hU).primeIdealOf ⟨𝒢.genericUnit, hξ⟩).asIdeal.primeCompl β
  have hbu : IsUnit (algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk (ab.2 : Γ(𝒢.G.left, U))) :=
    IsLocalization.map_units _ ab.2
  -- the germs at `ξ` come from germs at `e(t)`
  have hsp : ∀ c : Γ(𝒢.G.left, U), algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk c =
      specMap 𝒢 t (𝒢.G.left.presheaf.germ U (𝒢.unitSection t) htU c) := by
    intro c
    unfold specMap
    erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    rfl
  set a := algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk ab.1 with ha
  set b := algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk (ab.2 : Γ(𝒢.G.left, U)) with hb
  have hY : (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk a ∈ printedOmegaAt 𝒢 t := by
    rw [ha, hsp]; exact Submodule.subset_span ⟨_, rfl⟩
  have hZ : (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk b ∈ printedOmegaAt 𝒢 t := by
    rw [hb, hsp]; exact Submodule.subset_span ⟨_, rfl⟩
  -- `b • dβ = da - β • db`
  have hd : b • D (𝓞 L) 𝒢.genStalk β = D (𝓞 L) 𝒢.genStalk a - β • D (𝓞 L) 𝒢.genStalk b := by
    have h := Derivation.leibniz (D (𝓞 L) 𝒢.genStalk) β b
    rw [hab] at h
    rw [h]; abel
  have eq1 : b • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk β) =
      (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk a -
        β • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk b) := by
    rw [← TensorProduct.tmul_smul, hd, TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  -- clear denominators in `𝒪_{S,η} = Frac 𝓞_L`
  have : IsLocalization.AtPrime (Reta L) (⊥ : Ideal (𝓞 L)) := isLocalization_Reta
  have : Nontrivial (Reta L) := (isField_Reta (L := L)).nontrivial
  obtain ⟨x₁, h₁⟩ := IsLocalization.surj (⊥ : Ideal (𝓞 L)).primeCompl
    (algebraMap 𝒢.genStalk (Reta L) b)
  obtain ⟨x₂, h₂⟩ := IsLocalization.surj (⊥ : Ideal (𝓞 L)).primeCompl
    (algebraMap 𝒢.genStalk (Reta L) β)
  have hq : ∀ q : (⊥ : Ideal (𝓞 L)).primeCompl, (q : 𝓞 L) ≠ 0 := fun q h =>
    q.2 (by rw [h]; exact Ideal.zero_mem _)
  have hp₁ : x₁.1 ≠ 0 := by
    intro h0
    have hu : IsUnit (algebraMap 𝒢.genStalk (Reta L) b *
        algebraMap (𝓞 L) (Reta L) (x₁.2 : 𝓞 L)) :=
      (hbu.map _).mul (IsLocalization.map_units (Reta L) x₁.2)
    rw [h₁, h0, map_zero] at hu
    exact not_isUnit_zero hu
  refine ⟨(x₂.2 : 𝓞 L) * x₁.1, mul_ne_zero (hq x₂.2) hp₁, ?_⟩
  have e1 : ∀ (r : 𝓞 L) (y : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]),
      r • y = algebraMap (𝓞 L) (Reta L) r • y := fun r y => (algebraMap_smul (Reta L) r y).symm
  have e2 : ∀ (c : 𝒢.genStalk) (y : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]),
      c • y = algebraMap 𝒢.genStalk (Reta L) c • y := fun c y =>
    (algebraMap_smul (Reta L) c y).symm
  have key : ((x₂.2 : 𝓞 L) * x₁.1) • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk β) =
      ((x₁.2 : 𝓞 L) * x₂.2) • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk a) -
        ((x₁.2 : 𝓞 L) * x₂.1) • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk b) := by
    rw [e1, e1 _ ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk a),
      e1 _ ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk b), map_mul, map_mul, map_mul, ← h₁,
      ← h₂]
    rw [e2, e2 β] at eq1
    calc (algebraMap (𝓞 L) (Reta L) (x₂.2 : 𝓞 L) *
          (algebraMap 𝒢.genStalk (Reta L) b * algebraMap (𝓞 L) (Reta L) (x₁.2 : 𝓞 L))) •
          ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk β)
        = (algebraMap (𝓞 L) (Reta L) (x₁.2 : 𝓞 L) * algebraMap (𝓞 L) (Reta L) (x₂.2 : 𝓞 L)) •
          (algebraMap 𝒢.genStalk (Reta L) b •
            ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk β)) := by
          rw [smul_smul]; congr 1; ring
      _ = _ := by
          rw [eq1, smul_sub, smul_smul]; congr 2; ring
  rw [key]
  exact sub_mem (Submodule.smul_mem _ _ hY) (Submodule.smul_mem _ _ hZ)

/-- Every element of a stalk lattice has a nonzero multiple in the stalk lattice at any point.
(Used for reading step (R2).) -/
theorem exists_smul_mem_of_mem_printedOmegaAt (s t : Spec (CommRingCat.of (𝓞 L)))
    {x : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]} (hx : x ∈ printedOmegaAt 𝒢 s) :
    ∃ c : 𝓞 L, c ≠ 0 ∧ c • x ∈ printedOmegaAt 𝒢 t := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩
    exact exists_smul_mem_printedOmegaAt 𝒢 t _
  · exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  · rintro x y - - ⟨c, hc, hcx⟩ ⟨d, hd, hdy⟩
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have h : (c * d) • (x + y) = d • (c • x) + c • (d • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm c d x]
    rw [h]
    exact add_mem (Submodule.smul_mem _ d hcx) (Submodule.smul_mem _ c hdy)
  · rintro a x - ⟨c, hc, hcx⟩
    exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_mem _ a hcx⟩

/-- **Reading step (R2): the stalk lattices are the stalks of one quasi-coherent sheaf.** For every
point `s` of `Spec 𝓞_L`, the localization at `s` of the intersection `⋂_t printedOmegaAt t` of the
stalk lattices is the stalk lattice `printedOmegaAt s = (e*Ω¹)_s`. -/
theorem locIn_iInf_printedOmegaAt (s : PrimeSpectrum (𝓞 L)) :
    locIn (⨅ t, printedOmegaAt 𝒢 t) s.asIdeal.primeCompl = printedOmegaAt 𝒢 s := by
  apply le_antisymm
  · rintro x ⟨u, hu, hx⟩
    exact mem_printedOmegaAt_of_smul_mem 𝒢 s u hu ((Submodule.mem_iInf _).mp hx s)
  · intro x hx
    have hev := eventually_mem_of_mem_printedOmegaAt 𝒢 s hx
    obtain ⟨_, ⟨f, rfl⟩, hsf, hsub⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := 𝓞 L)).mem_nhds_iff.mp hev
    have hfs : f ∉ s.asIdeal := (PrimeSpectrum.mem_basicOpen f s).mp hsf
    have hf0 : f ≠ 0 := fun h => hfs (h ▸ Ideal.zero_mem _)
    have hout : ∀ t : Spec (CommRingCat.of (𝓞 L)), f ∉ t.asIdeal → x ∈ printedOmegaAt 𝒢 t :=
      fun t ht => hsub ((PrimeSpectrum.mem_basicOpen f t).mpr ht)
    have hin : ∀ t : Spec (CommRingCat.of (𝓞 L)), f ∈ t.asIdeal →
        ∃ n : ℕ, f ^ n • x ∈ printedOmegaAt 𝒢 t := by
      intro t hft
      have : t.asIdeal.IsPrime := t.isPrime
      have ht0 : t.asIdeal ≠ ⊥ := fun h =>
        hf0 (by rw [h] at hft; exact (Submodule.mem_bot _).mp hft)
      obtain ⟨c, hc0, hc⟩ := exists_smul_mem_of_mem_printedOmegaAt 𝒢 s t hx
      obtain ⟨n, u, d, hut, hud⟩ := exists_mul_pow_eq_mul ht0 hft hc0
      refine ⟨n, mem_printedOmegaAt_of_smul_mem 𝒢 t u hut ?_⟩
      rw [smul_smul, hud, mul_comm, mul_smul]
      exact Submodule.smul_mem _ d hc
    choose! n hn using hin
    have hZ := finite_setOf_mem_asIdeal hf0
    refine ⟨f ^ (hZ.toFinset.sup n), fun h => hfs (s.isPrime.mem_of_pow_mem _ h), ?_⟩
    rw [Submodule.mem_iInf]
    intro t
    by_cases hft : f ∈ t.asIdeal
    · have hle : n t ≤ hZ.toFinset.sup n := Finset.le_sup (hZ.mem_toFinset.mpr hft)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ (hn t hft)
    · exact Submodule.smul_mem _ _ (hout t hft)

/-- The intersection of the stalk lattices is the image of the tree's `printedOmega`. (Used for
reading step (R2).) -/
theorem iInf_printedOmegaAt_eq_map :
    (⨅ s : PrimeSpectrum (𝓞 L), printedOmegaAt 𝒢 s) = (printedOmega 𝒢).map (theta' 𝒢) :=
  calc (⨅ s : PrimeSpectrum (𝓞 L), printedOmegaAt 𝒢 s) = 𝒢.omega.map (theta' 𝒢) :=
        (omega_map 𝒢).symm
    _ = (printedOmega 𝒢).map (theta' 𝒢) := by rw [printedOmega_eq]

/-- **Reading step (R2), uniqueness.** An `𝓞_L`-submodule `N` of the generic stalk whose
localization at every point `s` of `Spec 𝓞_L` is the stalk `(e*Ω¹)_s` is `θ(printedOmega)`. -/
theorem eq_map_printedOmega_of_locIn
    (N : Submodule (𝓞 L) ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]))
    (hN : ∀ s : PrimeSpectrum (𝓞 L), locIn N s.asIdeal.primeCompl = printedOmegaAt 𝒢 s) :
    N = (printedOmega 𝒢).map (theta' 𝒢) := by
  rw [← iInf_printedOmegaAt_eq_map, ← iInf_congr hN]
  exact eq_iInf_locIn N

/-- **Reading step (R2), closed: `printedOmega = Γ(Spec 𝓞_L, e*Ω¹)`.** In the generic stalk
`V = 𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`, `θ(printedOmega)` has localization `(e*Ω¹)_s = printedOmegaAt s` at
every point `s` of `Spec 𝓞_L`, and it is the only `𝓞_L`-submodule of `V` with these localizations.
So for the quasi-coherent torsion-free sheaf `e*Ω¹ = N~` (`N` its module of global sections, embedded
in its generic stalk `V`), whose stalks are the `printedOmegaAt s`, `N = θ(printedOmega)`. -/
theorem printedOmega_eq_globalSections :
    (∀ s : PrimeSpectrum (𝓞 L),
      locIn ((printedOmega 𝒢).map (theta' 𝒢)) s.asIdeal.primeCompl = printedOmegaAt 𝒢 s) ∧
    ∀ N : Submodule (𝓞 L) ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]),
      (∀ s : PrimeSpectrum (𝓞 L), locIn N s.asIdeal.primeCompl = printedOmegaAt 𝒢 s) →
      N = (printedOmega 𝒢).map (theta' 𝒢) :=
  ⟨fun s => by rw [← iInf_printedOmegaAt_eq_map]; exact locIn_iInf_printedOmegaAt 𝒢 s,
    eq_map_printedOmega_of_locIn 𝒢⟩

/-- **Reading step (R2), inside `ω_{A_L} = 𝔪_ξ/𝔪_ξ²`.** `printedOmega` is the unique
`𝓞_L`-submodule of `ω_{A_L}` whose image under `θ` has the stalks `(e*Ω¹)_s` as localizations. -/
theorem printedOmega_unique (N : Submodule (𝓞 L) 𝒢.cotangent)
    (hN : ∀ s : PrimeSpectrum (𝓞 L),
      locIn (N.map (theta' 𝒢)) s.asIdeal.primeCompl = printedOmegaAt 𝒢 s) :
    N = printedOmega 𝒢 :=
  Submodule.map_injective_of_injective (show Function.Injective (theta' 𝒢) from theta_injective 𝒢)
    (eq_map_printedOmega_of_locIn 𝒢 _ hN)

/-- **Reading step (R2), inside `ω_{A_L}`**: every element of the conormal lattice `omegaAt s` at a
point `s` has a multiple by an element outside `s` in `printedOmega` (the localization of
`printedOmega` at `s` is `omegaAt s`). -/
theorem exists_smul_mem_printedOmega (s : PrimeSpectrum (𝓞 L)) {v : 𝒢.cotangent}
    (hv : v ∈ 𝒢.omegaAt s) : ∃ u : 𝓞 L, u ∉ s.asIdeal ∧ u • v ∈ printedOmega 𝒢 := by
  have h1 : theta' 𝒢 v ∈ printedOmegaAt 𝒢 s :=
    (omegaAt_map 𝒢 s).le (Submodule.mem_map_of_mem hv)
  have h2 : theta' 𝒢 v ∈ locIn (⨅ t, printedOmegaAt 𝒢 t) s.asIdeal.primeCompl :=
    (locIn_iInf_printedOmegaAt 𝒢 s).ge h1
  obtain ⟨u, hu, hux⟩ := h2
  refine ⟨u, hu, ?_⟩
  show theta' 𝒢 (u • v) ∈ ⨅ s, printedOmegaAt 𝒢 s
  rw [map_smul]
  exact hux

end R2

/-! ## (R2) The top wedge: `ε*Ω^g` -/

section Det

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `⋀^g` of the stalk lattice at `s`, in the Hodge line `hodgeSpace g`: the `𝓞_L`-span of the
wedges `1 ⊗ v₁ ∧ ⋯ ∧ v_g` of elements of the conormal lattice `omegaAt s = θ⁻¹((e*Ω¹)_s)`. Its
localization at `s` is the image of the stalk `(ε*Ω^g)_s = ⋀^g_{𝒪_{S,s}} (e*Ω¹)_s`. (Used for
reading step (R2).) -/
def detAt (g : ℕ) (s : PrimeSpectrum (𝓞 L)) : Submodule (𝓞 L) (𝒢.hodgeSpace g) :=
  Submodule.span (𝓞 L) (Set.range fun v : Fin g → 𝒢.omegaAt s =>
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => (v i : 𝒢.cotangent)))

/-- **Reading step (R2), top wedge: the stalks of the height lattice.** At every point `s` of
`Spec 𝓞_L`, the localization of `printedDetLattice 𝒢 g = ⋀^g printedOmega` is the stalk
`(ε*Ω^g)_s = 𝒪_{S,s} · ⋀^g (e*Ω¹)_s`. -/
theorem locIn_printedDetLattice (g : ℕ) (s : PrimeSpectrum (𝓞 L)) :
    locIn (printedDetLattice 𝒢 g) s.asIdeal.primeCompl =
      locIn (detAt 𝒢 g s) s.asIdeal.primeCompl := by
  apply le_antisymm
  · apply locIn_mono
    rw [printedDetLattice, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : ∀ i, (v i : 𝒢.cotangent) ∈ 𝒢.omegaAt s := fun i =>
      (Submodule.mem_iInf _).mp ((printedOmega_eq 𝒢).le (v i).2) s
    exact Submodule.subset_span ⟨fun i => ⟨v i, hv i⟩, rfl⟩
  · have hle : detAt 𝒢 g s ≤ locIn (printedDetLattice 𝒢 g) s.asIdeal.primeCompl := by
      rw [detAt, Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      choose u hu huv using fun i => exists_smul_mem_printedOmega 𝒢 s (v i).2
      refine ⟨∏ i, u i, Submonoid.prod_mem _ fun i _ => hu i, ?_⟩
      rw [← TensorProduct.tmul_smul, ← AlternatingMap.map_smul_univ]
      exact Submodule.subset_span ⟨fun i => ⟨u i • (v i : 𝒢.cotangent), huv i⟩, rfl⟩
    calc locIn (detAt 𝒢 g s) s.asIdeal.primeCompl
        ≤ locIn (locIn (printedDetLattice 𝒢 g) s.asIdeal.primeCompl) s.asIdeal.primeCompl :=
          locIn_mono hle _
      _ = locIn (printedDetLattice 𝒢 g) s.asIdeal.primeCompl := locIn_locIn _ _

/-- **Reading step (R2), top wedge, uniqueness.** An `𝓞_L`-submodule of the Hodge line whose
localization at every point `s` is the stalk `(ε*Ω^g)_s` is `printedDetLattice 𝒢 g`. -/
theorem eq_printedDetLattice_of_locIn (g : ℕ) (N : Submodule (𝓞 L) (𝒢.hodgeSpace g))
    (hN : ∀ s : PrimeSpectrum (𝓞 L),
      locIn N s.asIdeal.primeCompl = locIn (detAt 𝒢 g s) s.asIdeal.primeCompl) :
    N = printedDetLattice 𝒢 g :=
  calc N = ⨅ s : PrimeSpectrum (𝓞 L), locIn N s.asIdeal.primeCompl := eq_iInf_locIn N
    _ = ⨅ s : PrimeSpectrum (𝓞 L), locIn (printedDetLattice 𝒢 g) s.asIdeal.primeCompl :=
        iInf_congr fun s => (hN s).trans (locIn_printedDetLattice 𝒢 g s).symm
    _ = printedDetLattice 𝒢 g := (eq_iInf_locIn _).symm

/-- **Reading step (R2), closed for the height lattice: `printedDetLattice = Γ(Spec 𝓞_L, ε*Ω^g)`.**
`printedDetLattice 𝒢 g`, the lattice of `IsGR1StableHeightOriginal`, has localization
`(ε*Ω^g)_s = 𝒪_{S,s} · ⋀^g (e*Ω¹)_s` at every point `s` of `Spec 𝓞_L`, and it is the only
`𝓞_L`-submodule of the Hodge line with these localizations: it is the module of global sections of
the quasi-coherent sheaf `ε*Ω^g` (in its generic fibre). -/
theorem printedDetLattice_eq_globalSections (g : ℕ) :
    (∀ s : PrimeSpectrum (𝓞 L), locIn (printedDetLattice 𝒢 g) s.asIdeal.primeCompl =
      locIn (detAt 𝒢 g s) s.asIdeal.primeCompl) ∧
    ∀ N : Submodule (𝓞 L) (𝒢.hodgeSpace g),
      (∀ s : PrimeSpectrum (𝓞 L),
        locIn N s.asIdeal.primeCompl = locIn (detAt 𝒢 g s) s.asIdeal.primeCompl) →
      N = printedDetLattice 𝒢 g :=
  ⟨locIn_printedDetLattice 𝒢 g, eq_printedDetLattice_of_locIn 𝒢 g⟩

end Det

end ZInQ.HeightModelM.ReadingSteps
