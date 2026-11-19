import ZInQKernel.HDecomp.Faltings.HodgeLattice
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.IdentityPlace

/-!
# The local ring of a group model at the identity of its generic fibre

Let `𝒢` be a smooth group model over `𝓞_L` of an abelian variety `A_L`, with
`𝒢.gen : 𝒢_L ≅ A_L` (group schemes over `L`) and `ξ` the image of the generic point under the
unit section of `𝒢`. The projection `p : 𝒢_L = 𝒢 ×_{𝓞_L} L → 𝒢` sends the identity `ξ_L` of
the generic fibre to `ξ` and induces an isomorphism of local rings (`Spec L → Spec 𝓞_L` is a
localization); `𝒢.gen` sends `ξ_L` to the origin `o` of `A_L` and is an isomorphism. The
composite of the stalk map of `p` with the inverse of the stalk map of `𝒢.gen` is the ring
isomorphism `originStalkEquiv : 𝒪_{𝒢,ξ} ≅ 𝒪_{A_L,o}`, made only of actual stalk maps.

It induces `toModelCotangent : 𝔪_o/𝔪_o² → 𝔪_ξ/𝔪_ξ² = 𝒢.cotangent`. A wedge `1 ⊗ df` in
`hodgeSpace 1 = L ⊗_{𝓞_L} ⋀¹(𝔪_ξ/𝔪_ξ²)` is nonzero as soon as `f ∉ 𝔪_ξ²`
(`wedge_single_ne_zero`): nonzero elements of `𝓞_L` act invertibly on `𝔪_ξ/𝔪_ξ²`.

Only the unit section of `𝒢`, its generic fibre and `𝒢.gen` enter; no other group law and no
section of a projective model are used.

Locator: the identifications are `genericFibreStalkIso`, `fst_genericFibreUnit` and
`gen_genericFibreUnit` (proved in the module `ZInQKernel.HDecomp.Faltings.HodgeLattice`,
§9–§10);
EGA I, 3.6.5 for stalks of a base change.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TensorProduct
open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open ZInQ.Contrib.RC53Assist.S2aNumberField (identityPoint identitySection)

/-- THEOREM (proved). The origin `originPt` of the Hodge-lattice development is the
identity point of the number-field S2a development: `Spec L` has a single point.
Locator: `originPt`, `identityPoint`. -/
theorem originPt_eq_identityPoint {L : Type} [Field L] (B : PkgI3.AbVar L) :
    originPt B = identityPoint B.X := by
  unfold originPt identityPoint identitySection
  exact congrArg _ (Subsingleton.elim _ _)

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- THEOREM (proved). `𝒢.gen` sends the identity of the generic fibre to the identity point of
`A_L`. Locator: `gen_genericFibreUnit`, `originPt_eq_identityPoint`. -/
theorem gen_genericFibreUnit_eq (G : GroupModel E L) :
    G.gen.hom.left (genericFibreUnit G) = identityPoint (E.baseChange L).X :=
  (gen_genericFibreUnit G).trans (originPt_eq_identityPoint _)

/-- DEFINITION. The isomorphism `𝒪_{𝒢,ξ} ≅ 𝒪_{A_L,o}`: the stalk map of the projection of the
generic fibre at `ξ_L`, followed by the inverse of the stalk map of `𝒢.gen` at `ξ_L`.
Locator: `genericFibreStalkIso`; the construction of `originStalkIso_of`. -/
def originStalkEquiv (G : GroupModel E L) :
    G.genStalk ≃+* (E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X) :=
  haveI hp : IsIso ((pullback.fst G.G.hom (toGeneric L)).stalkMap (genericFibreUnit G)) :=
    genericFibreStalkIso L G.G _
  haveI hφ : IsOpenImmersion ((Over.forget _).mapIso G.gen).hom := inferInstance
  haveI hφs : IsIso (((Over.forget _).mapIso G.gen).hom.stalkMap (genericFibreUnit G)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hφ).2 _
  let e1 : G.genStalk ≅ (genericFibre L G.G).left.presheaf.stalk (genericFibreUnit G) :=
    G.G.left.presheaf.stalkCongr (Inseparable.of_eq (fst_genericFibreUnit G).symm) ≪≫
      @asIso _ _ _ _ _ hp
  let e2 : (E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X) ≅
      (genericFibre L G.G).left.presheaf.stalk (genericFibreUnit G) :=
    (E.baseChange L).X.left.presheaf.stalkCongr
        (Inseparable.of_eq (gen_genericFibreUnit_eq G).symm) ≪≫
      @asIso _ _ _ _ _ hφs
  (e1 ≪≫ e2.symm).commRingCatIsoToRingEquiv

/-- THEOREM (proved). The inverse of `originStalkEquiv` maps the maximal ideal into the maximal
ideal. Locator: a ring isomorphism preserves units. -/
theorem originStalkEquiv_symm_mem (G : GroupModel E L)
    {a : (E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X)}
    (ha : a ∈ maximalIdeal _) : (originStalkEquiv G).symm a ∈ maximalIdeal G.genStalk := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  intro hu
  apply ha
  simpa using hu.map (originStalkEquiv G)

/-- THEOREM (proved). The inverse of `originStalkEquiv` maps elements outside `𝔪_o²` to elements
outside `𝔪_ξ²`. Locator: `Ideal.map_pow`, `RingEquiv`-invariance of maximal ideals. -/
theorem originStalkEquiv_symm_not_mem_sq (G : GroupModel E L)
    {a : (E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X)}
    (ha : a ∉ maximalIdeal _ ^ 2) :
    (originStalkEquiv G).symm a ∉ maximalIdeal G.genStalk ^ 2 := by
  intro h
  apply ha
  have hmap : (maximalIdeal G.genStalk).map (originStalkEquiv G) = maximalIdeal _ :=
    map_ringEquiv_maximalIdeal (originStalkEquiv G)
  have h2 : originStalkEquiv G ((originStalkEquiv G).symm a) ∈
      ((maximalIdeal G.genStalk) ^ 2).map (originStalkEquiv G) :=
    Ideal.mem_map_of_mem _ h
  rwa [Ideal.map_pow, hmap, RingEquiv.apply_symm_apply] at h2

/-- DEFINITION. The map `𝔪_o/𝔪_o² → 𝔪_ξ/𝔪_ξ² = 𝒢.cotangent` induced by `originStalkEquiv`.
Locator: Mathlib, `Ideal.mapCotangent`. -/
def toModelCotangent (G : GroupModel E L) :
    CotangentSpace ((E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X)) →+
      G.cotangent :=
  (Ideal.mapCotangent (maximalIdeal _) (maximalIdeal G.genStalk)
    (originStalkEquiv G).symm.toRingHom.toIntAlgHom
    fun _ ha => originStalkEquiv_symm_mem G ha).toAddMonoidHom

/-- THEOREM (proved). `toModelCotangent` sends the class of `a ∈ 𝔪_o` to `d` of its image.
Locator: Mathlib, `Ideal.mapCotangent_toCotangent`. -/
theorem toModelCotangent_toCotangent (G : GroupModel E L)
    {a : (E.baseChange L).X.left.presheaf.stalk (identityPoint (E.baseChange L).X)}
    (ha : a ∈ maximalIdeal _) :
    toModelCotangent G ((maximalIdeal _).toCotangent ⟨a, ha⟩) =
      G.dCls ⟨(originStalkEquiv G).symm a, originStalkEquiv_symm_mem G ha⟩ :=
  rfl

/-- THEOREM (proved). A wedge `1 ⊗ df` in `hodgeSpace 1` is nonzero when `f ∉ 𝔪_ξ²`: a vanishing
`1 ⊗ ν` in `L ⊗_{𝓞_L} N` is killed by some nonzero `c ∈ 𝓞_L`, and `c` acts on `𝒢.cotangent`
through the unit `structMap c`. Locator: Mathlib, `IsLocalizedModule.exists_of_eq`,
`exteriorPower.oneEquiv`; `isUnit_structMap`. -/
theorem wedge_single_ne_zero (G : GroupModel E L) (f : maximalIdeal G.genStalk)
    (hf : (f : G.genStalk) ∉ maximalIdeal G.genStalk ^ 2) : G.wedge ![f] ≠ 0 := by
  intro h0
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 L))
      (TensorProduct.mk (𝓞 L) L (⋀[𝓞 L]^1 G.cotangent) 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L _).mpr
      (TensorProduct.isBaseChange _ _ _)
  have h1 : TensorProduct.mk (𝓞 L) L (⋀[𝓞 L]^1 G.cotangent) 1
      (exteriorPower.ιMulti (𝓞 L) 1 fun i => G.dCls (![f] i)) =
      TensorProduct.mk (𝓞 L) L (⋀[𝓞 L]^1 G.cotangent) 1 0 := by
    rw [map_zero]
    exact h0
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors (𝓞 L)) h1
  rw [smul_zero, Submonoid.smul_def] at hc
  have h2 := congrArg (exteriorPower.oneEquiv (𝓞 L) G.cotangent) hc
  rw [map_smul, exteriorPower.oneEquiv_ιMulti, map_zero] at h2
  have hu := isUnit_structMap G (nonZeroDivisors.ne_zero c.2)
  have h3 : G.structMap (c : 𝓞 L) • G.dCls f = 0 := h2
  rw [hu.smul_eq_zero] at h3
  exact hf ((Ideal.toCotangent_eq_zero _ f).mp h3)

end ZInQ.Contrib.RC53Assist.HodgeLineBinding
