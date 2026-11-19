import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.HodgeLine

/-!
# The unchanged degree-one Hodge lattice of a group model

The natural map from the cotangent space to its first Hodge space is injective. Its image
of the original integral cotangent lattice is exactly the original determinant lattice.
For dimension one, the reviewed cotangent calculation supplies the pointwise rank input
in the existing Hodge-lattice proof. No all-dimensions rank proposition is assumed.

Locators: `HodgeLattice.omegaLocal`, `HodgeLattice.hodgeLattice_of_lattice`,
`HodgeLineBinding.finrank_cotangentSpace_genStalk`, Mathlib, `exteriorPower.oneEquiv`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal

open NumberField TensorProduct AlgebraicGeometry IsLocalRing ExteriorAlgebra
open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open ZInQ.Contrib.RC53Assist.HodgeLineBinding
open ZInQ.Contrib.RC53Assist.S2aNumberField
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra abelian_scheme_integral)

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- DEFINITION. The original cotangent space maps naturally to the first Hodge space.
Locator: Mathlib, `exteriorPower.oneEquiv`, `TensorProduct.mk`. -/
def oneHodgeMap (G : GroupModel E L) : G.cotangent →ₗ[𝓞 L] G.hodgeSpace 1 :=
  (TensorProduct.mk (𝓞 L) L (exteriorPower (𝓞 L) 1 G.cotangent) 1) ∘ₗ
    (exteriorPower.oneEquiv (𝓞 L) G.cotangent).symm.toLinearMap

/-- THEOREM. The natural map sends a single vector to its original degree-one wedge.
Locator: Mathlib, `exteriorPower.oneEquiv_ιMulti`. -/
theorem oneHodgeMap_single (G : GroupModel E L) (v : Fin 1 → G.cotangent) :
    oneHodgeMap G (v 0) =
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) 1 v := by
  have he : exteriorPower.ιMulti (𝓞 L) 1 v =
      (exteriorPower.oneEquiv (𝓞 L) G.cotangent).symm (v 0) := by
    rw [LinearEquiv.eq_symm_apply, exteriorPower.oneEquiv_ιMulti]
  rw [he]
  rfl

/-- THEOREM. The map on the cotangent class of a germ is the model's original wedge.
Locator: `GroupModel.wedge`, `oneHodgeMap_single`. -/
theorem oneHodgeMap_dCls (G : GroupModel E L) (f : maximalIdeal G.genStalk) :
    oneHodgeMap G (G.dCls f) = G.wedge ![f] :=
  oneHodgeMap_single G ![G.dCls f]

/-- THEOREM. The natural degree-one map is injective, without a dimension assumption.
Locator: `HodgeLattice.isUnit_structMap`; Mathlib, `IsLocalizedModule.exists_of_eq`. -/
theorem oneHodgeMap_injective (G : GroupModel E L) : Function.Injective (oneHodgeMap G) := by
  intro x y hxy
  have hzero : oneHodgeMap G (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L))
      (TensorProduct.mk (𝓞 L) L (exteriorPower (𝓞 L) 1 G.cotangent) 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L _).mpr
      (TensorProduct.isBaseChange _ _ _)
  have key : TensorProduct.mk (𝓞 L) L (exteriorPower (𝓞 L) 1 G.cotangent) 1
      ((exteriorPower.oneEquiv (𝓞 L) G.cotangent).symm (x - y)) =
      TensorProduct.mk (𝓞 L) L (exteriorPower (𝓞 L) 1 G.cotangent) 1 0 := by
    rw [map_zero]
    exact hzero
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := nonZeroDivisors (𝓞 L)) key
  have hc' := congrArg (exteriorPower.oneEquiv (𝓞 L) G.cotangent) hc
  rw [smul_zero, Submonoid.smul_def, map_smul, LinearEquiv.apply_symm_apply, map_zero] at hc'
  have hz : G.structMap (c : 𝓞 L) • (x - y) = 0 := hc'
  rw [(isUnit_structMap G (nonZeroDivisors.ne_zero c.2)).smul_eq_zero] at hz
  exact sub_eq_zero.mp hz

/-- THEOREM. The first determinant lattice is exactly the image of the original `omega`.
Locator: `Models.detLattice`, `oneHodgeMap_single`, Mathlib, `Submodule.span_le`. -/
theorem detLattice_one_eq_map_omega (G : GroupModel E L) :
    G.detLattice 1 = G.omega.map (oneHodgeMap G) := by
  apply le_antisymm
  · rw [GroupModel.detLattice, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact ⟨(v 0 : G.cotangent), (v 0).property,
      oneHodgeMap_single G (fun j => (v j : G.cotangent))⟩
  · rintro _ ⟨x, hx, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun _ => ⟨x, hx⟩, ?_⟩
    exact (oneHodgeMap_single G (fun _ => x)).symm

/-- DEFINITION. The integral cotangent lattice and its first determinant lattice agree
as modules, without choosing an integral generator.
Locator: `detLattice_one_eq_map_omega`, Mathlib, `LinearEquiv.ofBijective`. -/
def omegaDetEquiv (G : GroupModel E L) : G.omega ≃ₗ[𝓞 L] G.detLattice 1 :=
  LinearEquiv.ofBijective ((oneHodgeMap G).restrict (fun x hx => by
    rw [detLattice_one_eq_map_omega]
    exact Submodule.mem_map_of_mem hx)) ⟨by
    intro x y hxy
    exact Subtype.ext (oneHodgeMap_injective G (congrArg Subtype.val hxy)), by
    rintro ⟨v, hv⟩
    rw [detLattice_one_eq_map_omega] at hv
    obtain ⟨x, hx, hxv⟩ := hv
    exact ⟨⟨x, hx⟩, Subtype.ext hxv⟩⟩

/-- THEOREM. The integral isomorphism is induced by the natural degree-one map.
Locator: `omegaDetEquiv`, Mathlib, `LinearEquiv.ofBijective_apply`. -/
@[simp] theorem omegaDetEquiv_apply (G : GroupModel E L) (x : G.omega) :
    (omegaDetEquiv G x : G.hodgeSpace 1) = oneHodgeMap G x := rfl

/-- THEOREM. The unchanged integral cotangent lattice is finitely generated.
Locator: `HodgeLattice.omegaLocal`, `HodgeLattice.omegaFG_of_omegaLocal`. -/
theorem omega_fg (G : GroupModel E L) : G.omega.FG :=
  omegaFG_of_omegaLocal omegaLocal K E L G

/-- THEOREM. Every original determinant lattice is finitely generated.
Locator: `HodgeLattice.detLattice_eq`, `HodgeLattice.detLat_fg`, `omega_fg`. -/
theorem detLattice_fg (G : GroupModel E L) (g : ℕ) : (G.detLattice g).FG := by
  rw [detLattice_eq]
  exact detLat_fg G.omega (omega_fg G) g

/-- THEOREM. The reviewed cotangent calculation gives the pointwise rank-one input.
Locator: `HodgeLineBinding.finrank_cotangentSpace_genStalk`,
`HodgeLattice.rank_tensor_cotangent`, `abVar_projectiveWeierstrassModel_numberField`. -/
theorem rank_tensor_cotangent_of_dim_one (G : GroupModel E L) (hdim : E.dim = 1) :
    Module.rank L (L ⊗[𝓞 L] G.cotangent) = 1 := by
  haveI := abelian_scheme_integral (E.baseChange L).X
  letI := functionFieldAlgebra (E.baseChange L).X.hom
  obtain ⟨E', -, -, i, -, -, hO⟩ :=
    abVar_projectiveWeierstrassModel_numberField L (E.baseChange L)
      (baseChange_dim_eq_one hdim)
  haveI : IsLocallyNoetherian G.G.left := LocallyOfFiniteType.isLocallyNoetherian G.G.hom
  rw [rank_tensor_cotangent G, ← Module.finrank_eq_rank,
    finrank_cotangentSpace_genStalk G E' i hO]
  simp

/-- THEOREM. The original Hodge-lattice conclusion holds for this dimension-one model.
This is the pointwise proof underlying `hodgeLatticeTheorem_of_cotangentRank`, not a proof
of its all-dimensions input.
Locator: `HodgeLattice.hodgeLattice_of_lattice`, `HodgeLattice.omegaLocal`. -/
theorem hodgeLattice_one (G : GroupModel E L) (hdim : E.dim = 1) :
    Module.finrank L (G.hodgeSpace 1) = 1 ∧
      ∃ s ∈ G.detLattice 1, s ≠ 0 ∧ secIndex (G.detLattice 1) s ≠ 0 := by
  rw [detLattice_eq]
  exact hodgeLattice_of_lattice G.omega (omega_fg G)
    (rank_tensor_cotangent_of_dim_one G hdim)
    (omegaSpans_of_omegaLocal omegaLocal K E L G)

/-- THEOREM. The first determinant lattice is nonzero.
Locator: `hodgeLattice_one`. -/
theorem detLattice_one_ne_bot (G : GroupModel E L) (hdim : E.dim = 1) :
    G.detLattice 1 ≠ ⊥ := by
  obtain ⟨-, s, hs, hs0, -⟩ := hodgeLattice_one G hdim
  intro hbot
  apply hs0
  have : s ∈ (⊥ : Submodule (𝓞 L) (G.hodgeSpace 1)) := hbot ▸ hs
  exact this

/-- THEOREM. The original determinant lattice spans the Hodge line over `L`.
Locator: `hodgeLattice_one`, Mathlib, `finrank_eq_one_iff_of_nonzero'`. -/
theorem detLattice_one_spans (G : GroupModel E L) (hdim : E.dim = 1) :
    Submodule.span L (G.detLattice 1 : Set (G.hodgeSpace 1)) = ⊤ := by
  obtain ⟨hV, s, hs, hs0, -⟩ := hodgeLattice_one G hdim
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' s hs0).mp hV v
  exact Submodule.smul_mem _ a (Submodule.subset_span hs)

end ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal
