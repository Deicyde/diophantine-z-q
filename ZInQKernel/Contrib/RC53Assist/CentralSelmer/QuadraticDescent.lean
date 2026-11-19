import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.Central
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Pullback
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange

/-!
# Quadratic descent for the two-primary Selmer group over `ℚ(√k)`

Let `E/ℚ` be a Weierstrass curve with `a₁ = a₃ = 0`, let `k` be an integer which is not a square,
`K = ℚ(√k)`, and let `E^{(k)}` be the quadratic twist `qtwist E k`. The manuscript's
sum-and-difference step (`diophantine_zq.tex` lines 2616--2626, used in the base-zero lemma at
lines 4341--4352) compares the full Selmer group over `K` with the two rational Selmer groups:

```text
Sel_{2^∞}(E/K) → Sel_{2^∞}(E/ℚ) × Sel_{2^∞}(E^{(k)}/ℚ),   x ↦ (cor x, cor ψ_* x),
```

with kernel and cokernel killed by a fixed power of two, and no integral splitting. This file
constructs that map for the genuine Selmer groups and proves that both defects are killed by `2`.

## The objects

* `galK r`: for `r ∈ ℚˢ`, the stabilizer of `r` in `G_ℚ = Gal(ℚˢ/ℚ)`. It is the subgroup fixing
  the intermediate field `ℚ(r)` (`galK_eq_fixingAdjoin`), so it is `G_K = Gal(ℚˢ/K)` for
  `K = ℚ(r)`, with `ℚˢ` a separable closure of `K`.
* `decomp r τ` and `locK r τ E`: for a completion `L` of `ℚ` and an embedding `τ : ℚˢ → Lˢ`
  over `ℚ`, the decomposition group of the place of `K` cut out by `τ`, which is
  `Gal(Lˢ/L(τ r))` (`decomp_eq_fixingAdjoin`), and the localization
  `H¹(G_K, E(ℚˢ)) → H¹(Gal(Lˢ/L(τ r)), E(Lˢ))`. Every place of `K` arises from such an
  embedding, at the primes and at the real place.
* `shaK r E` and `selmerK r E`: the classes of `H¹(G_K, E(ℚˢ))` vanishing at every place of `K`,
  and the classes of `H¹(G_K, E(ℚˢ)[2^∞])` whose image in `H¹(G_K, E(ℚˢ))` lies in `shaK`.
  As for `sha`, the first is the meet of the Selmer groups of two `SelmerStructure`s with zero
  local conditions (`shaStructureK`), at the places above the primes and above the real place;
  the second is then cut out exactly as `selmerTwoPower`. The local conditions are taken along
  decomposition groups (Silverman, X.4). For `K = ℚ` the construction gives `selmerTwoPower`
  (`mem_selmerTwoPower_iff_res_mem_selmerK_one`).
* `pointTwist`: the isomorphism `E(ℚˢ) ≃ E^{(k)}(ℚˢ)`, `(x, y) ↦ (k x, k √k y)`, which is
  defined over `K`: it is equivariant for `G_K` and anti-equivariant off `G_K`
  (`isQuadraticTwist_pointTwist`).
* `selmerDescent` and `selmerAscent`: corestriction, respectively restriction, combined with the
  twist. For `E = E_ℓ`, `SelK ℓ k` and `quadraticDescent ℓ hk` are the instances.
* `conjH1` and `selmerConj`: the action of the nontrivial element of `Gal(K/ℚ)` on `H¹(G_K, -)`
  and on `Sel_{2^∞}(E/K)`, an involution (`conjH1_conjH1`, `selmerConj_selmerConj`).

## The results

* `ascentH1_descentH1`, `descentH1_ascentH1`: for an open subgroup of index two and a quadratic
  twist, both composites of descent and ascent are multiplication by `2` on `H¹`.
* `res_cor_eq_add_conjH1`, `twist_res_cor_eq_sub_conjH1`: restriction of corestriction is
  `1 + τ`, and its twisted form is `1 - τ`, for the action `τ` of `Gal(K/ℚ)`: the two
  components of the descent map are the two eigenspace projections.
* `res_mem_shaK`, `cor_mem_sha`, `twist_mem_shaK`, `twist_symm_mem_shaK`, `conjH1_mem_shaK`:
  restriction, corestriction (at split and at non-split places), the twist and the Galois action
  preserve local triviality at every place.
* `selmerDescent_boundedDefects`, `quadraticDescent_boundedDefects`: on the genuine Selmer
  groups the descent map has kernel and cokernel killed by `2`.
* `two_nsmul_eq_zero_of_conj_eq_self`, `exists_conj_eq_self`, `two_nsmul_eq_zero_of_conj_eq_neg`,
  `exists_conj_eq_neg`: corestriction on the invariant part and twisted corestriction on the
  anti-invariant part of `Sel_{2^∞}(E/K)` have kernel and cokernel killed by `2`.

No printed theorem is assumed, and no finiteness of a Shafarevich--Tate group is used.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace ZInQ.Manuscript.RC53Assist.QuadraticDescent

open TauCeti TauCeti.ContCohomology

section IndexTwo

variable {G : Type*} [Group G] (U : Subgroup G) (σ : G)

open scoped Classical in
/-- The transversal `{1, σ}` of a subgroup. -/
def twoTransversal : G ⧸ U → G := fun q => if q = (QuotientGroup.mk 1 : G ⧸ U) then 1 else σ

theorem mk_eq_mk_one_iff {g : G} : (QuotientGroup.mk g : G ⧸ U) = QuotientGroup.mk 1 ↔ g ∈ U := by
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

theorem twoTransversal_mk_of_mem {g : G} (hg : g ∈ U) :
    twoTransversal U σ (QuotientGroup.mk g) = 1 := by
  classical
  unfold twoTransversal
  split_ifs with h
  · rfl
  · exact absurd ((mk_eq_mk_one_iff U).mpr hg) h

theorem twoTransversal_mk_of_not_mem {g : G} (hg : g ∉ U) :
    twoTransversal U σ (QuotientGroup.mk g) = σ := by
  classical
  unfold twoTransversal
  split_ifs with h
  · exact absurd ((mk_eq_mk_one_iff U).mp h) hg
  · rfl

variable {U σ}

theorem mk_eq_mk_sigma (hidx : U.index = 2) (hσ : σ ∉ U) {g : G} (hg : g ∉ U) :
    (QuotientGroup.mk g : G ⧸ U) = QuotientGroup.mk σ := by
  rw [QuotientGroup.eq, Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
  exact iff_of_false hg hσ

theorem mk_twoTransversal (hidx : U.index = 2) (hσ : σ ∉ U) (q : G ⧸ U) :
    (QuotientGroup.mk (twoTransversal U σ q) : G ⧸ U) = q := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    by_cases hg : g ∈ U
    · rw [twoTransversal_mk_of_mem U σ hg, eq_comm]
      exact (mk_eq_mk_one_iff U).mpr hg
    · rw [twoTransversal_mk_of_not_mem U σ hg]
      exact (mk_eq_mk_sigma hidx hσ hg).symm

theorem mk_one_ne_mk_sigma (hσ : σ ∉ U) :
    (QuotientGroup.mk 1 : G ⧸ U) ≠ QuotientGroup.mk σ := by
  rw [Ne, QuotientGroup.eq, inv_one, one_mul]
  exact hσ

theorem sum_quotient_two [U.FiniteIndex] {N : Type*} [AddCommMonoid N]
    (hidx : U.index = 2) (hσ : σ ∉ U) (F : G ⧸ U → N) :
    let _ := Subgroup.fintypeQuotientOfFiniteIndex (H := U)
    ∑ q : G ⧸ U, F q = F (QuotientGroup.mk 1) + F (QuotientGroup.mk σ) := by
  intro
  refine Fintype.sum_eq_add _ _ (mk_one_ne_mk_sigma hσ) fun q hq => ?_
  exfalso
  induction q using QuotientGroup.induction_on with
  | H g =>
    by_cases hg : g ∈ U
    · exact hq.1 ((mk_eq_mk_one_iff U).mpr hg)
    · exact hq.2 (mk_eq_mk_sigma hidx hσ hg)

theorem conj_mem (hidx : U.index = 2) (hσ : σ ∉ U) {γ : G} (hγ : γ ∈ U) :
    σ⁻¹ * γ * σ ∈ U := by
  simp [Subgroup.mul_mem_iff_of_index_two hidx, hσ, hγ]

theorem mul_sigma_mem (hidx : U.index = 2) (hσ : σ ∉ U) {γ : G} (hγ : γ ∉ U) :
    γ * σ ∈ U := by
  simp [Subgroup.mul_mem_iff_of_index_two hidx, hσ, hγ]

theorem inv_sigma_mul_mem (hidx : U.index = 2) (hσ : σ ∉ U) {γ : G} (hγ : γ ∉ U) :
    σ⁻¹ * γ ∈ U := by
  simp [Subgroup.mul_mem_iff_of_index_two hidx, hσ, hγ]

theorem lWord_one_of_mem {γ : G} (hγ : γ ∈ U) :
    lWord U (twoTransversal U σ) (QuotientGroup.mk 1) γ = γ := by
  rw [lWord_def, MulAction.Quotient.smul_mk, smul_eq_mul, twoTransversal_mk_of_mem U σ (one_mem U),
    twoTransversal_mk_of_mem U σ (g := γ⁻¹ * 1) (by simpa using hγ)]
  group

theorem lWord_sigma_of_mem (hσ : σ ∉ U) {γ : G} (hγ : γ ∈ U) :
    lWord U (twoTransversal U σ) (QuotientGroup.mk σ) γ = σ⁻¹ * γ * σ := by
  rw [lWord_def, MulAction.Quotient.smul_mk, smul_eq_mul, twoTransversal_mk_of_not_mem U σ hσ,
    twoTransversal_mk_of_not_mem U σ (g := γ⁻¹ * σ)
      (fun h => hσ (by simpa using mul_mem hγ h))]

theorem lWord_one_of_not_mem {γ : G} (hγ : γ ∉ U) :
    lWord U (twoTransversal U σ) (QuotientGroup.mk 1) γ = γ * σ := by
  rw [lWord_def, MulAction.Quotient.smul_mk, smul_eq_mul, twoTransversal_mk_of_mem U σ (one_mem U),
    twoTransversal_mk_of_not_mem U σ (g := γ⁻¹ * 1) (by simpa using hγ)]
  group

theorem lWord_sigma_of_not_mem (hidx : U.index = 2) (hσ : σ ∉ U) {γ : G} (hγ : γ ∉ U) :
    lWord U (twoTransversal U σ) (QuotientGroup.mk σ) γ = σ⁻¹ * γ := by
  rw [lWord_def, MulAction.Quotient.smul_mk, smul_eq_mul, twoTransversal_mk_of_not_mem U σ hσ,
    twoTransversal_mk_of_mem U σ (g := γ⁻¹ * σ) (by
      simp [Subgroup.mul_mem_iff_of_index_two hidx, hσ, hγ])]
  group

end IndexTwo

section Corestriction

variable {G : Type*} [Group G] {U : Subgroup G} [U.FiniteIndex] {σ : G}
  (hidx : U.index = 2) (hσ : σ ∉ U)
  {N : Type*} [AddCommGroup N] [DistribMulAction G N]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include hidx hσ in
/-- The corestriction cochain for the transversal `{1, σ}` on an element of `U`. -/
theorem cochainsCor1_two_of_mem (f : U → N) {γ : G} (hγ : γ ∈ U) :
    cochainsCor1 G N U (twoTransversal U σ) (mk_twoTransversal hidx hσ) f γ =
      f ⟨γ, hγ⟩ + σ • f ⟨σ⁻¹ * γ * σ, conj_mem hidx hσ hγ⟩ := by
  have h1 : (⟨_, lWord_mem U (twoTransversal U σ) (mk_twoTransversal hidx hσ)
      (QuotientGroup.mk 1) γ⟩ : U) = ⟨γ, hγ⟩ := Subtype.ext (lWord_one_of_mem hγ)
  have h2 : (⟨_, lWord_mem U (twoTransversal U σ) (mk_twoTransversal hidx hσ)
      (QuotientGroup.mk σ) γ⟩ : U) = ⟨σ⁻¹ * γ * σ, conj_mem hidx hσ hγ⟩ :=
    Subtype.ext (lWord_sigma_of_mem hσ hγ)
  rw [cochainsCor1_apply, sum_quotient_two hidx hσ, h1, h2,
    twoTransversal_mk_of_mem U σ (one_mem U), twoTransversal_mk_of_not_mem U σ hσ, one_smul]

include hidx hσ in
/-- The corestriction cochain for the transversal `{1, σ}` off `U`. -/
theorem cochainsCor1_two_of_not_mem (f : U → N) {γ : G} (hγ : γ ∉ U) :
    cochainsCor1 G N U (twoTransversal U σ) (mk_twoTransversal hidx hσ) f γ =
      f ⟨γ * σ, mul_sigma_mem hidx hσ hγ⟩ + σ • f ⟨σ⁻¹ * γ, inv_sigma_mul_mem hidx hσ hγ⟩ := by
  have h1 : (⟨_, lWord_mem U (twoTransversal U σ) (mk_twoTransversal hidx hσ)
      (QuotientGroup.mk 1) γ⟩ : U) = ⟨γ * σ, mul_sigma_mem hidx hσ hγ⟩ :=
    Subtype.ext (lWord_one_of_not_mem hγ)
  have h2 : (⟨_, lWord_mem U (twoTransversal U σ) (mk_twoTransversal hidx hσ)
      (QuotientGroup.mk σ) γ⟩ : U) = ⟨σ⁻¹ * γ, inv_sigma_mul_mem hidx hσ hγ⟩ :=
    Subtype.ext (lWord_sigma_of_not_mem hidx hσ hγ)
  rw [cochainsCor1_apply, sum_quotient_two hidx hσ, h1, h2,
    twoTransversal_mk_of_mem U σ (one_mem U), twoTransversal_mk_of_not_mem U σ hσ, one_smul]

end Corestriction

section TwistPredicate

variable {G : Type*} [Group G] {U : Subgroup G} {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
  [DistribMulAction G M] [DistribMulAction G M']

/-- An additive map twisting the action by the quadratic character attached to `U`:
it is equivariant for `U` and anti-equivariant off `U`. -/
structure IsQuadraticTwist (U : Subgroup G) (ψ : M →+ M') : Prop where
  map_smul_of_mem : ∀ g ∈ U, ∀ m, ψ (g • m) = g • ψ m
  map_smul_of_not_mem : ∀ g ∉ U, ∀ m, ψ (g • m) = -(g • ψ m)

theorem IsQuadraticTwist.symm {ψ : M ≃+ M'} (h : IsQuadraticTwist U ψ.toAddMonoidHom) :
    IsQuadraticTwist U ψ.symm.toAddMonoidHom where
  map_smul_of_mem g hg m := by
    apply ψ.injective
    have := h.map_smul_of_mem g hg (ψ.symm m)
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, AddEquiv.apply_symm_apply]
      at this ⊢
    exact this.symm
  map_smul_of_not_mem g hg m := by
    apply ψ.injective
    have := h.map_smul_of_not_mem g hg (ψ.symm m)
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, AddEquiv.apply_symm_apply,
      map_neg] at this ⊢
    rw [this, neg_neg]


/-- A quadratic twist restricts to invariant subgroups. -/
theorem IsQuadraticTwist.restrict {ψ : M →+ M'} (hψ : IsQuadraticTwist U ψ)
    (S : AddSubgroup M) (T : AddSubgroup M') (hS : ∀ (g : G), ∀ a ∈ S, g • a ∈ S)
    (hT : ∀ (g : G), ∀ b ∈ T, g • b ∈ T) (ψ' : S →+ T) (hψ' : ∀ a, (ψ' a : M') = ψ a) :
    @IsQuadraticTwist G _ S T _ _ (S.restrictDistribMulAction hS) (T.restrictDistribMulAction hT)
      U ψ' :=
  @IsQuadraticTwist.mk G _ S T _ _ (S.restrictDistribMulAction hS) (T.restrictDistribMulAction hT)
    U ψ'
    (fun g hg a => Subtype.ext <| (hψ' _).trans <| (hψ.map_smul_of_mem g hg a).trans <|
      congrArg (g • ·) (hψ' a).symm)
    (fun g hg a => Subtype.ext <| (hψ' _).trans <| (hψ.map_smul_of_not_mem g hg a).trans <|
      congrArg (fun x => -(g • x)) (hψ' a).symm)

end TwistPredicate

section Descent

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} [U.FiniteIndex] (hU : IsOpen (U : Set G)) {σ : G}
  (hidx : U.index = 2) (hσ : σ ∉ U)

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
  {M' : Type*} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
  [IsTopologicalAddGroup M'] [DistribMulAction G M'] [ContinuousSMul G M']

/-- The map on `H¹(U, -)` induced by a quadratic twist, which is `U`-equivariant. -/
def twistH1 (ψ : M →+ M') (hψ : IsQuadraticTwist U ψ) : H1 U M →+ H1 U M' :=
  explicitMap1 U M U M' (ContinuousMonoidHom.id U) ψ continuous_of_discreteTopology
    (fun u m => by simpa [Subgroup.smul_def] using hψ.map_smul_of_mem u u.2 m)

theorem twistH1_mk (ψ : M →+ M') (hψ : IsQuadraticTwist U ψ) (c : Z1 U M) :
    twistH1 ψ hψ (c : H1 U M) =
      (cocyclesMap1 U M U M' (ContinuousMonoidHom.id U) ψ continuous_of_discreteTopology
        (fun u m => by simpa [Subgroup.smul_def] using hψ.map_smul_of_mem u u.2 m) c :
          H1 U M') :=
  explicitMap1_mk _ _ _ _ _ _ _ _ c

theorem twistH1_symm_twistH1 {ψ : M ≃+ M'} (hψ : IsQuadraticTwist U ψ.toAddMonoidHom)
    (x : H1 U M) : twistH1 ψ.symm.toAddMonoidHom hψ.symm (twistH1 ψ.toAddMonoidHom hψ x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [twistH1_mk, twistH1_mk]
    congr 1
    apply Subtype.ext
    funext u
    simp [cocyclesMap1_apply]

theorem twistH1_twistH1_symm {ψ : M ≃+ M'} (hψ : IsQuadraticTwist U ψ.toAddMonoidHom)
    (x : H1 U M') : twistH1 ψ.toAddMonoidHom hψ (twistH1 ψ.symm.toAddMonoidHom hψ.symm x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [twistH1_mk, twistH1_mk]
    congr 1
    apply Subtype.ext
    funext u
    simp [cocyclesMap1_apply]

include hidx hσ in
/-- A `G`-cocycle conjugated by `σ`. -/
theorem smul_cocycle_conj {A : Type*} [AddCommGroup A] [DistribMulAction G A] {a : G → A}
    (ha : groupCohomology.IsCocycle₁ a) (γ : G) :
    σ • a (σ⁻¹ * γ * σ) = γ • a σ + a γ - a σ := by
  have h := ha σ (σ⁻¹ * γ * σ)
  rw [show σ * (σ⁻¹ * γ * σ) = γ * σ by group, ha γ σ] at h
  rw [h]
  abel

/-- A `G`-cocycle translated by `σ⁻¹`. -/
theorem smul_cocycle_inv_mul {A : Type*} [AddCommGroup A] [DistribMulAction G A] {a : G → A}
    (ha : groupCohomology.IsCocycle₁ a) (γ : G) :
    σ • a (σ⁻¹ * γ) = a γ - a σ := by
  have h := ha σ (σ⁻¹ * γ)
  rw [show σ * (σ⁻¹ * γ) = γ by group] at h
  rw [h]
  abel

include hidx hσ in
/-- **Twisted corestriction kills restriction.** For a quadratic twist `φ`, the composite
`H¹(G, A) → H¹(U, A) → H¹(U, B) → H¹(G, B)` of restriction, the twist and corestriction is zero:
the norm `m ↦ φ m + σ φ (σ⁻¹ m)` of the twist vanishes. -/
theorem cor_twistH1_res {A B : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalAddGroup A] [DistribMulAction G A] [ContinuousSMul G A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [IsTopologicalAddGroup B] [DistribMulAction G B] [ContinuousSMul G B]
    (φ : A →+ B) (hφ : IsQuadraticTwist U φ) (x : H1 G A) :
    explicitCor1 G B U hU (twistH1 φ hφ (explicitRes1 G A U x)) = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitRes1_mk, twistH1_mk,
      explicitCor1_eq_transversal G B U (twoTransversal U σ) (mk_twoTransversal hidx hσ) hU,
      explicitCor1Transversal_mk, H1pi_eq_zero_iff, coe_cocyclesCor1, mem_B1_iff]
    have hc := (mem_Z1_iff.1 c.2).2
    refine ⟨-φ ((c : G → A) σ), fun γ => ?_⟩
    by_cases hγ : γ ∈ U
    · rw [cochainsCor1_two_of_mem hidx hσ _ hγ]
      change _ = φ ((c : G → A) γ) + σ • φ ((c : G → A) (σ⁻¹ * γ * σ))
      have h1 : σ • φ ((c : G → A) (σ⁻¹ * γ * σ)) = -φ (σ • (c : G → A) (σ⁻¹ * γ * σ)) := by
        rw [hφ.map_smul_of_not_mem σ hσ, neg_neg]
      rw [h1, smul_cocycle_conj hidx hσ hc γ, smul_neg]
      simp only [map_add, map_sub, hφ.map_smul_of_mem γ hγ]
      abel
    · rw [cochainsCor1_two_of_not_mem hidx hσ _ hγ]
      change _ = φ ((c : G → A) (γ * σ)) + σ • φ ((c : G → A) (σ⁻¹ * γ))
      have h1 : σ • φ ((c : G → A) (σ⁻¹ * γ)) = -φ (σ • (c : G → A) (σ⁻¹ * γ)) := by
        rw [hφ.map_smul_of_not_mem σ hσ, neg_neg]
      rw [h1, smul_cocycle_inv_mul hc γ, hc γ σ, smul_neg]
      have h2 : φ (γ • (c : G → A) σ) = -(γ • φ ((c : G → A) σ)) :=
        hφ.map_smul_of_not_mem γ hγ _
      simp only [map_add, map_sub, h2]
      abel

/-- **The quadratic descent map** `H¹(U, M) → H¹(G, M) × H¹(G, M')`: corestriction, and
corestriction after the quadratic twist. -/
def descentH1 (ψ : M ≃+ M') (hψ : IsQuadraticTwist U ψ.toAddMonoidHom) :
    H1 U M →+ H1 G M × H1 G M' :=
  (explicitCor1 G M U hU).prod ((explicitCor1 G M' U hU).comp (twistH1 ψ.toAddMonoidHom hψ))

/-- **The ascent map** `H¹(G, M) × H¹(G, M') → H¹(U, M)`: restriction, and restriction followed
by the inverse twist. -/
def ascentH1 (ψ : M ≃+ M') (hψ : IsQuadraticTwist U ψ.toAddMonoidHom) :
    H1 G M × H1 G M' →+ H1 U M :=
  (explicitRes1 G M U).comp (AddMonoidHom.fst _ _) +
    (twistH1 ψ.symm.toAddMonoidHom hψ.symm).comp
      ((explicitRes1 G M' U).comp (AddMonoidHom.snd _ _))

include hidx hσ in
/-- **Ascent after descent is multiplication by two** on `H¹(U, M)`: with the transversal
`{1, σ}`, restriction of corestriction is `c + σ_* c`, and the twisted term is `c - σ_* c`. -/
theorem ascentH1_descentH1 (ψ : M ≃+ M') (hψ : IsQuadraticTwist U ψ.toAddMonoidHom)
    (x : H1 U M) : ascentH1 ψ hψ (descentH1 hU ψ hψ x) = 2 • x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    simp only [descentH1, ascentH1, AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.prod_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd]
    rw [explicitCor1_eq_transversal G M U (twoTransversal U σ) (mk_twoTransversal hidx hσ) hU,
      explicitCor1_eq_transversal G M' U (twoTransversal U σ) (mk_twoTransversal hidx hσ) hU,
      twistH1_mk, explicitCor1Transversal_mk, explicitCor1Transversal_mk, explicitRes1_mk,
      explicitRes1_mk, twistH1_mk, ← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_nsmul]
    congr 1
    apply Subtype.ext
    funext u
    have hm := hψ.map_smul_of_not_mem σ hσ
    simp only [AddSubgroup.coe_add, Pi.add_apply, AddSubgroup.coe_nsmul, Pi.smul_apply,
      cocyclesMap1_apply, coe_cocyclesCor1]
    change cochainsCor1 G M U (twoTransversal U σ) (mk_twoTransversal hidx hσ) (c : U → M) (u : G) +
        ψ.symm (cochainsCor1 G M' U (twoTransversal U σ) (mk_twoTransversal hidx hσ)
          (fun v => ψ ((c : U → M) v)) (u : G)) = 2 • (c : U → M) u
    rw [cochainsCor1_two_of_mem hidx hσ _ u.2, cochainsCor1_two_of_mem hidx hσ _ u.2]
    have h1 : σ • ψ ((c : U → M) ⟨σ⁻¹ * u * σ, conj_mem hidx hσ u.2⟩) =
        -ψ (σ • (c : U → M) ⟨σ⁻¹ * u * σ, conj_mem hidx hσ u.2⟩) := by
      have := hm ((c : U → M) ⟨σ⁻¹ * u * σ, conj_mem hidx hσ u.2⟩)
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass] at this
      rw [this, neg_neg]
    rw [h1, map_add, map_neg, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, two_nsmul]
    abel

include hidx hσ in
/-- **Descent after ascent is multiplication by two** on `H¹(G, M) × H¹(G, M')`: corestriction
after restriction is the index, and the two mixed terms vanish by `cor_twistH1_res`. -/
theorem descentH1_ascentH1 (ψ : M ≃+ M') (hψ : IsQuadraticTwist U ψ.toAddMonoidHom)
    (y : H1 G M × H1 G M') : descentH1 hU ψ hψ (ascentH1 ψ hψ y) = 2 • y := by
  obtain ⟨a, b⟩ := y
  simp only [descentH1, ascentH1, AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
    AddMonoidHom.prod_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, map_add,
    twistH1_twistH1_symm, explicitCor1_comp_res1, hidx,
    cor_twistH1_res hU hidx hσ, Prod.mk_add_mk, add_zero, zero_add, Prod.smul_mk]

end Descent

section Involution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} [U.FiniteIndex] (hU : IsOpen (U : Set G)) {σ : G}
  (hidx : U.index = 2) (hσ : σ ∉ U)

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
  {M' : Type*} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
  [IsTopologicalAddGroup M'] [DistribMulAction G M'] [ContinuousSMul G M']

/-- Conjugation `u ↦ σ⁻¹ u σ` of the index-two subgroup `U`. -/
def conjU : U →ₜ* U where
  toFun u := ⟨σ⁻¹ * u * σ, conj_mem hidx hσ u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- **The action of `Gal(K/ℚ)` on `H¹(U, M)`**: the class of `c` goes to the class of
`u ↦ σ c(σ⁻¹ u σ)`. -/
def conjH1 : H1 U M →+ H1 U M :=
  explicitMap1 U M U M (conjU hidx hσ) (DistribSMul.toAddMonoidHom M σ)
    continuous_of_discreteTopology (fun u m => by
      change σ • ((σ⁻¹ * (u : G) * σ) • m) = (u : G) • (σ • m)
      rw [smul_smul, smul_smul]
      congr 1
      group)

include hidx hσ in
/-- **Restriction of corestriction is `1 + τ`**, for the action `τ` of the nontrivial element of
`Gal(K/ℚ)` on `H¹(U, M)`. -/
theorem res_cor_eq_add_conjH1 (x : H1 U M) :
    explicitRes1 G M U (explicitCor1 G M U hU x) = x + conjH1 hidx hσ x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitCor1_eq_transversal G M U (twoTransversal U σ) (mk_twoTransversal hidx hσ) hU,
      explicitCor1Transversal_mk, explicitRes1_mk, conjH1, explicitMap1_mk,
      ← QuotientAddGroup.mk_add]
    congr 1
    apply Subtype.ext
    funext u
    change cochainsCor1 G M U (twoTransversal U σ) (mk_twoTransversal hidx hσ) (c : U → M)
        (u : G) = (c : U → M) u + σ • (c : U → M) (conjU hidx hσ u)
    rw [cochainsCor1_two_of_mem hidx hσ _ u.2]
    rfl

include hidx hσ in
/-- **The twisted restriction of corestriction is `1 - τ`.** -/
theorem twist_res_cor_eq_sub_conjH1 (ψ : M ≃+ M') (hψ : IsQuadraticTwist U ψ.toAddMonoidHom)
    (x : H1 U M) :
    twistH1 ψ.symm.toAddMonoidHom hψ.symm
        (explicitRes1 G M' U (explicitCor1 G M' U hU (twistH1 ψ.toAddMonoidHom hψ x))) =
      x - conjH1 hidx hσ x := by
  have h := res_cor_eq_add_conjH1 hU hidx hσ (twistH1 ψ.toAddMonoidHom hψ x)
  rw [h, AddMonoidHom.map_add, twistH1_symm_twistH1, sub_eq_add_neg]
  congr 1
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [twistH1_mk, conjH1, explicitMap1_mk, twistH1_mk, conjH1, explicitMap1_mk,
      ← QuotientAddGroup.mk_neg]
    congr 1
    apply Subtype.ext
    funext u
    have hm := hψ.map_smul_of_not_mem σ hσ ((c : U → M) (conjU hidx hσ u))
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass] at hm
    change ψ.symm (σ • ψ ((c : U → M) (conjU hidx hσ u))) = -(σ • (c : U → M) (conjU hidx hσ u))
    rw [show σ • ψ ((c : U → M) (conjU hidx hσ u)) = -ψ (σ • (c : U → M) (conjU hidx hσ u)) by
      rw [hm, neg_neg], map_neg, AddEquiv.symm_apply_apply]

include hidx in
/-- **The action of `Gal(K/ℚ)` on `H¹(U, M)` is an involution**: conjugation by `σ² ∈ U` is
inner, so it acts trivially on cohomology. -/
theorem conjH1_conjH1 (x : H1 U M) : conjH1 hidx hσ (conjH1 hidx hσ x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [conjH1, explicitMap1_mk, explicitMap1_mk, H1pi_eq_iff, mem_B1_iff]
    have hc := (mem_Z1_iff.1 c.2).2
    let s : U := ⟨σ * σ, Subgroup.mul_self_mem_of_index_two hidx σ⟩
    refine ⟨(c : U → M) s, fun u => ?_⟩
    have hu : conjU hidx hσ (conjU hidx hσ u) = s⁻¹ * u * s :=
      Subtype.ext (by simp only [conjU, s, ContinuousMonoidHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have h1 := hc s (s⁻¹ * u * s)
    rw [show s * (s⁻¹ * u * s) = u * s by group, hc u s] at h1
    change u • (c : U → M) s - (c : U → M) s =
      σ • σ • (c : U → M) (conjU hidx hσ (conjU hidx hσ u)) - (c : U → M) u
    rw [hu, smul_smul]
    change u • (c : U → M) s - (c : U → M) s = s • (c : U → M) (s⁻¹ * u * s) - (c : U → M) u
    rw [eq_sub_of_add_eq h1.symm]
    abel

include hidx hσ in
/-- **Restricted classes are invariant** under the action of `Gal(K/ℚ)`. -/
theorem conjH1_res (x : H1 G M) :
    conjH1 hidx hσ (explicitRes1 G M U x) = explicitRes1 G M U x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitRes1_mk, conjH1, explicitMap1_mk, H1pi_eq_iff, mem_B1_iff]
    have hc := (mem_Z1_iff.1 c.2).2
    refine ⟨(c : G → M) σ, fun u => ?_⟩
    change (u : G) • (c : G → M) σ - (c : G → M) σ =
      σ • (c : G → M) (σ⁻¹ * (u : G) * σ) - (c : G → M) u
    rw [smul_cocycle_conj hidx hσ hc]
    abel

/-- **The twist anticommutes with the action of `Gal(K/ℚ)`.** -/
theorem conjH1_twistH1 (ψ : M →+ M') (hψ : IsQuadraticTwist U ψ) (x : H1 U M) :
    conjH1 hidx hσ (twistH1 ψ hψ x) = -twistH1 ψ hψ (conjH1 hidx hσ x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [twistH1_mk, conjH1, explicitMap1_mk, conjH1, explicitMap1_mk, twistH1_mk,
      ← QuotientAddGroup.mk_neg]
    congr 1
    apply Subtype.ext
    funext u
    change σ • ψ ((c : U → M) (conjU hidx hσ u)) = -ψ (σ • (c : U → M) (conjU hidx hσ u))
    rw [hψ.map_smul_of_not_mem σ hσ, neg_neg]

end Involution


section Twist

open WeierstrassCurve

variable {F : Type*} [Field F]

/-- The scaling change of variables `(x, y) ↦ (u² x, u³ y)`. -/
def scaleChange (u : Fˣ) : VariableChange F := ⟨u, 0, 0, 0⟩

/-- A curve with `a₁ = a₃ = 0` is the scaling change of variables of its twist by `u²`. -/
theorem scaleChange_smul_eq {W W' : WeierstrassCurve F} (u : Fˣ)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (h₁' : W'.a₁ = 0) (h₃' : W'.a₃ = 0)
    (h₂ : W'.a₂ = (u : F) ^ 2 * W.a₂) (h₄ : W'.a₄ = (u : F) ^ 4 * W.a₄)
    (h₆ : W'.a₆ = (u : F) ^ 6 * W.a₆) : scaleChange u • W' = W := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  ext
  · rw [variableChange_a₁, h₁', h₁]
    simp [scaleChange]
  · rw [variableChange_a₂, h₂, h₁']
    simp only [scaleChange, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · rw [variableChange_a₃, h₃', h₃, h₁']
    simp [scaleChange]
  · rw [variableChange_a₄, h₄, h₁', h₃']
    simp only [scaleChange, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · rw [variableChange_a₆, h₆, h₁', h₃']
    simp only [scaleChange, Units.val_inv_eq_inv_val]
    field_simp
    ring

theorem twist_nonsingular {W W' : WeierstrassCurve F} (u : Fˣ) (h : scaleChange u • W' = W)
    {x y : F} (hxy : W.toAffine.Nonsingular x y) :
    W'.toAffine.Nonsingular ((u : F) ^ 2 * x) ((u : F) ^ 3 * y) := by
  have hxy' : (scaleChange u • W').toAffine.Nonsingular x y := by rw [h]; exact hxy
  have := (Affine.variableChange_nonsingular W' (scaleChange u) x y).mpr hxy'
  simpa [scaleChange] using this

variable [DecidableEq F]

/-- **The twist isomorphism on points** `(x, y) ↦ (u² x, u³ y)`, for `W = scaleChange u • W'`. -/
def twistPointEquiv {W W' : WeierstrassCurve F} (u : Fˣ) (h : scaleChange u • W' = W) :
    W.toAffine.Point ≃+ W'.toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve F => V.toAffine.Point) h.symm).trans
    (Affine.Point.addEquivVariableChange W' (scaleChange u))

theorem twistPointEquiv_zero {W W' : WeierstrassCurve F} (u : Fˣ) (h : scaleChange u • W' = W) :
    twistPointEquiv u h 0 = 0 :=
  map_zero _

theorem twistPointEquiv_some {W W' : WeierstrassCurve F} (u : Fˣ) (h : scaleChange u • W' = W)
    {x y : F} (hxy : W.toAffine.Nonsingular x y) :
    twistPointEquiv u h (.some x y hxy) = .some _ _ (twist_nonsingular u h hxy) := by
  rw [twistPointEquiv, AddEquiv.trans_apply, AddEquiv.cast_apply,
    Affine.Point.cast_some h.symm, Affine.Point.coe_addEquivVariableChange,
    Affine.Point.equivVariableChange_some]
  simp [scaleChange]

end Twist

section TwistCoeff

open WeierstrassCurve

variable {K : Type*} [Field K] {E E' : WeierstrassCurve K} (u : (SeparableClosure K)ˣ)
  (h : scaleChange u • E'.baseChange (SeparableClosure K) = E.baseChange (SeparableClosure K))

open scoped Classical in
/-- **The twist isomorphism on Galois coefficients** `E(Kˢ) ≃ E'(Kˢ)`. -/
def twistCoeff : E.PointCoeff ≃+ E'.PointCoeff :=
  (E.pointCoeffEquiv.symm.trans (twistPointEquiv u h)).trans E'.pointCoeffEquiv

open scoped Classical in
theorem twistCoeff_pointCoeffEquiv (Q : (E.baseChange (SeparableClosure K)).toAffine.Point) :
    twistCoeff u h (E.pointCoeffEquiv Q) = E'.pointCoeffEquiv (twistPointEquiv u h Q) := by
  simp [twistCoeff]

open scoped Classical in
/-- The twist is equivariant for the automorphisms fixing `u`. -/
theorem twistCoeff_smul_of_fix (g : AbsoluteGaloisGroup K) (hg : g (u : SeparableClosure K) = u)
    (P : E.PointCoeff) : twistCoeff u h (g • P) = g • twistCoeff u h P := by
  obtain ⟨Q, rfl⟩ := E.pointCoeffEquiv.surjective P
  rw [smul_pointCoeffEquiv, twistCoeff_pointCoeffEquiv, twistCoeff_pointCoeffEquiv,
    smul_pointCoeffEquiv]
  congr 1
  rcases Q with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, twistPointEquiv_zero, map_zero]
  · rw [Affine.Point.map_some, twistPointEquiv_some, twistPointEquiv_some, Affine.Point.map_some]
    simp only [AlgEquiv.coe_toAlgHom, map_mul, map_pow, hg]

open scoped Classical in
/-- The twist is anti-equivariant for the automorphisms negating `u`. -/
theorem twistCoeff_smul_of_neg (h₁' : E'.a₁ = 0) (h₃' : E'.a₃ = 0) (g : AbsoluteGaloisGroup K)
    (hg : g (u : SeparableClosure K) = -u) (P : E.PointCoeff) :
    twistCoeff u h (g • P) = -(g • twistCoeff u h P) := by
  obtain ⟨Q, rfl⟩ := E.pointCoeffEquiv.surjective P
  rw [smul_pointCoeffEquiv, twistCoeff_pointCoeffEquiv, twistCoeff_pointCoeffEquiv,
    smul_pointCoeffEquiv, ← map_neg]
  congr 1
  rcases Q with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, twistPointEquiv_zero, map_zero, neg_zero]
  · rw [Affine.Point.map_some, twistPointEquiv_some, twistPointEquiv_some, Affine.Point.map_some,
      Affine.Point.neg_some]
    simp only [AlgEquiv.coe_toAlgHom, map_mul, map_pow, hg,
      Affine.negY, map_a₁, map_a₃, baseChange, h₁', h₃', map_zero, zero_mul, sub_zero]
    congr 1 <;> ring

open scoped Classical in
/-- **The twist commutes with localization**: along an embedding `τ : Kˢ → Lˢ`, the twist by
`u` corresponds to the twist by `τ u`. -/
theorem pointCoeffBaseChange_twistCoeff {L : Type*} [Field L] [Algebra K L]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L) (u' : (SeparableClosure L)ˣ)
    (hu' : (u' : SeparableClosure L) = τ u)
    (h' : scaleChange u' • (E'.baseChange L).baseChange (SeparableClosure L) =
      (E.baseChange L).baseChange (SeparableClosure L)) (P : E.PointCoeff) :
    E'.pointCoeffBaseChange τ (twistCoeff u h P) =
      twistCoeff u' h' (E.pointCoeffBaseChange τ P) := by
  obtain ⟨Q, rfl⟩ := E.pointCoeffEquiv.surjective P
  rcases Q with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero, map_zero, map_zero]
  · rw [twistCoeff_pointCoeffEquiv, twistPointEquiv_some, pointCoeffBaseChange_pointCoeffEquiv_some,
      pointCoeffBaseChange_pointCoeffEquiv_some, twistCoeff_pointCoeffEquiv, twistPointEquiv_some]
    congr 1
    simp only [map_mul, map_pow, hu']

/-- `θL` corresponds to `θ` under the coordinate maps along `τ : Kˢ → Lˢ`. -/
def Intertwines {L : Type*} [Field L] [Algebra K L] {E₁ E₂ : WeierstrassCurve K}
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L) (θ : E₁.PointCoeff →+ E₂.PointCoeff)
    (θL : (E₁.baseChange L).PointCoeff →+ (E₂.baseChange L).PointCoeff) : Prop :=
  ∀ P, E₂.pointCoeffBaseChange τ (θ P) = θL (E₁.pointCoeffBaseChange τ P)

theorem intertwines_twistCoeff {L : Type*} [Field L] [Algebra K L]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L) (u' : (SeparableClosure L)ˣ)
    (hu' : (u' : SeparableClosure L) = τ u)
    (h' : scaleChange u' • (E'.baseChange L).baseChange (SeparableClosure L) =
      (E.baseChange L).baseChange (SeparableClosure L)) :
    Intertwines τ (twistCoeff u h).toAddMonoidHom (twistCoeff u' h').toAddMonoidHom :=
  fun P => pointCoeffBaseChange_twistCoeff u h τ u' hu' h' P

theorem Intertwines.symm {L : Type*} [Field L] [Algebra K L] {E₁ E₂ : WeierstrassCurve K}
    {τ : SeparableClosure K →ₐ[K] SeparableClosure L} {θ : E₁.PointCoeff ≃+ E₂.PointCoeff}
    {θL : (E₁.baseChange L).PointCoeff ≃+ (E₂.baseChange L).PointCoeff}
    (hθ : Intertwines τ θ.toAddMonoidHom θL.toAddMonoidHom) :
    Intertwines τ θ.symm.toAddMonoidHom θL.symm.toAddMonoidHom := fun P => by
  have := hθ (θ.symm P)
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    AddEquiv.apply_symm_apply] at this ⊢
  rw [AddEquiv.eq_symm_apply, ← this]

/-- The twist by `u` is a quadratic twist for any subgroup fixing `u` whose complement negates
`u`. -/
theorem isQuadraticTwist_twistCoeff (U : Subgroup (AbsoluteGaloisGroup K))
    (hfix : ∀ g ∈ U, g (u : SeparableClosure K) = u)
    (hneg : ∀ g ∉ U, g (u : SeparableClosure K) = -u) (h₁' : E'.a₁ = 0) (h₃' : E'.a₃ = 0) :
    IsQuadraticTwist U (twistCoeff u h).toAddMonoidHom where
  map_smul_of_mem g hg P := twistCoeff_smul_of_fix u h g (hfix g hg) P
  map_smul_of_not_mem g hg P := twistCoeff_smul_of_neg u h h₁' h₃' g (hneg g hg) P

end TwistCoeff

section QuadraticField

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

/-- The structure map `K → Kˢ`, with the algebra structure used by the Galois coefficient
modules. -/
def sepMap (K : Type*) [Field K] : K →+* SeparableClosure K := algebraMap K (SeparableClosure K)

/-- **The absolute Galois group of `K = ℚ(r)`**, for `r ∈ ℚˢ`, as the subgroup of
`G_ℚ = Gal(ℚˢ/ℚ)` fixing `r`; `ℚˢ` is a separable closure of `K`. -/
def galK (r : SeparableClosure ℚ) : Subgroup (AbsoluteGaloisGroup ℚ) :=
  MulAction.stabilizer (AbsoluteGaloisGroup ℚ) r

theorem mem_galK {r : SeparableClosure ℚ} {g : AbsoluteGaloisGroup ℚ} : g ∈ galK r ↔ g r = r :=
  MulAction.mem_stabilizer_iff

theorem isOpen_galK (r : SeparableClosure ℚ) : IsOpen (galK r : Set (AbsoluteGaloisGroup ℚ)) :=
  stabilizer_isOpen_of_isIntegral r

variable {d : ℚ} {r : SeparableClosure ℚ}

theorem apply_eq_or_eq_neg (hr : r ^ 2 = sepMap ℚ d) (g : AbsoluteGaloisGroup ℚ) :
    g r = r ∨ g r = -r := by
  have h : (g r) ^ 2 = r ^ 2 := by rw [← map_pow, hr, sepMap, AlgEquiv.commutes]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

theorem apply_eq_neg_of_not_mem (hr : r ^ 2 = sepMap ℚ d) {g : AbsoluteGaloisGroup ℚ}
    (hg : g ∉ galK r) : g r = -r :=
  (apply_eq_or_eq_neg hr g).resolve_left (fun h => hg (mem_galK.mpr h))

theorem ne_zero_of_moves {σ : AbsoluteGaloisGroup ℚ} (hσ : σ ∉ galK r) : r ≠ 0 := by
  rintro rfl
  exact hσ (mem_galK.mpr (map_zero σ))

theorem neg_ne_self_of_moves {σ : AbsoluteGaloisGroup ℚ} (hσ : σ ∉ galK r) : -r ≠ r := by
  intro h
  have h2 : (2 : SeparableClosure ℚ) * r = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero h3
  · exact ne_zero_of_moves hσ h3

theorem galK_index (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ}
    (hσ : σ ∉ galK r) : (galK r).index = 2 := by
  refine Subgroup.index_eq_two_iff.mpr ⟨σ, fun b => ?_⟩
  have hσr := apply_eq_neg_of_not_mem hr hσ
  have hbσ : (b * σ) r = -(b r) := by
    rw [AlgEquiv.mul_apply, hσr, map_neg]
  rw [mem_galK, mem_galK, hbσ]
  rcases apply_eq_or_eq_neg hr b with hb | hb
  · rw [hb]
    exact Or.inr ⟨rfl, neg_ne_self_of_moves hσ⟩
  · rw [hb, neg_neg]
    exact Or.inl ⟨rfl, neg_ne_self_of_moves hσ⟩

theorem galK_finiteIndex (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ}
    (hσ : σ ∉ galK r) : (galK r).FiniteIndex :=
  ⟨by rw [galK_index hr hσ]; decide⟩

/-- A curve with `a₁ = a₃ = 0` is the scaling change of variables of its quadratic twist by `d`,
over any field in which `d` is the square of a unit. -/
theorem qtwist_map_scaleChange {F : Type*} [Field F] {E : WeierstrassCurve ℚ}
    (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) (f : ℚ →+* F) (u : Fˣ) (hu : (u : F) ^ 2 = f d) :
    scaleChange u • (qtwist E d).map f = E.map f := by
  have e₂ : (qtwist E d).a₂ = d * E.a₂ := by
    simp only [qtwist, b₂, h₁]
    ring
  have e₄ : (qtwist E d).a₄ = d ^ 2 * E.a₄ := by
    simp only [qtwist, b₄, h₁, h₃]
    ring
  have e₆ : (qtwist E d).a₆ = d ^ 3 * E.a₆ := by
    simp only [qtwist, b₆, h₃]
    ring
  apply scaleChange_smul_eq u
  · simp [h₁]
  · simp [h₃]
  · simp [qtwist]
  · simp [qtwist]
  · rw [map_a₂, map_a₂, e₂, map_mul, hu]
  · rw [map_a₄, map_a₄, e₄, map_mul, map_pow, ← hu]
    ring
  · rw [map_a₆, map_a₆, e₆, map_mul, map_pow, ← hu]
    ring

end QuadraticField

section GlobalTwist

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

variable {E : WeierstrassCurve ℚ} (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) {d : ℚ}
  {r : SeparableClosure ℚ} (hr : r ^ 2 = sepMap ℚ d)
  {σ : AbsoluteGaloisGroup ℚ} (hσ : σ ∉ galK r)

/-- The root `r` as a unit of `ℚˢ`. -/
def rootUnit : (SeparableClosure ℚ)ˣ := Units.mk0 r (ne_zero_of_moves hσ)

include hr in
theorem rootUnit_sq : ((rootUnit hσ : (SeparableClosure ℚ)ˣ) : SeparableClosure ℚ) ^ 2 =
    sepMap ℚ d := by
  rw [rootUnit, Units.val_mk0, hr]

/-- **The twist `E(ℚˢ) ≃ E^{(d)}(ℚˢ)`**, `(x, y) ↦ (d x, d r y)`, over `ℚˢ`. -/
def pointTwist : E.PointCoeff ≃+ (qtwist E d).PointCoeff :=
  twistCoeff (rootUnit hσ)
    (qtwist_map_scaleChange h₁ h₃ (sepMap ℚ) _ (rootUnit_sq hr hσ))

theorem qtwist_a₁ (E : WeierstrassCurve ℚ) : (qtwist E d).a₁ = 0 := rfl

theorem qtwist_a₃ (E : WeierstrassCurve ℚ) : (qtwist E d).a₃ = 0 := rfl

theorem isQuadraticTwist_pointTwist :
    IsQuadraticTwist (galK r) (pointTwist h₁ h₃ hr hσ).toAddMonoidHom :=
  isQuadraticTwist_twistCoeff _ _ (galK r)
    (fun _ hg => by rw [rootUnit, Units.val_mk0]; exact mem_galK.mp hg)
    (fun _ hg => by rw [rootUnit, Units.val_mk0]; exact apply_eq_neg_of_not_mem hr hg) rfl rfl

theorem mem_twoPower_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    {P : A} (hP : P ∈ AddCommGroup.primaryComponent A 2) :
    e P ∈ AddCommGroup.primaryComponent B 2 := by
  obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.mp hP
  exact AddCommGroup.mem_primaryComponent.mpr ⟨n, by rw [← map_nsmul, hn, map_zero]⟩

/-- **The twist on two-primary torsion** `E(ℚˢ)[2^∞] ≃ E^{(d)}(ℚˢ)[2^∞]`. -/
def twoPowerTwist : TwoPowerCoeff E ≃+ TwoPowerCoeff (qtwist E d) where
  toFun P := ⟨pointTwist h₁ h₃ hr hσ P.1, mem_twoPower_of_addEquiv _ P.2⟩
  invFun P := ⟨(pointTwist h₁ h₃ hr hσ).symm P.1, mem_twoPower_of_addEquiv _ P.2⟩
  left_inv P := Subtype.ext ((pointTwist h₁ h₃ hr hσ).symm_apply_apply P.1)
  right_inv P := Subtype.ext ((pointTwist h₁ h₃ hr hσ).apply_symm_apply P.1)
  map_add' P Q := Subtype.ext (map_add (pointTwist h₁ h₃ hr hσ) P.1 Q.1)

theorem coe_twoPowerTwist (P : TwoPowerCoeff E) :
    ((twoPowerTwist h₁ h₃ hr hσ P : TwoPowerCoeff (qtwist E d)) : (qtwist E d).PointCoeff) =
      pointTwist h₁ h₃ hr hσ (P : E.PointCoeff) :=
  rfl

theorem coe_twoPowerTwist_symm (P : TwoPowerCoeff (qtwist E d)) :
    (((twoPowerTwist h₁ h₃ hr hσ).symm P : TwoPowerCoeff E) : E.PointCoeff) =
      (pointTwist h₁ h₃ hr hσ).symm (P : (qtwist E d).PointCoeff) :=
  rfl

theorem isQuadraticTwist_twoPowerTwist :
    IsQuadraticTwist (galK r) (twoPowerTwist h₁ h₃ hr hσ).toAddMonoidHom :=
  (isQuadraticTwist_pointTwist h₁ h₃ hr hσ).restrict _ _ (fun σ _ => smul_mem_twoPowerCoeff σ)
    (fun σ _ => smul_mem_twoPowerCoeff σ) _ (fun _ => rfl)

end GlobalTwist

section Localization

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

/-- An embedding `Kˢ → Lˢ` of separable closures over `K`, for a field extension `L/K`. -/
abbrev SepEmb (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  SeparableClosure K →ₐ[K] SeparableClosure L

/-- **Restriction to a completion does not depend on the embedding of separable closures**
(the conjugation argument of Neukirch--Schmidt--Wingberg, I §5). -/
theorem pointRes_eq_pointRes {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : WeierstrassCurve K) (τ τ' : SepEmb K L) : E.pointRes τ = E.pointRes τ' := by
  obtain ⟨h, rfl⟩ := τ.exists_comp_eq_of_normal τ'
  rw [pointRes_eq_explicitMap1, pointRes_eq_explicitMap1]
  exact (explicitMap1_eq_of_conj _ _ _ _ _ _ _ _ _ _ h (absoluteGaloisGroupMap_comp τ h)
    (E.pointCoeffBaseChange_comp τ h)).symm

variable {L : Type*} [Field L] [Algebra ℚ L] (r : SeparableClosure ℚ) (τ : SepEmb ℚ L)

/-- **The decomposition group** at the place of `K = ℚ(r)` determined by `τ : ℚˢ → Lˢ`: the
elements of `G_L` whose image in `G_ℚ` fixes `r`, i.e. `Gal(Lˢ / L(τ r))`. -/
def decomp : Subgroup (AbsoluteGaloisGroup L) :=
  (galK r).comap (absoluteGaloisGroupMap τ).toMonoidHom

theorem mem_decomp {h : AbsoluteGaloisGroup L} :
    h ∈ decomp r τ ↔ absoluteGaloisGroupMap τ h ∈ galK r :=
  Iff.rfl

theorem isOpen_decomp : IsOpen (decomp r τ : Set (AbsoluteGaloisGroup L)) :=
  (isOpen_galK r).preimage (absoluteGaloisGroupMap τ).continuous

/-- The decomposition group maps to `G_K`. -/
def decompHom : decomp r τ →ₜ* galK r where
  toMonoidHom := ((absoluteGaloisGroupMap τ).toMonoidHom.comp (decomp r τ).subtype).codRestrict
    (galK r) fun x => x.2
  continuous_toFun := ((absoluteGaloisGroupMap τ).continuous.comp continuous_subtype_val).subtype_mk _

theorem coe_decompHom (h : decomp r τ) :
    (decompHom r τ h : AbsoluteGaloisGroup ℚ) = absoluteGaloisGroupMap τ h :=
  rfl

/-- **Localization at the place of `K = ℚ(r)` determined by `τ`**: the map
`H¹(G_K, E(ℚˢ)) → H¹(G_{K_w}, E(Lˢ))` along the decomposition group and the coordinate map
`τ : E(ℚˢ) → E(Lˢ)`. -/
def locK (E : WeierstrassCurve ℚ) :
    H1 (galK r) E.PointCoeff →+ H1 (decomp r τ) (E.baseChange L).PointCoeff :=
  explicitMap1 (galK r) E.PointCoeff (decomp r τ) (E.baseChange L).PointCoeff (decompHom r τ)
    (E.pointCoeffBaseChange τ) continuous_of_discreteTopology
    (fun h m => @id (E.pointCoeffBaseChange τ (decompHom r τ h • m) =
      h • E.pointCoeffBaseChange τ m) (E.pointCoeffBaseChange_smul τ (h : AbsoluteGaloisGroup L) m))

variable {r} in
/-- **The Selmer structure of `Sha(E/K)` at a family of places of `K`**, in the sense of
`SelmerStructure`: for each embedding `τ i : ℚˢ → (L i)ˢ`, the decomposition group, the
coordinate map `E(ℚˢ) → E((L i)ˢ)`, and the zero local condition. -/
def shaStructureK (E : WeierstrassCurve ℚ) {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)]
    [∀ i, Algebra ℚ (L i)] (τ : ∀ i, SepEmb ℚ (L i)) :
    SelmerStructure (galK r) E.PointCoeff (fun i => decomp r (τ i))
      (fun i => (E.baseChange (L i)).PointCoeff) where
  groupHom i := decompHom r (τ i)
  coeffHom i := E.pointCoeffBaseChange (τ i)
  continuous_coeffHom _ := continuous_of_discreteTopology
  coeffHom_smul i h m := @id (E.pointCoeffBaseChange (τ i) (decompHom r (τ i) h • m) =
      h • E.pointCoeffBaseChange (τ i) m)
    (E.pointCoeffBaseChange_smul (τ i) (h : AbsoluteGaloisGroup (L i)) m)
  localCondition _ := ⊥

theorem shaStructureK_localization (E : WeierstrassCurve ℚ) {ι : Type*} {L : ι → Type*}
    [∀ i, Field (L i)] [∀ i, Algebra ℚ (L i)] (τ : ∀ i, SepEmb ℚ (L i)) (i : ι) :
    (shaStructureK (r := r) E τ).localization i = locK r (τ i) E :=
  rfl

/-- **`Sha(E/K)` for `K = ℚ(r)`**: the Selmer group of the Selmer structure with zero local
conditions at every place of `K`, that is, at every embedding of `ℚˢ` into `ℚ_pˢ` for every
prime `p` and into `ℝˢ`. This is the definition of `sha` with `ℚ` replaced by `K`. -/
def shaK (E : WeierstrassCurve ℚ) : AddSubgroup (H1 (galK r) E.PointCoeff) :=
  (shaStructureK (r := r) E
      (fun i : (p : Nat.Primes) × SepEmb ℚ (QpCompletion p) => i.2)).selmerGroup ⊓
    (shaStructureK (r := r) E (fun τ : SepEmb ℚ (RealCompletion ()) => τ)).selmerGroup

theorem mem_shaK {E : WeierstrassCurve ℚ} {z : H1 (galK r) E.PointCoeff} :
    z ∈ shaK r E ↔ (∀ (p : Nat.Primes) (τ : SepEmb ℚ (QpCompletion p)), locK r τ E z = 0) ∧
      ∀ τ : SepEmb ℚ (RealCompletion ()), locK r τ E z = 0 := by
  simp only [shaK, AddSubgroup.mem_inf, SelmerStructure.mem_selmerGroup_iff,
    shaStructureK_localization]
  exact and_congr ⟨fun h p τ => h ⟨p, τ⟩, fun h i => h i.1 i.2⟩ Iff.rfl

/-- The inclusion `E(ℚˢ)[2^∞] → E(ℚˢ)` on `H¹(G_K, -)`. -/
def inclK (E : WeierstrassCurve ℚ) :
    H1 (galK r) (TwoPowerCoeff E) →+ H1 (galK r) E.PointCoeff :=
  explicitMap1 (galK r) (TwoPowerCoeff E) (galK r) E.PointCoeff (ContinuousMonoidHom.id _)
    (twoPowerCoeffIncl E).toAddMonoidHom continuous_of_discreteTopology
    (fun u P => @id ((twoPowerCoeffIncl E).toAddMonoidHom ((ContinuousMonoidHom.id (galK r)) u • P) =
      u • (twoPowerCoeffIncl E).toAddMonoidHom P)
      ((twoPowerCoeffIncl E).map_smul (u : AbsoluteGaloisGroup ℚ) P))

/-- **The two-primary Selmer group `Sel_{2^∞}(E/K)` of `E` over `K = ℚ(r)`**: the classes in
`H¹(G_K, E(ℚˢ)[2^∞])` whose image in `H¹(G_K, E(ℚˢ))` lies in `Sha(E/K)`. This is the definition
of `selmerTwoPower` with `ℚ` replaced by `K`: local triviality at every place of `K`, each place
given through a decomposition group (Silverman X.4). -/
def selmerK (E : WeierstrassCurve ℚ) : AddSubgroup (H1 (galK r) (TwoPowerCoeff E)) :=
  (shaK r E).comap (inclK r E)

theorem mem_selmerK {E : WeierstrassCurve ℚ} {x : H1 (galK r) (TwoPowerCoeff E)} :
    x ∈ selmerK r E ↔ inclK r E x ∈ shaK r E :=
  Iff.rfl

/-- Localization after restriction is restriction to the decomposition group of the global
localization. -/
theorem locK_res (E : WeierstrassCurve ℚ) (y : H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff) :
    locK r τ E (explicitRes1 (AbsoluteGaloisGroup ℚ) E.PointCoeff (galK r) y) =
      explicitRes1 (AbsoluteGaloisGroup L) (E.baseChange L).PointCoeff (decomp r τ)
        (E.pointRes τ y) := by
  rw [locK, explicitRes1_eq_explicitMap1, explicitRes1_eq_explicitMap1, pointRes_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; rfl) y

/-- **Restriction carries `Sha(E/ℚ)` into `Sha(E/K)`.** -/
theorem res_mem_shaK {E : WeierstrassCurve ℚ} {y : H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff}
    (hy : y ∈ sha E) : explicitRes1 (AbsoluteGaloisGroup ℚ) E.PointCoeff (galK r) y ∈ shaK r E := by
  rw [sha, AddSubgroup.mem_inf, mem_shafarevichTateGroup_iff,
    mem_shafarevichTateGroup_iff] at hy
  rw [mem_shaK]
  refine ⟨fun p τ => ?_, fun τ => ?_⟩
  · rw [locK_res, pointRes_eq_pointRes E τ (embFin p), hy.1 p, map_zero]
  · rw [locK_res, pointRes_eq_pointRes E τ (embInf ()), hy.2 (), map_zero]

end Localization

section CorestrictionLocal

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

variable {L : Type*} [Field L] [Algebra ℚ L] {d : ℚ} {r : SeparableClosure ℚ}
  (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ} (hσ : σ ∉ galK r)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include hr hσ in
/-- **Corestriction at a split place.** If the local Galois group maps into `G_K`, the
localization of a corestriction is the sum of the localizations at the two places of `K` above,
given by `τ` and `τ ∘ σ`. -/
theorem pointRes_cor_of_split [(galK r).FiniteIndex] (E : WeierstrassCurve ℚ) (τ : SepEmb ℚ L)
    (hsplit : ∀ γ : AbsoluteGaloisGroup L, absoluteGaloisGroupMap τ γ ∈ galK r)
    (z : H1 (galK r) E.PointCoeff) (hz₁ : locK r τ E z = 0)
    (hz₂ : locK r (τ.comp (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ)) E z = 0) :
    E.pointRes τ (explicitCor1 _ _ (galK r) (isOpen_galK r) z) = 0 := by
  have hidx := galK_index hr hσ
  induction z using QuotientAddGroup.induction_on with
  | H c =>
    rw [locK, explicitMap1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hz₁ hz₂
    obtain ⟨m₁, hm₁⟩ := hz₁
    obtain ⟨m₂, hm₂⟩ := hz₂
    rw [explicitCor1_eq_transversal _ _ (galK r) (twoTransversal (galK r) σ)
        (mk_twoTransversal hidx hσ) (isOpen_galK r),
      explicitCor1Transversal_mk, pointRes_eq_explicitMap1, explicitMap1_mk, H1pi_eq_zero_iff,
      mem_B1_iff]
    refine ⟨m₁ + m₂, fun γ => ?_⟩
    rw [cocyclesMap1_apply, coe_cocyclesCor1, cochainsCor1_two_of_mem hidx hσ _ (hsplit γ),
      map_add]
    have hconj : absoluteGaloisGroupMap (τ.comp (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ))
        γ = σ⁻¹ * absoluteGaloisGroupMap τ γ * σ := absoluteGaloisGroupMap_comp τ σ γ
    have hmem : absoluteGaloisGroupMap (τ.comp (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ))
        γ ∈ galK r := by
      rw [hconj]
      exact conj_mem hidx hσ (hsplit γ)
    have e₁ := hm₁ ⟨γ, hsplit γ⟩
    have e₂ := hm₂ ⟨γ, hmem⟩
    rw [cocyclesMap1_apply] at e₁ e₂
    have hc₂ : (c : galK r → E.PointCoeff)
        (decompHom r (τ.comp (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ)) ⟨γ, hmem⟩) =
        (c : galK r → E.PointCoeff) ⟨σ⁻¹ * absoluteGaloisGroupMap τ γ * σ,
          conj_mem hidx hσ (hsplit γ)⟩ :=
      congrArg _ (Subtype.ext hconj)
    rw [hc₂, pointCoeffBaseChange_comp] at e₂
    change γ • (m₁ + m₂) - (m₁ + m₂) = _
    rw [smul_add]
    change γ • m₁ - m₁ = _ at e₁
    change γ • m₂ - m₂ = _ at e₂
    rw [show γ • m₁ + γ • m₂ - (m₁ + m₂) = (γ • m₁ - m₁) + (γ • m₂ - m₂) by abel, e₁, e₂]
    rfl

include hr hσ in
/-- **Corestriction at a non-split place.** If some element of the local Galois group maps
outside `G_K`, the cosets correspond and localization of a corestriction is the local
corestriction of the localization at the unique place above. -/
theorem pointRes_cor_of_not_split [(galK r).FiniteIndex] (E : WeierstrassCurve ℚ)
    (τ : SepEmb ℚ L) {γ₀ : AbsoluteGaloisGroup L} (hγ₀ : absoluteGaloisGroupMap τ γ₀ ∉ galK r)
    (z : H1 (galK r) E.PointCoeff) (hz : locK r τ E z = 0) :
    E.pointRes τ (explicitCor1 _ _ (galK r) (isOpen_galK r) z) = 0 := by
  have hidx := galK_index hr hσ
  have hVidx : (decomp r τ).index = 2 := by
    refine Subgroup.index_eq_two_iff.mpr ⟨γ₀, fun b => ?_⟩
    rw [mem_decomp, mem_decomp, map_mul, Subgroup.mul_mem_iff_of_index_two hidx]
    by_cases hb : absoluteGaloisGroupMap τ b ∈ galK r
    · exact Or.inr ⟨hb, fun h => hγ₀ (h.mp hb)⟩
    · exact Or.inl ⟨⟨fun h => absurd h hb, fun h => absurd h hγ₀⟩, hb⟩
  have : (decomp r τ).FiniteIndex := ⟨by rw [hVidx]; decide⟩
  let e₀ : AbsoluteGaloisGroup L ⧸ decomp r τ → AbsoluteGaloisGroup ℚ ⧸ galK r :=
    Quotient.map' (absoluteGaloisGroupMap τ) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      rw [← map_inv, ← map_mul]
      exact hab)
  have he₀ : ∀ h : AbsoluteGaloisGroup L, e₀ (h : AbsoluteGaloisGroup L ⧸ decomp r τ) =
      (absoluteGaloisGroupMap τ h : AbsoluteGaloisGroup ℚ ⧸ galK r) := fun _ => rfl
  have hbij : Function.Bijective e₀ := by
    constructor
    · intro q₁ q₂ hq
      induction q₁ using QuotientGroup.induction_on with
      | H a =>
        induction q₂ using QuotientGroup.induction_on with
        | H b =>
          rw [he₀, he₀, QuotientGroup.eq] at hq
          rw [QuotientGroup.eq, mem_decomp, map_mul, map_inv]
          exact hq
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        by_cases hg : g ∈ galK r
        · refine ⟨((1 : AbsoluteGaloisGroup L) : AbsoluteGaloisGroup L ⧸ decomp r τ), ?_⟩
          rw [he₀, map_one]
          exact ((mk_eq_mk_one_iff _).mpr hg).symm
        · refine ⟨(γ₀ : AbsoluteGaloisGroup L ⧸ decomp r τ), ?_⟩
          rw [he₀, mk_eq_mk_sigma hidx hσ hγ₀, mk_eq_mk_sigma hidx hσ hg]
  rw [pointRes_eq_explicitMap1, explicitCor1_pullback (galK r) (decomp r τ)
    (absoluteGaloisGroupMap τ) (decompHom r τ) (fun _ => rfl) (Equiv.ofBijective e₀ hbij)
    he₀ (E.pointCoeffBaseChange τ) continuous_of_discreteTopology
    (E.pointCoeffBaseChange_smul τ) (isOpen_galK r) (isOpen_decomp r τ) z]
  show explicitCor1 _ _ (decomp r τ) (isOpen_decomp r τ) (locK r τ E z) = 0
  rw [hz, map_zero]

include hr hσ in
/-- **Corestriction preserves local triviality**: a class of `H¹(G_K, E(ℚˢ))` trivial at every
place of `K` above the place of `L` has corestriction trivial at that place. -/
theorem pointRes_cor_eq_zero [(galK r).FiniteIndex] (E : WeierstrassCurve ℚ) (τ : SepEmb ℚ L)
    (z : H1 (galK r) E.PointCoeff) (hz : ∀ τ' : SepEmb ℚ L, locK r τ' E z = 0) :
    E.pointRes τ (explicitCor1 _ _ (galK r) (isOpen_galK r) z) = 0 := by
  by_cases hsplit : ∀ γ : AbsoluteGaloisGroup L, absoluteGaloisGroupMap τ γ ∈ galK r
  · exact pointRes_cor_of_split hr hσ E τ hsplit z (hz τ) (hz _)
  · obtain ⟨γ₀, hγ₀⟩ := not_forall.mp hsplit
    exact pointRes_cor_of_not_split hr hσ E τ hγ₀ z (hz τ)

end CorestrictionLocal

section CorestrictionSha

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

variable {d : ℚ} {r : SeparableClosure ℚ}
  (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ} (hσ : σ ∉ galK r)

include hr hσ in
/-- **Corestriction carries `Sha(E/K)` into `Sha(E/ℚ)`.** -/
theorem cor_mem_sha [(galK r).FiniteIndex] {E : WeierstrassCurve ℚ}
    {z : H1 (galK r) E.PointCoeff} (hz : z ∈ shaK r E) :
    explicitCor1 _ _ (galK r) (isOpen_galK r) z ∈ sha E := by
  rw [mem_shaK] at hz
  rw [sha, AddSubgroup.mem_inf, mem_shafarevichTateGroup_iff, mem_shafarevichTateGroup_iff]
  refine ⟨fun p => pointRes_cor_eq_zero hr hσ E (embFin p) z (hz.1 p), fun u => ?_⟩
  cases u
  exact pointRes_cor_eq_zero hr hσ E (embInf ()) z hz.2

end CorestrictionSha

section TwistLocal

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

/-- The structure maps of a tower `K → L → Lˢ`, compared through an embedding `Kˢ → Lˢ`. -/
theorem sepEmb_sepMap {K L : Type*} [Field K] [Field L] [Algebra K L] (τ : SepEmb K L) (x : K) :
    τ (sepMap K x) = ((algebraMap L (SeparableClosure L)).comp (algebraMap K L)) x := by
  rw [sepMap, AlgHom.commutes, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply K L (SeparableClosure L)]

variable {L : Type*} [Field L] [Algebra ℚ L] (r : SeparableClosure ℚ) (τ : SepEmb ℚ L)

/-- **Localization commutes with coefficient maps** compatible with the coordinate maps. -/
theorem locK_explicitMap1 {E₁ E₂ : WeierstrassCurve ℚ} (θ : E₁.PointCoeff →+ E₂.PointCoeff)
    (θL : (E₁.baseChange L).PointCoeff →+ (E₂.baseChange L).PointCoeff)
    (hθ : ∀ (u : galK r) (P : E₁.PointCoeff),
      θ ((ContinuousMonoidHom.id (galK r)) u • P) = u • θ P)
    (hθL : ∀ (h : decomp r τ) (P : (E₁.baseChange L).PointCoeff),
      θL ((ContinuousMonoidHom.id (decomp r τ)) h • P) = h • θL P)
    (hcomm : ∀ P, E₂.pointCoeffBaseChange τ (θ P) = θL (E₁.pointCoeffBaseChange τ P))
    (z : H1 (galK r) E₁.PointCoeff) :
    locK r τ E₂ (explicitMap1 _ _ _ _ (ContinuousMonoidHom.id (galK r)) θ
        continuous_of_discreteTopology hθ z) =
      explicitMap1 _ _ _ _ (ContinuousMonoidHom.id (decomp r τ)) θL
        continuous_of_discreteTopology hθL (locK r τ E₁ z) := by
  rw [locK, locK]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext P; exact hcomm P) z

theorem decomp_fix {h : AbsoluteGaloisGroup L} (hh : h ∈ decomp r τ) : h (τ r) = τ r := by
  rw [← absoluteGaloisGroupMap_commutes, (mem_galK.mp hh : absoluteGaloisGroupMap τ h r = r)]

variable {E : WeierstrassCurve ℚ} (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) {d : ℚ} {r}
  (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ} (hσ : σ ∉ galK r)

/-- The local root `τ r` as a unit of `Lˢ`. -/
def localRootUnit : (SeparableClosure L)ˣ :=
  Units.mk0 (τ r) ((map_ne_zero τ).mpr (ne_zero_of_moves hσ))

include hr in
theorem localRootUnit_sq : ((localRootUnit τ hσ : (SeparableClosure L)ˣ) : SeparableClosure L) ^ 2 =
    ((algebraMap L (SeparableClosure L)).comp (algebraMap ℚ L)) d := by
  rw [localRootUnit, Units.val_mk0, ← map_pow, hr, sepEmb_sepMap]

include h₁ h₃ hr in
theorem localTwist_eq : scaleChange (localRootUnit τ hσ) •
    ((qtwist E d).baseChange L).baseChange (SeparableClosure L) =
      (E.baseChange L).baseChange (SeparableClosure L) :=
  qtwist_map_scaleChange h₁ h₃ _ _ (localRootUnit_sq τ hr hσ)

/-- **The local twist** `E(Lˢ) ≃ E^{(d)}(Lˢ)` by the root `τ r`. -/
def localTwist : (E.baseChange L).PointCoeff ≃+ ((qtwist E d).baseChange L).PointCoeff :=
  twistCoeff (localRootUnit τ hσ) (localTwist_eq τ h₁ h₃ hr hσ)

theorem localTwist_smul {h : AbsoluteGaloisGroup L} (hh : h ∈ decomp r τ)
    (P : (E.baseChange L).PointCoeff) :
    localTwist τ h₁ h₃ hr hσ (h • P) = h • localTwist τ h₁ h₃ hr hσ P :=
  twistCoeff_smul_of_fix _ _ h (by rw [localRootUnit, Units.val_mk0]; exact decomp_fix r τ hh) P

theorem intertwines_pointTwist :
    Intertwines τ (pointTwist h₁ h₃ hr hσ).toAddMonoidHom
      (localTwist τ h₁ h₃ hr hσ).toAddMonoidHom :=
  intertwines_twistCoeff _ _ τ (localRootUnit τ hσ)
    (by rw [localRootUnit, rootUnit, Units.val_mk0, Units.val_mk0]) _

theorem localTwist_symm_smul {h : AbsoluteGaloisGroup L} (hh : h ∈ decomp r τ)
    (P : ((qtwist E d).baseChange L).PointCoeff) :
    (localTwist τ h₁ h₃ hr hσ).symm (h • P) = h • (localTwist τ h₁ h₃ hr hσ).symm P := by
  rw [AddEquiv.symm_apply_eq, localTwist_smul τ h₁ h₃ hr hσ hh, AddEquiv.apply_symm_apply]

end TwistLocal

section ShaTwist

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

variable {E : WeierstrassCurve ℚ} (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) {d : ℚ}
  {r : SeparableClosure ℚ} (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ}
  (hσ : σ ∉ galK r)

/-- **The twist carries `Sha(E/K)` into `Sha(E^{(d)}/K)`.** -/
theorem twist_mem_shaK {z : H1 (galK r) E.PointCoeff} (hz : z ∈ shaK r E) :
    twistH1 (pointTwist h₁ h₃ hr hσ).toAddMonoidHom (isQuadraticTwist_pointTwist h₁ h₃ hr hσ) z ∈
      shaK r (qtwist E d) := by
  have key : ∀ {L : Type} [Field L] [Algebra ℚ L] (τ : SepEmb ℚ L), locK r τ E z = 0 →
      locK r τ (qtwist E d) (twistH1 (pointTwist h₁ h₃ hr hσ).toAddMonoidHom
        (isQuadraticTwist_pointTwist h₁ h₃ hr hσ) z) = 0 := by
    intro L _ _ τ h
    rw [twistH1, locK_explicitMap1 r τ (pointTwist h₁ h₃ hr hσ).toAddMonoidHom
      (localTwist τ h₁ h₃ hr hσ).toAddMonoidHom _
      (fun h P => localTwist_smul τ h₁ h₃ hr hσ h.2 P)
      (intertwines_pointTwist τ h₁ h₃ hr hσ) z, h, map_zero]
  rw [mem_shaK] at hz ⊢
  exact ⟨fun p τ => key τ (hz.1 p τ), fun τ => key τ (hz.2 τ)⟩

/-- **The inverse twist carries `Sha(E^{(d)}/K)` into `Sha(E/K)`.** -/
theorem twist_symm_mem_shaK {z : H1 (galK r) (qtwist E d).PointCoeff}
    (hz : z ∈ shaK r (qtwist E d)) :
    twistH1 (pointTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
      (isQuadraticTwist_pointTwist h₁ h₃ hr hσ).symm z ∈ shaK r E := by
  have key : ∀ {L : Type} [Field L] [Algebra ℚ L] (τ : SepEmb ℚ L),
      locK r τ (qtwist E d) z = 0 →
      locK r τ E (twistH1 (pointTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
        (isQuadraticTwist_pointTwist h₁ h₃ hr hσ).symm z) = 0 := by
    intro L _ _ τ h
    rw [twistH1, locK_explicitMap1 r τ (pointTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
      (localTwist τ h₁ h₃ hr hσ).symm.toAddMonoidHom _
      (fun h P => localTwist_symm_smul τ h₁ h₃ hr hσ h.2 P)
      (intertwines_pointTwist τ h₁ h₃ hr hσ).symm z, h, map_zero]
  rw [mem_shaK] at hz ⊢
  exact ⟨fun p τ => key τ (hz.1 p τ), fun τ => key τ (hz.2 τ)⟩

end ShaTwist

section GaloisAction

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

variable {L : Type*} [Field L] [Algebra ℚ L] {d : ℚ} {r : SeparableClosure ℚ}
  (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ} (hσ : σ ∉ galK r)

include hr in
/-- **The Galois action moves the place given by `τ ∘ σ` to the place given by `τ`**: the
localization at `τ` of the conjugate class is trivial when the localization at `τ ∘ σ` of the
class is. -/
theorem locK_conjH1 [(galK r).FiniteIndex] (E : WeierstrassCurve ℚ) (τ : SepEmb ℚ L)
    (z : H1 (galK r) E.PointCoeff)
    (hz : locK r (τ.comp (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ)) E z = 0) :
    locK r τ E (conjH1 (galK_index hr hσ) hσ z) = 0 := by
  have hidx := galK_index hr hσ
  induction z using QuotientAddGroup.induction_on with
  | H c =>
    rw [locK, explicitMap1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hz
    obtain ⟨m, hm⟩ := hz
    rw [conjH1, explicitMap1_mk, locK, explicitMap1_mk, H1pi_eq_zero_iff, mem_B1_iff]
    refine ⟨m, fun γ => ?_⟩
    have hconj : absoluteGaloisGroupMap (τ.comp (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ))
        (γ : AbsoluteGaloisGroup L) = σ⁻¹ * absoluteGaloisGroupMap τ γ * σ :=
      absoluteGaloisGroupMap_comp τ σ γ
    have hmem : absoluteGaloisGroupMap (τ.comp (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ))
        (γ : AbsoluteGaloisGroup L) ∈ galK r := by
      rw [hconj]
      exact conj_mem hidx hσ γ.2
    have e := hm ⟨γ, hmem⟩
    rw [cocyclesMap1_apply] at e
    have hc : (c : galK r → E.PointCoeff)
        (decompHom r (τ.comp (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ)) ⟨γ, hmem⟩) =
        (c : galK r → E.PointCoeff) (conjU hidx hσ (decompHom r τ γ)) :=
      congrArg _ (Subtype.ext hconj)
    rw [hc, pointCoeffBaseChange_comp] at e
    exact e

include hr in
/-- **`Sha(E/K)` is stable under `Gal(K/ℚ)`.** -/
theorem conjH1_mem_shaK [(galK r).FiniteIndex] {E : WeierstrassCurve ℚ}
    {z : H1 (galK r) E.PointCoeff} (hz : z ∈ shaK r E) :
    conjH1 (galK_index hr hσ) hσ z ∈ shaK r E := by
  rw [mem_shaK] at hz ⊢
  exact ⟨fun p τ => locK_conjH1 hr hσ E τ z (hz.1 p _), fun τ => locK_conjH1 hr hσ E τ z (hz.2 _)⟩

theorem inclK_conjH1 [(galK r).FiniteIndex] (E : WeierstrassCurve ℚ)
    (x : H1 (galK r) (TwoPowerCoeff E)) :
    inclK r E (conjH1 (galK_index hr hσ) hσ x) = conjH1 (galK_index hr hσ) hσ (inclK r E x) := by
  rw [inclK, conjH1, conjH1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; rfl) x

/-- **The action of `Gal(K/ℚ)` on `Sel_{2^∞}(E/K)`**, an involution (`selmerConj_selmerConj`). -/
def selmerConj (E : WeierstrassCurve ℚ) : selmerK r E →+ selmerK r E :=
  letI := galK_finiteIndex hr hσ
  ((conjH1 (galK_index hr hσ) hσ).comp (selmerK r E).subtype).codRestrict (selmerK r E)
    fun x => by
      rw [mem_selmerK, AddMonoidHom.comp_apply, inclK_conjH1 hr hσ]
      exact conjH1_mem_shaK hr hσ x.2

theorem selmerConj_selmerConj (E : WeierstrassCurve ℚ) (x : selmerK r E) :
    selmerConj hr hσ E (selmerConj hr hσ E x) = x := by
  let _ := galK_finiteIndex hr hσ
  exact Subtype.ext (conjH1_conjH1 (galK_index hr hσ) hσ (x : H1 (galK r) (TwoPowerCoeff E)))

end GaloisAction

section SelmerDescent

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

variable {E : WeierstrassCurve ℚ} (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) {d : ℚ}
  {r : SeparableClosure ℚ} (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ}
  (hσ : σ ∉ galK r)

theorem inclK_twistH1 (x : H1 (galK r) (TwoPowerCoeff E)) :
    inclK r (qtwist E d) (twistH1 (twoPowerTwist h₁ h₃ hr hσ).toAddMonoidHom
        (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ) x) =
      twistH1 (pointTwist h₁ h₃ hr hσ).toAddMonoidHom (isQuadraticTwist_pointTwist h₁ h₃ hr hσ)
        (inclK r E x) := by
  rw [inclK, inclK, twistH1, twistH1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; rfl) x

theorem inclK_twistH1_symm (x : H1 (galK r) (TwoPowerCoeff (qtwist E d))) :
    inclK r E (twistH1 (twoPowerTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
        (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ).symm x) =
      twistH1 (pointTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
        (isQuadraticTwist_pointTwist h₁ h₃ hr hσ).symm (inclK r (qtwist E d) x) := by
  rw [inclK, inclK, twistH1, twistH1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; rfl) x

theorem inclK_res (E : WeierstrassCurve ℚ) (y : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) :
    inclK r E (explicitRes1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r) y) =
      explicitRes1 (AbsoluteGaloisGroup ℚ) E.PointCoeff (galK r)
        (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
          continuous_of_discreteTopology y) := by
  rw [inclK, explicitRes1_eq_explicitMap1, explicitRes1_eq_explicitMap1,
    explicitCoeff1_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; rfl) y

theorem incl_cor [(galK r).FiniteIndex] (E : WeierstrassCurve ℚ)
    (x : H1 (galK r) (TwoPowerCoeff E)) :
    explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
        continuous_of_discreteTopology
        (explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r) (isOpen_galK r) x) =
      explicitCor1 (AbsoluteGaloisGroup ℚ) E.PointCoeff (galK r) (isOpen_galK r)
        (inclK r E x) := by
  rw [explicitCoeff1_eq_explicitMap1, inclK]
  exact (explicitCor1_explicitMap1_id (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r)
    (isOpen_galK r) (twoPowerCoeffIncl E).toAddMonoidHom continuous_of_discreteTopology
    (fun g m => (twoPowerCoeffIncl E).map_smul g m) x).symm

include hr hσ in
/-- Corestriction carries `Sel_{2^∞}(E/K)` into `Sel_{2^∞}(E/ℚ)`. -/
theorem cor_mem_selmerTwoPower [(galK r).FiniteIndex] {x : H1 (galK r) (TwoPowerCoeff E)}
    (hx : x ∈ selmerK r E) :
    explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r) (isOpen_galK r) x ∈
      selmerTwoPower E := by
  rw [selmerTwoPower, AddSubgroup.mem_comap, incl_cor]
  exact cor_mem_sha hr hσ hx

/-- The twisted corestriction carries `Sel_{2^∞}(E/K)` into `Sel_{2^∞}(E^{(d)}/ℚ)`. -/
theorem cor_twist_mem_selmerTwoPower [(galK r).FiniteIndex] {x : H1 (galK r) (TwoPowerCoeff E)}
    (hx : x ∈ selmerK r E) :
    explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)) (galK r) (isOpen_galK r)
        (twistH1 (twoPowerTwist h₁ h₃ hr hσ).toAddMonoidHom
          (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ) x) ∈ selmerTwoPower (qtwist E d) := by
  rw [selmerTwoPower, AddSubgroup.mem_comap, incl_cor, inclK_twistH1]
  exact cor_mem_sha hr hσ (twist_mem_shaK h₁ h₃ hr hσ hx)

/-- Restriction carries `Sel_{2^∞}(E/ℚ)` into `Sel_{2^∞}(E/K)`. -/
theorem res_mem_selmerK (E : WeierstrassCurve ℚ) {y : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)}
    (hy : y ∈ selmerTwoPower E) :
    explicitRes1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r) y ∈ selmerK r E := by
  rw [mem_selmerK, inclK_res]
  exact res_mem_shaK r hy

/-- Restriction followed by the inverse twist carries `Sel_{2^∞}(E^{(d)}/ℚ)` into
`Sel_{2^∞}(E/K)`. -/
theorem twist_symm_res_mem_selmerK
    {y : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d))}
    (hy : y ∈ selmerTwoPower (qtwist E d)) :
    twistH1 (twoPowerTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
        (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ).symm
        (explicitRes1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)) (galK r) y) ∈
      selmerK r E := by
  rw [mem_selmerK, inclK_twistH1_symm, inclK_res]
  exact twist_symm_mem_shaK h₁ h₃ hr hσ (res_mem_shaK r hy)

/-- **The quadratic Selmer descent map** `Sel_{2^∞}(E/K) → Sel_{2^∞}(E/ℚ) × Sel_{2^∞}(E^{(d)}/ℚ)`:
corestriction, and corestriction after the quadratic twist. -/
def selmerDescent : selmerK r E →+ selmerTwoPower E × selmerTwoPower (qtwist E d) :=
  letI := galK_finiteIndex hr hσ
  (((explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r) (isOpen_galK r)).comp
      (selmerK r E).subtype).codRestrict (selmerTwoPower E)
      (fun x => cor_mem_selmerTwoPower hr hσ x.2)).prod
    (((explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)) (galK r)
        (isOpen_galK r)).comp ((twistH1 (twoPowerTwist h₁ h₃ hr hσ).toAddMonoidHom
          (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ)).comp (selmerK r E).subtype)).codRestrict
      (selmerTwoPower (qtwist E d)) (fun x => cor_twist_mem_selmerTwoPower h₁ h₃ hr hσ x.2))

/-- **The ascent map** `Sel_{2^∞}(E/ℚ) × Sel_{2^∞}(E^{(d)}/ℚ) → Sel_{2^∞}(E/K)`: restriction, and
restriction followed by the inverse twist. -/
def selmerAscent : selmerTwoPower E × selmerTwoPower (qtwist E d) →+ selmerK r E :=
  (((explicitRes1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r)).comp
      ((selmerTwoPower E).subtype.comp (AddMonoidHom.fst _ _))).codRestrict (selmerK r E)
      (fun y => res_mem_selmerK E y.1.2)) +
    (((twistH1 (twoPowerTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
        (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ).symm).comp
      ((explicitRes1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)) (galK r)).comp
        ((selmerTwoPower (qtwist E d)).subtype.comp (AddMonoidHom.snd _ _)))).codRestrict
      (selmerK r E) (fun y => twist_symm_res_mem_selmerK h₁ h₃ hr hσ y.2.2))

/-- The Selmer descent map is the restriction of `descentH1`. -/
theorem coe_selmerDescent (x : selmerK r E) :
    letI := galK_finiteIndex hr hσ
    (((selmerDescent h₁ h₃ hr hσ x).1 : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)),
        ((selmerDescent h₁ h₃ hr hσ x).2 :
          H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)))) =
      descentH1 (isOpen_galK r) (twoPowerTwist h₁ h₃ hr hσ)
        (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ) (x : H1 (galK r) (TwoPowerCoeff E)) :=
  rfl

/-- The Selmer ascent map is the restriction of `ascentH1`. -/
theorem coe_selmerAscent (y : selmerTwoPower E × selmerTwoPower (qtwist E d)) :
    ((selmerAscent h₁ h₃ hr hσ y : selmerK r E) : H1 (galK r) (TwoPowerCoeff E)) =
      ascentH1 (twoPowerTwist h₁ h₃ hr hσ) (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ)
        ((y.1 : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)),
          (y.2 : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)))) :=
  rfl

/-- **Ascent after descent is multiplication by two** on `Sel_{2^∞}(E/K)`. -/
theorem selmerAscent_selmerDescent (x : selmerK r E) :
    selmerAscent h₁ h₃ hr hσ (selmerDescent h₁ h₃ hr hσ x) = 2 • x := by
  let _ := galK_finiteIndex hr hσ
  apply Subtype.ext
  rw [coe_selmerAscent, AddSubgroup.coe_nsmul]
  have h := congrArg (ascentH1 (twoPowerTwist h₁ h₃ hr hσ)
    (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ)) (coe_selmerDescent h₁ h₃ hr hσ x)
  rw [h]
  exact ascentH1_descentH1 (isOpen_galK r) (galK_index hr hσ) hσ _ _ _

/-- **Descent after ascent is multiplication by two** on
`Sel_{2^∞}(E/ℚ) × Sel_{2^∞}(E^{(d)}/ℚ)`. -/
theorem selmerDescent_selmerAscent (y : selmerTwoPower E × selmerTwoPower (qtwist E d)) :
    selmerDescent h₁ h₃ hr hσ (selmerAscent h₁ h₃ hr hσ y) = 2 • y := by
  let _ := galK_finiteIndex hr hσ
  have h := coe_selmerDescent h₁ h₃ hr hσ (selmerAscent h₁ h₃ hr hσ y)
  rw [coe_selmerAscent, descentH1_ascentH1 (isOpen_galK r) (galK_index hr hσ) hσ] at h
  apply Prod.ext <;> apply Subtype.ext
  · exact (congrArg Prod.fst h).trans (by simp)
  · exact (congrArg Prod.snd h).trans (by simp)

/-- **The quadratic Selmer descent map has bounded defects**: kernel and cokernel are killed
by `2`. This is the form of `BoundedDefects` used by the central comparison. -/
theorem selmerDescent_boundedDefects :
    ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧
      (∀ x, selmerDescent h₁ h₃ hr hσ x = 0 → a • x = 0) ∧
      (∀ y, ∃ x, selmerDescent h₁ h₃ hr hσ x = b • y) := by
  refine ⟨2, 2, two_ne_zero, two_ne_zero, fun x hx => ?_, fun y =>
    ⟨selmerAscent h₁ h₃ hr hσ y, selmerDescent_selmerAscent h₁ h₃ hr hσ y⟩⟩
  rw [← selmerAscent_selmerDescent h₁ h₃ hr hσ x, hx, map_zero]

end SelmerDescent

section Eigenspaces

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

variable {E : WeierstrassCurve ℚ} (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) {d : ℚ}
  {r : SeparableClosure ℚ} (hr : r ^ 2 = sepMap ℚ d) {σ : AbsoluteGaloisGroup ℚ}
  (hσ : σ ∉ galK r)

/-- On the invariant part, the first component of the descent map has kernel killed by `2`. -/
theorem two_nsmul_eq_zero_of_conj_eq_self (x : selmerK r E) (hx : selmerConj hr hσ E x = x)
    (h0 : (selmerDescent h₁ h₃ hr hσ x).1 = 0) : 2 • x = 0 := by
  let _ := galK_finiteIndex hr hσ
  apply Subtype.ext
  have hx' : conjH1 (galK_index hr hσ) hσ (x : H1 (galK r) (TwoPowerCoeff E)) = x :=
    congrArg Subtype.val hx
  have h0' : explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r) (isOpen_galK r)
      (x : H1 (galK r) (TwoPowerCoeff E)) = 0 := congrArg Subtype.val h0
  have h := res_cor_eq_add_conjH1 (isOpen_galK r) (galK_index hr hσ) hσ
    (x : H1 (galK r) (TwoPowerCoeff E))
  rw [h0', map_zero, hx'] at h
  rw [AddSubgroup.coe_nsmul, two_nsmul, ← h, ZeroMemClass.coe_zero]

/-- Every class of `Sel_{2^∞}(E/ℚ)`, multiplied by `2`, is the first component of the descent of
an invariant class. -/
theorem exists_conj_eq_self (y : selmerTwoPower E) :
    ∃ x : selmerK r E, selmerConj hr hσ E x = x ∧ (selmerDescent h₁ h₃ hr hσ x).1 = 2 • y := by
  let _ := galK_finiteIndex hr hσ
  refine ⟨⟨_, res_mem_selmerK E y.2⟩, Subtype.ext ?_, Subtype.ext ?_⟩
  · exact conjH1_res (galK_index hr hσ) hσ (y : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E))
  · change explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r) (isOpen_galK r)
      (explicitRes1 _ _ (galK r) (y : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E))) = _
    rw [explicitCor1_comp_res1, galK_index hr hσ, AddSubgroup.coe_nsmul]

/-- On the anti-invariant part, the second component of the descent map has kernel killed
by `2`. -/
theorem two_nsmul_eq_zero_of_conj_eq_neg (x : selmerK r E) (hx : selmerConj hr hσ E x = -x)
    (h0 : (selmerDescent h₁ h₃ hr hσ x).2 = 0) : 2 • x = 0 := by
  let _ := galK_finiteIndex hr hσ
  apply Subtype.ext
  have hx' : conjH1 (galK_index hr hσ) hσ (x : H1 (galK r) (TwoPowerCoeff E)) = -x :=
    congrArg Subtype.val hx
  have h0' : explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)) (galK r)
      (isOpen_galK r) (twistH1 (twoPowerTwist h₁ h₃ hr hσ).toAddMonoidHom
        (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ) (x : H1 (galK r) (TwoPowerCoeff E))) = 0 :=
    congrArg Subtype.val h0
  have h := twist_res_cor_eq_sub_conjH1 (isOpen_galK r) (galK_index hr hσ) hσ
    (twoPowerTwist h₁ h₃ hr hσ) (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ)
    (x : H1 (galK r) (TwoPowerCoeff E))
  rw [h0', map_zero, map_zero, hx', sub_neg_eq_add] at h
  rw [AddSubgroup.coe_nsmul, two_nsmul, ← h, ZeroMemClass.coe_zero]

/-- Every class of `Sel_{2^∞}(E^{(d)}/ℚ)`, multiplied by `2`, is the second component of the
descent of an anti-invariant class. -/
theorem exists_conj_eq_neg (y : selmerTwoPower (qtwist E d)) :
    ∃ x : selmerK r E, selmerConj hr hσ E x = -x ∧ (selmerDescent h₁ h₃ hr hσ x).2 = 2 • y := by
  let _ := galK_finiteIndex hr hσ
  refine ⟨⟨_, twist_symm_res_mem_selmerK h₁ h₃ hr hσ y.2⟩, Subtype.ext ?_, Subtype.ext ?_⟩
  · change conjH1 (galK_index hr hσ) hσ (twistH1 (twoPowerTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
        (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ).symm (explicitRes1 _ _ (galK r)
          (y : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d))))) = -_
    rw [conjH1_twistH1, conjH1_res]
  · change explicitCor1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)) (galK r)
      (isOpen_galK r) (twistH1 (twoPowerTwist h₁ h₃ hr hσ).toAddMonoidHom
        (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ)
        (twistH1 (twoPowerTwist h₁ h₃ hr hσ).symm.toAddMonoidHom
          (isQuadraticTwist_twoPowerTwist h₁ h₃ hr hσ).symm (explicitRes1 _ _ (galK r)
            (y : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff (qtwist E d)))))) = _
    rw [twistH1_twistH1_symm, explicitCor1_comp_res1, galK_index hr hσ, AddSubgroup.coe_nsmul]

end Eigenspaces

section Consistency

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

/-- The subgroup of `G_K` fixing the intermediate field `K(r)` of `Kˢ`. -/
def fixingAdjoin {K : Type*} [Field K] (r : SeparableClosure K) :
    Subgroup (AbsoluteGaloisGroup K) :=
  (IntermediateField.adjoin K {r}).fixingSubgroup

/-- **`galK r` is the Galois group of `ℚˢ` over the intermediate field `ℚ(r)`.** -/
theorem stabilizer_eq_fixingAdjoin {K : Type*} [Field K] (r : SeparableClosure K) :
    MulAction.stabilizer (AbsoluteGaloisGroup K) r = fixingAdjoin r := by
  ext σ
  rw [fixingAdjoin, ← Subgroup.zpowers_le, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le,
    IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
    IntermediateField.mem_fixedField_iff]
  exact ⟨fun h f hf => MulAction.mem_stabilizer_iff.mp (h hf),
    fun h f hf => MulAction.mem_stabilizer_iff.mpr (h f hf)⟩

theorem galK_eq_fixingAdjoin (r : SeparableClosure ℚ) : galK r = fixingAdjoin r :=
  stabilizer_eq_fixingAdjoin r

/-- **The decomposition group at `τ` is the Galois group of `Lˢ` over the local field
`L(τ r)`**, the completion of `K = ℚ(r)` at the place given by `τ`. -/
theorem decomp_eq_fixingAdjoin {L : Type*} [Field L] [Algebra ℚ L] (r : SeparableClosure ℚ)
    (τ : SepEmb ℚ L) : decomp r τ = fixingAdjoin (τ r) := by
  rw [← stabilizer_eq_fixingAdjoin]
  ext h
  rw [mem_decomp, mem_galK, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def,
    ← absoluteGaloisGroupMap_commutes]
  exact ⟨fun h' => by rw [h'], fun h' => τ.injective h'⟩

/-- Restriction to a subgroup containing every element is injective on `H¹`. -/
theorem explicitRes1_injective_of_forall_mem {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M] (T : Subgroup G) (hT : ∀ g, g ∈ T) :
    Function.Injective (explicitRes1 G M T) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitRes1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hx
    obtain ⟨m, hm⟩ := hx
    rw [H1pi_eq_zero_iff, mem_B1_iff]
    exact ⟨m, fun g => hm ⟨g, hT g⟩⟩

/-- **Consistency with `selmerTwoPower`.** For `K = ℚ` (the root `1`), the construction of
`selmerK` is the two-primary Selmer group over `ℚ`: a class of `H¹(G_ℚ, E[2^∞])` is in
`Sel_{2^∞}(E/ℚ)` exactly when its restriction to `galK 1 = G_ℚ` is in `selmerK 1 E`. -/
theorem mem_selmerTwoPower_iff_res_mem_selmerK_one (E : WeierstrassCurve ℚ)
    (y : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) :
    y ∈ selmerTwoPower E ↔
      explicitRes1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK 1) y ∈ selmerK 1 E := by
  refine ⟨res_mem_selmerK E, fun hy => ?_⟩
  have hall : ∀ {L : Type} [Field L] [Algebra ℚ L] (τ : SepEmb ℚ L) (h : AbsoluteGaloisGroup L),
      h ∈ decomp 1 τ := fun τ h => mem_galK.mpr (map_one _)
  rw [mem_selmerK, inclK_res, mem_shaK] at hy
  rw [selmerTwoPower, AddSubgroup.mem_comap, sha, AddSubgroup.mem_inf,
    mem_shafarevichTateGroup_iff, mem_shafarevichTateGroup_iff]
  refine ⟨fun p => ?_, fun u => ?_⟩
  · have h := hy.1 p (embFin p)
    rw [locK_res] at h
    exact explicitRes1_injective_of_forall_mem _ (hall (embFin p)) (h.trans (map_zero _).symm)
  · cases u
    have h := hy.2 (embInf ())
    rw [locK_res] at h
    exact explicitRes1_injective_of_forall_mem _ (hall (embInf ())) (h.trans (map_zero _).symm)

end Consistency

section Curve

open WeierstrassCurve ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC

/-- Elements of `Kˢ` fixed by every automorphism lie in `K`. -/
theorem exists_moves {K : Type*} [Field K] {x : SeparableClosure K}
    (hx : x ∉ Set.range (sepMap K)) : ∃ σ : AbsoluteGaloisGroup K, σ x ≠ x := by
  by_contra h
  exact hx ((InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr fun σ => not_not.mp
    fun hσ => h ⟨σ, hσ⟩)

/-- A chosen square root of `k` in `ℚˢ`, generating `K = ℚ(√k)`. -/
def sqrtK (k : ℤ) : SeparableClosure ℚ :=
  Classical.choose (IsSepClosed.exists_pow_nat_eq (sepMap ℚ (k : ℚ)) 2)

theorem sqrtK_sq (k : ℤ) : sqrtK k ^ 2 = sepMap ℚ (k : ℚ) :=
  Classical.choose_spec (IsSepClosed.exists_pow_nat_eq (sepMap ℚ (k : ℚ)) 2)

/-- If `k` is not a square in `ℚ`, then `K = ℚ(√k)` is a quadratic field: some element of
`G_ℚ` moves `√k`. -/
theorem exists_not_mem_galK {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    ∃ σ : AbsoluteGaloisGroup ℚ, σ ∉ galK (sqrtK k) := by
  have hx : sqrtK k ∉ Set.range (sepMap ℚ) := by
    rintro ⟨q, hq⟩
    apply hk
    refine ⟨q, (sepMap ℚ).injective ?_⟩
    rw [map_mul, hq, ← sq, sqrtK_sq]
  obtain ⟨σ, hσ⟩ := exists_moves hx
  exact ⟨σ, fun h => hσ (mem_galK.mp h)⟩

/-- A negative integer is not a square in `ℚ`; this covers the final companion `k < 0`. -/
theorem not_isSquare_of_neg {k : ℤ} (hk : k < 0) : ¬ IsSquare (k : ℚ) := by
  rintro ⟨q, hq⟩
  have h0 : (0 : ℚ) ≤ q * q := mul_self_nonneg q
  have h1 : (k : ℚ) < 0 := by exact_mod_cast hk
  linarith

/-- A chosen element of `G_ℚ` not in `G_K`. -/
def sigmaK {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) : AbsoluteGaloisGroup ℚ :=
  Classical.choose (exists_not_mem_galK hk)

theorem sigmaK_not_mem {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) : sigmaK hk ∉ galK (sqrtK k) :=
  Classical.choose_spec (exists_not_mem_galK hk)

theorem Ecurve_a₁ (ℓ : ℕ) : (Ecurve ℓ).a₁ = 0 := rfl

theorem Ecurve_a₃ (ℓ : ℕ) : (Ecurve ℓ).a₃ = 0 := rfl

/-- **`Sel_{2^∞}(E_ℓ / ℚ(√k))`**, the full two-primary Selmer group of `E_ℓ` over the quadratic
field `K = ℚ(√k)`. -/
abbrev SelK (ℓ : ℕ) (k : ℤ) : AddSubgroup (H1 (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ))) :=
  selmerK (sqrtK k) (Ecurve ℓ)

/-- **The quadratic descent map for `E_ℓ` and `K = ℚ(√k)`**:
`Sel_{2^∞}(E_ℓ/K) → Sel_{2^∞}(E_ℓ/ℚ) × Sel_{2^∞}(E_ℓ^{(k)}/ℚ)`, by corestriction and by
corestriction after the twist `E_ℓ ≃ E_ℓ^{(k)}` over `K`. -/
def quadraticDescent (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    SelK ℓ k →+ selmerTwoPower (Ecurve ℓ) × selmerTwoPower (Etw ℓ k) :=
  selmerDescent (Ecurve_a₁ ℓ) (Ecurve_a₃ ℓ) (sqrtK_sq k) (sigmaK_not_mem hk)

/-- **The quadratic descent map has kernel and cokernel killed by `2`.** -/
theorem quadraticDescent_boundedDefects (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧
      (∀ x, quadraticDescent ℓ hk x = 0 → a • x = 0) ∧
      (∀ y, ∃ x, quadraticDescent ℓ hk x = b • y) :=
  selmerDescent_boundedDefects (Ecurve_a₁ ℓ) (Ecurve_a₃ ℓ) (sqrtK_sq k) (sigmaK_not_mem hk)

/-- **The action of `Gal(K/ℚ)` on `Sel_{2^∞}(E_ℓ/ℚ(√k))`.** -/
def selKConj (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) : SelK ℓ k →+ SelK ℓ k :=
  selmerConj (sqrtK_sq k) (sigmaK_not_mem hk) (Ecurve ℓ)

theorem selKConj_selKConj (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) (x : SelK ℓ k) :
    selKConj ℓ hk (selKConj ℓ hk x) = x :=
  selmerConj_selmerConj (sqrtK_sq k) (sigmaK_not_mem hk) (Ecurve ℓ) x

/-- On the invariant part of `Sel_{2^∞}(E_ℓ/K)`, corestriction has kernel killed by `2`. -/
theorem quadraticDescent_fst_two_nsmul (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) (x : SelK ℓ k)
    (hx : selKConj ℓ hk x = x) (h0 : (quadraticDescent ℓ hk x).1 = 0) : 2 • x = 0 :=
  two_nsmul_eq_zero_of_conj_eq_self (Ecurve_a₁ ℓ) (Ecurve_a₃ ℓ) (sqrtK_sq k) (sigmaK_not_mem hk)
    x hx h0

/-- Every class of `Sel_{2^∞}(E_ℓ/ℚ)` times `2` is the corestriction of an invariant class. -/
theorem quadraticDescent_exists_fst (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (y : selmerTwoPower (Ecurve ℓ)) :
    ∃ x : SelK ℓ k, selKConj ℓ hk x = x ∧ (quadraticDescent ℓ hk x).1 = 2 • y :=
  exists_conj_eq_self (Ecurve_a₁ ℓ) (Ecurve_a₃ ℓ) (sqrtK_sq k) (sigmaK_not_mem hk) y

/-- On the anti-invariant part, twisted corestriction has kernel killed by `2`. -/
theorem quadraticDescent_snd_two_nsmul (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) (x : SelK ℓ k)
    (hx : selKConj ℓ hk x = -x) (h0 : (quadraticDescent ℓ hk x).2 = 0) : 2 • x = 0 :=
  two_nsmul_eq_zero_of_conj_eq_neg (Ecurve_a₁ ℓ) (Ecurve_a₃ ℓ) (sqrtK_sq k) (sigmaK_not_mem hk)
    x hx h0

/-- Every class of `Sel_{2^∞}(E_ℓ^{(k)}/ℚ)` times `2` is the twisted corestriction of an
anti-invariant class. -/
theorem quadraticDescent_exists_snd (ℓ : ℕ) {k : ℤ} (hk : ¬ IsSquare (k : ℚ))
    (y : selmerTwoPower (Etw ℓ k)) :
    ∃ x : SelK ℓ k, selKConj ℓ hk x = -x ∧ (quadraticDescent ℓ hk x).2 = 2 • y :=
  exists_conj_eq_neg (Ecurve_a₁ ℓ) (Ecurve_a₃ ℓ) (sqrtK_sq k) (sigmaK_not_mem hk) y

end Curve

end ZInQ.Manuscript.RC53Assist.QuadraticDescent
