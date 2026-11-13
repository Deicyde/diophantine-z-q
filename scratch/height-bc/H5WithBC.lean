import ZInQKernel.HDecomp.Faltings.Leaves

/-! # h5-glue: `NeronModelMinimal`, `OpenSubgroupHeight`, H4b are theorems; H5 from N1, N2, H4a

Self-contained (Mathlib + project only; no `sorry`, no `axiom`).
* Part 1 (namespace `ZInQ.DefFaltings.HodgeLattice`): `scratch/hodge-lattice/HodgeLattice.lean`
  §1-§5 copied verbatim (task hodge-lattice), for `omegaLocal` and `omegaSpans_of_omegaLocal`.
* Part 2 (namespace `ZInQ.H5Glue`): `scratch/h5-glue/JacDet.lean` (transport along a generic
  isomorphism; `heightAntitone_of_omegaSpans`) and `scratch/h5-glue/Minimal.lean` (the Néron
  comparison map; `neronModelMinimal_of_heightAntitone`).
* Final of Part 2: `heightAntitone : HeightAntitone`, `neronModelMinimal : NeronModelMinimal`.
* Part 3: from `H5Glue.lean` §1, §3, §5 and `Additivity.lean` (h5-neron's product material copied
  verbatim): H4b, open subgroups, the reduction, and additivity, with `HeightAntitone` and
  `NeronModelMinimal` discharged.
* Part 4: `openImmersionHeightLe` (inverse transport through open immersions),
  `openSubgroupHeight`, `stableFaltingsHeight_eq_neron_all'` (H5 from N1, N2,
  `ModelHeightBaseChange`). -/

/-! # `HodgeLatticeTheorem`: the algebraic reduction (task hodge-lattice)

`ZInQ.DefFaltings.HodgeLatticeTheorem` (ZInQKernel/HDecomp/Faltings/Models.lean) asks, for a smooth
group model `𝒢` of `A_L` with `A.dim = g`, that
* `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)` is an `L`-line, and
* `detLattice g = 𝓞_L-span {1 ⊗ v₁ ∧ ⋯ ∧ v_g : vᵢ ∈ ω_𝒢}` is a full lattice in it.

§1 proves this, for an arbitrary `𝓞_K`-module `M` and submodule `ω` in place of
`(𝔪_ξ/𝔪_ξ², ω_𝒢)`, from three hypotheses: `ω` finitely generated, `K ⊗ M` of `K`-rank `g`, and
`ω` spanning `K ⊗ M` over `K` (`hodgeLattice_of_lattice`). §2 states the three hypotheses over the
genuine objects of `Models.lean` (`OmegaFG`, `CotangentRank`, `OmegaSpans`) and derives
`HodgeLatticeTheorem` from them (`hodgeLatticeTheorem_of`). §3-§5 prove `OmegaFG` and `OmegaSpans`
(`omegaLocal`: `ω_𝒢` is a finitely generated full lattice). §6 reduces `CotangentRank` to the
regularity and Krull dimension of `𝒪_{𝒢,ξ}`; §7 is a corollary; §8-§9 move these to statements about
abelian varieties over a field and the local rings of a generic fibre; §10 proves the latter
(`genericFibreStalkIso`); §11 needs only the tangent dimension at the origin. Final form:

`hodgeLatticeTheorem_of_tangent : TangentDimAtOrigin → DimBaseChange → HodgeLatticeTheorem`
(and `tangentDimAtOrigin_of : RegularAtOrigin → DimAtOrigin → TangentDimAtOrigin`).

No `sorry`, no `axiom`. -/

namespace ZInQ.DefFaltings.HodgeLattice

open NumberField TensorProduct

/-! ## 1. Commutative algebra -/

/-- A top-degree alternating map on `R^g`, with values in any module, is `det · F(e)`. -/
theorem alt_eq_smulRight {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] {g : ℕ}
    (F : (Fin g → R) [⋀^Fin g]→ₗ[R] N) :
    F = (Pi.basisFun R (Fin g)).det.smulRight (F (Pi.basisFun R (Fin g))) := by
  refine Module.Basis.ext_alternating (Pi.basisFun R (Fin g)) fun i h => ?_
  let σ : Equiv.Perm (Fin g) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change F (Pi.basisFun R (Fin g) ∘ σ) =
    ((Pi.basisFun R (Fin g)).det.smulRight (F (Pi.basisFun R (Fin g)))) (Pi.basisFun R (Fin g) ∘ σ)
  rw [AlternatingMap.smulRight_apply, AlternatingMap.map_perm, AlternatingMap.map_perm,
    Module.Basis.det_self]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Clearing denominators in `K ⊗_{𝓞_K} M`: if every `1 ⊗ v` is a `K`-combination of the
`1 ⊗ w_j`, then some nonzero multiple of `v` is an `𝓞_K`-combination of the `w_j` in `M`. -/
theorem exists_clear {g : ℕ} (w : Fin g → M)
    (hb : ∀ v : M, (1 : K) ⊗ₜ[𝓞 K] v ∈
      Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[𝓞 K] w j)) (v : M) :
    ∃ D : 𝓞 K, D ≠ 0 ∧ ∃ a : Fin g → 𝓞 K, D • v = ∑ j, a j • w j := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hb v)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ c
  choose a ha using fun j => hd j (Finset.mem_univ j)
  have key : (TensorProduct.mk (𝓞 K) K M 1) ((d : 𝓞 K) • v) =
      TensorProduct.mk (𝓞 K) K M 1 (∑ j, a j • w j) := by
    simp only [TensorProduct.mk_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    rw [← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K (a j), ha j, smul_assoc]
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (TensorProduct.mk (𝓞 K) K M 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 K)) K _).mpr
      (TensorProduct.isBaseChange _ _ _)
  obtain ⟨e, he⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors (𝓞 K)) key
  refine ⟨(e : 𝓞 K) * d, mul_ne_zero (nonZeroDivisors.ne_zero e.2)
    (nonZeroDivisors.ne_zero d.2), fun j => (e : 𝓞 K) * a j, ?_⟩
  have he' : (e : 𝓞 K) • ((d : 𝓞 K) • v) = (e : 𝓞 K) • ∑ j, a j • w j := he
  rw [mul_smul, he', Finset.smul_sum]
  simp only [mul_smul]

/-- The wedge of any `g` vectors is an `K`-multiple of the wedge of `w`, as soon as every vector
has a nonzero multiple in the `𝓞_K`-span of `w`. -/
theorem tmul_ιMulti_mem_span {g : ℕ} (w : Fin g → M)
    (hw : ∀ v : M, ∃ D : 𝓞 K, D ≠ 0 ∧ ∃ a : Fin g → 𝓞 K, D • v = ∑ j, a j • w j)
    (v : Fin g → M) :
    (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g v ∈
      Submodule.span K {(1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g w} := by
  choose D hD a ha using hw
  set ψ := Fintype.linearCombination (𝓞 K) w with hψ
  have h1 : exteriorPower.ιMulti (𝓞 K) g (fun i => D (v i) • v i) =
      (∏ i, D (v i)) • exteriorPower.ιMulti (𝓞 K) g v :=
    MultilinearMap.map_smul_univ _ _ _
  have h2 : (fun i => D (v i) • v i) = fun i => ψ (a (v i)) := by
    funext i; rw [ha, hψ, Fintype.linearCombination_apply]
  have he : (fun i => ψ (Pi.basisFun (𝓞 K) (Fin g) i)) = w := by
    funext i
    classical
    rw [Pi.basisFun_apply, hψ, Fintype.linearCombination_apply_single, one_smul]
  have hF := congrArg (fun F => F (fun i => a (v i)))
    (alt_eq_smulRight ((exteriorPower.ιMulti (𝓞 K) g).compLinearMap ψ))
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smulRight_apply] at hF
  set c : 𝓞 K := (Pi.basisFun (𝓞 K) (Fin g)).det (fun i => a (v i))
  have hF' : (∏ i, D (v i)) • exteriorPower.ιMulti (𝓞 K) g v =
      c • exteriorPower.ιMulti (𝓞 K) g w := by
    rw [← h1, h2, hF, he]
  have hP : (∏ i, D (v i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hD _
  have hPK : algebraMap (𝓞 K) K (∏ i, D (v i)) ≠ 0 := fun h =>
    hP (IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero]))
  rw [Submodule.mem_span_singleton]
  refine ⟨(algebraMap (𝓞 K) K (∏ i, D (v i)))⁻¹ * algebraMap (𝓞 K) K c, ?_⟩
  rw [mul_smul, algebraMap_smul K c, ← TensorProduct.tmul_smul, ← hF',
    TensorProduct.tmul_smul, ← algebraMap_smul K (∏ i, D (v i)), smul_smul, inv_mul_cancel₀ hPK,
    one_smul]

/-- The Hodge lattice of `ω ⊆ M` in `K ⊗ ⋀^g M` (the shape of `GroupModel.detLattice`). -/
noncomputable def detLat (ω : Submodule (𝓞 K) M) (g : ℕ) :
    Submodule (𝓞 K) (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) :=
  Submodule.span (𝓞 K) (Set.range fun v : Fin g → ω =>
    (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g (fun i => (v i : M)))

/-- **The algebraic content of `HodgeLatticeTheorem`.** If `ω ⊆ M` is finitely generated,
`K ⊗ M` has `K`-rank `g`, and `ω` spans `K ⊗ M` over `K`, then `K ⊗ ⋀^g M` is a `K`-line and
`detLat ω g` is a full lattice in it (some nonzero element generates a subgroup of finite index). -/
theorem hodgeLattice_of_lattice {g : ℕ} (ω : Submodule (𝓞 K) M) (hfg : ω.FG)
    (hrank : Module.rank K (K ⊗[𝓞 K] M) = g)
    (hspan : Submodule.span K (Set.range fun x : ω => (1 : K) ⊗ₜ[𝓞 K] (x : M)) = ⊤) :
    Module.finrank K (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) = 1 ∧
      ∃ s ∈ detLat ω g, s ≠ 0 ∧ secIndex (detLat ω g) s ≠ 0 := by
  classical
  set V := K ⊗[𝓞 K] M
  set f : ω → V := fun x => (1 : K) ⊗ₜ[𝓞 K] (x : M) with hf
  have : FiniteDimensional K V := Module.finite_of_rank_eq_nat hrank
  have hfin : Module.finrank K V = g := Module.finrank_eq_of_rank_eq hrank
  -- Step 1: a `K`-basis of `V` of the form `1 ⊗ w_j` with `w_j ∈ ω`.
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
  let bs : Module.Basis s K V := Module.Basis.mk hs_li (by
    rw [Subtype.range_coe, hs_span, hspan])
  let b : Module.Basis (Fin g) K V :=
    bs.reindex (bs.indexEquiv (Module.finBasisOfFinrankEq K V hfin))
  have hmem : ∀ j, ∃ x : ω, f x = b j := fun j => by
    have : (b j : V) ∈ s := by
      simp only [b, Module.Basis.reindex_apply, bs, Module.Basis.coe_mk]
      exact Subtype.mem _
    exact hs_sub this
  choose w hw using hmem
  set w' : Fin g → M := fun j => (w j : M) with hw'
  have hbw : ∀ j, (1 : K) ⊗ₜ[𝓞 K] w' j = b j := hw
  -- Step 2: every vector of `M` has a nonzero multiple in the `𝓞_K`-span of `w'`.
  have hclear := exists_clear (K := K) w' (fun v => by
    have hr : Set.range (fun j => (1 : K) ⊗ₜ[𝓞 K] w' j) = Set.range b := by
      rw [show (fun j => (1 : K) ⊗ₜ[𝓞 K] w' j) = b from funext hbw]
    rw [hr, b.span_eq]; exact Submodule.mem_top)
  -- Step 3: `s₀ = 1 ⊗ w'_1 ∧ ⋯ ∧ w'_g` spans `K ⊗ ⋀^g M` over `K`.
  set s0 : K ⊗[𝓞 K] ⋀[𝓞 K]^g M := (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g w' with hs0
  have hone : ∀ x : ⋀[𝓞 K]^g M, (1 : K) ⊗ₜ[𝓞 K] x ∈ Submodule.span K {s0} := by
    intro x
    have hx : x ∈ Submodule.span (𝓞 K) (Set.range (exteriorPower.ιMulti (𝓞 K) g)) := by
      rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact tmul_ιMulti_mem_span w' hclear v
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ r hy
  have htop : Submodule.span K {s0} = ⊤ := by
    rw [eq_top_iff]
    rintro h -
    induction h using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul k x =>
      have : k ⊗ₜ[𝓞 K] x = k • ((1 : K) ⊗ₜ[𝓞 K] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ k (hone x)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  -- Step 4: `s₀ ≠ 0`, through the functional induced by `det_b`.
  let φ : M [⋀^Fin g]→ₗ[𝓞 K] K :=
    { toMultilinearMap := (b.det.toMultilinearMap.restrictScalars (𝓞 K)).compLinearMap
        (fun _ => TensorProduct.mk (𝓞 K) K M 1)
      map_eq_zero_of_eq' := fun v i j hv hij =>
        b.det.map_eq_zero_of_eq (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) (by simp [hv]) hij }
  let Ψ : (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) →ₗ[K] K :=
    (exteriorPower.alternatingMapLinearEquiv φ).liftBaseChange K
  have hΨ : Ψ s0 = 1 := by
    simp only [Ψ, hs0, LinearMap.liftBaseChange_one_tmul,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change b.det (fun k => (1 : K) ⊗ₜ[𝓞 K] w' k) = 1
    rw [show (fun k => (1 : K) ⊗ₜ[𝓞 K] w' k) = b from funext hbw, Module.Basis.det_self]
  have hs0ne : s0 ≠ 0 := fun h => by rw [h, map_zero] at hΨ; exact zero_ne_one hΨ
  refine ⟨?_, s0, Submodule.subset_span ⟨w, rfl⟩, hs0ne, ?_⟩
  · rw [← finrank_top K, ← htop]
    exact finrank_span_singleton hs0ne
  -- Step 5: `detLat ω g` lies in a finitely generated module, hence in `𝓞_K · t₀` with
  -- `s₀ = d • t₀`; so `𝓞_K s₀` has finite index in it.
  have : Module.Finite (𝓞 K) ω := Module.Finite.iff_fg.mpr hfg
  set R : Submodule (𝓞 K) (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) := LinearMap.range
    ((TensorProduct.mk (𝓞 K) K (⋀[𝓞 K]^g M) 1) ∘ₗ exteriorPower.map g ω.subtype) with hR
  have hRfg : R.FG := by
    rw [hR, LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
  have hDR : detLat ω g ≤ R := by
    rw [detLat, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact ⟨exteriorPower.ιMulti (𝓞 K) g v, by
      simp [exteriorPower.map_apply_ιMulti]; rfl⟩
  obtain ⟨S, hS⟩ := hRfg
  have hc : ∀ t : K ⊗[𝓞 K] ⋀[𝓞 K]^g M, ∃ c : K, c • s0 = t := fun t => by
    have : t ∈ Submodule.span K {s0} := by rw [htop]; exact Submodule.mem_top
    exact Submodule.mem_span_singleton.mp this
  choose c hc using hc
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) S c
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hdK : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := fun h =>
    hd0 (IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero]))
  set t0 : K ⊗[𝓞 K] ⋀[𝓞 K]^g M := (algebraMap (𝓞 K) K (d : 𝓞 K))⁻¹ • s0 with ht0
  have hst : s0 = (d : 𝓞 K) • t0 := by
    rw [ht0, ← algebraMap_smul K (d : 𝓞 K), smul_smul, mul_inv_cancel₀ hdK, one_smul]
  have hRt : R ≤ Submodule.span (𝓞 K) {t0} := by
    rw [← hS, Submodule.span_le]
    intro t ht
    obtain ⟨a, ha⟩ := hd t ht
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    rw [← algebraMap_smul K a, ha, ht0, smul_smul]
    conv_rhs => rw [← hc t]
    congr 1
    rw [Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ hdK, one_mul]
  have ht0ne : t0 ≠ 0 := fun h => hs0ne (by rw [hst, h, smul_zero])
  have hidx : secIndex (Submodule.span (𝓞 K) {t0}) s0 ≠ 0 := by
    rw [hst, secIndex_smul _ (Submodule.mem_span_singleton_self t0) ht0ne]
    have h1 : secIndex (Submodule.span (𝓞 K) {t0}) t0 = 1 := by
      unfold secIndex; exact AddSubgroup.relIndex_self _
    rw [h1, mul_one]
    simp [Int.natAbs_eq_zero, (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hd0]
  unfold secIndex at hidx ⊢
  intro h0
  exact hidx (AddSubgroup.relIndex_eq_zero_of_le_right
    (show (detLat ω g).toAddSubgroup ≤ (Submodule.span (𝓞 K) {t0}).toAddSubgroup from
      fun x hx => hRt (hDR hx)) h0)

/-! ## 2. The three geometric inputs, over the objects of `Models.lean`

For a smooth group model `𝒢` of `A_L` (`GroupModel A L`), write `cot = 𝔪_ξ/𝔪_ξ²`
(`GroupModel.cotangent`, an `𝓞_L`-module through `structMap`) and `ω_𝒢 = ⋂_s (ω_𝒢)_s ⊆ cot`
(`GroupModel.omega`). -/

open PkgI3 (AbVar)

/-- **(G1)** `ω_𝒢` is a finitely generated `𝓞_L`-module. (Geometrically: `ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S})`
with `e*Ω¹` coherent, indeed locally free of rank `g`, on `S = Spec 𝓞_L`.) -/
def OmegaFG : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), 𝒢.omega.FG

/-- **(G2)** `L ⊗_{𝓞_L} 𝔪_ξ/𝔪_ξ²` (which is `𝔪_ξ/𝔪_ξ² = ω_{A_L}` itself) has `L`-dimension
`g = dim A`. (Geometrically: `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`, and the local ring of a smooth `L`-variety
of pure dimension `g` at a rational point is regular of dimension `g`.) -/
def CotangentRank : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g →
    Module.rank L (L ⊗[𝓞 L] 𝒢.cotangent) = g

/-- **(G3)** `ω_𝒢` spans `ω_{A_L}` over `L`: the image of `L ⊗ ω_𝒢 → L ⊗ cot` is everything.
(Geometrically: the generic stalk of the coherent sheaf `e*Ω¹_{𝒢/S}` is `ω_{A_L}`, and a coherent
sheaf on an affine scheme is generated by global sections.) -/
def OmegaSpans : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L),
    Submodule.span L (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) = ⊤

/-- `detLattice` is the generic `detLat` of `§1`. -/
theorem detLattice_eq {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L]
    [Algebra K L] (𝒢 : GroupModel A L) (g : ℕ) : 𝒢.detLattice g = detLat 𝒢.omega g := rfl

/-- **Main result.** `HodgeLatticeTheorem` follows from the three geometric inputs; everything
else (the exterior algebra, the line, the full lattice) is proved. -/
theorem hodgeLatticeTheorem_of (h1 : OmegaFG) (h2 : CotangentRank) (h3 : OmegaSpans) :
    HodgeLatticeTheorem := by
  intro K _ A L _ _ _ 𝒢 g hg
  rw [detLattice_eq]
  exact hodgeLattice_of_lattice 𝒢.omega (h1 K A L 𝒢) (h2 K A L 𝒢 g hg) (h3 K A L 𝒢)

end ZInQ.DefFaltings.HodgeLattice

namespace ZInQ.DefFaltings.HodgeLattice

open NumberField TensorProduct
open PkgI3 (AbVar)

/-! ## 3. Local-to-global over `Spec R` (pure algebra)

For a family `Ω s` of submodules indexed by the points of `Spec R`, finiteness and fullness of
`⋂_s Ω s` follow from local statements on a cover by basic opens `D(a)`. -/

section LocalGlobal

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- Finitely many basic opens `D(a s)` cover `Spec R` if `s ∈ D(a s)` for every `s`. -/
theorem exists_finset_cover (a : PrimeSpectrum R → R) (ha : ∀ s, a s ∉ s.asIdeal) :
    ∃ F : Finset (PrimeSpectrum R), ∀ s' : PrimeSpectrum R, ∃ s ∈ F, a s ∉ s'.asIdeal := by
  classical
  have htop : Ideal.span (Set.range a) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    exact ha ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨T, hT, hTtop⟩ := (Ideal.span_eq_top_iff_finite _).mp htop
  refine ⟨T.attach.image (fun r => (hT r.2).choose), fun s' => ?_⟩
  by_contra hno
  push_neg at hno
  have : Ideal.span (T : Set R) ≤ s'.asIdeal := by
    rw [Ideal.span_le]
    intro r hr
    have := hno _ (Finset.mem_image_of_mem _ (Finset.mem_attach T ⟨r, hr⟩))
    rwa [(hT hr).choose_spec] at this
  exact s'.isPrime.ne_top (top_le_iff.mp (hTtop ▸ this))

/-- **Finiteness, local to global.** -/
theorem fg_iInf_of_local [IsNoetherianRing R] (Ω : PrimeSpectrum R → Submodule R V)
    (h : ∀ s : PrimeSpectrum R, ∃ a : R, a ∉ s.asIdeal ∧ ∃ N : Submodule R V, N.FG ∧
      ∀ s' : PrimeSpectrum R, a ∉ s'.asIdeal → ∀ x ∈ Ω s', ∃ t ∉ s'.asIdeal, t • x ∈ N) :
    (⨅ s, Ω s).FG := by
  classical
  choose a ha N hN hloc using h
  obtain ⟨F, hF⟩ := exists_finset_cover a ha
  set N0 := F.sup N
  have hN0 : N0.FG := Submodule.fg_finset_sup F N fun i _ => hN i
  refine Submodule.FG.of_le hN0 fun x hx => ?_
  set J : Ideal R := N0.comap (LinearMap.toSpanSingleton R V x)
  have hJ : J = ⊤ := by
    by_contra hJ
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
    obtain ⟨s, hsF, hs⟩ := hF ⟨m, hm.isPrime⟩
    obtain ⟨t, ht, htN⟩ := hloc s ⟨m, hm.isPrime⟩ hs x (Submodule.mem_iInf _ |>.mp hx _)
    exact ht (hle (show t ∈ J from Finset.le_sup (f := N) hsF htN))
  have : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
  simpa [J] using this

/-- **Fullness, local to global.** -/
theorem exists_smul_mem_iInf_of_local [IsDomain R] (Ω : PrimeSpectrum R → Submodule R V)
    (h : ∀ s : PrimeSpectrum R, ∃ a : R, a ∉ s.asIdeal ∧ ∃ N : Submodule R V,
      (∀ x : V, ∃ c : R, c ≠ 0 ∧ c • x ∈ N) ∧
      ∀ s' : PrimeSpectrum R, a ∉ s'.asIdeal → N ≤ Ω s') (x : V) :
    ∃ c : R, c ≠ 0 ∧ c • x ∈ ⨅ s, Ω s := by
  classical
  choose a ha N hN hle using h
  obtain ⟨F, hF⟩ := exists_finset_cover a ha
  choose c hc0 hcN using fun s => hN s x
  refine ⟨∏ s ∈ F, c s, Finset.prod_ne_zero_iff.mpr fun s _ => hc0 s, ?_⟩
  rw [Submodule.mem_iInf]
  intro s'
  obtain ⟨s, hsF, hs⟩ := hF s'
  apply hle s s' hs
  rw [← Finset.mul_prod_erase F c hsF, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (hcN s)

end LocalGlobal

/-! ## 4. `OmegaFG` and `OmegaSpans` from one local statement

`OmegaLocal` says: near every point `s` of `S = Spec 𝓞_L` (on a basic open `D(a) ∋ s`), the
stalks `(ω_𝒢)_{s'}` (`omegaAt s'`) are the localizations of one finitely generated `N ⊆ ω_{A_L}`
that spans `ω_{A_L}` over `L`. This is "`e*Ω¹_{𝒢/S}` is quasi-coherent of finite type with generic
stalk `ω_{A_L}`" in the form needed: for an affine open `U = Spec B ⊆ 𝒢` with `e(D(a)) ⊆ U` and
`ε : B → 𝓞_L[1/a]` the section, take `N` = the `𝓞_L`-span of `d i`, `i` running over generators
of `I = ker ε` (finitely many: `B` is noetherian). It uses only that `𝒢` is locally of finite type
over `𝓞_L` (not smoothness). -/

/-- **(G-loc)** The local finiteness and fullness of `e*Ω¹_{𝒢/S}`. -/
def OmegaLocal : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (s : PrimeSpectrum (𝓞 L)), ∃ a : 𝓞 L, a ∉ s.asIdeal ∧
    ∃ N : Submodule (𝓞 L) 𝒢.cotangent, N.FG ∧ (∀ x : 𝒢.cotangent, ∃ c : 𝓞 L, c ≠ 0 ∧ c • x ∈ N) ∧
      ∀ s' : PrimeSpectrum (𝓞 L), a ∉ s'.asIdeal →
        N ≤ 𝒢.omegaAt s' ∧ ∀ x ∈ 𝒢.omegaAt s', ∃ t ∉ s'.asIdeal, t • x ∈ N

theorem omegaFG_of_omegaLocal (h : OmegaLocal) : OmegaFG := by
  intro K _ A L _ _ _ 𝒢
  exact fg_iInf_of_local (R := 𝓞 L) (fun s => 𝒢.omegaAt s) fun s => by
    obtain ⟨a, ha, N, hN, -, hloc⟩ := h K A L 𝒢 s
    exact ⟨a, ha, N, hN, fun s' hs' => (hloc s' hs').2⟩

theorem omegaSpans_of_omegaLocal (h : OmegaLocal) : OmegaSpans := by
  intro K _ A L _ _ _ 𝒢
  rw [eq_top_iff]
  rintro y -
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul k x =>
    obtain ⟨c, hc0, hc⟩ := exists_smul_mem_iInf_of_local (R := 𝓞 L) (fun s => 𝒢.omegaAt s)
      (fun s => by
        obtain ⟨a, ha, N, -, hspan, hloc⟩ := h K A L 𝒢 s
        exact ⟨a, ha, N, hspan, fun s' hs' => (hloc s' hs').1⟩) x
    have hcK : algebraMap (𝓞 L) L c ≠ 0 := fun h0 =>
      hc0 (IsFractionRing.injective (𝓞 L) L (by rw [h0, map_zero]))
    have hmem : (1 : L) ⊗ₜ[𝓞 L] (c • x) ∈
        Submodule.span L (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) :=
      Submodule.subset_span ⟨⟨c • x, hc⟩, rfl⟩
    have : k ⊗ₜ[𝓞 L] x = (k * (algebraMap (𝓞 L) L c)⁻¹) • ((1 : L) ⊗ₜ[𝓞 L] (c • x)) := by
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L c, smul_smul, mul_assoc,
        inv_mul_cancel₀ hcK, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hmem

/-- **Main result, sharpened.** `HodgeLatticeTheorem` from `OmegaLocal` (finite type) and
`CotangentRank` (the dimension of the tangent space at the origin). -/
theorem hodgeLatticeTheorem_of_local (h1 : OmegaLocal) (h2 : CotangentRank) :
    HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of (omegaFG_of_omegaLocal h1) h2 (omegaSpans_of_omegaLocal h1)

end ZInQ.DefFaltings.HodgeLattice

/-! ## 5. `OmegaLocal` is a theorem (affine charts, stalks as localizations) -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

local notation "S" => Spec (CommRingCat.of (𝓞 L))

theorem unitSection_comp : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  unfold GroupModel.unitSection
  rw [Over.w]
  rfl

/-- `ε(π^* c) = c`, at the level of stalks. -/
theorem stalkMap_structGerm (s : S) (c : 𝓞 L) :
    𝒢.unitSection.stalkMap s (𝒢.G.left.presheaf.germ ⊤ (𝒢.unitSection s) (TopologicalSpace.Opens.mem_top _)
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c))) =
    (S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have h : 𝒢.unitSection.appTop (𝒢.G.hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c := by
    have h1 : (Scheme.Hom.appTop (𝒢.unitSection ≫ 𝒢.G.hom)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) =
        (Scheme.Hom.appTop (𝟙 (S))).hom ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) := by
      rw [unitSection_comp]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h1
    exact h1
  exact congrArg _ h

theorem structMap_eq (c : 𝓞 L) : 𝒢.structMap c = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit
      (TopologicalSpace.Opens.mem_top _)
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c)) := rfl

theorem isUnit_germ_iff (s : S) (t : 𝓞 L) :
    IsUnit ((S).presheaf.germ ⊤ s (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv t)) ↔
      t ∉ (s : PrimeSpectrum (𝓞 L)).asIdeal := by
  rw [← Scheme.mem_basicOpen _ _ _ (TopologicalSpace.Opens.mem_top _),
    AlgebraicGeometry.basicOpen_eq_of_affine]
  rfl

/-- On an affine open, every element of a stalk is a fraction of sections. -/
theorem exists_germ_frac {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (f : X.presheaf.stalk x) : ∃ b u : Γ(X, U), IsUnit (X.presheaf.germ U x hx u) ∧
      f * X.presheaf.germ U x hx u = X.presheaf.germ U x hx b := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hl := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨b, u⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl f
  exact ⟨b, u, IsLocalization.map_units _ u, h⟩

/-- The specialization `𝒪_{𝒢,e(s')} → 𝒪_{𝒢,ξ}`. -/
noncomputable abbrev spec (s' : S) : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s') →+* 𝒢.genStalk :=
  (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s')).hom

theorem genericPt_specializes (s' : S) : genericPt L ⤳ s' :=
  (PrimeSpectrum.le_iff_specializes (genericPt L) s').mp bot_le

/-- **Residue lemma.** Every germ at `e(s')`, specialized to `ξ`, is congruent modulo `𝔪_ξ` to a
fraction `c/t` with `c, t ∈ 𝓞_L`, `t ∉ s'`. -/
theorem residue (s' : S) (w : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s')) :
    ∃ c t : 𝓞 L, t ∉ (s' : PrimeSpectrum (𝓞 L)).asIdeal ∧
      𝒢.structMap t * spec 𝒢 s' w - 𝒢.structMap c ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  set z := 𝒢.unitSection.stalkMap s' w
  obtain ⟨r, u, hu, hru⟩ := exists_germ_frac (isAffineOpen_top (S)) s'
    (TopologicalSpace.Opens.mem_top _) z
  set iso := Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))
  have hr : iso.inv (iso.hom r) = r := iso.hom_inv_id_apply r
  have hu' : iso.inv (iso.hom u) = u := iso.hom_inv_id_apply u
  refine ⟨iso.hom r, iso.hom u, ?_, ?_⟩
  · rw [← isUnit_germ_iff, hu']; exact hu
  by_contra hnot
  have hunit : IsUnit (𝒢.structMap (iso.hom u) * spec 𝒢 s' w - 𝒢.structMap (iso.hom r)) := by
    by_contra h'
    exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr h')
  let φ : 𝒢.genStalk →+* (S).presheaf.stalk (genericPt L) :=
    (𝒢.unitSection.stalkMap (genericPt L)).hom
  have himg := hunit.map φ
  have hη := genericPt_specializes (L := L) s'
  have hspec : φ (spec 𝒢 s' w) =
      (S).presheaf.stalkSpecializes hη z :=
    Scheme.Hom.stalkSpecializes_stalkMap_apply 𝒢.unitSection (genericPt L) s' hη w
  have hst : ∀ c : 𝓞 L, φ (𝒢.structMap c) =
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) (iso.inv c) :=
    fun c => stalkMap_structGerm 𝒢 (genericPt L) c
  rw [map_sub, map_mul, hspec, hst, hst, hr, hu'] at himg
  have hz : (S).presheaf.stalkSpecializes hη z *
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) u =
      (S).presheaf.germ ⊤ (genericPt L) (TopologicalSpace.Opens.mem_top _) r := by
    have := congrArg ((S).presheaf.stalkSpecializes hη).hom hru
    rw [map_mul, TopCat.Presheaf.germ_stalkSpecializes_apply,
      TopCat.Presheaf.germ_stalkSpecializes_apply] at this
    exact this
  rw [mul_comm, hz, sub_self] at himg
  exact not_isUnit_zero himg

/-- `c • x` on `cot` is `structMap c • x`. -/
theorem smul_cot_of_congr {y : 𝒢.genStalk} {c t : 𝓞 L}
    (h : 𝒢.structMap t * y - 𝒢.structMap c ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (n : 𝒢.cotangent) : t • (y • n) = c • n := by
  change 𝒢.structMap t • (y • n) = 𝒢.structMap c • n
  rw [smul_smul]
  have : 𝒢.structMap t * y = 𝒢.structMap c + (𝒢.structMap t * y - 𝒢.structMap c) := by ring
  rw [this, add_smul]
  have h0 : (𝒢.structMap t * y - 𝒢.structMap c) • n = 0 :=
    Ideal.Cotangent.smul_eq_zero_of_mem h n
  rw [h0, add_zero]

theorem dCls_add (x y : 𝒢.genStalk) (hx : x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hy : y ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hxy : x + y ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨x + y, hxy⟩ = 𝒢.dCls ⟨x, hx⟩ + 𝒢.dCls ⟨y, hy⟩ :=
  (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent.map_add ⟨x, hx⟩ ⟨y, hy⟩

theorem dCls_mul (a g : 𝒢.genStalk) (hg : g ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hag : a * g ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨a * g, hag⟩ = a • 𝒢.dCls ⟨g, hg⟩ :=
  (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent.map_smul a ⟨g, hg⟩

theorem dCls_zero (h : (0 : 𝒢.genStalk) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨0, h⟩ = 0 := by
  unfold GroupModel.dCls
  exact (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent.map_zero

/-- `d g` for a germ `g` (and `0` if `g ∉ 𝔪_ξ`). -/
noncomputable def dOf (g : 𝒢.genStalk) : 𝒢.cotangent := by
  classical
  exact if h : g ∈ IsLocalRing.maximalIdeal 𝒢.genStalk then 𝒢.dCls ⟨g, h⟩ else 0

theorem dOf_eq (g : 𝒢.genStalk) (h : g ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    dOf 𝒢 g = 𝒢.dCls ⟨g, h⟩ := by
  unfold dOf; rw [dif_pos h]

theorem dCls_sum {J : Type*} (T : Finset J) (a g : J → 𝒢.genStalk)
    (hg : ∀ i ∈ T, g i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hy : ∑ i ∈ T, a i * g i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨∑ i ∈ T, a i * g i, hy⟩ = ∑ i ∈ T, a i • dOf 𝒢 (g i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact dCls_zero 𝒢 _
  | insert j T hj ih =>
    have hgT : ∀ i ∈ T, g i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgj := hg j (Finset.mem_insert_self j T)
    have hT : ∑ i ∈ T, a i * g i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk :=
      Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (hgT i hi)
    simp only [Finset.sum_insert hj]
    rw [dCls_add 𝒢 _ _ (Ideal.mul_mem_left _ _ hgj) hT, dCls_mul 𝒢 _ _ hgj, ih hgT hT,
      dOf_eq 𝒢 _ hgj]

/-- A regular function `i` on an open `U ∋ e(s')` whose pullback along the unit section vanishes
near `s'` gives an element `d i` of the local lattice `(ω_𝒢)_{s'}`. -/
theorem dCls_mem_omegaAt (U : 𝒢.G.left.Opens) (i : Γ(𝒢.G.left, U))
    (s' : Spec (CommRingCat.of (𝓞 L))) (hs' : 𝒢.unitSection s' ∈ U)
    (h0 : (Spec (CommRingCat.of (𝓞 L))).presheaf.germ (𝒢.unitSection ⁻¹ᵁ U) s' hs'
      (𝒢.unitSection.app U i) = 0)
    (hm : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit
      ((𝒢.specializes_genericUnit s').mem_open U.isOpen hs') i ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.dCls ⟨_, hm⟩ ∈ 𝒢.omegaAt s' := by
  apply Submodule.subset_span
  refine ⟨𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs' i, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply]; exact h0
  · rw [TopCat.Presheaf.germ_stalkSpecializes_apply]; exact hm
  · congr 2
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- `{x | ∃ t ∉ p, t • x ∈ N}`: the elements of `V` that lie in `N_p`. -/
def locSub {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (p : Ideal R) [p.IsPrime]
    (N : Submodule R V) : Submodule R V where
  carrier := {x | ∃ t ∉ p, t • x ∈ N}
  add_mem' := by
    rintro x y ⟨t, ht, hx⟩ ⟨u, hu, hy⟩
    refine ⟨t * u, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht hu, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  zero_mem' := ⟨1, fun h => (‹p.IsPrime›).ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  smul_mem' := by
    rintro c x ⟨t, ht, hx⟩
    exact ⟨t, ht, by rw [smul_comm]; exact N.smul_mem _ hx⟩

end ZInQ.DefFaltings.HodgeLattice

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open PkgI3 (AbVar)

/-- **`OmegaLocal` holds** (it uses only that `𝒢 → Spec 𝓞_L` is locally of finite type, through
smoothness, and that `e` is a section). -/
theorem omegaLocal : OmegaLocal := by
  intro K _ A L _ _ _ 𝒢 s
  classical
  -- an affine chart `U ∋ e(s)` and a basic open `D(a) ∋ s` with `e(D(a)) ⊆ U`
  obtain ⟨U, hU, hsU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    𝒢.G.left.isBasis_affineOpens) (TopologicalSpace.Opens.mem_top (𝒢.unitSection s))
  obtain ⟨_, ⟨a, rfl⟩, hsa, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show s ∈ ((𝒢.unitSection ⁻¹ᵁ U : (Spec (CommRingCat.of (𝓞 L))).Opens) :
        Set (Spec (CommRingCat.of (𝓞 L)))) from hsU) (𝒢.unitSection ⁻¹ᵁ U).isOpen
  have hD : ∀ s' : PrimeSpectrum (𝓞 L), a ∉ s'.asIdeal → 𝒢.unitSection s' ∈ U :=
    fun s' h => hsub ((PrimeSpectrum.mem_basicOpen _ _).mpr h)
  have hsa' : a ∉ s.asIdeal := (PrimeSpectrum.mem_basicOpen _ _).mp hsa
  -- `Γ(U)` is noetherian; `I = ker(e^* : Γ(U) → Γ(e⁻¹U))` is finitely generated
  have : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  have : IsNoetherianRing Γ(𝒢.G.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  set I : Ideal Γ(𝒢.G.left, U) := RingHom.ker (𝒢.unitSection.app U).hom with hIdef
  obtain ⟨T, hT⟩ : I.FG := IsNoetherian.noetherian I
  have hTI : ∀ i ∈ T, i ∈ I := fun i hi => hT ▸ Submodule.subset_span hi
  have hξU : 𝒢.genericUnit ∈ U := (𝒢.specializes_genericUnit s).mem_open U.isOpen hsU
  set gξ := 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hξU
  have hmI : ∀ i ∈ I, gξ i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
    intro i hi
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    let φ : 𝒢.genStalk →+* (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L) :=
      (𝒢.unitSection.stalkMap (genericPt L)).hom
    have h1 := hunit.map φ
    have h0 : φ (gξ i) = 0 :=
      (Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U (genericPt L) hξU i).trans
        (by rw [RingHom.mem_ker.mp hi, map_zero])
    rw [h0] at h1
    exact not_isUnit_zero h1
  set N : Submodule (𝓞 L) 𝒢.cotangent :=
    Submodule.span (𝓞 L) ((fun i => dOf 𝒢 (gξ i)) '' (T : Set Γ(𝒢.G.left, U))) with hNdef
  have hNfg : N.FG := ⟨T.image fun i => dOf 𝒢 (gξ i), by rw [Finset.coe_image]⟩
  -- (C): the stalks `(ω_𝒢)_{s'}` lie in `N_{s'}`
  have hC : ∀ s' : PrimeSpectrum (𝓞 L), a ∉ s'.asIdeal →
      𝒢.omegaAt s' ≤ locSub s'.asIdeal N := by
    intro s' hs'
    have hs'U := hD s' hs'
    unfold GroupModel.omegaAt
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, hfm, rfl⟩
    obtain ⟨b, u, hu, hfu⟩ := exists_germ_frac hU (𝒢.unitSection s') hs'U f
    have hb : b ∈ I := by
      rw [RingHom.mem_ker]
      have h1 : (𝒢.unitSection.stalkMap s').hom
          (𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs'U b) = 0 := by
        rw [← hfu, map_mul, RingHom.mem_ker.mp hf, zero_mul]
      have h2 := (Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U
        (show Spec (CommRingCat.of (𝓞 L)) from s') hs'U b).symm.trans h1
      exact germ_injective_of_isIntegral (Spec (CommRingCat.of (𝓞 L))) _ hs'U
        (h2.trans (map_zero _).symm)
    rw [← hT] at hb
    obtain ⟨r, -, hr⟩ := Submodule.mem_span_finset.mp hb
    set v := hu.unit⁻¹
    have hf' : f = 𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs'U b * ↑v := by
      rw [← hfu, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    set w : Γ(𝒢.G.left, U) → 𝒢.G.left.presheaf.stalk (𝒢.unitSection s') := fun i =>
      𝒢.G.left.presheaf.germ U (𝒢.unitSection s') hs'U (r i) * ↑v
    have hsf : spec 𝒢 s' f = ∑ i ∈ T, spec 𝒢 s' (w i) * gξ i := by
      rw [hf', ← hr, map_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, smul_eq_mul, map_mul, spec, TopCat.Presheaf.germ_stalkSpecializes_apply]
      ring
    choose c t ht hct using fun i => residue 𝒢 s' (w i)
    refine ⟨∏ i ∈ T, t i, ?_, ?_⟩
    · intro hmem
      obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff).mp hmem
      exact ht i hi
    · have hsum : ∑ i ∈ T, spec 𝒢 s' (w i) * gξ i ∈ IsLocalRing.maximalIdeal 𝒢.genStalk :=
        hsf ▸ hfm
      have he : (⟨spec 𝒢 s' f, hfm⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) =
          ⟨∑ i ∈ T, spec 𝒢 s' (w i) * gξ i, hsum⟩ := Subtype.ext hsf
      change (∏ i ∈ T, t i) • 𝒢.dCls ⟨spec 𝒢 s' f, hfm⟩ ∈ N
      rw [he, dCls_sum 𝒢 T _ _ (fun i hi => hmI i (hTI i hi)), Finset.smul_sum]
      refine Submodule.sum_mem _ fun i hi => ?_
      rw [← Finset.mul_prod_erase T t hi, mul_comm, mul_smul, smul_cot_of_congr 𝒢 (hct i)]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩))
  refine ⟨a, hsa', N, hNfg, ?_, fun s' hs' => ⟨?_, fun x hx => hC s' hs' hx⟩⟩
  · intro x
    have ha0 : a ∉ (genericPt L : PrimeSpectrum (𝓞 L)).asIdeal := by
      intro h
      have : a = 0 := h
      exact hsa' (this ▸ Ideal.zero_mem _)
    have hx : x ∈ 𝒢.omegaAt (genericPt L) := by rw [𝒢.omegaAt_genericPt]; trivial
    obtain ⟨t, ht, htx⟩ := hC (genericPt L) ha0 hx
    exact ⟨t, fun h0 => ht (h0 ▸ Ideal.zero_mem _), htx⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hiI := hTI i hi
    have h := dCls_mem_omegaAt 𝒢 U i s' (hD s' hs')
      (by rw [RingHom.mem_ker.mp hiI, map_zero]) (hmI i hiI)
    have e := dOf_eq 𝒢 _ (hmI i hiI)
    exact (congrArg (· ∈ 𝒢.omegaAt s') e).mpr h

end ZInQ.DefFaltings.HodgeLattice

/-! ## Part 2 -/

set_option linter.style.haveILetI false

namespace ZInQ.H5Glue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open scoped Obj


open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- `ptC τ = Over.map (jL L) (Spec ℂ over L via τ)`. -/
noncomputable def ptCIso (τ : L →+* ℂ) :
    GroupModel.ptC (L := L) τ ≅ (Over.map (jL L)).obj (Over.mk (Spec.map (CommRingCat.ofHom τ))) :=
  Over.isoMk (Iso.refl _) (by
    simp only [GroupModel.ptC, Over.mk_hom, Over.map_obj_hom, Iso.refl_hom, Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- Complex points of a group model are complex points of its generic fibre. -/
noncomputable def ptsEquiv (𝒢 : GroupModel A L) (τ : L →+* ℂ) :
    𝒢.Pts τ ≃ (Over.mk (Spec.map (CommRingCat.ofHom τ)) ⟶ (Over.pullback (jL L)).obj 𝒢.G) :=
  ((ptCIso τ).homCongr (Iso.refl 𝒢.G)).trans ((Over.mapPullbackAdj (jL L)).homEquiv _ _)

theorem ptsEquiv_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) (τ : L →+* ℂ) (p : 𝒢.Pts τ) :
    ptsEquiv 𝒩 τ (p ≫ f) = ptsEquiv 𝒢 τ p ≫ (Over.pullback (jL L)).map f := by
  simp only [ptsEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- **A morphism of group models that is an isomorphism on generic fibres is bijective on
complex points** (at every `τ : L → ℂ`). -/
theorem pts_comp_bijective (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) :
    Function.Bijective (fun p : 𝒢.Pts τ => p ≫ f) := by
  have key : (fun p : 𝒢.Pts τ => p ≫ f) = (ptsEquiv 𝒩 τ).symm ∘
      (fun q => q ≫ (Over.pullback (jL L)).map f) ∘ ptsEquiv 𝒢 τ := by
    funext p
    simp only [Function.comp, ← ptsEquiv_comp, Equiv.symm_apply_apply]
  rw [key]
  refine (Equiv.bijective _).comp (Function.Bijective.comp ?_ (Equiv.bijective _))
  exact ⟨fun a b h => (cancel_mono _).mp h, fun c => ⟨c ≫ inv ((Over.pullback (jL L)).map f),
    by simp⟩⟩


/-- Values of regular functions along a morphism: `s(p ≫ f) = (f^* s)(p)`. -/
theorem evalAt_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    (U : 𝒩.G.left.Opens) (s : Γ(𝒩.G.left, U)) :
    𝒩.evalAt (p ≫ f) U s = 𝒢.evalAt p (f.left ⁻¹ᵁ U) (f.left.app U s) := by
  unfold GroupModel.evalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem dom_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) {τ : L →+* ℂ} {g : ℕ}
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (U : 𝒩.G.left.Opens) :
    𝒩.dom (fun z => Φ z ≫ f) U = 𝒢.dom Φ (f.left ⁻¹ᵁ U) := rfl

/-- **Analytic uniformizations transport along generic isomorphisms** (proved). -/
theorem isAnalyticUniformization_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (h : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    𝒩.IsAnalyticUniformization τ Λ (fun z => Φ z ≫ f) := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  have hb := pts_comp_bijective 𝒢 𝒩 f τ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    simp only
    rw [hmul, MonObj.mul_comp]
  · intro z
    rw [← hker z]
    constructor
    · intro h1
      apply hb.1
      have h1' : Φ z ≫ f = 1 := h1
      show Φ z ≫ f = 1 ≫ f
      rw [h1', MonObj.one_comp]
    · intro h1
      simp only
      rw [h1, MonObj.one_comp]
  · intro q
    obtain ⟨p, rfl⟩ := hb.2 q
    obtain ⟨z, rfl⟩ := hsurj p
    exact ⟨z, rfl⟩
  · intro U
    rw [dom_comp]
    exact hopen _
  · intro U s
    rw [dom_comp]
    simp only [evalAt_comp]
    exact hdiff _ _


/-- A homomorphism of group models sends `ξ_𝒢` to `ξ_𝒩` (as in `Stalk.lean`). -/
theorem map_genericUnit' (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    f.left 𝒢.genericUnit = 𝒩.genericUnit := by
  have h : 𝒢.unitSection ≫ f.left = 𝒩.unitSection := by
    have := congrArg CommaMorphism.left (IsMonHom.one_hom (f := f))
    exact (Over.comp_left (f := η[𝒢.G]) (g := f)).symm.trans this
  have h2 := congrArg (fun φ => φ (genericPt L)) h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h2

/-! ### Jacobian determinants along a generic isomorphism -/

/-- Restriction does not change values at points that land in the smaller open. -/
theorem evalAt_res (𝒢 : GroupModel A L) {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens}
    (i : W ⟶ U) (hp : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U s = 𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) := by
  unfold GroupModel.evalAt
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hp.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  rw [dif_pos hU, dif_pos hp]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- The point `Spec ℂ → Spec 𝓞_L` (through `τ`) is the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : PrimeSpectrum ℂ) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  change PrimeSpectrum.comap (τ.comp (algebraMap (𝓞 L) L)) x = _
  haveI := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  show τ (algebraMap (𝓞 L) L a) ∈ x.asIdeal ↔ a ∈ (⊥ : Ideal (𝓞 L))
  rw [hx, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ τ.injective]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- The unit complex point lands in every open containing `ξ`. -/
theorem one_mem_dom (𝒢 : GroupModel A L) (τ : L →+* ℂ) {W : 𝒢.G.left.Opens}
    (hW : 𝒢.genericUnit ∈ W) : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x ∈ W
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  show (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left ((GroupModel.ptC τ).hom x) ∈ W
  have hx : (GroupModel.ptC (L := L) τ).hom x = genericPt L := ptC_hom_apply τ x
  rw [hx]
  exact hW

/-- `Φ(0) = 1` for a homomorphism `Φ`. -/
theorem map_zero_of_hom {G : Type*} [Group G] {g : ℕ} (Φ : (Fin g → ℂ) → G)
    (h : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact (mul_eq_left.mp this.symm)

/-- **The germ along `Φ ≫ f` of `t` agrees near `0` with the germ along `Φ` of `φ(t)`**, for any
map `φ : 𝒪_{𝒩,ξ} → 𝒪_{𝒢,ξ}` compatible with `f^*` on sections (the stalk map of `f`). -/
theorem germAlong_comp_eventuallyEq (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (φ : 𝒩.genStalk → 𝒢.genStalk)
    (hφ : ∀ (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
      (s : Γ(𝒩.G.left, U)), φ (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
        𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s))
    (t : 𝒩.genStalk) :
    𝒩.germAlong (fun z => Φ z ≫ f) t =ᶠ[nhds 0] 𝒢.germAlong Φ (φ t) := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒩.exists_rep t).choose
  set m := (𝒩.exists_rep t).choose_spec.choose
  set s := (𝒩.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒩.G.left.presheaf.germ U 𝒩.genericUnit m s = t :=
    (𝒩.exists_rep t).choose_spec.choose_spec.choose_spec
  have hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U := by
    show f.left 𝒢.genericUnit ∈ U
    rw [map_genericUnit' 𝒢 𝒩 f]; exact m
  set U' := (𝒢.exists_rep (φ t)).choose
  set m' := (𝒢.exists_rep (φ t)).choose_spec.choose
  set s' := (𝒢.exists_rep (φ t)).choose_spec.choose_spec.choose
  have hs' : 𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' = φ t :=
    (𝒢.exists_rep (φ t)).choose_spec.choose_spec.choose_spec
  have heq : 𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s) =
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' := by
    rw [hs', ← hs, hφ U m hx' s]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ hx' m' _ _ heq
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  filter_upwards [hnhds] with z hz
  show 𝒩.evalAt (Φ z ≫ f) U s = 𝒢.evalAt (Φ z) U' s'
  rw [evalAt_comp, evalAt_res 𝒢 (Φ z) iU hz, hW, ← evalAt_res 𝒢 (Φ z) iV hz]

/-- **Jacobian determinants along a generic isomorphism** (proved): with `φ` as above,
`jacDet (Φ ≫ f) t = jacDet Φ (φ ∘ t)`. -/
theorem jacDet_comp_map (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (φ : 𝒩.genStalk → 𝒢.genStalk)
    (hφ : ∀ (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
      (s : Γ(𝒩.G.left, U)), φ (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
        𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s))
    (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk)
    (t' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (ht : ∀ i, (t' i : 𝒢.genStalk) = φ (t i)) :
    𝒩.jacDet (fun z => Φ z ≫ f) t = 𝒢.jacDet Φ t' := by
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [(germAlong_comp_eventuallyEq 𝒢 𝒩 f Λ Φ hΦ φ hφ (t i)).fderiv_eq, ht i]

/-- The comparison `𝒪_{𝒩,ξ} → 𝒪_{𝒢,ξ}` along a homomorphism `f` (`f(ξ_𝒢) = ξ_𝒩`). -/
noncomputable def genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒩.genStalk ⟶ 𝒢.genStalk :=
  𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes ≫
    f.left.stalkMap 𝒢.genericUnit

/-- `genMap` is `f^*` on germs. -/
theorem genMap_germ (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
    (s : Γ(𝒩.G.left, U)) : (genMap 𝒢 𝒩 f) (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
      𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s) := by
  unfold genMap
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- **Jacobian determinants along a homomorphism**, with the stalk map (proved). -/
theorem jacDet_comp_genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk)
    (t' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk)
    (ht : ∀ i, (t' i : 𝒢.genStalk) = genMap 𝒢 𝒩 f (t i)) :
    𝒩.jacDet (fun z => Φ z ≫ f) t = 𝒢.jacDet Φ t' :=
  jacDet_comp_map 𝒢 𝒩 f Λ Φ hΦ (genMap 𝒢 𝒩 f) (genMap_germ 𝒢 𝒩 f) t t' ht

/-! ### The induced map on cotangent spaces -/

theorem isIso_stalkSpecializes_genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    IsIso (𝒩.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes) :=
  Iso.isIso_hom (𝒩.G.left.presheaf.stalkCongr (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).symm)

theorem genMap_mem_maximalIdeal (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (t : 𝒩.genStalk) (ht : t ∈ IsLocalRing.maximalIdeal 𝒩.genStalk) :
    genMap 𝒢 𝒩 f t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  haveI := isIso_stalkSpecializes_genMap 𝒢 𝒩 f
  set e := 𝒩.G.left.presheaf.stalkSpecializes
    (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes
  have h1 : e t ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
    intro hu
    apply ht
    have := hu.map (inv e).hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  have h2 := map_nonunit (f.left.stalkMap 𝒢.genericUnit).hom _ h1
  exact h2

/-- `genMap` is compatible with the structure maps from `𝓞_L`. -/
theorem genMap_structMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (r : 𝓞 L) :
    genMap 𝒢 𝒩 f (𝒩.structMap r) = 𝒢.structMap r := by
  have e1 : 𝒩.structMap r = 𝒩.G.left.presheaf.germ ⊤ 𝒩.genericUnit trivial
      (𝒩.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  have e2 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  rw [e1, e2, genMap_germ 𝒢 𝒩 f ⊤ (show 𝒩.genericUnit ∈ (⊤ : 𝒩.G.left.Opens) from trivial)
    (show 𝒢.genericUnit ∈ f.left ⁻¹ᵁ (⊤ : 𝒩.G.left.Opens) from trivial)]
  have hw : f.left ≫ 𝒩.G.hom = 𝒢.G.hom := Over.w f
  have : 𝒢.G.hom.appTop = 𝒩.G.hom.appTop ≫ f.left.appTop := by
    rw [← hw, Scheme.Hom.comp_appTop]
  rw [this, CommRingCat.comp_apply]
  rfl

/-- **The induced `𝓞_L`-linear map `ω_{𝒩_L} → ω_{𝒢_L}` on cotangent spaces at `ξ`** (`f^*`). -/
noncomputable def cotMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒩.cotangent →ₗ[𝓞 L] 𝒢.cotangent where
  toFun x := Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
    (IsLocalRing.maximalIdeal 𝒢.genStalk) (genMap 𝒢 𝒩 f).hom.toIntAlgHom
    (fun t ht => genMap_mem_maximalIdeal 𝒢 𝒩 f t ht) x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    let ψ := (genMap 𝒢 𝒩 f).hom.toIntAlgHom
    have h : IsLocalRing.maximalIdeal 𝒩.genStalk ≤
        (IsLocalRing.maximalIdeal 𝒢.genStalk).comap ψ :=
      fun t ht => genMap_mem_maximalIdeal 𝒢 𝒩 f t ht
    change Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
        (IsLocalRing.maximalIdeal 𝒢.genStalk) ψ h (𝒩.structMap r • Ideal.toCotangent _ m) =
      𝒢.structMap r • Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
        (IsLocalRing.maximalIdeal 𝒢.genStalk) ψ h (Ideal.toCotangent _ m)
    rw [← (Ideal.toCotangent _).map_smul, Ideal.mapCotangent_toCotangent,
      Ideal.mapCotangent_toCotangent, ← (Ideal.toCotangent _).map_smul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, ψ, RingHom.toIntAlgHom_apply]
    rw [genMap_structMap]

theorem cotMap_dCls (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (t : IsLocalRing.maximalIdeal 𝒩.genStalk) :
    cotMap 𝒢 𝒩 f (𝒩.dCls t) =
      𝒢.dCls ⟨genMap 𝒢 𝒩 f t, genMap_mem_maximalIdeal 𝒢 𝒩 f t t.2⟩ := rfl

/-! ### `f^*` maps `ω_𝒩` into `ω_𝒢` (step R1) -/

theorem stalkSpecializes_stalkSpecializes_apply {X : Scheme.{0}} {x y z : X} (h : x ⤳ y)
    (h' : y ⤳ z) (t : X.presheaf.stalk z) :
    X.presheaf.stalkSpecializes h (X.presheaf.stalkSpecializes h' t) =
      X.presheaf.stalkSpecializes (h.trans h') t := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem stalkSpecializes_self_apply {X : Scheme.{0}} {x : X} (h : x ⤳ x)
    (t : X.presheaf.stalk x) : X.presheaf.stalkSpecializes h t = t := by
  rw [show h = specializes_refl x from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

theorem unitSection_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒢.unitSection ≫ f.left = 𝒩.unitSection := by
  have := congrArg CommaMorphism.left (IsMonHom.one_hom (f := f))
  exact (Over.comp_left (f := η[𝒢.G]) (g := f)).symm.trans this

/-- At each point `s` of `Spec 𝓞_L`, `f^*` maps the local lattice `(ω_𝒩)_s` into `(ω_𝒢)_s`. -/
theorem cotMap_omegaAt (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (s : Spec (CommRingCat.of (𝓞 L))) (m : 𝒩.cotangent) (hm : m ∈ 𝒩.omegaAt s) :
    cotMap 𝒢 𝒩 f m ∈ 𝒢.omegaAt s := by
  have hE := unitSection_comp 𝒢 𝒩 f
  have hp : f.left (𝒢.unitSection s) = 𝒩.unitSection s :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun φ => φ s) hE)
  let T := 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, hmem, rfl⟩ := hx
    set g' := f.left.stalkMap (𝒢.unitSection s) (T g)
    have hspec : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) g' =
        genMap 𝒢 𝒩 f (𝒩.G.left.presheaf.stalkSpecializes (𝒩.specializes_genericUnit s) g) := by
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
      unfold genMap
      rw [CommRingCat.comp_apply]
      congr 1
      rw [stalkSpecializes_stalkSpecializes_apply, stalkSpecializes_stalkSpecializes_apply]
    have hker : g' ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom := by
      rw [RingHom.mem_ker]
      have h1 := Scheme.Hom.stalkMap_comp 𝒢.unitSection f.left s
      have h2 := Scheme.Hom.stalkMap_congr_hom _ _ hE s
      have h1' : (𝒢.unitSection.stalkMap s) g' = ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h1
        exact this.symm
      have h2' : ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) =
          (𝒩.unitSection.stalkMap s) ((𝒩.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g)) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h2
        exact this
      rw [h1', h2']
      have h4 : ∀ y : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s), y = g →
          (𝒩.unitSection.stalkMap s) y = 0 := by
        rintro y rfl; exact hg
      apply h4
      show 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).symm.specializes (T g) = g
      exact (stalkSpecializes_stalkSpecializes_apply _ _ g).trans (stalkSpecializes_self_apply _ g)
    have hmem' : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) g' ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk := by
      rw [hspec]; exact genMap_mem_maximalIdeal 𝒢 𝒩 f _ hmem
    apply Submodule.subset_span
    refine ⟨g', hker, hmem', ?_⟩
    rw [cotMap_dCls]
    congr 1
    exact Subtype.ext hspec.symm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- **Step R1: `f^* (ω_𝒩) ⊆ ω_𝒢`** (proved). -/
theorem cotMap_omega (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (m : 𝒩.cotangent)
    (hm : m ∈ 𝒩.omega) : cotMap 𝒢 𝒩 f m ∈ 𝒢.omega := by
  rw [GroupModel.omega, Submodule.mem_iInf] at hm ⊢
  exact fun s => cotMap_omegaAt 𝒢 𝒩 f s m (hm s)

/-! ### The map of Hodge lines (step R2, lattice part) -/

/-- `L ⊗ ⋀^g f^* : 𝒩.hodgeSpace g → 𝒢.hodgeSpace g`, `L`-linear. -/
noncomputable def hodgeMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ) :
    𝒩.hodgeSpace g →ₗ[L] 𝒢.hodgeSpace g :=
  (exteriorPower.map g (cotMap 𝒢 𝒩 f)).baseChange L

theorem hodgeMap_wedge (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ)
    (v : Fin g → 𝒩.cotangent) :
    hodgeMap 𝒢 𝒩 f g ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v) =
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => cotMap 𝒢 𝒩 f (v i)) := by
  rw [hodgeMap, LinearMap.baseChange_tmul, exteriorPower.map_apply_ιMulti]
  rfl

/-- **`L ⊗ ⋀^g f^*` maps `⋀^g ω_𝒩` into `⋀^g ω_𝒢`** (proved, from R1). -/
theorem hodgeMap_detLattice (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ)
    (x : 𝒩.hodgeSpace g) (hx : x ∈ 𝒩.detLattice g) : hodgeMap 𝒢 𝒩 f g x ∈ 𝒢.detLattice g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [hodgeMap_wedge]
    apply Submodule.subset_span
    exact ⟨fun i => ⟨cotMap 𝒢 𝒩 f (v i), cotMap_omega 𝒢 𝒩 f _ (v i).2⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul L r y, LinearMap.map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ r hy

theorem hodgeMap_wedgeGerm (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] {g : ℕ}
    (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk) :
    hodgeMap 𝒢 𝒩 f g (𝒩.wedge t) =
      𝒢.wedge (fun i => ⟨genMap 𝒢 𝒩 f (t i), genMap_mem_maximalIdeal 𝒢 𝒩 f _ (t i).2⟩) := by
  unfold GroupModel.wedge
  rw [hodgeMap_wedge]
  rfl

/-! ### Assembly: `HeightAntitone` from two algebraic statements -/

section Assembly

variable {V V' : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]
  [AddCommGroup V'] [Module L V'] [Module (𝓞 L) V'] [IsScalarTower (𝓞 L) L V']

omit [Algebra K L] in
/-- In a Hodge line, every nonzero lattice vector has finite index. -/
theorem secIndex_ne_zero_of_mem {g : ℕ} (D : HodgeData L g V) {v : V} (hv : v ∈ D.lattice)
    (hv0 : v ≠ 0) : secIndex D.lattice v ≠ 0 := by
  obtain ⟨s, hs, hs0, hsi⟩ := D.isLattice
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s hs0).mp D.finrank_eq_one v
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) c
  have hb0 : (b : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 L) L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, zero_smul] at hc
    exact hv0 hc.symm
  have key : b • v = a • s := by
    rw [← hc, ← algebraMap_smul L b, smul_smul, ← algebraMap_smul L a]
    congr 1
    field_simp
  have h1 := secIndex_smul D.lattice hv hv0 b
  have h2 := secIndex_smul D.lattice hs hs0 a
  rw [key, h2] at h1
  intro h
  rw [h, mul_zero] at h1
  have hna : (Algebra.norm ℤ a).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha0)
  exact mul_ne_zero hna hsi h1

omit [NumberField L] in
theorem map_span_singleton_toAddSubgroup (H : V' →ₗ[L] V) (v₀ : V') :
    (Submodule.span (𝓞 L) {v₀}).toAddSubgroup.map H.toAddMonoidHom =
      (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup := by
  ext x
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton,
    LinearMap.toAddMonoidHom_coe]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, by rw [← algebraMap_smul L c, ← algebraMap_smul L c, map_smul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • v₀, ⟨c, rfl⟩, by rw [← algebraMap_smul L c, ← algebraMap_smul L c, map_smul]⟩

omit [NumberField L] in
/-- Indices along an injective map into a lattice. -/
theorem secIndex_le_of_map (H : V' →ₗ[L] V) (hH : Function.Injective H)
    (Λ' : Submodule (𝓞 L) V') (Λ : Submodule (𝓞 L) V) (hle : ∀ x ∈ Λ', H x ∈ Λ) {v₀ : V'}
    (hv₀ : v₀ ∈ Λ') (hne : secIndex Λ (H v₀) ≠ 0) :
    secIndex Λ' v₀ ≠ 0 ∧ secIndex Λ' v₀ ≤ secIndex Λ (H v₀) := by
  have hinj : Function.Injective H.toAddMonoidHom := hH
  have e1 : secIndex Λ' v₀ = ((Submodule.span (𝓞 L) {v₀}).toAddSubgroup.map H.toAddMonoidHom).relIndex
      (Λ'.toAddSubgroup.map H.toAddMonoidHom) :=
    (AddSubgroup.relIndex_map_map_of_injective _ _ hinj).symm
  rw [map_span_singleton_toAddSubgroup] at e1
  have hAB : (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup ≤ Λ'.toAddSubgroup.map H.toAddMonoidHom := by
    rw [← map_span_singleton_toAddSubgroup]
    exact AddSubgroup.map_mono (fun x hx => by
      simp only [Submodule.mem_toAddSubgroup] at hx ⊢
      exact (Submodule.span_le.mpr (by simpa using hv₀)) hx)
  have hBC : Λ'.toAddSubgroup.map H.toAddMonoidHom ≤ Λ.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hle y hy
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hAB hBC
  have hne' : secIndex Λ (H v₀) = (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup.relIndex
      Λ.toAddSubgroup := rfl
  rw [e1]
  have hmul' := hmul.trans hne'.symm
  exact ⟨left_ne_zero_of_mul (hmul'.symm ▸ hne), Nat.le_of_dvd (Nat.pos_of_ne_zero hne)
    (Dvd.intro _ hmul')⟩

omit [NumberField L] in
/-- Pull back Hodge data along an injective `L`-linear map onto a new lattice. -/
noncomputable def pullHodge {g : ℕ} (D : HodgeData L g V) (H : V' →ₗ[L] V)
    (hH : Function.Injective H) (Λ' : Submodule (𝓞 L) V') (hfin : Module.finrank L V' = 1)
    (hlat : ∃ s ∈ Λ', s ≠ 0 ∧ secIndex Λ' s ≠ 0) : HodgeData L g V' where
  lattice := Λ'
  finrank_eq_one := hfin
  isLattice := hlat
  periods := D.periods
  periods_discrete := D.periods_discrete
  periods_isZLattice := D.periods_isZLattice
  coeff τ := (D.coeff τ).comp H
  coeff_ne_zero τ := by
    obtain ⟨s, -, hs0, -⟩ := hlat
    intro h
    have h1 := LinearMap.congr_fun h s
    have hHs : H s ≠ 0 := fun h0 => hs0 (hH (h0.trans (map_zero H).symm))
    exact D.coeff_apply_ne_zero τ hHs h1

omit [Algebra K L] in
theorem modelHeight_pullHodge_le {g : ℕ} (D : HodgeData L g V) (H : V' →ₗ[L] V)
    (hH : Function.Injective H) (Λ' : Submodule (𝓞 L) V') (hfin : Module.finrank L V' = 1)
    (hlat : ∃ s ∈ Λ', s ≠ 0 ∧ secIndex Λ' s ≠ 0) (hle : ∀ x ∈ Λ', H x ∈ D.lattice) :
    (pullHodge D H hH Λ' hfin hlat).modelHeight ≤ D.modelHeight := by
  obtain ⟨v₀, hv₀, hv0, -⟩ := hlat
  have hHv0 : H v₀ ≠ 0 := fun h0 => hv0 (hH (h0.trans (map_zero H).symm))
  have hne := secIndex_ne_zero_of_mem D (hle v₀ hv₀) hHv0
  obtain ⟨hpos, hle'⟩ := secIndex_le_of_map H hH Λ' D.lattice hle hv₀ hne
  rw [(pullHodge D H hH Λ' hfin _).modelHeight_eq hv₀ hv0,
    D.modelHeight_eq (hle v₀ hv₀) hHv0]
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  apply div_le_div_of_nonneg_right _ hd.le
  have : Real.log (secIndex Λ' v₀) ≤ Real.log (secIndex D.lattice (H v₀)) :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hpos) (by exact_mod_cast hle')
  show Real.log (secIndex Λ' v₀) - (1 / 2) * ∑ σ : L →+* ℂ,
      Real.log (torusMetricSq (D.periods σ) (D.coeff σ (H v₀))) ≤ _
  linarith

end Assembly

/-- **`L ⊗ ⋀^g f^*` is bijective for a generic isomorphism** (stated here; proved below as
`hodgeMapBijective`) (it is induced by the
ring isomorphism `genMap`, `stalkIso_of_genericIso`; STANDARD algebra). -/
def HodgeMapBijective : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f], IsIso ((Over.pullback (jL L)).map f) →
    ∀ g : ℕ, Function.Bijective (hodgeMap 𝒢 𝒩 f g)

/-- **A Hodge line contains a nonzero lattice vector** (stated here; proved below as
`hodgeLatticeNonzero_of_omegaSpans omegaSpans`). If `hodgeSpace g` is an
`L`-line, then `⋀^g ω_𝒩 ≠ 0` (`ω_𝒩` spans `ω_{A_L}`: `OmegaSpans`, proved in hodge-lattice; then
the wedges of `ω_𝒩` span the line; STANDARD). -/
def HodgeLatticeNonzero : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel A L) (g : ℕ), Module.finrank L (𝒩.hodgeSpace g) = 1 →
      ∃ v₀ ∈ 𝒩.detLattice g, v₀ ≠ 0

/-- **Glue (as in `Minimal.lean`)** -/
def HeightAntitone : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G), IsMonHom f →
    IsIso ((Over.pullback (jL L)).map f) → 𝒩.height ≤ 𝒢.height

/-- **`HeightAntitone` from `HodgeMapBijective` and `HodgeLatticeNonzero`** (proved). -/
theorem heightAntitone_of (hb : HodgeMapBijective) (hn : HodgeLatticeNonzero) :
    HeightAntitone := by
  intro K _ A L _ _ _ 𝒢 𝒩 f hm hi
  haveI := hm
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
  subst hM
  have hbij := hb K A L M.model 𝒩 f hi g
  set H := hodgeMap M.model 𝒩 f g
  have hfin : Module.finrank L (𝒩.hodgeSpace g) = 1 :=
    (LinearEquiv.ofBijective H hbij).finrank_eq.trans M.hodge.finrank_eq_one
  obtain ⟨v₀, hv₀, hv0⟩ := hn K A L 𝒩 g hfin
  have hle : ∀ x ∈ 𝒩.detLattice g, H x ∈ M.hodge.lattice := fun x hx => by
    rw [M.lattice_eq]; exact hodgeMap_detLattice _ _ f g x hx
  have hHv0 : H v₀ ≠ 0 := fun h0 => hv0 (hbij.1 (h0.trans (map_zero H).symm))
  have hne := secIndex_ne_zero_of_mem M.hodge (hle v₀ hv₀) hHv0
  have hlat : ∃ s ∈ 𝒩.detLattice g, s ≠ 0 ∧ secIndex (𝒩.detLattice g) s ≠ 0 :=
    ⟨v₀, hv₀, hv0, (secIndex_le_of_map H hbij.1 _ _ hle hv₀ hne).1⟩
  let M' : MetrizedModel A L g :=
    { model := 𝒩
      hodge := pullHodge M.hodge H hbij.1 (𝒩.detLattice g) hfin hlat
      lattice_eq := rfl
      arch := fun τ => by
        obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
        refine ⟨fun z => Φ z ≫ f, isAnalyticUniformization_comp _ _ f τ _ Φ hΦ, fun t => ?_⟩
        show M.hodge.coeff τ (H (𝒩.wedge t)) = _
        rw [hodgeMap_wedgeGerm, hc, jacDet_comp_genMap M.model 𝒩 f _ Φ hΦ t
          (fun i => ⟨genMap M.model 𝒩 f (t i), genMap_mem_maximalIdeal _ _ f _ (t i).2⟩)
          (fun i => rfl)] }
  calc (⨅ (g' : ℕ) (M'' : MetrizedModel A L g') (_ : M''.model = 𝒩),
        (M''.hodge.modelHeight : EReal)) ≤ (M'.hodge.modelHeight : EReal) :=
        iInf_le_of_le g (iInf_le_of_le M' (iInf_le_of_le rfl le_rfl))
    _ ≤ (M.hodge.modelHeight : EReal) :=
        EReal.coe_le_coe_iff.mpr (modelHeight_pullHodge_le M.hodge H hbij.1 _ hfin hlat hle)

/-! ### `HodgeMapBijective` (proved): local rings along a generic isomorphism

The lemmas below up to `genericFibreStalkIso` are copied verbatim from
`scratch/hodge-lattice/HodgeLattice.lean` §9-§10 (via `Stalk.lean`, with `toGeneric` renamed `jL`). -/

section StalkSec
open TensorProduct

/-! ### Copied from hodge-lattice §9 -/

/-- **(S')** The projection `X_L = X ×_{𝓞_L} L → X` induces isomorphisms on local rings. -/
def GenericFibreStalkIso : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (X : Over (Spec (CommRingCat.of (𝓞 L))))
    (x : (genericFibre L X).left), IsIso ((pullback.fst X.hom (jL L)).stalkMap x)

section
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem fst_genericFibre_unit :
    letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left ≫
      pullback.fst 𝒢.G.hom (jL L) = jL L ≫ 𝒢.unitSection := by
  let _ : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  change (Functor.LaxMonoidal.ε (Over.pullback (jL L)) ≫
    (Over.pullback (jL L)).map η[𝒢.G]).left ≫ pullback.fst 𝒢.G.hom (jL L) = _
  rw [Over.comp_left, Category.assoc]
  have h1 : ((Over.pullback (jL L)).map η[𝒢.G]).left ≫
      pullback.fst 𝒢.G.hom (jL L) =
      pullback.fst _ (jL L) ≫ (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left := by
    simp
  rw [h1, ← Category.assoc]
  have h2 : (Functor.LaxMonoidal.ε (Over.pullback (jL L))).left ≫
      pullback.snd ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (jL L) = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε (Over.pullback (jL L)))
  have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
    (g := jL L)
  have hc' : pullback.fst ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (jL L) =
      pullback.snd _ _ ≫ jL L := by
    rw [← hc]; exact (Category.comp_id _).symm
  rw [hc', ← Category.assoc, h2, Category.id_comp]
  rfl

omit [NumberField L] in
theorem toGeneric_pt [NumberField L] :
    (jL L) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L) = genericPt L := by
  change PrimeSpectrum.comap (algebraMap (𝓞 L) L) ⟨⊥, Ideal.isPrime_bot⟩ = _
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_bot, genericPt]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- The identity `ξ_L` of the generic fibre. -/
noncomputable def genericFibreUnit : (genericFibre L 𝒢.G).left :=
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)

theorem fst_genericFibreUnit :
    pullback.fst 𝒢.G.hom (jL L) (genericFibreUnit 𝒢) = 𝒢.genericUnit := by
  have h := congrArg (fun φ => φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L))
    (fst_genericFibre_unit 𝒢)
  exact ((Scheme.Hom.comp_apply _ _ _).symm.trans h).trans
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => 𝒢.unitSection y) (toGeneric_pt (L := L))))

end

/-! ### Copied from hodge-lattice §10 -/

/-- Bijectivity of ring maps respects isomorphisms. -/
theorem bijective_respectsIso :
    RingHom.RespectsIso (fun {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) =>
      Function.Bijective f) :=
  ⟨fun f e hf => e.bijective.comp hf, fun f e hf => hf.comp e.bijective⟩

local notation "Pb" => stalkwise (fun {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) =>
      Function.Bijective f)

/-- `Spec (A ⊗_R K) → Spec A` has bijective stalk maps when `K` is a localization of `R`. -/
theorem stalkwise_tensor_localization (R : Type) [CommRing R] (K : Type) [CommRing K]
    [Algebra R K] (M : Submonoid R) [IsLocalization M K] (A : Type) [CommRing A] [Algebra R A] :
    Pb (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K)))) := by
  have := stalkwise_respectsIso bijective_respectsIso
  set M' := Algebra.algebraMapSubmonoid A M
  let e : A ⊗[R] K ≃ₐ[A] Localization M' := IsLocalization.algEquiv M' _ _
  have hfac : CommRingCat.ofHom (algebraMap A (A ⊗[R] K)) =
      CommRingCat.ofHom (algebraMap A (Localization M')) ≫
        CommRingCat.ofHom e.symm.toAlgHom.toRingHom := by
    ext a
    simp
  have : IsIso (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) :=
    ⟨⟨CommRingCat.ofHom e.toAlgHom.toRingHom,
      CommRingCat.hom_ext (RingHom.ext fun y => e.apply_symm_apply y),
      CommRingCat.hom_ext (RingHom.ext fun y => e.symm_apply_apply y)⟩⟩
  rw [hfac, Spec.map_comp]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  intro x
  have h := isIso_specMap_stalkMap_localization (CommRingCat.of A) M' x
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- On an affine chart: `Spec A ×_{𝓞_L} Spec L → Spec A` has bijective stalk maps. -/
theorem stalkwise_fst_toGeneric {L : Type} [Field L] [NumberField L] {A : CommRingCat}
    (g : Spec A ⟶ Spec (CommRingCat.of (𝓞 L))) : (Pb) (pullback.fst g (jL L)) := by
  have : (Pb).RespectsIso := stalkwise_respectsIso bijective_respectsIso
  let φ := Spec.preimage g
  letI : Algebra (𝓞 L) A := φ.hom.toAlgebra
  have hg : g = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) A)) := by
    rw [← Spec.map_preimage g]; rfl
  have he2 : (pullback.congrHom hg rfl).hom ≫ pullback.fst _ _ = pullback.fst g (jL L) := by
    simp [pullback.congrHom]
  rw [← he2]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  rw [← pullbackSpecIso_hom_fst' (𝓞 L) A L]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  exact stalkwise_tensor_localization (𝓞 L) L (nonZeroDivisors (𝓞 L)) A

/-- **`GenericFibreStalkIso` holds**: base change along `Spec L → Spec 𝓞_L` does not change local
rings (Zariski-local on the target; on an affine chart it is `Spec (A ⊗_{𝓞_L} L) → Spec A`, a
localization). -/
theorem genericFibreStalkIso : GenericFibreStalkIso := by
  intro L _ _ X x
  have : (Pb).RespectsIso := stalkwise_respectsIso bijective_respectsIso
  have : IsZariskiLocalAtTarget (Pb) :=
    stalkwiseIsZariskiLocalAtTarget_of_respectsIso bijective_respectsIso
  suffices H : (Pb) (pullback.fst X.hom (jL L)) from
    (ConcreteCategory.isIso_iff_bijective _).mpr (H x)
  refine IsZariskiLocalAtTarget.of_openCover X.left.affineOpenCover.openCover ?_
  intro i
  show (Pb) (pullback.snd (pullback.fst X.hom (jL L)) (X.left.affineOpenCover.f i))
  have he : (pullbackSymmetry (pullback.fst X.hom (jL L)) (X.left.affineOpenCover.f i) ≪≫
      pullbackRightPullbackFstIso X.hom (jL L) (X.left.affineOpenCover.f i)).hom ≫
        pullback.fst (X.left.affineOpenCover.f i ≫ X.hom) (jL L) =
      pullback.snd (pullback.fst X.hom (jL L)) (X.left.affineOpenCover.f i) := by
    simp
  rw [← he]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  exact stalkwise_fst_toGeneric _



section NewStalk
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **A generic isomorphism induces an isomorphism of local rings at `ξ`.** -/
theorem stalkIso_of_genericIso (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    [hF : IsIso ((Over.pullback (jL L)).map f)] :
    IsIso (f.left.stalkMap 𝒢.genericUnit) := by
  have hsq : pullback.fst 𝒢.G.hom (jL L) ≫ f.left =
      ((Over.pullback (jL L)).map f).left ≫ pullback.fst 𝒩.G.hom (jL L) := by
    simp
  haveI : IsIso ((Over.pullback (jL L)).map f).left := by
    have := Functor.map_isIso (Over.forget _) ((Over.pullback (jL L)).map f)
    exact this
  haveI : IsIso (((Over.pullback (jL L)).map f).left.stalkMap (genericFibreUnit 𝒢)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  haveI : IsIso ((pullback.fst 𝒢.G.hom (jL L)).stalkMap (genericFibreUnit 𝒢)) :=
    genericFibreStalkIso L 𝒢.G _
  haveI : IsIso ((pullback.fst 𝒩.G.hom (jL L)).stalkMap
      (((Over.pullback (jL L)).map f).left (genericFibreUnit 𝒢))) :=
    genericFibreStalkIso L 𝒩.G _
  have h1 := Scheme.Hom.stalkMap_comp (pullback.fst 𝒢.G.hom (jL L)) f.left
    (genericFibreUnit 𝒢)
  have h2 := Scheme.Hom.stalkMap_comp ((Over.pullback (jL L)).map f).left
    (pullback.fst 𝒩.G.hom (jL L)) (genericFibreUnit 𝒢)
  have h3 := Scheme.Hom.stalkMap_congr_hom _ _ hsq (genericFibreUnit 𝒢)
  have hc : IsIso ((pullback.fst 𝒢.G.hom (jL L) ≫ f.left).stalkMap (genericFibreUnit 𝒢)) := by
    rw [h3, h2]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) ?_
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›
  haveI : IsIso (f.left.stalkMap ((pullback.fst 𝒢.G.hom (jL L)) (genericFibreUnit 𝒢)) ≫
      (pullback.fst 𝒢.G.hom (jL L)).stalkMap (genericFibreUnit 𝒢)) := by
    rw [← h1]; exact hc
  haveI := IsIso.of_isIso_comp_right
    (f.left.stalkMap ((pullback.fst 𝒢.G.hom (jL L)) (genericFibreUnit 𝒢)))
    ((pullback.fst 𝒢.G.hom (jL L)).stalkMap (genericFibreUnit 𝒢))
  rw [← fst_genericFibreUnit 𝒢]
  infer_instance

end NewStalk

end StalkSec

/-- `genMap` is an isomorphism for a generic isomorphism. -/
theorem isIso_genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] : IsIso (genMap 𝒢 𝒩 f) := by
  haveI := isIso_stalkSpecializes_genMap 𝒢 𝒩 f
  haveI := stalkIso_of_genericIso 𝒢 𝒩 f
  unfold genMap
  infer_instance

/-- `f^*` on cotangent spaces is bijective for a generic isomorphism. -/
theorem cotMap_bijective (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] : Function.Bijective (cotMap 𝒢 𝒩 f) := by
  haveI := isIso_genMap 𝒢 𝒩 f
  let e : 𝒩.genStalk ≃+* 𝒢.genStalk := (asIso (genMap 𝒢 𝒩 f)).commRingCatIsoToRingEquiv
  have he : ∀ x, e x = genMap 𝒢 𝒩 f x := fun x => rfl
  have hmax : ∀ x, x ∈ IsLocalRing.maximalIdeal 𝒩.genStalk ↔
      e x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
    intro x
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff e x).symm
  have hcomap : (IsLocalRing.maximalIdeal 𝒢.genStalk).comap e =
      IsLocalRing.maximalIdeal 𝒩.genStalk := by
    ext x; exact (hmax x).symm
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    have h0 := hx
    change Ideal.toCotangent _ ⟨genMap 𝒢 𝒩 f m, _⟩ = 0 at h0
    rw [Ideal.toCotangent_eq_zero] at h0
    change (IsLocalRing.maximalIdeal 𝒩.genStalk).toCotangent m =
      (0 : (IsLocalRing.maximalIdeal 𝒩.genStalk).Cotangent)
    rw [Ideal.toCotangent_eq_zero]
    have h1 : (m : 𝒩.genStalk) ∈ ((IsLocalRing.maximalIdeal 𝒢.genStalk) ^ 2).comap e := by
      rw [Ideal.mem_comap, he]; exact h0
    rw [← Ideal.map_symm, Ideal.map_pow, Ideal.map_symm, hcomap] at h1
    exact h1
  · intro y
    obtain ⟨m', rfl⟩ := Ideal.toCotangent_surjective _ y
    have hm : e.symm m' ∈ IsLocalRing.maximalIdeal 𝒩.genStalk := by
      rw [hmax, RingEquiv.apply_symm_apply]; exact m'.2
    refine ⟨Ideal.toCotangent _ ⟨e.symm m', hm⟩, ?_⟩
    change Ideal.toCotangent _ ⟨genMap 𝒢 𝒩 f (e.symm m'), _⟩ = _
    congr 1
    apply Subtype.ext
    show e (e.symm m') = m'
    exact RingEquiv.apply_symm_apply e m'

omit [NumberField L] in
/-- `L ⊗ ⋀^g φ` is bijective if `φ` is. -/
theorem baseChange_map_bijective {M N : Type*} [AddCommGroup M] [Module (𝓞 L) M] [AddCommGroup N]
    [Module (𝓞 L) N] (g : ℕ) (φ : M →ₗ[𝓞 L] N) (hφ : Function.Bijective φ) :
    Function.Bijective ((exteriorPower.map g φ).baseChange L) := by
  let e := LinearEquiv.ofBijective φ hφ
  let ψ := (exteriorPower.map g (e.symm : N →ₗ[𝓞 L] M)).baseChange L
  have h1 : ψ ∘ₗ (exteriorPower.map g φ).baseChange L = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, ← exteriorPower.map_comp]
    have : (e.symm : N →ₗ[𝓞 L] M) ∘ₗ φ = LinearMap.id := by
      ext x; exact e.symm_apply_apply x
    rw [this, exteriorPower.map_id, LinearMap.baseChange_id]
  have h2 : (exteriorPower.map g φ).baseChange L ∘ₗ ψ = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, ← exteriorPower.map_comp]
    have : φ ∘ₗ (e.symm : N →ₗ[𝓞 L] M) = LinearMap.id := by
      ext x; exact e.apply_symm_apply x
    rw [this, exteriorPower.map_id, LinearMap.baseChange_id]
  refine Function.bijective_iff_has_inverse.mpr ⟨ψ, fun x => ?_, fun x => ?_⟩
  · exact LinearMap.congr_fun h1 x
  · exact LinearMap.congr_fun h2 x

/-- **Glue `HodgeMapBijective`, proved.** -/
theorem hodgeMapBijective : HodgeMapBijective := by
  intro K _ A L _ _ _ 𝒢 𝒩 f _ hi g
  exact baseChange_map_bijective g _ (cotMap_bijective 𝒢 𝒩 f)

/-- **`HeightAntitone` from `HodgeLatticeNonzero` alone** (proved). -/
theorem heightAntitone_of_hodgeLatticeNonzero (hn : HodgeLatticeNonzero) : HeightAntitone :=
  heightAntitone_of hodgeMapBijective hn

/-! ### `HodgeLatticeNonzero` from `OmegaSpans` (proved; `OmegaSpans` is proved in hodge-lattice) -/

/-- (copied verbatim from `scratch/hodge-lattice/HodgeLattice.lean` §2, where it is proved as
`omegaSpans_of_omegaLocal omegaLocal`) `ω_𝒢` spans `ω_{A_L}` over `L`. -/
def OmegaSpans : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L),
    Submodule.span L (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) = ⊤

/-- Every cotangent vector has a nonzero `𝓞_L`-multiple in `ω`. -/
theorem exists_smul_mem_omega (h : OmegaSpans) (𝒩 : GroupModel A L) (x : 𝒩.cotangent) :
    ∃ D : 𝓞 L, D ≠ 0 ∧ D • x ∈ 𝒩.omega := by
  have hx : (1 : L) ⊗ₜ[𝓞 L] x ∈ Submodule.span L
      (Set.range fun w : 𝒩.omega => (1 : L) ⊗ₜ[𝓞 L] (w : 𝒩.cotangent)) := by
    rw [h K A L 𝒩]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 L)) c.support c
  choose a ha using fun w (hw : w ∈ c.support) => hd w hw
  set y : 𝒩.cotangent := ∑ w ∈ c.support.attach, a w.1 w.2 • (w.1 : 𝒩.cotangent) with hy_def
  have hy : y ∈ 𝒩.omega := Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ w.1.2
  have key : (TensorProduct.mk (𝓞 L) L 𝒩.cotangent 1) ((d : 𝓞 L) • x) =
      TensorProduct.mk (𝓞 L) L 𝒩.cotangent 1 y := by
    simp only [TensorProduct.mk_apply, hy_def, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    rw [← hc, Finsupp.sum, Finset.smul_sum, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun w _ => ?_
    symm
    rw [← algebraMap_smul L (a w.1 w.2), ha w.1 w.2, smul_assoc]
  have : IsLocalizedModule (nonZeroDivisors (𝓞 L)) (TensorProduct.mk (𝓞 L) L 𝒩.cotangent 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L _).mpr
      (TensorProduct.isBaseChange _ _ _)
  obtain ⟨e, he⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors (𝓞 L)) key
  refine ⟨(e : 𝓞 L) * d, mul_ne_zero (nonZeroDivisors.ne_zero e.2)
    (nonZeroDivisors.ne_zero d.2), ?_⟩
  have he' : (e : 𝓞 L) • ((d : 𝓞 L) • x) = (e : 𝓞 L) • y := he
  rw [mul_smul, he']
  exact Submodule.smul_mem _ _ hy

/-- **`HodgeLatticeNonzero` from `OmegaSpans`** (proved). -/
theorem hodgeLatticeNonzero_of_omegaSpans (h : OmegaSpans) : HodgeLatticeNonzero := by
  intro K _ A L _ _ _ 𝒩 g hfin
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hpure : ∀ v : Fin g → 𝒩.cotangent,
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v = 0 := by
    intro v
    choose D hD hDm using fun i => exists_smul_mem_omega h 𝒩 (v i)
    have h1 : exteriorPower.ιMulti (𝓞 L) g (fun i => D i • v i) =
        (∏ i, D i) • exteriorPower.ιMulti (𝓞 L) g v :=
      MultilinearMap.map_smul_univ _ _ _
    have h2 : (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => D i • v i) = 0 :=
      hcon _ (Submodule.subset_span ⟨fun i => ⟨D i • v i, hDm i⟩, rfl⟩)
    rw [h1, TensorProduct.tmul_smul, ← algebraMap_smul L] at h2
    have hP : algebraMap (𝓞 L) L (∏ i, D i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr
        (Finset.prod_ne_zero_iff.mpr fun i _ => hD i)
    calc (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v
        = (algebraMap (𝓞 L) L (∏ i, D i))⁻¹ • (algebraMap (𝓞 L) L (∏ i, D i) •
          ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v)) := by
          rw [smul_smul, inv_mul_cancel₀ hP, one_smul]
      _ = 0 := by rw [h2, smul_zero]
  have hall : ∀ x : 𝒩.hodgeSpace g, x = 0 := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul l y =>
      have hy : y ∈ Submodule.span (𝓞 L) (Set.range (exteriorPower.ιMulti (𝓞 L) g)) := by
        rw [exteriorPower.ιMulti_span]; trivial
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨v, rfl⟩ := hz
        have : l ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v =
            l • ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, hpure, smul_zero]
      | zero => rw [TensorProduct.tmul_zero]
      | add a b _ _ ha hb => rw [TensorProduct.tmul_add, ha, hb, add_zero]
      | smul r a _ ha => rw [TensorProduct.tmul_smul, ha, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  haveI : Subsingleton (𝒩.hodgeSpace g) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  rw [Module.finrank_zero_of_subsingleton] at hfin
  exact zero_ne_one hfin

/-- **`HeightAntitone` from `OmegaSpans`** (proved; `OmegaSpans` is a theorem of hodge-lattice). -/
theorem heightAntitone_of_omegaSpans (h : OmegaSpans) : HeightAntitone :=
  heightAntitone_of_hodgeLatticeNonzero (hodgeLatticeNonzero_of_omegaSpans h)


/-! ### The Néron comparison map (from `Minimal.lean`) -/

section Abstract

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor that is injective on `Hom(𝟙, Y)` and `Hom(X ⊗ X, Y)` reflects
monoid morphisms `X → Y`. -/
theorem isMonHom_of_map {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom (F.map f)]
    (h1 : ∀ g g' : 𝟙_ C ⟶ Y, F.map g = F.map g' → g = g')
    (h2 : ∀ g g' : X ⊗ X ⟶ Y, F.map g = F.map g' → g = g') : IsMonHom f where
  one_hom := by
    apply h1
    rw [← cancel_epi (Functor.LaxMonoidal.ε F), F.map_comp, ← Category.assoc]
    exact IsMonHom.one_hom (f := F.map f)
  mul_hom := by
    apply h2
    rw [← cancel_epi (Functor.LaxMonoidal.μ F X X), F.map_comp, ← Category.assoc]
    have hm := IsMonHom.mul_hom (f := F.map f)
    refine hm.trans ?_
    rw [F.map_comp, Functor.obj.μ_def, ← Functor.LaxMonoidal.μ_natural_assoc]

end Abstract

section Neron

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

instance smooth_tensor (𝒢 : GroupModel A L) : Smooth (𝒢.G ⊗ 𝒢.G).hom := by
  show Smooth (pullback.fst 𝒢.G.hom 𝒢.G.hom ≫ 𝒢.G.hom); infer_instance

instance smooth_unit : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom := by
  dsimp; infer_instance

/-- The comparison map `𝒢 → 𝒩` to a Néron model (unique with `F(f) ≫ gen_𝒩 = gen_𝒢`). -/
theorem neron_lift {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) :
    ∃ f : 𝒢.G ⟶ 𝒩.G, (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom :=
  (h𝒩 𝒢.G).2 𝒢.gen.hom

/-- Injectivity of `F = Over.pullback (jL L)` on maps from a smooth scheme into a Néron model. -/
theorem neron_map_injective {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    {Y : Over (Spec (CommRingCat.of (𝓞 L)))} [Smooth Y.hom] (g g' : Y ⟶ 𝒩.G)
    (h : (Over.pullback (jL L)).map g = (Over.pullback (jL L)).map g') : g = g' :=
  (h𝒩 Y).1 (by simp only [h])

/-- **The Néron comparison map is a homomorphism of group schemes**, and an isomorphism on
generic fibres. -/
theorem neron_lift_isMonHom {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    (hf : (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom) :
    IsMonHom f ∧ IsIso ((Over.pullback (jL L)).map f) := by
  let F := Over.pullback (jL L)
  let e₁ : F.obj 𝒢.G ≅ (A.baseChange L).X := 𝒢.gen
  let e₂ : F.obj 𝒩.G ≅ (A.baseChange L).X := 𝒩.gen
  have g1 : IsMonHom e₁.hom := 𝒢.gen_hom
  have g2 : IsMonHom e₂.hom := 𝒩.gen_hom
  have hiso : F.map f = e₁.hom ≫ e₂.inv := by
    rw [Iso.eq_comp_inv]; exact hf
  refine ⟨?_, by rw [hiso]; infer_instance⟩
  have : IsMonHom (F.map f) := by rw [hiso]; infer_instance
  exact isMonHom_of_map F f (fun g g' => neron_map_injective h𝒩 g g')
    (fun g g' => neron_map_injective h𝒩 g g')

/-- **`NeronModelMinimal` from `HeightAntitone`.** -/
theorem neronModelMinimal_of_heightAntitone (h : HeightAntitone) : NeronModelMinimal := by
  intro K _ A L _ _ _ 𝒩 𝒢 h𝒩
  obtain ⟨f, hf⟩ := neron_lift h𝒩 𝒢
  obtain ⟨hm, hi⟩ := neron_lift_isMonHom h𝒩 𝒢 f hf
  exact h K A L 𝒢 𝒩 f hm hi

end Neron


/-! ### Final -/

/-- `OmegaSpans` (hodge-lattice's theorem). -/
theorem omegaSpans : OmegaSpans :=
  HodgeLattice.omegaSpans_of_omegaLocal HodgeLattice.omegaLocal

/-- **Glue `HeightAntitone`, proved.** A homomorphism of group models that is an isomorphism on
generic fibres does not increase the height. -/
theorem heightAntitone : HeightAntitone := heightAntitone_of_omegaSpans omegaSpans

/-- **`NeronModelMinimal`, proved.** Over every `L`, a Néron model has the least height among the
group models of `A_L`. -/
theorem neronModelMinimal : NeronModelMinimal :=
  neronModelMinimal_of_heightAntitone heightAntitone


/-! ## Part 3 -/
/-! ## §1 Base change of group models -/



/-- (copied from h5-neron) -/
def IsBaseChangeOf {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L]
    [Algebra K L] [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) : Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

/-- (copied from h5-neron) **Glue H4b.** -/
def GroupModelBaseChangeExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L), ∃ 𝒢' : GroupModel A L', IsBaseChangeOf 𝒢' 𝒢

section Abstract

variable {S S' T T' B : Scheme.{0}}

/-- `(f ≫ g)^* G → f^* g^* G`, with the iterated target type. (copied from h5-neron) -/
noncomputable def pbCompHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback (f ≫ g)).obj G ⟶ (Over.pullback f).obj ((Over.pullback g).obj G) :=
  (Over.pullbackComp f g).hom.app G

/-- `f^* g^* G → (f ≫ g)^* G`. (copied from h5-neron) -/
noncomputable def pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback f).obj ((Over.pullback g).obj G) ⟶ (Over.pullback (f ≫ g)).obj G :=
  (Over.pullbackComp f g).inv.app G

/-- (copied from h5-neron) -/
theorem isMonHom_pbCompHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompHom f g G) := by
  have h := ((Functor.mapMonNatIso (Over.pullbackComp f g)).hom.app (Mon.mk G) ≫
    (Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).hom.app
      (Mon.mk G)).isMonHom_hom
  have e : pbCompHom f g G = pbCompHom f g G ≫ 𝟙 _ := (Category.comp_id _).symm
  rw [e]
  exact h

/-- (copied from h5-neron) -/
theorem isMonHom_pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompInv f g G) := by
  have h := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).inv.app
      (Mon.mk G) ≫ (Functor.mapMonNatIso (Over.pullbackComp f g)).inv.app (Mon.mk G)).isMonHom_hom
  have e : pbCompInv f g G = 𝟙 _ ≫ pbCompInv f g G := (Category.id_comp _).symm
  rw [e]
  exact h

/-- `(f ≫ g)^* G ≅ f^* g^* G` with explicit components. (copied from h5-neron) -/
noncomputable def pbCompIso {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback (f ≫ g)).obj G ≅ (Over.pullback f).obj ((Over.pullback g).obj G) :=
  ⟨pbCompHom f g G, pbCompInv f g G, ((Over.pullbackComp f g).app G).hom_inv_id,
    ((Over.pullbackComp f g).app G).inv_hom_id⟩

/-- `f^* G ≅ g^* G` for `f = g`. -/
noncomputable def pbEqIso {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y) :
    (Over.pullback f).obj G ≅ (Over.pullback g).obj G :=
  eqToIso (by subst h; rfl)

theorem isMonHom_pbEqIso {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y)
    [MonObj G] : IsMonHom (pbEqIso h G).hom := by
  subst h
  exact (inferInstance : IsMonHom (𝟙 ((Over.pullback f).obj G)))

/-- The generic-fibre identification of a base change, for abstract morphisms:
`a^* b^* G ≅ (a ≫ b)^* G = (c ≫ d)^* G ≅ c^* d^* G ≅ c^* k^* X ≅ (c ≫ k)^* X = k'^* X`. -/
noncomputable def genBC (a : T' ⟶ S') (b : S' ⟶ S) (c : T' ⟶ T) (d : T ⟶ S) (k : T ⟶ B)
    (k' : T' ⟶ B) (h1 : a ≫ b = c ≫ d) (h2 : c ≫ k = k') (G : Over S) (X : Over B)
    (gen : (Over.pullback d).obj G ≅ (Over.pullback k).obj X) :
    (Over.pullback a).obj ((Over.pullback b).obj G) ≅ (Over.pullback k').obj X :=
  (pbCompIso a b G).symm ≪≫ pbEqIso h1 G ≪≫ pbCompIso c d G ≪≫
    (Over.pullback c).mapIso gen ≪≫ (pbCompIso c k X).symm ≪≫ pbEqIso h2 X

theorem genBC_isMonHom (a : T' ⟶ S') (b : S' ⟶ S) (c : T' ⟶ T) (d : T ⟶ S) (k : T ⟶ B)
    (k' : T' ⟶ B) (h1 : a ≫ b = c ≫ d) (h2 : c ≫ k = k') (G : Over S) [GrpObj G] (X : Over B)
    [GrpObj X] (gen : (Over.pullback d).obj G ≅ (Over.pullback k).obj X)
    (hgen : letI : GrpObj ((Over.pullback d).obj G) := Functor.grpObjObj
      letI : GrpObj ((Over.pullback k).obj X) := Functor.grpObjObj
      IsMonHom gen.hom) :
    letI : GrpObj ((Over.pullback b).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback a).obj ((Over.pullback b).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback k').obj X) := Functor.grpObjObj
    IsMonHom (genBC a b c d k k' h1 h2 G X gen).hom := by
  have c1 := isMonHom_pbCompInv a b G
  have c2 := isMonHom_pbEqIso h1 G
  have c3 := isMonHom_pbCompHom c d G
  have c5 := isMonHom_pbCompInv c k X
  have c6 := isMonHom_pbEqIso h2 X
  have c4 : IsMonHom ((Over.pullback c).map gen.hom) := inferInstance
  have e : (genBC a b c d k k' h1 h2 G X gen).hom = pbCompInv a b G ≫ (pbEqIso h1 G).hom ≫
      pbCompHom c d G ≫ (Over.pullback c).map gen.hom ≫ pbCompInv c k X ≫ (pbEqIso h2 X).hom :=
    rfl
  rw [e]
  infer_instance

end Abstract

section Concrete

variable {K : Type} [Field K] (L L' : Type) [Field L] [Algebra K L]
    [Field L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']

theorem square1 :
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))) =
      Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem square2 :
    Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable [NumberField L] [NumberField L']

/-- The base change `𝒢 ×_{𝓞_L} 𝓞_{L'}` of a group model, as a group model of `A_{L'}`. -/
noncomputable def GroupModel.baseChange {A : AbVar K} (𝒢 : GroupModel A L) : GroupModel A L' :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G).hom := by dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  { G := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G
    gen := genBC _ _ _ _ _ _ (square1 L L') (square2 L L') 𝒢.G A.X 𝒢.gen
    gen_hom := genBC_isMonHom _ _ _ _ _ _ (square1 L L') (square2 L L') 𝒢.G A.X 𝒢.gen
      𝒢.gen_hom }

/-- **Glue H4b, proved.** -/
theorem groupModelBaseChangeExists : GroupModelBaseChangeExists := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢
  refine ⟨GroupModel.baseChange L L' 𝒢, Iso.refl (GroupModel.baseChange L L' 𝒢).G, ?_⟩
  exact (inferInstance : IsMonHom (𝟙 (GroupModel.baseChange L L' 𝒢).G))

end Concrete


/-! ## §3 Open subgroup models are generic isomorphisms -/

section OpenSubSec



variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]


/-- The base change of an open immersion along any `j` is an open immersion (for `Over.pullback`). -/
theorem isOpenImmersion_pullback_map {S S' : Scheme.{0}} (j : S' ⟶ S) {U G : Over S} (f : U ⟶ G)
    [IsOpenImmersion f.left] : IsOpenImmersion ((Over.pullback j).map f).left := by
  have t : IsPullback (pullback.fst G.hom j) (pullback.snd G.hom j) G.hom j :=
    IsPullback.of_hasPullback _ _
  have p : pullback.fst U.hom j ≫ f.left = ((Over.pullback j).map f).left ≫ pullback.fst G.hom j := by
    simp
  have s : IsPullback (pullback.fst U.hom j) (((Over.pullback j).map f).left ≫ pullback.snd G.hom j)
      (f.left ≫ G.hom) j := by
    have e1 : ((Over.pullback j).map f).left ≫ pullback.snd G.hom j = pullback.snd U.hom j := by
      simp
    have e2 : f.left ≫ G.hom = U.hom := Over.w f
    rw [e1, e2]
    exact IsPullback.of_hasPullback _ _
  have sq := IsPullback.of_bot s p t
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›

/-- An open immersion `h : X → X` over `Spec L` of an abelian variety is an isomorphism. -/
theorem isIso_of_openImmersion_self (B : AbVar L) (h : B.X ⟶ B.X) [IsOpenImmersion h.left] :
    IsIso h := by
  have hw : h.left ≫ B.X.hom = B.X.hom := Over.w h
  haveI : UniversallyClosed (h.left ≫ B.X.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed h.left := UniversallyClosed.of_comp_of_isSeparated h.left B.X.hom
  haveI : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton B.X.hom
  have hrange : Set.range h.left = Set.univ := by
    have hc : IsClosed (Set.range h.left) := h.left.isClosedMap.isClosed_range
    have ho : IsOpen (Set.range h.left) := h.left.isOpenEmbedding.isOpen_range
    obtain ⟨x⟩ := (inferInstance : Nonempty B.X.left)
    exact IsClopen.eq_univ ⟨hc, ho⟩ ⟨h.left x, x, rfl⟩
  haveI : Surjective h.left := ⟨fun y => by
    have : y ∈ Set.range h.left := hrange ▸ Set.mem_univ y
    exact this⟩
  haveI : IsIso h.left := (isIso_iff_isOpenImmersion_and_surjective h.left).mpr ⟨‹_›, ‹_›⟩
  haveI : IsIso ((Over.forget _).map h) := inferInstanceAs (IsIso h.left)
  exact isIso_of_reflects_iso h (Over.forget _)

/-- **Open subgroup models agree generically** (proved). -/
theorem genericIso_of_openImmersion (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G)
    [IsOpenImmersion f.left] : IsIso ((Over.pullback (jL L)).map f) := by
  let F := Over.pullback (jL L)
  let e₁ : F.obj 𝒰.G ≅ (A.baseChange L).X := 𝒰.gen
  let e₂ : F.obj 𝒢.G ≅ (A.baseChange L).X := 𝒢.gen
  haveI : IsOpenImmersion (F.map f).left := isOpenImmersion_pullback_map (jL L) f
  let h : (A.baseChange L).X ⟶ (A.baseChange L).X := e₁.inv ≫ F.map f ≫ e₂.hom
  haveI : IsIso e₁.inv.left := Functor.map_isIso (Over.forget _) e₁.inv
  haveI : IsIso e₂.hom.left := Functor.map_isIso (Over.forget _) e₂.hom
  haveI : IsOpenImmersion h.left := by
    show IsOpenImmersion (e₁.inv.left ≫ (F.map f).left ≫ e₂.hom.left)
    infer_instance
  haveI := isIso_of_openImmersion_self (A.baseChange L) h
  have : F.map f = e₁.hom ≫ h ≫ e₂.inv := by
    simp only [h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance


end OpenSubSec


section Red
/-! ## §5 Copied statements (verbatim from `scratch/h5-neron/H5Neron.lean`) and the reduction -/

section Reduction

variable {K : Type} [Field K] {A : AbVar K}

/-- `𝒰 → 𝒢` is an open immersion of group schemes over `𝓞_L`. -/
def IsOpenSubgroupModel {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L) : Prop :=
  ∃ f : 𝒰.G ⟶ 𝒢.G, IsOpenImmersion f.left ∧ IsMonHom f

/-- **Leaf N1 (Néron)**, as in `Reduction.lean` (BLR §1.4 Thm 3, UNVERIFIED locator). -/
def NeronModelExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ 𝒩 : GroupModel A L, 𝒩.IsNeronModel

/-- **Leaf N2 (semistable reduction and base change of the identity component).** For `A` over
a number field `K` there are a finite extension `L₀/K` and a Néron model `𝒩₀` over `𝓞_{L₀}` such
that for every finite extension `L'/L₀` and every Néron model `𝒩'` over `𝓞_{L'}`, there is a group
model `𝒰` (the identity component `𝒩'⁰`) that is an open subgroup both of `𝒩'` and of a base
change `𝒱` of `𝒩₀` (namely `𝒱 = 𝒩₀ ×_{𝓞_{L₀}} 𝓞_{L'}`, with `𝒰 = 𝒩₀⁰ ×_{𝓞_{L₀}} 𝓞_{L'}`).
Consequence of SGA 7 IX Thm 3.6 (Grothendieck's semistable reduction theorem: `A_{L₀}` is
semistable for some finite `L₀`) and SGA 7 IX Prop./Cor. 3.3 (in the semistable case
`(𝒩_{L'})⁰ = (𝒩⁰)_{L'}`), with the openness of the identity component (SGA 3 VI_B 3.10) and
the compatibility of Néron models with localization (BLR §1.2); all locators UNVERIFIED. -/
def SemistableNeronIdentityComponent : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        ∃ 𝒰 𝒱 : GroupModel A L', IsBaseChangeOf 𝒱 𝒩₀ ∧ IsOpenSubgroupModel 𝒰 𝒩' ∧
          IsOpenSubgroupModel 𝒰 𝒱

/-! ## Glue (stated; to be proved by the project) -/

/-- **Glue H4a.** The height of a fixed smooth model is invariant under base change:
`ω_{𝒢_{L'}} = ω_𝒢 ⊗ 𝓞_{L'}` (flat base change of the conormal sheaf), the Arakelov degree is
multiplied by `[L':L]`, and each `τ' : L' → ℂ` restricts to `τ = τ'|_L` with the same
uniformization. -/
def ModelHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height = 𝒢.height

/-- **Glue M6.** An open subgroup model has the same height: an open immersion `𝒰 → 𝒢` of group
schemes induces isomorphisms of the local rings along the unit section (so the same `ω`) and a
group bijection on complex points (on generic fibres it is an open immersion from a proper
connected scheme, hence an isomorphism; it need not be compatible with the two `gen`). -/
def OpenSubgroupHeight : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L), IsOpenSubgroupModel 𝒰 𝒢 → 𝒰.height = 𝒢.height

/-- **The compositum.** Two number fields `L, L₀` over a number field `K` embed `K`-linearly in a
common number field `L'`. Proved (inside `AlgebraicClosure K`). -/
theorem compositum (K : Type) [Field K] [NumberField K] (L L₀ : Type) [Field L] [NumberField L]
    [Algebra K L] [Field L₀] [NumberField L₀] [Algebra K L₀] :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra K L') (_ : Algebra L L')
      (_ : Algebra L₀ L'), IsScalarTower K L L' ∧ IsScalarTower K L₀ L' := by
  let Ω := AlgebraicClosure K
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Module.Finite K L₀ := Module.Finite.of_restrictScalars_finite ℚ K L₀
  let eL : L →ₐ[K] Ω := IsAlgClosed.lift
  let eL₀ : L₀ →ₐ[K] Ω := IsAlgClosed.lift
  let E : IntermediateField K Ω := eL.fieldRange ⊔ eL₀.fieldRange
  haveI : FiniteDimensional K eL.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField eL).toLinearEquiv
  haveI : FiniteDimensional K eL₀.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField eL₀).toLinearEquiv
  haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_sup _ _
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : FiniteDimensional ℚ E := Module.Finite.trans K E
  haveI : NumberField E := ⟨⟩
  let f : L →ₐ[K] E := (IntermediateField.inclusion le_sup_left).comp
    (AlgEquiv.ofInjectiveField eL).toAlgHom
  let f₀ : L₀ →ₐ[K] E := (IntermediateField.inclusion le_sup_right).comp
    (AlgEquiv.ofInjectiveField eL₀).toAlgHom
  letI : Algebra L E := f.toRingHom.toAlgebra
  letI : Algebra L₀ E := f₀.toRingHom.toAlgebra
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  · exact IsScalarTower.of_algebraMap_eq fun x => (f₀.commutes x).symm


/-- **An open immersion of group models does not increase the height** (stated here; proved
below as `openImmersionHeightLe`). If
`f : 𝒰 → 𝒢` is a homomorphism of group models of `A_L` whose underlying morphism is an open
immersion (so, by `genericIso_of_openImmersion`, an isomorphism on generic fibres), then
`h(𝒰) ≤ h(𝒢)`: the unit section of `𝒢` factors through `𝒰` (`e_𝒢 = e_𝒰 ≫ f`), `f` induces
isomorphisms of local rings along it, so `ω_𝒰 = ω_𝒢`; complex points correspond bijectively
(`pts_comp_bijective`). -/
def OpenImmersionHeightLe : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G), IsOpenImmersion f.left → IsMonHom f →
    IsIso ((Over.pullback (jL L)).map f) → 𝒰.height ≤ 𝒢.height

/-- **Glue M6 from `HeightAntitone` and `OpenImmersionHeightLe`** (the generic-isomorphism
clause is proved, `genericIso_of_openImmersion`). -/
theorem openSubgroupHeight_of (hA : HeightAntitone) (hO : OpenImmersionHeightLe) :
    OpenSubgroupHeight := by
  intro K _ A L _ _ _ 𝒰 𝒢 ⟨f, hf, hm⟩
  haveI := hf
  have hi := genericIso_of_openImmersion 𝒰 𝒢 f
  exact le_antisymm (hO K A L 𝒰 𝒢 f hf hm hi) (hA K A L 𝒰 𝒢 f hm hi)

/-- **H5 in the form R19-R21 need**, from the leaves N1, N2 and `OpenImmersionHeightLe`,
`ModelHeightBaseChange` (the former is proved below, giving `stableFaltingsHeight_eq_neron_all'`) (`NeronModelMinimal`,
`GroupModelBaseChangeExists` are theorems; `OpenSubgroupHeight` follows). Same conclusion as h5-neron's
`stableFaltingsHeight_eq_neron_all`. -/
theorem stableFaltingsHeight_eq_neron_all (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hO : OpenImmersionHeightLe)
    (hbc : ModelHeightBaseChange) (K : Type) [Field K] [NumberField K] (A : AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        stableFaltingsHeight A = 𝒩'.height := by
  have hmin := neronModelMinimal
  have hbcE := groupModelBaseChangeExists
  have hop := openSubgroupHeight_of heightAntitone hO
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hbase⟩ := hN2 K A
  have heq : stableFaltingsHeight A = 𝒩₀.height := by
    rw [stableFaltingsHeight_eq_iInf_height]
    refine le_antisymm (iInf_le_of_le (FinExt.mk L₀) (iInf_le_of_le 𝒩₀ le_rfl)) ?_
    refine le_iInf fun E => le_iInf fun 𝒢 => ?_
    obtain ⟨L', j1, j2, j3, j4, j5, t1, t2⟩ := compositum K E.L L₀
    obtain ⟨𝒢', h𝒢'⟩ := hbcE K A E.L L' 𝒢
    obtain ⟨𝒩', h𝒩'⟩ := hN1 K A L'
    obtain ⟨𝒰, 𝒱, h𝒱, h𝒰𝒩, h𝒰𝒱⟩ := hbase L' 𝒩' h𝒩'
    calc 𝒩₀.height = 𝒱.height := (hbc K A L₀ L' 𝒩₀ 𝒱 h𝒱).symm
      _ = 𝒰.height := (hop K A L' 𝒰 𝒱 h𝒰𝒱).symm
      _ = 𝒩'.height := hop K A L' 𝒰 𝒩' h𝒰𝒩
      _ ≤ 𝒢'.height := hmin K A L' 𝒩' 𝒢' h𝒩'
      _ = 𝒢.height := hbc K A E.L L' 𝒢 𝒢' h𝒢'
  refine ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, heq, ?_⟩
  intro L' j1 j2 j3 j4 j5 𝒩' h𝒩'
  obtain ⟨𝒰, 𝒱, h𝒱, h𝒰𝒩, h𝒰𝒱⟩ := hbase L' 𝒩' h𝒩'
  rw [heq, ← hbc K A L₀ L' 𝒩₀ 𝒱 h𝒱, ← hop K A L' 𝒰 𝒱 h𝒰𝒱, hop K A L' 𝒰 𝒩' h𝒰𝒩]

end Reduction

end Red

/-! ### Additivity -/

section General

variable {S S' : Scheme.{0}} (j : S' ⟶ S) (P : Over S → Prop)

/-- The Néron mapping property of `N` (over `S`) for `A` (over `S'`) along `j`, tested on the
objects satisfying `P`. -/
def NeronProp (N : Over S) (A : Over S') (e : (Over.pullback j).obj N ≅ A) : Prop :=
  ∀ Y : Over S, P Y → Function.Bijective fun f : Y ⟶ N => (Over.pullback j).map f ≫ e.hom

variable {j P}

/-- Existence and uniqueness of the extension. -/
theorem NeronProp.lift {N : Over S} {A : Over S'} {e : (Over.pullback j).obj N ≅ A}
    (h : NeronProp j P N A e) {Y : Over S} (hY : P Y) (g : (Over.pullback j).obj Y ⟶ A) :
    ∃! f : Y ⟶ N, (Over.pullback j).map f ≫ e.hom = g := by
  obtain ⟨f, hf⟩ := (h Y hY).2 g
  exact ⟨f, hf, fun f' hf' => (h Y hY).1 (hf'.trans hf.symm)⟩

/-- **Uniqueness of Néron models**: two Néron models of `A` (each a test object) are isomorphic,
compatibly with the identifications of their generic fibres. -/
theorem NeronProp.uniqueIso {N N' : Over S} {A : Over S'} {e : (Over.pullback j).obj N ≅ A}
    {e' : (Over.pullback j).obj N' ≅ A} (h : NeronProp j P N A e) (h' : NeronProp j P N' A e')
    (hN : P N) (hN' : P N') :
    ∃ φ : N ≅ N', (Over.pullback j).map φ.hom ≫ e'.hom = e.hom := by
  obtain ⟨f, hf⟩ := (h' N hN).2 e.hom
  obtain ⟨f', hf'⟩ := (h N' hN').2 e'.hom
  simp only at hf hf'
  have h1 : f ≫ f' = 𝟙 N := by
    apply (h N hN).1
    simp only [Functor.map_comp, Category.assoc, hf', hf]
    erw [(Over.pullback j).map_id, Category.id_comp]
  have h2 : f' ≫ f = 𝟙 N' := by
    apply (h' N' hN').1
    simp only [Functor.map_comp, Category.assoc, hf', hf]
    erw [(Over.pullback j).map_id, Category.id_comp]
  exact ⟨⟨f, f', h1, h2⟩, hf⟩

/-- The identification of the generic fibre of `N₁ ⊗ N₂` with `A₁ ⊗ A₂`. -/
noncomputable def tensorGen {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (Over.pullback j).obj (N₁ ⊗ N₂) ≅ A₁ ⊗ A₂ :=
  prodComparisonIso (Over.pullback j) N₁ N₂ ≪≫ tensorIso e₁ e₂

theorem tensorGen_fst {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (tensorGen e₁ e₂).hom ≫ fst A₁ A₂ = (Over.pullback j).map (fst N₁ N₂) ≫ e₁.hom := by
  rw [tensorGen, Iso.trans_hom, prodComparisonIso_hom, tensorIso_hom, Category.assoc, tensorHom_fst,
    CartesianMonoidalCategory.prodComparison_fst_assoc]

theorem tensorGen_snd {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (tensorGen e₁ e₂).hom ≫ snd A₁ A₂ = (Over.pullback j).map (snd N₁ N₂) ≫ e₂.hom := by
  rw [tensorGen, Iso.trans_hom, prodComparisonIso_hom, tensorIso_hom, Category.assoc, tensorHom_snd,
    CartesianMonoidalCategory.prodComparison_snd_assoc]

/-- **A product of Néron models is a Néron model of the product.** -/
theorem NeronProp.tensor {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    {e₁ : (Over.pullback j).obj N₁ ≅ A₁} {e₂ : (Over.pullback j).obj N₂ ≅ A₂}
    (h₁ : NeronProp j P N₁ A₁ e₁) (h₂ : NeronProp j P N₂ A₂ e₂) :
    NeronProp j P (N₁ ⊗ N₂) (A₁ ⊗ A₂) (tensorGen e₁ e₂) := by
  intro Y hY
  have hfst : ∀ f : Y ⟶ N₁ ⊗ N₂, ((Over.pullback j).map f ≫ (tensorGen e₁ e₂).hom) ≫
      fst A₁ A₂ = (Over.pullback j).map (f ≫ fst N₁ N₂) ≫ e₁.hom := by
    intro f
    rw [Category.assoc, tensorGen_fst, Functor.map_comp, Category.assoc]
  have hsnd : ∀ f : Y ⟶ N₁ ⊗ N₂, ((Over.pullback j).map f ≫ (tensorGen e₁ e₂).hom) ≫
      snd A₁ A₂ = (Over.pullback j).map (f ≫ snd N₁ N₂) ≫ e₂.hom := by
    intro f
    rw [Category.assoc, tensorGen_snd, Functor.map_comp, Category.assoc]
  constructor
  · intro f f' hff'
    have a := hfst f
    have b := hfst f'
    have c := hsnd f
    have d := hsnd f'
    simp only at hff'
    rw [hff'] at a c
    apply CartesianMonoidalCategory.hom_ext
    · exact (h₁ Y hY).1 (a.symm.trans b)
    · exact (h₂ Y hY).1 (c.symm.trans d)
  · intro g
    obtain ⟨f₁, hf₁⟩ := (h₁ Y hY).2 (g ≫ fst A₁ A₂)
    obtain ⟨f₂, hf₂⟩ := (h₂ Y hY).2 (g ≫ snd A₁ A₂)
    refine ⟨CartesianMonoidalCategory.lift f₁ f₂, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [hfst, CartesianMonoidalCategory.lift_fst]; exact hf₁
    · rw [hsnd, CartesianMonoidalCategory.lift_snd]; exact hf₂

end General


section GroupModels2
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
/-- The project's `IsNeronModel` is `NeronProp` for smooth test objects. -/
theorem GroupModel.isNeronModel_iff (𝒩 : GroupModel A L) :
    𝒩.IsNeronModel ↔ NeronProp (jL L) (fun Y => Smooth Y.hom) 𝒩.G (A.baseChange L).X 𝒩.gen :=
  ⟨fun h Y hY => @h Y hY, fun h Y hY => h Y hY⟩

end GroupModels2

section Transport

variable {S S' : Scheme.{0}} {j : S' ⟶ S} {P : Over S → Prop}

/-- The Néron property is invariant under isomorphisms of `N` and of `A`. -/
theorem NeronProp.of_iso {N N' : Over S} {A A' : Over S'} {e : (Over.pullback j).obj N ≅ A}
    (h : NeronProp j P N A e) (φ : N' ≅ N) (ψ : A ≅ A') (e' : (Over.pullback j).obj N' ≅ A')
    (he : (Over.pullback j).map φ.hom ≫ e.hom ≫ ψ.hom = e'.hom) : NeronProp j P N' A' e' := by
  intro Y hY
  have key : (fun f : Y ⟶ N' => (Over.pullback j).map f ≫ e'.hom) =
      (fun g => g ≫ ψ.hom) ∘ (fun f : Y ⟶ N => (Over.pullback j).map f ≫ e.hom) ∘
        (fun f => f ≫ φ.hom) := by
    funext f
    simp only [Function.comp, Functor.map_comp, Category.assoc, ← he]
  rw [key]
  refine Function.Bijective.comp ?_ ((h Y hY).comp ?_)
  · exact ⟨fun a b hab => (cancel_mono ψ.hom).mp hab, fun c => ⟨c ≫ ψ.inv, by simp⟩⟩
  · exact ⟨fun a b hab => (cancel_mono φ.hom).mp hab, fun c => ⟨c ≫ φ.inv, by simp⟩⟩

end Transport

section Additivity

open NumberField DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K]

/-- `C ≅ A × B` as abelian varieties: an isomorphism `C ≅ A ⊗ B` of `K`-schemes whose two
components are homomorphisms. (Mathlib v4.35 cannot form `A × B` as an `AbVar`: it lacks the
stability of geometric integrality under composition; so the product enters as `C`.) -/
def IsProductAbVar (C A B : AbVar K) : Prop :=
  ∃ e : C.X ≅ A.X ⊗ B.X, IsMonHom (e.hom ≫ fst A.X B.X) ∧ IsMonHom (e.hom ≫ snd A.X B.X)

/-- `C_L ≅ A_L ⊗ B_L`. -/
noncomputable def bcProd {A B C : AbVar K} (L : Type) [Field L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) : (C.baseChange L).X ≅ (A.baseChange L).X ⊗ (B.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso eC ≪≫
    prodComparisonIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))) A.X B.X

/-- `𝒢P ≅ 𝒢₁ × 𝒢₂` as group models of `C_L ≅ A_L × B_L`. -/
def IsProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) :
    Prop :=
  ∃ e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G, IsMonHom (e.hom ≫ fst _ _) ∧ IsMonHom (e.hom ≫ snd _ _) ∧
    (Over.pullback (jL L)).map e.hom ≫ (tensorGen 𝒢₁.gen 𝒢₂.gen).hom =
      𝒢P.gen.hom ≫ (bcProd L eC).hom

/-- **A product of Néron models is a Néron model** (for group models). -/
theorem isNeronModel_of_isProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
    [Algebra K L] {eC : C.X ≅ A.X ⊗ B.X} {𝒢P : GroupModel C L} {𝒩₁ : GroupModel A L}
    {𝒩₂ : GroupModel B L} (h₁ : 𝒩₁.IsNeronModel) (h₂ : 𝒩₂.IsNeronModel)
    (hP : IsProductModel eC 𝒢P 𝒩₁ 𝒩₂) : 𝒢P.IsNeronModel := by
  obtain ⟨e, -, -, he⟩ := hP
  rw [GroupModel.isNeronModel_iff] at h₁ h₂ ⊢
  refine (h₁.tensor h₂).of_iso e (bcProd L eC).symm 𝒢P.gen ?_
  rw [← Category.assoc, he]
  erw [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

/-- **Glue P1.** Group models of `A_L` and `B_L` give a group model of `C_L ≅ A_L × B_L`
(the fibre product over `𝓞_L`; smooth, separated, quasi-compact; `GrpObj` of a product). -/
def ProductGroupModelExists : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X),
    IsMonHom (eC.hom ≫ fst A.X B.X) → IsMonHom (eC.hom ≫ snd A.X B.X) →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (𝒢₁ : GroupModel A L)
      (𝒢₂ : GroupModel B L), ∃ 𝒢P : GroupModel C L, IsProductModel eC 𝒢P 𝒢₁ 𝒢₂

/-- **Glue P2** (the direction used). The height of a product model is at least the sum of the
heights: `ω_{𝒢₁×𝒢₂} = ω_{𝒢₁} ⊕ ω_{𝒢₂}`, `det(ω₁ ⊕ ω₂) = det ω₁ ⊗ det ω₂`, the Arakelov degree is
additive, and a product of uniformizations is a uniformization of the product (equality holds). -/
def ProductModelHeight : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ → 𝒢₁.height + 𝒢₂.height ≤ 𝒢P.height

/-- **`h(A) + h(B) ≤ h(A × B)`** (rv-blueprints F1, the direction step E4 uses) from Néron
existence, Néron minimality and the two product glue statements. No semistable reduction is
needed: the comparison is made over each `L` separately. -/
theorem stableFaltingsHeight_add_le (hN1 : NeronModelExists) (hmin : NeronModelMinimal)
    (hP : ProductGroupModelExists) (hH : ProductModelHeight) (A B C : AbVar K)
    (hC : IsProductAbVar C A B) :
    stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C := by
  obtain ⟨eC, h1, h2⟩ := hC
  rw [stableFaltingsHeight_eq_iInf_height C]
  refine le_iInf fun E => le_iInf fun 𝒢 => ?_
  obtain ⟨𝒩₁, hN₁⟩ := hN1 K A E.L
  obtain ⟨𝒩₂, hN₂⟩ := hN1 K B E.L
  obtain ⟨𝒢P, h𝒢P⟩ := hP K A B C eC h1 h2 E.L 𝒩₁ 𝒩₂
  have hA : stableFaltingsHeight A ≤ 𝒩₁.height := by
    rw [stableFaltingsHeight_eq_iInf_height]; exact iInf_le_of_le E (iInf_le_of_le 𝒩₁ le_rfl)
  have hB : stableFaltingsHeight B ≤ 𝒩₂.height := by
    rw [stableFaltingsHeight_eq_iInf_height]; exact iInf_le_of_le E (iInf_le_of_le 𝒩₂ le_rfl)
  calc stableFaltingsHeight A + stableFaltingsHeight B ≤ 𝒩₁.height + 𝒩₂.height :=
        add_le_add hA hB
    _ ≤ 𝒢P.height := hH K A B C eC E.L 𝒢P 𝒩₁ 𝒩₂ h𝒢P
    _ ≤ 𝒢.height :=
        hmin K C E.L 𝒢P 𝒢 (isNeronModel_of_isProductModel hN₁ hN₂ h𝒢P)

end Additivity

section ProductProof

/-- `prodComparison` of a braided monoidal functor between cartesian categories is a monoid
morphism. -/
theorem isMonHom_prodComparisonIso {S S' : Scheme.{0}} (j : S' ⟶ S) (X Y : Over S) [GrpObj X]
    [GrpObj Y] :
    IsMonHom (prodComparisonIso (Over.pullback j) X Y).hom := by
  have h : (prodComparisonIso (Over.pullback j) X Y).hom =
      (Functor.Monoidal.μIso (Over.pullback j) X Y).inv := by
    rw [prodComparisonIso_hom, ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    rfl
  have h0 : IsMonHom (Functor.Monoidal.μIso (Over.pullback j) X Y).hom :=
    (inferInstance : IsMonHom (Functor.LaxMonoidal.μ (Over.pullback j) X Y))
  rw [h]
  infer_instance

/-- **Glue P1, proved.** -/
theorem productGroupModelExists : ProductGroupModelExists := by
  unfold ProductGroupModelExists
  intro K _ A B C eC h1 h2 L _ _ _ 𝒢₁ 𝒢₂
  haveI : Smooth (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show Smooth (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : IsSeparated (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show IsSeparated (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : QuasiCompact (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show QuasiCompact (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : IsMonHom eC.hom := by
    have : eC.hom = lift (eC.hom ≫ fst A.X B.X) (eC.hom ≫ snd A.X B.X) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [this]; infer_instance
  let F := Over.pullback (jL L)
  let F' := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let gen : genericFibre L (𝒢₁.G ⊗ 𝒢₂.G) ≅ (C.baseChange L).X :=
    tensorGen 𝒢₁.gen 𝒢₂.gen ≪≫ (bcProd L eC).symm
  have gen_hom : letI : GrpObj (genericFibre L (𝒢₁.G ⊗ 𝒢₂.G)) := Functor.grpObjObj
      IsMonHom gen.hom := by
    let g₁ : F.obj 𝒢₁.G ⟶ F'.obj A.X := 𝒢₁.gen.hom
    let g₂ : F.obj 𝒢₂.G ⟶ F'.obj B.X := 𝒢₂.gen.hom
    have g1 : IsMonHom g₁ := 𝒢₁.gen_hom
    have g2 : IsMonHom g₂ := 𝒢₂.gen_hom
    have p1 := isMonHom_prodComparisonIso (jL L) 𝒢₁.G 𝒢₂.G
    have p2 := isMonHom_prodComparisonIso (Spec.map (CommRingCat.ofHom (algebraMap K L))) A.X B.X
    have : IsMonHom ((prodComparisonIso F 𝒢₁.G 𝒢₂.G).hom ≫
        (g₁ ⊗ₘ g₂) ≫
        (prodComparisonIso F' A.X B.X).inv ≫ F'.map eC.inv) := inferInstance
    exact this
  refine ⟨⟨𝒢₁.G ⊗ 𝒢₂.G, gen, gen_hom⟩, Iso.refl _, ?_, ?_, ?_⟩
  · show IsMonHom (𝟙 _ ≫ fst _ _); infer_instance
  · show IsMonHom (𝟙 _ ≫ snd _ _); infer_instance
  · show F.map (𝟙 _) ≫ _ = (tensorGen 𝒢₁.gen 𝒢₂.gen ≪≫ (bcProd L eC).symm).hom ≫ _
    rw [F.map_id, Category.id_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]



/-- **`h(A) + h(B) ≤ h(A × B)` from N1 and `ProductModelHeight`** (P1 and `NeronModelMinimal` are
theorems). -/
theorem stableFaltingsHeight_add_le_of_productModelHeight (hN1 : NeronModelExists)
    (hH : ProductModelHeight) {K : Type} [Field K] (A B C : AbVar K)
    (hC : IsProductAbVar C A B) :
    stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C :=
  stableFaltingsHeight_add_le hN1 neronModelMinimal productGroupModelExists hH A B C hC

end ProductProof


/-! ## Part 4: `OpenImmersionHeightLe` (the inverse transport) -/

section OpenHeight

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The kernel computation of `cotMap_omegaAt`, as an equation. -/
theorem stalk_ker_eq (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (s : Spec (CommRingCat.of (𝓞 L))) (hp : f.left (𝒢.unitSection s) = 𝒩.unitSection s)
    (g : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s)) :
    (𝒢.unitSection.stalkMap s) (f.left.stalkMap (𝒢.unitSection s)
      (𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes g)) =
      (𝒩.unitSection.stalkMap s) g := by
  have hE := unitSection_comp 𝒢 𝒩 f
  set T := 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes
  have h1 := Scheme.Hom.stalkMap_comp 𝒢.unitSection f.left s
  have h2 := Scheme.Hom.stalkMap_congr_hom _ _ hE s
  have h1' : (𝒢.unitSection.stalkMap s) (f.left.stalkMap (𝒢.unitSection s) (T g)) =
      ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h1
    exact this.symm
  have h2' : ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) =
      (𝒩.unitSection.stalkMap s) ((𝒩.G.left.presheaf.stalkCongr
        (Inseparable.of_eq (hE ▸ rfl))).hom (T g)) := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h2
    exact this
  rw [h1', h2']
  have h4 : ∀ y : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s), y = g →
      (𝒩.unitSection.stalkMap s) y = (𝒩.unitSection.stalkMap s) g := by
    rintro y rfl; rfl
  apply h4
  show 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).symm.specializes (T g) = g
  exact (stalkSpecializes_stalkSpecializes_apply _ _ g).trans (stalkSpecializes_self_apply _ g)

/-- The specialization computation of `cotMap_omegaAt`, as an equation. -/
theorem stalk_spec_eq (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (s : Spec (CommRingCat.of (𝓞 L))) (hp : f.left (𝒢.unitSection s) = 𝒩.unitSection s)
    (g : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s)) :
    𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (f.left.stalkMap (𝒢.unitSection s)
        (𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes g)) =
      genMap 𝒢 𝒩 f (𝒩.G.left.presheaf.stalkSpecializes (𝒩.specializes_genericUnit s) g) := by
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  unfold genMap
  rw [CommRingCat.comp_apply]
  congr 1
  rw [stalkSpecializes_stalkSpecializes_apply, stalkSpecializes_stalkSpecializes_apply]

theorem genMap_mem_maximalIdeal_iff (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] (x : 𝒩.genStalk) :
    genMap 𝒢 𝒩 f x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ↔
      x ∈ IsLocalRing.maximalIdeal 𝒩.genStalk := by
  haveI := isIso_genMap 𝒢 𝒩 f
  let e : 𝒩.genStalk ≃+* 𝒢.genStalk := (asIso (genMap 𝒢 𝒩 f)).commRingCatIsoToRingEquiv
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr (isUnit_map_iff e x)

/-- **For an open immersion, `(ω_𝒰)_s ⊆ f^* (ω_𝒢)_s`** at every `s`. -/
theorem omegaAt_le_cotMap (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G) [IsMonHom f]
    [IsOpenImmersion f.left] [IsIso ((Over.pullback (jL L)).map f)]
    (s : Spec (CommRingCat.of (𝓞 L))) (x : 𝒰.cotangent) (hx : x ∈ 𝒰.omegaAt s) :
    ∃ y ∈ 𝒢.omegaAt s, cotMap 𝒰 𝒢 f y = x := by
  have hE := unitSection_comp 𝒰 𝒢 f
  have hp : f.left (𝒰.unitSection s) = 𝒢.unitSection s :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun φ => φ s) hE)
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, hmem, rfl⟩ := hx
    have hiso1 : IsIso (f.left.stalkMap (𝒰.unitSection s)) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
    have hiso2 : IsIso (𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes) :=
      Iso.isIso_hom (𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq hp).symm)
    let Ψ := 𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes ≫
      f.left.stalkMap (𝒰.unitSection s)
    haveI : IsIso Ψ := inferInstance
    set g₀ := (inv Ψ) g
    have hg₀ : f.left.stalkMap (𝒰.unitSection s)
        (𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes g₀) = g := by
      show Ψ (inv Ψ g) = g
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
    have hker := stalk_ker_eq 𝒰 𝒢 f s hp g₀
    rw [hg₀] at hker
    have hspec := stalk_spec_eq 𝒰 𝒢 f s hp g₀
    rw [hg₀] at hspec
    have hmem₀ : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) g₀ ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk := by
      rw [← genMap_mem_maximalIdeal_iff 𝒰 𝒢 f, ← hspec]; exact hmem
    refine ⟨𝒢.dCls ⟨_, hmem₀⟩, Submodule.subset_span ⟨g₀, ?_, hmem₀, rfl⟩, ?_⟩
    · rw [RingHom.mem_ker, ← hker]; exact hg
    · rw [cotMap_dCls]
      congr 1
      exact Subtype.ext hspec.symm
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨r • a, Submodule.smul_mem _ r ha, map_smul _ _ _⟩

/-- **For an open immersion, `ω_𝒰 ⊆ f^* ω_𝒢`.** -/
theorem omega_le_cotMap (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G) [IsMonHom f]
    [IsOpenImmersion f.left] [IsIso ((Over.pullback (jL L)).map f)]
    (x : 𝒰.cotangent) (hx : x ∈ 𝒰.omega) : ∃ y ∈ 𝒢.omega, cotMap 𝒰 𝒢 f y = x := by
  obtain ⟨y, hy⟩ := (cotMap_bijective 𝒰 𝒢 f).2 x
  refine ⟨y, ?_, hy⟩
  rw [GroupModel.omega, Submodule.mem_iInf] at hx ⊢
  intro s
  obtain ⟨y', hy', hy'x⟩ := omegaAt_le_cotMap 𝒰 𝒢 f s x (hx s)
  rwa [(cotMap_bijective 𝒰 𝒢 f).1 (hy'x.trans hy.symm)] at hy'

theorem detLattice_le_hodgeMap (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G) [IsMonHom f]
    [IsOpenImmersion f.left] [IsIso ((Over.pullback (jL L)).map f)] (g : ℕ)
    (x : 𝒰.hodgeSpace g) (hx : x ∈ 𝒰.detLattice g) :
    ∃ y ∈ 𝒢.detLattice g, hodgeMap 𝒰 𝒢 f g y = x := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    choose w hw hwv using fun i => omega_le_cotMap 𝒰 𝒢 f (v i : 𝒰.cotangent) (v i).2
    refine ⟨(1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g w,
      Submodule.subset_span ⟨fun i => ⟨w i, hw i⟩, rfl⟩, ?_⟩
    rw [hodgeMap_wedge]
    simp only [hwv]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, rfl⟩ := ha
    obtain ⟨d, hd, rfl⟩ := hb
    exact ⟨c + d, add_mem hc hd, map_add _ _ _⟩
  | smul r a _ ha =>
    obtain ⟨c, hc, rfl⟩ := ha
    refine ⟨r • c, Submodule.smul_mem _ r hc, ?_⟩
    rw [← algebraMap_smul L r c, LinearMap.map_smul, algebraMap_smul]

/-- **Inverse transport of analytic uniformizations through an open immersion.** -/
theorem isAnalyticUniformization_of_comp (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G) [IsMonHom f]
    [IsOpenImmersion f.left] [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (Ψ : (Fin g → ℂ) → 𝒰.Pts τ)
    (h : 𝒢.IsAnalyticUniformization τ Λ (fun z => Ψ z ≫ f)) :
    𝒰.IsAnalyticUniformization τ Λ Ψ := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  have hb := pts_comp_bijective 𝒰 𝒢 f τ
  have hdom : ∀ V, 𝒰.dom Ψ V = 𝒢.dom (fun z => Ψ z ≫ f) (f.left ''ᵁ V) := by
    intro V
    ext z
    show ⊤ ≤ (Ψ z).left ⁻¹ᵁ V ↔ ⊤ ≤ (Ψ z ≫ f).left ⁻¹ᵁ (f.left ''ᵁ V)
    have : (Ψ z ≫ f).left ⁻¹ᵁ (f.left ''ᵁ V) = (Ψ z).left ⁻¹ᵁ V := by
      show (Ψ z).left ⁻¹ᵁ (f.left ⁻¹ᵁ (f.left ''ᵁ V)) = _
      rw [Scheme.Hom.preimage_image_eq]
    rw [this]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    apply hb.1
    show Ψ (z + w) ≫ f = (Ψ z * Ψ w) ≫ f
    rw [MonObj.mul_comp]
    exact hmul z w
  · intro z
    rw [← hker z]
    constructor
    · intro h1
      show Ψ z ≫ f = 1
      rw [h1, MonObj.one_comp]
    · intro h1
      apply hb.1
      show Ψ z ≫ f = 1 ≫ f
      rw [MonObj.one_comp]
      exact h1
  · intro p
    obtain ⟨z, hz⟩ := hsurj (p ≫ f)
    exact ⟨z, hb.1 hz⟩
  · intro V
    rw [hdom]
    exact hopen _
  · intro V s
    rw [hdom]
    refine (hdiff (f.left ''ᵁ V) ((f.left.appIso V).inv s)).congr fun z hz => ?_
    have hz' : z ∈ 𝒰.dom Ψ V := (hdom V).symm ▸ hz
    rw [evalAt_comp, evalAt_res 𝒰 (Ψ z) (homOfLE (Scheme.Hom.preimage_image_eq f.left V).ge) hz']
    congr 1
    have hh : f.left.app (f.left ''ᵁ V) ≫
        𝒰.G.left.presheaf.map (homOfLE (Scheme.Hom.preimage_image_eq f.left V).ge).op =
        (f.left.appIso V).hom := by
      rw [Scheme.Hom.appIso_hom]
      rfl
    rw [← CommRingCat.comp_apply, hh, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]

end OpenHeight

/-- **Glue `OpenImmersionHeightLe`, proved.** -/
theorem openImmersionHeightLe : OpenImmersionHeightLe := by
  intro K _ A L _ _ _ 𝒰 𝒢 f hf hm hi
  haveI := hf
  haveI := hm
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
  subst hM
  have hbij := hodgeMapBijective K A L 𝒰 M.model f hi g
  let e := LinearEquiv.ofBijective (hodgeMap 𝒰 M.model f g) hbij
  have hfin : Module.finrank L (𝒰.hodgeSpace g) = 1 :=
    e.finrank_eq.symm.trans M.hodge.finrank_eq_one
  obtain ⟨v, hv, hv0⟩ := hodgeLatticeNonzero_of_omegaSpans omegaSpans K A L 𝒰 g hfin
  let H : 𝒰.hodgeSpace g →ₗ[L] M.model.hodgeSpace g := e.symm
  have hinj : Function.Injective H := e.symm.injective
  have hle : ∀ x ∈ 𝒰.detLattice g, H x ∈ M.hodge.lattice := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := detLattice_le_hodgeMap 𝒰 M.model f g x hx
    have : H (hodgeMap 𝒰 M.model f g y) = y := e.symm_apply_apply y
    rw [this, M.lattice_eq]
    exact hy
  have hv0' : H v ≠ 0 := fun h0 => hv0 (hinj (h0.trans (map_zero H).symm))
  have hne := secIndex_ne_zero_of_mem M.hodge (hle v hv) hv0'
  have hlat : ∃ s ∈ 𝒰.detLattice g, s ≠ 0 ∧ secIndex (𝒰.detLattice g) s ≠ 0 :=
    ⟨v, hv, hv0, (secIndex_le_of_map H hinj _ _ hle hv hne).1⟩
  haveI := isIso_genMap 𝒰 M.model f
  let M' : MetrizedModel A L g :=
    { model := 𝒰
      hodge := pullHodge M.hodge H hinj (𝒰.detLattice g) hfin hlat
      lattice_eq := rfl
      arch := fun τ => by
        obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
        let Ψ : (Fin g → ℂ) → 𝒰.Pts τ := fun z =>
          (Equiv.ofBijective _ (pts_comp_bijective 𝒰 M.model f τ)).symm (Φ z)
        have hΦΨ : (fun z => Ψ z ≫ f) = Φ := funext fun z =>
          (Equiv.ofBijective _ (pts_comp_bijective 𝒰 M.model f τ)).apply_symm_apply (Φ z)
        have hU : 𝒰.IsAnalyticUniformization τ (M.hodge.periods τ) Ψ :=
          isAnalyticUniformization_of_comp 𝒰 M.model f τ _ Ψ (hΦΨ ▸ hΦ)
        refine ⟨Ψ, hU, fun t => ?_⟩
        let t₀ : Fin g → IsLocalRing.maximalIdeal M.model.genStalk := fun i =>
          ⟨(inv (genMap 𝒰 M.model f)) (t i), by
            rw [← genMap_mem_maximalIdeal_iff 𝒰 M.model f, ← CommRingCat.comp_apply,
              IsIso.inv_hom_id, CommRingCat.id_apply]
            exact (t i).2⟩
        have ht : ∀ i, (t i : 𝒰.genStalk) = genMap 𝒰 M.model f (t₀ i) := fun i => by
          show _ = genMap 𝒰 M.model f ((inv (genMap 𝒰 M.model f)) (t i))
          rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
        have hw : 𝒰.wedge t = hodgeMap 𝒰 M.model f g (M.model.wedge t₀) := by
          rw [hodgeMap_wedgeGerm]
          congr 1
          funext i
          exact Subtype.ext (ht i)
        show M.hodge.coeff τ (H (𝒰.wedge t)) = _
        have hH : H (𝒰.wedge t) = M.model.wedge t₀ := by
          rw [hw]; exact e.symm_apply_apply _
        rw [hH, hc, ← jacDet_comp_genMap 𝒰 M.model f _ Ψ hU t₀ t ht, hΦΨ] }
  calc (⨅ (g' : ℕ) (M'' : MetrizedModel A L g') (_ : M''.model = 𝒰),
        (M''.hodge.modelHeight : EReal)) ≤ (M'.hodge.modelHeight : EReal) :=
        iInf_le_of_le g (iInf_le_of_le M' (iInf_le_of_le rfl le_rfl))
    _ ≤ (M.hodge.modelHeight : EReal) :=
        EReal.coe_le_coe_iff.mpr (modelHeight_pullHodge_le M.hodge H hinj _ hfin hlat hle)

/-- **`OpenSubgroupHeight` (glue M6), proved.** -/
theorem openSubgroupHeight : OpenSubgroupHeight :=
  openSubgroupHeight_of heightAntitone openImmersionHeightLe

/-- **H5 in the form R19-R21 need, from the leaves N1, N2 and the one remaining glue statement
`ModelHeightBaseChange`.** -/
theorem stableFaltingsHeight_eq_neron_all' (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hbc : ModelHeightBaseChange) (K : Type) [Field K]
    [NumberField K] (A : AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        stableFaltingsHeight A = 𝒩'.height :=
  stableFaltingsHeight_eq_neron_all hN1 hN2 openImmersionHeightLe hbc K A

end ZInQ.H5Glue

/-! # height-bc (`scratch/height-bc/Final.lean`, copied) -/

/-! # height-bc: glue H4a (`ModelHeightBaseChange`) and `HodgeLineBaseChange`

Self-contained (Mathlib + project only; no `sorry`, no `axiom`).
* Verbatim copies: `IsBaseChangeOf`, `ModelHeightBaseChange` (from `scratch/h5-glue/H5Final.lean`,
  over the kernel's objects); `ModelHeightBaseChangeLE`, the Arakelov half of H4a,
  `MetrizationBaseChange`, `HodgeLineBaseChange` and `metrizationBaseChange_of_hodgeLine` (from
  `scratch/g0-stablebc/Main.part`, there over a verbatim copy of the same objects).
* Part A (new): the descent half `ModelHeightBaseChangeGE` and the reduction of H4a (`=`) to one
  geometric statement `HodgeLineBaseChangeDescent` (`modelHeightBaseChange_of_descent`).
* Part B (new): the natural map of a base change `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`: `bcProj` (π), `bcMap`
  (stalk map at the origin), `bcCot`, `bcExt`, `bcHodge` (ψ = L' ⊗ ⋀^g π^*), `bcPts` (β on complex
  points); compatibility of germs and Jacobians (`jacDet_bcPts`); half of the lattice clause
  (`span_bcHodge_le`).
* Part C (new): glue statements over the natural map. Proved here: `ptsBaseChangeMul`,
  `ptsBaseChangeBij`, `detLatticeBC_of_omega`, `hodgeSpanBC_of`, `jacobianPullbackSpan_of`,
  `uniformizationLift_of`.
  **Main results** (finest form): `modelHeightBaseChange_of_glue5` and
  `hodgeLineBaseChange_of_glue5` (H4a and `HodgeLineBaseChange`, verbatim, from the five glue
  statements `HodgeBCInjective`, `CotangentSpanBC`, `OmegaBaseChange`,
  `UniformizationLiftAnalytic`, `JacobianSemilinear`), and `modelHeightBaseChangeGE_of_main`
  (the descent half from `HodgeBCInjective` and `OmegaBaseChange`). Coarser forms:
  `_of_five`, `_of_main`, `_of_four`, `_of_glue`. -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

/-! ## Verbatim copies -/

/-- (copied from h5-neron) -/
def IsBaseChangeOf {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L]
    [Algebra K L] [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) : Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

-- copied verbatim from scratch/h5-glue/H5Final.lean

/-- **Glue H4a.** The height of a fixed smooth model is invariant under base change:
`ω_{𝒢_{L'}} = ω_𝒢 ⊗ 𝓞_{L'}` (flat base change of the conormal sheaf), the Arakelov degree is
multiplied by `[L':L]`, and each `τ' : L' → ℂ` restricts to `τ = τ'|_L` with the same
uniformization. -/
def ModelHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height = 𝒢.height

-- copied verbatim from scratch/g0-stablebc/Main.part

/-- **Glue H4a, the inequality half (used here).** `h(𝒢_{L'}) ≤ h(𝒢)` for a group model `𝒢` and
a base change `𝒢'` of it. Implied by `ModelHeightBaseChange` (`modelHeightBaseChangeLE`
below). Same justification (h5-neron §2): `ω` of a smooth model commutes with base change, the
Arakelov degree is multiplied by `[L':L]`, and `𝒢'(ℂ)_{τ'} = 𝒢(ℂ)_{τ'|_L}`. -/
def ModelHeightBaseChangeLE : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height ≤ 𝒢.height


-- copied verbatim from scratch/g0-stablebc/Main.part (lines 240-500)
/-! ### The Arakelov half of H4a (proved) and the geometric half (glue, stated)

`modelHeight_eq_of_isHodgeBaseChange`: if `D'` over `L'` is obtained from `D` over `L` by base
change (a semilinear injection `ψ` on the Hodge lines, with `⋀^g ω' = 𝓞_{L'} · ψ(⋀^g ω)`,
restricted period lattices and compatible coefficient maps), the model heights agree. The finite
part reduces to fractional ideals (`N(𝔞𝓞_{L'}) = N(𝔞)^{[L':L]}`, def-faltings'
`absNorm_extendedHom`) and the archimedean part to `sum_embeddings_comp`. -/

section ArakelovBC

open scoped nonZeroDivisors

/-- `secIndex` is invariant under an injective linear map. -/
theorem secIndex_map {K : Type*} [Field K] [NumberField K] {V W : Type*} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (f : V →ₗ[𝓞 K] W) (hf : Function.Injective f)
    (Λ : Submodule (𝓞 K) V) (w : V) : secIndex (Λ.map f) (f w) = secIndex Λ w := by
  unfold secIndex
  rw [← Set.image_singleton, ← Submodule.map_span, Submodule.map_toAddSubgroup,
    Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf

/-- A finite index kills the quotient: `#(Λ/𝓞η) • x ∈ 𝓞η` for `x ∈ Λ`. -/
theorem secIndex_nsmul_mem {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) (w : V)
    {x : V} (hx : x ∈ Λ) : secIndex Λ w • x ∈ Submodule.span (𝓞 K) {w} :=
  AddSubgroup.nsmul_relIndex_mem (Submodule.span (𝓞 K) {w}).toAddSubgroup hx

variable {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

/-- **The finite part of base change**: `#(Λ'/𝓞_{L'}ιη) = #(Λ/𝓞_Lη)^{[L':L]}` for
`Λ' = 𝓞_{L'} · ψ(Λ)`. -/
theorem secIndex_baseChange {V V' : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V'] [Module (𝓞 L') V']
    [IsScalarTower (𝓞 L') L' V'] (hV : Module.finrank L V = 1) (ψ : V →+ V')
    (hsmul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) (Λ : Submodule (𝓞 L) V)
    {w : V} (hηΛ : w ∈ Λ) (hη : w ≠ 0) (hη' : ψ w ≠ 0) (hi : secIndex Λ w ≠ 0) :
    secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) = secIndex Λ w ^ Module.finrank L L' := by
  -- coordinates `c ↦ c • w` and `c ↦ c • ιη`
  let φ : L →ₗ[𝓞 L] V := (LinearMap.toSpanSingleton L V w).restrictScalars (𝓞 L)
  let φ' : L' →ₗ[𝓞 L'] V' := (LinearMap.toSpanSingleton L' V' (ψ w)).restrictScalars (𝓞 L')
  have hφ : ∀ c, φ c = c • w := fun c => rfl
  have hφ' : ∀ c, φ' c = c • ψ w := fun c => rfl
  have hφinj : Function.Injective φ := fun a b h => by
    rw [hφ, hφ] at h
    exact smul_left_injective L hη h
  have hφ'inj : Function.Injective φ' := fun a b h => by
    rw [hφ', hφ'] at h
    exact smul_left_injective L' hη' h
  have hφsurj : Function.Surjective φ := fun v => by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hη).mp hV v
    exact ⟨c, hc⟩
  set I : Submodule (𝓞 L) L := Λ.comap φ with hI
  have hΛ : Λ = I.map φ := (Submodule.map_comap_eq_of_surjective hφsurj Λ).symm
  have h1I : (1 : L) ∈ I := by simpa [hI, hφ] using hηΛ
  have hidx : secIndex I 1 = secIndex Λ w := by
    conv_rhs => rw [hΛ, show w = φ 1 by simp [hφ]]
    exact (secIndex_map φ hφinj I 1).symm
  -- `ψ(Λ) = φ'(L'-image of I)`
  have himg : ψ '' (Λ : Set V) = φ' '' (algebraMap L L' '' (I : Set L)) := by
    rw [hΛ, Submodule.map_coe, Set.image_image, Set.image_image]
    refine Set.image_congr fun c _ => ?_
    rw [hφ, hφ', hsmul]
  have hspan : Submodule.span (𝓞 L') (ψ '' (Λ : Set V)) =
      (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))).map φ' := by
    rw [himg, Submodule.map_span]
  have hidx' : secIndex (Submodule.span (𝓞 L') (ψ '' (Λ : Set V))) (ψ w) =
      secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 := by
    rw [hspan, show ψ w = φ' 1 by simp [hφ']]
    exact secIndex_map φ' hφ'inj _ 1
  -- `I` is a fractional ideal
  set N := secIndex I 1 with hN
  have hN0 : N ≠ 0 := hidx ▸ hi
  have hfrac : IsFractional (𝓞 L)⁰ I := by
    refine ⟨(N : 𝓞 L), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0), fun b hb => ?_⟩
    have hm := secIndex_nsmul_mem I 1 hb
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← ha, Algebra.smul_def, _root_.mul_one]
  let I₀ : FractionalIdeal (𝓞 L)⁰ L := ⟨I, hfrac⟩
  have hI₀ : (I₀ : Submodule (𝓞 L) L) = I := rfl
  have e1 := secIndex_mul_absNorm I₀ (x := 1) h1I one_ne_zero
  have e2 := secIndex_mul_absNorm (FractionalIdeal.extendedHom L' (𝓞 L') I₀) (x := 1)
    (by
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_extendedHom_eq_span]
      exact Submodule.subset_span ⟨1, h1I, map_one _⟩) one_ne_zero
  rw [FractionalIdeal.coe_extendedHom_eq_span, absNorm_extendedHom, map_one, abs_one] at e2
  rw [map_one, abs_one] at e1
  have e1' : (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I₀ = 1 := e1
  have e2' : (secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 : ℚ) *
      FractionalIdeal.absNorm I₀ ^ Module.finrank L L' = 1 := e2
  rw [← hidx, hidx']
  have key : (secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 : ℚ) =
      (secIndex I 1 : ℚ) ^ Module.finrank L L' := by
    rw [eq_inv_of_mul_eq_one_left e1', eq_inv_of_mul_eq_one_left e2', inv_pow]
  exact_mod_cast key

/-- **Base change data for Hodge data** `D/L ↦ D'/L'` along a semilinear injection `ψ`. -/
structure IsHodgeBaseChange {g : ℕ} {V V' : Type*} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [AddCommGroup V'] [Module L' V'] [Module (𝓞 L') V']
    (D : HodgeData L g V) (D' : HodgeData L' g V') (ψ : V →+ V') : Prop where
  smul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v
  ne_zero : ∀ v, v ≠ 0 → ψ v ≠ 0
  lattice : D'.lattice = Submodule.span (𝓞 L') (ψ '' D.lattice)
  periods : ∀ τ' : L' →+* ℂ, D'.periods τ' = D.periods (τ'.comp (algebraMap L L'))
  coeff : ∀ (τ' : L' →+* ℂ) v, D'.coeff τ' (ψ v) = D.coeff (τ'.comp (algebraMap L L')) v

/-- **The model height is invariant under base change of Hodge data.** Proved. -/
theorem modelHeight_eq_of_isHodgeBaseChange {g : ℕ} {V V' : Type*} [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V']
    [Module (𝓞 L') V'] [IsScalarTower (𝓞 L') L' V'] (D : HodgeData L g V) (D' : HodgeData L' g V')
    (ψ : V →+ V') (h : IsHodgeBaseChange D D' ψ) : D'.modelHeight = D.modelHeight := by
  obtain ⟨w, hηM, hη, hi⟩ := D.isLattice
  have hη' : ψ w ≠ 0 := h.ne_zero w hη
  have hηM' : ψ w ∈ D'.lattice := by
    rw [h.lattice]; exact Submodule.subset_span ⟨w, hηM, rfl⟩
  rw [D.modelHeight_eq hηM hη, D'.modelHeight_eq hηM' hη']
  have hsec : secIndex D'.lattice (ψ w) = secIndex D.lattice w ^ Module.finrank L L' := by
    rw [h.lattice]
    exact secIndex_baseChange D.finrank_eq_one ψ h.smul D.lattice hηM hη hη' hi
  have hsum : ∑ τ' : L' →+* ℂ, Real.log (torusMetricSq (D'.periods τ') (D'.coeff τ' (ψ w))) =
      Module.finrank L L' *
        ∑ σ : L →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)) := by
    simp only [h.periods, h.coeff]
    exact sum_embeddings_comp (fun σ => Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)))
  rw [hsec, hsum, ← Module.finrank_mul_finrank ℚ L L']
  have hK : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank L L' := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow]
  field_simp

end ArakelovBC

/-- **Glue H4a, geometric half (stated).** A metrization of a group model `𝒢/𝓞_L` induces one of
its base change `𝒢'/𝓞_{L'}`, by base change of the Hodge data: `ψ` is the natural map
`⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (from `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`), `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)`
(formation of `e*Ω¹` of a smooth group scheme commutes with base change; EGA IV 17.2.3,
UNVERIFIED locator), and at `τ' : L' → ℂ` the uniformization of `𝒢(ℂ)_{τ'|_L}` composed with the
bijection `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` (universal property of the pullback). Glue (a property of
def-faltings' definitions), STANDARD; not a literature leaf. -/
def MetrizationBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 →
    ∀ (g : ℕ) (Mm : MetrizedModel A L g), Mm.model = 𝒢 →
    ∃ (Mm' : MetrizedModel A L' g) (ψ : Mm.model.hodgeSpace g →+ Mm'.model.hodgeSpace g),
      Mm'.model = 𝒢' ∧ IsHodgeBaseChange Mm.hodge Mm'.hodge ψ

/-- **`ModelHeightBaseChangeLE` from the geometric half.** Proved. -/
theorem modelHeightBaseChangeLE_of_metrization (h : MetrizationBaseChange) :
    ModelHeightBaseChangeLE := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm => le_iInf fun hM => ?_
  obtain ⟨Mm', ψ, hM', hι⟩ := h K A L L' 𝒢 𝒢' h𝒢 g Mm hM
  refine iInf_le_of_le g (iInf_le_of_le Mm' (iInf_le_of_le hM' ?_))
  rw [modelHeight_eq_of_isHodgeBaseChange Mm.hodge Mm'.hodge ψ hι]

/-- **Glue H4a, geometric content, stated without metrized models.** For a base change `𝒢'` of
`𝒢` and each `g`, the natural map `ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (induced by
`𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`):
* is `L`-semilinear over `L → L'` and injective on nonzero vectors, and the Hodge space of `𝒢'` is
  an `L'`-line when that of `𝒢` is an `L`-line (it is `L' ⊗_L` of it);
* carries the lattice: `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)` (formation of `e*Ω¹` of a smooth group
  scheme commutes with base change; EGA IV 17.2.3, UNVERIFIED locator);
* is compatible with uniformizations: an analytic uniformization `Φ` of `𝒢(ℂ)_{τ'|_L}` gives one
  `Φ'` of `𝒢'(ℂ)_{τ'}` with the same kernel (compose with the bijection
  `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` of the pullback), and if a coefficient map `c` is computed by `Φ` on
  wedges of germs, its `τ'`-semilinear extension `c'` (`c' ∘ ψ = c`) is computed by `Φ'` on wedges
  of germs of `𝒢'` (both sides are `τ'`-semilinear alternating functions of the differentials
  `df'_i`, and they agree on pulled-back germs, which span).
Glue (a property of def-faltings' definitions), STANDARD; not a literature leaf. -/
def HodgeLineBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 → Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      ∀ (τ' : L' →+* ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
        (Φ : (Fin g → ℂ) → 𝒢.Pts (τ'.comp (algebraMap L L'))),
        𝒢.IsAnalyticUniformization _ Λ Φ →
        ∃ Φ' : (Fin g → ℂ) → 𝒢'.Pts τ', 𝒢'.IsAnalyticUniformization τ' Λ Φ' ∧
          ∀ (c : 𝒢.hodgeSpace g →ₛₗ[τ'.comp (algebraMap L L')] ℂ)
            (c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ),
            (∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f) → (∀ v, c' (ψ v) = c v) →
            ∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f'

/-- **`MetrizationBaseChange` from `HodgeLineBaseChange`.** The Hodge data of `𝒢'`: lattice
`⋀^g ω_{𝒢'}`, restricted period lattices, and the `τ'`-semilinear extension of the coefficient
maps along `ψ` (through the coordinate `c ↦ c · ψ(w)` on the `L'`-line). Proved. -/
theorem metrizationBaseChange_of_hodgeLine (h : HodgeLineBaseChange) :
    MetrizationBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g Mm hM
  subst hM
  obtain ⟨ψ, hsmul, hne, hfin, hlat, harch⟩ := h K A L L' Mm.model 𝒢' h𝒢 g
  obtain ⟨w, hwM, hw, hi⟩ := Mm.hodge.isLattice
  have hw' : ψ w ≠ 0 := hne w hw
  have hfin' : Module.finrank L' (𝒢'.hodgeSpace g) = 1 := hfin Mm.hodge.finrank_eq_one
  -- the coordinate `c ↦ c • ψ w` on the `L'`-line
  have hinj : Function.Injective (LinearMap.toSpanSingleton L' (𝒢'.hodgeSpace g) (ψ w)) :=
    fun a b hab => smul_left_injective L' hw' hab
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton L' (𝒢'.hodgeSpace g) (ψ w)) :=
    fun v => (finrank_eq_one_iff_of_nonzero' (ψ w) hw').mp hfin' v
  let e : L' ≃ₗ[L'] 𝒢'.hodgeSpace g := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have he : ∀ c, e c = c • ψ w := fun c => rfl
  -- the extended coefficient maps
  let lin : ∀ τ' : L' →+* ℂ, L' →ₛₗ[τ'] ℂ := fun τ' =>
    { toFun := fun c => τ' c * Mm.hodge.coeff (τ'.comp (algebraMap L L')) w
      map_add' := fun a b => by rw [map_add, add_mul]
      map_smul' := fun a b => by rw [smul_eq_mul, map_mul, smul_eq_mul, _root_.mul_assoc] }
  let coeff' : ∀ τ' : L' →+* ℂ, 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ := fun τ' =>
    (lin τ').comp e.symm.toLinearMap
  have hcoeff' : ∀ (τ' : L' →+* ℂ) v,
      coeff' τ' (ψ v) = Mm.hodge.coeff (τ'.comp (algebraMap L L')) v := by
    intro τ' v
    obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp Mm.hodge.finrank_eq_one v
    have h1 : e.symm (ψ (a • w)) = algebraMap L L' a := by
      rw [LinearEquiv.symm_apply_eq, he, hsmul]
    show lin τ' (e.symm (ψ (a • w))) = _
    rw [h1]
    show τ' (algebraMap L L' a) * _ = _
    rw [map_smulₛₗ, smul_eq_mul]
    rfl
  have hlat' : 𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' Mm.hodge.lattice) := by
    rw [hlat, Mm.lattice_eq]
  let D' : HodgeData L' g (𝒢'.hodgeSpace g) :=
    { lattice := 𝒢'.detLattice g
      finrank_eq_one := hfin'
      isLattice := by
        refine ⟨ψ w, ?_, hw', ?_⟩
        · rw [hlat']; exact Submodule.subset_span ⟨w, hwM, rfl⟩
        · rw [hlat', secIndex_baseChange Mm.hodge.finrank_eq_one ψ hsmul _ hwM hw hw' hi]
          exact pow_ne_zero _ hi
      periods := fun τ' => Mm.hodge.periods (τ'.comp (algebraMap L L'))
      periods_discrete := fun τ' => Mm.hodge.periods_discrete _
      periods_isZLattice := fun τ' => Mm.hodge.periods_isZLattice _
      coeff := coeff'
      coeff_ne_zero := fun τ' h0 => by
        have h2 := hcoeff' τ' w
        rw [h0, LinearMap.zero_apply] at h2
        exact Mm.hodge.coeff_apply_ne_zero _ hw h2.symm }
  let Mm' : MetrizedModel A L' g :=
    { model := 𝒢'
      hodge := D'
      lattice_eq := rfl
      arch := fun τ' => by
        obtain ⟨Φ, hΦ, hc⟩ := Mm.arch (τ'.comp (algebraMap L L'))
        obtain ⟨Φ', hΦ', hc'⟩ := harch τ' _ Φ hΦ
        exact ⟨Φ', hΦ', hc' _ (coeff' τ') hc (hcoeff' τ')⟩ }
  exact ⟨Mm', ψ, rfl,
    { smul := hsmul
      ne_zero := hne
      lattice := hlat'
      periods := fun _ => rfl
      coeff := hcoeff' }⟩


/-! ## Part A (new): the descent half of H4a -/

section DescentArakelov

open scoped nonZeroDivisors

variable {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

/-- Every complex embedding of `L` extends to `L'`. -/
theorem exists_comp_eq (σ : L →+* ℂ) : ∃ τ' : L' →+* ℂ, τ'.comp (algebraMap L L') = σ := by
  let _ : Algebra L ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic L L' := Algebra.IsAlgebraic.of_finite L L'
  refine ⟨(IsAlgClosed.lift (R := L) (S := L') (M := ℂ)).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift (R := L) (S := L') (M := ℂ)).commutes x

/-- An element of `L` whose image in `L'` is an algebraic integer is an algebraic integer. -/
theorem exists_ringOfIntegers_of_algebraMap {c : L} {a : 𝓞 L'}
    (h : algebraMap (𝓞 L') L' a = algebraMap L L' c) : ∃ y : 𝓞 L, algebraMap (𝓞 L) L y = c := by
  have h1 : IsIntegral ℤ (algebraMap L L' c) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 L')).mpr ⟨a, h⟩
  have h2 : IsIntegral ℤ c :=
    (isIntegral_algHom_iff (algebraMap L L').toIntAlgHom (algebraMap L L').injective).mp h1
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 L)).mp h2

/-- **Descent of finite index**: if `Λ' = 𝓞_{L'} · ψ(Λ)` has finite index over `𝓞_{L'} ψ(w)`,
then `Λ` has finite index over `𝓞_L w` (`Λ` is then a fractional ideal in coordinates). -/
theorem secIndex_ne_zero_of_baseChange {V V' : Type*} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V']
    [Module (𝓞 L') V'] [IsScalarTower (𝓞 L') L' V'] (hV : Module.finrank L V = 1)
    (ψ : V →+ V') (hsmul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v)
    (Λ : Submodule (𝓞 L) V) {w : V} (hηΛ : w ∈ Λ) (hη : w ≠ 0) (hη' : ψ w ≠ 0)
    (hi' : secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) ≠ 0) : secIndex Λ w ≠ 0 := by
  let φ : L →ₗ[𝓞 L] V := (LinearMap.toSpanSingleton L V w).restrictScalars (𝓞 L)
  have hφ : ∀ c, φ c = c • w := fun c => rfl
  have hφinj : Function.Injective φ := fun a b h => by
    rw [hφ, hφ] at h
    exact smul_left_injective L hη h
  have hφsurj : Function.Surjective φ := fun v => by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hη).mp hV v
    exact ⟨c, hc⟩
  set I : Submodule (𝓞 L) L := Λ.comap φ with hI
  have hΛ : Λ = I.map φ := (Submodule.map_comap_eq_of_surjective hφsurj Λ).symm
  have h1I : (1 : L) ∈ I := by simpa [hI, hφ] using hηΛ
  have hidx : secIndex I 1 = secIndex Λ w := by
    conv_rhs => rw [hΛ, show w = φ 1 by simp [hφ]]
    exact (secIndex_map φ hφinj I 1).symm
  set N := secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) with hN
  have hfrac : IsFractional (𝓞 L)⁰ I := by
    refine ⟨(N : 𝓞 L), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hi'), fun b hb => ?_⟩
    have hbΛ : b • w ∈ Λ := hb
    have hm := secIndex_nsmul_mem (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w)
      (Submodule.subset_span ⟨_, hbΛ, rfl⟩)
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨a, ha⟩ := hm
    rw [hsmul] at ha
    have h2 : (algebraMap (𝓞 L') L' a) • ψ w = algebraMap L L' ((N : L) * b) • ψ w := by
      rw [algebraMap_smul, ha, map_mul, mul_smul, map_natCast, Nat.cast_smul_eq_nsmul]
    obtain ⟨y, hy⟩ := exists_ringOfIntegers_of_algebraMap (smul_left_injective L' hη' h2)
    refine ⟨y, ?_⟩
    rw [hy, Algebra.smul_def, map_natCast]
  let I₀ : FractionalIdeal (𝓞 L)⁰ L := ⟨I, hfrac⟩
  have e1 := secIndex_mul_absNorm I₀ (x := 1) h1I one_ne_zero
  rw [map_one, abs_one] at e1
  have e1' : (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I₀ = 1 := e1
  rw [← hidx]
  intro h0
  rw [h0] at e1'
  simp at e1'

end DescentArakelov

/-- **Glue H4a, the descent half.** `h(𝒢) ≤ h(𝒢_{L'})` for a base change `𝒢'` of `𝒢`. Together
with `ModelHeightBaseChangeLE` it is `ModelHeightBaseChange`. -/
def ModelHeightBaseChangeGE : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢.height ≤ 𝒢'.height

/-- **Glue H4a, geometric content in both directions** (a property of def-faltings' definitions;
STANDARD, not a literature leaf). For a base change `𝒢'` of `𝒢` and each `g`, there is a map
`ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (the Prop asserts `∃ ψ`; the witness used in Part C is the
natural map `bcHodge`, induced by `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`) satisfying the clauses of
`HodgeLineBaseChange`, with the line clause as an equivalence (`hodgeSpace' = L' ⊗_L hodgeSpace`),
and in addition the *descent* clause: an analytic uniformization `Φ'` of `𝒢'(ℂ)_{τ'}` gives one
`Φ` of `𝒢(ℂ)_σ`, `σ = τ'|_L`, with the same kernel (compose with the bijection
`β : 𝒢'(ℂ)_{τ'} ≅ 𝒢(ℂ)_σ` of the pullback), and a coefficient map `c'` computed by `Φ'` on wedges of
germs of `𝒢'` computes `jacDet Φ` on wedges of germs of `𝒢` through `ψ`
(`ψ(wedge f) = wedge' (f pulled back)`, and the Jacobians agree along the bijection). -/
def HodgeLineBaseChangeDescent : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      (∀ (τ' : L' →+* ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
        (Φ : (Fin g → ℂ) → 𝒢.Pts (τ'.comp (algebraMap L L'))),
        𝒢.IsAnalyticUniformization _ Λ Φ →
        ∃ Φ' : (Fin g → ℂ) → 𝒢'.Pts τ', 𝒢'.IsAnalyticUniformization τ' Λ Φ' ∧
          ∀ (c : 𝒢.hodgeSpace g →ₛₗ[τ'.comp (algebraMap L L')] ℂ)
            (c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ),
            (∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f) → (∀ v, c' (ψ v) = c v) →
            ∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') ∧
      (∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ), τ'.comp (algebraMap L L') = σ →
        ∀ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
        𝒢'.IsAnalyticUniformization τ' Λ Φ' →
        ∃ Φ : (Fin g → ℂ) → 𝒢.Pts σ, 𝒢.IsAnalyticUniformization σ Λ Φ ∧
          ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ, (∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') →
            ∀ f, c' (ψ (𝒢.wedge f)) = 𝒢.jacDet Φ f)

/-- **The descent half of `HodgeLineBaseChangeDescent`** (all clauses except the forward
uniformization clause); it is what `ModelHeightBaseChangeGE` uses. -/
def HodgeLineDescentHalf : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      (∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ), τ'.comp (algebraMap L L') = σ →
        ∀ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
        𝒢'.IsAnalyticUniformization τ' Λ Φ' →
        ∃ Φ : (Fin g → ℂ) → 𝒢.Pts σ, 𝒢.IsAnalyticUniformization σ Λ Φ ∧
          ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ, (∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') →
            ∀ f, c' (ψ (𝒢.wedge f)) = 𝒢.jacDet Φ f)

theorem descentHalf_of_descent (h : HodgeLineBaseChangeDescent) : HodgeLineDescentHalf := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨ψ, h1, h2, h3, h4, -, h6⟩ := h K A L L' 𝒢 𝒢' h𝒢 g
  exact ⟨ψ, h1, h2, h3, h4, h6⟩

/-- `HodgeLineBaseChangeDescent` implies `HodgeLineBaseChange`. Proved. -/
theorem hodgeLineBaseChange_of_descent (h : HodgeLineBaseChangeDescent) : HodgeLineBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨ψ, h1, h2, h3, h4, h5, -⟩ := h K A L L' 𝒢 𝒢' h𝒢 g
  exact ⟨ψ, h1, h2, h3.mp, h4, h5⟩

/-- **`ModelHeightBaseChangeGE` from the geometric statement.** A metrization of `𝒢'` gives one
of `𝒢`: lattice `⋀^g ω_𝒢`, and at each `σ : L → ℂ` the data of `𝒢'` at a place `τ'` above `σ`
that maximizes `log ‖ψ w‖²_{τ'}` (the maximum over the fibre is at least the average). Proved. -/
theorem modelHeightBaseChangeGE_of_descentHalf (h : HodgeLineDescentHalf) :
    ModelHeightBaseChangeGE := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm' => le_iInf fun hM' => ?_
  subst hM'
  obtain ⟨ψ, hsmul, hne, hfin, hlat, hdesc⟩ := h K A L L' 𝒢 Mm'.model h𝒢 g
  have hfinL : Module.finrank L (𝒢.hodgeSpace g) = 1 := hfin.mpr Mm'.hodge.finrank_eq_one
  have hlat' : Mm'.hodge.lattice = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) := by
    rw [Mm'.lattice_eq, hlat]
  obtain ⟨s', hs'M, hs', -⟩ := Mm'.hodge.isLattice
  have hex : ∃ w ∈ 𝒢.detLattice g, ψ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hs'
    rw [hlat'] at hs'M
    have hsub : ψ '' (𝒢.detLattice g : Set (𝒢.hodgeSpace g)) ⊆ {0} := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcon x hx
    have h0 := Submodule.span_mono (R := 𝓞 L') hsub hs'M
    simpa using h0
  obtain ⟨w, hwM, hw'⟩ := hex
  have hw : w ≠ 0 := by
    rintro rfl
    exact hw' (map_zero ψ)
  have hψwM : ψ w ∈ Mm'.hodge.lattice := by
    rw [hlat']
    exact Submodule.subset_span ⟨w, hwM, rfl⟩
  have hi' : secIndex Mm'.hodge.lattice (ψ w) ≠ 0 :=
    Mm'.hodge.hodgeBundle.secIndex_ne_zero hψwM hw'
  have hi : secIndex (𝒢.detLattice g) w ≠ 0 :=
    secIndex_ne_zero_of_baseChange hfinL ψ hsmul _ hwM hw hw' (hlat' ▸ hi')
  -- the place above `σ` maximizing the archimedean term
  let F : (L' →+* ℂ) → ℝ := fun τ' =>
    Real.log (torusMetricSq (Mm'.hodge.periods τ') (Mm'.hodge.coeff τ' (ψ w)))
  have hext : ∀ σ : L →+* ℂ, ∃ τ' : L' →+* ℂ, τ'.comp (algebraMap L L') = σ ∧
      ∀ τ'' : L' →+* ℂ, τ''.comp (algebraMap L L') = σ → F τ'' ≤ F τ' := by
    intro σ
    classical
    obtain ⟨τ₀, hτ₀⟩ := exists_comp_eq (L' := L') σ
    have hne' : (Finset.univ.filter
        fun τ' : L' →+* ℂ => τ'.comp (algebraMap L L') = σ).Nonempty :=
      ⟨τ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ₀⟩⟩
    obtain ⟨τ', hτ'm, hmax⟩ := Finset.exists_max_image _ F hne'
    exact ⟨τ', (Finset.mem_filter.mp hτ'm).2,
      fun τ'' h'' => hmax τ'' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h''⟩)⟩
  choose ch hch hmax using hext
  let coeff : ∀ σ : L →+* ℂ, 𝒢.hodgeSpace g →ₛₗ[σ] ℂ := fun σ =>
    { toFun := fun v => Mm'.hodge.coeff (ch σ) (ψ v)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun a v => by
        rw [hsmul, map_smulₛₗ, smul_eq_mul, smul_eq_mul]
        have hσa : (ch σ) (algebraMap L L' a) = σ a := by
          have := congrArg (fun f : L →+* ℂ => f a) (hch σ)
          simpa using this
        rw [hσa] }
  let D : HodgeData L g (𝒢.hodgeSpace g) :=
    { lattice := 𝒢.detLattice g
      finrank_eq_one := hfinL
      isLattice := ⟨w, hwM, hw, hi⟩
      periods := fun σ => Mm'.hodge.periods (ch σ)
      periods_discrete := fun σ => Mm'.hodge.periods_discrete _
      periods_isZLattice := fun σ => Mm'.hodge.periods_isZLattice _
      coeff := coeff
      coeff_ne_zero := fun σ h0 => by
        have h2 : coeff σ w = 0 := by rw [h0]; rfl
        exact Mm'.hodge.coeff_apply_ne_zero (ch σ) hw' h2 }
  let Mm : MetrizedModel A L g :=
    { model := 𝒢
      hodge := D
      lattice_eq := rfl
      arch := fun σ => by
        obtain ⟨Φ', hΦ', hc'⟩ := Mm'.arch (ch σ)
        obtain ⟨Φ, hΦ, hc⟩ := hdesc σ (ch σ) (hch σ) _ Φ' hΦ'
        exact ⟨Φ, hΦ, fun f => hc _ hc' f⟩ }
  refine iInf_le_of_le g (iInf_le_of_le Mm (iInf_le_of_le rfl ?_))
  refine EReal.coe_le_coe_iff.mpr ?_
  show D.modelHeight ≤ Mm'.hodge.modelHeight
  rw [D.modelHeight_eq hwM hw, Mm'.hodge.modelHeight_eq hψwM hw']
  have hsec : secIndex Mm'.hodge.lattice (ψ w) =
      secIndex (𝒢.detLattice g) w ^ Module.finrank L L' := by
    rw [hlat']
    exact secIndex_baseChange hfinL ψ hsmul _ hwM hw hw' hi
  have hsum : ∑ τ' : L' →+* ℂ, F τ' ≤ Module.finrank L L' * ∑ σ : L →+* ℂ, F (ch σ) := by
    rw [← sum_embeddings_comp (fun σ => F (ch σ))]
    exact Finset.sum_le_sum fun τ' _ => hmax _ τ' rfl
  have hD : ∑ σ : L →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)) =
      ∑ σ : L →+* ℂ, F (ch σ) := rfl
  have hD' : ∑ τ' : L' →+* ℂ,
      Real.log (torusMetricSq (Mm'.hodge.periods τ') (Mm'.hodge.coeff τ' (ψ w))) =
      ∑ τ' : L' →+* ℂ, F τ' := rfl
  rw [hD, hD', hsec, ← Module.finrank_mul_finrank ℚ L L']
  have hK : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank L L' := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow, div_le_div_iff₀ hK (mul_pos hK hL)]
  have := mul_le_mul_of_nonneg_left hsum hK.le
  nlinarith

theorem modelHeightBaseChangeGE_of_descent (h : HodgeLineBaseChangeDescent) :
    ModelHeightBaseChangeGE :=
  modelHeightBaseChangeGE_of_descentHalf (descentHalf_of_descent h)

/-- **Glue H4a (`ModelHeightBaseChange`, verbatim statement) from `HodgeLineBaseChangeDescent`.**
Proved. -/
theorem modelHeightBaseChange_of_descent (h : HodgeLineBaseChangeDescent) :
    ModelHeightBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  exact le_antisymm
    (modelHeightBaseChangeLE_of_metrization
      (metrizationBaseChange_of_hodgeLine (hodgeLineBaseChange_of_descent h)) K A L L' 𝒢 𝒢' h𝒢)
    (modelHeightBaseChangeGE_of_descent h K A L L' 𝒢 𝒢' h𝒢)


/-! # Part B: the natural map of a base change (from `Natural.lean`) -/

/-- `Spec 𝓞_{L'} → Spec 𝓞_L`. -/
noncomputable abbrev bO (L L' : Type) [Field L] [Field L'] [Algebra L L'] :
    Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))

section Construction

variable {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']

theorem bO_genericPt : bO L L' (genericPt L') = genericPt L := by
  change PrimeSpectrum.comap (algebraMap (𝓞 L) (𝓞 L')) (genericPt L') = _
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap (𝓞 L) (𝓞 L')) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 L'))

theorem bO_appTop (r : 𝓞 L) :
    (bO L L').appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv (algebraMap (𝓞 L) (𝓞 L') r) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom
      ((bO L L').appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) =
        algebraMap (𝓞 L) (𝓞 L') r := by
    rw [← CommRingCat.comp_apply, h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  rw [← h3, Iso.hom_inv_id_apply]

variable (𝒢 : GroupModel A L) (𝒢' : GroupModel A L')
  (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)

/-- `e` is an isomorphism of group schemes (the content of `IsBaseChangeOf`). -/
def IsMonBC : Prop :=
  letI : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  IsMonHom e.hom

/-- The projection `π : 𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'} → 𝒢`. -/
noncomputable def bcProj : 𝒢'.G.left ⟶ 𝒢.G.left := e.hom.left ≫ pullback.fst _ _

theorem bcProj_w : bcProj 𝒢 𝒢' e ≫ 𝒢.G.hom = 𝒢'.G.hom ≫ bO L L' := by
  unfold bcProj
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact Over.w e.hom

variable {𝒢 𝒢' e} in
theorem bcProj_unit (he : IsMonBC 𝒢 𝒢' e) :
    𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e = bO L L' ≫ 𝒢.unitSection := by
  let _ : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  have : IsMonHom e.hom := he
  have h1 : (η[𝒢'.G] ≫ e.hom).left = (η[(Over.pullback (bO L L')).obj 𝒢.G]).left :=
    congrArg Over.Hom.left (IsMonHom.one_hom (f := e.hom))
  have hε : (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫ pullback.fst _ _ =
      bO L L' := by
    have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback (bO L L')))
    have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
      (g := bO L L')
    calc _ = (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫
          (pullback.fst _ _ ≫ (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) := by
            exact congrArg (fun k => _ ≫ k) (Category.comp_id _).symm
      _ = (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫ pullback.snd _ _ ≫ bO L L' := by
            rw [hc]
      _ = bO L L' := by
            rw [← Category.assoc]
            erw [hw]
            exact Category.id_comp _
  unfold GroupModel.unitSection bcProj
  rw [← Category.assoc, ← Over.comp_left]
  erw [h1]
  show (Functor.LaxMonoidal.ε _ ≫ (Over.pullback (bO L L')).map η[𝒢.G]).left ≫ pullback.fst _ _ = _
  have hmap : ((Over.pullback (bO L L')).map η[𝒢.G]).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ η[𝒢.G].left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Category.assoc]
  erw [hmap]
  rw [← Category.assoc]
  erw [hε]

variable {𝒢 𝒢' e} in
theorem bcProj_genericUnit (he : IsMonBC 𝒢 𝒢' e) :
    bcProj 𝒢 𝒢' e 𝒢'.genericUnit = 𝒢.genericUnit := by
  have h2 := congrArg (fun φ => φ (genericPt L')) (bcProj_unit he)
  unfold GroupModel.genericUnit
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  simp only
  rw [bO_genericPt]

variable {𝒢 𝒢' e}

/-- The comparison `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}` along `π` (`π(ξ') = ξ`). -/
noncomputable def bcMap (he : IsMonBC 𝒢 𝒢' e) : 𝒢.genStalk ⟶ 𝒢'.genStalk :=
  𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq (bcProj_genericUnit he)).specializes ≫
    (bcProj 𝒢 𝒢' e).stalkMap 𝒢'.genericUnit

/-- `bcMap` is `π^*` on germs. -/
theorem bcMap_germ (he : IsMonBC 𝒢 𝒢' e) (U : 𝒢.G.left.Opens) (hx : 𝒢.genericUnit ∈ U)
    (hx' : 𝒢'.genericUnit ∈ (bcProj 𝒢 𝒢' e) ⁻¹ᵁ U) (s : Γ(𝒢.G.left, U)) :
    (bcMap he) (𝒢.G.left.presheaf.germ U 𝒢.genericUnit hx s) =
      𝒢'.G.left.presheaf.germ ((bcProj 𝒢 𝒢' e) ⁻¹ᵁ U) 𝒢'.genericUnit hx'
        ((bcProj 𝒢 𝒢' e).app U s) := by
  unfold bcMap
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

theorem isIso_stalkSpecializes_bcMap (he : IsMonBC 𝒢 𝒢' e) :
    IsIso (𝒢.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (bcProj_genericUnit he)).specializes) :=
  Iso.isIso_hom (𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq (bcProj_genericUnit he)).symm)

theorem bcMap_mem_maximalIdeal (he : IsMonBC 𝒢 𝒢' e) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcMap he t ∈ IsLocalRing.maximalIdeal 𝒢'.genStalk := by
  haveI := isIso_stalkSpecializes_bcMap he
  set e' := 𝒢.G.left.presheaf.stalkSpecializes
    (Inseparable.of_eq (bcProj_genericUnit he)).specializes
  have h1 : e' t ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
    intro hu
    apply ht
    have := hu.map (inv e').hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  exact map_nonunit ((bcProj 𝒢 𝒢' e).stalkMap 𝒢'.genericUnit).hom _ h1

/-- `bcMap` is compatible with the structure maps `𝓞_L → 𝓞_{L'}`. -/
theorem bcMap_structMap (he : IsMonBC 𝒢 𝒢' e) (r : 𝓞 L) :
    bcMap he (𝒢.structMap r) = 𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) := by
  have e1 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  have e2 : 𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) =
      𝒢'.G.left.presheaf.germ ⊤ 𝒢'.genericUnit trivial
      (𝒢'.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv
        (algebraMap (𝓞 L) (𝓞 L') r))) := rfl
  rw [e1, e2, bcMap_germ he ⊤ (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
    (show 𝒢'.genericUnit ∈ (bcProj 𝒢 𝒢' e) ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) from trivial)]
  have hw := bcProj_w 𝒢 𝒢' e
  have : 𝒢.G.hom.appTop ≫ (bcProj 𝒢 𝒢' e).appTop = (bO L L').appTop ≫ 𝒢'.G.hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop]
  rw [← bO_appTop, ← CommRingCat.comp_apply (bO L L').appTop, ← this, CommRingCat.comp_apply]
  rfl

/-- The `𝓞_L`-module structure on `ω_{A_{L'}}` by restriction along `𝓞_L → 𝓞_{L'}`. -/
noncomputable abbrev cotRes (𝒢' : GroupModel A L') : Module (𝓞 L) 𝒢'.cotangent :=
  Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))

/-- **The induced map `ω_{A_L} → ω_{A_{L'}}` on cotangent spaces at the origin** (`π^*`),
semilinear over `𝓞_L → 𝓞_{L'}`. -/
noncomputable def bcCot (he : IsMonBC 𝒢 𝒢' e) :
    𝒢.cotangent →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] 𝒢'.cotangent where
  toFun x := Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
    (IsLocalRing.maximalIdeal 𝒢'.genStalk) (bcMap he).hom.toIntAlgHom
    (fun t ht => bcMap_mem_maximalIdeal he t ht) x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    let ψ := (bcMap he).hom.toIntAlgHom
    have h : IsLocalRing.maximalIdeal 𝒢.genStalk ≤
        (IsLocalRing.maximalIdeal 𝒢'.genStalk).comap ψ :=
      fun t ht => bcMap_mem_maximalIdeal he t ht
    change Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
        (IsLocalRing.maximalIdeal 𝒢'.genStalk) ψ h (𝒢.structMap r • Ideal.toCotangent _ m) =
      𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) • Ideal.mapCotangent
        (IsLocalRing.maximalIdeal 𝒢.genStalk) (IsLocalRing.maximalIdeal 𝒢'.genStalk) ψ h
        (Ideal.toCotangent _ m)
    rw [← (Ideal.toCotangent _).map_smul, Ideal.mapCotangent_toCotangent,
      Ideal.mapCotangent_toCotangent, ← (Ideal.toCotangent _).map_smul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, ψ, RingHom.toIntAlgHom_apply]
    rw [bcMap_structMap]

theorem bcCot_dCls (he : IsMonBC 𝒢 𝒢' e) (t : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcCot he (𝒢.dCls t) = 𝒢'.dCls ⟨bcMap he t, bcMap_mem_maximalIdeal he t t.2⟩ := rfl

/-! ### The map of Hodge lines `ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` -/

open scoped TensorProduct
open ExteriorAlgebra

/-- The `𝓞_L`-module structure on `⋀^g_{𝓞_{L'}} ω_{A_{L'}}` by restriction of scalars. -/
noncomputable abbrev extRes (𝒢' : GroupModel A L') (g : ℕ) :
    Module (𝓞 L) (exteriorPower (𝓞 L') g 𝒢'.cotangent) :=
  Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))

theorem bcCot_update (he : IsMonBC 𝒢 𝒢' e) {g : ℕ} [DecidableEq (Fin g)]
    (m : Fin g → 𝒢.cotangent) (i : Fin g) (z : 𝒢.cotangent) :
    (fun j => bcCot he (Function.update m i z j)) =
      Function.update (fun j => bcCot he (m j)) i (bcCot he z) := by
  funext j
  exact Function.apply_update (fun _ => bcCot he) m i z j

/-- `v ↦ π^*v₁ ∧ ⋯ ∧ π^*v_g`, alternating over `𝓞_L`. -/
noncomputable def bcAlt (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    letI := extRes (L := L) 𝒢' g
    𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] exteriorPower (𝓞 L') g 𝒢'.cotangent :=
  letI := extRes (L := L) 𝒢' g
  { toFun := fun v => exteriorPower.ιMulti (𝓞 L') g (fun i => bcCot he (v i))
    map_update_add' := by
      intro _ m i x y
      simp only [bcCot_update he, map_add]
      exact (exteriorPower.ιMulti (𝓞 L') g).map_update_add _ i _ _
    map_update_smul' := by
      intro _ m i r x
      simp only [bcCot_update he, map_smulₛₗ]
      exact (exteriorPower.ιMulti (𝓞 L') g).map_update_smul _ i _ _
    map_eq_zero_of_eq' := by
      intro v i j hv hij
      exact (exteriorPower.ιMulti (𝓞 L') g).map_eq_zero_of_eq _ (by simp only [hv]) hij }

/-- `⋀^g π^* : ⋀^g_{𝓞_L} ω_{A_L} → ⋀^g_{𝓞_{L'}} ω_{A_{L'}}`, additive and semilinear. -/
noncomputable def bcExt (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    exteriorPower (𝓞 L) g 𝒢.cotangent →+ exteriorPower (𝓞 L') g 𝒢'.cotangent :=
  letI := extRes (L := L) 𝒢' g
  (exteriorPower.alternatingMapLinearEquiv (bcAlt he g)).toAddMonoidHom

theorem bcExt_ιMulti (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (v : Fin g → 𝒢.cotangent) :
    bcExt he g (exteriorPower.ιMulti (𝓞 L) g v) =
      exteriorPower.ιMulti (𝓞 L') g (fun i => bcCot he (v i)) := by
  letI := extRes (L := L) 𝒢' g
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (bcAlt he g) v

theorem bcExt_smul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (r : 𝓞 L)
    (x : exteriorPower (𝓞 L) g 𝒢.cotangent) :
    bcExt he g (r • x) = algebraMap (𝓞 L) (𝓞 L') r • bcExt he g x := by
  letI := extRes (L := L) 𝒢' g
  exact (exteriorPower.alternatingMapLinearEquiv (bcAlt he g)).map_smul r x

/-- **The natural map of Hodge spaces** `ψ = L' ⊗ ⋀^g π^* : hodgeSpace g → hodgeSpace' g`. -/
noncomputable def bcHodge (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a : L => AddMonoidHom.mk'
      (fun x => algebraMap L L' a ⊗ₜ[𝓞 L'] bcExt he g x)
      (fun x y => by rw [map_add, TensorProduct.tmul_add]))
      (fun a b => by
        ext x
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
          TensorProduct.add_tmul]))
    (fun r a x => by
      simp only [AddMonoidHom.mk'_apply]
      rw [bcExt_smul, ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl)

theorem bcHodge_tmul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (a : L)
    (x : exteriorPower (𝓞 L) g 𝒢.cotangent) :
    bcHodge he g (a ⊗ₜ[𝓞 L] x) = algebraMap L L' a ⊗ₜ[𝓞 L'] bcExt he g x := rfl

theorem bcHodge_smul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (c : L) (v : 𝒢.hodgeSpace g) :
    bcHodge he g (c • v) = algebraMap L L' c • bcHodge he g v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [TensorProduct.smul_tmul', bcHodge_tmul, bcHodge_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `ψ(1 ⊗ df₁ ∧ ⋯ ∧ df_g) = 1 ⊗ d(π^*f₁) ∧ ⋯ ∧ d(π^*f_g)`. -/
theorem bcHodge_wedge (he : IsMonBC 𝒢 𝒢' e) {g : ℕ}
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcHodge he g (𝒢.wedge f) =
      𝒢'.wedge (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩) := by
  unfold GroupModel.wedge
  rw [bcHodge_tmul, map_one, bcExt_ιMulti]
  rfl

/-! ### Complex points and Jacobians along `π` -/

omit [NumberField L] [NumberField L'] in
/-- (copied from `scratch/h5-glue/BaseChangePts.lean`, proved there) -/
theorem ptC_hom_comp_bO (τ' : L' →+* ℂ) :
    (GroupModel.ptC (L := L') τ').hom ≫ bO L L' =
      (GroupModel.ptC (L := L) (τ'.comp (algebraMap L L'))).hom := by
  simp only [GroupModel.ptC, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) Restriction does not change values
at points that land in the smaller open. -/
theorem evalAt_res {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens}
    (i : W ⟶ U) (hp : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U s = 𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) := by
  unfold GroupModel.evalAt
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hp.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  rw [dif_pos hU, dif_pos hp]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem ptC_hom_apply {L : Type} [Field L] [NumberField L] (τ : L →+* ℂ) (x : PrimeSpectrum ℂ) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  change PrimeSpectrum.comap (τ.comp (algebraMap (𝓞 L) L)) x = _
  haveI := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  show τ (algebraMap (𝓞 L) L a) ∈ x.asIdeal ↔ a ∈ (⊥ : Ideal (𝓞 L))
  rw [hx, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ τ.injective]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem one_mem_dom {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (τ : L →+* ℂ) {W : 𝒢.G.left.Opens}
    (hW : 𝒢.genericUnit ∈ W) : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x ∈ W
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  show (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left ((GroupModel.ptC τ).hom x) ∈ W
  have hx : (GroupModel.ptC (L := L) τ).hom x = genericPt L := ptC_hom_apply τ x
  rw [hx]
  exact hW

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem map_zero_of_hom {G : Type*} [Group G] {g : ℕ} (Φ : (Fin g → ℂ) → G)
    (h : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact (mul_eq_left.mp this.symm)

variable (e) in
/-- **Complex points along the base change**: `β : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ`, `p' ↦ π ∘ p'`, for
`σ = τ'|_L`. -/
noncomputable def bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p : 𝒢'.Pts τ') : 𝒢.Pts σ :=
  Over.homMk (p.left ≫ bcProj 𝒢 𝒢' e) (by
    subst hστ
    refine (Category.assoc _ _ _).trans ?_
    rw [bcProj_w]
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ bO L L') (Over.w p)).trans (ptC_hom_comp_bO τ'))

theorem evalAt_bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p : 𝒢'.Pts τ') (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt (bcPts e σ τ' hστ p) U s =
      𝒢'.evalAt p (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) ((bcProj 𝒢 𝒢' e).app U s) := by
  unfold GroupModel.evalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (bcProj 𝒢 𝒢' e ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (bcPts e σ τ' hστ p).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (bcPts e σ τ' hστ p).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem dom_bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ}
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (U : 𝒢.G.left.Opens) :
    𝒢.dom (fun z => bcPts e σ τ' hστ (Φ' z)) U = 𝒢'.dom Φ' (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) := rfl

/-- **The germ along `β ∘ Φ'` of `t` agrees near `0` with the germ along `Φ'` of `π^* t`.** -/
theorem germAlong_bcPts_eventuallyEq (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ)
    (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (hΦ : 𝒢'.IsAnalyticUniformization τ' Λ Φ')
    (t : 𝒢.genStalk) :
    𝒢.germAlong (fun z => bcPts e σ τ' hστ (Φ' z)) t =ᶠ[nhds 0] 𝒢'.germAlong Φ' (bcMap he t) := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒢.exists_rep t).choose
  set m := (𝒢.exists_rep t).choose_spec.choose
  set s := (𝒢.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  have hx' : 𝒢'.genericUnit ∈ bcProj 𝒢 𝒢' e ⁻¹ᵁ U := by
    show bcProj 𝒢 𝒢' e 𝒢'.genericUnit ∈ U
    rw [bcProj_genericUnit he]; exact m
  set U' := (𝒢'.exists_rep (bcMap he t)).choose
  set m' := (𝒢'.exists_rep (bcMap he t)).choose_spec.choose
  set s' := (𝒢'.exists_rep (bcMap he t)).choose_spec.choose_spec.choose
  have hs' : 𝒢'.G.left.presheaf.germ U' 𝒢'.genericUnit m' s' = bcMap he t :=
    (𝒢'.exists_rep (bcMap he t)).choose_spec.choose_spec.choose_spec
  have heq : 𝒢'.G.left.presheaf.germ (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) 𝒢'.genericUnit hx'
      ((bcProj 𝒢 𝒢' e).app U s) = 𝒢'.G.left.presheaf.germ U' 𝒢'.genericUnit m' s' := by
    rw [hs', ← hs, bcMap_germ he U m hx' s]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ hx' m' _ _ heq
  have hnhds : 𝒢'.dom Φ' W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ' 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ' hmul]
    exact one_mem_dom 𝒢' τ' mW
  filter_upwards [hnhds] with z hz
  show 𝒢.evalAt (bcPts e σ τ' hστ (Φ' z)) U s = 𝒢'.evalAt (Φ' z) U' s'
  rw [evalAt_bcPts, evalAt_res 𝒢' (Φ' z) iU hz, hW, ← evalAt_res 𝒢' (Φ' z) iV hz]

/-- **Jacobian determinants along the base change**:
`jacDet (β ∘ Φ') f = jacDet' Φ' (π^* f)`. -/
theorem jacDet_bcPts (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ)
    (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (hΦ : 𝒢'.IsAnalyticUniformization τ' Λ Φ')
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet (fun z => bcPts e σ τ' hστ (Φ' z)) f =
      𝒢'.jacDet Φ' (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩) := by
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [(germAlong_bcPts_eventuallyEq he σ τ' hστ Λ Φ' hΦ (f i)).fderiv_eq]

end Construction

/-! ### Half of BC-lat: `ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}` (proved) -/

section LatticeHalf

variable {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem stalkSpecializes_stalkSpecializes_apply' {X : Scheme.{0}} {x y z : X} (h : x ⤳ y)
    (h' : y ⤳ z) (t : X.presheaf.stalk z) :
    X.presheaf.stalkSpecializes h (X.presheaf.stalkSpecializes h' t) =
      X.presheaf.stalkSpecializes (h.trans h') t := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem stalkSpecializes_self_apply' {X : Scheme.{0}} {x : X} (h : x ⤳ x)
    (t : X.presheaf.stalk x) : X.presheaf.stalkSpecializes h t = t := by
  rw [show h = specializes_refl x from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- At each point `s'` of `Spec 𝓞_{L'}`, `π^*` maps `(ω_𝒢)_{s}` (`s` the image of `s'`) into
`(ω_{𝒢'})_{s'}`. -/
theorem bcCot_omegaAt (he : IsMonBC 𝒢 𝒢' e) (s' : Spec (CommRingCat.of (𝓞 L')))
    (m : 𝒢.cotangent) (hm : m ∈ 𝒢.omegaAt (bO L L' s')) : bcCot he m ∈ 𝒢'.omegaAt s' := by
  have hE := bcProj_unit he
  have hp : bcProj 𝒢 𝒢' e (𝒢'.unitSection s') = 𝒢.unitSection (bO L L' s') :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun φ => φ s') hE).trans (Scheme.Hom.comp_apply _ _ _))
  let T := 𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, hmem, rfl⟩ := hx
    set g' := (bcProj 𝒢 𝒢' e).stalkMap (𝒢'.unitSection s') (T g)
    have hspec : 𝒢'.G.left.presheaf.stalkSpecializes (𝒢'.specializes_genericUnit s') g' =
        bcMap he (𝒢.G.left.presheaf.stalkSpecializes
          (𝒢.specializes_genericUnit (bO L L' s')) g) := by
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
      unfold bcMap
      rw [CommRingCat.comp_apply]
      congr 1
      rw [stalkSpecializes_stalkSpecializes_apply', stalkSpecializes_stalkSpecializes_apply']
    have hker : g' ∈ RingHom.ker (𝒢'.unitSection.stalkMap s').hom := by
      rw [RingHom.mem_ker]
      have h1 := Scheme.Hom.stalkMap_comp 𝒢'.unitSection (bcProj 𝒢 𝒢' e) s'
      have h2 := Scheme.Hom.stalkMap_congr_hom _ _ hE s'
      have h1' : (𝒢'.unitSection.stalkMap s') g' =
          ((𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e).stalkMap s') (T g) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h1
        exact this.symm
      have h2' : ((𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e).stalkMap s') (T g) =
          ((bO L L' ≫ 𝒢.unitSection).stalkMap s') ((𝒢.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g)) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h2
        exact this
      rw [h1', h2']
      have h3 := Scheme.Hom.stalkMap_comp (bO L L') 𝒢.unitSection s'
      have h3' := congrArg (fun φ => (ConcreteCategory.hom φ) ((𝒢.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g))) h3
      simp only at h3'
      rw [h3']
      have h4 : ∀ y : 𝒢.G.left.presheaf.stalk (𝒢.unitSection (bO L L' s')), y = g →
          (𝒢.unitSection.stalkMap (bO L L' s')) y = 0 := by
        rintro y rfl; exact hg
      have h5 : (𝒢.unitSection.stalkMap (bO L L' s')) ((𝒢.G.left.presheaf.stalkCongr
          (Inseparable.of_eq hp)).hom (T g)) = 0 := by
        apply h4
        show 𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).symm.specializes
          (T g) = g
        exact (stalkSpecializes_stalkSpecializes_apply' _ _ g).trans
          (stalkSpecializes_self_apply' _ g)
      exact (congrArg (fun y => ((bO L L').stalkMap s') y) h5).trans (map_zero _)
    have hmem' : 𝒢'.G.left.presheaf.stalkSpecializes (𝒢'.specializes_genericUnit s') g' ∈
        IsLocalRing.maximalIdeal 𝒢'.genStalk := by
      rw [hspec]; exact bcMap_mem_maximalIdeal he _ hmem
    apply Submodule.subset_span
    refine ⟨g', hker, hmem', ?_⟩
    rw [bcCot_dCls]
    congr 1
    exact Subtype.ext hspec.symm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- `π^*(ω_𝒢) ⊆ ω_{𝒢'}`. -/
theorem bcCot_omega (he : IsMonBC 𝒢 𝒢' e) (m : 𝒢.cotangent) (hm : m ∈ 𝒢.omega) :
    bcCot he m ∈ 𝒢'.omega := by
  rw [GroupModel.omega, Submodule.mem_iInf] at hm ⊢
  exact fun s' => bcCot_omegaAt he s' m (hm _)

/-- `ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}`. -/
theorem bcHodge_detLattice (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (x : 𝒢.hodgeSpace g)
    (hx : x ∈ 𝒢.detLattice g) : bcHodge he g x ∈ 𝒢'.detLattice g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [bcHodge_tmul, map_one, bcExt_ιMulti]
    apply Submodule.subset_span
    exact ⟨fun i => ⟨bcCot he (v i), bcCot_omega he _ (v i).2⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul L r y, bcHodge_smul]
    have : algebraMap L L' (algebraMap (𝓞 L) L r) • bcHodge he g y =
        (algebraMap (𝓞 L) (𝓞 L') r) • bcHodge he g y := by
      rw [← algebraMap_smul L' (algebraMap (𝓞 L) (𝓞 L') r)]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ hy

/-- **Half of BC-lat (proved)**: `𝓞_{L'} · ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}`. -/
theorem span_bcHodge_le (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    Submodule.span (𝓞 L') (bcHodge he g '' 𝒢.detLattice g) ≤ 𝒢'.detLattice g :=
  Submodule.span_le.mpr (by
    rintro _ ⟨x, hx, rfl⟩
    exact bcHodge_detLattice he g x hx)

/-- A multilinear map sends a tuple of vectors of `span S` into the span of its values on tuples
of vectors of `S` (induction on the number of coordinates not yet in `S`). -/
theorem multilinear_mem_span {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M) N)
    (S : Set M) : ∀ (k : ℕ) (v : Fin n → M), (∀ i : Fin n, (i : ℕ) < k → v i ∈ Submodule.span R S) →
      (∀ i : Fin n, k ≤ (i : ℕ) → v i ∈ S) →
      f v ∈ Submodule.span R (f '' {w | ∀ i, w i ∈ S}) := by
  classical
  intro k
  induction k with
  | zero =>
    intro v _ hS
    exact Submodule.subset_span ⟨v, fun i => hS i (Nat.zero_le _), rfl⟩
  | succ k ih =>
    intro v hspan hS
    by_cases hk : k < n
    · set i0 : Fin n := ⟨k, hk⟩
      have hmot : ∀ x ∈ Submodule.span R S,
          f (Function.update v i0 x) ∈ Submodule.span R (f '' {w | ∀ i, w i ∈ S}) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          apply ih
          · intro i hi
            rw [Function.update_of_ne (fun h => by rw [h] at hi; exact lt_irrefl _ hi)]
            exact hspan i (Nat.lt_succ_of_lt hi)
          · intro i hi
            by_cases hii : i = i0
            · rw [hii, Function.update_self]; exact hy
            · rw [Function.update_of_ne hii]
              apply hS i
              have : (i : ℕ) ≠ k := fun h => hii (Fin.ext h)
              omega
        | zero => rw [f.map_update_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [f.map_update_add]; exact add_mem hx hy
        | smul r x _ hx => rw [f.map_update_smul]; exact Submodule.smul_mem _ r hx
      have := hmot (v i0) (hspan i0 (Nat.lt_succ_self k))
      rwa [Function.update_eq_self] at this
    · apply ih v
      · intro i hi; exact hspan i (Nat.lt_succ_of_lt hi)
      · intro i hi
        apply hS i
        have := i.2
        omega

end LatticeHalf

/-- **Glue BC-omega (flat base change of `e*Ω¹`, the hard inclusion).** Every element of
`ω_{𝒢'} = Γ(Spec 𝓞_{L'}, e'*Ω¹_{𝒢'/𝓞_{L'}})` is an `𝓞_{L'}`-combination of pull-backs
`π^*η`, `η ∈ ω_𝒢`. True: `e*Ω¹_{𝒢/𝓞_L}` is locally free (`𝒢` smooth), its formation commutes with
base change (EGA IV 16.4.5 / 17.2.5, UNVERIFIED locators), and for the projective `𝓞_L`-module
`ω_𝒢`, `Γ(Spec 𝓞_{L'}, f^*ω̃) = 𝓞_{L'} ⊗ ω_𝒢`. The other inclusion is proved (`bcCot_omega`).
A model review notes that this inclusion needs less: `e` is a closed immersion (`𝒢` separated),
`omegaAt s` is the image of the stalk of the quasi-coherent conormal `e^*(I/I²)`, and
`I'_{e'(s')} = I_{e(s)} · 𝒪_{𝒢',e'(s')}` for the base-changed section, so
`d(a · π^*f) = e'^#(a) · π^*(df)`; smoothness is not used. STANDARD. -/
def OmegaBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e), 𝒢'.omega ≤ Submodule.span (𝓞 L') (bcCot he '' 𝒢.omega)


/-! # Part C: `HodgeLineBaseChangeDescent` from glue statements over the natural map

All six are about the honest natural map: `π = e.hom.left ≫ pullback.fst : 𝒢' → 𝒢`, its stalk map
`bcMap : 𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`, `ψ = bcHodge = L' ⊗ ⋀^g π^*` and `β = bcPts : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ`,
`p' ↦ π ∘ p'`. None is a literature leaf; each is glue (a property of def-faltings' definitions).
Six statements are stated; `PtsBaseChangeMul` and `PtsBaseChangeBij` are then proved, and
`DetLatticeBC` is reduced to `OmegaBaseChange` (`detLatticeBC_of_omega`). -/

/-- **Glue BC-alg (cotangent base change).** `ψ` is injective on nonzero vectors and the Hodge space
of `𝒢'` is an `L'`-line iff that of `𝒢` is an `L`-line. True because `ω_{A_{L'}} = L' ⊗_L ω_{A_L}`
(the cotangent space at a rational point commutes with field extension: `𝒪_{𝒢',ξ'}` is a
localization of `𝒪_{𝒢,ξ} ⊗_L L'` with maximal ideal generated by that of `𝒪_{𝒢,ξ}`), and `⋀^g`
commutes with base change; with `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} V ≅ ⋀^g_L V` (exterior powers commute with
localization) this gives `L' ⊗_L hodgeSpace ≅ hodgeSpace'` through `ψ`. STANDARD. -/
def HodgeBCInjective : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    (∀ v, v ≠ 0 → bcHodge he g v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1)

/-- **Glue BC-lat (flat base change of `e*Ω¹`).** `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)`. True because
formation of `e*Ω¹_{𝒢/𝓞_L}` (locally free, `𝒢` smooth) commutes with base change
(EGA IV 16.4.5 for `Ω¹`, IV 17.2.5 for conormal `≅ e*Ω¹`; UNVERIFIED locators), so
`ω_{𝒢'} = 𝓞_{L'} · π^*(ω_𝒢)` inside `ω_{A_{L'}}`. It relies on `omegaAt s` being the conormal stalk
and on `omega` being the intersection of the stalks, as every statement about `ω` does.
Reduced to `OmegaBaseChange` below (`detLatticeBC_of_omega`). STANDARD. -/
def DetLatticeBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    𝒢'.detLattice g = Submodule.span (𝓞 L') (bcHodge he g '' 𝒢.detLattice g)

open ExteriorAlgebra in
/-- **BC-lat from BC-omega** (proved; the inclusion `⊇` is `span_bcHodge_le`). -/
theorem detLatticeBC_of_omega (h : OmegaBaseChange) : DetLatticeBC := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he g
  refine le_antisymm ?_ (span_bcHodge_le he g)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v', rfl⟩
  let F : MultilinearMap (𝓞 L') (fun _ : Fin g => 𝒢'.cotangent) (𝒢'.hodgeSpace g) :=
    (TensorProduct.mk (𝓞 L') L' (exteriorPower (𝓞 L') g 𝒢'.cotangent) 1).compMultilinearMap
      (exteriorPower.ιMulti (𝓞 L') g).toMultilinearMap
  have key := multilinear_mem_span F (bcCot he '' 𝒢.omega) g (fun i => (v' i : 𝒢'.cotangent))
    (fun i _ => h K A L L' 𝒢 𝒢' e he (v' i).2) (fun i hi => absurd i.2 (not_lt.mpr hi))
  show F (fun i => (v' i : 𝒢'.cotangent)) ∈ _
  refine Submodule.span_mono ?_ key
  rintro _ ⟨w, hw, rfl⟩
  choose u hu hwu using hw
  refine ⟨(1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => u i),
    Submodule.subset_span ⟨fun i => ⟨u i, hu i⟩, rfl⟩, ?_⟩
  rw [bcHodge_tmul, map_one, bcExt_ιMulti]
  have hw' : (fun i => bcCot he (u i)) = w := funext hwu
  rw [hw']
  rfl

/-- **Glue BC-pts-mul.** `β : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ` is multiplicative (it is induced by the
pullback, a monoidal functor, and `e` is a homomorphism). Category theory; STANDARD. -/
def PtsBaseChangeMul : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p q : 𝒢'.Pts τ'), bcPts e σ τ' hστ (p * q) = bcPts e σ τ' hστ p * bcPts e σ τ' hστ q

/-- **Glue BC-pts-bij.** `β` is bijective (universal property of the pullback; h5-glue's
`ptsBaseChangeEquiv` is a bijection with the same underlying map). STANDARD. -/
def PtsBaseChangeBij : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ),
    Function.Bijective (bcPts e σ τ' hστ)

/-- **Glue BC-lift (local structure of the base change).** A map `Φ' : ℂ^g → 𝒢'(ℂ)_{τ'}` whose
composite with `β` is an analytic uniformization of `𝒢(ℂ)_σ` is an analytic uniformization of
`𝒢'(ℂ)_{τ'}`: `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}` is covered by affine opens `Spec(R ⊗_{𝓞_L} 𝓞_{L'})`, whose
regular functions are, locally, quotients of sums `∑ fᵢ ⊗ aᵢ`, so their values along `Φ'` are
holomorphic where those of the `fᵢ` along `β ∘ Φ'` are (`evalAt_bcPts`). Openness of
`Φ'⁻¹(U'(ℂ))` for opens `U'` defined over `L'` (not pulled back from `𝒢`): `U'` is a union of
basic opens `D(h') ⊂ π⁻¹V`, and `{z ∈ dom (β ∘ Φ') V : h'(Φ' z) ≠ 0}` is open by continuity.
Neither `Λ` nor the group clauses are used for these two clauses. STANDARD. -/
def UniformizationLift : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) →
      𝒢'.IsAnalyticUniformization τ' Λ Φ'

/-- **Glue BC-span (Jacobians are determined by pulled-back germs).** For an analytic
uniformization `Φ'` of `𝒢'(ℂ)_{τ'}` and a `τ'`-semilinear `c'` on the Hodge space of `𝒢'`: if `c'`
computes `jacDet Φ'` on wedges of germs pulled back from `𝒢`, it does so on all wedges. True: the
derivative at `0` of `t ↦ germAlong Φ' t` kills `𝔪'²` and is `τ'`-semilinear, so `jacDet Φ'` is a
`τ'`-semilinear alternating function of `(df'_i)`, as is `c' ∘ wedge`; the classes `d(π^*f)`
span `ω_{A_{L'}}` over `𝓞_{L'}` (cotangent base change `V' = L' · bcCot(V)`, clearing
denominators; this spanning fact is part of this statement, not of `HodgeBCInjective`).
STANDARD. -/
def JacobianPullbackSpan : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (τ' : L' →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'), 𝒢'.IsAnalyticUniformization τ' Λ Φ' →
    ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ,
      (∀ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
        c' (𝒢'.wedge (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩)) =
          𝒢'.jacDet Φ' (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩)) →
      ∀ f' : Fin g → IsLocalRing.maximalIdeal 𝒢'.genStalk, c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f'

/-- **BC-pts-bij is a theorem** (universal property of the pullback). -/
theorem ptsBaseChangeBij : PtsBaseChangeBij := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ
  subst hστ
  have hhominv : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id]; rfl
  have hinvhom : e.inv.left ≫ e.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, e.inv_hom_id]; rfl
  have hw : e.hom.left ≫ pullback.snd _ _ = 𝒢'.G.hom := Over.w e.hom
  constructor
  · intro p q hpq
    have h1 : p.left ≫ bcProj 𝒢 𝒢' e = q.left ≫ bcProj 𝒢 𝒢' e := congrArg Over.Hom.left hpq
    have h2 : p.left ≫ e.hom.left = q.left ≫ e.hom.left := by
      apply pullback.hom_ext
      · simpa only [bcProj, Category.assoc] using h1
      · rw [Category.assoc, Category.assoc, hw]
        exact (Over.w p).trans (Over.w q).symm
    have h3 := congrArg (· ≫ e.inv.left) h2
    simp only [Category.assoc, hhominv, Category.comp_id] at h3
    exact Over.OverMorphism.ext h3
  · intro q
    have w : q.left ≫ 𝒢.G.hom = (GroupModel.ptC (L := L') τ').hom ≫ bO L L' :=
      (Over.w q).trans (ptC_hom_comp_bO (L := L) τ').symm
    let pl : (GroupModel.ptC (L := L') τ').left ⟶ 𝒢'.G.left :=
      pullback.lift q.left (GroupModel.ptC (L := L') τ').hom w ≫ e.inv.left
    have hpl : pl ≫ 𝒢'.G.hom = (GroupModel.ptC (L := L') τ').hom := by
      have hw' : e.inv.left ≫ 𝒢'.G.hom = pullback.snd _ _ := Over.w e.inv
      simp only [pl, Category.assoc, hw']
      exact pullback.lift_snd _ _ _
    refine ⟨Over.homMk pl hpl, ?_⟩
    apply Over.OverMorphism.ext
    show pl ≫ bcProj 𝒢 𝒢' e = q.left
    simp only [pl, bcProj, Category.assoc]
    rw [reassoc_of% hinvhom]
    exact pullback.lift_fst _ _ _

/-- **BC-pts-mul is a theorem** (`e` is a homomorphism; components of `μ` of `Over.pullback`). -/
theorem ptsBaseChangeMul : PtsBaseChangeMul := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ p q
  subst hστ
  let _ : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  have : IsMonHom e.hom := he
  apply Over.OverMorphism.ext
  show (p * q).left ≫ bcProj 𝒢 𝒢' e =
    (bcPts e _ τ' rfl p * bcPts e _ τ' rfl q).left
  have h1 : (p * q) ≫ e.hom = (p ≫ e.hom) * (q ≫ e.hom) := MonObj.mul_comp p q e.hom
  have h2 : (p * q).left ≫ bcProj 𝒢 𝒢' e =
      ((p ≫ e.hom) * (q ≫ e.hom)).left ≫ pullback.fst _ _ := by
    rw [← h1, Over.comp_left, Category.assoc]
    rfl
  rw [h2]
  show (lift (p ≫ e.hom) (q ≫ e.hom) ≫ (Functor.LaxMonoidal.μ (Over.pullback (bO L L')) 𝒢.G 𝒢.G ≫
      (Over.pullback (bO L L')).map μ[𝒢.G])).left ≫ pullback.fst _ _ =
    (lift (bcPts e _ τ' rfl p) (bcPts e _ τ' rfl q) ≫ μ[𝒢.G]).left
  have hmap : ((Over.pullback (bO L L')).map μ[𝒢.G]).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ μ[𝒢.G].left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hmap,
    ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst, Over.lift_left,
      Over.lift_left, pullback.lift_fst_assoc]
    rw [Over.comp_left, Category.assoc]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd, Over.lift_left,
      Over.lift_left, pullback.lift_snd_assoc]
    rw [Over.comp_left, Category.assoc]
    exact (pullback.lift_snd _ _ _).symm

/-- **Glue AN-jac (the Jacobian is a semilinear function of the wedge).** For an analytic
uniformization `Φ` of `𝒢(ℂ)_τ` (any group model, any `g`), `f ↦ jacDet Φ f` factors through
`wedge` by a `τ`-semilinear map on the Hodge space. True: near `0`, `t ↦ germAlong Φ t` is a ring
homomorphism into germs of holomorphic functions (`Φ(0) = 1` lies over `ξ`, the sets `dom Φ U`
are open), so `D(t) = d(germAlong Φ t)(0)` is a derivation at evaluation at `0`: it kills `𝔪_ξ²`
and is `τ`-semilinear on `𝔪_ξ/𝔪_ξ²` (structure sections are constant `τ(r)` along `Φ`), and
`det(D(fᵢ)(e_j))` is alternating in the `dfᵢ`; it extends to `L ⊗ ⋀^g` by `a ⊗ x ↦ τ(a) J(x)`.
A statement about one group model; analytic glue. STANDARD. -/
def JacobianSemilinear : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ J : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, 𝒢.jacDet Φ f = J (𝒢.wedge f)

/-- **Glue BC-hspan (the image of `ψ` spans).** `L' · ψ(hodgeSpace g) = hodgeSpace' g`. True by
cotangent base change `ω_{A_{L'}} = L' · π^*(ω_{A_L})` and multilinearity; proved from
`CotangentSpanBC` below (`hodgeSpanBC_of`). (The `L'`-linear extension `L' ⊗_L hodgeSpace →
hodgeSpace'` is in fact an isomorphism, but that does not follow from this statement and
`HodgeBCInjective` alone unless `hodgeSpace` is a line.) STANDARD. -/
def HodgeSpanBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    Submodule.span L' (Set.range (bcHodge he g)) = ⊤

/-- **Glue BC-cot (cotangent base change, spanning half).** The classes `π^*v`, `v ∈ ω_{A_L}`,
span `ω_{A_{L'}}` over `𝓞_{L'}`. True: `𝒪_{𝒢',ξ'}` is a localization of `𝒪_{𝒢,ξ} ⊗_L L'` whose
maximal ideal is generated by `𝔪_ξ`, so `ω_{A_{L'}} = L' ⊗_L ω_{A_L}`; denominators in `L'` are
cleared because `ω_{A_L}` is a `ℚ`-vector space. A statement about the local rings at the origin
only (no Hodge data). STANDARD. -/
def CotangentSpanBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e), Submodule.span (𝓞 L') (Set.range (bcCot he)) = ⊤

open ExteriorAlgebra in
/-- **BC-hspan from BC-cot** (multilinearity; proved). -/
theorem hodgeSpanBC_of (h : CotangentSpanBC) : HodgeSpanBC := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he g
  rw [eq_top_iff]
  rintro w -
  induction w using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a x =>
    rw [show a ⊗ₜ[𝓞 L'] x = a • ((1 : L') ⊗ₜ[𝓞 L'] x) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]]
    refine Submodule.smul_mem _ a ?_
    have hx : x ∈ Submodule.span (𝓞 L') (Set.range (exteriorPower.ιMulti (𝓞 L') g)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v', rfl⟩ := hy
      let F : MultilinearMap (𝓞 L') (fun _ : Fin g => 𝒢'.cotangent) (𝒢'.hodgeSpace g) :=
        (TensorProduct.mk (𝓞 L') L' (exteriorPower (𝓞 L') g 𝒢'.cotangent) 1).compMultilinearMap
          (exteriorPower.ιMulti (𝓞 L') g).toMultilinearMap
      have key := multilinear_mem_span F (Set.range (bcCot he)) g v'
        (fun i _ => by rw [h K A L L' 𝒢 𝒢' e he]; trivial)
        (fun i hi => absurd i.2 (not_lt.mpr hi))
      have hsub : Submodule.span (𝓞 L') (F '' {w | ∀ i, w i ∈ Set.range (bcCot he)}) ≤
          (Submodule.span L' (Set.range (bcHodge he g))).restrictScalars (𝓞 L') := by
        rw [Submodule.span_le]
        rintro _ ⟨w, hw, rfl⟩
        choose u hu using hw
        apply Submodule.subset_span
        refine ⟨(1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g u, ?_⟩
        rw [bcHodge_tmul, map_one, bcExt_ιMulti]
        have hw' : (fun i => bcCot he (u i)) = w := funext hu
        rw [hw']
        rfl
      exact hsub key
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_of_tower_mem _ r hy
  | add x y hx hy => exact add_mem hx hy

open ExteriorAlgebra in
/-- **BC-span from AN-jac and BC-hspan** (proved). -/
theorem jacobianPullbackSpan_of (hJ : JacobianSemilinear) (hS : HodgeSpanBC) :
    JacobianPullbackSpan := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he τ' g Λ Φ' hΦ' c' hc f'
  obtain ⟨J, hJf⟩ := hJ K A L' 𝒢' τ' Λ Φ' hΦ'
  suffices hcJ : c' = J by rw [hcJ, hJf]
  have hwedge : ∀ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      c' (bcHodge he g (𝒢.wedge f)) = J (bcHodge he g (𝒢.wedge f)) := by
    intro f
    rw [bcHodge_wedge, hc f, hJf]
  have hagree : ∀ v, c' (bcHodge he g v) = J (bcHodge he g v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have hx : x ∈ Submodule.span (𝓞 L) (Set.range (exteriorPower.ιMulti (𝓞 L) g)) := by
        rw [exteriorPower.ιMulti_span]; trivial
      induction hx using Submodule.span_induction generalizing a with
      | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        choose f hf using fun i => (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective (v i)
        have h1 : a ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v = a • 𝒢.wedge f := by
          unfold GroupModel.wedge GroupModel.dCls
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
          congr 2
          funext i
          exact (hf i).symm
        rw [h1, bcHodge_smul, map_smulₛₗ, map_smulₛₗ, hwedge f]
      | zero => simp
      | add y z _ _ hy hz =>
        rw [TensorProduct.tmul_add, map_add, map_add, map_add, hy, hz]
      | smul r y _ hy =>
        rw [← TensorProduct.smul_tmul]
        exact hy _
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  apply LinearMap.ext
  intro w
  have hw : w ∈ Submodule.span L' (Set.range (bcHodge he g)) := by
    rw [hS K A L L' 𝒢 𝒢' e he g]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    exact hagree v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a y _ hy => rw [map_smulₛₗ, map_smulₛₗ, hy]

/-- **Glue BC-lift-an (the analytic core of BC-lift).** If `β ∘ Φ'` is an analytic
uniformization of `𝒢(ℂ)_σ`, then the sets `Φ'⁻¹(U'(ℂ))` are open and the regular functions of
`𝒢'` are holomorphic along `Φ'`, for every open `U'` of `𝒢'` (including opens defined over `L'`
and not pulled back from `𝒢`). Same justification as `UniformizationLift` (affine opens
`Spec(R ⊗_{𝓞_L} 𝓞_{L'})` and basic opens `D(h')`). STANDARD. -/
def UniformizationLiftAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) →
      (∀ U, IsOpen (𝒢'.dom Φ' U)) ∧
        ∀ U (s : Γ(𝒢'.G.left, U)),
          DifferentiableOn ℂ (fun z => 𝒢'.evalAt (Φ' z) U s) (𝒢'.dom Φ' U)

/-- **BC-lift from its analytic core** (the group clauses come from `β` being a bijective
homomorphism: `ptsBaseChangeMul`, `ptsBaseChangeBij`). Proved. -/
theorem uniformizationLift_of (h : UniformizationLiftAnalytic) : UniformizationLift := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ g Λ Φ' hU
  obtain ⟨hopen, hdiff⟩ := h K A L L' 𝒢 𝒢' e he σ τ' hστ Λ Φ' hU
  obtain ⟨hmul, hker, hsurj, -, -⟩ := hU
  have hbij := ptsBaseChangeBij K A L L' 𝒢 𝒢' e he σ τ' hστ
  have hm := ptsBaseChangeMul K A L L' 𝒢 𝒢' e he σ τ' hστ
  have h1 : bcPts e σ τ' hστ (1 : 𝒢'.Pts τ') = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.mp this.symm
  refine ⟨?_, ?_, ?_, hopen, hdiff⟩
  · intro z w
    apply hbij.1
    rw [hm]
    exact hmul z w
  · intro z
    rw [← hker z]
    constructor
    · intro hz
      show bcPts e σ τ' hστ (Φ' z) = 1
      rw [hz, h1]
    · intro hz
      apply hbij.1
      rw [h1]
      exact hz
  · intro p
    obtain ⟨z, hz⟩ := hsurj (bcPts e σ τ' hστ p)
    exact ⟨z, hbij.1 hz⟩

/-- **Descent of analytic uniformizations along `β`** (proved, from BC-pts-mul and BC-pts-bij). -/
theorem isAnalyticUniformization_bcPts (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij)
    {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}
    (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ')
    (h : 𝒢'.IsAnalyticUniformization τ' Λ Φ') :
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  have hbij := hb K A L L' 𝒢 𝒢' e he σ τ' hστ
  have hmul' := hm K A L L' 𝒢 𝒢' e he σ τ' hστ
  have h1 : bcPts e σ τ' hστ (1 : 𝒢'.Pts τ') = 1 := by
    have := hmul' 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.mp this.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    simp only
    rw [hmul, hmul']
  · intro z
    rw [← hker z]
    constructor
    · intro hz
      apply hbij.1
      have hz' : bcPts e σ τ' hστ (Φ' z) = 1 := hz
      rw [hz', h1]
    · intro hz
      simp only
      rw [hz, h1]
  · intro q
    obtain ⟨p, rfl⟩ := hbij.2 q
    obtain ⟨z, rfl⟩ := hsurj p
    exact ⟨z, rfl⟩
  · intro U
    rw [dom_bcPts]
    exact hopen _
  · intro U s
    rw [dom_bcPts]
    simp only [evalAt_bcPts]
    exact hdiff _ _

/-- **`HodgeLineBaseChangeDescent` from the six glue statements over the natural map** (two of
them, `PtsBaseChangeMul` and `PtsBaseChangeBij`, are proved above). Proved. -/
theorem hodgeLineBaseChangeDescent_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : HodgeLineBaseChangeDescent := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨e, he⟩ := h𝒢
  obtain ⟨hinj, hfin⟩ := h1 K A L L' 𝒢 𝒢' e he g
  refine ⟨bcHodge he g, bcHodge_smul he g, hinj, hfin, h2 K A L L' 𝒢 𝒢' e he g, ?_, ?_⟩
  · intro τ' Λ Φ hΦ
    have hbij := hb K A L L' 𝒢 𝒢' e he _ τ' rfl
    choose Φ' hΦ' using fun z => hbij.2 (Φ z)
    have hΦeq : (fun z => bcPts e _ τ' rfl (Φ' z)) = Φ := funext hΦ'
    have hU' : 𝒢'.IsAnalyticUniformization τ' Λ Φ' := by
      refine hl K A L L' 𝒢 𝒢' e he _ τ' rfl Λ Φ' ?_
      rw [hΦeq]
      exact hΦ
    refine ⟨Φ', hU', fun c c' hc hcc' => hj K A L L' 𝒢 𝒢' e he τ' Λ Φ' hU' c' (fun f => ?_)⟩
    rw [← bcHodge_wedge he f, hcc', hc, ← jacDet_bcPts he _ τ' rfl Λ Φ' hU' f, hΦeq]
  · intro σ τ' hστ Λ Φ' hΦ'
    refine ⟨fun z => bcPts e σ τ' hστ (Φ' z),
      isAnalyticUniformization_bcPts hm hb he σ τ' hστ Λ Φ' hΦ', fun c' hc' f => ?_⟩
    rw [bcHodge_wedge he f, hc', jacDet_bcPts he σ τ' hστ Λ Φ' hΦ' f]

/-- **Glue H4a (`ModelHeightBaseChange`, verbatim) from the six glue statements.** Proved. -/
theorem modelHeightBaseChange_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_descent (hodgeLineBaseChangeDescent_of_glue h1 h2 hm hb hl hj)

/-- **`HodgeLineBaseChange` (verbatim) from the six glue statements.** Proved. -/
theorem hodgeLineBaseChange_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_descent (hodgeLineBaseChangeDescent_of_glue h1 h2 hm hb hl hj)

/-- **Main result: glue H4a (`ModelHeightBaseChange`, verbatim) from four glue statements**
(BC-alg, BC-lat, BC-lift, BC-span; BC-pts-mul and BC-pts-bij are now theorems). Proved. -/
theorem modelHeightBaseChange_of_four (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_glue h1 h2 ptsBaseChangeMul ptsBaseChangeBij hl hj

/-- **Main result: `HodgeLineBaseChange` (verbatim) from the same four glue statements.** -/
theorem hodgeLineBaseChange_of_four (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_glue h1 h2 ptsBaseChangeMul ptsBaseChangeBij hl hj

/-- **`ModelHeightBaseChangeGE` (descent half of H4a) needs only BC-alg and BC-lat** (the
uniformization descent is proved). -/
theorem modelHeightBaseChangeGE_of_two (h1 : HodgeBCInjective) (h2 : DetLatticeBC) :
    ModelHeightBaseChangeGE := by
  refine modelHeightBaseChangeGE_of_descentHalf ?_
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨e, he⟩ := h𝒢
  obtain ⟨hinj, hfin⟩ := h1 K A L L' 𝒢 𝒢' e he g
  refine ⟨bcHodge he g, bcHodge_smul he g, hinj, hfin, h2 K A L L' 𝒢 𝒢' e he g, ?_⟩
  intro σ τ' hστ Λ Φ' hΦ'
  refine ⟨fun z => bcPts e σ τ' hστ (Φ' z), isAnalyticUniformization_bcPts ptsBaseChangeMul
    ptsBaseChangeBij he σ τ' hστ Λ Φ' hΦ', fun c' hc' f => ?_⟩
  rw [bcHodge_wedge he f, hc', jacDet_bcPts he σ τ' hστ Λ Φ' hΦ' f]

/-- **Main result: glue H4a (`ModelHeightBaseChange`, verbatim) from four glue statements over
the natural map**: BC-alg (`HodgeBCInjective`), BC-omega (`OmegaBaseChange`), BC-lift
(`UniformizationLift`), BC-span (`JacobianPullbackSpan`). Proved. -/
theorem modelHeightBaseChange_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_four h1 (detLatticeBC_of_omega hω) hl hj

/-- **Main result: `HodgeLineBaseChange` (verbatim) from the same four glue statements.** -/
theorem hodgeLineBaseChange_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_four h1 (detLatticeBC_of_omega hω) hl hj

/-- **The descent half of H4a from BC-alg and BC-omega only.** -/
theorem modelHeightBaseChangeGE_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange) :
    ModelHeightBaseChangeGE :=
  modelHeightBaseChangeGE_of_two h1 (detLatticeBC_of_omega hω)

/-- **Main result (finest form): glue H4a (`ModelHeightBaseChange`, verbatim) from five glue
statements**: BC-alg (`HodgeBCInjective`), BC-hspan (`HodgeSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-jac (`JacobianSemilinear`).
Proved. -/
theorem modelHeightBaseChange_of_five (h1 : HodgeBCInjective) (hS : HodgeSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_main h1 hω (uniformizationLift_of hl) (jacobianPullbackSpan_of hJ hS)

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements.** -/
theorem hodgeLineBaseChange_of_five (h1 : HodgeBCInjective) (hS : HodgeSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_main h1 hω (uniformizationLift_of hl) (jacobianPullbackSpan_of hJ hS)

/-- **Main result (finest form, with BC-cot): glue H4a (`ModelHeightBaseChange`, verbatim) from
five glue statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-jac (`JacobianSemilinear`).
Proved. -/
theorem modelHeightBaseChange_of_glue5 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_five h1 (hodgeSpanBC_of hc) hω hl hJ

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements.** -/
theorem hodgeLineBaseChange_of_glue5 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_five h1 (hodgeSpanBC_of hc) hω hl hJ



/-! # Part D: H5 (h5-glue's `stableFaltingsHeight_eq_neron_all'`) with H4a discharged -/

/-- h5-glue's `ModelHeightBaseChange` is this file's (same statement, verbatim copies). -/
theorem h5_modelHeightBaseChange_iff :
    ZInQ.H5Glue.ModelHeightBaseChange ↔ ModelHeightBaseChange := Iff.rfl

/-- **H5 in the multi-field form R19-R21 need, from the leaves N1, N2 and the five glue
statements of Part C** (h5-glue's theorem with `hbc` discharged by
`modelHeightBaseChange_of_glue5`). Proved. -/
theorem stableFaltingsHeight_eq_neron_of_glue5 (hN1 : ZInQ.H5Glue.NeronModelExists)
    (hN2 : ZInQ.H5Glue.SemistableNeronIdentityComponent) (h1 : HodgeBCInjective)
    (hc : CotangentSpanBC) (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic)
    (hJ : JacobianSemilinear) (K : Type) [Field K] [NumberField K] (A : AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        stableFaltingsHeight A = 𝒩'.height :=
  ZInQ.H5Glue.stableFaltingsHeight_eq_neron_all' hN1 hN2
    (h5_modelHeightBaseChange_iff.mpr (modelHeightBaseChange_of_glue5 h1 hc hω hl hJ)) K A

end ZInQ.HeightBC

#print axioms ZInQ.HeightBC.modelHeightBaseChange_of_glue5
#print axioms ZInQ.HeightBC.hodgeLineBaseChange_of_glue5
#print axioms ZInQ.HeightBC.stableFaltingsHeight_eq_neron_of_glue5
