import ZInQKernel.HDecomp.Faltings.Leaves
import Mathlib

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


/-! # infra-stalks: height-bc glue `CotangentSpanBC` and `UniformizationLiftAnalytic` proved
Part 1: general lemmas (`StalkPullback.lean`, `local_structure.lean.part`). Part 2: verbatim
`scratch/height-bc/Final.lean` (after its import). Part 3: `bc_proof.lean.part`,
`ula_proof.lean.part`, `hbc_final.lean.part`. -/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The stalk of `T` at `t` is *generated* by the stalk maps of `p : T ⟶ X` and `q : T ⟶ Y`:
every element is `c / w` with `c, w` in the subring generated by the two images and `w` a unit. -/
def StalkGen {T X Y : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ Y) (t : T) : Prop :=
  ∀ r : T.presheaf.stalk t, ∃ c ∈ (p.stalkMap t).hom.range ⊔ (q.stalkMap t).hom.range,
    ∃ w ∈ (p.stalkMap t).hom.range ⊔ (q.stalkMap t).hom.range, IsUnit w ∧ r * w = c

theorem stalkMap_comp_apply' {T X X' : Scheme.{u}} (p : T ⟶ X) (j : X ⟶ X') (t : T)
    (y : X'.presheaf.stalk ((p ≫ j) t)) :
    (p ≫ j).stalkMap t y = p.stalkMap t (j.stalkMap (p t) y) := by
  rw [Scheme.Hom.stalkMap_comp]; rfl

theorem range_stalkMap_comp {T X X' : Scheme.{u}} (p : T ⟶ X) (j : X ⟶ X') (t : T) :
    ((p ≫ j).stalkMap t).hom.range = (j.stalkMap (p t)).hom.range.map (p.stalkMap t).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨j.stalkMap (p t) y, ⟨y, rfl⟩, (stalkMap_comp_apply' p j t y).symm⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, stalkMap_comp_apply' p j t y⟩

/-- Post-composing with a morphism whose stalk map is an isomorphism (e.g. an open immersion)
does not change the image of the stalk map. -/
theorem range_stalkMap_comp_of_isIso {T X X' : Scheme.{u}} (p : T ⟶ X) (j : X ⟶ X') (t : T)
    [IsIso (j.stalkMap (p t))] :
    ((p ≫ j).stalkMap t).hom.range = (p.stalkMap t).hom.range := by
  rw [range_stalkMap_comp]
  have hs : Function.Surjective (j.stalkMap (p t)).hom :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap (p t))).2
  rw [RingHom.range_eq_top.mpr hs, ← RingHom.range_eq_map]

theorem StalkGen.comp_openImmersion {T X Y X' Y' : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y} {t : T}
    (h : StalkGen p q t) (jX : X ⟶ X') (jY : Y ⟶ Y') [IsOpenImmersion jX] [IsOpenImmersion jY] :
    StalkGen (p ≫ jX) (q ≫ jY) t := by
  unfold StalkGen
  rw [range_stalkMap_comp_of_isIso, range_stalkMap_comp_of_isIso]
  exact h

/-- Transport of `StalkGen` along a morphism `m : T ⟶ Q` whose stalk map at `t` is an isomorphism
(e.g. an open immersion). -/
theorem StalkGen.of_comp {T Q X Y : Scheme.{u}} (m : T ⟶ Q) (p : Q ⟶ X) (q : Q ⟶ Y) (t : T)
    [IsIso (m.stalkMap t)] (h : StalkGen (m ≫ p) (m ≫ q) t) : StalkGen p q (m t) := by
  intro r
  set α := m.stalkMap t
  have hα : Function.Bijective α.hom := ConcreteCategory.bijective_of_isIso α
  have hrange : ∀ φ : Q ⟶ X, ((m ≫ φ).stalkMap t).hom.range =
      (φ.stalkMap (m t)).hom.range.map α.hom := fun φ => range_stalkMap_comp m φ t
  have hrange' : ∀ φ : Q ⟶ Y, ((m ≫ φ).stalkMap t).hom.range =
      (φ.stalkMap (m t)).hom.range.map α.hom := fun φ => range_stalkMap_comp m φ t
  obtain ⟨c, hc, w, hw, hwu, hrw⟩ := h (α r)
  rw [hrange, hrange', ← Subring.map_sup] at hc hw
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨w', hw', rfl⟩ := hw
  refine ⟨c', hc', w', hw', ?_, ?_⟩
  · have := hwu.map (inv α).hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  · apply hα.1
    rw [map_mul, hrw]

/-- Germs at `t` of global sections of `Spec S` coming from `R` along `φ : R ⟶ S` are images under
the stalk map of `Spec.map φ`. -/
theorem germ_ΓSpecIso_inv_map {R S : CommRingCat.{u}} (φ : R ⟶ S) (t : Spec S) (a : R) :
    (Spec S).presheaf.germ ⊤ t trivial ((Scheme.ΓSpecIso S).inv (φ a)) =
      (Spec.map φ).stalkMap t
        ((Spec R).presheaf.germ ⊤ (Spec.map φ t) trivial ((Scheme.ΓSpecIso R).inv a)) := by
  erw [Scheme.Hom.germ_stalkMap_apply (Spec.map φ) ⊤ t (by trivial)]
  have h := Scheme.ΓSpecIso_inv_naturality φ
  have h2 : (Scheme.ΓSpecIso S).inv (φ a) = (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv a) := by
    rw [← CommRingCat.comp_apply, h, CommRingCat.comp_apply]
  rw [h2]
  rfl

open TensorProduct in
/-- **The affine case.** The stalk of `Spec (A ⊗[R] B)` is generated by the images of the stalks
of `Spec A` and `Spec B`. -/
theorem stalkGen_spec_tensor (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
    (t : Spec (CommRingCat.of (A ⊗[R] B))) :
    StalkGen (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A →+* A ⊗[R] B)))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] A ⊗[R] B).toRingHom)) t := by
  let T := Spec (CommRingCat.of (A ⊗[R] B))
  set iL : T ⟶ Spec A := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A →+* A ⊗[R] B))
  set iR : T ⟶ Spec B := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] A ⊗[R] B).toRingHom)
  set S' := (iL.stalkMap t).hom.range ⊔ (iR.stalkMap t).hom.range
  let γ : A ⊗[R] B →+* T.presheaf.stalk t :=
    (T.presheaf.germ ⊤ t trivial).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).inv.hom
  have hγ : ∀ a, γ a ∈ S' := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S'.zero_mem
    | add x y hx hy => rw [map_add]; exact S'.add_mem hx hy
    | tmul a b =>
      have e : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [e, map_mul]
      refine S'.mul_mem ((le_sup_left : _ ≤ S') ⟨_, (germ_ΓSpecIso_inv_map
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) t a).symm⟩)
        ((le_sup_right : _ ≤ S') ⟨_, (germ_ΓSpecIso_inv_map
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          B →ₐ[R] A ⊗[R] B).toRingHom) t b).symm⟩)
  intro r
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk t) := (T.presheaf.germ ⊤ t trivial).hom.toAlgebra
  have hL : IsLocalization.AtPrime (T.presheaf.stalk t)
      ((isAffineOpen_top T).primeIdealOf ⟨t, trivial⟩).asIdeal :=
    (isAffineOpen_top T).isLocalization_stalk ⟨t, trivial⟩
  obtain ⟨⟨a, s⟩, hrs⟩ := @IsLocalization.surj _ _ _ _ _ _ hL r
  refine ⟨_, ?_, _, ?_, @IsLocalization.map_units _ _ _ _ _ _ hL s, hrs⟩
  · have := hγ ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom a)
    convert this using 1
    exact (congrArg (T.presheaf.germ ⊤ t trivial).hom
      (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))) a)).symm
  · have := hγ ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom s.1)
    convert this using 1
    exact (congrArg (T.presheaf.germ ⊤ t trivial).hom
      (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))) s.1)).symm

/-- An affine chart of `X` through `x`, lying over a given affine chart `jV : Spec R ⟶ S` of `S`. -/
theorem exists_affine_chart_over {X S : Scheme.{u}} (f : X ⟶ S) {R : CommRingCat.{u}}
    (jV : Spec R ⟶ S) [IsOpenImmersion jV] (x : X) (hx : f x ∈ Set.range jV) :
    ∃ (A : CommRingCat.{u}) (jU : Spec A ⟶ X) (_ : IsOpenImmersion jU) (φ : R ⟶ A),
      x ∈ Set.range jU ∧ Spec.map φ ≫ jV = jU ≫ f := by
  obtain ⟨x', hx'⟩ : x ∈ Set.range (pullback.fst f jV) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  let 𝒰 := (pullback f jV).affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers x'
  refine ⟨𝒰.X (𝒰.idx x'), 𝒰.f _ ≫ pullback.fst f jV, inferInstance,
    Spec.preimage (𝒰.f _ ≫ pullback.snd f jV), ⟨y, ?_⟩, ?_⟩
  · rw [Scheme.Hom.comp_apply, hy, hx']
  · rw [Spec.map_preimage]
    simp only [Category.assoc, pullback.condition]

/-- **Stalks of a fibre product are generated by the stalks of the factors.** For `f : X ⟶ S`,
`g : Y ⟶ S` and `z ∈ X ×_S Y`, every element of `𝒪_{X ×_S Y, z}` is `c / w` with `c, w` in the
subring generated by the images of `𝒪_{X, fst z}` and `𝒪_{Y, snd z}` and `w` a unit. -/
theorem pullback_stalkGen {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (z : ↥(pullback f g)) :
    StalkGen (pullback.fst f g) (pullback.snd f g) z := by
  let 𝒱 := S.affineOpenCover
  let R := 𝒱.X (𝒱.idx (f (pullback.fst f g z)))
  let jV : Spec R ⟶ S := 𝒱.f (𝒱.idx (f (pullback.fst f g z)))
  have hs : f (pullback.fst f g z) ∈ Set.range jV := 𝒱.covers _
  obtain ⟨A, jU, _, φ, hxU, eU⟩ := exists_affine_chart_over f jV (pullback.fst f g z) hs
  have hs' : g (pullback.snd f g z) ∈ Set.range jV := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]; exact hs
  obtain ⟨B, jW, _, ψ, hyW, eW⟩ := exists_affine_chart_over g jV (pullback.snd f g z) hs'
  let _ : Algebra R A := φ.hom.toAlgebra
  let _ : Algebra R B := ψ.hom.toAlgebra
  let m := pullback.map (Spec.map φ) (Spec.map ψ) f g jU jW jV eU eW
  have hz : z ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]; exact ⟨hxU, hyW⟩
  obtain ⟨t0, ht0⟩ := hz
  let e := pullbackSpecIso R A B
  let m' : Spec (CommRingCat.of (TensorProduct R A B)) ⟶ pullback f g := e.inv ≫ m
  have h1 : m' ≫ pullback.fst f g = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A B)) ≫ jU := by
    simp only [m', m, e, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc]
    exact congrArg (· ≫ jU) (pullbackSpecIso_inv_fst R A B)
  have h2 : m' ≫ pullback.snd f g = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R A B).toRingHom) ≫ jW := by
    simp only [m', m, e, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc]
    exact congrArg (· ≫ jW) (pullbackSpecIso_inv_snd R A B)
  have key := StalkGen.of_comp m' (pullback.fst f g) (pullback.snd f g) (e.hom t0)
    (by rw [h1, h2]; exact (stalkGen_spec_tensor R A B _).comp_openImmersion jU jW)
  have hpt : m' (e.hom t0) = m t0 := by
    have he : e.inv (e.hom t0) = t0 := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    simp only [m']
    rw [Scheme.Hom.comp_apply, he]
  rw [hpt, ht0] at key
  exact key

/-! ### Maximal ideals and residue fields -/

/-- `x` is *rational over* `f x`: every element of `𝒪_{X,x}` is congruent modulo `𝔪_x` to the
image of an element of `𝒪_{S, f x}` (the residue field extension `κ(f x) → κ(x)` is onto). -/
def RationalOver {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∀ a : X.presheaf.stalk x, ∃ c : S.presheaf.stalk (f x),
    a - f.stalkMap x c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)

theorem StalkGen.comp_of_isIso {T Q X Y : Scheme.{u}} (m : T ⟶ Q) (p : Q ⟶ X) (q : Q ⟶ Y)
    (t : T) [IsIso (m.stalkMap t)] (h : StalkGen p q (m t)) : StalkGen (m ≫ p) (m ≫ q) t := by
  intro r
  set α := m.stalkMap t
  have hα : Function.Bijective α.hom := ConcreteCategory.bijective_of_isIso α
  obtain ⟨r', rfl⟩ := hα.2 r
  obtain ⟨c, hc, w, hw, hwu, hrw⟩ := h r'
  refine ⟨α c, ?_, α w, ?_, hwu.map α.hom, by rw [← map_mul, hrw]⟩
  · rw [range_stalkMap_comp, range_stalkMap_comp, ← Subring.map_sup]; exact ⟨c, hc, rfl⟩
  · rw [range_stalkMap_comp, range_stalkMap_comp, ← Subring.map_sup]; exact ⟨w, hw, rfl⟩

/-- The two composite stalk maps `𝒪_{S} → 𝒪_{T,t}` of a commutative square agree. -/
theorem exists_stalkMap_comp_eq {T X Y S : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ Y) (f : X ⟶ S)
    (g : Y ⟶ S) (w : p ≫ f = q ≫ g) (t : T) (c : S.presheaf.stalk (f (p t))) :
    ∃ c' : S.presheaf.stalk (g (q t)),
      p.stalkMap t (f.stalkMap (p t) c) = q.stalkMap t (g.stalkMap (q t) c') := by
  have hpt : (p ≫ f) t = (q ≫ g) t := by rw [w]
  refine ⟨(S.presheaf.stalkCongr (.of_eq hpt)).hom c, ?_⟩
  calc p.stalkMap t (f.stalkMap (p t) c) = (p ≫ f).stalkMap t c :=
        (stalkMap_comp_apply' p f t c).symm
    _ = (q ≫ g).stalkMap t ((S.presheaf.stalkCongr (.of_eq hpt)).hom c) := by
        rw [Scheme.Hom.stalkMap_congr_hom (p ≫ f) (q ≫ g) w t]; rfl
    _ = _ := stalkMap_comp_apply' q g t _

section MaximalIdeal

variable {T X Y S : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}

/-- The ideal `𝔪_x 𝒪_t + 𝔪_y 𝒪_t`. -/
noncomputable abbrev stalkIdeal (p : T ⟶ X) (q : T ⟶ Y) (t : T) : Ideal (T.presheaf.stalk t) :=
  (IsLocalRing.maximalIdeal _).map (p.stalkMap t).hom ⊔
    (IsLocalRing.maximalIdeal _).map (q.stalkMap t).hom

theorem stalkIdeal_le (t : T) : stalkIdeal p q t ≤ IsLocalRing.maximalIdeal _ := by
  refine sup_le (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
    (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
  · exact map_nonunit (p.stalkMap t).hom a ha
  · exact map_nonunit (q.stalkMap t).hom a ha

/-- Every element of the subring generated by the two images is congruent modulo
`𝔪_x 𝒪_t + 𝔪_y 𝒪_t` to an element coming from `𝒪_{Y,y}`, when `x` is rational over `s`. -/
theorem exists_sub_mem_stalkIdeal (w : p ≫ f = q ≫ g) {t : T} (hrat : RationalOver f (p t))
    {u : T.presheaf.stalk t} (hu : u ∈ (p.stalkMap t).hom.range ⊔ (q.stalkMap t).hom.range) :
    ∃ b : Y.presheaf.stalk (q t), u - q.stalkMap t b ∈ stalkIdeal p q t := by
  have hR : (p.stalkMap t).hom.range ⊔ (q.stalkMap t).hom.range ≤
      Subring.closure (Set.range (p.stalkMap t).hom ∪ Set.range (q.stalkMap t).hom) :=
    sup_le (fun x hx => Subring.subset_closure (Or.inl (RingHom.mem_range.mp hx)))
      (fun x hx => Subring.subset_closure (Or.inr (RingHom.mem_range.mp hx)))
  set I := stalkIdeal p q t
  suffices H : ∀ u' (hu' : u' ∈ Subring.closure
      (Set.range (p.stalkMap t).hom ∪ Set.range (q.stalkMap t).hom)),
      ∃ b : Y.presheaf.stalk (q t), u' - q.stalkMap t b ∈ I from H u (hR hu)
  intro u' hu'
  induction hu' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · obtain ⟨c, hc⟩ := hrat a
      obtain ⟨c', hc'⟩ := exists_stalkMap_comp_eq p q f g w t c
      refine ⟨g.stalkMap (q t) c', ?_⟩
      rw [← hc', ← map_sub]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc)
    · exact ⟨b, by rw [sub_self]; exact I.zero_mem⟩
  | zero => exact ⟨0, by rw [map_zero, sub_self]; exact I.zero_mem⟩
  | one => exact ⟨1, by rw [map_one, sub_self]; exact I.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨b1, h1⟩ := hx
    obtain ⟨b2, h2⟩ := hy
    refine ⟨b1 + b2, ?_⟩
    have : x + y - q.stalkMap t (b1 + b2) =
        (x - q.stalkMap t b1) + (y - q.stalkMap t b2) := by rw [map_add]; ring
    rw [this]; exact I.add_mem h1 h2
  | neg x _ hx =>
    obtain ⟨b1, h1⟩ := hx
    refine ⟨-b1, ?_⟩
    have : -x - q.stalkMap t (-b1) = -(x - q.stalkMap t b1) := by rw [map_neg]; ring
    rw [this]; exact I.neg_mem h1
  | mul x y _ _ hx hy =>
    obtain ⟨b1, h1⟩ := hx
    obtain ⟨b2, h2⟩ := hy
    refine ⟨b1 * b2, ?_⟩
    have : x * y - q.stalkMap t (b1 * b2) =
        (x - q.stalkMap t b1) * y + q.stalkMap t b1 * (y - q.stalkMap t b2) := by
      rw [map_mul]; ring
    rw [this]
    exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)

/-- **Maximal ideal of a stalk generated by two stalks.** If `𝒪_{T,t}` is generated by the stalks
at `x = p t` and `y = q t` (`StalkGen`, e.g. `T = X ×_S Y`) and `x` is rational over `s`, then
`𝔪_t = 𝔪_x 𝒪_t + 𝔪_y 𝒪_t`. -/
theorem maximalIdeal_eq_of_stalkGen (w : p ≫ f = q ≫ g) {t : T} (h : StalkGen p q t)
    (hrat : RationalOver f (p t)) :
    IsLocalRing.maximalIdeal (T.presheaf.stalk t) = stalkIdeal p q t := by
  refine le_antisymm (fun r hr => ?_) (stalkIdeal_le t)
  obtain ⟨c, hc, w', hw', hwu, hrw⟩ := h r
  obtain ⟨b, hb⟩ := exists_sub_mem_stalkIdeal w hrat hc
  have hcm : c ∈ IsLocalRing.maximalIdeal _ := hrw ▸ Ideal.mul_mem_right _ _ hr
  have hqb : q.stalkMap t b ∈ IsLocalRing.maximalIdeal _ := by
    have := Ideal.sub_mem _ hcm (stalkIdeal_le t hb)
    rwa [sub_sub_cancel] at this
  have hbm : b ∈ IsLocalRing.maximalIdeal _ := by
    intro hbu
    exact hqb (hbu.map (q.stalkMap t).hom)
  have hcI : c ∈ stalkIdeal p q t := by
    have := Ideal.add_mem _ hb (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hbm))
    rwa [sub_add_cancel] at this
  obtain ⟨v, rfl⟩ := hwu
  have : r = c * ↑v⁻¹ := by rw [← hrw, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hcI

/-- **Residue field of a stalk generated by two stalks.** Under the hypotheses of
`maximalIdeal_eq_of_stalkGen`, every element of `𝒪_{T,t}` is congruent modulo `𝔪_t` to the image of
an element of `𝒪_{Y,y}`. -/
theorem exists_sub_mem_maximalIdeal_of_stalkGen (w : p ≫ f = q ≫ g) {t : T} (h : StalkGen p q t)
    (hrat : RationalOver f (p t)) (r : T.presheaf.stalk t) :
    ∃ b : Y.presheaf.stalk (q t), r - q.stalkMap t b ∈ IsLocalRing.maximalIdeal _ := by
  obtain ⟨c, hc, w', hw', hwu, hrw⟩ := h r
  obtain ⟨b1, hb1⟩ := exists_sub_mem_stalkIdeal w hrat hc
  obtain ⟨b2, hb2⟩ := exists_sub_mem_stalkIdeal w hrat hw'
  have e1 : IsLocalRing.residue _ c = IsLocalRing.residue _ (q.stalkMap t b1) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact stalkIdeal_le t hb1
  have e2 : IsLocalRing.residue _ w' = IsLocalRing.residue _ (q.stalkMap t b2) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact stalkIdeal_le t hb2
  have hw0 : IsLocalRing.residue _ w' ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hwu
  have hb2u : IsUnit b2 := by
    rw [e2, IsLocalRing.residue_ne_zero_iff_isUnit] at hw0
    exact isUnit_of_map_unit (q.stalkMap t).hom _ hw0
  obtain ⟨v, rfl⟩ := hb2u
  refine ⟨b1 * ↑v⁻¹, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
  apply mul_right_cancel₀ hw0
  rw [← map_mul, hrw, e1, e2, ← map_mul, ← map_mul, mul_assoc, Units.inv_mul, mul_one]

end MaximalIdeal

/-- **A point on a section is rational.** If `e` is a section of `f` (`e ≫ f = 𝟙`), the point
`e s` is rational over `f (e s)`. -/
theorem rationalOver_of_section {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    (s : S) : RationalOver f (e s) := by
  intro a
  have hs : f (e s) = s := by rw [← Scheme.Hom.comp_apply, he]; rfl
  refine ⟨(S.presheaf.stalkCongr (.of_eq hs)).inv (e.stalkMap s a), ?_⟩
  have key : e.stalkMap s (f.stalkMap (e s) ((S.presheaf.stalkCongr (.of_eq hs)).inv
      (e.stalkMap s a))) = e.stalkMap s a := by
    have h3 : ∀ y, (S.presheaf.stalkCongr (.of_eq hs)).hom
        ((S.presheaf.stalkCongr (.of_eq hs)).inv y) = y := fun y => Iso.inv_hom_id_apply _ y
    refine (stalkMap_comp_apply' e f s _).symm.trans ?_
    rw [Scheme.Hom.stalkMap_congr_hom (e ≫ f) (𝟙 S) he s, Scheme.Hom.stalkMap_id]
    exact h3 _
  intro hu
  apply hu.map (e.stalkMap s).hom |> fun h' => ?_
  rw [map_sub, key, sub_self] at h'
  exact not_isUnit_zero h'

/-! ### Sections and points with field stalks -/

theorem StalkGen.symm {T X Y : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y} {t : T}
    (h : StalkGen p q t) : StalkGen q p t := by
  intro r
  obtain ⟨c, hc, w, hw, hu, h'⟩ := h r
  rw [sup_comm] at hc hw
  exact ⟨c, hc, w, hw, hu, h'⟩

/-- A morphism with a retraction is rational at every point (it is surjective on stalks). -/
theorem rationalOver_of_retraction {X S : Scheme.{u}} (f : X ⟶ S) (r : S ⟶ X)
    (hr : f ≫ r = 𝟙 X) (x : X) : RationalOver f x := by
  intro a
  have hx : r (f x) = x := by rw [← Scheme.Hom.comp_apply, hr]; rfl
  refine ⟨r.stalkMap (f x) ((X.presheaf.stalkCongr (.of_eq hx)).inv a), ?_⟩
  have key : f.stalkMap x (r.stalkMap (f x) ((X.presheaf.stalkCongr (.of_eq hx)).inv a)) = a := by
    have h3 : ∀ y, (X.presheaf.stalkCongr (.of_eq hx)).hom
        ((X.presheaf.stalkCongr (.of_eq hx)).inv y) = y := fun y => Iso.inv_hom_id_apply _ y
    refine (stalkMap_comp_apply' f r x _).symm.trans ?_
    rw [Scheme.Hom.stalkMap_congr_hom (f ≫ r) (𝟙 X) hr x, Scheme.Hom.stalkMap_id]
    exact h3 _
  rw [key, sub_self]
  exact Ideal.zero_mem _

/-- The stalks of the spectrum of a field are fields. -/
theorem maximalIdeal_stalk_spec_field (k : Type u) [Field k] (x : Spec (CommRingCat.of k)) :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of k)).presheaf.stalk x) = ⊥ := by
  have h : x = genericPoint (Spec (CommRingCat.of k)) := Subsingleton.elim _ _
  rw [← IsLocalRing.isField_iff_maximalIdeal_eq, h]
  exact Field.toIsField (Spec (CommRingCat.of k)).functionField

theorem mem_maximalIdeal_of_iso {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (φ : R ≅ S) {a : R} (ha : a ∈ IsLocalRing.maximalIdeal R) :
    φ.hom a ∈ IsLocalRing.maximalIdeal S := by
  intro hu
  apply ha
  have := hu.map φ.inv.hom
  rwa [Iso.hom_inv_id_apply] at this

/-- In a commutative square `p ≫ f = q ≫ g`, if the stalk of `Y` at `q t` is a field, the
composite `𝒪_{S, f(p t)} → 𝒪_{X, p t} → 𝒪_{T, t}` kills the maximal ideal. -/
theorem stalkMap_comp_eq_zero_of_maximalIdeal_eq_bot {T X Y S : Scheme.{u}} (p : T ⟶ X)
    (q : T ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (w : p ≫ f = q ≫ g) (t : T)
    (hY : IsLocalRing.maximalIdeal (Y.presheaf.stalk (q t)) = ⊥)
    (c : S.presheaf.stalk (f (p t))) (hc : c ∈ IsLocalRing.maximalIdeal _) :
    p.stalkMap t (f.stalkMap (p t) c) = 0 := by
  have hpt : (p ≫ f) t = (q ≫ g) t := by rw [w]
  have e : p.stalkMap t (f.stalkMap (p t) c) =
      q.stalkMap t (g.stalkMap (q t) ((S.presheaf.stalkCongr (.of_eq hpt)).hom c)) := by
    calc p.stalkMap t (f.stalkMap (p t) c) = (p ≫ f).stalkMap t c :=
          (stalkMap_comp_apply' p f t c).symm
      _ = (q ≫ g).stalkMap t ((S.presheaf.stalkCongr (.of_eq hpt)).hom c) := by
          rw [Scheme.Hom.stalkMap_congr_hom (p ≫ f) (q ≫ g) w t]; rfl
      _ = _ := stalkMap_comp_apply' q g t _
  have hc' := mem_maximalIdeal_of_iso (S.presheaf.stalkCongr (.of_eq hpt)) hc
  have h0 : g.stalkMap (q t) ((S.presheaf.stalkCongr (.of_eq hpt)).hom c) ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (q t)) := map_nonunit _ _ hc'
  rw [hY, Ideal.mem_bot] at h0
  rw [e, h0, map_zero]

/-- **A section through a point with field stalk is an open immersion.** Let `q : P ⟶ Spec k` be
locally of finite type over a field `k` and `u` a section of `q`. If the stalk of `P` at the
point `u pt` is a field, then `u` is an open immersion. -/
theorem isOpenImmersion_of_section_of_maximalIdeal_eq_bot {k : Type u} [Field k] {P : Scheme.{u}}
    (q : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] (u : Spec (CommRingCat.of k) ⟶ P)
    (hu : u ≫ q = 𝟙 _) (pt : Spec (CommRingCat.of k))
    (hm : IsLocalRing.maximalIdeal (P.presheaf.stalk (u pt)) = ⊥) : IsOpenImmersion u := by
  have hcl : IsClosedImmersion u := isClosedImmersion_of_comp_eq_id q u hu
  have hF : IsField (P.presheaf.stalk (u pt)) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
  have hinj : Function.Injective (u.stalkMap pt).hom := by
    letI := hF.toField
    exact RingHom.injective _
  have hsurj : Function.Surjective (u.stalkMap pt).hom := u.stalkMap_surjective pt
  have hqs : Function.Surjective (q.stalkMap (u pt)).hom := by
    intro y
    have hpt : (u ≫ q) pt = (𝟙 (Spec (CommRingCat.of k))) pt := by rw [hu]
    let c := ((Spec (CommRingCat.of k)).presheaf.stalkCongr (.of_eq hpt)).inv (u.stalkMap pt y)
    have hc : (u ≫ q).stalkMap pt c = u.stalkMap pt y := by
      rw [Scheme.Hom.stalkMap_congr_hom (u ≫ q) (𝟙 _) hu pt, Scheme.Hom.stalkMap_id]
      exact Iso.inv_hom_id_apply ((Spec (CommRingCat.of k)).presheaf.stalkCongr (.of_eq hpt))
        (u.stalkMap pt y)
    refine ⟨c, hinj ?_⟩
    rw [← hc]
    exact (stalkMap_comp_apply' u q pt c).symm
  have hqf : q.QuasiFiniteAt (u pt) :=
    RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ hqs)
  have h1 : IsOpen {q.asFiber (u pt)} := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hqf
  have h2 : IsOpen ((q.fiberHomeo (q (u pt))) '' {q.asFiber (u pt)}) :=
    (q.fiberHomeo _).isOpenMap _ h1
  rw [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply] at h2
  have hopen : IsOpen (q.base ⁻¹' {q (u pt)}) := by
    convert isOpen_univ
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h3 : IsOpen ({u pt} : Set P) := by
    have := hopen.isOpenMap_subtype_val _ h2
    simpa using this
  have hrange : Set.range u = {u pt} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [Subsingleton.elim x pt]
      rfl
    · rintro rfl
      exact ⟨pt, rfl⟩
  have hemb : Topology.IsOpenEmbedding u :=
    ⟨u.isClosedEmbedding.isEmbedding, by rw [hrange]; exact h3⟩
  haveI : ∀ x, IsIso (u.stalkMap x) := by
    intro x
    obtain rfl : x = pt := Subsingleton.elim x pt
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  exact IsOpenImmersion.of_isIso_stalkMap u hemb

theorem stalkMap_congr_point_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X} (h : x = x')
    (z : Y.presheaf.stalk (f x)) :
    (X.presheaf.stalkCongr (.of_eq h)).hom (f.stalkMap x z) =
      f.stalkMap x' ((Y.presheaf.stalkCongr (.of_eq (congrArg f h))).hom z) :=
  ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_congr_point f x x' h) z

/-! ### Stalk maps between given points -/

/-- The stalk map of `f` from `y` to `x`, for `f x = y`. -/
noncomputable def Scheme.Hom.stalkMapAt {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) : Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  (Y.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ f.stalkMap x

instance {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    IsLocalHom (f.stalkMapAt h).hom := by
  unfold Scheme.Hom.stalkMapAt
  rw [CommRingCat.hom_comp]
  infer_instance

theorem Scheme.Hom.stalkMapAt_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.stalkMapAt (rfl : f x = f x) = f.stalkMap x := by
  unfold Scheme.Hom.stalkMapAt
  have : (Y.presheaf.stalkCongr (.of_eq (rfl : f x = f x).symm)).hom = 𝟙 _ :=
    Y.presheaf.stalkSpecializes_refl _
  rw [this, Category.id_comp]

theorem Scheme.Hom.stalkMapAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} {y : Y}
    {z : Z} (hf : f x = y) (hg : g y = z) (hfg : (f ≫ g) x = z) :
    (f ≫ g).stalkMapAt hfg = g.stalkMapAt hg ≫ f.stalkMapAt hf := by
  subst hf hg
  rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.stalkMapAt_rfl]
  unfold Scheme.Hom.stalkMapAt
  have : (Z.presheaf.stalkCongr (.of_eq hfg.symm)).hom = 𝟙 _ :=
    Z.presheaf.stalkSpecializes_refl _
  rw [this]
  exact (Category.id_comp _).trans (Scheme.Hom.stalkMap_comp f g x)

theorem Scheme.Hom.stalkMapAt_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) {x : X} {y : Y}
    (hf : f x = y) (hg : g x = y) : f.stalkMapAt hf = g.stalkMapAt hg := by
  subst e; rfl

theorem Scheme.Hom.stalkMapAt_id {X : Scheme.{u}} (x : X) (h : (𝟙 X) x = x) :
    Scheme.Hom.stalkMapAt (𝟙 X) h = 𝟙 _ := by
  unfold Scheme.Hom.stalkMapAt
  rw [Scheme.Hom.stalkMap_id]
  exact (Category.comp_id _).trans (X.presheaf.stalkSpecializes_refl _)

theorem Scheme.Hom.map_stalkMapAt_maximalIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) :
    Ideal.map (f.stalkMapAt h).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) =
      Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) := by
  subst h; rw [Scheme.Hom.stalkMapAt_rfl]

theorem Scheme.Hom.exists_stalkMapAt_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) (b : Y.presheaf.stalk (f x)) :
    ∃ c : Y.presheaf.stalk y, f.stalkMapAt h c = f.stalkMap x b := by
  subst h; exact ⟨b, by rw [Scheme.Hom.stalkMapAt_rfl]⟩

end AlgebraicGeometry



/-! # Local structure of a fibre product at points with values in a field

For `f : X ⟶ Spec R`, `g : Y ⟶ Spec R` and points `p₁ : Spec F ⟶ X`, `p₂ : Spec F ⟶ Y` over
`Spec R` (`F` a field), a regular function on an open of `X ×_R Y` (pulled back along any
`W : X ×_R Y ⟶ P`) is, near `(p₁, p₂)`, a quotient of sums of products of regular functions on
opens `V₁ ∋ p₁`, `V₂ ∋ p₂`, uniformly for all `F`-points of `V₁ × V₂` where the denominator does
not vanish (`exists_localStructure_pullback`). Proof: affine charts `Spec A → X`, `Spec B → Y`,
the open chart `Spec (A ⊗[R] B) → X ×_R Y`, a basic open `D(h)` around the point inside the open,
`s = a / h^n` on `D(h)`, and pure tensors evaluate to products. -/

namespace AlgebraicGeometry

open CategoryTheory Limits TensorProduct

/-- The value `s(p) ∈ F` of a section at an `F`-point (and `0` if `p ∉ V`); the same formula as
`GroupModel.evalAt`. -/
noncomputable def evalPt {F : Type u} [Field F] {X : Scheme.{u}}
    (p : Spec (CommRingCat.of F) ⟶ X) (V : X.Opens) (s : Γ(X, V)) : F := by
  classical
  exact if h : ⊤ ≤ p ⁻¹ᵁ V then (Scheme.ΓSpecIso (CommRingCat.of F)).hom (p.appLE V ⊤ h s) else 0

/-- The section on `j(Spec A)` corresponding to `α ∈ A`, for an open immersion `j`. -/
noncomputable def secOf {X : Scheme.{u}} {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
    (α : A) : Γ(X, j ''ᵁ ⊤) :=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv α)

theorem appLE_secOf {X : Scheme.{u}} {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
    (α : A) (e : ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤)) :
    j.appLE (j ''ᵁ ⊤) ⊤ e (secOf j α) = (Scheme.ΓSpecIso A).inv α := by
  unfold secOf
  rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  have : (homOfLE (by rwa [Scheme.Hom.preimage_image_eq] at e) :
      (⊤ : (Spec A).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem ΓSpecIso_hom_appLE_top {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (e : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤) (x : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso S).hom ((Spec.map φ).appLE ⊤ ⊤ e x) = φ ((Scheme.ΓSpecIso R).hom x) := by
  have h : (Spec.map φ).appLE ⊤ ⊤ e = (Spec.map φ).appTop :=
    (Scheme.Hom.app_eq_appLE (f := Spec.map φ) (U := ⊤)).symm
  rw [h, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

theorem evalPt_secOf {F : Type u} [Field F] {X : Scheme.{u}} {A : CommRingCat.{u}}
    (j : Spec A ⟶ X) [IsOpenImmersion j] (χ : A ⟶ CommRingCat.of F) (α : A) :
    evalPt (Spec.map χ ≫ j) (j ''ᵁ ⊤) (secOf j α) = χ α := by
  have hle : ⊤ ≤ (Spec.map χ ≫ j) ⁻¹ᵁ (j ''ᵁ ⊤) := by
    intro x _
    exact ⟨Spec.map χ x, trivial, rfl⟩
  unfold evalPt
  rw [dif_pos hle, ← Scheme.Hom.appLE_comp_appLE (Spec.map χ) j (j ''ᵁ ⊤) ⊤ ⊤
    (Scheme.Hom.preimage_image_eq j ⊤).ge (fun _ _ => trivial), CommRingCat.comp_apply,
    appLE_secOf]
  exact (ΓSpecIso_hom_appLE_top χ _ _).trans (by rw [Iso.inv_hom_id_apply])

/-- Every element of `A ⊗[R] B` is a finite sum of pure tensors. -/
theorem exists_fin_sum_tmul {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (x : A ⊗[R] B) :
    ∃ (n : ℕ) (a : Fin n → A) (b : Fin n → B), x = ∑ k, a k ⊗ₜ[R] b k := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ => a, fun _ => b, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, a, b, rfl⟩ := hx
    obtain ⟨m, a', b', rfl⟩ := hy
    refine ⟨n + m, Fin.append a a', Fin.append b b', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

/-- Two finite families of pure tensors with a common index type. -/
theorem exists_fin_sum_tmul₂ {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (x y : A ⊗[R] B) :
    ∃ (n : ℕ) (a c : Fin n → A) (b d : Fin n → B),
      x = ∑ k, a k ⊗ₜ[R] b k ∧ y = ∑ k, c k ⊗ₜ[R] d k := by
  obtain ⟨n, a, b, rfl⟩ := exists_fin_sum_tmul x
  obtain ⟨m, c, d, rfl⟩ := exists_fin_sum_tmul y
  refine ⟨n + m, Fin.append a 0, Fin.append 0 c, Fin.append b 0, Fin.append 0 d, ?_, ?_⟩
  · rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

/-- An `F`-point lies in the basic open `D(h)` of `Spec T` iff `h` does not vanish at it. -/
theorem SpecMap_mem_basicOpen_iff {F : Type u} [Field F] {T : CommRingCat.{u}}
    (χ : T ⟶ CommRingCat.of F) (h : Γ(Spec T, ⊤)) (x : Spec (CommRingCat.of F)) :
    Spec.map χ x ∈ (Spec T).basicOpen h ↔ χ ((Scheme.ΓSpecIso T).hom h) ≠ 0 := by
  rw [basicOpen_eq_of_affine']
  change x ∈ Spec.map χ ⁻¹ᵁ PrimeSpectrum.basicOpen _ ↔ _
  rw [SpecMap_preimage_basicOpen]
  change χ ((Scheme.ΓSpecIso T).hom h) ∉ x.asIdeal ↔ _
  have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime
  rw [hx, Ideal.mem_bot]

/-- **Points of the product chart.** If `F`-points `p₁'`, `p₂'` lie in the charts `jU`, `jW`,
then `(p₁', p₂')` factors through `Spec (A ⊗[R] B)` via a ring map `χ` with `χ (α ⊗ 1) = p₁'(α)`
and `χ (1 ⊗ β) = p₂'(β)`. -/
theorem exists_chart_point {F : Type u} [Field F] {R A B : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Y ⟶ Spec R) (jU : Spec A ⟶ X) [IsOpenImmersion jU] (jW : Spec B ⟶ Y)
    [IsOpenImmersion jW] (φ : R ⟶ A) (ψ : R ⟶ B) (eU : Spec.map φ = jU ≫ f)
    (eW : Spec.map ψ = jW ≫ g)
    (p₁' : Spec (CommRingCat.of F) ⟶ X) (p₂' : Spec (CommRingCat.of F) ⟶ Y)
    (hp' : p₁' ≫ f = p₂' ≫ g) (h1' : ⊤ ≤ p₁' ⁻¹ᵁ (jU ''ᵁ ⊤)) (h2' : ⊤ ≤ p₂' ⁻¹ᵁ (jW ''ᵁ ⊤)) :
    letI : Algebra R A := φ.hom.toAlgebra
    letI : Algebra R B := ψ.hom.toAlgebra
    ∃ χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F,
      p₁' = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          A →+* A ⊗[R] B) ≫ χ) ≫ jU ∧
      p₂' = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          B →ₐ[R] A ⊗[R] B).toRingHom ≫ χ) ≫ jW := by
  letI : Algebra R A := φ.hom.toAlgebra
  letI : Algebra R B := ψ.hom.toAlgebra
  have hr1 : Set.range p₁' ⊆ Set.range jU := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, -, hy⟩ := h1' (Set.mem_univ x)
    exact ⟨y, hy⟩
  have hr2 : Set.range p₂' ⊆ Set.range jW := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, -, hy⟩ := h2' (Set.mem_univ x)
    exact ⟨y, hy⟩
  set l₁ := IsOpenImmersion.lift jU p₁' hr1
  set l₂ := IsOpenImmersion.lift jW p₂' hr2
  have hl₁ : l₁ ≫ jU = p₁' := IsOpenImmersion.lift_fac _ _ _
  have hl₂ : l₂ ≫ jW = p₂' := IsOpenImmersion.lift_fac _ _ _
  set χ₁ := Spec.preimage l₁
  set χ₂ := Spec.preimage l₂
  have hχ₁ : Spec.map χ₁ = l₁ := Spec.map_preimage _
  have hχ₂ : Spec.map χ₂ = l₂ := Spec.map_preimage _
  have hcompat : φ ≫ χ₁ = ψ ≫ χ₂ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hχ₁, hχ₂, eU, eW, ← Category.assoc, ← Category.assoc, hl₁,
      hl₂, hp']
  letI : Algebra R F := (φ ≫ χ₁).hom.toAlgebra
  let χ1a : A →ₐ[R] F := { χ₁.hom with commutes' := fun r => rfl }
  let χ2a : B →ₐ[R] F :=
    { χ₂.hom with
      commutes' := fun r => (congrArg (fun k : R ⟶ CommRingCat.of F => k.hom r) hcompat).symm }
  have hfg : ∀ x y, Commute (χ1a x) (χ2a y) := fun x y => Commute.all _ _
  let χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F :=
    CommRingCat.ofHom (Algebra.TensorProduct.lift χ1a χ2a hfg).toRingHom
  refine ⟨χ, ?_, ?_⟩
  · have : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) ≫ χ =
        χ₁ := by
      ext a
      change Algebra.TensorProduct.lift χ1a χ2a hfg (a ⊗ₜ[R] 1) = χ₁ a
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    rw [this, hχ₁, hl₁]
  · have : CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] A ⊗[R] B).toRingHom ≫ χ = χ₂ := by
      ext b
      change Algebra.TensorProduct.lift χ1a χ2a hfg ((1 : A) ⊗ₜ[R] b) = χ₂ b
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    rw [this, hχ₂, hl₂]

/-- **Local structure of a fibre product at `F`-points.** See the module docstring. -/
theorem exists_localStructure_pullback {F : Type u} [Field F] {R : CommRingCat.{u}}
    {X Y P : Scheme.{u}} (f : X ⟶ Spec R) (g : Y ⟶ Spec R) (W : pullback f g ⟶ P)
    (U : P.Opens) (s : Γ(P, U)) (p₁ : Spec (CommRingCat.of F) ⟶ X)
    (p₂ : Spec (CommRingCat.of F) ⟶ Y) (hp : p₁ ≫ f = p₂ ≫ g)
    (hU : ⊤ ≤ (pullback.lift p₁ p₂ hp ≫ W) ⁻¹ᵁ U) :
    ∃ (V₁ : X.Opens) (V₂ : Y.Opens) (n : ℕ) (a c : Fin n → Γ(X, V₁)) (b d : Fin n → Γ(Y, V₂)),
      ⊤ ≤ p₁ ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂ ⁻¹ᵁ V₂ ∧
      (∑ k, evalPt p₁ V₁ (c k) * evalPt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : Spec (CommRingCat.of F) ⟶ X) (p₂' : Spec (CommRingCat.of F) ⟶ Y)
        (hp' : p₁' ≫ f = p₂' ≫ g), ⊤ ≤ p₁' ⁻¹ᵁ V₁ → ⊤ ≤ p₂' ⁻¹ᵁ V₂ →
        (∑ k, evalPt p₁' V₁ (c k) * evalPt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (pullback.lift p₁' p₂' hp' ≫ W) ⁻¹ᵁ U ∧
        evalPt (pullback.lift p₁' p₂' hp' ≫ W) U s *
            (∑ k, evalPt p₁' V₁ (c k) * evalPt p₂' V₂ (d k)) =
          ∑ k, evalPt p₁' V₁ (a k) * evalPt p₂' V₂ (b k) := by
  classical
  let pt : Spec (CommRingCat.of F) := default
  have hall : ∀ x : Spec (CommRingCat.of F), x = pt := fun x => Subsingleton.elim _ _
  obtain ⟨A, jU, _, φ, hxU, eU⟩ := exists_affine_chart_over f (𝟙 (Spec R)) (p₁ pt) ⟨_, rfl⟩
  obtain ⟨B, jW, _, ψ, hyW, eW⟩ := exists_affine_chart_over g (𝟙 (Spec R)) (p₂ pt) ⟨_, rfl⟩
  have eU' : Spec.map φ = jU ≫ f := by rw [← eU, Category.comp_id]
  have eW' : Spec.map ψ = jW ≫ g := by rw [← eW, Category.comp_id]
  letI : Algebra R A := φ.hom.toAlgebra
  letI : Algebra R B := ψ.hom.toAlgebra
  let m := pullback.map (Spec.map φ) (Spec.map ψ) f g jU jW (𝟙 _) eU eW
  let e := pullbackSpecIso R A B
  let m' : Spec (CommRingCat.of (TensorProduct R A B)) ⟶ pullback f g := e.inv ≫ m
  have h1 : m' ≫ pullback.fst f g = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A B)) ≫ jU := by
    simp only [m', m, e, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc]
    exact congrArg (· ≫ jU) (pullbackSpecIso_inv_fst R A B)
  have h2 : m' ≫ pullback.snd f g = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R A B).toRingHom) ≫ jW := by
    simp only [m', m, e, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc]
    exact congrArg (· ≫ jW) (pullbackSpecIso_inv_snd R A B)
  have hmi : IsOpenImmersion m' := by infer_instance
  -- the chart point of `(p₁', p₂')`
  have hlift : ∀ (p₁' : Spec (CommRingCat.of F) ⟶ X) (p₂' : Spec (CommRingCat.of F) ⟶ Y)
      (hp' : p₁' ≫ f = p₂' ≫ g), ⊤ ≤ p₁' ⁻¹ᵁ (jU ''ᵁ ⊤) → ⊤ ≤ p₂' ⁻¹ᵁ (jW ''ᵁ ⊤) →
      ∃ χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F,
        pullback.lift p₁' p₂' hp' = Spec.map χ ≫ m' ∧
        (∀ α, evalPt p₁' (jU ''ᵁ ⊤) (secOf jU α) = χ (α ⊗ₜ[R] 1)) ∧
        (∀ β, evalPt p₂' (jW ''ᵁ ⊤) (secOf jW β) = χ ((1 : A) ⊗ₜ[R] β)) := by
    intro p₁' p₂' hp' h1' h2'
    obtain ⟨χ, e1, e2⟩ := exists_chart_point f g jU jW φ ψ eU' eW' p₁' p₂' hp' h1' h2'
    refine ⟨χ, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, e1]
      · rw [pullback.lift_snd, Category.assoc, h2, ← Category.assoc, ← Spec.map_comp, e2]
    · intro α
      rw [e1, evalPt_secOf]
      rfl
    · intro β
      rw [e2, evalPt_secOf]
      rfl
  -- the open, the basic open and the fraction
  let q := pullback.lift p₁ p₂ hp
  have hz : q pt ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ?_⟩
    · show pullback.fst f g (q pt) ∈ Set.range jU
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]; exact hxU
    · show pullback.snd f g (q pt) ∈ Set.range jW
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd]; exact hyW
  obtain ⟨t0', ht0'⟩ := hz
  let t0 := e.hom t0'
  have hmt0 : m' t0 = q pt := by
    have he : e.inv (e.hom t0') = t0' := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    simp only [m', t0]
    rw [Scheme.Hom.comp_apply, he, ht0']
  let U' : (Spec (CommRingCat.of (A ⊗[R] B))).Opens := (m' ≫ W) ⁻¹ᵁ U
  have ht0 : t0 ∈ U' := by
    show (m' ≫ W) t0 ∈ U
    rw [Scheme.Hom.comp_apply, hmt0, ← Scheme.Hom.comp_apply]
    exact hU (Set.mem_univ pt)
  obtain ⟨h, hDU, ht0D⟩ := (isAffineOpen_top (Spec (CommRingCat.of (A ⊗[R] B)))).exists_basicOpen_le
    (⟨t0, ht0⟩ : U') (Set.mem_univ _)
  let s' := (m' ≫ W).appLE U _ hDU s
  haveI := (isAffineOpen_top (Spec (CommRingCat.of (A ⊗[R] B)))).isLocalization_basicOpen h
  obtain ⟨k0, a0, hs'⟩ := IsLocalization.Away.surj h s'
  let h0 := (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom h
  let a0' := (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom a0
  obtain ⟨n, a, c, b, d, hN, hH⟩ := exists_fin_sum_tmul₂ (a0' * h0) (h0 ^ (k0 + 1))
  -- evaluation of the sums
  have hsum : ∀ (p₁' : Spec (CommRingCat.of F) ⟶ X) (p₂' : Spec (CommRingCat.of F) ⟶ Y)
      (χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F),
      (∀ α, evalPt p₁' (jU ''ᵁ ⊤) (secOf jU α) = χ (α ⊗ₜ[R] 1)) →
      (∀ β, evalPt p₂' (jW ''ᵁ ⊤) (secOf jW β) = χ ((1 : A) ⊗ₜ[R] β)) →
      (∑ k, evalPt p₁' (jU ''ᵁ ⊤) (secOf jU (c k)) * evalPt p₂' (jW ''ᵁ ⊤) (secOf jW (d k)) =
        χ (h0 ^ (k0 + 1))) ∧
      (∑ k, evalPt p₁' (jU ''ᵁ ⊤) (secOf jU (a k)) * evalPt p₂' (jW ''ᵁ ⊤) (secOf jW (b k)) =
        χ (a0' * h0)) := by
    intro p₁' p₂' χ e1 e2
    constructor
    · rw [hH, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [e1, e2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · rw [hN, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [e1, e2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  -- evaluation of `s` at a chart point in `D(h)`
  have hval : ∀ χ : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of F, χ h0 ≠ 0 →
      ⊤ ≤ (Spec.map χ ≫ m' ≫ W) ⁻¹ᵁ U ∧
      evalPt (Spec.map χ ≫ m' ≫ W) U s * χ (h0 ^ (k0 + 1)) = χ (a0' * h0) := by
    intro χ hχ
    have hD : ⊤ ≤ Spec.map χ ⁻¹ᵁ (Spec (CommRingCat.of (A ⊗[R] B))).basicOpen h := by
      intro x _
      exact (SpecMap_mem_basicOpen_iff χ h x).mpr hχ
    have hT : ⊤ ≤ (Spec.map χ ≫ m' ≫ W) ⁻¹ᵁ U := fun x hx => hDU (hD hx)
    refine ⟨hT, ?_⟩
    unfold evalPt
    rw [dif_pos hT]
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map χ) (m' ≫ W) U _ ⊤ hDU hD]
    let ev : Γ(Spec (CommRingCat.of (A ⊗[R] B)), (Spec (CommRingCat.of (A ⊗[R] B))).basicOpen h)
        →+* F := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp
        ((Spec.map χ).appLE _ ⊤ hD).hom
    have hev : ∀ x : Γ(Spec (CommRingCat.of (A ⊗[R] B)), ⊤),
        ev (algebraMap _ _ x) = χ ((Scheme.ΓSpecIso _).hom x) := by
      intro x
      change (Scheme.ΓSpecIso (CommRingCat.of F)).hom (((Spec (CommRingCat.of (A ⊗[R] B))).presheaf.map
        (homOfLE ((Spec (CommRingCat.of (A ⊗[R] B))).basicOpen_le h)).op ≫
          (Spec.map χ).appLE _ ⊤ hD) x) = _
      rw [Scheme.Hom.map_appLE]
      exact ΓSpecIso_hom_appLE_top χ _ x
    have key := congrArg ev hs'
    rw [map_mul, map_pow, hev, hev] at key
    change ev s' * χ (h0 ^ (k0 + 1)) = χ (a0' * h0)
    rw [map_pow, pow_succ, ← mul_assoc, key, map_mul]
  refine ⟨jU ''ᵁ ⊤, jW ''ᵁ ⊤, n, fun k => secOf jU (a k), fun k => secOf jU (c k),
    fun k => secOf jW (b k), fun k => secOf jW (d k), ?_, ?_, ?_, ?_⟩
  · intro x _
    rw [hall x]
    obtain ⟨y, hy⟩ := hxU
    exact ⟨y, trivial, hy⟩
  · intro x _
    rw [hall x]
    obtain ⟨y, hy⟩ := hyW
    exact ⟨y, trivial, hy⟩
  · have h1p : ⊤ ≤ p₁ ⁻¹ᵁ (jU ''ᵁ ⊤) := by
      intro x _; rw [hall x]; obtain ⟨y, hy⟩ := hxU; exact ⟨y, trivial, hy⟩
    have h2p : ⊤ ≤ p₂ ⁻¹ᵁ (jW ''ᵁ ⊤) := by
      intro x _; rw [hall x]; obtain ⟨y, hy⟩ := hyW; exact ⟨y, trivial, hy⟩
    obtain ⟨χ, hq, e1, e2⟩ := hlift p₁ p₂ hp h1p h2p
    rw [(hsum p₁ p₂ χ e1 e2).1, map_pow]
    refine pow_ne_zero _ ?_
    rw [← SpecMap_mem_basicOpen_iff χ h pt]
    have : Spec.map χ pt = t0 := by
      apply m'.isOpenEmbedding.injective
      rw [hmt0, ← Scheme.Hom.comp_apply, ← hq]
    rw [this]
    exact ht0D
  · intro p₁' p₂' hp' h1' h2' hne
    obtain ⟨χ, hq, e1, e2⟩ := hlift p₁' p₂' hp' h1' h2'
    obtain ⟨hs1, hs2⟩ := hsum p₁' p₂' χ e1 e2
    rw [hs1] at hne ⊢
    rw [hs2]
    have hχ : χ h0 ≠ 0 := by
      intro h0z
      apply hne
      rw [map_pow, h0z, zero_pow (Nat.succ_ne_zero _)]
    obtain ⟨hT, hv⟩ := hval χ hχ
    rw [hq, Category.assoc]
    exact ⟨hT, hv⟩

end AlgebraicGeometry





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
  `uniformizationLift_of`, `jacobianSemilinear_of`, and the glue statement `GermDerivation`
  itself (`germDerivation`, from the section `GermDer`: germs along `Φ` form a ring
  homomorphism near `0`, germs in `𝔪_ξ` vanish at the unit point, structure sections take the
  value `τ(r)`).
  **Main results** (final form): `modelHeightBaseChange_of_glue4` and
  `hodgeLineBaseChange_of_glue4` (H4a and `HodgeLineBaseChange`, verbatim, from the four glue
  statements `HodgeBCInjective`, `CotangentSpanBC`, `OmegaBaseChange`,
  `UniformizationLiftAnalytic`), and `modelHeightBaseChangeGE_of_main` (the descent half from
  `HodgeBCInjective` and `OmegaBaseChange`). Coarser forms: `_of_final`, `_of_glue5`,
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


/-! ### The differential at the origin along `Φ` (proves `GermDerivation`) -/

section GermDer

variable {K : Type} [Field K] {A : AbVar K}

variable {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)

/-- Values at a point of `V(ℂ)` are additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (r₁ r₂ : Γ(𝒢.G.left, V)) : 𝒢.evalAt p V (r₁ + r₂) = 𝒢.evalAt p V r₁ + 𝒢.evalAt p V r₂ := by
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp, dif_pos hp, map_add]
  exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _

/-- Values at a point of `V(ℂ)` are multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (r₁ r₂ : Γ(𝒢.G.left, V)) : 𝒢.evalAt p V (r₁ * r₂) = 𝒢.evalAt p V r₁ * 𝒢.evalAt p V r₂ := by
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp, dif_pos hp, map_mul]
  exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _

variable {𝒢}

/-- **Any representative computes the germ along `Φ` near `0`.** -/
theorem germAlong_eventuallyEq_rep {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (V : 𝒢.G.left.Opens) (mV : 𝒢.genericUnit ∈ V) (r : Γ(𝒢.G.left, V))
    (ht : 𝒢.G.left.presheaf.germ V 𝒢.genericUnit mV r = t) :
    𝒢.germAlong Φ t =ᶠ[nhds 0] fun z => 𝒢.evalAt (Φ z) V r := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒢.exists_rep t).choose
  set m := (𝒢.exists_rep t).choose_spec.choose
  set s := (𝒢.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  have heq : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ V 𝒢.genericUnit mV r := by rw [hs, ht]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ m mV _ _ heq
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  filter_upwards [hnhds] with z hz
  show 𝒢.evalAt (Φ z) U s = 𝒢.evalAt (Φ z) V r
  rw [evalAt_res 𝒢 (Φ z) iU hz, hW, ← evalAt_res 𝒢 (Φ z) iV hz]

/-- The germ along `Φ` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨V, mV, r, hr⟩ := 𝒢.exists_rep t
  have hev := germAlong_eventuallyEq_rep hΦ t V mV r hr
  obtain ⟨hmul, -, -, hopen, hdiff⟩ := hΦ
  have h0 : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V := by
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ V
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mV
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V r) 0 :=
    (hdiff V r).differentiableAt ((hopen V).mem_nhds h0)
  exact hev.differentiableAt_iff.mpr hd

/-- **Eventual additivity and multiplicativity of germs along `Φ`.** -/
theorem germAlong_add_mul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    (𝒢.germAlong Φ (t₁ + t₂) =ᶠ[nhds 0] fun z => 𝒢.germAlong Φ t₁ z + 𝒢.germAlong Φ t₂ z) ∧
      (𝒢.germAlong Φ (t₁ * t₂) =ᶠ[nhds 0] fun z => 𝒢.germAlong Φ t₁ z * 𝒢.germAlong Φ t₂ z) := by
  obtain ⟨V₁, m₁, r₁, h₁⟩ := 𝒢.exists_rep t₁
  obtain ⟨V₂, m₂, r₂, h₂⟩ := 𝒢.exists_rep t₂
  have e₁ := germAlong_eventuallyEq_rep hΦ t₁ V₁ m₁ r₁ h₁
  have e₂ := germAlong_eventuallyEq_rep hΦ t₂ V₂ m₂ r₂ h₂
  set W := V₁ ⊓ V₂
  have mW : 𝒢.genericUnit ∈ W := ⟨m₁, m₂⟩
  let i₁ : W ⟶ V₁ := homOfLE inf_le_left
  let i₂ : W ⟶ V₂ := homOfLE inf_le_right
  let ρ₁ := 𝒢.G.left.presheaf.map i₁.op r₁
  let ρ₂ := 𝒢.G.left.presheaf.map i₂.op r₂
  have g₁ : 𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW ρ₁ = t₁ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact h₁
  have g₂ : 𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW ρ₂ = t₂ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact h₂
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  constructor
  · have eS := germAlong_eventuallyEq_rep hΦ (t₁ + t₂) W mW (ρ₁ + ρ₂)
      (by rw [map_add, g₁, g₂])
    filter_upwards [eS, e₁, e₂, hnhds] with z hS hz₁ hz₂ hz
    rw [hS, hz₁, hz₂, evalAt_add 𝒢 (Φ z) W hz, evalAt_res 𝒢 (Φ z) i₁ hz r₁,
      evalAt_res 𝒢 (Φ z) i₂ hz r₂]
  · have eP := germAlong_eventuallyEq_rep hΦ (t₁ * t₂) W mW (ρ₁ * ρ₂)
      (by rw [map_mul, g₁, g₂])
    filter_upwards [eP, e₁, e₂, hnhds] with z hP hz₁ hz₂ hz
    rw [hP, hz₁, hz₂, evalAt_mul 𝒢 (Φ z) W hz, evalAt_res 𝒢 (Φ z) i₁ hz r₁,
      evalAt_res 𝒢 (Φ z) i₂ hz r₂]

/-- `appLE ⊤ ⊤` is `appTop`. -/
theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (U := ⊤) f

/-- **Structure sections take the value `τ(r)` at every complex point.** -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (r : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) =
      τ (algebraMap (𝓞 L) L r) := by
  unfold GroupModel.evalAt
  have h : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  rw [dif_pos h, appLE_top_top, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have hw : p.left ≫ 𝒢.G.hom = Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))) :=
    Over.w p
  rw [hw]
  have hN := congrArg (fun φ => (ConcreteCategory.hom φ)
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  refine hN.trans ?_
  erw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- **Germs in `𝔪_ξ` vanish at the unit complex point.** -/
theorem evalAt_one_eq_zero (τ : L →+* ℂ) (U : 𝒢.G.left.Opens) (hU : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hU s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  unfold GroupModel.evalAt
  have h : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U := one_mem_dom 𝒢 τ hU
  rw [dif_pos h]
  have h1 : (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := rfl
  have hgen : genericPt L ∈ 𝒢.unitSection ⁻¹ᵁ U := hU
  have hz : 𝒢.unitSection.app U s = 0 := by
    apply germ_injective_of_isIntegral _ (genericPt L) hgen
    rw [map_zero]
    refine (Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U (genericPt L) hgen s).symm.trans ?_
    have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
      have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
        (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
      rw [this]
      exact Field.toIsField _
    have hloc := map_nonunit (𝒢.unitSection.stalkMap (genericPt L)).hom _
      ((IsLocalRing.mem_maximalIdeal _).mp hs)
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at hloc
    exact hloc
  have h2 : (1 : 𝒢.Pts τ).left.appLE U ⊤ h s =
      ((GroupModel.ptC τ).hom.appLE (𝒢.unitSection ⁻¹ᵁ U) ⊤ h) (𝒢.unitSection.app U s) := by
    have := Scheme.Hom.comp_appLE (GroupModel.ptC τ).hom 𝒢.unitSection U ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) s) this
  rw [h2, hz, map_zero]
  exact map_zero _

section Derivation

variable {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}

/-- Germs in `𝔪_ξ` vanish at `0` along `Φ`. -/
theorem germAlong_zero_of_mem (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ t 0 = 0 := by
  have hs : 𝒢.G.left.presheaf.germ (𝒢.exists_rep t).choose 𝒢.genericUnit
      (𝒢.exists_rep t).choose_spec.choose (𝒢.exists_rep t).choose_spec.choose_spec.choose = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  show 𝒢.evalAt (Φ 0) _ _ = 0
  rw [map_zero_of_hom Φ hΦ.1]
  exact evalAt_one_eq_zero τ _ _ _ (hs ▸ ht)

/-- Structure sections are constant `τ(r)` along `Φ` near `0`. -/
theorem germAlong_structMap (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (r : 𝓞 L) :
    𝒢.germAlong Φ (𝒢.structMap r) =ᶠ[nhds 0] fun _ => τ (algebraMap (𝓞 L) L r) := by
  have e1 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  filter_upwards [germAlong_eventuallyEq_rep hΦ _ ⊤ trivial _ e1.symm] with z hz
  rw [hz, evalAt_structSection]

/-- The derivative at `0` of the germ along `Φ`. -/
noncomputable def D0 (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (t : 𝒢.genStalk) : (Fin g → ℂ) →L[ℂ] ℂ :=
  fderiv ℂ (𝒢.germAlong Φ t) 0

theorem D0_add (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    D0 Φ (t₁ + t₂) = D0 Φ t₁ + D0 Φ t₂ := by
  unfold D0
  rw [(germAlong_add_mul hΦ t₁ t₂).1.fderiv_eq]
  exact fderiv_add (germAlong_differentiableAt hΦ t₁) (germAlong_differentiableAt hΦ t₂)

theorem D0_mul (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    D0 Φ (t₁ * t₂) = 𝒢.germAlong Φ t₁ 0 • D0 Φ t₂ + 𝒢.germAlong Φ t₂ 0 • D0 Φ t₁ := by
  unfold D0
  rw [(germAlong_add_mul hΦ t₁ t₂).2.fderiv_eq]
  exact fderiv_mul (germAlong_differentiableAt hΦ t₁) (germAlong_differentiableAt hΦ t₂)

theorem D0_mul_apply (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (t₁ * t₂) v =
      𝒢.germAlong Φ t₁ 0 * D0 Φ t₂ v + 𝒢.germAlong Φ t₂ 0 * D0 Φ t₁ v := by
  rw [D0_mul hΦ]
  rfl

theorem D0_add_apply (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (t₁ + t₂) v = D0 Φ t₁ v + D0 Φ t₂ v := by
  rw [D0_add hΦ]
  rfl

theorem D0_structMap_mul (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (r : 𝓞 L) (t : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (𝒢.structMap r * t) v = τ (algebraMap (𝓞 L) L r) * D0 Φ t v := by
  rw [D0_mul_apply hΦ]
  have h0 : D0 Φ (𝒢.structMap r) = 0 := by
    unfold D0
    rw [(germAlong_structMap hΦ r).fderiv_eq, fderiv_const_apply]
  rw [h0, (germAlong_structMap hΦ r).eq_of_nhds]
  simp

theorem D0_sq (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x : 𝒢.genStalk)
    (hx : x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) (v : Fin g → ℂ) : D0 Φ x v = 0 := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on (C := fun x => D0 Φ x v = 0) hx ?_ ?_
  · intro a ha b hb
    rw [D0_mul_apply hΦ, germAlong_zero_of_mem hΦ a ha, germAlong_zero_of_mem hΦ b hb]
    ring
  · intro x y hx hy
    rw [D0_add_apply hΦ, hx, hy, add_zero]

/-- **`GermDerivation` holds for every analytic uniformization** (proved). -/
theorem germDerivation_at (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    ∃ D : 𝒢.cotangent →+ (Fin g → ℂ),
      (∀ (r : 𝓞 L) x, D (r • x) = τ (algebraMap (𝓞 L) L r) • D x) ∧
      ∀ (t : IsLocalRing.maximalIdeal 𝒢.genStalk) (j : Fin g),
        D (𝒢.dCls t) j = fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1) := by
  let 𝔪 := IsLocalRing.maximalIdeal 𝒢.genStalk
  let D1 : 𝔪 → (Fin g → ℂ) := fun t j => D0 Φ (t : 𝒢.genStalk) (Pi.single j 1)
  have hD1add : ∀ a b : 𝔪, D1 (a + b) = D1 a + D1 b := by
    intro a b
    funext j
    simp only [D1, Submodule.coe_add, D0_add_apply hΦ, Pi.add_apply]
  have hD1wd : ∀ a b : 𝔪, 𝔪.toCotangent a = 𝔪.toCotangent b → D1 a = D1 b := by
    intro a b hab
    rw [Ideal.toCotangent_eq] at hab
    have this : D0 Φ (a : 𝒢.genStalk) = D0 Φ ((a : 𝒢.genStalk) - b) + D0 Φ (b : 𝒢.genStalk) := by
      rw [← D0_add hΦ, sub_add_cancel]
    funext j
    simp only [D1]
    rw [this, ContinuousLinearMap.add_apply, D0_sq hΦ _ hab, zero_add]
  let sec : 𝒢.cotangent → 𝔪 := Function.surjInv (𝔪.toCotangent_surjective)
  have hsec : ∀ x : 𝒢.cotangent, 𝔪.toCotangent (sec x) = x :=
    Function.surjInv_eq _
  let D : 𝒢.cotangent →+ (Fin g → ℂ) :=
    { toFun := fun x => D1 (sec x)
      map_zero' := by
        have : D1 (sec 0) = D1 0 := hD1wd _ _ (by rw [hsec, map_zero]; rfl)
        rw [this]
        have h00 : D0 Φ (0 : 𝒢.genStalk) = 0 := by
          have := D0_add hΦ (0 : 𝒢.genStalk) 0
          rw [add_zero] at this
          exact add_eq_left.mp this.symm
        funext j
        simp [D1, h00]
      map_add' := fun x y => by
        show D1 (sec (x + y)) = D1 (sec x) + D1 (sec y)
        rw [← hD1add]
        exact hD1wd _ _ (by rw [hsec, map_add, hsec, hsec]; rfl) }
  have hD : ∀ t : 𝔪, D (𝔪.toCotangent t) = D1 t := fun t => hD1wd _ _ (hsec _)
  refine ⟨D, fun r x => ?_, fun t j => ?_⟩
  · obtain ⟨t, rfl⟩ := 𝔪.toCotangent_surjective x
    have hrx : r • 𝒢.dCls t = 𝔪.toCotangent (𝒢.structMap r • t) := by
      show 𝒢.structMap r • 𝔪.toCotangent t = _
      rw [LinearMap.map_smul]
    show D (r • 𝒢.dCls t) = _ • D (𝒢.dCls t)
    rw [hrx]
    show D (𝔪.toCotangent _) = _ • D (𝔪.toCotangent t)
    rw [hD, hD]
    funext j
    simp only [D1, SetLike.val_smul, smul_eq_mul, Pi.smul_apply]
    rw [D0_structMap_mul hΦ]
  · show D (𝔪.toCotangent t) j = _
    rw [hD]
    rfl

end Derivation

end GermDer

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

/-- **Glue AN-der (the differential at the origin along `Φ`).** For an analytic uniformization
`Φ` of `𝒢(ℂ)_τ`, `t ↦ d(germAlong Φ t)(0)` on `𝔪_ξ` descends to an additive map
`D : 𝔪_ξ/𝔪_ξ² → ℂ^g` (the `j`-th coordinate is the derivative in the direction `e_j`) which is
`τ`-semilinear over `𝓞_L`. True: near `0`, `t ↦ germAlong Φ t` is a ring homomorphism into germs
of holomorphic functions (`Φ(0) = 1` lies over `ξ`, the sets `dom Φ U` are open, representatives
agree near `0`), germs in `𝔪_ξ` vanish at `0`, so the product rule kills `𝔪_ξ²`; structure
sections are the constants `τ(r)` along `Φ`. A statement about one group model; analytic glue.
STANDARD. -/
def GermDerivation : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ D : 𝒢.cotangent →+ (Fin g → ℂ),
      (∀ (r : 𝓞 L) x, D (r • x) = τ (algebraMap (𝓞 L) L r) • D x) ∧
      ∀ (t : IsLocalRing.maximalIdeal 𝒢.genStalk) (j : Fin g),
        D (𝒢.dCls t) j = fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1)

open ExteriorAlgebra in
/-- **AN-jac from AN-der** (determinants and the universal property of `⋀^g`; proved). -/
theorem jacobianSemilinear_of (h : GermDerivation) : JacobianSemilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨D, hDs, hDf⟩ := h K A L 𝒢 τ Λ Φ hΦ
  let σ0 : 𝓞 L →+* ℂ := τ.comp (algebraMap (𝓞 L) L)
  let _ : Module (𝓞 L) ℂ := Module.compHom ℂ σ0
  have e : ∀ [DecidableEq (Fin g)] (m : Fin g → 𝒢.cotangent) (i : Fin g) (z : 𝒢.cotangent),
      (Matrix.of fun i' j => D (Function.update m i z i') j) =
        (Matrix.of fun i' j => D (m i') j).updateRow i (D z) := by
    intro _ m i z
    ext i' j
    by_cases hi : i' = i
    · subst hi
      simp [Matrix.updateRow_self]
    · simp [Matrix.updateRow_ne hi, Function.update_of_ne hi]
  let alt : 𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] ℂ :=
    { toFun := fun v => (Matrix.of fun i j => D (v i) j).det
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = instDecidableEqFin g := Subsingleton.elim _ _
        rw [e, e, e, map_add]
        exact Matrix.det_updateRow_add _ _ _ _
      map_update_smul' := by
        intro inst m i r x
        obtain rfl : inst = instDecidableEqFin g := Subsingleton.elim _ _
        rw [e, e, hDs, Matrix.det_updateRow_smul]
        rfl
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact Matrix.det_zero_of_row_eq hij (by funext k; simp [hv]) }
  let J0 : exteriorPower (𝓞 L) g 𝒢.cotangent →ₗ[𝓞 L] ℂ :=
    exteriorPower.alternatingMapLinearEquiv alt
  have hJ0 : ∀ (r : 𝓞 L) x, J0 (r • x) = σ0 r * J0 x := fun r x => J0.map_smul r x
  let Jadd : 𝒢.hodgeSpace g →+ ℂ :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun a : L => AddMonoidHom.mk' (fun x => τ a * J0 x)
        (fun x y => by rw [map_add, mul_add]))
        (fun a b => by
          ext x
          simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
      (fun r a x => by
        simp only [AddMonoidHom.mk'_apply]
        rw [hJ0, Algebra.smul_def, map_mul]
        show τ (algebraMap (𝓞 L) L r) * τ a * J0 x = τ a * (σ0 r * J0 x)
        simp only [σ0, RingHom.comp_apply]
        ring)
  have hJt : ∀ (a : L) x, Jadd (a ⊗ₜ[𝓞 L] x) = τ a * J0 x := fun a x => rfl
  let J : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ :=
    { toFun := Jadd
      map_add' := map_add Jadd
      map_smul' := fun c v => by
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul a x =>
          rw [TensorProduct.smul_tmul', hJt, hJt, smul_eq_mul, map_mul, smul_eq_mul, _root_.mul_assoc]
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }
  refine ⟨J, fun f => ?_⟩
  show 𝒢.jacDet Φ f = Jadd ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i)))
  rw [hJt, map_one, _root_.one_mul]
  show _ = exteriorPower.alternatingMapLinearEquiv alt
    (exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i)))
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  show _ = (Matrix.of fun i j => D (𝒢.dCls (f i)) j).det
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [hDf]

/-- **AN-der is a theorem** (`germDerivation_at`). -/
theorem germDerivation : GermDerivation :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hΦ => germDerivation_at hΦ

/-- **AN-jac is a theorem.** -/
theorem jacobianSemilinear : JacobianSemilinear := jacobianSemilinear_of germDerivation

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

/-- **Main result (final form): glue H4a (`ModelHeightBaseChange`, verbatim) from five glue
statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-der (`GermDerivation`). Proved. -/
theorem modelHeightBaseChange_of_final (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hD : GermDerivation) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_glue5 h1 hc hω hl (jacobianSemilinear_of hD)

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements** (final form). -/
theorem hodgeLineBaseChange_of_final (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hD : GermDerivation) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_glue5 h1 hc hω hl (jacobianSemilinear_of hD)

/-- **Main result (final form): glue H4a (`ModelHeightBaseChange`, verbatim) from four glue
statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`). `GermDerivation` is proved.
Proved. -/
theorem modelHeightBaseChange_of_glue4 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_final h1 hc hω hl germDerivation

/-- **`HodgeLineBaseChange` (verbatim) from the same four glue statements** (final form). -/
theorem hodgeLineBaseChange_of_glue4 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_final h1 hc hω hl germDerivation


end ZInQ.HeightBC


namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)


/-! # infra-stalks: `CotangentSpanBC` from the stalk of a fibre product -/

section InfraStalks

variable {K : Type} [Field K] {A : AbVar K}

/-- The unit section is a section of the structure morphism. -/
theorem unitSection_comp_hom {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  unfold GroupModel.unitSection
  simpa using Over.w η[𝒢.G]

theorem hom_genericUnit {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  unfold GroupModel.genericUnit
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

theorem rationalOver_genericUnit {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : RationalOver 𝒢.G.hom 𝒢.genericUnit :=
  rationalOver_of_section _ _ (unitSection_comp_hom 𝒢) (genericPt L)

/-- The stalk of `Spec 𝓞_L` at its generic point is a field. -/
theorem isField_stalk_genericPt (L : Type) [Field L] [NumberField L]
    (y : Spec (CommRingCat.of (𝓞 L))) (hy : y = genericPt L) :
    IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk y) := by
  have h : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) := by
    rw [genericPoint_eq_bot_of_affine]; rfl
  rw [hy, h]
  exact Field.toIsField (Spec (CommRingCat.of (𝓞 L))).functionField

theorem maximalIdeal_stalk_genericPt (L : Type) [Field L] [NumberField L]
    (y : Spec (CommRingCat.of (𝓞 L))) (hy : y = genericPt L) :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk y) = ⊥ :=
  (IsLocalRing.isField_iff_maximalIdeal_eq).mp (isField_stalk_genericPt L y hy)

/-- Nonzero global functions are units at the generic point. -/
theorem isUnit_germ_genericPt (L : Type) [Field L] [NumberField L]
    (y : Spec (CommRingCat.of (𝓞 L))) (hy : y = genericPt L) (a : 𝓞 L) (ha : a ≠ 0) :
    IsUnit ((Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ y trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) := by
  have hF := isField_stalk_genericPt L y hy
  letI := hF.toField
  refine isUnit_iff_ne_zero.mpr fun h0 => ha ?_
  have h1 := germ_injective_of_isIntegral (Spec (CommRingCat.of (𝓞 L))) (U := ⊤) y trivial
    (h0.trans (map_zero _).symm)
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).hom h1
  rwa [Iso.inv_hom_id_apply, map_zero] at h2

theorem structMap_eq_stalkMap {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (a : 𝓞 L) :
    𝒢.structMap a = 𝒢.G.hom.stalkMap 𝒢.genericUnit
      ((Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ (𝒢.G.hom 𝒢.genericUnit) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) := by
  erw [Scheme.Hom.germ_stalkMap_apply 𝒢.G.hom ⊤ 𝒢.genericUnit (by trivial)]
  rfl

/-- Nonzero elements of `𝓞_L` are units in the local ring at the origin of the generic fibre. -/
theorem isUnit_structMap {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (a : 𝓞 L) (ha : a ≠ 0) : IsUnit (𝒢.structMap a) := by
  rw [structMap_eq_stalkMap]
  exact (isUnit_germ_genericPt L _ (hom_genericUnit 𝒢) a ha).map _

/-- Elements of the maximal ideal act by zero on the cotangent space. -/
theorem smul_cotangent_eq_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] {r r' : R}
    (h : r - r' ∈ IsLocalRing.maximalIdeal R) (v : IsLocalRing.CotangentSpace R) :
    r • v = r' • v := by
  obtain ⟨x, rfl⟩ := (IsLocalRing.maximalIdeal R).toCotangent_surjective v
  rw [← sub_eq_zero, ← sub_smul, ← map_smul, Ideal.toCotangent_eq_zero]
  rw [pow_two]
  exact Ideal.mul_mem_mul h x.2

/-- A nonzero `s ∈ 𝓞_L` divides a nonzero integer. -/
theorem exists_int_dvd {L : Type} [Field L] [NumberField L] (s : 𝓞 L) (hs : s ≠ 0) :
    ∃ (N : ℤ) (s' : 𝓞 L), N ≠ 0 ∧ (N : 𝓞 L) = s * s' := by
  have hlt := Ideal.under_lt_under_of_integral_mem_sdiff (R := ℤ) (I := (⊥ : Ideal (𝓞 L)))
    (J := Ideal.span {s}) bot_le (x := s)
    ⟨Ideal.mem_span_singleton_self s, by simpa using hs⟩ (Algebra.IsIntegral.isIntegral s)
  obtain ⟨N, hN, hN0⟩ := IsConcreteLE.exists_of_lt hlt
  rw [Ideal.under, Ideal.mem_comap, Ideal.mem_span_singleton] at hN
  obtain ⟨s', hs'⟩ := hN
  refine ⟨N, s', fun h => hN0 ?_, by simpa using hs'⟩
  rw [h]; exact Ideal.zero_mem _

variable {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']

/-- `bcCot` commutes with division by a nonzero integer. -/
theorem bcCot_intInv {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'}
    {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G} (he : IsMonBC 𝒢 𝒢' e) (N : ℤ) (hN : N ≠ 0)
    (u : 𝒢.cotangent) :
    ∃ u' : 𝒢.cotangent, (↑((isUnit_structMap 𝒢' (N : 𝓞 L') (by exact_mod_cast hN)).unit⁻¹) :
      𝒢'.genStalk) • bcCot he u = bcCot he u' := by
  set U := (isUnit_structMap 𝒢 (N : 𝓞 L) (by exact_mod_cast hN)).unit
  set U' := (isUnit_structMap 𝒢' (N : 𝓞 L') (by exact_mod_cast hN)).unit
  refine ⟨(↑(U⁻¹) : 𝒢.genStalk) • u, ?_⟩
  have hU : (U : 𝒢.genStalk) = (N : 𝒢.genStalk) := by
    simp [U, map_intCast]
  have hU' : (U' : 𝒢'.genStalk) = (N : 𝒢'.genStalk) := by
    simp [U', map_intCast]
  have h1 : u = (N : 𝒢.genStalk) • ((↑(U⁻¹) : 𝒢.genStalk) • u) := by
    rw [smul_smul, ← hU, Units.mul_inv, one_smul]
  have h2 : bcCot he u = (N : 𝒢'.genStalk) • bcCot he ((↑(U⁻¹) : 𝒢.genStalk) • u) := by
    conv_lhs => rw [h1]
    change bcCot he (((N : 𝒢.genStalk)) • ((↑(U⁻¹) : 𝒢.genStalk) • u)) = _
    rw [Int.cast_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]
  rw [h2, smul_smul, ← hU', Units.inv_mul, one_smul]

/-- **`CotangentSpanBC` holds** (glue BC-cot of height-bc, statement verbatim). -/
theorem cotangentSpanBC : CotangentSpanBC := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he
  set p := bcProj 𝒢 𝒢' e
  set ξ' := 𝒢'.genericUnit
  have hw : p ≫ 𝒢.G.hom = 𝒢'.G.hom ≫ bO L L' := bcProj_w 𝒢 𝒢' e
  have hgen : StalkGen p 𝒢'.G.hom ξ' := by
    have h0 := StalkGen.comp_of_isIso e.hom.left (pullback.fst 𝒢.G.hom (bO L L'))
      (pullback.snd _ _) ξ' (pullback_stalkGen _ _ _)
    have hsnd : e.hom.left ≫ pullback.snd 𝒢.G.hom (bO L L') = 𝒢'.G.hom := Over.w e.hom
    rw [hsnd] at h0
    exact h0
  have hrat : RationalOver 𝒢.G.hom (p ξ') := by
    have := rationalOver_genericUnit 𝒢
    rwa [← bcProj_genericUnit he] at this
  have hm := maximalIdeal_eq_of_stalkGen hw hgen hrat
  dsimp only [stalkIdeal] at hm
  rw [maximalIdeal_stalk_genericPt L' _ (hom_genericUnit 𝒢'), Ideal.map_bot, sup_bot_eq] at hm
  have hres := exists_sub_mem_maximalIdeal_of_stalkGen hw hgen hrat
  set N := Submodule.span (𝓞 L') (Set.range (bcCot he))
  -- `N` is stable under the local ring `𝒪_{𝒢',ξ'}`
  have hgenN : ∀ (r : 𝒢'.genStalk) (u : 𝒢.cotangent), r • bcCot he u ∈ N := by
    intro r u
    obtain ⟨b, hb⟩ := hres r
    have e1 : r • bcCot he u = 𝒢'.G.hom.stalkMap ξ' b • bcCot he u :=
      smul_cotangent_eq_of_sub_mem hb _
    rw [e1]
    -- write `b = a / s` in the stalk of `Spec 𝓞_{L'}` at the generic point
    let Y := Spec (CommRingCat.of (𝓞 L'))
    let y := 𝒢'.G.hom ξ'
    letI : Algebra Γ(Y, ⊤) (Y.presheaf.stalk y) := (Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
    have hL : IsLocalization.AtPrime (Y.presheaf.stalk y)
        ((isAffineOpen_top Y).primeIdealOf ⟨y, trivial⟩).asIdeal :=
      (isAffineOpen_top Y).isLocalization_stalk ⟨y, trivial⟩
    obtain ⟨⟨a, s⟩, hbs⟩ := @IsLocalization.surj _ _ _ _ _ _ hL b
    set a0 := (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom a
    set s0 := (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom s.1
    have hs0 : s0 ≠ 0 := by
      intro h0
      apply s.2
      have : s.1 = 0 := by
        have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv h0
        rwa [Iso.hom_inv_id_apply, map_zero] at this
      rw [this]; exact Ideal.zero_mem _
    have hga : ∀ c : Γ(Y, ⊤), 𝒢'.G.hom.stalkMap ξ' (algebraMap Γ(Y, ⊤) _ c) =
        𝒢'.structMap ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom c) := by
      intro c
      rw [structMap_eq_stalkMap, Iso.hom_inv_id_apply]
      rfl
    have hbs' : 𝒢'.G.hom.stalkMap ξ' b * 𝒢'.structMap s0 = 𝒢'.structMap a0 := by
      rw [← hga, ← hga, ← map_mul]; exact congrArg _ hbs
    obtain ⟨N0, s1, hN0, hN0s⟩ := exists_int_dvd s0 hs0
    obtain ⟨u', hu'⟩ := bcCot_intInv he N0 hN0 u
    set U' := (isUnit_structMap 𝒢' (N0 : 𝓞 L') (by exact_mod_cast hN0)).unit
    have hb' : 𝒢'.G.hom.stalkMap ξ' b = 𝒢'.structMap (a0 * s1) * (↑(U'⁻¹) : 𝒢'.genStalk) := by
      rw [Units.eq_mul_inv_iff_mul_eq]
      change _ = 𝒢'.structMap (a0 * s1)
      rw [show (U' : 𝒢'.genStalk) = 𝒢'.structMap (N0 : 𝓞 L') from rfl, hN0s, map_mul,
        map_mul, ← _root_.mul_assoc, hbs']
    rw [hb', mul_smul, hu']
    exact N.smul_mem (a0 * s1) (Submodule.subset_span ⟨u', rfl⟩)
  have hN : ∀ (r : 𝒢'.genStalk) (v : 𝒢'.cotangent), v ∈ N → r • v ∈ N := by
    intro r v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      exact hgenN r u
    | zero => rw [smul_zero]; exact N.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
    | smul c x _ hx =>
      change r • (𝒢'.structMap c • x) ∈ N
      rw [smul_smul, mul_comm, ← smul_smul]
      exact N.smul_mem c hx
  -- every cotangent vector lies in `N`
  rw [eq_top_iff]
  rintro v -
  obtain ⟨x, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢'.genStalk).toCotangent_surjective v
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Ideal.map (p.stalkMap ξ').hom (IsLocalRing.maximalIdeal _) := hm ▸ hx
  have hmem : ∀ y, y ∈ Ideal.map (p.stalkMap ξ').hom (IsLocalRing.maximalIdeal _) →
      y ∈ IsLocalRing.maximalIdeal 𝒢'.genStalk := fun y hy => hm ▸ hy
  suffices H : ∀ y (hy : y ∈ Ideal.map (p.stalkMap ξ').hom (IsLocalRing.maximalIdeal _)),
      (IsLocalRing.maximalIdeal 𝒢'.genStalk).toCotangent ⟨y, hmem y hy⟩ ∈ N from H x hx'
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    haveI := isIso_stalkSpecializes_bcMap he
    set sp := 𝒢.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (bcProj_genericUnit he)).specializes
    set a' := (inv sp).hom a
    have hsa : sp.hom a' = a := by
      simp only [a']
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
    have ha' : a' ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
      intro hu
      apply ha
      rw [← hsa]
      exact hu.map sp.hom
    refine Submodule.subset_span ⟨𝒢.dCls ⟨a', ha'⟩, ?_⟩
    rw [bcCot_dCls]
    unfold GroupModel.dCls
    congr 2
    change (sp ≫ p.stalkMap ξ') a' = _
    rw [CommRingCat.comp_apply, hsa]
  | zero =>
    have : (⟨0, hmem 0 (Submodule.zero_mem _)⟩ : IsLocalRing.maximalIdeal 𝒢'.genStalk) = 0 := rfl
    rw [this, map_zero]; exact N.zero_mem
  | add z w hz hw hzN hwN =>
    have : (⟨z + w, hmem _ (Submodule.add_mem _ hz hw)⟩ : IsLocalRing.maximalIdeal 𝒢'.genStalk) =
        ⟨z, hmem z hz⟩ + ⟨w, hmem w hw⟩ := rfl
    rw [this, map_add]; exact N.add_mem hzN hwN
  | smul c z hz hzN =>
    have : (⟨c • z, hmem _ (Submodule.smul_mem _ c hz)⟩ :
        IsLocalRing.maximalIdeal 𝒢'.genStalk) = c • ⟨z, hmem z hz⟩ := rfl
    rw [this, map_smul]
    exact hN c _ hzN

end InfraStalks

end ZInQ.HeightBC




/-! # infra-stalks: `UniformizationLiftAnalytic` (height-bc) proved -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

/-- **`UniformizationLiftAnalytic` holds** (glue BC-lift-an of height-bc, statement verbatim), from
`AlgebraicGeometry.exists_localStructure_pullback` applied to `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`. -/
theorem uniformizationLiftAnalytic : UniformizationLiftAnalytic := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ g Λ Φ' hΦ
  let p₁ : (Fin g → ℂ) → ((GroupModel.ptC τ').left ⟶ 𝒢.G.left) :=
    fun z => (Φ' z).left ≫ bcProj 𝒢 𝒢' e
  let p₂ : (GroupModel.ptC τ').left ⟶ Spec (CommRingCat.of (𝓞 L')) := (GroupModel.ptC τ').hom
  have hsnd : e.hom.left ≫ pullback.snd 𝒢.G.hom (bO L L') = 𝒢'.G.hom := Over.w e.hom
  have hw : ∀ z, p₁ z ≫ 𝒢.G.hom = p₂ ≫ bO L L' := fun z =>
    (Category.assoc _ _ _).trans ((congrArg ((Φ' z).left ≫ ·) (bcProj_w 𝒢 𝒢' e)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ bO L L') (Over.w (Φ' z)))))
  have hei : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id]; rfl
  have hlift : ∀ z, pullback.lift (p₁ z) p₂ (hw z) ≫ e.inv.left = (Φ' z).left := by
    intro z
    have h1 : pullback.lift (p₁ z) p₂ (hw z) = (Φ' z).left ≫ e.hom.left := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        exact (Category.assoc _ _ _).symm
      · rw [pullback.lift_snd]
        exact ((Over.w (Φ' z)).symm.trans (congrArg ((Φ' z).left ≫ ·) hsnd.symm)).trans
          (Category.assoc _ _ _).symm
    rw [h1]
    exact (Category.assoc _ _ _).trans ((congrArg ((Φ' z).left ≫ ·) hei).trans
      (Category.comp_id _))
  obtain ⟨-, -, -, hopen, hdiff⟩ := hΦ
  have hloc : ∀ (U : 𝒢'.G.left.Opens) (s : Γ(𝒢'.G.left, U)) (z₀ : Fin g → ℂ),
      z₀ ∈ 𝒢'.dom Φ' U → ∃ O : Set (Fin g → ℂ), IsOpen O ∧ z₀ ∈ O ∧ O ⊆ 𝒢'.dom Φ' U ∧
        DifferentiableOn ℂ (fun z => 𝒢'.evalAt (Φ' z) U s) O := by
    intro U s z₀ hz₀
    have hU : ⊤ ≤ (pullback.lift (p₁ z₀) p₂ (hw z₀) ≫ e.inv.left) ⁻¹ᵁ U := by
      rw [hlift]; exact hz₀
    obtain ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, hall⟩ :=
      exists_localStructure_pullback 𝒢.G.hom (bO L L') e.inv.left U s (p₁ z₀) p₂ (hw z₀) hU
    let Hf : (Fin g → ℂ) → ℂ := fun z =>
      ∑ k, 𝒢.evalAt (bcPts e σ τ' hστ (Φ' z)) V₁ (c k) * evalPt p₂ V₂ (d k)
    let Nf : (Fin g → ℂ) → ℂ := fun z =>
      ∑ k, 𝒢.evalAt (bcPts e σ τ' hστ (Φ' z)) V₁ (a k) * evalPt p₂ V₂ (b k)
    let D1 := 𝒢.dom (fun z => bcPts e σ τ' hστ (Φ' z)) V₁
    have hHd : DifferentiableOn ℂ Hf D1 :=
      DifferentiableOn.fun_sum fun k _ => (hdiff V₁ (c k)).mul_const _
    have hNd : DifferentiableOn ℂ Nf D1 :=
      DifferentiableOn.fun_sum fun k _ => (hdiff V₁ (a k)).mul_const _
    let O := D1 ∩ Hf ⁻¹' {0}ᶜ
    have hO : IsOpen O := hHd.continuousOn.isOpen_inter_preimage (hopen V₁) isOpen_compl_singleton
    have hmem : ∀ z ∈ O, z ∈ 𝒢'.dom Φ' U ∧ 𝒢'.evalAt (Φ' z) U s * Hf z = Nf z := by
      rintro z ⟨hz1, hz2⟩
      have := hall (p₁ z) p₂ (hw z) hz1 h2 hz2
      refine ⟨?_, ?_⟩
      · show ⊤ ≤ (Φ' z).left ⁻¹ᵁ U
        exact (hlift z) ▸ this.1
      · show evalPt (Φ' z).left U s * Hf z = Nf z
        exact (hlift z) ▸ this.2
    refine ⟨O, hO, ⟨h1, hne⟩, fun z hz => (hmem z hz).1, ?_⟩
    have hq : ∀ z ∈ O, 𝒢'.evalAt (Φ' z) U s = Nf z * (Hf z)⁻¹ := by
      intro z hz
      rw [← div_eq_mul_inv, eq_div_iff hz.2]
      exact (hmem z hz).2
    exact ((hNd.mono Set.inter_subset_left).mul ((hHd.mono Set.inter_subset_left).inv
      (fun z hz => hz.2))).congr hq
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨O, hO, hzO, hOsub, -⟩ := hloc U 0 z hz
    exact ⟨O, hOsub, hO, hzO⟩
  · intro z hz
    obtain ⟨O, hO, hzO, -, hd⟩ := hloc U s z hz
    exact (hd.differentiableAt (hO.mem_nhds hzO)).differentiableWithinAt

/-- `UniformizationLift` is a theorem. -/
theorem uniformizationLift : UniformizationLift :=
  uniformizationLift_of uniformizationLiftAnalytic

end ZInQ.HeightBC




/-! # infra-stalks: height-bc's H4a and `HodgeLineBaseChange` from two glue statements -/

namespace ZInQ.HeightBC

/-- **H4a (`ModelHeightBaseChange`, verbatim) from `HodgeBCInjective` and `OmegaBaseChange`**:
`CotangentSpanBC` and `UniformizationLiftAnalytic` are now theorems. -/
theorem modelHeightBaseChange_of_two (h1 : HodgeBCInjective) (hω : OmegaBaseChange) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_glue4 h1 cotangentSpanBC hω uniformizationLiftAnalytic

/-- **`HodgeLineBaseChange` (verbatim) from `HodgeBCInjective` and `OmegaBaseChange`.** -/
theorem hodgeLineBaseChange_of_two (h1 : HodgeBCInjective) (hω : OmegaBaseChange) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_glue4 h1 cotangentSpanBC hω uniformizationLiftAnalytic

end ZInQ.HeightBC




/-! # The stalk of a fibre product is a localization of the tensor product of stalks

For `z ∈ X ×_S Y` over `x ∈ X`, `y ∈ Y`, `s ∈ S`, the ring map
`Φ : 𝒪_{X,x} ⊗_{𝒪_{S,s}} 𝒪_{Y,y} → 𝒪_{X ×_S Y, z}` is a localization at the prime `Φ⁻¹(𝔪_z)`:
every element of `𝒪_z` is `Φ a / Φ u` with `Φ u` a unit, and `Φ t = 0` implies `u t = 0` for some
`u` with `Φ u` a unit (`pullback_stalk_tensor_isLocalization`; Stacks 01JT, EGA I 3.6.5,
UNVERIFIED locators). -/

namespace AlgebraicGeometry

open CategoryTheory Limits TensorProduct

/-- `Spec.map φ` on germs of global sections, at a named point. -/
theorem stalkMapAt_germ_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (t : Spec S)
    {r0 : Spec R} (h : Spec.map φ t = r0) (a : R) :
    (Spec.map φ).stalkMapAt h ((Spec R).presheaf.germ ⊤ r0 trivial ((Scheme.ΓSpecIso R).inv a)) =
      (Spec S).presheaf.germ ⊤ t trivial ((Scheme.ΓSpecIso S).inv (φ a)) := by
  subst h
  rw [Scheme.Hom.stalkMapAt_rfl]
  exact (germ_ΓSpecIso_inv_map φ t a).symm

theorem stalkMapAt_comp_apply' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} {y : Y}
    {z : Z} (hf : f x = y) (hg : g y = z) (hfg : (f ≫ g) x = z) (c : Z.presheaf.stalk z) :
    (f.stalkMapAt hf).hom ((g.stalkMapAt hg).hom c) = ((f ≫ g).stalkMapAt hfg).hom c := by
  rw [Scheme.Hom.stalkMapAt_comp f g hf hg hfg]
  rfl

/-- **Stalks of a fibre product.** See the section docstring. The points are named:
`x = fst z`, `y = snd z`, `s = f x = g y`; the algebra structures are `f^♯ : 𝒪_s → 𝒪_x` and
`g^♯ : 𝒪_s → 𝒪_y`. -/
theorem pullback_stalk_tensor_isLocalization {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : ↥(pullback f g)) {x : X} {y : Y} {s : S} (hx : pullback.fst f g z = x)
    (hy : pullback.snd f g z = y) (hs : f x = s) (hys : g y = s) :
    letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) := (f.stalkMapAt hs).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk s) (Y.presheaf.stalk y) := (g.stalkMapAt hys).hom.toAlgebra
    ∃ Φ : (X.presheaf.stalk x) ⊗[S.presheaf.stalk s] (Y.presheaf.stalk y) →+*
        (pullback f g).presheaf.stalk z,
      (∀ a b, Φ (a ⊗ₜ b) =
        ((pullback.fst f g).stalkMapAt hx).hom a * ((pullback.snd f g).stalkMapAt hy).hom b) ∧
      (∀ r : (pullback f g).presheaf.stalk z, ∃ a u, IsUnit (Φ u) ∧ r * Φ u = Φ a) ∧
      (∀ t, Φ t = 0 → ∃ u, IsUnit (Φ u) ∧ u * t = 0) := by
  let Ox := X.presheaf.stalk x
  let Oy := Y.presheaf.stalk y
  let Os := S.presheaf.stalk s
  let Oz := (pullback f g).presheaf.stalk z
  letI : Algebra Os Ox := (f.stalkMapAt hs).hom.toAlgebra
  letI : Algebra Os Oy := (g.stalkMapAt hys).hom.toAlgebra
  let ψX := ((pullback.fst f g).stalkMapAt hx).hom
  let ψY := ((pullback.snd f g).stalkMapAt hy).hom
  letI : Algebra Os Oz := (ψX.comp (f.stalkMapAt hs).hom).toAlgebra
  have hzs1 : (pullback.fst f g ≫ f) z = s := by rw [Scheme.Hom.comp_apply, hx, hs]
  have hzs2 : (pullback.snd f g ≫ g) z = s := by rw [Scheme.Hom.comp_apply, hy, hys]
  -- the two composites `𝒪_s → 𝒪_z` agree
  have hc0 : ∀ r : Os, ψY ((g.stalkMapAt hys).hom r) = ψX ((f.stalkMapAt hs).hom r) := by
    intro r
    rw [stalkMapAt_comp_apply' (pullback.snd f g) g hy hys hzs2,
      stalkMapAt_comp_apply' (pullback.fst f g) f hx hs hzs1,
      Scheme.Hom.stalkMapAt_congr pullback.condition.symm hzs2 hzs1]
  let ψXa : Ox →ₐ[Os] Oz := { ψX with commutes' := fun r => rfl }
  let ψYa : Oy →ₐ[Os] Oz := { ψY with commutes' := fun r => hc0 r }
  have hcomm : ∀ a b, Commute (ψXa a) (ψYa b) := fun a b => Commute.all _ _
  let Φ : Ox ⊗[Os] Oy →+* Oz := (Algebra.TensorProduct.lift ψXa ψYa hcomm).toRingHom
  have hΦ : ∀ a b, Φ (a ⊗ₜ b) = ψX a * ψY b := fun a b => rfl
  refine ⟨Φ, hΦ, ?_, ?_⟩
  -- surjectivity half, from `pullback_stalkGen`
  · intro r
    obtain ⟨c, hc, w, hw, hwu, hrw⟩ := pullback_stalkGen f g z r
    have hle : ((pullback.fst f g).stalkMap z).hom.range ⊔
        ((pullback.snd f g).stalkMap z).hom.range ≤ Φ.range := by
      refine sup_le ?_ ?_
      · rintro _ ⟨a', rfl⟩
        obtain ⟨a, ha⟩ := Scheme.Hom.exists_stalkMapAt_eq (pullback.fst f g) hx a'
        exact ⟨a ⊗ₜ 1, by rw [hΦ, map_one, mul_one]; exact ha⟩
      · rintro _ ⟨b', rfl⟩
        obtain ⟨b, hb⟩ := Scheme.Hom.exists_stalkMapAt_eq (pullback.snd f g) hy b'
        exact ⟨1 ⊗ₜ b, by rw [hΦ, map_one, one_mul]; exact hb⟩
    obtain ⟨a, rfl⟩ := hle hc
    obtain ⟨u, rfl⟩ := hle hw
    exact ⟨a, u, hwu, hrw⟩
  -- kernel half, through affine charts
  · intro t ht
    let 𝒱 := S.affineOpenCover
    let R := 𝒱.X (𝒱.idx s)
    let jV : Spec R ⟶ S := 𝒱.f (𝒱.idx s)
    have hsV : f x ∈ Set.range jV := by rw [hs]; exact 𝒱.covers _
    obtain ⟨A, jU, _, φ, hxU, eU⟩ := exists_affine_chart_over f jV x hsV
    have hsV' : g y ∈ Set.range jV := by rw [hys]; exact 𝒱.covers _
    obtain ⟨B, jW, _, ψ, hyW, eW⟩ := exists_affine_chart_over g jV y hsV'
    letI : Algebra R A := φ.hom.toAlgebra
    letI : Algebra R B := ψ.hom.toAlgebra
    let m := pullback.map (Spec.map φ) (Spec.map ψ) f g jU jW jV eU eW
    have hz : z ∈ Set.range m := by
      rw [Scheme.Pullback.range_map]
      exact ⟨by rw [Set.mem_preimage, hx]; exact hxU, by rw [Set.mem_preimage, hy]; exact hyW⟩
    obtain ⟨t0', ht0'⟩ := hz
    let e := pullbackSpecIso R A B
    let T := CommRingCat.of (A ⊗[R] B)
    let m' : Spec T ⟶ pullback f g := e.inv ≫ m
    let iL := CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)
    let iR := CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      B →ₐ[R] A ⊗[R] B).toRingHom
    have h1 : m' ≫ pullback.fst f g = Spec.map iL ≫ jU := by
      simp only [m', m, e, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc]
      exact congrArg (· ≫ jU) (pullbackSpecIso_inv_fst R A B)
    have h2 : m' ≫ pullback.snd f g = Spec.map iR ≫ jW := by
      simp only [m', m, e, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc]
      exact congrArg (· ≫ jW) (pullbackSpecIso_inv_snd R A B)
    let t0 := e.hom t0'
    have hmt0 : m' t0 = z := by
      have he : e.inv (e.hom t0') = t0' := by
        rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
      simp only [m', t0]
      rw [Scheme.Hom.comp_apply, he, ht0']
    -- chart points
    let a0 := Spec.map iL t0
    let b0 := Spec.map iR t0
    let r0 := Spec.map φ a0
    have ha0 : jU a0 = x := by
      have : (m' ≫ pullback.fst f g) t0 = x := by rw [Scheme.Hom.comp_apply, hmt0, hx]
      rw [h1, Scheme.Hom.comp_apply] at this
      exact this
    have hb0 : jW b0 = y := by
      have : (m' ≫ pullback.snd f g) t0 = y := by rw [Scheme.Hom.comp_apply, hmt0, hy]
      rw [h2, Scheme.Hom.comp_apply] at this
      exact this
    have hφψ : φ ≫ iL = ψ ≫ iR := by
      ext r
      change φ r ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] ψ r
      rw [show φ r = r • (1 : A) from (Algebra.algebraMap_eq_smul_one r),
        show ψ r = r • (1 : B) from (Algebra.algebraMap_eq_smul_one r), TensorProduct.smul_tmul]
    have hr0' : Spec.map ψ b0 = r0 := by
      change (Spec.map iR ≫ Spec.map ψ) t0 = (Spec.map iL ≫ Spec.map φ) t0
      rw [← Spec.map_comp, ← Spec.map_comp, hφψ]
    have hr0 : jV r0 = s := by
      change (Spec.map φ ≫ jV) a0 = s
      rw [eU, Scheme.Hom.comp_apply, ha0, hs]
    -- germ maps and the stalk isomorphisms of the charts
    let germT : T →+* (Spec T).presheaf.stalk t0 :=
      ((Scheme.ΓSpecIso T).inv ≫ (Spec T).presheaf.germ ⊤ t0 trivial).hom
    let germA : A →+* (Spec A).presheaf.stalk a0 :=
      ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ a0 trivial).hom
    let germB : B →+* (Spec B).presheaf.stalk b0 :=
      ((Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ b0 trivial).hom
    let germR : R →+* (Spec R).presheaf.stalk r0 :=
      ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ r0 trivial).hom
    let κT := m'.stalkMapAt hmt0
    let κA := jU.stalkMapAt ha0
    let κB := jW.stalkMapAt hb0
    let κR := jV.stalkMapAt hr0
    haveI : IsIso κT := by
      simp only [κT, Scheme.Hom.stalkMapAt]; infer_instance
    haveI : IsIso κA := by
      simp only [κA, Scheme.Hom.stalkMapAt]; infer_instance
    haveI : IsIso κB := by
      simp only [κB, Scheme.Hom.stalkMapAt]; infer_instance
    haveI : IsIso κR := by
      simp only [κR, Scheme.Hom.stalkMapAt]; infer_instance
    have inj : ∀ {P Q : CommRingCat.{u}} (κ : P ⟶ Q) [IsIso κ], Function.Injective κ.hom :=
      fun κ _ => (ConcreteCategory.bijective_of_isIso κ).1
    have invκ : ∀ {P Q : CommRingCat.{u}} (κ : P ⟶ Q) [IsIso κ] (q : Q), κ.hom ((inv κ).hom q) = q :=
      fun κ _ q => by rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
    let γA : A →+* Ox := (inv κA).hom.comp germA
    let γB : B →+* Oy := (inv κB).hom.comp germB
    let γR : R →+* Os := (inv κR).hom.comp germR
    let Θ : T →+* Oz := (inv κT).hom.comp germT
    -- compatibilities
    have hγA : ∀ α, κA.hom (γA α) = germA α := fun α => invκ κA _
    have hγB : ∀ β, κB.hom (γB β) = germB β := fun β => invκ κB _
    have hγR : ∀ r, κR.hom (γR r) = germR r := fun r => invκ κR _
    have hΘ : ∀ w, κT.hom (Θ w) = germT w := fun w => invκ κT _
    have c1 : ∀ r, γA (φ r) = (f.stalkMapAt hs).hom (γR r) := by
      intro r
      apply inj κA
      rw [hγA]
      have hpt : (jU ≫ f) a0 = s := by rw [Scheme.Hom.comp_apply, ha0, hs]
      rw [stalkMapAt_comp_apply' jU f ha0 hs hpt,
        Scheme.Hom.stalkMapAt_congr eU.symm hpt (by rw [Scheme.Hom.comp_apply]; exact hr0),
        ← stalkMapAt_comp_apply' (Spec.map φ) jV rfl hr0, hγR]
      exact (stalkMapAt_germ_ΓSpecIso_inv φ a0 rfl r).symm
    have c2 : ∀ r, γB (ψ r) = (g.stalkMapAt hys).hom (γR r) := by
      intro r
      apply inj κB
      rw [hγB]
      have hpt : (jW ≫ g) b0 = s := by rw [Scheme.Hom.comp_apply, hb0, hys]
      rw [stalkMapAt_comp_apply' jW g hb0 hys hpt,
        Scheme.Hom.stalkMapAt_congr eW.symm hpt
          (by rw [Scheme.Hom.comp_apply, hr0']; exact hr0),
        ← stalkMapAt_comp_apply' (Spec.map ψ) jV hr0' hr0, hγR]
      exact (stalkMapAt_germ_ΓSpecIso_inv ψ b0 hr0' r).symm
    have c3A : ∀ α, ψX (γA α) = Θ (α ⊗ₜ[R] 1) := by
      intro α
      apply inj κT
      rw [hΘ]
      have hpt : (m' ≫ pullback.fst f g) t0 = x := by rw [Scheme.Hom.comp_apply, hmt0, hx]
      rw [stalkMapAt_comp_apply' m' (pullback.fst f g) hmt0 hx hpt,
        Scheme.Hom.stalkMapAt_congr h1 hpt (by rw [Scheme.Hom.comp_apply]; exact ha0),
        ← stalkMapAt_comp_apply' (Spec.map iL) jU rfl ha0, hγA]
      exact stalkMapAt_germ_ΓSpecIso_inv iL t0 rfl α
    have c3B : ∀ β, ψY (γB β) = Θ ((1 : A) ⊗ₜ[R] β) := by
      intro β
      apply inj κT
      rw [hΘ]
      have hpt : (m' ≫ pullback.snd f g) t0 = y := by rw [Scheme.Hom.comp_apply, hmt0, hy]
      rw [stalkMapAt_comp_apply' m' (pullback.snd f g) hmt0 hy hpt,
        Scheme.Hom.stalkMapAt_congr h2 hpt (by rw [Scheme.Hom.comp_apply]; exact hb0),
        ← stalkMapAt_comp_apply' (Spec.map iR) jW rfl hb0, hγB]
      exact stalkMapAt_germ_ΓSpecIso_inv iR t0 rfl β
    -- the map `A ⊗[R] B → 𝒪_x ⊗[𝒪_s] 𝒪_y`
    letI : Algebra R (Ox ⊗[Os] Oy) := ((algebraMap Os (Ox ⊗[Os] Oy)).comp γR).toAlgebra
    let fA : A →ₐ[R] Ox ⊗[Os] Oy :=
      { (Algebra.TensorProduct.includeLeftRingHom : Ox →+* Ox ⊗[Os] Oy).comp γA with
        commutes' := fun r => by
          change γA (φ r) ⊗ₜ[Os] (1 : Oy) = algebraMap Os (Ox ⊗[Os] Oy) (γR r)
          rw [c1, Algebra.TensorProduct.algebraMap_apply]
          rfl }
    let fB : B →ₐ[R] Ox ⊗[Os] Oy :=
      { (Algebra.TensorProduct.includeRight : Oy →ₐ[Os] Ox ⊗[Os] Oy).toRingHom.comp γB with
        commutes' := fun r => by
          change (1 : Ox) ⊗ₜ[Os] γB (ψ r) = algebraMap Os (Ox ⊗[Os] Oy) (γR r)
          rw [c2, Algebra.TensorProduct.algebraMap_apply']
          rfl }
    let ι : T →+* Ox ⊗[Os] Oy :=
      (Algebra.TensorProduct.lift fA fB (fun _ _ => Commute.all _ _)).toRingHom
    have hι : ∀ α β, ι (α ⊗ₜ β) = γA α ⊗ₜ γB β := by
      intro α β
      change fA α * fB β = _
      change (γA α ⊗ₜ[Os] (1 : Oy)) * ((1 : Ox) ⊗ₜ[Os] γB β) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hΦι : ∀ w, Φ (ι w) = Θ w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
      | tmul α β =>
        rw [hι, hΦ, c3A, c3B, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    -- every element of `𝒪_x`, `𝒪_y` is a fraction of chart elements
    have locA : ∀ a : Ox, ∃ α u : A, IsUnit (γA u) ∧ a * γA u = γA α := by
      intro a
      letI : Algebra Γ(Spec A, ⊤) ((Spec A).presheaf.stalk a0) :=
        ((Spec A).presheaf.germ ⊤ a0 trivial).hom.toAlgebra
      have hL : IsLocalization.AtPrime ((Spec A).presheaf.stalk a0)
          ((isAffineOpen_top (Spec A)).primeIdealOf ⟨a0, trivial⟩).asIdeal :=
        (isAffineOpen_top (Spec A)).isLocalization_stalk ⟨a0, trivial⟩
      obtain ⟨⟨p, q⟩, hpq⟩ := @IsLocalization.surj _ _ _ _ _ _ hL (κA.hom a)
      have hq := @IsLocalization.map_units _ _ _ _ _ _ hL q
      refine ⟨(Scheme.ΓSpecIso A).hom p, (Scheme.ΓSpecIso A).hom q.1, ?_, ?_⟩
      · have : germA ((Scheme.ΓSpecIso A).hom q.1) = algebraMap _ _ q.1 :=
          congrArg ((Spec A).presheaf.germ ⊤ a0 trivial).hom
            (Iso.hom_inv_id_apply (Scheme.ΓSpecIso A) q.1)
        have h' : IsUnit (κA.hom (γA ((Scheme.ΓSpecIso A).hom q.1))) := by
          rw [hγA, this]; exact hq
        have := h'.map (inv κA).hom
        rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
      · apply inj κA
        rw [map_mul, hγA, hγA]
        have e1 : germA ((Scheme.ΓSpecIso A).hom q.1) = algebraMap _ _ q.1 :=
          congrArg ((Spec A).presheaf.germ ⊤ a0 trivial).hom
            (Iso.hom_inv_id_apply (Scheme.ΓSpecIso A) q.1)
        have e2 : germA ((Scheme.ΓSpecIso A).hom p) = algebraMap _ _ p :=
          congrArg ((Spec A).presheaf.germ ⊤ a0 trivial).hom
            (Iso.hom_inv_id_apply (Scheme.ΓSpecIso A) p)
        rw [e1, e2]
        exact hpq
    have locB : ∀ b : Oy, ∃ β v : B, IsUnit (γB v) ∧ b * γB v = γB β := by
      intro b
      letI : Algebra Γ(Spec B, ⊤) ((Spec B).presheaf.stalk b0) :=
        ((Spec B).presheaf.germ ⊤ b0 trivial).hom.toAlgebra
      have hL : IsLocalization.AtPrime ((Spec B).presheaf.stalk b0)
          ((isAffineOpen_top (Spec B)).primeIdealOf ⟨b0, trivial⟩).asIdeal :=
        (isAffineOpen_top (Spec B)).isLocalization_stalk ⟨b0, trivial⟩
      obtain ⟨⟨p, q⟩, hpq⟩ := @IsLocalization.surj _ _ _ _ _ _ hL (κB.hom b)
      have hq := @IsLocalization.map_units _ _ _ _ _ _ hL q
      refine ⟨(Scheme.ΓSpecIso B).hom p, (Scheme.ΓSpecIso B).hom q.1, ?_, ?_⟩
      · have : germB ((Scheme.ΓSpecIso B).hom q.1) = algebraMap _ _ q.1 :=
          congrArg ((Spec B).presheaf.germ ⊤ b0 trivial).hom
            (Iso.hom_inv_id_apply (Scheme.ΓSpecIso B) q.1)
        have h' : IsUnit (κB.hom (γB ((Scheme.ΓSpecIso B).hom q.1))) := by
          rw [hγB, this]; exact hq
        have := h'.map (inv κB).hom
        rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
      · apply inj κB
        rw [map_mul, hγB, hγB]
        have e1 : germB ((Scheme.ΓSpecIso B).hom q.1) = algebraMap _ _ q.1 :=
          congrArg ((Spec B).presheaf.germ ⊤ b0 trivial).hom
            (Iso.hom_inv_id_apply (Scheme.ΓSpecIso B) q.1)
        have e2 : germB ((Scheme.ΓSpecIso B).hom p) = algebraMap _ _ p :=
          congrArg ((Spec B).presheaf.germ ⊤ b0 trivial).hom
            (Iso.hom_inv_id_apply (Scheme.ΓSpecIso B) p)
        rw [e1, e2]
        exact hpq
    -- clear denominators in `t`
    have hden : ∀ t' : Ox ⊗[Os] Oy, ∃ (u : A) (v : B) (t₀ : T), IsUnit (γA u) ∧ IsUnit (γB v) ∧
        (γA u ⊗ₜ[Os] γB v) * t' = ι t₀ := by
      intro t'
      induction t' using TensorProduct.induction_on with
      | zero => exact ⟨1, 1, 0, by simp, by simp, by simp⟩
      | tmul a b =>
        obtain ⟨α, u, hu, hau⟩ := locA a
        obtain ⟨β, v, hv, hbv⟩ := locB b
        refine ⟨u, v, α ⊗ₜ β, hu, hv, ?_⟩
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_comm (γA u), mul_comm (γB v), hau, hbv, hι]
      | add t₁ t₂ h₁ h₂ =>
        obtain ⟨u₁, v₁, s₁, hu₁, hv₁, e₁⟩ := h₁
        obtain ⟨u₂, v₂, s₂, hu₂, hv₂, e₂⟩ := h₂
        refine ⟨u₁ * u₂, v₁ * v₂, (u₂ ⊗ₜ v₂) * s₁ + (u₁ ⊗ₜ v₁) * s₂,
          by rw [map_mul]; exact hu₁.mul hu₂, by rw [map_mul]; exact hv₁.mul hv₂, ?_⟩
        rw [map_add, map_mul ι, map_mul ι, hι, hι, ← e₁, ← e₂, mul_add]
        congr 1
        · rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, map_mul γA, map_mul γB,
            mul_comm (γA u₁), mul_comm (γB v₁)]
        · rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, map_mul γA, map_mul γB]
    obtain ⟨u, v, t₀, hu, hv, htu⟩ := hden t
    have hΘ0 : Θ t₀ = 0 := by
      rw [← hΦι, ← htu, map_mul, ht, mul_zero]
    have hgerm0 : germT t₀ = 0 := by
      rw [← hΘ, hΘ0, map_zero]
    letI : Algebra Γ(Spec T, ⊤) ((Spec T).presheaf.stalk t0) :=
      ((Spec T).presheaf.germ ⊤ t0 trivial).hom.toAlgebra
    have hLT : IsLocalization.AtPrime ((Spec T).presheaf.stalk t0)
        ((isAffineOpen_top (Spec T)).primeIdealOf ⟨t0, trivial⟩).asIdeal :=
      (isAffineOpen_top (Spec T)).isLocalization_stalk ⟨t0, trivial⟩
    have h0' : algebraMap Γ(Spec T, ⊤) ((Spec T).presheaf.stalk t0)
        ((Scheme.ΓSpecIso T).inv t₀) = 0 := hgerm0
    obtain ⟨w, hw⟩ := (@IsLocalization.map_eq_zero_iff _ _ _ _ _ _ hLT _).mp h0'
    let w₀ : T := (Scheme.ΓSpecIso T).hom w.1
    have hww : w₀ * t₀ = 0 := by
      have := congrArg (Scheme.ΓSpecIso T).hom hw
      rwa [map_mul, map_zero, Iso.inv_hom_id_apply] at this
    refine ⟨ι w₀ * (γA u ⊗ₜ[Os] γB v), ?_, ?_⟩
    · rw [map_mul, hΦι, hΦ]
      refine IsUnit.mul ?_ ((hu.map ψX).mul (hv.map ψY))
      have hgw : IsUnit (germT w₀) := by
        have e1 : germT w₀ = algebraMap _ _ w.1 :=
          congrArg ((Spec T).presheaf.germ ⊤ t0 trivial).hom
            (Iso.hom_inv_id_apply (Scheme.ΓSpecIso T) w.1)
        rw [e1]
        exact @IsLocalization.map_units _ _ _ _ _ _ hLT w
      have h' : IsUnit (κT.hom (Θ w₀)) := by rw [hΘ]; exact hgw
      have := h'.map (inv κT).hom
      rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
    · rw [mul_assoc, htu, ← map_mul, hww, map_zero]

/-- **`𝒪_{X ×_S Y, z} = (𝒪_{X,x} ⊗_{𝒪_{S,s}} 𝒪_{Y,y})_𝔭`**, as Mathlib's `IsLocalization` at the
prime `𝔭 = Φ⁻¹(𝔪_z)`. -/
theorem pullback_stalk_isLocalization {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : ↥(pullback f g)) {x : X} {y : Y} {s : S} (hx : pullback.fst f g z = x)
    (hy : pullback.snd f g z = y) (hs : f x = s) (hys : g y = s) :
    letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) := (f.stalkMapAt hs).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk s) (Y.presheaf.stalk y) := (g.stalkMapAt hys).hom.toAlgebra
    ∃ Φ : (X.presheaf.stalk x) ⊗[S.presheaf.stalk s] (Y.presheaf.stalk y) →+*
        (pullback f g).presheaf.stalk z,
      (∀ a b, Φ (a ⊗ₜ b) =
        ((pullback.fst f g).stalkMapAt hx).hom a * ((pullback.snd f g).stalkMapAt hy).hom b) ∧
      @IsLocalization _ _ (Ideal.comap Φ (IsLocalRing.maximalIdeal _)).primeCompl _ _
        Φ.toAlgebra := by
  letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) := (f.stalkMapAt hs).hom.toAlgebra
  letI : Algebra (S.presheaf.stalk s) (Y.presheaf.stalk y) := (g.stalkMapAt hys).hom.toAlgebra
  obtain ⟨Φ, hΦ, hsurj, hker⟩ := pullback_stalk_tensor_isLocalization f g z hx hy hs hys
  refine ⟨Φ, hΦ, ?_⟩
  letI := Φ.toAlgebra
  have hunit : ∀ u, u ∈ (Ideal.comap Φ (IsLocalRing.maximalIdeal _)).primeCompl ↔ IsUnit (Φ u) := by
    intro u
    change ¬ (Φ u ∈ IsLocalRing.maximalIdeal _) ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  rw [isLocalization_iff]
  refine ⟨fun u => (hunit u.1).mp u.2, fun r => ?_, fun {a b} hab => ?_⟩
  · obtain ⟨a, u, hu, h⟩ := hsurj r
    exact ⟨(a, ⟨u, (hunit u).mpr hu⟩), h⟩
  · have h0 : Φ (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab
    obtain ⟨u, hu, h⟩ := hker _ h0
    exact ⟨⟨u, (hunit u).mpr hu⟩, by rw [← sub_eq_zero, ← mul_sub]; exact h⟩

end AlgebraicGeometry




/-! # Cotangent space of a base change by a field extension (bijective)

For `z ∈ X ×_S Y` with `𝒪_{S,s}` and `𝒪_{Y,y}` fields (e.g. `S = Spec L`, `Y = Spec L'`) and `x`
rational over `s`, the map `𝒪_y ⊗_{𝒪_s} 𝔪_x/𝔪_x² → 𝔪_z/𝔪_z²`, `c ⊗ da ↦ c · d(fst^♯ a)`, is
injective (`cotangent_baseChange_injective`); it is onto by `cotangent_span_pullback`. The proof
combines Mathlib's `Ideal.tensorCotangentHom` (flat base change of `I/I²`) with the localization
`pullback_stalk_tensor_isLocalization` and an algebraic lemma on cotangent spaces of localizations
at a maximal ideal (`mem_sq_of_map_mem_sq`). -/

/-- If `φ : B → R` (`R` local) is a localization at an ideal `J` with `φ(J)R = 𝔪_R` and
`B/J` a field in the sense that every `w` with `φ w` a unit is invertible modulo `J`, then
`φ p ∈ 𝔪_R²` forces `p ∈ J²` for `p ∈ J`. -/
theorem IsLocalRing.mem_sq_of_map_mem_sq {B R : Type*} [CommRing B] [CommRing R] [IsLocalRing R]
    (φ : B →+* R) (J : Ideal B) (hJ : J.map φ = IsLocalRing.maximalIdeal R)
    (hsurj : ∀ r : R, ∃ a u, IsUnit (φ u) ∧ r * φ u = φ a)
    (hker : ∀ t, φ t = 0 → ∃ u, IsUnit (φ u) ∧ u * t = 0)
    (hres : ∀ w, IsUnit (φ w) → ∃ d, d * w - 1 ∈ J)
    {p : B} (hp : p ∈ J) (hφp : φ p ∈ IsLocalRing.maximalIdeal R ^ 2) : p ∈ J ^ 2 := by
  have hK : ∀ q ∈ (J ^ 2).map φ, ∃ a ∈ J ^ 2, ∃ u, IsUnit (φ u) ∧ q * φ u = φ a := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, hk, rfl⟩ := hw
      exact ⟨k, hk, 1, by simp, by simp⟩
    | zero => exact ⟨0, Ideal.zero_mem _, 1, by simp, by simp⟩
    | add q₁ q₂ _ _ h₁ h₂ =>
      obtain ⟨a₁, ha₁, u₁, hu₁, e₁⟩ := h₁
      obtain ⟨a₂, ha₂, u₂, hu₂, e₂⟩ := h₂
      refine ⟨a₁ * u₂ + a₂ * u₁, Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha₁)
        (Ideal.mul_mem_right _ _ ha₂), u₁ * u₂, by rw [map_mul]; exact hu₁.mul hu₂, ?_⟩
      rw [map_add, map_mul, map_mul, map_mul, ← e₁, ← e₂]
      ring
    | smul r q _ h =>
      obtain ⟨a, ha, u, hu, e⟩ := h
      obtain ⟨b, v, hv, ev⟩ := hsurj r
      refine ⟨b * a, Ideal.mul_mem_left _ _ ha, v * u, by rw [map_mul]; exact hv.mul hu, ?_⟩
      rw [smul_eq_mul, map_mul, map_mul, ← ev, ← e]
      ring
  have hφp' : φ p ∈ (J ^ 2).map φ := by rwa [Ideal.map_pow, hJ]
  obtain ⟨a, ha, u, hu, e⟩ := hK _ hφp'
  have h0 : φ (p * u - a) = 0 := by rw [map_sub, map_mul, e, sub_self]
  obtain ⟨u', hu', e'⟩ := hker _ h0
  -- `w p ∈ J²` with `w = u' u`, `φ w` a unit
  have hwp : u' * u * p ∈ J ^ 2 := by
    have : u' * u * p = u' * a := by
      have := e'
      rw [mul_sub, sub_eq_zero] at this
      rw [← this]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ ha
  obtain ⟨d, hd⟩ := hres (u' * u) (by rw [map_mul]; exact hu'.mul hu)
  have : p = d * (u' * u * p) - (d * (u' * u) - 1) * p := by ring
  rw [this]
  refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hwp) ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul hd hp

namespace AlgebraicGeometry

open CategoryTheory Limits TensorProduct

/-- **Cotangent space of a base change by a field extension.** See the section docstring.
`Ψ ∘ tensorCotangentHom` is the map `c ⊗ da ↦ c · d(fst^♯ a)` and it is injective. -/
theorem cotangent_baseChange_injective {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : ↥(pullback f g)) {x : X} {y : Y} {s : S} (hx : pullback.fst f g z = x)
    (hy : pullback.snd f g z = y) (hs : f x = s) (hys : g y = s)
    (hS : IsLocalRing.maximalIdeal (S.presheaf.stalk s) = ⊥)
    (hY : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥) (hrat : RationalOver f x) :
    letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) := (f.stalkMapAt hs).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk s) (Y.presheaf.stalk y) := (g.stalkMapAt hys).hom.toAlgebra
    ∃ Ψ : (Ideal.map (Algebra.TensorProduct.includeRight.toRingHom :
          X.presheaf.stalk x →+* (Y.presheaf.stalk y) ⊗[S.presheaf.stalk s] (X.presheaf.stalk x))
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).Cotangent →+
        IsLocalRing.CotangentSpace ((pullback f g).presheaf.stalk z),
      (∀ (c : Y.presheaf.stalk y) (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x)),
        Ψ (Ideal.tensorCotangentHom (S.presheaf.stalk s) (Y.presheaf.stalk y)
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (c ⊗ₜ (IsLocalRing.maximalIdeal _).toCotangent a)) =
          ((pullback.snd f g).stalkMapAt hy).hom c •
            (IsLocalRing.maximalIdeal _).toCotangent
              ⟨((pullback.fst f g).stalkMapAt hx).hom a, map_nonunit _ _ a.2⟩) ∧
      Function.Injective fun t => Ψ (Ideal.tensorCotangentHom (S.presheaf.stalk s)
        (Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) t) := by
  letI : Algebra (S.presheaf.stalk s) (X.presheaf.stalk x) := (f.stalkMapAt hs).hom.toAlgebra
  letI : Algebra (S.presheaf.stalk s) (Y.presheaf.stalk y) := (g.stalkMapAt hys).hom.toAlgebra
  obtain ⟨Φ, hΦ, hsurj, hker⟩ := pullback_stalk_tensor_isLocalization f g z hx hy hs hys
  let Ox := X.presheaf.stalk x
  let Oy := Y.presheaf.stalk y
  let Os := S.presheaf.stalk s
  let Oz := (pullback f g).presheaf.stalk z
  let ψX := ((pullback.fst f g).stalkMapAt hx).hom
  let ψY := ((pullback.snd f g).stalkMapAt hy).hom
  let cm : Oy ⊗[Os] Ox →+* Ox ⊗[Os] Oy := (Algebra.TensorProduct.comm Os Oy Ox).toRingHom
  let cm' : Ox ⊗[Os] Oy →+* Oy ⊗[Os] Ox := (Algebra.TensorProduct.comm Os Oy Ox).symm.toRingHom
  have hcm : ∀ w, cm' (cm w) = w := fun w =>
    (Algebra.TensorProduct.comm Os Oy Ox).symm_apply_apply w
  have hcm' : ∀ w, cm (cm' w) = w := fun w =>
    (Algebra.TensorProduct.comm Os Oy Ox).apply_symm_apply w
  let Φ' : Oy ⊗[Os] Ox →+* Oz := Φ.comp cm
  have hΦ' : ∀ c a, Φ' (c ⊗ₜ a) = ψY c * ψX a := by
    intro c a
    change Φ ((Algebra.TensorProduct.comm Os Oy Ox) (c ⊗ₜ a)) = _
    rw [Algebra.TensorProduct.comm_tmul, hΦ, mul_comm]
  let J : Ideal (Oy ⊗[Os] Ox) := Ideal.map (Algebra.TensorProduct.includeRight.toRingHom :
    Ox →+* Oy ⊗[Os] Ox) (IsLocalRing.maximalIdeal Ox)
  -- `φ(J) = 𝔪_z`
  have hrat' : RationalOver f (pullback.fst f g z) := by rw [hx]; exact hrat
  have hm := maximalIdeal_eq_of_stalkGen pullback.condition (pullback_stalkGen f g z) hrat'
  dsimp only [stalkIdeal] at hm
  have hY' : IsLocalRing.maximalIdeal (Y.presheaf.stalk (pullback.snd f g z)) = ⊥ := by
    rw [hy]; exact hY
  rw [hY', Ideal.map_bot, sup_bot_eq] at hm
  have hJ : J.map Φ' = IsLocalRing.maximalIdeal Oz := by
    rw [hm, Ideal.map_map, ← Scheme.Hom.map_stalkMapAt_maximalIdeal (pullback.fst f g) hx]
    congr 1
    ext a
    change Φ' (1 ⊗ₜ a) = ψX a
    rw [hΦ', map_one, one_mul]
  have hJle : J ≤ (IsLocalRing.maximalIdeal Oz).comap Φ' := by
    rw [← Ideal.map_le_iff_le_comap, hJ]
  -- localization properties for `Φ'`
  have hsurj' : ∀ r : Oz, ∃ a u, IsUnit (Φ' u) ∧ r * Φ' u = Φ' a := by
    intro r
    obtain ⟨a, u, hu, e⟩ := hsurj r
    refine ⟨cm' a, cm' u, ?_, ?_⟩
    · change IsUnit (Φ (cm (cm' u))); rw [hcm']; exact hu
    · change r * Φ (cm (cm' u)) = Φ (cm (cm' a)); rw [hcm', hcm']; exact e
  have hker' : ∀ t, Φ' t = 0 → ∃ u, IsUnit (Φ' u) ∧ u * t = 0 := by
    intro t ht
    obtain ⟨u, hu, e⟩ := hker (cm t) ht
    refine ⟨cm' u, ?_, ?_⟩
    · change IsUnit (Φ (cm (cm' u))); rw [hcm']; exact hu
    · have := congrArg cm' e
      rwa [map_mul, hcm, map_zero] at this
  -- residues: every element is `c ⊗ 1` modulo `J`
  have hres0 : ∀ w : Oy ⊗[Os] Ox, ∃ c : Oy, w - c ⊗ₜ 1 ∈ J := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a =>
      obtain ⟨r₀, hr₀⟩ := hrat a
      obtain ⟨r, hr⟩ := Scheme.Hom.exists_stalkMapAt_eq f hs r₀
      refine ⟨c * algebraMap Os Oy r, ?_⟩
      have e1 : c ⊗ₜ[Os] a - (c * algebraMap Os Oy r) ⊗ₜ[Os] (1 : Ox) =
          (c ⊗ₜ[Os] (1 : Ox)) * ((1 : Oy) ⊗ₜ[Os] (a - algebraMap Os Ox r)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub]
        congr 1
        rw [Algebra.algebraMap_eq_smul_one (A := Ox) r, ← TensorProduct.smul_tmul,
          Algebra.smul_def, mul_comm]
      rw [e1]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      change a - (f.stalkMapAt hs).hom r ∈ _
      rw [hr]; exact hr₀
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨c₁, e₁⟩ := h₁
      obtain ⟨c₂, e₂⟩ := h₂
      refine ⟨c₁ + c₂, ?_⟩
      have : w₁ + w₂ - (c₁ + c₂) ⊗ₜ[Os] (1 : Ox) =
          (w₁ - c₁ ⊗ₜ[Os] (1 : Ox)) + (w₂ - c₂ ⊗ₜ[Os] (1 : Ox)) := by
        rw [TensorProduct.add_tmul]; ring
      rw [this]; exact Ideal.add_mem _ e₁ e₂
  have hres : ∀ w, IsUnit (Φ' w) → ∃ d, d * w - 1 ∈ J := by
    intro w hw
    obtain ⟨c, hc⟩ := hres0 w
    have hcu : IsUnit (ψY c) := by
      have h1 : Φ' w - ψY c ∈ IsLocalRing.maximalIdeal Oz := by
        have := hJle hc
        rw [Ideal.mem_comap, map_sub, hΦ', map_one, mul_one] at this
        exact this
      by_contra hn
      exact (IsLocalRing.mem_maximalIdeal _).mp
        (by have := Ideal.add_mem _ h1 (show ψY c ∈ IsLocalRing.maximalIdeal Oz from hn)
            rwa [sub_add_cancel] at this) hw
    have hcu' : IsUnit c := isUnit_of_map_unit ψY c hcu
    obtain ⟨cu, rfl⟩ := hcu'
    refine ⟨(↑cu⁻¹ : Oy) ⊗ₜ[Os] (1 : Ox), ?_⟩
    have : (↑cu⁻¹ : Oy) ⊗ₜ[Os] (1 : Ox) * w - 1 =
        (↑cu⁻¹ : Oy) ⊗ₜ[Os] (1 : Ox) * (w - (↑cu : Oy) ⊗ₜ[Os] (1 : Ox)) := by
      rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, mul_one,
        Algebra.TensorProduct.one_def]
    rw [this]
    exact Ideal.mul_mem_left _ _ hc
  -- the map `J/J² → 𝔪_z/𝔪_z²`
  set Ψ := Ideal.mapCotangent J (IsLocalRing.maximalIdeal Oz) Φ'.toIntAlgHom hJle with hΨ
  refine ⟨Ψ.toAddMonoidHom, ?_, ?_⟩
  · intro c a
    rw [Ideal.tensorCotangentHom_tmul]
    have hmem : c ⊗ₜ[Os] (a : Ox) ∈ J := by
      have : c ⊗ₜ[Os] (a : Ox) = (c ⊗ₜ[Os] (1 : Ox)) * ((1 : Oy) ⊗ₜ[Os] (a : Ox)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ a.2)
    have e1 : (c • J.toCotangent ⟨1 ⊗ₜ (a : Ox), Ideal.mem_map_of_mem _ a.2⟩) =
        J.toCotangent ⟨c ⊗ₜ (a : Ox), hmem⟩ := by
      rw [← LinearMap.map_smul_of_tower]
      congr 1
      apply Subtype.ext
      change c • ((1 : Oy) ⊗ₜ[Os] (a : Ox)) = c ⊗ₜ[Os] (a : Ox)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change Ψ (c • J.toCotangent ⟨1 ⊗ₜ (a : Ox), Ideal.mem_map_of_mem _ a.2⟩) = _
    rw [e1, hΨ]
    refine (Ideal.mapCotangent_toCotangent _ _ _ _ _).trans ?_
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    change Φ' (c ⊗ₜ (a : Ox)) = ψY c * ψX a
    exact hΦ' c a
  · haveI : Module.Flat Os Oy := by
      letI : Field Os := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hS).toField
      infer_instance
    have hinj1 := Ideal.tensorCotangentHom_injective_of_flat Os Oy (IsLocalRing.maximalIdeal Ox)
    have hinj2 : Function.Injective Ψ := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      obtain ⟨⟨p, hp⟩, rfl⟩ := J.toCotangent_surjective v
      rw [hΨ] at hv
      have hv' := (Ideal.mapCotangent_toCotangent _ _ _ _ _).symm.trans hv
      rw [Ideal.toCotangent_eq_zero] at hv'
      rw [Ideal.toCotangent_eq_zero]
      exact IsLocalRing.mem_sq_of_map_mem_sq Φ' J hJ hsurj' hker' hres hp hv'
    exact fun t₁ t₂ h => hinj1 (hinj2 h)

end AlgebraicGeometry



/-! # Exterior powers commute with passage to the fraction field (Mathlib-only)

For a domain `R` with fraction field `K` and an `R`-module `M` that is a `K`-vector space
(compatibly), `K ⊗_R ⋀^n_R M ≅ ⋀^n_K M` (`extFracEquiv`), `1 ⊗ ιMulti_R v ↔ ιMulti_K v`.
Hence a `K`-basis `b` of `M` gives the `K`-basis `1 ⊗ ιMulti_family R n b` of `K ⊗_R ⋀^n_R M`
(`extFracBasis`). -/

namespace ZInQ.HodgeBC2

open TensorProduct

variable {R K M : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower R K M] (n : ℕ)

/-- `v ↦ 1 ⊗ ιMulti_R v`, `R`-multilinear. -/
noncomputable def extFracAltR : M [⋀^Fin n]→ₗ[R] K ⊗[R] ⋀[R]^n M :=
  (TensorProduct.mk R K (⋀[R]^n M) 1).compAlternatingMap (exteriorPower.ιMulti R n)

omit [IsDomain R] [IsFractionRing R K] [Module K M] [IsScalarTower R K M] in
theorem extFracAltR_apply (v : Fin n → M) :
    extFracAltR (K := K) n v = (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v := rfl

include R in
/-- `K`-homogeneity of an `R`-linear map into a `K`-module, from that of its restriction to `R`. -/
theorem smul_eq_of_frac {N P : Type*} [AddCommGroup N] [Module R N] [Module K N]
    [IsScalarTower R K N] [AddCommGroup P] [Module R P] [Module K P] [IsScalarTower R K P]
    (F : N → P) (hF : ∀ (r : R) x, F (r • x) = r • F x) (c : K) (x : N) :
    F (c • x) = c • F x := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
  have hs : (algebraMap R K (s : R)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have key : (s : R) • F (IsLocalization.mk' K a s • x) = (a : R) • F x := by
    rw [← hF, ← algebraMap_smul K, smul_smul, IsLocalization.mk'_spec', algebraMap_smul, hF]
  have key' : algebraMap R K (s : R) • F (IsLocalization.mk' K a s • x) =
      algebraMap R K (s : R) • (IsLocalization.mk' K a s • F x) := by
    rw [algebraMap_smul, key, smul_smul, IsLocalization.mk'_spec', algebraMap_smul]
  exact smul_right_injective P hs key'

/-- `v ↦ 1 ⊗ ιMulti_R v` is `K`-multilinear. -/
noncomputable def extFracAlt : M [⋀^Fin n]→ₗ[K] K ⊗[R] ⋀[R]^n M where
  toFun v := (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v
  map_update_add' v i x y := (extFracAltR (K := K) n).map_update_add v i x y
  map_update_smul' v i c x := by
    classical
    have := smul_eq_of_frac (R := R) (K := K)
      (fun y : M => (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n (Function.update v i y))
      (fun r y => (extFracAltR (K := K) n).map_update_smul v i r y) c x
    convert this using 2
  map_eq_zero_of_eq' v i j h hij := (extFracAltR (K := K) n).map_eq_zero_of_eq v h hij

/-- `⋀^n_K M → K ⊗_R ⋀^n_R M`. -/
noncomputable def extFracTo : ⋀[K]^n M →ₗ[K] K ⊗[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (extFracAlt (R := R) n)

theorem extFracTo_ιMulti (v : Fin n → M) :
    extFracTo (R := R) (K := K) n (exteriorPower.ιMulti K n v) =
      (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- `⋀^n_R M → ⋀^n_K M`, induced by `ιMulti_K`. -/
noncomputable def extFracJ : ⋀[R]^n M →ₗ[R] ⋀[K]^n M :=
  exteriorPower.alternatingMapLinearEquiv
    { ((exteriorPower.ιMulti K n (M := M)).toMultilinearMap.restrictScalars R) with
      map_eq_zero_of_eq' := fun v _ _ h hij => (exteriorPower.ιMulti K n).map_eq_zero_of_eq v h hij }

/-- `K ⊗_R ⋀^n_R M → ⋀^n_K M`. -/
noncomputable def extFracFrom : K ⊗[R] ⋀[R]^n M →ₗ[K] ⋀[K]^n M :=
  (extFracJ (R := R) (K := K) n).liftBaseChange K

theorem extFracFrom_tmul (c : K) (v : Fin n → M) :
    extFracFrom (R := R) (K := K) n (c ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      c • exteriorPower.ιMulti K n v := by
  rw [extFracFrom, LinearMap.liftBaseChange_tmul]
  congr 1
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- **`K ⊗_R ⋀^n_R M ≅ ⋀^n_K M`.** -/
noncomputable def extFracEquiv : ⋀[K]^n M ≃ₗ[K] K ⊗[R] ⋀[R]^n M :=
  LinearEquiv.ofLinearMap (extFracTo (R := R) n) (extFracFrom (R := R) n)
    (by
      apply TensorProduct.AlgebraTensorModule.curry_injective
      apply LinearMap.ext_ring
      apply exteriorPower.linearMap_ext
      ext v
      simp only [AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply,
        TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.restrictScalars_apply, LinearMap.id_apply,
        TensorProduct.curry_apply]
      rw [extFracFrom_tmul, one_smul, extFracTo_ιMulti])
    (by
      apply exteriorPower.linearMap_ext
      ext v
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.id_apply]
      rw [extFracTo_ιMulti, extFracFrom_tmul, one_smul])

theorem extFracEquiv_ιMulti (v : Fin n → M) :
    extFracEquiv (R := R) (K := K) n (exteriorPower.ιMulti K n v) =
      (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v :=
  extFracTo_ιMulti n v

/-- **The basis `1 ⊗ ιMulti_family R n b` of `K ⊗_R ⋀^n_R M`** for a `K`-basis `b` of `M`. -/
noncomputable def extFracBasis {I : Type*} [LinearOrder I] (b : Module.Basis I K M) :
    Module.Basis (Set.powersetCard I n) K (K ⊗[R] ⋀[R]^n M) :=
  (b.exteriorPower n).map (extFracEquiv (R := R) n)

theorem extFracBasis_apply {I : Type*} [LinearOrder I] (b : Module.Basis I K M)
    (s : Set.powersetCard I n) :
    extFracBasis (R := R) n b s = (1 : K) ⊗ₜ[R] exteriorPower.ιMulti_family R n b s := by
  rw [extFracBasis, Module.Basis.map_apply, exteriorPower.basis_apply]
  exact extFracEquiv_ιMulti n _

end ZInQ.HodgeBC2



/-! # hodge-bc2: `HodgeBCInjective` proved

* `cotL`: the `L`-vector space structure on `ω_{A_L} = 𝔪_ξ/𝔪_ξ²`, through
  `φ : L ≅ κ(η) → 𝒪_{𝒢,ξ}` (`η` the generic point of `Spec 𝓞_L`, `κ(η)` its function field);
* `bcCot_smulL`: `π^*` is semilinear over `L → L'`;
* `bcCot_core`: `π^*` maps `L`-independent vectors to `𝓞_{L'}`-independent vectors
  (`cotangent_baseChange_injective` of infra-stalks at the generic unit, flatness of `κ(η')/κ(η)`);
* `bcCot_basis`: an `L`-basis `b` of `ω_{A_L}` gives the `L'`-basis `π^* ∘ b` of `ω_{A_{L'}}`
  (with `cotangentSpanBC`);
* `hodgeBCInjective`: `ψ = bcHodge` maps the basis `1 ⊗ ιMulti_family b` of the Hodge space
  (`extFracBasis`) to the basis `1 ⊗ ιMulti_family (π^* ∘ b)`, hence is injective and preserves
  `finrank`. -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open scoped TensorProduct

section HodgeBC2

variable {K : Type} [Field K] {A : AbVar K}

theorem genericPt_eq_genericPoint (L : Type) [Field L] [NumberField L] :
    genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) := by
  rw [genericPoint_eq_bot_of_affine]; rfl

/-- The stalk map at named points on germs. -/
theorem stalkMapAt_germ' {X Y : Scheme.{0}} (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y)
    (U : Y.Opens) (hy : y ∈ U) (hy' : f x ∈ U) (s : Γ(Y, U)) :
    f.stalkMapAt h (Y.presheaf.germ U y hy s) = f.stalkMap x (Y.presheaf.germ U (f x) hy' s) := by
  subst h; rw [Scheme.Hom.stalkMapAt_rfl]

/-- The function field of `Spec 𝓞_L`. -/
noncomputable abbrev FF (L : Type) [Field L] [NumberField L] : CommRingCat :=
  (Spec (CommRingCat.of (𝓞 L))).functionField

noncomputable instance (L : Type) [Field L] [NumberField L] : Algebra (𝓞 L) (FF L) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫ (Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤
      (genericPoint (Spec (CommRingCat.of (𝓞 L)))) trivial).hom.toAlgebra

instance (L : Type) [Field L] [NumberField L] : IsFractionRing (𝓞 L) (FF L) := by
  have := functionField_isFractionRing_of_affine (CommRingCat.of (𝓞 L))
  exact this

theorem algebraMap_FF (L : Type) [Field L] [NumberField L] (a : 𝓞 L) :
    algebraMap (𝓞 L) (FF L) a = (Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤
      (genericPoint (Spec (CommRingCat.of (𝓞 L)))) trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) := rfl

/-- `L ≅ κ(η)`. -/
noncomputable def σFF (L : Type) [Field L] [NumberField L] : L ≃ₐ[𝓞 L] FF L :=
  IsLocalization.algEquiv (nonZeroDivisors (𝓞 L)) L (FF L)

theorem hom_genericUnit' {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) :
    𝒢.G.hom 𝒢.genericUnit = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
  (hom_genericUnit 𝒢).trans (genericPt_eq_genericPoint L)

/-- `φ : L → 𝒪_{𝒢,ξ}` (through `κ(η)`). -/
noncomputable def φL {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L) :
    L →+* 𝒢.genStalk :=
  (𝒢.G.hom.stalkMapAt (hom_genericUnit' 𝒢)).hom.comp (σFF L).toRingEquiv.toRingHom

theorem φL_algebraMap {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (a : 𝓞 L) : φL 𝒢 (algebraMap (𝓞 L) L a) = 𝒢.structMap a := by
  unfold φL
  rw [RingHom.comp_apply]
  change (𝒢.G.hom.stalkMapAt (hom_genericUnit' 𝒢)).hom ((σFF L) (algebraMap (𝓞 L) L a)) = _
  rw [AlgEquiv.commutes, algebraMap_FF, structMap_eq_stalkMap]
  exact stalkMapAt_germ' _ _ ⊤ trivial trivial _

/-- **The `L`-vector space structure on `ω_{A_L}`.** -/
noncomputable abbrev cotL {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : Module L 𝒢.cotangent :=
  Module.compHom _ (φL 𝒢)

theorem cotL_smul {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (c : L) (v : 𝒢.cotangent) :
    (letI := cotL 𝒢; c • v) = φL 𝒢 c • v := rfl

theorem cotL_isScalarTower {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : letI := cotL 𝒢; IsScalarTower (𝓞 L) L 𝒢.cotangent := by
  letI := cotL 𝒢
  refine ⟨fun r c v => ?_⟩
  rw [cotL_smul, cotL_smul, Algebra.smul_def, map_mul, φL_algebraMap, mul_smul]
  rfl

/-- `mapCotangent` is semilinear along the ring map. -/
theorem mapCotangent_smul' {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (F : R →+* S) (hF : I ≤ J.comap F.toIntAlgHom) (r : R) (x : I.Cotangent) :
    Ideal.mapCotangent I J F.toIntAlgHom hF (r • x) =
      F r • Ideal.mapCotangent I J F.toIntAlgHom hF x := by
  obtain ⟨m, rfl⟩ := I.toCotangent_surjective x
  rw [← map_smul, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, ← map_smul]
  congr 1
  apply Subtype.ext
  simp only [SetLike.val_smul, smul_eq_mul, map_mul, RingHom.toIntAlgHom_apply]

variable {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}

theorem bcCot_smul_genStalk (he : IsMonBC 𝒢 𝒢' e) (r : 𝒢.genStalk) (v : 𝒢.cotangent) :
    bcCot he (r • v) = bcMap he r • bcCot he v :=
  mapCotangent_smul' (IsLocalRing.maximalIdeal 𝒢.genStalk) (IsLocalRing.maximalIdeal 𝒢'.genStalk)
    (bcMap he).hom (fun t ht => bcMap_mem_maximalIdeal he t ht) r v

omit [NumberField L] [NumberField L'] in
theorem algebraMap_ringOfIntegers_coe (a : 𝓞 L) :
    algebraMap L L' (algebraMap (𝓞 L) L a) =
      algebraMap (𝓞 L') L' (algebraMap (𝓞 L) (𝓞 L') a) := rfl

theorem bcMap_φL (he : IsMonBC 𝒢 𝒢' e) (c : L) :
    bcMap he (φL 𝒢 c) = φL 𝒢' (algebraMap L L' c) := by
  have : (bcMap he).hom.comp (φL 𝒢) = (φL 𝒢').comp (algebraMap L L') := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 L))
    ext a
    simp only [RingHom.comp_apply]
    rw [φL_algebraMap, bcMap_structMap, algebraMap_ringOfIntegers_coe, φL_algebraMap]
  exact congrArg (fun F => F c) this

/-- `π^*` is semilinear over `L → L'`. -/
theorem bcCot_smulL (he : IsMonBC 𝒢 𝒢' e) (c : L) (v : 𝒢.cotangent) :
    bcCot he (letI := cotL 𝒢; c • v) = (letI := cotL 𝒢'; algebraMap L L' c • bcCot he v) := by
  rw [cotL_smul, cotL_smul, bcCot_smul_genStalk, bcMap_φL]

/-- A local ring isomorphism induces an injective map on cotangent spaces. -/
theorem mapCotangent_injective_of_isIso {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S]
    (E : R ⟶ S) [IsIso E] (hE : IsLocalRing.maximalIdeal R ≤
      (IsLocalRing.maximalIdeal S).comap E.hom.toIntAlgHom) :
    Function.Injective (Ideal.mapCotangent (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal S) E.hom.toIntAlgHom hE) := by
  have hE' : IsLocalRing.maximalIdeal S ≤
      (IsLocalRing.maximalIdeal R).comap (inv E).hom.toIntAlgHom := fun t ht =>
    map_nonunit (inv E).hom t ht
  have hinv : ∀ x, Ideal.mapCotangent _ _ (inv E).hom.toIntAlgHom hE'
      (Ideal.mapCotangent _ _ E.hom.toIntAlgHom hE x) = x := by
    intro x
    obtain ⟨m, rfl⟩ := (IsLocalRing.maximalIdeal R).toCotangent_surjective x
    rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    change (inv E).hom (E.hom m) = m
    rw [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]
  intro x y hxy
  rw [← hinv x, ← hinv y, hxy]

/-- **Core of the injectivity of cotangent base change.** `𝓞_{L'}`-combinations of pull-backs of
`L`-independent cotangent vectors vanish only trivially. From infra-stalks'
`cotangent_baseChange_injective` at the generic unit and flatness of `κ(η')` over `κ(η)`. -/
theorem bcCot_core (he : IsMonBC 𝒢 𝒢' e) {I : Type} (b : I → 𝒢.cotangent)
    (hb : letI := cotL 𝒢; LinearIndependent L b) (s : Finset I) (a : I → 𝓞 L')
    (h : ∑ i ∈ s, a i • bcCot he (b i) = 0) : ∀ i ∈ s, a i = 0 := by
  classical
  set ξ' := 𝒢'.genericUnit
  set z := e.hom.left ξ'
  set y0 := genericPoint (Spec (CommRingCat.of (𝓞 L')))
  set s0 := genericPoint (Spec (CommRingCat.of (𝓞 L)))
  have hx : pullback.fst 𝒢.G.hom (bO L L') z = 𝒢.genericUnit := by
    rw [← Scheme.Hom.comp_apply]; exact bcProj_genericUnit he
  have hsnd : e.hom.left ≫ pullback.snd 𝒢.G.hom (bO L L') = 𝒢'.G.hom := Over.w e.hom
  have hy : pullback.snd 𝒢.G.hom (bO L L') z = y0 := by
    rw [← Scheme.Hom.comp_apply, hsnd]; exact hom_genericUnit' 𝒢'
  have hs : 𝒢.G.hom 𝒢.genericUnit = s0 := hom_genericUnit' 𝒢
  have hys : bO L L' y0 = s0 := by
    simp only [y0, s0, ← genericPt_eq_genericPoint]; exact bO_genericPt
  have hS := maximalIdeal_stalk_genericPt L s0 (genericPt_eq_genericPoint L).symm
  have hY := maximalIdeal_stalk_genericPt L' y0 (genericPt_eq_genericPoint L').symm
  have hrat := rationalOver_genericUnit 𝒢
  obtain ⟨Ψ, hΨ, hinj⟩ := cotangent_baseChange_injective 𝒢.G.hom (bO L L') z hx hy hs hys hS hY hrat
  let Os := (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s0
  let Ox := 𝒢.G.left.presheaf.stalk 𝒢.genericUnit
  let Oy := (Spec (CommRingCat.of (𝓞 L'))).presheaf.stalk y0
  letI : Algebra Os Ox := (𝒢.G.hom.stalkMapAt hs).hom.toAlgebra
  letI : Algebra Os Oy := ((bO L L').stalkMapAt hys).hom.toAlgebra
  letI : Field Os := inferInstanceAs (Field (Spec (CommRingCat.of (𝓞 L))).functionField)
  -- germs of `𝓞_{L'}` at the generic point
  let germY : 𝓞 L' → Oy := fun r => (Spec (CommRingCat.of (𝓞 L'))).presheaf.germ ⊤ y0 trivial
    ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv r)
  have germY_inj : ∀ r, germY r = 0 → r = 0 := by
    intro r hr
    by_contra hne
    have hu := isUnit_germ_genericPt L' y0 (genericPt_eq_genericPoint L').symm r hne
    exact hu.ne_zero hr
  -- `b` is independent over `κ(η)`
  let bb : I → (IsLocalRing.maximalIdeal Ox).Cotangent := b
  have hbOs : LinearIndependent Os bb := by
    letI := cotL 𝒢
    rw [linearIndependent_iff'] at hb ⊢
    intro t c hc i hi
    have key := hb t (fun j => (σFF L).symm (c j)) (by
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hc
      rw [cotL_smul]
      change (𝒢.G.hom.stalkMapAt (hom_genericUnit' 𝒢)).hom ((σFF L) ((σFF L).symm (c j))) • b j = _
      rw [AlgEquiv.apply_symm_apply]
      rfl) i hi
    simpa using key
  have hli := Module.Flat.linearIndependent_one_tmul (S := Oy) hbOs
  -- the element of `𝒪_{η'} ⊗ 𝔪_ξ/𝔪_ξ²`
  set t : Oy ⊗[Os] (IsLocalRing.maximalIdeal Ox).Cotangent :=
    ∑ i ∈ s, germY (a i) • ((1 : Oy) ⊗ₜ[Os] bb i)
  have ht0 : t = 0 := by
    choose β hβ using fun i => (IsLocalRing.maximalIdeal Ox).toCotangent_surjective (bb i)
    let E := e.hom.left.stalkMap ξ'
    have hE : IsLocalRing.maximalIdeal ((pullback 𝒢.G.hom (bO L L')).presheaf.stalk z) ≤
        (IsLocalRing.maximalIdeal 𝒢'.genStalk).comap E.hom.toIntAlgHom := fun r hr =>
      map_nonunit E.hom r hr
    let Ecot := Ideal.mapCotangent _ _ E.hom.toIntAlgHom hE
    have hEinj : Function.Injective Ecot := mapCotangent_injective_of_isIso E hE
    -- `E ∘ ψY` on germs of `𝓞_{L'}` is the structure map of `𝒢'`
    have hEY : ∀ r : 𝓞 L', E.hom ((pullback.snd 𝒢.G.hom (bO L L')).stalkMapAt hy |>.hom
        (germY r)) = 𝒢'.structMap r := by
      intro r
      have h1 := stalkMapAt_comp_apply' e.hom.left (pullback.snd 𝒢.G.hom (bO L L'))
        (rfl : e.hom.left ξ' = z) hy (by rw [hsnd]; exact hom_genericUnit' 𝒢') (germY r)
      rw [Scheme.Hom.stalkMapAt_rfl] at h1
      change (e.hom.left.stalkMap ξ').hom _ = _
      rw [h1, Scheme.Hom.stalkMapAt_congr hsnd _ (hom_genericUnit' 𝒢'), structMap_eq_stalkMap]
      exact stalkMapAt_germ' _ _ ⊤ trivial trivial _
    -- `E ∘ ψX` is `bcMap`
    have hEX : ∀ m : Ox, E.hom ((pullback.fst 𝒢.G.hom (bO L L')).stalkMapAt hx |>.hom m) =
        bcMap he m := by
      intro m
      have h1 := stalkMapAt_comp_apply' e.hom.left (pullback.fst 𝒢.G.hom (bO L L'))
        (rfl : e.hom.left ξ' = z) hx (bcProj_genericUnit he) m
      rw [Scheme.Hom.stalkMapAt_rfl] at h1
      change (e.hom.left.stalkMap ξ').hom _ = _
      rw [h1]
      rfl
    apply hinj
    simp only [map_zero]
    apply hEinj
    rw [map_zero]
    simp only [t, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
    have hb' : b i = 𝒢.dCls (β i) := (hβ i).symm
    rw [hb', bcCot_dCls, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
      show bb i = (IsLocalRing.maximalIdeal Ox).toCotangent (β i) from (hβ i).symm, hΨ]
    simp only [Ecot]
    rw [mapCotangent_smul', Ideal.mapCotangent_toCotangent, hEY]
    refine congrArg (fun v : 𝒢'.cotangent => 𝒢'.structMap (a i) • v) ?_
    unfold GroupModel.dCls
    congr 1
    exact Subtype.ext (hEX _)
  intro i hi
  rw [linearIndependent_iff'] at hli
  exact germY_inj _ (hli s (fun j => germY (a j)) ht0 i hi)

/-- `π^*` maps an `L`-basis to an `L'`-independent family. -/
theorem bcCot_linearIndependent (he : IsMonBC 𝒢 𝒢' e) {I : Type}
    (b : letI := cotL 𝒢; Module.Basis I L 𝒢.cotangent) :
    letI := cotL 𝒢'; LinearIndependent L' (fun i => bcCot he (b i)) := by
  classical
  letI := cotL 𝒢
  letI := cotL 𝒢'
  haveI := cotL_isScalarTower 𝒢'
  rw [linearIndependent_iff']
  intro s c hc i hi
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 L')) s c
  let a : I → 𝓞 L' := fun j => if h : j ∈ s then (hd j h).choose else 0
  have ha : ∀ j ∈ s, algebraMap (𝓞 L') L' (a j) = (d : 𝓞 L') • c j := by
    intro j hj
    simp only [a, dif_pos hj]
    exact (hd j hj).choose_spec
  have hsum : ∑ j ∈ s, a j • bcCot he (b j) = 0 := by
    have : ∑ j ∈ s, a j • bcCot he (b j) = (d : 𝓞 L') • ∑ j ∈ s, c j • bcCot he (b j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← algebraMap_smul L' (a j), ha j hj, smul_assoc]
    rw [this, hc, smul_zero]
  have h0 := bcCot_core he (fun j => b j) b.linearIndependent s a hsum i hi
  have h1 := ha i hi
  rw [h0, map_zero, Algebra.smul_def] at h1
  have hd0 : algebraMap (𝓞 L') L' (d : 𝓞 L') ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  exact (mul_eq_zero.mp h1.symm).resolve_left hd0

/-- `π^*` of an `L`-basis spans `ω_{A_{L'}}` over `L'` (from `cotangentSpanBC`). -/
theorem bcCot_span [IsScalarTower K L L'] (he : IsMonBC 𝒢 𝒢' e) {I : Type}
    (b : letI := cotL 𝒢; Module.Basis I L 𝒢.cotangent) :
    letI := cotL 𝒢'; ⊤ ≤ Submodule.span L' (Set.range (fun i => bcCot he (b i))) := by
  letI := cotL 𝒢
  letI := cotL 𝒢'
  haveI := cotL_isScalarTower 𝒢'
  set W := Submodule.span L' (Set.range (fun i => bcCot he (b i)))
  have hbc : ∀ u : 𝒢.cotangent, bcCot he u ∈ W := by
    intro u
    have hu : u ∈ Submodule.span L (Set.range b) := b.mem_span u
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul c x _ hx =>
      rw [bcCot_smulL]
      exact W.smul_mem _ hx
  have hspan := cotangentSpanBC K A L L' 𝒢 𝒢' e he
  intro v _
  have hv : v ∈ Submodule.span (𝓞 L') (Set.range (bcCot he)) := by rw [hspan]; trivial
  have hle : Submodule.span (𝓞 L') (Set.range (bcCot he)) ≤ W.restrictScalars (𝓞 L') := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    exact hbc u
  exact hle hv

/-- **`π^*` of an `L`-basis of `ω_{A_L}` is an `L'`-basis of `ω_{A_{L'}}`.** -/
noncomputable def bcCotBasis [IsScalarTower K L L'] (he : IsMonBC 𝒢 𝒢' e) {I : Type}
    (b : letI := cotL 𝒢; Module.Basis I L 𝒢.cotangent) :
    letI := cotL 𝒢'; Module.Basis I L' 𝒢'.cotangent :=
  letI := cotL 𝒢'
  Module.Basis.mk (bcCot_linearIndependent he b) (bcCot_span he b)

theorem bcCotBasis_apply [IsScalarTower K L L'] (he : IsMonBC 𝒢 𝒢' e) {I : Type}
    (b : letI := cotL 𝒢; Module.Basis I L 𝒢.cotangent) (i : I) :
    bcCotBasis he b i = bcCot he (b i) := by
  letI := cotL 𝒢'
  exact Module.Basis.mk_apply _ _ i

end HodgeBC2

/-- **`HodgeBCInjective` holds** (height-bc glue BC-alg; statement verbatim). The natural map
`ψ = bcHodge` sends the `L`-basis `1 ⊗ ιMulti_family b` of the Hodge space of `𝒢` (`b` an `L`-basis
of `ω_{A_L}`, `extFracBasis`) to the `L'`-basis `1 ⊗ ιMulti_family (π^* ∘ b)` of that of `𝒢'`
(`bcCotBasis`); it is `L`-semilinear, hence injective, and both spaces have bases indexed by the
same set, hence the same `finrank`. -/
theorem hodgeBCInjective : HodgeBCInjective := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he g
  classical
  letI := cotL 𝒢
  letI := cotL 𝒢'
  haveI := cotL_isScalarTower 𝒢
  haveI := cotL_isScalarTower 𝒢'
  let I := Module.Basis.ofVectorSpaceIndex L 𝒢.cotangent
  let b : Module.Basis I L 𝒢.cotangent := Module.Basis.ofVectorSpace L 𝒢.cotangent
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let b' := bcCotBasis he b
  let B := ZInQ.HodgeBC2.extFracBasis (R := 𝓞 L) g b
  let B' := ZInQ.HodgeBC2.extFracBasis (R := 𝓞 L') g b'
  have hψ : ∀ s, bcHodge he g (B s) = B' s := by
    intro s
    simp only [B, B', ZInQ.HodgeBC2.extFracBasis_apply]
    rw [bcHodge_tmul, map_one]
    congr 1
    simp only [exteriorPower.ιMulti_family]
    rw [bcExt_ιMulti]
    congr 1
    funext j
    simp only [Function.comp_apply, b', bcCotBasis_apply]
  constructor
  · intro v hv hψv
    apply hv
    have hsum : bcHodge he g v =
        ∑ t ∈ (B.repr v).support, algebraMap L L' (B.repr v t) • B' t := by
      conv_lhs => rw [← B.linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [bcHodge_smul, hψ]
    rw [hψv] at hsum
    have h0 := (linearIndependent_iff'.mp B'.linearIndependent) _ _ hsum.symm
    rw [← B.linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun t ht => ?_
    have : B.repr v t = 0 := (algebraMap L L').injective (by rw [h0 t ht, map_zero])
    rw [this, zero_smul]
  · rw [Module.finrank_eq_nat_card_basis B, Module.finrank_eq_nat_card_basis B']

end ZInQ.HeightBC





/-! # hodge-bc2: `OmegaBaseChange` from the localization property of `omegaAt`

* Step A (`mem_of_forall_locSub`): a vector lies in a submodule `N` over a ring `R` if for every
  maximal ideal `P` some `d ∉ P` has `d • v ∈ N`.
* Step B (`omegaAt_bc_local`, conormal base change at a point `s'` of `Spec 𝓞_{L'}`): every
  `v ∈ (ω_{𝒢'})_{s'}` has a multiple `d • v`, `d ∉ s'`, in `𝓞_{L'} · π^*((ω_𝒢)_{s})`, `s` the image
  of `s'`. From infra-stalks' `pullback_stalkGen`: `I'_{e'(s')} = π^*(I_{e(s)}) · 𝒪_{𝒢',e'(s')}`.
* `OmegaLocalization` (named Prop, one group model): `(ω_𝒢)_s` is the localization of `ω_𝒢` at `s`.
* `omegaBaseChange_of_localization : OmegaLocalization → OmegaBaseChange`. -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open scoped TensorProduct

/-! ### Step A: local–global for submodules -/

/-- `{v | ∃ d ∉ P, d • v ∈ N}`. -/
def locSub {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (P : Ideal R) [P.IsPrime]
    (N : Submodule R M) : Submodule R M where
  carrier := {v | ∃ d : R, d ∉ P ∧ d • v ∈ N}
  add_mem' := by
    rintro v w ⟨d₁, h₁, hv⟩ ⟨d₂, h₂, hw⟩
    refine ⟨d₁ * d₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim h₁ h₂, ?_⟩
    have : (d₁ * d₂) • (v + w) = d₂ • (d₁ • v) + d₁ • (d₂ • w) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm d₂ d₁]
    rw [this]
    exact N.add_mem (N.smul_mem _ hv) (N.smul_mem _ hw)
  zero_mem' := ⟨1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr h),
    by rw [smul_zero]; exact N.zero_mem⟩
  smul_mem' := by
    rintro c v ⟨d, hd, hv⟩
    exact ⟨d, hd, by rw [smul_comm]; exact N.smul_mem c hv⟩

theorem mem_locSub {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (P : Ideal R)
    [P.IsPrime] (N : Submodule R M) (v : M) : v ∈ locSub P N ↔ ∃ d : R, d ∉ P ∧ d • v ∈ N :=
  Iff.rfl

/-- **Step A.** -/
theorem mem_of_forall_locSub {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (v : M)
    (h : ∀ (P : Ideal R) (hP : P.IsMaximal), haveI := hP.isPrime; v ∈ locSub P N) : v ∈ N := by
  let J : Ideal R := N.comap (LinearMap.toSpanSingleton R M v)
  by_cases hJ : J = ⊤
  · have : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
    simpa [J] using this
  · obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
    obtain ⟨d, hd, hdv⟩ := h P hP
    exact absurd (hJP (by simpa [J] using hdv)) hd

/-! ### Dedekind lemmas -/

/-- A nonzero ideal of a Dedekind domain that is saturated at a nonzero prime `P₁` is not contained
in any prime `P ≠ P₁` (it contains a power of `P₁`, by the DVR `R_{P₁}`). -/
theorem exists_mem_not_mem_of_sat {R : Type*} [CommRing R] [IsDedekindDomain R] (P₁ P : Ideal R)
    [P₁.IsPrime] [hP : P.IsPrime] (hP₁ : P₁ ≠ ⊥) (hne : P ≠ P₁) (J : Ideal R) (hJ : J ≠ ⊥)
    (hsat : ∀ u ∉ P₁, ∀ d, u * d ∈ J → d ∈ J) : ∃ d ∈ J, d ∉ P := by
  by_contra hcon
  push_neg at hcon
  have hJP : J ≤ P := fun d hd => hcon d hd
  let Rp := Localization.AtPrime P₁
  haveI : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP₁ Rp
  have hinj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp P₁.primeCompl_le_nonZeroDivisors
  have hmap : J.map (algebraMap R Rp) ≠ ⊥ := by
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    intro h
    apply hc0
    have : algebraMap R Rp c = 0 := by
      rw [← Ideal.mem_bot, ← h]; exact Ideal.mem_map_of_mem _ hc
    exact hinj (this.trans (map_zero _).symm)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap hϖ
  have hle : P₁ ^ n ≤ J := by
    intro a ha
    have hpow : (P₁ ^ n).map (algebraMap R Rp) = Ideal.span {ϖ ^ n} := by
      rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, hϖ.maximalIdeal_eq,
        Ideal.span_singleton_pow]
    have ha' : algebraMap R Rp a ∈ J.map (algebraMap R Rp) := by
      rw [hn, ← hpow]; exact Ideal.mem_map_of_mem _ ha
    obtain ⟨⟨j, u⟩, hju⟩ := (IsLocalization.mem_map_algebraMap_iff P₁.primeCompl Rp).mp ha'
    have hau : (u : R) * a = j := hinj (by rw [map_mul, mul_comm]; exact hju)
    exact hsat u u.2 a (hau ▸ j.2)
  have h1 : P₁ ≤ P := Ideal.IsPrime.le_of_pow_le (hle.trans hJP)
  have hmax : P₁.IsMaximal := Ideal.IsPrime.isMaximal ‹_› hP₁
  exact hne (hmax.eq_of_le hP.ne_top h1).symm

/-- A closed subset of `Spec 𝓞_L` avoiding the generic point is finite. -/
theorem finite_of_isClosed_not_genericPt (L : Type) [Field L] [NumberField L]
    (Z : Set (Spec (CommRingCat.of (𝓞 L)))) (hZ : IsClosed Z) (hg : genericPt L ∉ Z) :
    Z.Finite := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    (show Set (PrimeSpectrum (𝓞 L)) from Z)).mp hZ
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hg
    change (genericPt L : PrimeSpectrum (𝓞 L)) ∈ (show Set (PrimeSpectrum (𝓞 L)) from Z)
    rw [hI]
    intro x hx
    simp only [Submodule.bot_coe, Set.mem_singleton_iff] at hx
    rw [hx]; exact Ideal.zero_mem _
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (𝓞 L) I
  refine (hfin.preimage (Set.injOn_of_injective
    (fun p q (h : (p : PrimeSpectrum (𝓞 L)).asIdeal = (q : PrimeSpectrum (𝓞 L)).asIdeal) =>
      PrimeSpectrum.ext h))).subset ?_
  intro p hp
  have hp' : (p : PrimeSpectrum (𝓞 L)) ∈ PrimeSpectrum.zeroLocus (I : Set (𝓞 L)) := by
    rw [← hI]; exact hp
  have hIp : I ≤ (p : PrimeSpectrum (𝓞 L)).asIdeal := fun x hx => hp' hx
  refine ⟨⟨(p : PrimeSpectrum (𝓞 L)).isPrime, hIp⟩, fun q hq hqp => ?_⟩
  have hq0 : q ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hq.2))
  have hqmax : q.IsMaximal := Ideal.IsPrime.isMaximal hq.1 hq0
  exact (hqmax.eq_of_le (p : PrimeSpectrum (𝓞 L)).isPrime.ne_top hqp).symm.le

section OmegaBC

variable {K : Type} [Field K] {A : AbVar K}

/-! ### Sections and stalks -/

theorem hom_unitSection {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (s : Spec (CommRingCat.of (𝓞 L))) : 𝒢.G.hom (𝒢.unitSection s) = s := by
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]; rfl

/-- `e^♯ ∘ G^♯ = id` on stalks at a point of the section. -/
theorem unitSection_stalkMapAt_hom {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) {s : Spec (CommRingCat.of (𝓞 L))} {x : 𝒢.G.left}
    (hx : 𝒢.unitSection s = x) (hG : 𝒢.G.hom x = s)
    (gam : (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) :
    (𝒢.unitSection.stalkMapAt hx).hom ((𝒢.G.hom.stalkMapAt hG).hom gam) = gam := by
  have hfg : (𝒢.unitSection ≫ 𝒢.G.hom) s = s := by rw [Scheme.Hom.comp_apply, hx, hG]
  rw [stalkMapAt_comp_apply' _ _ hx hG hfg,
    Scheme.Hom.stalkMapAt_congr (unitSection_comp_hom 𝒢) hfg
      (show (𝟙 (Spec (CommRingCat.of (𝓞 L)))) s = s from rfl),
    Scheme.Hom.stalkMapAt_id]
  rfl

/-- Elements of `I_{e(s)}` specialize into `𝔪_ξ`. -/
theorem spec_mem_of_ker {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (s : Spec (CommRingCat.of (𝓞 L))) (f : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    (hf : (𝒢.unitSection.stalkMap s).hom f = 0) :
    𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk := by
  intro hu
  have h1 := hu.map (𝒢.unitSection.stalkMap (genericPt L)).hom
  have hsp : genericPt L ⤳ s := (PrimeSpectrum.le_iff_specializes (genericPt L) s).mp bot_le
  have h2 := Scheme.Hom.stalkSpecializes_stalkMap_apply 𝒢.unitSection (genericPt L) s hsp f
  have h3 : (𝒢.unitSection.stalkMap (genericPt L)).hom
      (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f) = 0 := by
    have h2' := h2
    rw [hf, map_zero] at h2'
    exact h2'
  have h4 : IsUnit ((𝒢.unitSection.stalkMap (genericPt L)).hom
      (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f)) := h1
  rw [h3] at h4
  exact not_isUnit_zero h4

/-- `structMap a` is the specialization of `G^♯(a)` at any point of the section. -/
theorem structMap_eq_spec {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (s : Spec (CommRingCat.of (𝓞 L))) (a : 𝓞 L) :
    𝒢.structMap a = 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      ((𝒢.G.hom.stalkMapAt (hom_unitSection 𝒢 s)).hom
        ((Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ s trivial
          ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a))) := by
  rw [stalkMapAt_germ' _ _ ⊤ (by trivial) (by trivial)]
  erw [Scheme.Hom.germ_stalkMap_apply 𝒢.G.hom ⊤ (𝒢.unitSection s) (by trivial),
    TopCat.Presheaf.germ_stalkSpecializes_apply]
  rfl

/-- `toCotangent (r x) = r • toCotangent x`. -/
theorem toCotangent_mul {R : Type*} [CommRing R] [IsLocalRing R] (r x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hrx : r * x ∈ IsLocalRing.maximalIdeal R) :
    (IsLocalRing.maximalIdeal R).toCotangent ⟨r * x, hrx⟩ =
      r • (IsLocalRing.maximalIdeal R).toCotangent ⟨x, hx⟩ := by
  rw [← map_smul]; rfl

/-- **Elements of the stalk at a point of the section act on `ω_{A_L}` through `𝒪_{S,s}`.** -/
theorem exists_act {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (s : Spec (CommRingCat.of (𝓞 L))) (r : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) :
    ∃ p t : 𝓞 L, t ∉ s.asIdeal ∧ (IsUnit r → p ∉ s.asIdeal) ∧ ∀ v : 𝒢.cotangent,
      t • (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) r • v) = p • v := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  set Os := (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s
  letI : Algebra (𝓞 L) Os := ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫
    (Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ s trivial).hom.toAlgebra
  haveI : IsLocalization.AtPrime Os s.asIdeal := by
    have := StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) s
    exact this
  set sp := 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
  set Gat := (𝒢.G.hom.stalkMapAt (hom_unitSection 𝒢 s)).hom
  set gam : Os := (𝒢.unitSection.stalkMap s).hom r
  obtain ⟨⟨p, t⟩, hpt⟩ := IsLocalization.surj s.asIdeal.primeCompl gam
  have hSM : ∀ a : 𝓞 L, 𝒢.structMap a = sp (Gat (algebraMap (𝓞 L) Os a)) :=
    fun a => structMap_eq_spec 𝒢 s a
  refine ⟨p, t, t.2, fun hr => ?_, fun v => ?_⟩
  · intro hp
    have hu : IsUnit (algebraMap (𝓞 L) Os p) := by
      rw [← hpt]
      exact (hr.map (𝒢.unitSection.stalkMap s).hom).mul
        (IsLocalization.map_units Os (⟨t.1, t.2⟩ : s.asIdeal.primeCompl))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Os s.asIdeal p).mp hu hp
  · have hker : (𝒢.unitSection.stalkMap s).hom (r - Gat gam) = 0 := by
      rw [map_sub]
      have := unitSection_stalkMapAt_hom 𝒢 (rfl : 𝒢.unitSection s = 𝒢.unitSection s)
        (hom_unitSection 𝒢 s) gam
      rw [Scheme.Hom.stalkMapAt_rfl] at this
      rw [this, sub_self]
    have h1 : sp r • v = sp (Gat gam) • v := by
      apply smul_cotangent_eq_of_sub_mem
      rw [← map_sub]
      exact spec_mem_of_ker 𝒢 s _ hker
    change 𝒢.structMap t • (sp r • v) = 𝒢.structMap p • v
    rw [h1, smul_smul, hSM, hSM, ← map_mul, ← map_mul, mul_comm, hpt]

theorem stalkSpec_comp_apply {X : Scheme.{0}} {x y z : X} (h : x ⤳ y) (h' : y ⤳ z)
    (t : X.presheaf.stalk z) :
    X.presheaf.stalkSpecializes h (X.presheaf.stalkSpecializes h' t) =
      X.presheaf.stalkSpecializes (h.trans h') t := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem stalkSpec_self_apply {X : Scheme.{0}} {x : X} (h : x ⤳ x) (t : X.presheaf.stalk x) :
    X.presheaf.stalkSpecializes h t = t := by
  rw [show h = specializes_refl x from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

variable {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}

/-- **Step B: conormal base change at a point `s'` of `Spec 𝓞_{L'}`.** -/
theorem omegaAt_bc_local (he : IsMonBC 𝒢 𝒢' e) (s' : Spec (CommRingCat.of (𝓞 L')))
    (v : 𝒢'.cotangent) (hv : v ∈ 𝒢'.omegaAt s') :
    haveI := s'.isPrime
    v ∈ locSub s'.asIdeal (Submodule.span (𝓞 L') (bcCot he '' 𝒢.omegaAt (bO L L' s'))) := by
  haveI := s'.isPrime
  set N := Submodule.span (𝓞 L') (bcCot he '' 𝒢.omegaAt (bO L L' s'))
  set x' := 𝒢'.unitSection s'
  set p := bcProj 𝒢 𝒢' e
  set sp' := 𝒢'.G.left.presheaf.stalkSpecializes (𝒢'.specializes_genericUnit s')
  have hp : p x' = 𝒢.unitSection (bO L L' s') :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun φ => φ s') (bcProj_unit he)).trans (Scheme.Hom.comp_apply _ _ _))
  have hx : 𝒢.unitSection (bO L L' s') = p x' := hp.symm
  have hG : 𝒢.G.hom (p x') = bO L L' s' := by rw [hp]; exact hom_unitSection 𝒢 _
  set eat := (𝒢.unitSection.stalkMapAt hx).hom
  set Gat := (𝒢.G.hom.stalkMapAt hG).hom
  set Kk := RingHom.ker eat
  set T : Ideal (𝒢'.G.left.presheaf.stalk x') := Kk.map (p.stalkMap x').hom
  set e' := (𝒢'.unitSection.stalkMap s').hom
  -- `π^♯(I_{e(s)})` lies in `I'_{e'(s')}`
  have hKker : ∀ k ∈ Kk, e' ((p.stalkMap x').hom k) = 0 := by
    intro k hk
    have hfg : (𝒢'.unitSection ≫ p) s' = p x' := Scheme.Hom.comp_apply _ _ _
    have hfg' : (bO L L' ≫ 𝒢.unitSection) s' = p x' := by
      rw [Scheme.Hom.comp_apply, hx]
    have h1 := stalkMapAt_comp_apply' 𝒢'.unitSection p (rfl : 𝒢'.unitSection s' = x')
      (rfl : p x' = p x') hfg k
    rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.stalkMapAt_rfl] at h1
    change (𝒢'.unitSection.stalkMap s').hom ((p.stalkMap x').hom k) = 0
    rw [h1, Scheme.Hom.stalkMapAt_congr (bcProj_unit he) hfg hfg',
      ← stalkMapAt_comp_apply' (bO L L') 𝒢.unitSection (rfl : bO L L' s' = bO L L' s') hx hfg']
    change (Scheme.Hom.stalkMapAt (bO L L') rfl).hom (eat k) = 0
    rw [RingHom.mem_ker.mp hk, map_zero]
  have hTker : ∀ u ∈ T, e' u = 0 := by
    intro u hu
    have hle : T ≤ RingHom.ker e' := Ideal.map_le_iff_le_comap.mpr fun k hk => by
      rw [Ideal.mem_comap, RingHom.mem_ker]; exact hKker k hk
    exact RingHom.mem_ker.mp (hle hu)
  have hT𝔪 : ∀ u ∈ T, sp' u ∈ IsLocalRing.maximalIdeal 𝒢'.genStalk :=
    fun u hu => spec_mem_of_ker 𝒢' s' u (hTker u hu)
  -- generators of `T` give vectors of `π^*((ω_𝒢)_s)`
  have hgenT : ∀ k ∈ Kk, ∀ h : sp' ((p.stalkMap x').hom k) ∈ IsLocalRing.maximalIdeal 𝒢'.genStalk,
      𝒢'.dCls ⟨_, h⟩ ∈ N := by
    intro k hk h
    set spk := 𝒢.G.left.presheaf.stalkSpecializes
      ((𝒢.specializes_genericUnit (bO L L' s')).trans (Inseparable.of_eq hx).specializes) k
    set f := (𝒢.G.left.presheaf.stalkCongr (.of_eq hx.symm)).hom k
    have hfker : f ∈ RingHom.ker (𝒢.unitSection.stalkMap (bO L L' s')).hom := hk
    have hspf : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (bO L L' s')) f =
        spk :=
      stalkSpec_comp_apply (𝒢.specializes_genericUnit (bO L L' s')) (Inseparable.of_eq hx).specializes k
    have hspk : spk ∈ IsLocalRing.maximalIdeal 𝒢.genStalk :=
      hspf ▸ spec_mem_of_ker 𝒢 _ f hfker
    have hmem : 𝒢.dCls ⟨spk, hspk⟩ ∈ 𝒢.omegaAt (bO L L' s') :=
      Submodule.subset_span ⟨f, hfker, hspf ▸ hspk, by congr 1; exact Subtype.ext hspf.symm⟩
    have hbc : sp' ((p.stalkMap x').hom k) = bcMap he spk := by
      have h2 := Scheme.Hom.stalkSpecializes_stalkMap_apply p 𝒢'.genericUnit x'
        (𝒢'.specializes_genericUnit s') k
      change _ = (p.stalkMap 𝒢'.genericUnit).hom (𝒢.G.left.presheaf.stalkSpecializes _ spk)
      rw [stalkSpec_comp_apply]
      exact h2.symm
    refine Submodule.subset_span ⟨_, hmem, ?_⟩
    rw [bcCot_dCls]
    congr 1
    exact Subtype.ext hbc.symm
  -- every element of `T` gives a vector of `locSub`
  have hPr : ∀ u (hu : u ∈ T), 𝒢'.dCls ⟨sp' u, hT𝔪 u hu⟩ ∈ locSub s'.asIdeal N := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      exact ⟨1, fun h => Ideal.IsPrime.ne_top s'.isPrime ((Ideal.eq_top_iff_one _).mpr h),
        by rw [one_smul]; exact hgenT k hk _⟩
    | zero =>
      have : (⟨sp' 0, hT𝔪 0 (Submodule.zero_mem _)⟩ : IsLocalRing.maximalIdeal 𝒢'.genStalk) = 0 :=
        Subtype.ext (map_zero _)
      rw [this, GroupModel.dCls, map_zero]; exact Submodule.zero_mem _
    | add y z hy hz ihy ihz =>
      have : (⟨sp' (y + z), hT𝔪 _ (Submodule.add_mem _ hy hz)⟩ :
          IsLocalRing.maximalIdeal 𝒢'.genStalk) = ⟨sp' y, hT𝔪 y (show y ∈ T from hy)⟩ +
            ⟨sp' z, hT𝔪 z (show z ∈ T from hz)⟩ :=
        Subtype.ext (map_add _ _ _)
      rw [this, GroupModel.dCls, map_add]; exact Submodule.add_mem _ ihy ihz
    | smul r y hy ihy =>
      obtain ⟨pr, tr, htr, -, hact⟩ := exists_act 𝒢' s' r
      obtain ⟨d, hd, hdN⟩ := ihy
      have hcot : 𝒢'.dCls ⟨sp' (r • y), hT𝔪 _ (Submodule.smul_mem _ r hy)⟩ =
          sp' r • 𝒢'.dCls ⟨sp' y, hT𝔪 y (show y ∈ T from hy)⟩ := by
        unfold GroupModel.dCls
        refine (congrArg _ (Subtype.ext ?_)).trans
          (map_smul (IsLocalRing.maximalIdeal 𝒢'.genStalk).toCotangent (sp' r)
            ⟨sp' y, hT𝔪 y (show y ∈ T from hy)⟩)
        simp only [smul_eq_mul, map_mul, SetLike.val_smul]
      rw [hcot]
      refine ⟨d * tr, fun h => (Ideal.IsPrime.mem_or_mem s'.isPrime h).elim hd htr, ?_⟩
      rw [mul_comm, mul_smul, smul_comm tr d, hact, smul_comm d pr]
      exact N.smul_mem pr hdN
  -- `𝒪_{𝒢',x'}` is generated by `π^♯` and `G'^♯` (infra-stalks' `pullback_stalkGen`)
  have hgen : StalkGen p 𝒢'.G.hom x' := by
    have h0 := StalkGen.comp_of_isIso e.hom.left (pullback.fst 𝒢.G.hom (bO L L'))
      (pullback.snd _ _) x' (pullback_stalkGen _ _ _)
    have hsnd : e.hom.left ≫ pullback.snd 𝒢.G.hom (bO L L') = 𝒢'.G.hom := Over.w e.hom
    rw [hsnd] at h0
    exact h0
  -- elements of the generated subring are `G'^♯(γ)` modulo `T`
  have hdec : ∀ c ∈ (p.stalkMap x').hom.range ⊔ (𝒢'.G.hom.stalkMap x').hom.range,
      ∃ gam, c - (𝒢'.G.hom.stalkMap x').hom gam ∈ T := by
    intro c hc
    have hR : (p.stalkMap x').hom.range ⊔ (𝒢'.G.hom.stalkMap x').hom.range ≤
        Subring.closure (Set.range (p.stalkMap x').hom ∪ Set.range (𝒢'.G.hom.stalkMap x').hom) :=
      sup_le (fun y hy => Subring.subset_closure (Or.inl (RingHom.mem_range.mp hy)))
        (fun y hy => Subring.subset_closure (Or.inr (RingHom.mem_range.mp hy)))
    suffices H : ∀ u (hu : u ∈ Subring.closure
        (Set.range (p.stalkMap x').hom ∪ Set.range (𝒢'.G.hom.stalkMap x').hom)),
        ∃ gam, u - (𝒢'.G.hom.stalkMap x').hom gam ∈ T from H c (hR hc)
    intro u hu
    induction hu using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · set c0 := (((Spec (CommRingCat.of (𝓞 L))).presheaf.stalkCongr
          (.of_eq hG.symm)).hom (eat a))
        have hGat : Gat (eat a) = (𝒢.G.hom.stalkMap (p x')).hom c0 := by
          change ((((Spec (CommRingCat.of (𝓞 L))).presheaf.stalkCongr (.of_eq hG.symm)).hom ≫
            𝒢.G.hom.stalkMap (p x')).hom (eat a)) = _
          rw [CommRingCat.comp_apply]
        have hk : a - (𝒢.G.hom.stalkMap (p x')).hom c0 ∈ Kk := by
          rw [RingHom.mem_ker, ← hGat, map_sub, unitSection_stalkMapAt_hom 𝒢 hx hG, sub_self]
        obtain ⟨c', hc'⟩ := exists_stalkMap_comp_eq p 𝒢'.G.hom 𝒢.G.hom (bO L L')
          (bcProj_w 𝒢 𝒢' e) x' c0
        refine ⟨(bO L L').stalkMap _ c', ?_⟩
        rw [← hc', ← map_sub]
        exact Ideal.mem_map_of_mem _ hk
      · exact ⟨b, by rw [sub_self]; exact T.zero_mem⟩
    | zero => exact ⟨0, by rw [map_zero, sub_self]; exact T.zero_mem⟩
    | one => exact ⟨1, by rw [map_one, sub_self]; exact T.zero_mem⟩
    | add y z _ _ hy hz =>
      obtain ⟨b1, h1⟩ := hy
      obtain ⟨b2, h2⟩ := hz
      refine ⟨b1 + b2, ?_⟩
      have : y + z - (𝒢'.G.hom.stalkMap x').hom (b1 + b2) =
          (y - (𝒢'.G.hom.stalkMap x').hom b1) + (z - (𝒢'.G.hom.stalkMap x').hom b2) := by
        rw [map_add]; ring
      rw [this]; exact T.add_mem h1 h2
    | neg y _ hy =>
      obtain ⟨b1, h1⟩ := hy
      refine ⟨-b1, ?_⟩
      have : -y - (𝒢'.G.hom.stalkMap x').hom (-b1) = -(y - (𝒢'.G.hom.stalkMap x').hom b1) := by
        rw [map_neg]; ring
      rw [this]; exact T.neg_mem h1
    | mul y z _ _ hy hz =>
      obtain ⟨b1, h1⟩ := hy
      obtain ⟨b2, h2⟩ := hz
      refine ⟨b1 * b2, ?_⟩
      have : y * z - (𝒢'.G.hom.stalkMap x').hom (b1 * b2) =
          (y - (𝒢'.G.hom.stalkMap x').hom b1) * z +
            (𝒢'.G.hom.stalkMap x').hom b1 * (z - (𝒢'.G.hom.stalkMap x').hom b2) := by
        rw [map_mul]; ring
      rw [this]
      exact T.add_mem (T.mul_mem_right _ h1) (T.mul_mem_left _ h2)
  -- the generators of `(ω_{𝒢'})_{s'}`
  induction hv using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨f', hf', hmem, rfl⟩ := hm
    obtain ⟨c, hc, w, hw, hwu, hfw⟩ := hgen f'
    obtain ⟨gam, hgam⟩ := hdec c hc
    have hec : e' c = 0 := by rw [← hfw, map_mul, RingHom.mem_ker.mp hf', zero_mul]
    have hegam : e' ((𝒢'.G.hom.stalkMap x').hom gam) = 0 := by
      have h1 := hTker _ hgam
      rw [map_sub, hec, zero_sub, neg_eq_zero] at h1
      exact h1
    have hgam0 : (𝒢'.G.hom.stalkMap x').hom gam = 0 := by
      set CI := (Spec (CommRingCat.of (𝓞 L'))).presheaf.stalkCongr
        (.of_eq (hom_unitSection 𝒢' s').symm)
      have key := unitSection_stalkMapAt_hom 𝒢' (rfl : 𝒢'.unitSection s' = x')
        (hom_unitSection 𝒢' s') (CI.inv gam)
      rw [Scheme.Hom.stalkMapAt_rfl] at key
      have h2 : (𝒢'.G.hom.stalkMapAt (hom_unitSection 𝒢' s')).hom (CI.inv gam) =
          (𝒢'.G.hom.stalkMap x').hom gam := by
        change ((CI.hom ≫ 𝒢'.G.hom.stalkMap x').hom (CI.inv gam)) = _
        rw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
      rw [h2] at key
      change e' _ = _ at key
      rw [hegam] at key
      have hg0 : gam = 0 := by
        have := congrArg CI.hom key
        rwa [map_zero, Iso.inv_hom_id_apply, eq_comm] at this
      rw [hg0, map_zero]
    have hcT : c ∈ T := by rw [hgam0, sub_zero] at hgam; exact hgam
    have hfwT : f' * w ∈ T := hfw ▸ hcT
    obtain ⟨d, hd, hdN⟩ := hPr (f' * w) hfwT
    have hcot : 𝒢'.dCls ⟨sp' (f' * w), hT𝔪 _ hfwT⟩ = sp' w • 𝒢'.dCls ⟨sp' f', hmem⟩ := by
      unfold GroupModel.dCls
      refine (congrArg _ (Subtype.ext ?_)).trans
        (map_smul (IsLocalRing.maximalIdeal 𝒢'.genStalk).toCotangent (sp' w) ⟨sp' f', hmem⟩)
      change sp' (f' * w) = sp' w * sp' f'
      rw [map_mul, mul_comm]
    obtain ⟨pw, tw, htw, hpw, hact⟩ := exists_act 𝒢' s' w
    refine ⟨d * pw, fun h => (Ideal.IsPrime.mem_or_mem s'.isPrime h).elim hd (hpw hwu), ?_⟩
    rw [mul_smul, ← hact, smul_comm d tw, ← hcot]
    exact N.smul_mem tw hdN
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul r y _ hy => exact Submodule.smul_mem _ r hy

/-! ### Toward `OmegaLocalization`: properties of the local lattices of one model -/

/-- `(ω_𝒢)_s` is stable under `𝒪_{S,s}`: elements `u ∉ s` act injectively modulo it. -/
theorem omegaAt_sat {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (s : Spec (CommRingCat.of (𝓞 L))) (u : 𝓞 L) (hu : u ∉ s.asIdeal) (w : 𝒢.cotangent)
    (hw : u • w ∈ 𝒢.omegaAt s) : w ∈ 𝒢.omegaAt s := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  set Os := (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s
  letI : Algebra (𝓞 L) Os := ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫
    (Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ s trivial).hom.toAlgebra
  haveI : IsLocalization.AtPrime Os s.asIdeal := by
    have := StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) s
    exact this
  set sp := 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
  set Gat := (𝒢.G.hom.stalkMapAt (hom_unitSection 𝒢 s)).hom
  have hgu : IsUnit (algebraMap (𝓞 L) Os u) :=
    IsLocalization.map_units Os (⟨u, hu⟩ : s.asIdeal.primeCompl)
  set y := Gat (algebraMap (𝓞 L) Os u)
  have hy : IsUnit y := hgu.map Gat
  set y' : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s) := ↑(hy.unit⁻¹)
  have hyy : y' * y = 1 := hy.unit.inv_mul
  have hsy : 𝒢.structMap u = sp y := structMap_eq_spec 𝒢 s u
  have hΦ : ∀ m ∈ 𝒢.omegaAt s, sp y' • m ∈ 𝒢.omegaAt s := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨f, hf, hmem, rfl⟩ := hm
      have hf' : y' * f ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom := by
        rw [RingHom.mem_ker, map_mul, RingHom.mem_ker.mp hf, mul_zero]
      have hmem' : sp (y' * f) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ hmem
      apply Submodule.subset_span
      refine ⟨_, hf', hmem', ?_⟩
      unfold GroupModel.dCls
      refine (map_smul (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent (sp y') ⟨_, hmem⟩).symm.trans
        (congrArg _ (Subtype.ext ?_))
      change sp y' * sp f = sp (y' * f)
      rw [map_mul]
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      have : sp y' • (r • a) = r • (sp y' • a) := by
        change sp y' • (𝒢.structMap r • a) = 𝒢.structMap r • (sp y' • a)
        rw [smul_smul, smul_smul, mul_comm]
      rw [this]; exact Submodule.smul_mem _ r ha
  have hw' : sp y' • (u • w) = w := by
    change sp y' • (𝒢.structMap u • w) = w
    rw [hsy, smul_smul, ← map_mul, hyy, map_one, one_smul]
  have := hΦ _ hw
  rwa [hw'] at this

/-- `(ω_𝒢)_s` is full: every `v ∈ ω_{A_L}` has a nonzero multiple in it. -/
theorem omegaAt_full {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (s₁ : Spec (CommRingCat.of (𝓞 L))) (v : 𝒢.cotangent) :
    ∃ c : 𝓞 L, c ≠ 0 ∧ c • v ∈ 𝒢.omegaAt s₁ := by
  obtain ⟨g, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective v
  change ∃ c : 𝓞 L, c ≠ 0 ∧ c • 𝒢.dCls g ∈ 𝒢.omegaAt s₁
  set x₁ := 𝒢.unitSection s₁
  obtain ⟨U, hUaff, hx₁U, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    𝒢.G.left.isBasis_affineOpens (show x₁ ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hξU : 𝒢.genericUnit ∈ U := (𝒢.specializes_genericUnit s₁).mem_open U.isOpen hx₁U
  letI := 𝒢.G.left.presheaf.algebra_section_stalk ⟨𝒢.genericUnit, hξU⟩
  haveI hL := (show IsAffineOpen U from hUaff).isLocalization_stalk ⟨𝒢.genericUnit, hξU⟩
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj
    ((show IsAffineOpen U from hUaff).primeIdealOf ⟨_, hξU⟩).asIdeal.primeCompl (g : 𝒢.genStalk)
  set ga := 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hξU a
  set gt := 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hξU t
  have hat' : (g : 𝒢.genStalk) * gt = ga := hat
  have htu : IsUnit gt := IsLocalization.map_units 𝒢.genStalk t
  -- `e^♯ a` vanishes on `e⁻¹ U`
  have hzero : 𝒢.unitSection.app U a = 0 := by
    have hηU : 𝒢.unitSection (genericPt L) ∈ U := by
      unfold GroupModel.genericUnit at hξU; exact hξU
    apply germ_injective_of_isIntegral (Spec (CommRingCat.of (𝓞 L))) (genericPt L)
      (show genericPt L ∈ 𝒢.unitSection ⁻¹ᵁ U from hηU)
    rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply]
    change (𝒢.unitSection.stalkMap (genericPt L)).hom ga = 0
    rw [← hat']
    erw [map_mul]
    have hg0 : (𝒢.unitSection.stalkMap (genericPt L)).hom (g : 𝒢.genStalk) ∈
        IsLocalRing.maximalIdeal _ := map_nonunit _ _ g.2
    rw [maximalIdeal_stalk_genericPt L _ rfl] at hg0
    rw [(Submodule.mem_bot _).mp hg0, zero_mul]
  have ha₁ : 𝒢.G.left.presheaf.germ U x₁ hx₁U a ∈
      RingHom.ker (𝒢.unitSection.stalkMap s₁).hom := by
    rw [RingHom.mem_ker]
    erw [Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U s₁ hx₁U]
    rw [hzero, map_zero]
  have hspa : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s₁)
      (𝒢.G.left.presheaf.germ U x₁ hx₁U a) = ga :=
    TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  have hga𝔪 : ga ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
    rw [← hat']; exact Ideal.mul_mem_right _ _ g.2
  have hmem : 𝒢.dCls ⟨ga, hga𝔪⟩ ∈ 𝒢.omegaAt s₁ :=
    Submodule.subset_span ⟨_, ha₁, hspa ▸ hga𝔪, by congr 1; exact Subtype.ext hspa.symm⟩
  have hcot : 𝒢.dCls ⟨ga, hga𝔪⟩ = gt • 𝒢.dCls g := by
    unfold GroupModel.dCls
    refine (congrArg _ (Subtype.ext ?_)).trans
      (map_smul (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent gt g)
    change ga = gt * (g : 𝒢.genStalk)
    rw [← hat', mul_comm]
  obtain ⟨p, t', ht', hp, hact⟩ := exists_act 𝒢 (genericPt L) gt
  have hsp : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (genericPt L)) gt = gt :=
    stalkSpec_self_apply _ _
  refine ⟨p, fun h0 => hp htu (by rw [h0]; exact Submodule.zero_mem _), ?_⟩
  rw [← hact, hsp, ← hcot]
  exact Submodule.smul_mem _ t' hmem

/-- A germ in `I_{e(s)}` extends over an open `W ∋ e(s)`; its class lies in `(ω_𝒢)_{s₁}` for every
`s₁` with `e(s₁) ∈ W`. -/
theorem omegaAt_open {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (s : Spec (CommRingCat.of (𝓞 L))) (f : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    (hf : f ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom)
    (h : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk) :
    ∃ W : 𝒢.G.left.Opens, 𝒢.unitSection s ∈ W ∧ ∀ s₁, 𝒢.unitSection s₁ ∈ W →
      𝒢.dCls ⟨_, h⟩ ∈ 𝒢.omegaAt s₁ := by
  obtain ⟨W, hxW, F, rfl⟩ := 𝒢.G.left.presheaf.exists_germ_eq f
  refine ⟨W, hxW, fun s₁ hs₁ => ?_⟩
  have hzero : 𝒢.unitSection.app W F = 0 := by
    apply germ_injective_of_isIntegral (Spec (CommRingCat.of (𝓞 L))) s
      (show s ∈ 𝒢.unitSection ⁻¹ᵁ W from hxW)
    rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply]
    exact RingHom.mem_ker.mp hf
  have hk : 𝒢.G.left.presheaf.germ W (𝒢.unitSection s₁) hs₁ F ∈
      RingHom.ker (𝒢.unitSection.stalkMap s₁).hom := by
    rw [RingHom.mem_ker]
    erw [Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection W s₁ hs₁]
    rw [hzero, map_zero]
  have hξW : 𝒢.genericUnit ∈ W := (𝒢.specializes_genericUnit s).mem_open W.isOpen hxW
  have h1 : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s₁)
      (𝒢.G.left.presheaf.germ W (𝒢.unitSection s₁) hs₁ F) =
      𝒢.G.left.presheaf.germ W 𝒢.genericUnit hξW F :=
    TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  have h2 : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (𝒢.G.left.presheaf.germ W (𝒢.unitSection s) hxW F) =
      𝒢.G.left.presheaf.germ W 𝒢.genericUnit hξW F :=
    TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  apply Submodule.subset_span
  refine ⟨_, hk, h1 ▸ h2 ▸ h, ?_⟩
  congr 1
  exact Subtype.ext (h2.trans h1.symm)

end OmegaBC

/-- **Glue `OmegaLocalization` (the local lattices of `ω_𝒢` are its localizations).** For a group
model `𝒢` over `𝓞_L` and a point `s` of `Spec 𝓞_L`, every vector of `(ω_𝒢)_s = omegaAt s` has a
multiple `d • v` with `d ∉ s` lying in `ω_𝒢 = ⋂_t omegaAt t`. True: `omegaAt s` is the stalk at `s`
of the coherent conormal sheaf `e^*(I/I²)` (`I` the ideal of the unit section), and the global
sections of a coherent sheaf on the Dedekind scheme `Spec 𝓞_L` localize to its stalks (a germ at
`s` extends over an open `U ∋ s`; at the finitely many closed points outside `U` the local lattices
are full and `𝒪_t`-stable, and a suitable `d ∈ 𝔭_t^k ∖ s` clears them). A statement about one group
model; glue (not a literature leaf). STANDARD (Hartshorne II.5.x / EGA I 1.3, UNVERIFIED locators). -/
def OmegaLocalization : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (s : Spec (CommRingCat.of (𝓞 L))) (v : 𝒢.cotangent),
    v ∈ 𝒢.omegaAt s → ∃ d : 𝓞 L, d ∉ s.asIdeal ∧ d • v ∈ 𝒢.omega

/-- **`OmegaBaseChange` from `OmegaLocalization`** (Steps A and B). -/
theorem omegaBaseChange_of_localization (hloc : OmegaLocalization) : OmegaBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he v hv
  set N := Submodule.span (𝓞 L') (bcCot he '' 𝒢.omega)
  apply mem_of_forall_locSub N v
  intro P hP
  haveI := hP.isPrime
  let s' : Spec (CommRingCat.of (𝓞 L')) := ⟨P, hP.isPrime⟩
  have hv' : v ∈ 𝒢'.omegaAt s' := by
    rw [GroupModel.omega, Submodule.mem_iInf] at hv; exact hv s'
  obtain ⟨d, hd, hdv⟩ := omegaAt_bc_local he s' v hv'
  have hle : Submodule.span (𝓞 L') (bcCot he '' 𝒢.omegaAt (bO L L' s')) ≤ locSub P N := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨c, hc, hcw⟩ := hloc K A L 𝒢 (bO L L' s') w hw
    refine ⟨algebraMap (𝓞 L) (𝓞 L') c, fun h => hc h, ?_⟩
    rw [← map_smulₛₗ]
    exact Submodule.subset_span ⟨_, hcw, rfl⟩
  obtain ⟨d₂, hd₂, hd₂v⟩ := hle hdv
  exact ⟨d₂ * d, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hd₂ hd, by rw [mul_smul]; exact hd₂v⟩


/-- **`OmegaLocalization` holds.** For a generator `df` of `(ω_𝒢)_s` (`f ∈ I_{e(s)}`): `f` extends
over an open `W ∋ e(s)` (`omegaAt_open`), so `df ∈ (ω_𝒢)_{s₁}` whenever `e(s₁) ∈ W`; the other
points form a finite set of closed points `≠ s` (`finite_of_isClosed_not_genericPt`); at each of
them the ideal `{d | d • df ∈ (ω_𝒢)_{s₁}}` is nonzero (`omegaAt_full`) and saturated
(`omegaAt_sat`), hence has an element `∉ s` (`exists_mem_not_mem_of_sat`); their product works. -/
theorem omegaLocalization : OmegaLocalization := by
  intro K _ A L _ _ _ 𝒢 s v hv
  classical
  haveI := s.isPrime
  suffices key : 𝒢.omegaAt s ≤ locSub s.asIdeal 𝒢.omega from key hv
  unfold GroupModel.omegaAt
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, h, rfl⟩
  obtain ⟨W, hsW, hW⟩ := omegaAt_open 𝒢 s f hf h
  set m := 𝒢.dCls ⟨_, h⟩
  set Z : Set (Spec (CommRingCat.of (𝓞 L))) := {s₁ | 𝒢.unitSection s₁ ∉ W}
  have hZc : IsClosed Z := by
    have : IsOpen ((𝒢.unitSection ⁻¹ᵁ W : (Spec (CommRingCat.of (𝓞 L))).Opens) :
        Set (Spec (CommRingCat.of (𝓞 L)))) := (𝒢.unitSection ⁻¹ᵁ W).isOpen
    exact this.isClosed_compl
  have hξW : 𝒢.genericUnit ∈ W := (𝒢.specializes_genericUnit s).mem_open W.isOpen hsW
  have hgen : genericPt L ∉ Z := fun h' => h' hξW
  have hZfin := finite_of_isClosed_not_genericPt L Z hZc hgen
  have hd : ∀ s₁ ∈ Z, ∃ d : 𝓞 L, d ∉ s.asIdeal ∧ d • m ∈ 𝒢.omegaAt s₁ := by
    intro s₁ hs₁
    haveI := s₁.isPrime
    let J : Ideal (𝓞 L) := (𝒢.omegaAt s₁).comap (LinearMap.toSpanSingleton (𝓞 L) _ m)
    have hJ0 : J ≠ ⊥ := by
      obtain ⟨c, hc0, hc⟩ := omegaAt_full 𝒢 s₁ m
      intro hJ
      apply hc0
      have : c ∈ J := hc
      rw [hJ] at this
      exact this
    have hsat : ∀ u ∉ s₁.asIdeal, ∀ d, u * d ∈ J → d ∈ J := by
      intro u hu d hud
      apply omegaAt_sat 𝒢 s₁ u hu (d • m)
      have : (u * d) • m ∈ 𝒢.omegaAt s₁ := hud
      rwa [mul_smul] at this
    have hne : s₁.asIdeal ≠ ⊥ := by
      intro h0
      apply hgen
      have : s₁ = genericPt L := PrimeSpectrum.ext h0
      rw [← this]; exact hs₁
    have hss : s.asIdeal ≠ s₁.asIdeal := by
      intro h0
      apply hs₁
      have : s = s₁ := PrimeSpectrum.ext h0
      rw [← this]; exact hsW
    obtain ⟨d, hdJ, hdP⟩ := exists_mem_not_mem_of_sat s₁.asIdeal s.asIdeal hne hss J hJ0 hsat
    exact ⟨d, hdP, hdJ⟩
  choose! dd hdd using hd
  refine ⟨∏ s₁ ∈ hZfin.toFinset, dd s₁, ?_, ?_⟩
  · intro hD
    obtain ⟨s₁, hs₁, h1⟩ := Ideal.IsPrime.prod_mem_iff.mp hD
    exact (hdd s₁ (hZfin.mem_toFinset.mp hs₁)).1 h1
  · rw [GroupModel.omega, Submodule.mem_iInf]
    intro s₁
    by_cases hs₁ : s₁ ∈ Z
    · rw [← Finset.mul_prod_erase _ _ (hZfin.mem_toFinset.mpr hs₁), mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (hdd s₁ hs₁).2
    · have : 𝒢.unitSection s₁ ∈ W := by
        by_contra h'; exact hs₁ h'
      exact Submodule.smul_mem _ _ (hW s₁ this)

/-- **`OmegaBaseChange` holds** (height-bc glue BC-omega; statement verbatim). -/
theorem omegaBaseChange : OmegaBaseChange :=
  omegaBaseChange_of_localization omegaLocalization

end ZInQ.HeightBC




/-- Alias (added for this check): g0-split's statement names `ZInQ.DefFaltings.AbVar`, its
verbatim copy of the kernel's `PkgI3.AbVar` (`LeafAdopt.abVarEquiv`); here it is the kernel's. -/
abbrev ZInQ.DefFaltings.AbVar (K : Type) [Field K] : Type 1 := PkgI3.AbVar K



/-! ## g0-stablebc: the piece `StableHeightBaseChange` -/

namespace G0StableBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

-- The following definition (docstring and body) is copied verbatim from scratch/g0-split/Split.lean.
/-- **Missing piece 6 (definition-level glue; used by E3-E4).** The *stable* Faltings
height is invariant under finite extension of the number field (Faltings 1983 §1; Deligne,
Sém. Bourbaki 616). For def-faltings' infimum this needs semistable reduction and the Néron
models of H5 (`NeronModelMinimal`); it is a property of the definition, not a literature leaf. -/
def StableHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K),
    stableFaltingsHeight (A.baseChange L) = stableFaltingsHeight A

/-! ### Glue statements copied from `scratch/h5-neron/Reduction.lean` (verbatim, over this file's
`AbVar`; h5-neron states them over the kernel's `PkgI3.AbVar`, the same structure) -/

section H5NeronCopies

variable {K : Type} [Field K] {A : AbVar K}

/-- `𝒢'` (over `𝓞_{L'}`) is the base change of `𝒢` (over `𝓞_L`) along `𝓞_L → 𝓞_{L'}`, as a group
scheme: an isomorphism of group objects `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`. (The identifications with
`A_{L'}` are not compared; the height does not use them.) (copied from h5-neron) -/
def IsBaseChangeOf {L L' : Type} [Field L] [NumberField L] [Algebra K L] [Field L']
    [NumberField L'] [Algebra K L'] [Algebra L L'] (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) :
    Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

end H5NeronCopies

/-- **Glue H4a** (h5-neron). The height of a fixed smooth model is invariant under base change:
`ω_{𝒢_{L'}} = ω_𝒢 ⊗ 𝓞_{L'}` (flat base change of the conormal sheaf), the Arakelov degree is
multiplied by `[L':L]`, and each `τ' : L' → ℂ` restricts to `τ = τ'|_L` with the same
uniformization. (copied from h5-neron) -/
def ModelHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height = 𝒢.height

/-- **Glue H4a, the inequality half (used here).** `h(𝒢_{L'}) ≤ h(𝒢)` for a group model `𝒢` and
a base change `𝒢'` of it. Implied by `ModelHeightBaseChange` (`modelHeightBaseChangeLE`
below). Same justification (h5-neron §2): `ω` of a smooth model commutes with base change, the
Arakelov degree is multiplied by `[L':L]`, and `𝒢'(ℂ)_{τ'} = 𝒢(ℂ)_{τ'|_L}`. -/
def ModelHeightBaseChangeLE : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height ≤ 𝒢.height

theorem modelHeightBaseChangeLE (h : ModelHeightBaseChange) : ModelHeightBaseChangeLE :=
  fun K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 => (h K A L L' 𝒢 𝒢' h𝒢).le

/-- **Glue H4b** (h5-neron). A group model base-changes to a group model (smoothness,
separatedness and quasi-compactness are stable under base change; the group structure is
transported by the monoidal functor `Over.pullback`; the generic fibre is `A_L ×_L L' ≅ A_{L'}` by
pullback pasting). (copied from h5-neron) -/
def GroupModelBaseChangeExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L), ∃ 𝒢' : GroupModel A L', IsBaseChangeOf 𝒢' 𝒢

/-- **The compositum** (proved in h5-neron; proof copied). Two number fields `L, L₀` over a
number field `K` embed `K`-linearly in a common number field `L'`. -/
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

/-! ### New glue: pullback pasting for abelian varieties -/

/-- **Glue (pullback pasting, `(A_L)_M ≅ A_M`).** For fields `K → L → M` (a scalar tower), the
iterated base change `(A ×_K L) ×_L M` is isomorphic to `A ×_K M` as a group scheme over `M`
(`Over.pullbackComp`, and `Spec` of the tower `K → L → M`). Category theory, no arithmetic. -/
def BaseChangeCompIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L M : Type) [Field L] [Algebra K L] [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M],
    ∃ e : ((A.baseChange L).baseChange M).X ≅ (A.baseChange M).X, IsMonHom e.hom

/-! ### Pullback pasting and base change of group models (proved)

The kernel timeout met by h5-neron (`bcGen_isMonHom`) is avoided by proving the pasting lemmas
for an arbitrary scheme square (`exists_pbPaste`, `exists_pbSquare`, where the equation of the
square is eliminated by `subst`) and only then instantiating them; the last composition is
assembled with an explicit `instIsMonHomComp`, so that unification (not instance search) matches
the instance terms of `AbVar.baseChange`. -/

section PbPaste

open scoped Obj

/-- `f^* g^* G → (f ≫ g)^* G` (h5-neron). -/
noncomputable def pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback f).obj ((Over.pullback g).obj G) ⟶ (Over.pullback (f ≫ g)).obj G :=
  (Over.pullbackComp f g).inv.app G

theorem isMonHom_pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompInv f g G) := by
  have h := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).inv.app
      (Mon.mk G) ≫ (Functor.mapMonNatIso (Over.pullbackComp f g)).inv.app (Mon.mk G)).isMonHom_hom
  have e : pbCompInv f g G = 𝟙 _ ≫ pbCompInv f g G := (Category.id_comp _).symm
  rw [e]
  exact h

/-- Pullback pasting for group objects, with an arbitrary third side `h = f ≫ g`. -/
theorem exists_pbPaste {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (sq : f ≫ g = h)
    (G : Over Z) [GrpObj G] :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback h).obj G) := Functor.grpObjObj
    ∃ e : (Over.pullback f).obj ((Over.pullback g).obj G) ≅ (Over.pullback h).obj G,
      IsMonHom e.hom := by
  subst sq
  letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj G)) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (f ≫ g)).obj G) := Functor.grpObjObj
  exact ⟨(Over.pullbackComp f g).symm.app G, isMonHom_pbCompInv f g G⟩

/-- **`BaseChangeCompIso`, proved.** -/
theorem baseChangeCompIso : BaseChangeCompIso := by
  intro K _ A L M _ _ _ _ _ _
  have sq : Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact exists_pbPaste _ _ _ sq A.X

/-- Pasting two pullback squares, with a group-scheme iso on one leg. -/
theorem exists_pbSquare {X Y₁ Y₂ Z : Scheme.{0}} (f₁ : X ⟶ Y₁) (g₁ : Y₁ ⟶ Z) (f₂ : X ⟶ Y₂)
    (g₂ : Y₂ ⟶ Z) (sq : f₁ ≫ g₁ = f₂ ≫ g₂) (G : Over Z) [GrpObj G] (H : Over Y₂) [GrpObj H]
    (u : (Over.pullback g₂).obj G ≅ H)
    (hu : letI : GrpObj ((Over.pullback g₂).obj G) := Functor.grpObjObj; IsMonHom u.hom) :
    letI : GrpObj ((Over.pullback g₁).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f₁).obj ((Over.pullback g₁).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f₂).obj H) := Functor.grpObjObj
    ∃ e : (Over.pullback f₁).obj ((Over.pullback g₁).obj G) ≅ (Over.pullback f₂).obj H,
      IsMonHom e.hom := by
  obtain ⟨e₁, he₁⟩ := exists_pbPaste f₁ g₁ (f₁ ≫ g₁) rfl G
  obtain ⟨e₂, he₂⟩ := exists_pbPaste f₂ g₂ (f₁ ≫ g₁) sq.symm G
  have hu' : IsMonHom ((Over.pullback f₂).map u.hom) := inferInstance
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ (Over.pullback f₂).mapIso u,
    (inferInstance : IsMonHom (e₁.hom ≫ e₂.inv ≫ (Over.pullback f₂).map u.hom))⟩

/-- The square `Spec L' → Spec 𝓞_{L'} → Spec 𝓞_L = Spec L' → Spec L → Spec 𝓞_L` (h5-neron). -/
theorem square1 (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] :
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))) =
      Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- **Glue H4b (`GroupModelBaseChangeExists`), proved**: `𝒢 ×_{𝓞_L} 𝓞_{L'}` with the generic
fibre identification `(𝒢 ×_{𝓞_L} 𝓞_{L'})_{L'} ≅ (𝒢_L)_{L'} ≅ (A_L)_{L'} ≅ A_{L'}`. -/
theorem groupModelBaseChangeExists : GroupModelBaseChangeExists := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G).hom := by dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  obtain ⟨c, hc⟩ := baseChangeCompIso K A L L'
  obtain ⟨e, he⟩ := exists_pbSquare _ _ _ _ (square1 L L') 𝒢.G (A.baseChange L).X 𝒢.gen 𝒢.gen_hom
  refine ⟨⟨_, e ≪≫ c, ?_⟩, Iso.refl _, ?_⟩
  · exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ e.hom c.hom he hc
  · exact (inferInstance : IsMonHom (𝟙 ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G)))

end PbPaste

/-! ### Transport of (metrized) group models along an isomorphism of generic fibres (proved) -/

section Transport

variable {K K' : Type} [Field K] [Field K'] {A : AbVar K} {B : AbVar K'}
  {L : Type} [Field L] [NumberField L] [Algebra K L] [Algebra K' L]

/-- A group model of `A_L` is a group model of `B_L` for any group-scheme isomorphism
`A_L ≅ B_L`: same `𝒢`, generic-fibre identification composed with the isomorphism. -/
noncomputable def transportModel (e : (A.baseChange L).X ≅ (B.baseChange L).X)
    (he : IsMonHom e.hom) (𝒢 : GroupModel A L) : GroupModel B L where
  G := 𝒢.G
  gen := 𝒢.gen ≪≫ e
  gen_hom := by
    letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    haveI := 𝒢.gen_hom
    exact (inferInstance : IsMonHom (𝒢.gen.hom ≫ e.hom))

/-- The same Hodge data metrize the transported model (the Hodge line, its lattice and the
complex points depend only on `𝒢`, not on the identification of the generic fibre). -/
noncomputable def transportMetrized (e : (A.baseChange L).X ≅ (B.baseChange L).X)
    (he : IsMonHom e.hom) {g : ℕ} (Mm : MetrizedModel A L g) : MetrizedModel B L g where
  model := transportModel e he Mm.model
  hodge := Mm.hodge
  lattice_eq := Mm.lattice_eq
  arch := Mm.arch

/-- Transport does not increase the height of a group model. Proved. -/
theorem transportModel_height_le (e : (A.baseChange L).X ≅ (B.baseChange L).X)
    (he : IsMonHom e.hom) (𝒢 : GroupModel A L) :
    (transportModel e he 𝒢).height ≤ 𝒢.height := by
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm => le_iInf fun hM => ?_
  subst hM
  exact iInf_le_of_le g (iInf_le_of_le (transportMetrized e he Mm) (iInf_le_of_le rfl le_rfl))

end Transport


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

/-! ### The piece, from the glue (proved) -/

/-- **`StableHeightBaseChange` from three glue statements** (`BaseChangeCompIso`, and h5-neron's
`GroupModelBaseChangeExists` (H4b) and the `≤` half `ModelHeightBaseChangeLE` of H4a) and the proved
`compositum`. `≥`: a model of `(A_L)_M` is a model of `A_M` (transport along `(A_L)_M ≅ A_M`).
`≤`: a model `𝒢` of `A_E` base-changes to a model of `A_M` over a compositum `M` of `E` and `L`,
with no larger height (H4a `≤`, H4b), and is then a model of `(A_L)_M`. -/
theorem stableHeightBaseChange_of_glue (hcomp : BaseChangeCompIso)
    (hbcE : GroupModelBaseChangeExists) (hbc : ModelHeightBaseChangeLE) :
    StableHeightBaseChange := by
  intro K _ _ L _ _ _ A
  rw [stableFaltingsHeight_eq_iInf_height, stableFaltingsHeight_eq_iInf_height]
  apply le_antisymm
  · refine le_iInf fun E => le_iInf fun 𝒢 => ?_
    obtain ⟨M, i1, i2, i3, i4, i5, t1, t2⟩ := compositum K E.L L
    obtain ⟨𝒢', h𝒢'⟩ := hbcE K A E.L M 𝒢
    obtain ⟨e, he⟩ := hcomp K A L M
    have he' : IsMonHom e.symm.hom := (inferInstance : IsMonHom e.inv)
    calc ⨅ (E' : FinExt L) (𝒢₁ : GroupModel (A.baseChange L) E'.L), 𝒢₁.height
        ≤ (transportModel e.symm he' 𝒢').height :=
          iInf_le_of_le (FinExt.mk M) (iInf_le_of_le _ le_rfl)
      _ ≤ 𝒢'.height := transportModel_height_le _ _ _
      _ ≤ 𝒢.height := hbc K A E.L M 𝒢 𝒢' h𝒢'
  · refine le_iInf fun E => le_iInf fun 𝒢 => ?_
    letI : Algebra K E.L := ((algebraMap L E.L).comp (algebraMap K L)).toAlgebra
    haveI : IsScalarTower K L E.L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨e, he⟩ := hcomp K A L E.L
    calc ⨅ (E' : FinExt K) (𝒢₁ : GroupModel A E'.L), 𝒢₁.height
        ≤ (transportModel e he 𝒢).height :=
          iInf_le_of_le (FinExt.mk E.L) (iInf_le_of_le _ le_rfl)
      _ ≤ 𝒢.height := transportModel_height_le _ _ _

/-- **`StableHeightBaseChange` from the inequality half of glue H4a alone** (`BaseChangeCompIso`
and H4b are proved above). -/
theorem stableHeightBaseChange_of_modelHeightBaseChangeLE (hbc : ModelHeightBaseChangeLE) :
    StableHeightBaseChange :=
  stableHeightBaseChange_of_glue baseChangeCompIso groupModelBaseChangeExists hbc

/-- **`StableHeightBaseChange` from h5-neron's glue H4a.** -/
theorem stableHeightBaseChange_of_modelHeightBaseChange (hbc : ModelHeightBaseChange) :
    StableHeightBaseChange :=
  stableHeightBaseChange_of_modelHeightBaseChangeLE (modelHeightBaseChangeLE hbc)

/-- **`StableHeightBaseChange` from the geometric half of H4a alone.** -/
theorem stableHeightBaseChange_of_metrization (h : MetrizationBaseChange) :
    StableHeightBaseChange :=
  stableHeightBaseChange_of_modelHeightBaseChangeLE (modelHeightBaseChangeLE_of_metrization h)

/-- **`StableHeightBaseChange` from `HodgeLineBaseChange` alone.** -/
theorem stableHeightBaseChange_of_hodgeLine (h : HodgeLineBaseChange) :
    StableHeightBaseChange :=
  stableHeightBaseChange_of_metrization (metrizationBaseChange_of_hodgeLine h)

end G0StableBC



/-! # Part E: g0-split's piece `StableHeightBaseChange` from the four glue statements -/

namespace ZInQ.HeightBC

/-- g0-stablebc's `HodgeLineBaseChange` is this file's (verbatim copies, both over the kernel's
objects). -/
theorem g0_hodgeLine_iff : G0StableBC.HodgeLineBaseChange ↔ HodgeLineBaseChange := Iff.rfl

/-- **`StableHeightBaseChange` (g0-split missing piece 6, verbatim) from the four glue statements
of Part C**, through g0-stablebc's `stableHeightBaseChange_of_hodgeLine`. Proved. -/
theorem stableHeightBaseChange_of_glue4 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) :
    G0StableBC.StableHeightBaseChange :=
  G0StableBC.stableHeightBaseChange_of_hodgeLine
    (g0_hodgeLine_iff.mpr (hodgeLineBaseChange_of_glue4 h1 hc hω hl))

end ZInQ.HeightBC




/-! # hodge-bc2: H4a, `HodgeLineBaseChange` and `StableHeightBaseChange` without hypotheses -/

namespace ZInQ.HeightBC

/-- **H4a (`ModelHeightBaseChange`, verbatim) is a theorem**: infra-stalks'
`modelHeightBaseChange_of_two` with `hodgeBCInjective` and `omegaBaseChange`. -/
theorem modelHeightBaseChange : ModelHeightBaseChange :=
  modelHeightBaseChange_of_two hodgeBCInjective omegaBaseChange

/-- **`HodgeLineBaseChange` (verbatim) is a theorem.** -/
theorem hodgeLineBaseChange : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_two hodgeBCInjective omegaBaseChange

/-- **g0-split's piece 6 `StableHeightBaseChange` (g0-stablebc's statement, verbatim) is a
theorem**: height-bc's `stableHeightBaseChange_of_glue4` with the four glue statements, all now
proved (`cotangentSpanBC`, `uniformizationLiftAnalytic` by infra-stalks; `hodgeBCInjective`,
`omegaBaseChange` here). -/
theorem stableHeightBaseChange : G0StableBC.StableHeightBaseChange :=
  stableHeightBaseChange_of_glue4 hodgeBCInjective cotangentSpanBC omegaBaseChange
    uniformizationLiftAnalytic

end ZInQ.HeightBC

#print axioms ZInQ.HeightBC.hodgeBCInjective
#print axioms ZInQ.HeightBC.omegaBaseChange
#print axioms ZInQ.HeightBC.omegaLocalization
#print axioms ZInQ.HeightBC.cotangentSpanBC
#print axioms ZInQ.HeightBC.uniformizationLiftAnalytic
#print axioms ZInQ.HeightBC.modelHeightBaseChange
#print axioms ZInQ.HeightBC.hodgeLineBaseChange
#print axioms ZInQ.HeightBC.stableHeightBaseChange


/-! # hodge-bc2: h5-glue's H5 from the leaves N1, N2 alone (H4a now a theorem) -/

namespace ZInQ.HeightBC

open NumberField

/-- h5-glue's `ModelHeightBaseChange` is height-bc's (verbatim copies of one statement; as
height-bc's `h5_modelHeightBaseChange_iff`). -/
theorem h5_modelHeightBaseChange_iff' :
    ZInQ.H5Glue.ModelHeightBaseChange ↔ ModelHeightBaseChange := Iff.rfl

/-- **H5 in the multi-field form (h5-glue's `stableFaltingsHeight_eq_neron_all'`) from the
literature leaves N1, N2 only**: H4a is `modelHeightBaseChange`. -/
theorem stableFaltingsHeight_eq_neron_of_N1N2 (hN1 : ZInQ.H5Glue.NeronModelExists)
    (hN2 : ZInQ.H5Glue.SemistableNeronIdentityComponent)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : DefFaltings.GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ DefFaltings.stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : DefFaltings.GroupModel A L'), 𝒩'.IsNeronModel →
        DefFaltings.stableFaltingsHeight A = 𝒩'.height :=
  ZInQ.H5Glue.stableFaltingsHeight_eq_neron_all' hN1 hN2
    (h5_modelHeightBaseChange_iff'.mpr modelHeightBaseChange) K A

end ZInQ.HeightBC

#print axioms ZInQ.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2
