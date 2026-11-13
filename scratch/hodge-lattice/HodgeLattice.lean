import ZInQKernel.HDecomp.Faltings.Models

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
abelian varieties over a field and the local rings of a generic fibre. Final form:

`hodgeLatticeTheorem_of_varieties : GenericFibreStalkIso → RegularAtOrigin → DimAtOrigin →
  DimBaseChange → HodgeLatticeTheorem`.

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


namespace ZInQ.DefFaltings.HodgeLattice

/-- **Main result.** `HodgeLatticeTheorem` follows from `CotangentRank` alone. -/
theorem hodgeLatticeTheorem_of_cotangentRank (h : CotangentRank) : HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_local omegaLocal h

end ZInQ.DefFaltings.HodgeLattice

/-! ## 6. `CotangentRank` from the regularity and the dimension of `𝒪_{𝒢,ξ}`

The residue field `κ(ξ)` of `𝒪_{𝒢,ξ}` is a fraction field of `𝓞_L` (through `structMap`; the
residue lemma of §5 at the generic point), so `L ⊗_{𝓞_L} 𝔪_ξ/𝔪_ξ² ≅ 𝔪_ξ/𝔪_ξ²` has `L`-rank the
`κ(ξ)`-dimension of the cotangent space (`rank_tensor_cotangent`). With Mathlib's
`IsRegularLocalRing.iff_finrank_cotangentSpace` this reduces `CotangentRank` to two statements
about the local ring `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`: it is regular (`RegularOrigin`) and has Krull
dimension `dim A` (`DimOrigin`). -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry TensorProduct
open PkgI3 (AbVar)

/-- **(G2')** The tangent space of `A_L` at the origin has dimension `dim A` over `κ(ξ)`. -/
def TangentDim : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g →
    Module.finrank (IsLocalRing.ResidueField 𝒢.genStalk)
      (IsLocalRing.CotangentSpace 𝒢.genStalk) = g

/-- **(G2a)** `𝒪_{𝒢,ξ}` (`= 𝒪_{A_L,0}`) is a regular local ring. -/
def RegularOrigin : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), IsRegularLocalRing 𝒢.genStalk

/-- **(G2b)** `𝒪_{𝒢,ξ}` (`= 𝒪_{A_L,0}`) has Krull dimension `dim A`. -/
def DimOrigin : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g → ringKrullDim 𝒢.genStalk = g

section Tangent

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem isUnit_structMap {c : 𝓞 L} (hc : c ≠ 0) : IsUnit (𝒢.structMap c) := by
  have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
    have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
      (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
    rw [this]; exact Field.toIsField _
  let φ : 𝒢.genStalk →+* (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L) :=
    (𝒢.unitSection.stalkMap (genericPt L)).hom
  haveI : IsLocalHom φ := inferInstanceAs (IsLocalHom (𝒢.unitSection.stalkMap (genericPt L)).hom)
  have hφ : φ (𝒢.structMap c) = (Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ (genericPt L)
      (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c) :=
    stalkMap_structGerm 𝒢 (genericPt L) c
  have hne : φ (𝒢.structMap c) ≠ 0 := by
    rw [hφ]; intro h0
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv c = 0 :=
      germ_injective_of_isIntegral (Spec (CommRingCat.of (𝓞 L))) (genericPt L)
        (TopologicalSpace.Opens.mem_top _) (h0.trans (map_zero _).symm)
    apply hc
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).hom h1
    rwa [Iso.inv_hom_id_apply, map_zero] at this
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
  exact isUnit_of_map_unit φ _ (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)

theorem spec_genericPt (y : 𝒢.genStalk) : spec 𝒢 (genericPt L) y = y := by
  show (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (genericPt L))).hom y = y
  rw [show 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (genericPt L)) =
    𝟙 _ from TopCat.Presheaf.stalkSpecializes_refl _ _]
  rfl

/-- `rank_L (L ⊗_{𝓞_L} 𝔪_ξ/𝔪_ξ²) = rank_{κ(ξ)} (𝔪_ξ/𝔪_ξ²)`. -/
theorem rank_tensor_cotangent :
    Module.rank L (L ⊗[𝓞 L] 𝒢.cotangent) =
      Module.rank (IsLocalRing.ResidueField 𝒢.genStalk) (IsLocalRing.CotangentSpace 𝒢.genStalk) := by
  classical
  set κ := IsLocalRing.ResidueField 𝒢.genStalk
  set ψ : 𝓞 L →+* κ := (IsLocalRing.residue 𝒢.genStalk).comp 𝒢.structMap with hψ
  have hψ0 : ∀ c : 𝓞 L, c ≠ 0 → ψ c ≠ 0 := fun c hc =>
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (isUnit_structMap 𝒢 hc)
  let _ : Algebra (𝓞 L) κ := ψ.toAlgebra
  have halg : ∀ c, algebraMap (𝓞 L) κ c = ψ c := fun _ => rfl
  have : IsFractionRing (𝓞 L) κ := by
    refine (isLocalization_iff (nonZeroDivisors (𝓞 L)) κ).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩
    · rw [halg]; exact (hψ0 _ (nonZeroDivisors.ne_zero y.2)).isUnit
    · obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨c, t, ht, hct⟩ := residue 𝒢 (genericPt L) w
      have ht0 : t ≠ 0 := fun h => ht (h ▸ Ideal.zero_mem _)
      refine ⟨(c, ⟨t, mem_nonZeroDivisors_of_ne_zero ht0⟩), ?_⟩
      rw [spec_genericPt] at hct
      have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hct
      rw [map_sub, map_mul] at h0
      simp only [halg, hψ, RingHom.comp_apply]
      linear_combination h0
    · refine ⟨1, ?_⟩
      have h0 : ψ (x - y) = 0 := by rw [map_sub, ← halg, ← halg, h, sub_self]
      by_cases hxy : x - y = 0
      · simp [sub_eq_zero.mp hxy]
      · exact absurd h0 (hψ0 _ hxy)
  set e : L ≃ₐ[𝓞 L] κ := IsLocalization.algEquiv (nonZeroDivisors (𝓞 L)) L κ
  let _ : Module L 𝒢.cotangent := (Module.compHom (IsLocalRing.CotangentSpace 𝒢.genStalk)
    e.toRingHom : Module L (IsLocalRing.CotangentSpace 𝒢.genStalk))
  have key : ∀ (r : 𝒢.genStalk) (n : IsLocalRing.CotangentSpace 𝒢.genStalk),
      (algebraMap 𝒢.genStalk κ r) • n = r • n := fun r n => algebraMap_smul κ r n
  have : IsScalarTower (𝓞 L) L 𝒢.cotangent :=
      ⟨fun c l (n : IsLocalRing.CotangentSpace 𝒢.genStalk) => by
    change (e (c • l)) • n = 𝒢.structMap c • ((e l) • n)
    rw [map_smul, Algebra.smul_def, halg, mul_smul]
    exact key _ _⟩
  have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 L))
      (LinearMap.id : 𝒢.cotangent →ₗ[𝓞 L] 𝒢.cotangent) := isLocalizedModule_id _ _ L
  have hbc : IsBaseChange L (LinearMap.id : 𝒢.cotangent →ₗ[𝓞 L] 𝒢.cotangent) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L _).mp hloc
  rw [hbc.equiv.rank_eq]
  exact rank_eq_of_equiv_equiv e
    (AddEquiv.refl 𝒢.cotangent : 𝒢.cotangent ≃+ IsLocalRing.CotangentSpace 𝒢.genStalk)
    e.bijective (fun l n => rfl)

end Tangent

theorem cotangentRank_of_tangentDim (h : TangentDim) : CotangentRank := by
  intro K _ A L _ _ _ 𝒢 g hg
  rw [rank_tensor_cotangent 𝒢]
  haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  rw [← Module.finrank_eq_rank, h K A L 𝒢 g hg]

theorem tangentDim_of_regular (h1 : RegularOrigin) (h2 : DimOrigin) : TangentDim := by
  intro K _ A L _ _ _ 𝒢 g hg
  haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
  have := (IsRegularLocalRing.iff_finrank_cotangentSpace 𝒢.genStalk).mp (h1 K A L 𝒢)
  rw [h2 K A L 𝒢 g hg] at this
  exact_mod_cast this

/-- **Main result, final form.** `HodgeLatticeTheorem` follows from the two statements on the
local ring `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`: it is regular, of Krull dimension `dim A`. -/
theorem hodgeLatticeTheorem_of_regular (h1 : RegularOrigin) (h2 : DimOrigin) :
    HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_cotangentRank (cotangentRank_of_tangentDim (tangentDim_of_regular h1 h2))

end ZInQ.DefFaltings.HodgeLattice

/-! ## 7. Corollary: `ω_𝒢` and `⋀^g ω_𝒢` are lattices, and `L ⊗ ⋀^g ω_𝒢 → hodgeSpace g` is onto

(Projectivity of the rank-one `𝓞_L`-module `detLattice g` then follows from: finitely generated and
torsion-free over a Dedekind domain; STANDARD, not in Mathlib in this form.) -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField TensorProduct
open PkgI3 (AbVar)

theorem detLat_fg {K : Type*} [Field K] [NumberField K] {M : Type*} [AddCommGroup M]
    [Module (𝓞 K) M] (ω : Submodule (𝓞 K) M) (hfg : ω.FG) (g : ℕ) : (detLat ω g).FG := by
  have : Module.Finite (𝓞 K) ω := Module.Finite.iff_fg.mpr hfg
  have hRfg : (LinearMap.range ((TensorProduct.mk (𝓞 K) K (⋀[𝓞 K]^g M) 1) ∘ₗ
      exteriorPower.map g ω.subtype)).FG := by
    rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
  refine Submodule.FG.of_le hRfg ?_
  rw [detLat, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact ⟨exteriorPower.ιMulti (𝓞 K) g v, by simp [exteriorPower.map_apply_ιMulti]; rfl⟩

/-- Under `RegularOrigin` and `DimOrigin`: `ω_𝒢` and `detLattice g` are finitely generated, and
`detLattice g` spans the Hodge line over `L`. -/
theorem hodgeLattice_lattice_of_regular (h1 : RegularOrigin) (h2 : DimOrigin)
    (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = g) :
    𝒢.omega.FG ∧ (𝒢.detLattice g).FG ∧
      Submodule.span L (𝒢.detLattice g : Set (𝒢.hodgeSpace g)) = ⊤ := by
  have hfg := omegaFG_of_omegaLocal omegaLocal K A L 𝒢
  refine ⟨hfg, by rw [detLattice_eq]; exact detLat_fg _ hfg g, ?_⟩
  obtain ⟨hrank, s, hs, hs0, -⟩ := hodgeLatticeTheorem_of_regular h1 h2 K A L 𝒢 g hg
  rw [eq_top_iff]
  intro w _
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' s hs0).mp hrank w
  exact Submodule.smul_mem _ c (Submodule.subset_span hs)

end ZInQ.DefFaltings.HodgeLattice

/-! ## 8. The remaining inputs, stated over abelian varieties

`RegularOrigin` and `DimOrigin` concern the model `𝒢`. Both follow from statements about the
abelian variety `B = A_L` over the field `L` alone, plus one scheme-theoretic identification
(`OriginStalkIso`: the local ring of `𝒢` at the identity `ξ` of its generic fibre is the local ring
of `A_L` at its origin; true because `Spec L → Spec 𝓞_L` is a localization and `𝒢.gen` is an
isomorphism of group schemes). -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open PkgI3 (AbVar)

/-- The origin `0 ∈ B` of an abelian variety over a field `L` (image of the point of `Spec L`
under the unit section). -/
noncomputable def originPt {L : Type} [Field L] (B : AbVar L) : B.X.left :=
  (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ B.X).left
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)

/-- **(S)** `𝒪_{𝒢,ξ} ≅ 𝒪_{A_L,0}`. -/
def OriginStalkIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L),
    Nonempty (𝒢.genStalk ≃+* (A.baseChange L).X.left.presheaf.stalk (originPt (A.baseChange L)))

/-- **(V1)** The local ring of an abelian variety at its origin is regular (a smooth variety is
regular). -/
def RegularAtOrigin : Prop :=
  ∀ (L : Type) [Field L] (B : AbVar L), IsRegularLocalRing (B.X.left.presheaf.stalk (originPt B))

/-- **(V2)** The local ring of an abelian variety of dimension `g` at its origin has Krull dimension
`g` (the local ring of an irreducible variety at a closed point has dimension `dim`). -/
def DimAtOrigin : Prop :=
  ∀ (L : Type) [Field L] (B : AbVar L) (g : ℕ), B.dim = g →
    ringKrullDim (B.X.left.presheaf.stalk (originPt B)) = g

/-- **(V3)** Dimension is invariant under extension of the base field. -/
def DimBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [Algebra K L],
    (A.baseChange L).dim = A.dim

theorem regularOrigin_of (h0 : OriginStalkIso) (h1 : RegularAtOrigin) : RegularOrigin := by
  intro K _ A L _ _ _ 𝒢
  obtain ⟨e⟩ := h0 K A L 𝒢
  haveI := h1 L (A.baseChange L)
  exact IsRegularLocalRing.of_ringEquiv e.symm

theorem dimOrigin_of (h0 : OriginStalkIso) (h2 : DimAtOrigin) (h3 : DimBaseChange) :
    DimOrigin := by
  intro K _ A L _ _ _ 𝒢 g hg
  obtain ⟨e⟩ := h0 K A L 𝒢
  rw [ringKrullDim_eq_of_ringEquiv e]
  exact h2 L (A.baseChange L) g ((h3 K A L).trans hg)

/-- **Main result, over abelian varieties.** -/
theorem hodgeLatticeTheorem_of_abVar (h0 : OriginStalkIso) (h1 : RegularAtOrigin)
    (h2 : DimAtOrigin) (h3 : DimBaseChange) : HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_regular (regularOrigin_of h0 h1) (dimOrigin_of h0 h2 h3)

end ZInQ.DefFaltings.HodgeLattice

/-! ## 9. `OriginStalkIso` from the local rings of the generic fibre

`p : 𝒢_L = 𝒢 ×_{𝓞_L} L → 𝒢` sends the identity `ξ_L` of `𝒢_L` to `ξ` (`fst_genericFibreUnit`, from
`η_{𝒢_L} = ε ≫ (pullback).map η_𝒢` and `Over.w ε`), and `𝒢.gen` sends `ξ_L` to the origin of
`A_L` (`gen_genericFibreUnit`, from `IsMonHom.one_hom`). So `OriginStalkIso` follows from
`GenericFibreStalkIso`: `p` induces isomorphisms on local rings (true for any scheme over `𝓞_L`,
since `Spec L → Spec 𝓞_L` is a localization). -/

namespace ZInQ.DefFaltings.HodgeLattice
open NumberField CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open PkgI3 (AbVar)

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev toGeneric (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- **(S')** The projection `X_L = X ×_{𝓞_L} L → X` induces isomorphisms on local rings. -/
def GenericFibreStalkIso : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (X : Over (Spec (CommRingCat.of (𝓞 L))))
    (x : (genericFibre L X).left), IsIso ((pullback.fst X.hom (toGeneric L)).stalkMap x)

section
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem fst_genericFibre_unit :
    letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left ≫
      pullback.fst 𝒢.G.hom (toGeneric L) = toGeneric L ≫ 𝒢.unitSection := by
  let _ : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  change (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L)) ≫
    (Over.pullback (toGeneric L)).map η[𝒢.G]).left ≫ pullback.fst 𝒢.G.hom (toGeneric L) = _
  rw [Over.comp_left, Category.assoc]
  have h1 : ((Over.pullback (toGeneric L)).map η[𝒢.G]).left ≫
      pullback.fst 𝒢.G.hom (toGeneric L) =
      pullback.fst _ (toGeneric L) ≫ (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left := by
    simp
  rw [h1, ← Category.assoc]
  have h2 : (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L))).left ≫
      pullback.snd ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (toGeneric L) = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε (Over.pullback (toGeneric L)))
  have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
    (g := toGeneric L)
  have hc' : pullback.fst ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (toGeneric L) =
      pullback.snd _ _ ≫ toGeneric L := by
    rw [← hc]; exact (Category.comp_id _).symm
  rw [hc', ← Category.assoc, h2, Category.id_comp]
  rfl

omit [NumberField L] in
theorem toGeneric_pt [NumberField L] :
    (toGeneric L) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L) = genericPt L := by
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
    pullback.fst 𝒢.G.hom (toGeneric L) (genericFibreUnit 𝒢) = 𝒢.genericUnit := by
  have h := congrArg (fun φ => φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L))
    (fst_genericFibre_unit 𝒢)
  exact ((Scheme.Hom.comp_apply _ _ _).symm.trans h).trans
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => 𝒢.unitSection y) (toGeneric_pt (L := L))))

theorem gen_genericFibreUnit :
    𝒢.gen.hom.left (genericFibreUnit 𝒢) = originPt (A.baseChange L) := by
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  haveI := 𝒢.gen_hom
  have h := congrArg (fun φ : (𝟙_ _ ⟶ (A.baseChange L).X) =>
    φ.left (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)) (IsMonHom.one_hom (f := 𝒢.gen.hom))
  simp only [Over.comp_left] at h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h

end

theorem originStalkIso_of (h : GenericFibreStalkIso) : OriginStalkIso := by
  intro K _ A L _ _ _ 𝒢
  have hp : IsIso ((pullback.fst 𝒢.G.hom (toGeneric L)).stalkMap (genericFibreUnit 𝒢)) :=
    h L 𝒢.G _
  have hφ : IsOpenImmersion ((Over.forget _).mapIso 𝒢.gen).hom := inferInstance
  have hφs : IsIso (((Over.forget _).mapIso 𝒢.gen).hom.stalkMap (genericFibreUnit 𝒢)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hφ).2 _
  let e1 : 𝒢.genStalk ≅ (genericFibre L 𝒢.G).left.presheaf.stalk (genericFibreUnit 𝒢) :=
    𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq (fst_genericFibreUnit 𝒢).symm) ≪≫
      @asIso _ _ _ _ _ hp
  let e2 : (A.baseChange L).X.left.presheaf.stalk (originPt (A.baseChange L)) ≅
      (genericFibre L 𝒢.G).left.presheaf.stalk (genericFibreUnit 𝒢) :=
    (A.baseChange L).X.left.presheaf.stalkCongr
      (Inseparable.of_eq (gen_genericFibreUnit 𝒢).symm) ≪≫ @asIso _ _ _ _ _ hφs
  exact ⟨(e1 ≪≫ e2.symm).commRingCatIsoToRingEquiv⟩

/-- **Main result, final form.** `HodgeLatticeTheorem` from one scheme-theoretic fact (local rings of
the generic fibre) and three facts about abelian varieties over a field. -/
theorem hodgeLatticeTheorem_of_varieties (h0 : GenericFibreStalkIso) (h1 : RegularAtOrigin)
    (h2 : DimAtOrigin) (h3 : DimBaseChange) : HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_abVar (originStalkIso_of h0) h1 h2 h3

end ZInQ.DefFaltings.HodgeLattice


#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLattice_of_lattice
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_local
#print axioms ZInQ.DefFaltings.HodgeLattice.omegaLocal
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_cotangentRank
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_regular
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLattice_lattice_of_regular
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_abVar
#print axioms ZInQ.DefFaltings.HodgeLattice.originStalkIso_of
#print axioms ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_varieties
