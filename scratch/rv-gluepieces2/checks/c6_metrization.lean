/-! ## rv-gluepieces2 check (f): metrization's reductions of fields 7 (`MetrizationExists`) and 8
(`ProductMetrizationGeo`), applied to G0Assemble's constants: ExtLine.lean body and metrization's
part files in build.sh order, without part_g0dim.lean (G0Assemble already has `G0Dim`). -/


/-!
# metrization: the degree of a Hodge line is unique (pure algebra)

For a flat `R`-algebra `F` that is a field and any `R`-module `C`: if `F ⊗_R ⋀^g_R C` and
`F ⊗_R ⋀^{g'}_R C` are both `F`-lines and `0 < g`, `0 < g'`, then `g = g'`.
(Applied with `R = 𝓞_L`, `F = L`, `C = 𝔪_ξ/𝔪_ξ²`: `hodgeSpace g` determines `g ≥ 1`.)
-/

open scoped TensorProduct

namespace ZInQ.Metrization

variable {R F C : Type*} [CommRing R] [Field F] [Algebra R F] [AddCommGroup C] [Module R C]

/-- If `F ⊗ ⋀^n C ≠ 0` (positive finrank) some `1 ⊗ v₁ ∧ ⋯ ∧ vₙ` is nonzero. -/
theorem exists_one_tmul_ιMulti_ne_zero (n : ℕ)
    (h : Module.finrank F (F ⊗[R] ⋀[R]^n C) ≠ 0) :
    ∃ v : Fin n → C, (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R n v ≠ 0 := by
  by_contra! hv
  apply h
  have hall : ∀ x : F ⊗[R] ⋀[R]^n C, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m =>
      have hm : m ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
        rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        rw [show a ⊗ₜ[R] exteriorPower.ιMulti R n v =
          a • ((1 : F) ⊗ₜ[R] exteriorPower.ιMulti R n v) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], hv v, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, hx, hy, add_zero]
      | smul r x _ hx => rw [TensorProduct.tmul_smul, hx, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  haveI : Subsingleton (F ⊗[R] ⋀[R]^n C) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- The core: `F ⊗ ⋀^g C` and `F ⊗ ⋀^{g+n} C` cannot both be lines when `g, n ≥ 1`. -/
theorem not_finrank_one_of_add [Module.Flat R F] {g n : ℕ} (hg : 0 < g) (hn : 0 < n)
    (h : Module.finrank F (F ⊗[R] ⋀[R]^g C) = 1)
    (h' : Module.finrank F (F ⊗[R] ⋀[R]^(g + n) C) = 1) : False := by
  obtain ⟨v, hv⟩ := exists_one_tmul_ιMulti_ne_zero (R := R) (F := F) (C := C) (g + n)
    (by rw [h']; exact one_ne_zero)
  -- `Z = 1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀ C` (flatness)
  let ι' : ⋀[R]^(g + n) C →ₗ[R] ExteriorAlgebra R C := (⋀[R]^(g + n) C).subtype
  have hinj : Function.Injective (ι'.lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι' Subtype.val_injective
  have hZ : (1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v ≠ 0 := by
    intro h0
    apply hv
    apply hinj
    rw [LinearMap.lTensor_tmul, map_zero]
    exact h0
  let a : Fin g → C := fun i => v (Fin.castAdd n i)
  let b : Fin n → C := fun j => v (Fin.natAdd g j)
  have hab : Fin.append a b = v := Fin.append_castAdd_natAdd
  let i0 : Fin g := ⟨0, hg⟩
  let j0 : Fin n := ⟨0, hn⟩
  let a' : Fin g → C := Function.update a i0 (b j0)
  let b' : Fin n → C := Function.update b j0 (a i0)
  have hp : (Fin.castAdd n i0 : Fin (g + n)) ≠ Fin.natAdd g j0 := by
    intro hc
    have := congrArg Fin.val hc
    simp [i0, j0] at this
    omega
  -- the four products
  have h1 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a' b) = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hi
    apply hp
    apply hi
    simp [a', Fin.append_left, Fin.append_right]
  have h2 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a b') = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hi
    apply hp
    apply hi
    simp [b', Fin.append_left, Fin.append_right]
  have hswap : Fin.append a' b' = v ∘ Equiv.swap (Fin.castAdd n i0) (Fin.natAdd g j0) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Function.comp_apply]
      by_cases hi : i = i0
      · subst hi
        rw [Equiv.swap_apply_left]
        simp [a', b]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [a', hi, a]
        · exact fun hc => hi (Fin.castAdd_injective _ _ hc)
        · intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
    · rw [Fin.append_right, Function.comp_apply]
      by_cases hj : j = j0
      · subst hj
        rw [Equiv.swap_apply_right]
        simp [b', a]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [b', hj, b]
        · intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
        · exact fun hc => hj (Fin.natAdd_injective _ _ hc)
  have h3 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a' b') =
      -ExteriorAlgebra.ιMulti R (g + n) v := by
    rw [hswap]
    exact (ExteriorAlgebra.ιMulti R (g + n)).map_swap v hp
  -- the two wedge maps, base changed
  let Φ := (LinearMap.mulRight R (ExteriorAlgebra.ιMulti R n b) ∘ₗ (⋀[R]^g C).subtype).baseChange F
  let Ψ := (LinearMap.mulRight R (ExteriorAlgebra.ιMulti R n b') ∘ₗ (⋀[R]^g C).subtype).baseChange F
  set XS : F ⊗[R] ⋀[R]^g C := (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R g a
  set XT : F ⊗[R] ⋀[R]^g C := (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R g a'
  have hΦS : Φ XS = (1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v := by
    simp only [Φ, XS, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      hab]
  have hΨS : Ψ XS = 0 := by
    simp only [Ψ, XS, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      h2, TensorProduct.tmul_zero]
  have hΨT : Ψ XT = -((1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v) := by
    simp only [Ψ, XT, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      h3, TensorProduct.tmul_neg]
  have hXS : XS ≠ 0 := by
    intro h0
    apply hZ
    rw [← hΦS, h0, map_zero]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' XS hXS).mp h XT
  apply hZ
  have : Ψ XT = 0 := by rw [← hc, map_smul, hΨS, smul_zero]
  rw [hΨT, neg_eq_zero] at this
  exact this

/-- **The degree of a Hodge line is unique.** -/
theorem eq_of_finrank_one [Module.Flat R F] {g g' : ℕ} (hg : 0 < g) (hg' : 0 < g')
    (h : Module.finrank F (F ⊗[R] ⋀[R]^g C) = 1)
    (h' : Module.finrank F (F ⊗[R] ⋀[R]^g' C) = 1) : g = g' := by
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact (not_finrank_one_of_add hg (Nat.succ_pos n) h h').elim
  · exact heq
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact (not_finrank_one_of_add hg' (Nat.succ_pos n) h' h).elim

end ZInQ.Metrization


/-! ## metrization (2026-11-13): `MetrizationDimUnique`, proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- A discrete `ℤ`-submodule of `ℂ^g`, `g ≥ 1`, is not all of `ℂ^g`. -/
theorem exists_not_mem_of_discrete {g : ℕ} (hg : 0 < g) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] : ∃ z, z ∉ Λ := by
  by_contra! hall
  let e : Fin g → ℂ := Pi.single ⟨0, hg⟩ 1
  let f : ℝ → Λ := fun t => ⟨(t : ℂ) • e, hall _⟩
  have hf : Continuous f :=
    Continuous.subtype_mk (Complex.continuous_ofReal.smul continuous_const) _
  have h1 := PreconnectedSpace.constant inferInstance hf (x := 0) (y := 1)
  have h2 := congrArg (fun x : Λ => (x : Fin g → ℂ) ⟨0, hg⟩) h1
  simp [f, e] at h2

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization of dimension `g ≥ 1` has a nontrivial complex point at every `τ`. -/
theorem metrized_exists_pts_ne_one {g : ℕ} (hg : 0 < g) (M : MetrizedModel A L g)
    (τ : L →+* ℂ) : ∃ p : M.model.Pts τ, p ≠ 1 := by
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  haveI := M.hodge.periods_discrete τ
  obtain ⟨z, hz⟩ := exists_not_mem_of_discrete hg (M.hodge.periods τ)
  exact ⟨Φ z, fun h => hz ((hΦ.2.1 z).mp h)⟩

/-- A metrization of dimension `0` forces `𝒢(ℂ)_τ` to be trivial (`Φ : ℂ⁰ → 𝒢(ℂ)_τ` is onto). -/
theorem metrized_pts_subsingleton (M : MetrizedModel A L 0) (τ : L →+* ℂ) :
    Subsingleton (M.model.Pts τ) := by
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  refine ⟨fun p q => ?_⟩
  obtain ⟨z, rfl⟩ := hΦ.2.2.1 p
  obtain ⟨w, rfl⟩ := hΦ.2.2.1 q
  rw [Subsingleton.elim z w]

/-- **`MetrizationDimUnique`, proved.** Two metrizations of one group model have the same
dimension. For `g, g' ≥ 1`: `hodgeSpace g = L ⊗ ⋀^g C` is a line for at most one `g ≥ 1`
(`eq_of_finrank_one`, `L` flat over `𝓞_L`). For `g = 0 < g'`: the dimension-`0` uniformization
makes `𝒢(ℂ)_τ` trivial, the dimension-`g'` one (discrete kernel) makes it nontrivial. -/
theorem metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique := by
  intro K _ A L _ _ _ g g' M M' h
  obtain ⟨τ⟩ := (inferInstance : Nonempty (L →+* ℂ))
  have key : ∀ {g g' : ℕ} (M : MetrizedModel A L g) (M' : MetrizedModel A L g'),
      M.model = M'.model → g = 0 → g' = 0 := by
    intro g g' M M' h hg0
    subst hg0
    by_contra hg'
    obtain ⟨p, hp⟩ := metrized_exists_pts_ne_one (Nat.pos_of_ne_zero hg') M' τ
    have hs := metrized_pts_subsingleton M τ
    rw [h] at hs
    exact hp (Subsingleton.elim _ _)
  by_cases hg : g = 0
  · rw [hg, key M M' h hg]
  by_cases hg' : g' = 0
  · rw [hg', key M' M h.symm hg']
  haveI : Module.Flat (𝓞 L) L := IsLocalization.flat L (nonZeroDivisors (𝓞 L))
  have h1 := M.hodge.finrank_eq_one
  have h2 := M'.hodge.finrank_eq_one
  rw [← h] at h2
  exact eq_of_finrank_one (R := 𝓞 L) (F := L) (C := M.model.cotangent)
    (Nat.pos_of_ne_zero hg) (Nat.pos_of_ne_zero hg') h1 h2

end ZInQ.Metrization



/-! ## metrization (2026-11-13): `MetrizationExists` reduced to `HodgeLatticeTheorem`, one leaf
(the uniformization theorem with its dimension) and two glue Props on Jacobians -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- An abelian variety (def-faltings' copy) has finite dimension (proved, from g0-dim's
`G0Dim.dim_finite`; the same proof as g0-dim's `dimFinite` for `PkgI3.AbVar`). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : AbVar K) : ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- **Leaf (AN3 with its dimension: the uniformization theorem).** For every smooth group model
`𝒢` of `A_L`, every `τ : L → ℂ` and `g = dim A`, there are a full lattice `Λ ⊂ ℂ^g` and an analytic
uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ`. This is def-faltings'
`AnalyticUniformizationExists` with the dimension pinned to `dim A` (`𝒢(ℂ)_τ = A_τ(ℂ)` is a compact
connected complex Lie group of dimension `dim A`, hence `≅ ℂ^g/Λ`: Mumford, *Abelian varieties*,
§1 and §4 (UNVERIFIED locators), with Serre's GAGA for the analytic structure of `A_τ(ℂ)`).
Implies `AnalyticUniformizationExists` (`analyticUniformizationExists_of`). -/
def AnalyticUniformizationOfDim : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
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
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
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
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      IsZLattice ℝ Λ → 𝒢.IsAnalyticUniformization τ Λ Φ →
      ∃ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk, 𝒢.jacDet Φ f ≠ 0

/-- `AnalyticUniformizationOfDim` is at least as strong as def-faltings'
`AnalyticUniformizationExists` (proved; with `abVar_dim_finite`). -/
theorem analyticUniformizationExists_of (h : AnalyticUniformizationOfDim) :
    AnalyticUniformizationExists := by
  intro K _ A L _ _ _ 𝒢 τ
  obtain ⟨g, hg⟩ := abVar_dim_finite K A
  exact ⟨g, h K A L 𝒢 τ g hg⟩

/-- The metrization at `g = dim A` (proved from the four hypotheses): lattice `⋀^g ω_𝒢`, periods
and coefficient maps from the uniformizations. -/
theorem exists_metrization_of_dim (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) {K : Type} [Field K] {A : AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L) (g : ℕ)
    (hg : A.dim = g) : ∃ M : MetrizedModel A L g, M.model = 𝒢 := by
  obtain ⟨hfr, hlat⟩ := hH K A L 𝒢 g hg
  choose Λ Φ hdisc hZ hΦ using fun τ => hU K A L 𝒢 τ g hg
  choose c hc using fun τ => hJ K A L 𝒢 τ g (Λ τ) (Φ τ) (hΦ τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    haveI := hdisc τ
    obtain ⟨f, hf⟩ := hN K A L 𝒢 τ g hg (Λ τ) (Φ τ) (hZ τ) (hΦ τ)
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

/-- **`MetrizationExists` from `HodgeLatticeTheorem`, the leaf `AnalyticUniformizationOfDim` and
the glue `JacDetDescends`, `JacDetNondegenerate` (proved).** -/
theorem metrizationExists_of (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) : ZInQ.G0HeightAdd.MetrizationExists := by
  intro K _ A L _ _ _ 𝒢
  obtain ⟨g, hg⟩ := abVar_dim_finite K A
  obtain ⟨M, hM⟩ := exists_metrization_of_dim hH hU hJ hN 𝒢 g hg
  exact ⟨g, M, hM⟩

/-- Every metrization has dimension `dim A` (proved, from the four hypotheses and
`metrizationDimUnique`). -/
theorem metrized_dim_eq (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) {K : Type} [Field K] {A : AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ} (M : MetrizedModel A L g) :
    A.dim = g := by
  obtain ⟨d, hd⟩ := abVar_dim_finite K A
  obtain ⟨M', hM'⟩ := exists_metrization_of_dim hH hU hJ hN M.model d hd
  rw [hd, metrizationDimUnique K A L d g M' M hM']

end ZInQ.Metrization



/-! ## metrization (2026-11-13): `ProductMetrizationGeo` reduced

`ProductMetrizationGeo` (P2a-geo) follows from `JacDetDescends` (shared with `MetrizationExists`),
`ProductUniformization` (glue: `Φ₁ × Φ₂` is an analytic uniformization of the product model),
`ProductLatticeFacts` (pure Mathlib glue: `Λ₁ × Λ₂` is a full lattice and covolumes multiply)
and `ProductHodgeCompat` (glue: `⋀^{top}ω_{𝒢P} = ⋀ω₁ ⊗ ⋀ω₂` with the block-diagonal Jacobian). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- The first `g₁` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def leftBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₁ → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Fin.castAdd g₂ i)

/-- The last `g₂` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def rightBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ) :=
  LinearMap.pi fun j => LinearMap.proj (Fin.natAdd g₁ j)

/-- The product lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁} × ℂ^{g₂} = ℂ^{g₁+g₂}` (coordinates `Fin.append`). -/
noncomputable def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) : Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (leftBlock g₁ g₂).toAddMonoidHom.toIntLinearMap ⊓
    Λ₂.comap (rightBlock g₁ g₂).toAddMonoidHom.toIntLinearMap

/-- The product map `ℂ^{g₁+g₂} → 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ ≅ 𝒢P(ℂ)_τ`, `z ↦ e⁻¹(Φ₁(z'), Φ₂(z''))`. -/
noncomputable def prodPts {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) :
    (Fin (g₁ + g₂) → ℂ) → 𝒢P.Pts τ :=
  fun z => lift (Φ₁ (leftBlock g₁ g₂ z)) (Φ₂ (rightBlock g₁ g₂ z)) ≫ e.inv

/-- **Glue (pure Mathlib): product lattices.** If `Λ₁ ⊂ ℂ^{g₁}`, `Λ₂ ⊂ ℂ^{g₂}` are full lattices,
so is `Λ₁ × Λ₂ ⊂ ℂ^{g₁+g₂}`, and `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂` (the product of fundamental
domains is a fundamental domain; `volume` on `Fin (g₁+g₂) → ℂ` is the product measure under
`Fin.append`). STANDARD; provable from Mathlib, not yet proved. -/
def ProductLatticeFacts : Prop :=
  ∀ (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    [DiscreteTopology Λ₁] [DiscreteTopology Λ₂], IsZLattice ℝ Λ₁ → IsZLattice ℝ Λ₂ →
    ∃ (_ : DiscreteTopology (prodLattice Λ₁ Λ₂)) (_ : IsZLattice ℝ (prodLattice Λ₁ Λ₂)),
      ZLattice.covolume (prodLattice Λ₁ Λ₂) = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂

/-- **Glue (the product uniformization).** For an isomorphism `e : 𝒢P ≅ 𝒢₁ ×_{𝓞_L} 𝒢₂` of
`𝓞_L`-schemes whose components are homomorphisms, and analytic uniformizations `Φᵢ` of `𝒢ᵢ(ℂ)_τ`
with kernels `Λᵢ`, `prodPts e Φ₁ Φ₂` is an analytic uniformization of `𝒢P(ℂ)_τ` with kernel
`Λ₁ × Λ₂`. Why true: the homomorphism, kernel and surjectivity clauses follow from `e` and the
universal property of `⊗` (points of a product are pairs of points); openness of `dom` and
holomorphy: a Zariski open of `𝒢₁ ×_{𝓞_L} 𝒢₂` is covered by basic opens `D(h)` of products
`Spec(R₁ ⊗ R₂)` of affine opens, and a regular function there is `a/hⁿ` with
`a, h ∈ R₁ ⊗_{𝓞_L} R₂`, i.e. sums of products of functions holomorphic along `Φ₁` resp. `Φ₂`
(STANDARD). Unproved (Mathlib lacks the affine-cover description of fibre products used here). -/
def ProductUniformization : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G), IsMonHom (e.hom ≫ fst _ _) → IsMonHom (e.hom ≫ snd _ _) →
    ∀ (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
      (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂)

/-- **Glue (the Hodge line of a product, with its coefficient).** For `e : 𝒢P ≅ 𝒢₁ × 𝒢₂` as in
`ProductUniformization` and metrizations `M₁`, `M₂` of `𝒢₁`, `𝒢₂`: `hodgeSpace (g₁+g₂)` of `𝒢P` is
an `L`-line, and there are nonzero `s ∈ ⋀^{g₁+g₂}ω_{𝒢P}`, `sᵢ ∈ ⋀^{gᵢ}ω_{𝒢ᵢ}` with
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]` such that, at every `τ`, every `τ`-semilinear map `c`
that sends wedges to the Jacobians of `prodPts e Φ₁ Φ₂` (for uniformizations `Φᵢ` computing `Mᵢ`'s
coefficients) has `c s = coeff₁(s₁) · coeff₂(s₂)`. Why true (STANDARD): take `s₁ = a₁ · 1⊗df₁`,
`s₂ = a₂ · 1⊗df₂` and `s = p₁*s₁ ∧ p₂*s₂ = a₁a₂ · 1 ⊗ d(p₁*f₁) ∧ d(p₂*f₂)`. Algebra: for the
smooth group scheme `𝒢₁ ×_{𝓞_L} 𝒢₂`, `e*Ω¹ = e₁*Ω¹ ⊕ e₂*Ω¹`, so `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` (and the
cotangent space at `ξ` is the direct sum, so `⋀^{g₁+g₂}` is the tensor product of the two lines);
for invertible `𝓞_L`-modules the index of `𝓞s₁ ⊗ 𝓞s₂` in `⋀ω₁ ⊗ ⋀ω₂` is the product. Analysis:
`(p₁*f) ∘ prodPts = f ∘ Φ₁ ∘ leftBlock` near `0`, so the Jacobian matrix of `d(p₁*f₁) ∧ d(p₂*f₂)`
is block diagonal and `jacDet` is the product. Unproved (stalks and differentials of fibre products
of schemes are not in Mathlib). -/
def ProductHodgeCompat : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G), IsMonHom (e.hom ≫ fst _ _) →
    IsMonHom (e.hom ≫ snd _ _) →
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (s : 𝒢P.hodgeSpace (g₁ + g₂)) (s₁ : M₁.model.hodgeSpace g₁) (s₂ : M₂.model.hodgeSpace g₂),
      s ∈ 𝒢P.detLattice (g₁ + g₂) ∧ s ≠ 0 ∧ s₁ ∈ M₁.hodge.lattice ∧ s₁ ≠ 0 ∧
      s₂ ∈ M₂.hodge.lattice ∧ s₂ ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) s =
        secIndex M₁.hodge.lattice s₁ * secIndex M₂.hodge.lattice s₂ ∧
      ∀ (τ : L →+* ℂ) (Φ₁ : (Fin g₁ → ℂ) → M₁.model.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → M₂.model.Pts τ),
        M₁.model.IsAnalyticUniformization τ (M₁.hodge.periods τ) Φ₁ →
        (∀ f, M₁.hodge.coeff τ (M₁.model.wedge f) = M₁.model.jacDet Φ₁ f) →
        M₂.model.IsAnalyticUniformization τ (M₂.hodge.periods τ) Φ₂ →
        (∀ f, M₂.hodge.coeff τ (M₂.model.wedge f) = M₂.model.jacDet Φ₂ f) →
        ∀ c : 𝒢P.hodgeSpace (g₁ + g₂) →ₛₗ[τ] ℂ,
          (∀ f, c (𝒢P.wedge f) = 𝒢P.jacDet (prodPts e Φ₁ Φ₂) f) →
          c s = M₁.hodge.coeff τ s₁ * M₂.hodge.coeff τ s₂

/-- **`ProductMetrizationGeo` from `JacDetDescends`, `ProductUniformization`,
`ProductLatticeFacts` and `ProductHodgeCompat` (proved).** `MP` has lattice `⋀^{g₁+g₂}ω_{𝒢P}`,
periods `Λ₁ × Λ₂` and coefficients from `prodPts e Φ₁ Φ₂`. -/
theorem productMetrizationGeo_of (hJ : JacDetDescends) (hPU : ProductUniformization)
    (hPL : ProductLatticeFacts) (hPC : ProductHodgeCompat) :
    ZInQ.G0HeightAdd.ProductMetrizationGeo := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  subst h₁ h₂
  obtain ⟨e, hfst, hsnd, -⟩ := hP
  obtain ⟨hfr, s, s₁, s₂, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hcoeff⟩ :=
    hPC K A B C L 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  choose Φ₁ hΦ₁ hc₁ using M₁.arch
  choose Φ₂ hΦ₂ hc₂ using M₂.arch
  have hΦP := fun τ => hPU K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ (Φ₁ τ) (Φ₂ τ)
    (hΦ₁ τ) (hΦ₂ τ)
  choose c hc using fun τ => hJ K C L 𝒢P τ (g₁ + g₂) _ _ (hΦP τ)
  have hlatf : ∀ τ : L →+* ℂ, ∃ (_ : DiscreteTopology
      (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)))
      (_ : IsZLattice ℝ (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ))),
      ZLattice.covolume (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)) =
        ZLattice.covolume (M₁.hodge.periods τ) * ZLattice.covolume (M₂.hodge.periods τ) := by
    intro τ
    haveI := M₁.hodge.periods_discrete τ
    haveI := M₂.hodge.periods_discrete τ
    exact hPL g₁ g₂ _ _ (M₁.hodge.periods_isZLattice τ) (M₂.hodge.periods_isZLattice τ)
  choose hdisc hZ hcov using hlatf
  have hcs : ∀ τ, c τ s = M₁.hodge.coeff τ s₁ * M₂.hodge.coeff τ s₂ := fun τ =>
    hcoeff τ (Φ₁ τ) (Φ₂ τ) (hΦ₁ τ) (hc₁ τ) (hΦ₂ τ) (hc₂ τ) (c τ) (hc τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    have h := hcs τ
    rw [h0, LinearMap.zero_apply] at h
    exact mul_ne_zero (M₁.hodge.coeff_apply_ne_zero τ hs₁0)
      (M₂.hodge.coeff_apply_ne_zero τ hs₂0) h.symm
  have hlat : ∃ t ∈ 𝒢P.detLattice (g₁ + g₂), t ≠ 0 ∧ secIndex (𝒢P.detLattice (g₁ + g₂)) t ≠ 0 :=
    ⟨s, hs, hs0, by
      rw [hidx]
      exact mul_ne_zero (M₁.hodge.hodgeBundle.secIndex_ne_zero hs₁ hs₁0)
        (M₂.hodge.hodgeBundle.secIndex_ne_zero hs₂ hs₂0)⟩
  let MP : MetrizedModel C L (g₁ + g₂) :=
    { model := 𝒢P
      hodge :=
        { lattice := 𝒢P.detLattice (g₁ + g₂)
          finrank_eq_one := hfr
          isLattice := hlat
          periods := fun τ => prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)
          periods_discrete := hdisc
          periods_isZLattice := hZ
          coeff := c
          coeff_ne_zero := hc0 }
      lattice_eq := rfl
      arch := fun τ => ⟨prodPts e (Φ₁ τ) (Φ₂ τ), hΦP τ, hc τ⟩ }
  exact ⟨MP, s, s₁, s₂, rfl, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hcs, hcov⟩

end ZInQ.Metrization



/-! ## metrization: `ProductLatticeFacts`, proved (body of ProdLattice.lean, section Proof) -/

namespace ZInQ.Metrization

open MeasureTheory

section Proof

variable {g₁ g₂ : ℕ}

@[simp] theorem leftBlock_apply (z : Fin (g₁ + g₂) → ℂ) (i : Fin g₁) :
    leftBlock g₁ g₂ z i = z (Fin.castAdd g₂ i) := rfl

@[simp] theorem rightBlock_apply (z : Fin (g₁ + g₂) → ℂ) (j : Fin g₂) :
    rightBlock g₁ g₂ z j = z (Fin.natAdd g₁ j) := rfl

theorem mem_prodLattice {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {z : Fin (g₁ + g₂) → ℂ} :
    z ∈ prodLattice Λ₁ Λ₂ ↔ leftBlock g₁ g₂ z ∈ Λ₁ ∧ rightBlock g₁ g₂ z ∈ Λ₂ := Iff.rfl

theorem eq_of_blocks {z w : Fin (g₁ + g₂) → ℂ} (h1 : leftBlock g₁ g₂ z = leftBlock g₁ g₂ w)
    (h2 : rightBlock g₁ g₂ z = rightBlock g₁ g₂ w) : z = w := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact congrFun h1 i
  · exact congrFun h2 j

@[simp] theorem leftBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    leftBlock g₁ g₂ (Fin.append x y) = x := by
  funext i; simp

@[simp] theorem rightBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    rightBlock g₁ g₂ (Fin.append x y) = y := by
  funext j; simp

/-- `ℂ^{g₁+g₂} ≃ ℂ^{g₁} × ℂ^{g₂}` over `ℝ`. -/
noncomputable def blockLinearEquiv (g₁ g₂ : ℕ) :
    (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (leftBlock g₁ g₂ z, rightBlock g₁ g₂ z)
  invFun p := Fin.append p.1 p.2
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp
  left_inv z := eq_of_blocks (by simp) (by simp)
  right_inv p := by ext <;> simp

/-- `blockLinearEquiv` preserves `volume`. -/
theorem measurePreserving_blockLinearEquiv (g₁ g₂ : ℕ) :
    MeasurePreserving (blockLinearEquiv g₁ g₂) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)
    (finSumFinEquiv (m := g₁) (n := g₂)).symm
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)).symm
  have hc := h2.comp h1
  convert hc using 1
  funext z
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.coe_piCongrLeft]
    rw [show (Sum.inl i : Fin g₁ ⊕ Fin g₂) = finSumFinEquiv.symm (Fin.castAdd g₂ i) by simp,
      Equiv.piCongrLeft_apply_apply]
    rfl
  · simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.coe_piCongrLeft]
    rw [show (Sum.inr j : Fin g₁ ⊕ Fin g₂) = finSumFinEquiv.symm (Fin.natAdd g₁ j) by simp,
      Equiv.piCongrLeft_apply_apply]
    rfl

/-- A full lattice has a measurable fundamental domain with unique translates, whose volume is
the covolume. -/
theorem exists_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ F : Set E, MeasurableSet F ∧ (∀ x, ∃! g : Λ, (g : E) + x ∈ F) ∧
      ZLattice.covolume Λ μ = μ.real F := by
  let b := Module.Free.chooseBasis ℤ Λ
  let b' := b.ofZLatticeBasis ℝ Λ
  have hspan : Submodule.span ℤ (Set.range b') = Λ := b.ofZLatticeBasis_span ℝ Λ
  refine ⟨ZSpan.fundamentalDomain b', ZSpan.fundamentalDomain_measurableSet b', fun x => ?_,
    ZLattice.covolume_eq_measure_fundamentalDomain Λ μ (ZLattice.isAddFundamentalDomain b μ)⟩
  obtain ⟨⟨v, hv⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b' x
  refine ⟨⟨v, hspan ▸ hv⟩, h1, fun w hw => ?_⟩
  have h3 := h2 ⟨w, hspan.symm ▸ w.2⟩ hw
  have h4 : (w : E) = v := congrArg Subtype.val h3
  exact Subtype.ext h4

/-- **`ProductLatticeFacts`, proved.** -/
theorem productLatticeFacts : ProductLatticeFacts := by
  intro g₁ g₂ Λ₁ Λ₂ _ _ hZ₁ hZ₂
  -- discreteness: inject into `Λ₁ × Λ₂`
  have hdisc : DiscreteTopology (prodLattice Λ₁ Λ₂) := by
    let f : prodLattice Λ₁ Λ₂ → Λ₁ × Λ₂ := fun z =>
      (⟨leftBlock g₁ g₂ z, z.2.1⟩, ⟨rightBlock g₁ g₂ z, z.2.2⟩)
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · refine Continuous.prodMk ?_ ?_
      · exact Continuous.subtype_mk
          ((leftBlock g₁ g₂).continuous_of_finiteDimensional.comp continuous_subtype_val) _
      · exact Continuous.subtype_mk
          ((rightBlock g₁ g₂).continuous_of_finiteDimensional.comp continuous_subtype_val) _
    · intro z w h
      have h1 := congrArg (fun p => (p.1 : Fin g₁ → ℂ)) h
      have h2 := congrArg (fun p => (p.2 : Fin g₂ → ℂ)) h
      exact Subtype.ext (eq_of_blocks h1 h2)
  -- full rank
  have hZ : IsZLattice ℝ (prodLattice Λ₁ Λ₂) := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    rintro z -
    have hz : z = Fin.append (leftBlock g₁ g₂ z) 0 + Fin.append 0 (rightBlock g₁ g₂ z) :=
      eq_of_blocks (by funext i; simp) (by funext j; simp)
    rw [hz]
    refine Submodule.add_mem _ ?_ ?_
    · let ι₁ : (Fin g₁ → ℂ) →ₗ[ℝ] (Fin (g₁ + g₂) → ℂ) :=
        (blockLinearEquiv g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _
      have hι : ∀ x, ι₁ x = Fin.append x 0 := fun x => rfl
      have hle : (Submodule.span ℝ (Λ₁ : Set (Fin g₁ → ℂ))).map ι₁ ≤
          Submodule.span ℝ (prodLattice Λ₁ Λ₂ : Set (Fin (g₁ + g₂) → ℂ)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨x, hx, rfl⟩
        rw [hι]
        exact ⟨by simpa using hx, by simp [Submodule.zero_mem]⟩
      apply hle
      rw [hZ₁.span_top]
      exact ⟨leftBlock g₁ g₂ z, Submodule.mem_top, hι _⟩
    · let ι₂ : (Fin g₂ → ℂ) →ₗ[ℝ] (Fin (g₁ + g₂) → ℂ) :=
        (blockLinearEquiv g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inr ℝ _ _
      have hι : ∀ y, ι₂ y = Fin.append 0 y := fun y => rfl
      have hle : (Submodule.span ℝ (Λ₂ : Set (Fin g₂ → ℂ))).map ι₂ ≤
          Submodule.span ℝ (prodLattice Λ₁ Λ₂ : Set (Fin (g₁ + g₂) → ℂ)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨y, hy, rfl⟩
        rw [hι]
        exact ⟨by simp [Submodule.zero_mem], by simpa using hy⟩
      apply hle
      rw [hZ₂.span_top]
      exact ⟨rightBlock g₁ g₂ z, Submodule.mem_top, hι _⟩
  refine ⟨hdisc, hZ, ?_⟩
  -- covolume
  obtain ⟨F₁, hF₁m, hF₁u, hF₁c⟩ := exists_fd Λ₁ volume
  obtain ⟨F₂, hF₂m, hF₂u, hF₂c⟩ := exists_fd Λ₂ volume
  let φ := blockLinearEquiv g₁ g₂
  have hφm : Measurable φ := (measurePreserving_blockLinearEquiv g₁ g₂).measurable
  let F : Set (Fin (g₁ + g₂) → ℂ) := φ ⁻¹' (F₁ ×ˢ F₂)
  have hFd : IsAddFundamentalDomain (prodLattice Λ₁ Λ₂) F volume := by
    refine IsAddFundamentalDomain.mk' ((hφm (hF₁m.prod hF₂m)).nullMeasurableSet) fun z => ?_
    obtain ⟨a, ha, hau⟩ := hF₁u (leftBlock g₁ g₂ z)
    obtain ⟨b, hb, hbu⟩ := hF₂u (rightBlock g₁ g₂ z)
    refine ⟨⟨Fin.append (a : Fin g₁ → ℂ) (b : Fin g₂ → ℂ),
      mem_prodLattice.mpr ⟨by simpa using a.2, by simpa using b.2⟩⟩, ?_, fun w hw => ?_⟩
    · beta_reduce
      rw [Submodule.vadd_def, vadd_eq_add]
      show (leftBlock g₁ g₂ _, rightBlock g₁ g₂ _) ∈ F₁ ×ˢ F₂
      simpa using ⟨ha, hb⟩
    · beta_reduce at hw
      rw [Submodule.vadd_def, vadd_eq_add] at hw
      have hw' : (leftBlock g₁ g₂ ((w : Fin (g₁ + g₂) → ℂ) + z),
          rightBlock g₁ g₂ ((w : Fin (g₁ + g₂) → ℂ) + z)) ∈ F₁ ×ˢ F₂ := hw
      simp only [map_add, Set.mem_prod] at hw'
      have e1 := hau ⟨leftBlock g₁ g₂ w, w.2.1⟩ hw'.1
      have e2 := hbu ⟨rightBlock g₁ g₂ w, w.2.2⟩ hw'.2
      apply Subtype.ext
      apply eq_of_blocks
      · simpa using congrArg Subtype.val e1
      · simpa using congrArg Subtype.val e2
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hFd, hF₁c, hF₂c,
    (measurePreserving_blockLinearEquiv g₁ g₂).measureReal_preimage
      (hF₁m.prod hF₂m).nullMeasurableSet,
    Measure.volume_eq_prod, measureReal_def, measureReal_def, measureReal_def,
    Measure.prod_prod, ENNReal.toReal_mul]

end Proof

end ZInQ.Metrization



/-! ## metrization: what remains of `ProductMetrizationGeo` and `HeightAdditivity` -/

namespace ZInQ.Metrization

/-- **`ProductMetrizationGeo` from `JacDetDescends`, `ProductUniformization` and
`ProductHodgeCompat`** (`ProductLatticeFacts` proved). -/
theorem productMetrizationGeo_of' (hJ : JacDetDescends) (hPU : ProductUniformization)
    (hPC : ProductHodgeCompat) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of hJ hPU productLatticeFacts hPC

end ZInQ.Metrization

namespace HSyn.G0Split

-- rv-gluepieces2: removed (uses g0-heightadd's `heightAdditivity_of_geo`, not in G0Assemble): theorem heightAdditivity_of_metrization 

end HSyn.G0Split



/-! ## metrization: the algebraic half of `ProductUniformization`, proved

`prodPts e Φ₁ Φ₂` is a surjective homomorphism with kernel `Λ₁ × Λ₂` (from `e` and the universal
property of `⊗`); `ProductUniformization` is reduced to `ProductUniformizationAnalytic` (openness
of `dom` and holomorphy). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section ProdPtsAlg

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}

theorem prodPts_comp_fst (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ fst _ _ = Φ₁ (leftBlock g₁ g₂ z) := by
  simp [prodPts]

theorem prodPts_comp_snd (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ snd _ _ = Φ₂ (rightBlock g₁ g₂ z) := by
  simp [prodPts]

theorem pts_ext {p q : 𝒢P.Pts τ} (h1 : p ≫ e.hom ≫ fst _ _ = q ≫ e.hom ≫ fst _ _)
    (h2 : p ≫ e.hom ≫ snd _ _ = q ≫ e.hom ≫ snd _ _) : p = q := by
  rw [← cancel_mono e.hom]
  apply CartesianMonoidalCategory.hom_ext
  · simpa using h1
  · simpa using h2

/-- **The algebraic clauses of `IsAnalyticUniformization` for `prodPts` (proved).** -/
theorem prodPts_alg (hfst : IsMonHom (e.hom ≫ fst _ _)) (hsnd : IsMonHom (e.hom ≫ snd _ _))
    {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}
    (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁) (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    (∀ z w, prodPts e Φ₁ Φ₂ (z + w) = prodPts e Φ₁ Φ₂ z * prodPts e Φ₁ Φ₂ w) ∧
    (∀ z, prodPts e Φ₁ Φ₂ z = 1 ↔ z ∈ prodLattice Λ₁ Λ₂) ∧
    Function.Surjective (prodPts e Φ₁ Φ₂) := by
  refine ⟨fun z w => ?_, fun z => ?_, fun p => ?_⟩
  · apply pts_ext e
    · rw [MonObj.mul_comp, prodPts_comp_fst, prodPts_comp_fst, prodPts_comp_fst, map_add,
        h₁.1]
    · rw [MonObj.mul_comp, prodPts_comp_snd, prodPts_comp_snd, prodPts_comp_snd, map_add,
        h₂.1]
  · constructor
    · intro h
      have e1 : Φ₁ (leftBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_fst e Φ₁ Φ₂ z, h, MonObj.one_comp]
      have e2 : Φ₂ (rightBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_snd e Φ₁ Φ₂ z, h, MonObj.one_comp]
      exact mem_prodLattice.mpr ⟨(h₁.2.1 _).mp e1, (h₂.2.1 _).mp e2⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := mem_prodLattice.mp hz
      apply pts_ext e
      · rw [prodPts_comp_fst, MonObj.one_comp, (h₁.2.1 _).mpr hz1]
      · rw [prodPts_comp_snd, MonObj.one_comp, (h₂.2.1 _).mpr hz2]
  · obtain ⟨x, hx⟩ := h₁.2.2.1 (p ≫ e.hom ≫ fst _ _)
    obtain ⟨y, hy⟩ := h₂.2.2.1 (p ≫ e.hom ≫ snd _ _)
    refine ⟨Fin.append x y, pts_ext e ?_ ?_⟩
    · rw [prodPts_comp_fst, leftBlock_append, hx]
    · rw [prodPts_comp_snd, rightBlock_append, hy]

end ProdPtsAlg

/-- **Glue (the analytic half of the product uniformization).** With the hypotheses of
`ProductUniformization`: each `dom (prodPts e Φ₁ Φ₂) U` is open and each regular function on `U`
is holomorphic along `prodPts e Φ₁ Φ₂` there. Why true: as in `ProductUniformization` (basic opens
`D(h)` of products of affine opens; regular functions `a/hⁿ`, `a, h ∈ R₁ ⊗_{𝓞_L} R₂`). STANDARD,
unproved. -/
def ProductUniformizationAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G), IsMonHom (e.hom ≫ fst _ _) → IsMonHom (e.hom ≫ snd _ _) →
    ∀ (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
      (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      (∀ U, IsOpen (𝒢P.dom (prodPts e Φ₁ Φ₂) U)) ∧
      (∀ U (s : Γ(𝒢P.G.left, U)), DifferentiableOn ℂ
        (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) (𝒢P.dom (prodPts e Φ₁ Φ₂) U))

/-- **`ProductUniformization` from `ProductUniformizationAnalytic` (proved).** -/
theorem productUniformization_of (h : ProductUniformizationAnalytic) : ProductUniformization := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  obtain ⟨hhom, hker, hsurj⟩ := prodPts_alg e hfst hsnd h₁ h₂
  obtain ⟨hopen, hdiff⟩ := h K A B C L 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  exact ⟨hhom, hker, hsurj, hopen, hdiff⟩

end ZInQ.Metrization

namespace HSyn.G0Split

-- rv-gluepieces2: removed (depends on g0-heightadd's `heightAdditivity_of_geo`, not in G0Assemble): heightAdditivity_of_metrization'

end HSyn.G0Split



/-! ## metrization: `JacDetDescends` reduced to four calculus properties of `jacDet`

The algebra (universal property of `⋀^g`, extension of scalars `L ⊗_{𝓞_L} -` along `τ`) is
proved; what remains (`JacDetMultilinear`) are four statements about the derivative at `0` of
germs composed with `Φ`. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

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
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
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

namespace HSyn.G0Split

-- rv-gluepieces2: removed (depends on g0-heightadd's `heightAdditivity_of_geo`, not in G0Assemble): heightAdditivity_of_metrization''

end HSyn.G0Split



/-! ## metrization: `ProductHodgeCompat` split into an algebraic and an analytic Prop

`pullGerm φ : 𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}` (pull-back of germs along a homomorphism of group models; it
needs `φ(ξ_𝒢) = ξ_ℋ`, proved from `IsMonHom`). `ProductHodgeLattice` (algebra: `s = p₁*s₁ ∧ p₂*s₂`
lies in the lattice with multiplicative index) and `ProductJacobian` (analysis: block-diagonal
Jacobian) give `ProductHodgeCompat` (with `ProductUniformization`). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section Pull

variable {K : Type} [Field K] {A C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A homomorphism of group models maps the identity `ξ` of the generic fibre to `ξ` (proved). -/
theorem map_genericUnit_of_isMonHom {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : φ.left 𝒢.genericUnit = ℋ.genericUnit := by
  have h1 : η[𝒢.G] ≫ φ = η[ℋ.G] := IsMonHom.one_hom φ
  have h2 : (η[𝒢.G]).left ≫ φ.left = (η[ℋ.G]).left := by rw [← Over.comp_left, h1]
  show φ.left ((η[𝒢.G]).left (genericPt L)) = (η[ℋ.G]).left (genericPt L)
  rw [← h2]
  rfl

/-- Pull-back of germs at `ξ` along a homomorphism of group models: `𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}`. -/
noncomputable def pullGerm {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : ℋ.genStalk ⟶ 𝒢.genStalk :=
  ℋ.G.left.presheaf.stalkSpecializes
      ((congrArg (fun x => x ⤳ ℋ.genericUnit) (map_genericUnit_of_isMonHom φ)).mpr
        specializes_rfl) ≫
    φ.left.stalkMap 𝒢.genericUnit

end Pull

/-- **Glue (algebra: the Hodge lattice of a product).** For `e : 𝒢P ≅ M₁.model × M₂.model` with
homomorphic components: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line, and there are germ tuples
`f₁, f₂` and their pull-backs `f = (p₁*f₁, p₂*f₂)`, and `a₁, a₂ ∈ L`, such that `sᵢ = aᵢ · 1⊗dfᵢ`
are nonzero elements of `⋀ω_{𝒢ᵢ}`, `s = a₁a₂ · 1⊗df` is a nonzero element of `⋀ω_{𝒢P}`, and
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`. Why true (STANDARD): `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` and
`𝔪_ξ/𝔪_ξ² = p₁*C₁ ⊕ p₂*C₂` for a product of smooth group schemes (EGA IV 17.2.3, UNVERIFIED
locator), so `⋀^{g₁+g₂}` is the tensor product of the two lines; for invertible `𝓞_L`-modules
indices multiply (norms of ideals). Unproved (stalks and differentials of fibre products are
not in Mathlib). -/
def ProductHodgeLattice : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal M₁.model.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal M₂.model.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk) (a₁ a₂ : L),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) ∧
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) ∧
      a₁ • M₁.model.wedge f₁ ∈ M₁.hodge.lattice ∧ a₁ • M₁.model.wedge f₁ ≠ 0 ∧
      a₂ • M₂.model.wedge f₂ ∈ M₂.hodge.lattice ∧ a₂ • M₂.model.wedge f₂ ≠ 0 ∧
      (a₁ * a₂) • 𝒢P.wedge f ∈ 𝒢P.detLattice (g₁ + g₂) ∧ (a₁ * a₂) • 𝒢P.wedge f ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) ((a₁ * a₂) • 𝒢P.wedge f) =
        secIndex M₁.hodge.lattice (a₁ • M₁.model.wedge f₁) *
          secIndex M₂.hodge.lattice (a₂ • M₂.model.wedge f₂)

/-- **Glue (analysis: the Jacobian of the product uniformization is block diagonal).** If
`prodPts e Φ₁ Φ₂` is an analytic uniformization and `f = (p₁*f₁, p₂*f₂)`, then
`jacDet (prodPts e Φ₁ Φ₂) f = jacDet Φ₁ f₁ · jacDet Φ₂ f₂`. Why true: `p₁ ∘ prodPts = Φ₁ ∘ leftBlock`
(`prodPts_comp_fst`), so near `0` the germ `(p₁*f₁ᵢ) ∘ prodPts` is `f₁ᵢ ∘ Φ₁ ∘ leftBlock` (the
representatives agree on an open `V ∋ ξ` and `dom (prodPts) V` is open), whose derivative
vanishes on the last `g₂` coordinates; the matrix is block diagonal (`Matrix.det_fromBlocks_zero₂₁`
after `finSumFinEquiv`). Elementary, unproved (needs the `evalAt`/stalk compatibilities of
`JacDetMultilinear` and functoriality of `evalAt` along morphisms). -/
def ProductJacobian : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _))
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂) →
    ∀ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal 𝒢₁.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal 𝒢₂.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) →
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) →
      𝒢P.jacDet (prodPts e Φ₁ Φ₂) f = 𝒢₁.jacDet Φ₁ f₁ * 𝒢₂.jacDet Φ₂ f₂

/-- **`ProductHodgeCompat` from `ProductUniformization`, `ProductHodgeLattice` and
`ProductJacobian` (proved).** -/
theorem productHodgeCompat_of (hPU : ProductUniformization) (hL : ProductHodgeLattice)
    (hJ : ProductJacobian) : ProductHodgeCompat := by
  intro K _ A B C L _ _ _ 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  obtain ⟨hfr, f₁, f₂, f, a₁, a₂, hf1, hf2, hs₁, hs₁0, hs₂, hs₂0, hs, hs0, hidx⟩ :=
    hL K A B C L 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  refine ⟨hfr, (a₁ * a₂) • 𝒢P.wedge f, a₁ • M₁.model.wedge f₁, a₂ • M₂.model.wedge f₂, hs, hs0,
    hs₁, hs₁0, hs₂, hs₂0, hidx, ?_⟩
  intro τ Φ₁ Φ₂ h₁ hc₁ h₂ hc₂ c hc
  have hΦP := hPU K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ Φ₁ Φ₂ h₁ h₂
  have hjac := hJ K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ Φ₁ Φ₂ h₁ h₂ hΦP
    f₁ f₂ f hf1 hf2
  rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hc, hc₁, hc₂, hjac, map_mul]
  simp only [smul_eq_mul]
  ring

end ZInQ.Metrization

namespace HSyn.G0Split

-- rv-gluepieces2: removed (depends on g0-heightadd's `heightAdditivity_of_geo`, not in G0Assemble): heightAdditivity_of_metrization'''

end HSyn.G0Split



/-! ## metrization: two of the four clauses of `JacDetMultilinear`, proved

`Φ 0 = 1` lies over `ξ` (`zero_mem_dom`); `germAlong Φ t` agrees near `0` with `z ↦ evalAt (Φ z) U s`
for every representative `(U, s)` of `t` (`germAlong_eventuallyEq`); hence slot additivity
(`jacDet_update_add`). Vanishing on equal slots is immediate (`jacDet_eq_zero_of_eq`). What
remains is `JacDetClassScalar` (clauses (i) and (iii)). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Germ

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
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

/-- **Glue (the two remaining clauses of `JacDetMultilinear`).** (i) `jacDet Φ f` depends only on
the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`; (iii) multiplying slot `i` by the image of `a ∈ 𝓞_L` multiplies
`jacDet` by `τ(a)`. Why true: by `germAlong_eventuallyEq` it suffices that for `f ∈ 𝔪_ξ²` the
function `evalAt (Φ z) U s` of a representative has derivative `0` at `0` (it is a sum of products
of functions vanishing at `0`, as evaluation at a complex point over `ξ` kills `𝔪_ξ`: the induced
map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ` is local), and that the image of `a` evaluates to `τ(a)` (the point
lies over `Spec 𝓞_L` through `τ`). Unproved: needs `evalAt` through `Scheme.Hom.stalkMap` and
`ΓSpecIso`. -/
def JacDetClassScalar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
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

section Scalar

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `evalAt` is multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s * s') = 𝒢.evalAt p U s * 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

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
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
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

section ClassInv

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
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

/-- **`MetrizationExists` from `HodgeLatticeTheorem`, the leaf `AnalyticUniformizationOfDim` and
the glue `JacDetNondegenerate`.** -/
theorem metrizationExists_of' (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hN : JacDetNondegenerate) : ZInQ.G0HeightAdd.MetrizationExists :=
  metrizationExists_of hH hU jacDetDescends hN

/-- **`ProductMetrizationGeo` from `ProductUniformizationAnalytic`, `ProductHodgeLattice` and
`ProductJacobian`.** -/
theorem productMetrizationGeo_of'' (hPA : ProductUniformizationAnalytic)
    (hPL : ProductHodgeLattice) (hPJ : ProductJacobian) :
    ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of' jacDetDescends (productUniformization_of hPA)
    (productHodgeCompat_of (productUniformization_of hPA) hPL hPJ)

end ZInQ.Metrization

namespace HSyn.G0Split

-- rv-gluepieces2: removed (uses g0-heightadd's `heightAdditivity_of_geo`, not in G0Assemble): theorem heightAdditivity_of_metrization_final 

end HSyn.G0Split



/-! ## metrization: `ProductJacobian`, proved (block-diagonal Jacobian of `prodPts`) -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section ProdJac

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- Pull-back of a germ is the germ of the pulled-back section. -/
theorem pullGerm_germ {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) [IsMonHom φ]
    (U : ℋ.G.left.Opens) (m : ℋ.genericUnit ∈ U) (s : Γ(ℋ.G.left, U)) :
    (pullGerm φ).hom (ℋ.G.left.presheaf.germ U ℋ.genericUnit m s) =
      𝒢.G.left.presheaf.germ (φ.left ⁻¹ᵁ U) 𝒢.genericUnit
        (by show φ.left 𝒢.genericUnit ∈ U; rw [map_genericUnit_of_isMonHom φ]; exact m)
        (φ.left.app U s) := by
  unfold pullGerm
  rw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- `evalAt` along a morphism of models. -/
theorem evalAt_comp {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) {τ : L →+* ℂ}
    (p : 𝒢.Pts τ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (hp : ⊤ ≤ p.left ⁻¹ᵁ (φ.left ⁻¹ᵁ U)) :
    𝒢.evalAt p (φ.left ⁻¹ᵁ U) (φ.left.app U s) = ℋ.evalAt (p ≫ φ) U s := by
  have hp' : ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := hp
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp']
  rw [show (p ≫ φ).left.appLE U ⊤ hp' = φ.left.app U ≫ p.left.appLE (φ.left ⁻¹ᵁ U) ⊤ hp from
    Scheme.Hom.comp_appLE p.left φ.left U ⊤ hp']
  rfl

variable {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
  {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
  {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem germAlong_pull_fst_eventuallyEq (hΦ₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₁.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ fst _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₁.germAlong Φ₁ t (leftBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₁.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (leftBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (leftBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₁ hΦ₁ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ fst _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ fst _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₁.germAlong Φ₁ (𝒢₁.G.left.presheaf.germ U 𝒢₁.genericUnit m s) (leftBlock g₁ g₂ z) =
      𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_fst]

theorem germAlong_pull_snd_eventuallyEq (hΦ₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₂.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ snd _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₂.germAlong Φ₂ t (rightBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₂.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (rightBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (rightBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₂ hΦ₂ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ snd _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ snd _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₂.germAlong Φ₂ (𝒢₂.G.left.presheaf.germ U 𝒢₂.genericUnit m s) (rightBlock g₁ g₂ z) =
      𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_snd]

/-- Derivative of `F ∘ ℓ` for a linear `ℓ` on `ℂ^{g₁+g₂}` (chain rule). -/
theorem fderiv_comp_linear {n : ℕ} (ℓ : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (F : (Fin n → ℂ) → ℂ) (hF : DifferentiableAt ℂ F 0) (w : Fin (g₁ + g₂) → ℂ) :
    fderiv ℂ (fun z => F (ℓ z)) 0 w = fderiv ℂ F 0 (ℓ w) := by
  let ℓc := LinearMap.toContinuousLinearMap ℓ
  have hfun : (fun z => F (ℓ z)) = F ∘ ℓc := by
    funext z; simp [ℓc]
  have hF' : DifferentiableAt ℂ F (ℓc 0) := by rw [map_zero]; exact hF
  rw [hfun, fderiv_comp _ hF' ℓc.differentiableAt, ContinuousLinearMap.fderiv, map_zero]
  simp [ℓc]

end ProdJac

/-- **`ProductJacobian`, proved.** -/
theorem productJacobian : ProductJacobian := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ hΦ₁ hΦ₂ hΦP f₁ f₂ f hf1 hf2
  have hl : ∀ (i : Fin g₁) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.castAdd g₂ i) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (leftBlock g₁ g₂ w) := by
    intro i w
    rw [hf1 i, (germAlong_pull_fst_eventuallyEq e hΦ₁ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (leftBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₁ hΦ₁ _) w
  have hr : ∀ (j : Fin g₂) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.natAdd g₁ j) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ j : 𝒢₂.genStalk)) 0 (rightBlock g₁ g₂ w) := by
    intro j w
    rw [hf2 j, (germAlong_pull_snd_eventuallyEq e hΦ₂ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (rightBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₂ hΦ₂ _) w
  have hL1 : ∀ j : Fin g₁, leftBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  have hL2 : ∀ j : Fin g₂, leftBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR1 : ∀ j : Fin g₁, rightBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR2 : ∀ j : Fin g₂, rightBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  let J₁ : Matrix (Fin g₁) (Fin g₁) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (Pi.single j 1)
  let J₂ : Matrix (Fin g₂) (Fin g₂) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ i : 𝒢₂.genStalk)) 0 (Pi.single j 1)
  have hblock : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (Matrix.of fun i j : Fin (g₁ + g₂) =>
        fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f i : 𝒢P.genStalk)) 0 (Pi.single j 1)) =
      Matrix.fromBlocks J₁ 0 0 J₂ := by
    ext (i | i) (j | j)
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, J₁]
      rw [hl, hL1 j]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [hl, hL2, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [hr, hR1, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_right, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, J₂]
      rw [hr, hR2]
  unfold GroupModel.jacDet
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm, hblock, Matrix.det_fromBlocks_zero₂₁]

/-- **`ProductMetrizationGeo` from `ProductUniformizationAnalytic` and `ProductHodgeLattice`.** -/
theorem productMetrizationGeo_of''' (hPA : ProductUniformizationAnalytic)
    (hPL : ProductHodgeLattice) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of'' hPA hPL productJacobian

end ZInQ.Metrization

namespace HSyn.G0Split

-- rv-gluepieces2: removed (uses g0-heightadd's `heightAdditivity_of_geo`, not in G0Assemble): theorem heightAdditivity_of_metrization_v2 

end HSyn.G0Split



/-! ## metrization: `ProductUniformizationAnalytic` reduced to a statement about complex points

`ProductLocalStructure` (pure algebraic geometry, no analysis): near a complex point of
`𝒢₁ × 𝒢₂`, membership in a Zariski open `U` and a regular function on `U` are given, on
`V₁(ℂ) × V₂(ℂ)`, by sums of products of regular functions on opens `V₁ ⊂ 𝒢₁`, `V₂ ⊂ 𝒢₂`. The
analytic consequences (openness of `dom`, holomorphy) are proved. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

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
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
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

section Local

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
  {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem leftBlock_differentiable : Differentiable ℂ (leftBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (leftBlock g₁ g₂)).differentiable
  simpa using h

theorem rightBlock_differentiable : Differentiable ℂ (rightBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (rightBlock g₁ g₂)).differentiable
  simpa using h

/-- The local statement: every point of `dom (prodPts) U` has an open neighbourhood inside
`dom (prodPts) U` on which `z ↦ s(prodPts z)` is holomorphic. -/
theorem prodPts_local (hLS : ProductLocalStructure) (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (z₀ : Fin (g₁ + g₂) → ℂ) (hz₀ : z₀ ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U) :
    ∃ N : Set (Fin (g₁ + g₂) → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      DifferentiableOn ℂ (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) N := by
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hLS K A B C L 𝒢P 𝒢₁ 𝒢₂ e τ U s (Φ₁ (leftBlock g₁ g₂ z₀)) (Φ₂ (rightBlock g₁ g₂ z₀)) hz₀
  let O : Set (Fin (g₁ + g₂) → ℂ) :=
    leftBlock g₁ g₂ ⁻¹' 𝒢₁.dom Φ₁ V₁ ∩ rightBlock g₁ g₂ ⁻¹' 𝒢₂.dom Φ₂ V₂
  have hO : IsOpen O :=
    ((h₁.2.2.2.1 V₁).preimage (leftBlock_differentiable).continuous).inter
      ((h₂.2.2.2.1 V₂).preimage (rightBlock_differentiable).continuous)
  have hd1 : ∀ σ : Γ(𝒢₁.G.left, V₁),
      DifferentiableOn ℂ (fun z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ σ) O := fun σ =>
    (h₁.2.2.2.2 V₁ σ).comp (leftBlock_differentiable).differentiableOn (fun z hz => hz.1)
  have hd2 : ∀ σ : Γ(𝒢₂.G.left, V₂),
      DifferentiableOn ℂ (fun z => 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ σ) O := fun σ =>
    (h₂.2.2.2.2 V₂ σ).comp (rightBlock_differentiable).differentiableOn (fun z hz => hz.2)
  let H : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k)
  let Afun : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k)
  have hH : DifferentiableOn ℂ H O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k))
      (fun k _ => (hd1 (c k)).mul (hd2 (d k)))
    convert this using 1
    funext z
    simp [H, Finset.sum_apply]
  have hA : DifferentiableOn ℂ Afun O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k))
      (fun k _ => (hd1 (a k)).mul (hd2 (b k)))
    convert this using 1
    funext z
    simp [Afun, Finset.sum_apply]
  let N := O ∩ H ⁻¹' {0}ᶜ
  have hN : IsOpen N := hH.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hsub : ∀ z ∈ N, z ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s = Afun z / H z := by
    intro z hz
    obtain ⟨hmem, heq⟩ := hall _ _ hz.1.1 hz.1.2 hz.2
    refine ⟨hmem, ?_⟩
    rw [eq_div_iff hz.2]
    exact heq
  refine ⟨N, hN, ⟨⟨hV₁, hV₂⟩, hne⟩, fun z hz => (hsub z hz).1, ?_⟩
  have hdiv : DifferentiableOn ℂ (fun z => Afun z * (H z)⁻¹) N :=
    (hA.mono Set.inter_subset_left).mul
      ((hH.mono Set.inter_subset_left).inv (fun z hz => hz.2))
  refine hdiv.congr fun z hz => ?_
  rw [(hsub z hz).2, div_eq_mul_inv]

end Local

/-- **`ProductUniformizationAnalytic` from `ProductLocalStructure` (proved).** -/
theorem productUniformizationAnalytic_of (hLS : ProductLocalStructure) :
    ProductUniformizationAnalytic := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, hsub, -⟩ := prodPts_local e hLS h₁ h₂ U 0 z₀ hz₀
    exact ⟨N, hsub, hN, hz₀N⟩
  · intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, -, hd⟩ := prodPts_local e hLS h₁ h₂ U s z₀ hz₀
    exact ((hd z₀ hz₀N).differentiableAt (hN.mem_nhds hz₀N)).differentiableWithinAt

/-- **`ProductMetrizationGeo` from `ProductLocalStructure` and `ProductHodgeLattice`.** -/
theorem productMetrizationGeo_of_local (hLS : ProductLocalStructure)
    (hPL : ProductHodgeLattice) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of''' (productUniformizationAnalytic_of hLS) hPL

end ZInQ.Metrization

namespace HSyn.G0Split

-- rv-gluepieces2: removed (depends on g0-heightadd's `heightAdditivity_of_geo`, not in G0Assemble): heightAdditivity_of_metrization_v3

end HSyn.G0Split



namespace RvGP2
/-- Field 6 of `GluePieces2` is a theorem (metrization's proof). -/
theorem metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique :=
  ZInQ.Metrization.metrizationDimUnique
/-- Field 7 of `GluePieces2` from def-faltings' `HodgeLatticeTheorem`, the uniformization leaf and
one glue Prop (metrization's reduction). -/
theorem metrizationExists (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hU : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hN : ZInQ.Metrization.JacDetNondegenerate) : ZInQ.G0HeightAdd.MetrizationExists :=
  ZInQ.Metrization.metrizationExists_of' hH hU hN
/-- Field 8 of `GluePieces2` from two glue Props (metrization's reduction). -/
theorem productMetrizationGeo (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  ZInQ.Metrization.productMetrizationGeo_of_local hLS hPL
end RvGP2

#print axioms RvGP2.metrizationDimUnique
#print axioms RvGP2.metrizationExists
#print axioms RvGP2.productMetrizationGeo
