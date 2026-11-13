-- (g0-assemble2 edits: the `open PkgI4 …` lines name `_root_.HDec.PkgI4` explicitly, and also the extension namespace
-- `ZInQ.Contrib.G9.PkgI4` once it exists, since `open` resolves only the innermost match.)
/-! ## g0-assemble2: g9-derham (ZInQKernel/Contrib/G9/*.lean, verbatim minus imports and `#print` lines, in import
order; its I3Layer.lean, I4Layer.lean and Statement.lean are verbatim restatements, inside `ZInQ.Contrib.G9`,
of Leaves.lean's `PkgI3Sec`, `PkgI4Sec` and g0-mod-galois' `G9Glue`; they are omitted, so the names resolve to
Leaves.lean's and part 70's declarations) -/

-- ===== ZInQKernel/Contrib/G9/HenselEmb.lean

/-!
# G9: lifting a finite separable extension through a Henselian residue map

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Let `θ : R → Ω` be a surjective `K`-algebra map from a domain `R`, Henselian along `ker θ`, with
every `y ∉ ker θ` a unit (so `R` is local with maximal ideal `ker θ`), and `K` of characteristic
`0`. Then every `K`-embedding `ι_Ω : L → Ω` of a finite extension `L/K` lifts to `ι₀ : L → R`
(`exists_hensel_lift`), and the lift is unique and natural: for a `K`-algebra map `s : R → R` and
`τ : L → L` with `θ(s(ι₀ x)) = ι_Ω(τ x)`, `s ∘ ι₀ = ι₀ ∘ τ` (`hensel_lift_natural`).

Applied in `BdREmb.lean` to `θ⁺ : B_dR^+ → ℂ_p`: the classical embedding `ℚ̄_p ⊆ B_dR^+`
(STANDARD: Fontaine, Astérisque 223, Exp. II, §1.5; Brinon–Conrad, CMI notes, §4.4;
numbering UNVERIFIED), compatible with the Galois action.
-/

namespace ZInQ.Contrib.G9

open Polynomial

section Hensel

variable {K R Ω : Type*} [Field K] [CommRing R] [Algebra K R] [Field Ω] [Algebra K Ω]

/-- Two roots of `P` with the same residue at which `P'` does not vanish are equal. -/
theorem root_eq_of_theta [IsDomain R] (θ : R →ₐ[K] Ω) (P : K[X]) {a b : R}
    (ha : aeval a P = 0) (hb : aeval b P = 0) (hab : θ a = θ b)
    (hd : aeval (θ b) (derivative P) ≠ 0) : a = b := by
  set Q := P.map (algebraMap K R)
  obtain ⟨k, hk⟩ := Q.binomExpansion b (a - b)
  rw [add_sub_cancel, eval_map_algebraMap, eval_map_algebraMap, ha, hb, derivative_map,
    eval_map_algebraMap, zero_add] at hk
  have hfac : (a - b) * (aeval b (derivative P) + k * (a - b)) = 0 := by
    linear_combination -hk
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    apply hd
    have := congrArg θ h
    rwa [map_add, map_mul, map_sub, hab, sub_self, mul_zero, add_zero, map_zero,
      ← Polynomial.aeval_algHom_apply] at this

variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **Hensel lift** of `ι_Ω : L → Ω` through `θ`. -/
theorem exists_hensel_lift (θ : R →ₐ[K] Ω) (hsurj : Function.Surjective θ)
    [HenselianRing R (RingHom.ker θ.toRingHom)] (hunit : ∀ y, θ y ≠ 0 → IsUnit y) (ιΩ : L →ₐ[K] Ω) :
    ∃ ι₀ : L →ₐ[K] R, ∀ x, θ (ι₀ x) = ιΩ x := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  set P := minpoly K pb.gen
  have hP : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hroot : aeval pb.gen P = 0 := minpoly.aeval K pb.gen
  have hd : aeval (ιΩ pb.gen) (derivative P) ≠ 0 := by
    rw [Polynomial.aeval_algHom_apply]
    exact (map_ne_zero ιΩ).mpr (hsep.aeval_derivative_ne_zero hroot)
  obtain ⟨a₀, ha₀⟩ := hsurj (ιΩ pb.gen)
  obtain ⟨a, haroot, hamem⟩ := HenselianRing.is_henselian (I := RingHom.ker θ.toRingHom) (P.map (algebraMap K R))
    (hP.map _) a₀ (by
      change θ _ = 0
      rw [eval_map_algebraMap, ← Polynomial.aeval_algHom_apply, ha₀,
        Polynomial.aeval_algHom_apply, hroot, map_zero])
    (by
      apply IsUnit.map
      apply hunit
      rwa [derivative_map, eval_map_algebraMap, ← Polynomial.aeval_algHom_apply, ha₀])
  have haP : aeval a P = 0 := by
    rw [← eval_map_algebraMap]; exact haroot
  have hθa : θ a = ιΩ pb.gen := by
    change θ (a - a₀) = 0 at hamem
    rw [map_sub, sub_eq_zero] at hamem
    rw [← ha₀]; exact hamem
  refine ⟨pb.lift a haP, ?_⟩
  have : θ.comp (pb.lift a haP) = ιΩ := pb.algHom_ext (by
    rw [AlgHom.comp_apply, PowerBasis.lift_gen, hθa])
  intro x
  rw [← this, AlgHom.comp_apply]

/-- **Naturality of the Hensel lift.** -/
theorem hensel_lift_natural [IsDomain R] (θ : R →ₐ[K] Ω) (ιΩ : L →ₐ[K] Ω) (ι₀ : L →ₐ[K] R)
    (hι₀ : ∀ x, θ (ι₀ x) = ιΩ x) (s : R →ₐ[K] R) (τ : L →ₐ[K] L)
    (hs : ∀ x, θ (s (ι₀ x)) = ιΩ (τ x)) (x : L) : s (ι₀ x) = ι₀ (τ x) := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  set P := minpoly K pb.gen
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hroot : aeval pb.gen P = 0 := minpoly.aeval K pb.gen
  have hτroot : aeval (τ pb.gen) P = 0 := by
    rw [Polynomial.aeval_algHom_apply, hroot, map_zero]
  have key : (s.comp ι₀) = ι₀.comp τ := by
    apply pb.algHom_ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    refine root_eq_of_theta θ P ?_ ?_ ?_ ?_
    · rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, hroot, map_zero,
        map_zero]
    · rw [Polynomial.aeval_algHom_apply, hτroot, map_zero]
    · rw [hs, hι₀]
    · rw [hι₀, Polynomial.aeval_algHom_apply]
      exact (map_ne_zero ιΩ).mpr (hsep.aeval_derivative_ne_zero hτroot)
  exact congrArg (fun φ => φ x) key

end Hensel

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Speiser.lean

/-!
# G9: Galois descent for semilinear actions (Speiser's lemma)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Let `L/K` be a finite Galois extension with group `Γ`, and `M` an `L`-vector space with a
semilinear action of `Γ` (`τ(c • m) = τ(c) • τ(m)`). Then `L ⊗_K M^Γ → M` is an isomorphism
(Speiser's lemma; STANDARD: Serre, *Local fields*, X §1, Lemma; Bourbaki *Algèbre* V §10).
We need only the dimension count `dim_K M = [L:K] · dim_K M^Γ`, `speiser_finrank`.

The proof: for a `K`-basis `b` of `L` indexed by `Γ`, the matrix `A = (τ(b_j))_{τ,j}` is
invertible by Dedekind's independence of characters; this gives both surjectivity (each `m` is an
`L`-combination of the traces `Σ_σ σ(b_j m)`) and injectivity.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct Classical

section Speiser

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A `K`-basis of `L` indexed by `Gal(L/K)`. -/
noncomputable def galBasis : Basis (L ≃ₐ[K] L) K L :=
  (Module.finBasisOfFinrankEq K L
    (by rw [← IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card])).reindex
    (Fintype.equivFin (L ≃ₐ[K] L)).symm

/-- The matrix `(τ(b_j))_{τ, j}`. -/
noncomputable def galMatrix : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L :=
  Matrix.of fun τ j => τ (galBasis (K := K) (L := L) j)

/-- Dedekind: `(τ(b_j))` is invertible. -/
theorem isUnit_galMatrix : IsUnit (galMatrix (K := K) (L := L)) := by
  rw [← Matrix.vecMul_injective_iff_isUnit]
  have hli : LinearIndependent L
      (fun τ : L ≃ₐ[K] L => ((τ : L →ₐ[K] L)).toLinearMap) :=
    (linearIndependent_toLinearMap K L L).comp (fun τ : L ≃ₐ[K] L => (τ : L →ₐ[K] L))
      (fun _ _ h => AlgEquiv.coe_toAlgHom_injective h)
  have key : ∀ c : (L ≃ₐ[K] L) → L, Matrix.vecMul c galMatrix = 0 → c = 0 := by
    intro c hc
    have hsum : (∑ τ, c τ • ((τ : L →ₐ[K] L)).toLinearMap) = 0 := by
      refine (galBasis (K := K) (L := L)).ext fun j => ?_
      have := congrFun hc j
      simp only [Matrix.vecMul, dotProduct, galMatrix, Matrix.of_apply, Pi.zero_apply] at this
      simpa [LinearMap.sum_apply] using this
    funext τ
    exact (Fintype.linearIndependent_iff.mp hli) c hsum τ
  intro c d h
  have h' : Matrix.vecMul (c - d) galMatrix = 0 := by
    have h0 : Matrix.vecMul c galMatrix = Matrix.vecMul d (galMatrix (K := K) (L := L)) := h
    rw [Matrix.sub_vecMul, h0, sub_self]
  exact sub_eq_zero.mp (key _ h')

variable {M : Type*} [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]

variable (T : (L ≃ₐ[K] L) → M →+ M)
  (hsmul : ∀ τ (c : L) (m : M), T τ (c • m) = τ c • T τ m)
  (hone : ∀ m, T 1 m = m)
  (hmul : ∀ τ σ m, T (τ * σ) m = T τ (T σ m))

include hsmul in
theorem semilin_smulK (τ : L ≃ₐ[K] L) (k : K) (m : M) : T τ (k • m) = k • T τ m := by
  rw [← algebraMap_smul L k m, hsmul, AlgEquiv.commutes, algebraMap_smul]

/-- The fixed points `M^Γ`, a `K`-subspace. -/
def fixedK : Submodule K M where
  carrier := {m | ∀ τ, T τ m = m}
  zero_mem' := by intro τ; simp
  add_mem' := by
    intro x y hx hy τ
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [map_add, hx, hy]
  smul_mem' := by
    intro k x hx τ
    simp only [Set.mem_ofPred_eq] at hx
    rw [semilin_smulK T hsmul, hx]

/-- `L ⊗_K M^Γ → M`. -/
noncomputable def speiserMap : L ⊗[K] (fixedK T hsmul) →ₗ[K] M :=
  TensorProduct.lift (LinearMap.mk₂ K (fun (x : L) (n : fixedK T hsmul) => x • (n : M))
    (fun x y n => add_smul x y _)
    (fun k x n => by simp only [smul_assoc])
    (fun x n n' => by simp only [Submodule.coe_add, smul_add])
    (fun k x n => by simp only [SetLike.val_smul, smul_comm x k (n : M)]))

theorem speiserMap_tmul (x : L) (n : fixedK T hsmul) :
    speiserMap T hsmul (x ⊗ₜ n) = x • (n : M) := by
  simp [speiserMap]

include hone hmul in
theorem speiserMap_surjective : Function.Surjective (speiserMap T hsmul) := by
  intro m
  set b := galBasis (K := K) (L := L)
  set A := galMatrix (K := K) (L := L)
  have hA := isUnit_galMatrix (K := K) (L := L)
  -- the traces `y j = Σ_σ σ(b j • m)`
  let y : (L ≃ₐ[K] L) → M := fun j => ∑ σ, T σ (b j • m)
  have hy : ∀ j, y j ∈ fixedK T hsmul := by
    intro j τ
    simp only [y, map_sum, ← hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  have hy' : ∀ j, y j = ∑ σ, A σ j • T σ m := by
    intro j
    simp only [y, hsmul, A, galMatrix, Matrix.of_apply, b]
  refine ⟨∑ j, (A⁻¹ j (1 : L ≃ₐ[K] L)) ⊗ₜ ⟨y j, hy j⟩, ?_⟩
  rw [map_sum]
  simp only [speiserMap_tmul, hy', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hmul1 : ∀ σ, (∑ j, A⁻¹ j (1 : L ≃ₐ[K] L) * A σ j) =
      (1 : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) σ (1 : L ≃ₐ[K] L) := by
    intro σ
    rw [← Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hmul1, Matrix.one_apply]
  simp [hone]

include hone hmul in
theorem speiserMap_injective : Function.Injective (speiserMap T hsmul) := by
  set b := galBasis (K := K) (L := L)
  set A := galMatrix (K := K) (L := L)
  have hA := isUnit_galMatrix (K := K) (L := L)
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  set n := TensorProduct.equivFinsuppOfBasisLeft b x
  have hxn : x = ∑ j, b j ⊗ₜ n j := by
    have h1 := LinearMap.congr_fun (TensorProduct.equivFinsuppOfBasisLeft_symm b) n
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, n] at h1
    rw [h1, Finsupp.lsum_apply, Finsupp.sum_fintype _ _ (by simp)]
    rfl
  rw [hxn, map_sum] at hx
  simp only [speiserMap_tmul] at hx
  -- apply every `τ`
  have hτ : ∀ τ, ∑ j, A τ j • (n j : M) = 0 := by
    intro τ
    have := congrArg (T τ) hx
    rw [map_sum, map_zero] at this
    simpa only [hsmul, (n _).2 τ, A, galMatrix, Matrix.of_apply, b] using this
  have hn : ∀ k, (n k : M) = 0 := by
    intro k
    have hinv : A⁻¹ * A = 1 :=
      Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
    have : (n k : M) = ∑ τ, A⁻¹ k τ • ∑ j, A τ j • (n j : M) := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have h2 : ∀ j, (∑ τ, A⁻¹ k τ * A τ j) = (1 : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) k j := by
        intro j; rw [← hinv, Matrix.mul_apply]
      simp_rw [h2, Matrix.one_apply]
      simp
    rw [this]
    simp [hτ]
  rw [hxn]
  simp [show ∀ k, n k = 0 from fun k => Subtype.ext (hn k)]

include hone hmul in
/-- **Speiser's lemma, dimension form.** `dim_K M = [L:K] · dim_K M^Γ`. -/
theorem speiser_finrank :
    finrank K M = finrank K L * finrank K (fixedK T hsmul) := by
  have e := LinearEquiv.ofBijective (speiserMap T hsmul)
    ⟨speiserMap_injective T hsmul hone hmul, speiserMap_surjective T hsmul hone hmul⟩
  rw [← e.finrank_eq, Module.finrank_tensorProduct]

end Speiser

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Descent.lean

/-!
# G9: finite Galois descent for spaces of equivariant maps

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

A group `G` acts `K`-linearly on a `K`-algebra `B` (`act`) and on a `K`-space `V` (`ρ`). For
`S ⊆ G`, `Dsp act ρ S` is the space of `K`-linear maps `φ : V → B` with `φ(ρ(g) v) = act(g)(φ v)`
for `g ∈ S`. (pkg-I4's `ddrSpace`, `ddrSpaceOver`, `htSpace`, `htSpaceOver` are all of this
form: `B = B_dR` or `B = ℂ_p` with the twisted action `χ(g)^i · g`.)

**Descent (`descent_finrank`).** Let `L/K` be finite Galois, `γ : G → Gal(L/K)` a surjective
homomorphism, and `ι : L → B` a `K`-algebra map with `act(g)(ι(x) b) = ι(γ(g) x) · act(g)(b)`.
Then `dim_K Dsp(ker γ) = [L:K] · dim_K Dsp(G)`. Proof: `Dsp(ker γ)` is an `L`-space through `ι`,
with a semilinear action of `Gal(L/K) = G/ker γ`, whose invariants are `Dsp(G)`; apply Speiser's
lemma (`speiser_finrank`). This is the finite-descent paragraph of N5's Lemma
`lem:de-rham-descent` (`D_K = D_{F}^{Gal(F/K)}`, `F ⊗_K D_K ≅ D_F`).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct

section Dsp

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  {V : Type*} [AddCommGroup V] [Module K V]

/-- `S`-equivariant `K`-linear maps `V → B`. -/
def Dsp (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V) (S : Set G) :
    Submodule K (V →ₗ[K] B) where
  carrier := {φ | ∀ g ∈ S, ∀ v, φ (ρ g v) = act g (φ v)}
  zero_mem' := by intro g _ v; simp
  add_mem' := by
    intro φ ψ hφ hψ g hg v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ g hg v, hψ g hg v, map_add]
  smul_mem' := by
    intro c φ hφ g hg v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ g hg v, map_smul]

theorem mem_Dsp {act : G → B →ₗ[K] B} {ρ : G → V →ₗ[K] V} {S : Set G} {φ : V →ₗ[K] B} :
    φ ∈ Dsp act ρ S ↔ ∀ g ∈ S, ∀ v, φ (ρ g v) = act g (φ v) := Iff.rfl

end Dsp

section Descent

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [CommRing B] [Algebra K B]
  {V : Type*} [AddCommGroup V] [Module K V]
  (act : G →* (B →ₗ[K] B)) (ρ : G →* (V →ₗ[K] V))
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (ι : L →ₐ[K] B) (γ : G →* (L ≃ₐ[K] L))

theorem act_inv_act (g : G) (b : B) : act g (act g⁻¹ b) = b := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_inv_rho (g : G) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- `g · φ = act(g) ∘ φ ∘ ρ(g)⁻¹`, on `Hom_K(V, B)`. -/
def twist (g : G) : (V →ₗ[K] B) →ₗ[K] (V →ₗ[K] B) where
  toFun φ := act g ∘ₗ φ ∘ₗ ρ g⁻¹
  map_add' φ ψ := by ext v; simp
  map_smul' c φ := by ext v; simp

theorem twist_apply (g : G) (φ : V →ₗ[K] B) (v : V) :
    twist act ρ g φ v = act g (φ (ρ g⁻¹ v)) := rfl

theorem twist_mul (g h : G) (φ : V →ₗ[K] B) :
    twist act ρ (g * h) φ = twist act ρ g (twist act ρ h φ) := by
  ext v
  simp only [twist_apply, map_mul, mul_inv_rev, Module.End.mul_apply]

theorem twist_mem (g : G) {φ : V →ₗ[K] B} (hφ : φ ∈ Dsp act ρ (γ.ker : Set G)) :
    twist act ρ g φ ∈ Dsp act ρ (γ.ker : Set G) := by
  intro h hh v
  have hh' : γ h = 1 := hh
  have hk : g⁻¹ * h * g ∈ γ.ker := by
    show γ (g⁻¹ * h * g) = 1
    simp [hh']
  have e1 : ρ g⁻¹ (ρ h v) = ρ (g⁻¹ * h * g) (ρ g⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    group
  rw [twist_apply, twist_apply, e1, hφ _ hk]
  rw [← Module.End.mul_apply (act g), ← map_mul, ← Module.End.mul_apply (act h), ← map_mul]
  congr 2
  group

theorem twist_eq_self_of_mem_ker {h : G} (hh : h ∈ γ.ker) {φ : V →ₗ[K] B}
    (hφ : φ ∈ Dsp act ρ (γ.ker : Set G)) : twist act ρ h φ = φ := by
  ext v
  have hh' : h⁻¹ ∈ γ.ker := γ.ker.inv_mem hh
  rw [twist_apply, hφ _ hh', act_inv_act]

theorem twist_eq_self_of_mem_univ (g : G) {φ : V →ₗ[K] B}
    (hφ : φ ∈ Dsp act ρ Set.univ) : twist act ρ g φ = φ := by
  ext v
  rw [twist_apply, hφ _ (Set.mem_univ _), act_inv_act]

theorem mem_univ_of_twist (φ : V →ₗ[K] B) (h : ∀ g, twist act ρ g φ = φ) :
    φ ∈ Dsp act ρ Set.univ := by
  intro g _ v
  have := LinearMap.congr_fun (h g) (ρ g v)
  rw [twist_apply, rho_inv_rho] at this
  exact this.symm

variable (hγ : Function.Surjective γ)
  (hsemi : ∀ g x b, act g (ι x * b) = ι (γ g x) * act g b)

include hsemi in
theorem twist_smul (g : G) (x : L) (φ : V →ₗ[K] B) :
    twist act ρ g (ι x • φ) = ι (γ g x) • twist act ρ g φ := by
  ext v
  simp only [twist_apply, LinearMap.smul_apply, smul_eq_mul, hsemi]

include hγ hsemi in
/-- **Finite Galois descent for `Dsp`.** `dim_K Dsp(ker γ) = [L:K] · dim_K Dsp(G)`. -/
theorem descent_finrank :
    finrank K (Dsp act ρ (γ.ker : Set G)) = finrank K L * finrank K (Dsp act ρ Set.univ) := by
  classical
  -- `B` as an `L`-algebra through `ι`
  let _ : Algebra L B := ι.toRingHom.toAlgebra
  have : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq (fun k => (ι.commutes k).symm)
  have hLsmul : ∀ (x : L) (b : B), x • b = ι x * b := fun _ _ => rfl
  -- the `L`-subspace `Dsp(ker γ)`
  let DL : Submodule L (V →ₗ[K] B) :=
    { carrier := {φ | φ ∈ Dsp act ρ (γ.ker : Set G)}
      zero_mem' := (Dsp act ρ _).zero_mem
      add_mem' := fun ha hb => (Dsp act ρ _).add_mem ha hb
      smul_mem' := by
        intro x φ hφ h hh v
        simp only [Set.mem_ofPred_eq] at hφ
        have hx : γ h x = x := by
          rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh
          rw [hh]; rfl
        simp only [LinearMap.smul_apply, hLsmul, hφ h hh v, hsemi, hx] }
  have hDL : DL.restrictScalars K = Dsp act ρ (γ.ker : Set G) := Submodule.ext fun _ => Iff.rfl
  -- the action of `g ∈ G` on `DL`
  let Tg : G → DL →+ DL := fun g =>
    { toFun := fun φ => ⟨twist act ρ g φ, twist_mem act ρ γ g φ.2⟩
      map_zero' := by ext1; simp
      map_add' := by intro φ ψ; ext1; simp }
  have Tg_val : ∀ g (φ : DL), ((Tg g φ : DL) : V →ₗ[K] B) = twist act ρ g φ := fun _ _ => rfl
  let s : (L ≃ₐ[K] L) → G := Function.surjInv hγ
  have hs : ∀ τ, γ (s τ) = τ := Function.surjInv_eq hγ
  have hker : ∀ g, (s (γ g))⁻¹ * g ∈ γ.ker := by
    intro g; rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
  let T : (L ≃ₐ[K] L) → DL →+ DL := fun τ => Tg (s τ)
  have hT_eq : ∀ g (φ : DL), Tg g φ = T (γ g) φ := by
    intro g φ
    apply Subtype.ext
    have hg : g = s (γ g) * ((s (γ g))⁻¹ * g) := by group
    change twist act ρ g φ = twist act ρ (s (γ g)) φ
    conv_lhs => rw [hg]
    rw [twist_mul, twist_eq_self_of_mem_ker act ρ γ (hker g) φ.2]
  have hsmul : ∀ τ (c : L) (φ : DL), T τ (c • φ) = τ c • T τ φ := by
    intro τ c φ
    apply Subtype.ext
    change twist act ρ (s τ) (ι c • (φ : V →ₗ[K] B)) = ι (τ c) • twist act ρ (s τ) φ
    rw [twist_smul act ρ ι γ hsemi, hs]
  have hone : ∀ φ, T 1 φ = φ := by
    intro φ
    apply Subtype.ext
    change twist act ρ (s 1) φ = φ
    have : s 1 ∈ γ.ker := by rw [MonoidHom.mem_ker, hs]
    exact twist_eq_self_of_mem_ker act ρ γ this φ.2
  have hmul : ∀ τ σ φ, T (τ * σ) φ = T τ (T σ φ) := by
    intro τ σ φ
    have h1 : T (τ * σ) φ = Tg (s τ * s σ) φ := by
      rw [hT_eq (s τ * s σ), map_mul, hs, hs]
    rw [h1]
    apply Subtype.ext
    change twist act ρ (s τ * s σ) φ = twist act ρ (s τ) (twist act ρ (s σ) φ)
    rw [twist_mul]
  have hsp := speiser_finrank (K := K) (L := L) (M := DL) T hsmul hone hmul
  -- the fixed points are `Dsp(G)`
  have hfix : Submodule.map (DL.subtype.restrictScalars K) (fixedK (K := K) (L := L) (M := DL) T hsmul)
      = Dsp act ρ Set.univ := by
    ext φ
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      apply mem_univ_of_twist
      intro g
      have := congrArg Subtype.val ((hT_eq g ψ).trans (hψ (γ g)))
      exact this
    · intro hφ
      refine ⟨⟨φ, fun g hg v => hφ g (Set.mem_univ _) v⟩, ?_, rfl⟩
      intro τ
      apply Subtype.ext
      exact twist_eq_self_of_mem_univ act ρ (s τ) hφ
  have e1 : finrank K (fixedK (K := K) (L := L) (M := DL) T hsmul) = finrank K (Dsp act ρ Set.univ) := by
    rw [← hfix]
    exact (Submodule.equivMapOfInjective (DL.subtype.restrictScalars K)
      (Submodule.injective_subtype DL) _).finrank_eq
  have e2 : finrank K DL = finrank K (Dsp act ρ (γ.ker : Set G)) := by
    rw [← hDL]
    rfl
  rw [← e2, hsp, e1]

end Descent

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/OverF.lean

/-!
# G9: counting equivariant maps through `V ⊗ C ≅ U ⊕ U`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Pure linear algebra on the spaces `Dsp act ρ S` of `Descent.lean`:
* `finrank_Dsp_congr`: an equivariant isomorphism `V ≅ V'` preserves `dim Dsp`;
* `finrank_Dsp_pi`: `dim Dsp(V^ι) = |ι| · dim Dsp(V)`;
* `finrank_Dsp_prod`: `dim Dsp(U × U) = 2 · dim Dsp(U)`;
* `overF_count`: if `C ⊗_K V ≅ U × U` equivariantly (`C/K` finite) and `Dsp(V) ≠ 0`, then
  `[C:K] · dim Dsp(V) = 2 · dim Dsp(U)`.
This is the step "extension of the coefficient field is, on underlying `ℚ_ℓ`-representations, a
finite direct sum; the displayed decomposition therefore makes `r|G_F` de Rham" of N5's Lemma
`lem:de-rham-descent`, done by counting (no closure property of de Rham representations is used).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct

noncomputable section

section OverF

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  (act : G → B →ₗ[K] B)

theorem finrank_Dsp_congr {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank K (Dsp act ρ S) = finrank K (Dsp act ρ' S) := by
  let L : (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B) := LinearEquiv.arrowCongr e (LinearEquiv.refl K B)
  have hL : ∀ φ v', L φ v' = φ (e.symm v') := fun _ _ => rfl
  have hL' : ∀ φ' v, L.symm φ' v = φ' (e v) := fun _ _ => rfl
  have hmap : (Dsp act ρ S).map (L : (V →ₗ[K] B) →ₗ[K] (V' →ₗ[K] B)) = Dsp act ρ' S := by
    ext φ'
    constructor
    · rintro ⟨φ, hφ, rfl⟩ g hg v'
      have h1 : e.symm (ρ' g v') = ρ g (e.symm v') := by
        apply e.injective
        rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      change L φ (ρ' g v') = act g (L φ v')
      rw [hL, hL, h1, hφ g hg]
    · intro hφ'
      refine ⟨L.symm φ', ?_, by simp⟩
      intro g hg v
      rw [hL', hL', he, hφ' g hg]
  rw [← hmap, LinearEquiv.finrank_map_eq]

/-- The diagonal action on `ι → V`. -/
def piRep {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (ι : Type*) :
    G → (ι → V) →ₗ[K] (ι → V) :=
  fun g => LinearMap.pi fun i => ρ g ∘ₗ LinearMap.proj i

theorem piRep_apply {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (ι : Type*)
    (g : G) (v : ι → V) (i : ι) : piRep ρ ι g v i = ρ g (v i) := rfl

theorem piRep_single {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (ι : Type*) [DecidableEq ι] (g : G) (i : ι) (v : V) :
    piRep ρ ι g (Pi.single i v) = Pi.single i (ρ g v) := by
  funext j
  rw [piRep_apply]
  by_cases hij : j = i
  · subst hij; simp
  · simp [Pi.single_eq_of_ne hij]

/-- `Dsp(V^ι) ≅ Dsp(V)^ι`. -/
def DspPiEquiv {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Dsp act (piRep ρ ι) S ≃ₗ[K] (ι → Dsp act ρ S) :=
  { toFun := fun φ i => ⟨(φ : (ι → V) →ₗ[K] B) ∘ₗ LinearMap.single K (fun _ => V) i, by
      intro g hg v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
      rw [← piRep_single, φ.2 g hg]⟩
    map_add' := fun φ ψ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    map_smul' := fun c φ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    invFun := fun ψ => ⟨∑ i, ((ψ i : Dsp act ρ S) : V →ₗ[K] B) ∘ₗ LinearMap.proj i, by
      intro g hg v
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [piRep_apply, (ψ i).2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearMap.single_apply]
      rw [← map_sum, Finset.univ_sum_single v]
    right_inv := fun ψ => by
      funext i
      apply Subtype.ext
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
        LinearMap.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Pi.single_eq_of_ne hji, map_zero]
      · intro h; exact absurd (Finset.mem_univ i) h }

theorem finrank_Dsp_pi {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] [FiniteDimensional K (Dsp act ρ S)] :
    finrank K (Dsp act (piRep ρ ι) S) = Fintype.card ι * finrank K (Dsp act ρ S) := by
  rw [(DspPiEquiv act ρ S ι).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- `Dsp(U × U) ≅ Dsp(U) × Dsp(U)`. -/
def DspProdEquiv {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G) :
    Dsp act (fun g => (ρ g).prodMap (ρ g)) S ≃ₗ[K] (Dsp act ρ S × Dsp act ρ S) :=
  { toFun := fun φ => (⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inl K V V, by
        intro g hg v
        have := φ.2 g hg (v, 0)
        simpa using this⟩,
      ⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inr K V V, by
        intro g hg v
        have := φ.2 g hg (0, v)
        simpa using this⟩)
    map_add' := fun φ ψ => by ext <;> simp
    map_smul' := fun c φ => by ext <;> simp
    invFun := fun ψ => ⟨(ψ.1 : V →ₗ[K] B).coprod (ψ.2 : V →ₗ[K] B), by
      intro g hg v
      simp only [LinearMap.coprod_apply, LinearMap.prodMap_apply, map_add]
      rw [ψ.1.2 g hg, ψ.2.2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      ext v <;> simp
    right_inv := fun ψ => by
      ext v <;> simp }

theorem finrank_Dsp_prod {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) [FiniteDimensional K (Dsp act (fun g => (ρ g).prodMap (ρ g)) S)] :
    finrank K (Dsp act (fun g => (ρ g).prodMap (ρ g)) S) = 2 * finrank K (Dsp act ρ S) := by
  let E := DspProdEquiv act ρ S
  have hfin : FiniteDimensional K (Dsp act ρ S × Dsp act ρ S) :=
    LinearEquiv.finiteDimensional E
  have : FiniteDimensional K (Dsp act ρ S) :=
    Module.Finite.of_surjective (LinearMap.fst K (Dsp act ρ S) (Dsp act ρ S))
      LinearMap.fst_surjective
  rw [E.finrank_eq, Module.finrank_prod, two_mul]

/-- `C ⊗_K V ≅ V^ι` for a basis of `C` indexed by `ι`. -/
def tensorPiEquiv {C : Type*} [Field C] [Algebra K C] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bC : Basis ι K C) : C ⊗[K] V ≃ₗ[K] (ι → V) :=
  (TensorProduct.equivFinsuppOfBasisLeft bC).trans (Finsupp.linearEquivFunOnFinite K V ι)

theorem tensorPiEquiv_baseChange {C : Type*} [Field C] [Algebra K C] {V : Type*}
    [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι] (bC : Basis ι K C)
    (f : V →ₗ[K] V)
    (x : C ⊗[K] V) :
    tensorPiEquiv bC (f.baseChange C x) = fun i => f (tensorPiEquiv bC x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    funext i
    simp [tensorPiEquiv, LinearMap.baseChange_tmul]
  | add x y hx hy =>
    funext i
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]

/-- **Counting through `C ⊗_K V ≅ U × U`.** -/
theorem overF_count {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x))
    (hpos : 0 < finrank K (Dsp act ρV S)) :
    finrank K C * finrank K (Dsp act ρV S) = 2 * finrank K (Dsp act ρU S) := by
  classical
  have : FiniteDimensional K (Dsp act ρV S) := Module.finite_of_finrank_pos hpos
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  have h1 : finrank K (Dsp act ρCV S) = finrank K C * finrank K (Dsp act ρV S) := by
    rw [finrank_Dsp_congr act ρCV (piRep ρV (Fin (finrank K C))) S (tensorPiEquiv bC)
      (fun g x => tensorPiEquiv_baseChange bC (ρV g) x), finrank_Dsp_pi, Fintype.card_fin]
  have h2 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    finrank_Dsp_congr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  have hfin : FiniteDimensional K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) := by
    apply Module.finite_of_finrank_pos
    rw [← h2, h1]
    exact Nat.mul_pos Module.finrank_pos hpos
  rw [← h1, h2, finrank_Dsp_prod]

/-- **Reverse count**: if `Dsp(U) ≠ 0` (finite-dimensional), then `Dsp(V) ≠ 0`. -/
theorem overF_pos_rev {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x))
    (hU : 0 < finrank K (Dsp act ρU S)) :
    0 < finrank K (Dsp act ρV S) := by
  classical
  have : FiniteDimensional K (Dsp act ρU S) := Module.finite_of_finrank_pos hU
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  have hUU : FiniteDimensional K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    LinearEquiv.finiteDimensional (DspProdEquiv act ρU S).symm
  have h2 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    finrank_Dsp_congr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  have h1 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (piRep ρV (Fin (finrank K C))) S) :=
    finrank_Dsp_congr act ρCV (piRep ρV (Fin (finrank K C))) S (tensorPiEquiv bC)
      (fun g x => tensorPiEquiv_baseChange bC (ρV g) x)
  have hpos : 0 < finrank K (Dsp act (piRep ρV (Fin (finrank K C))) S) := by
    rw [← h1, h2, finrank_Dsp_prod]
    omega
  have : FiniteDimensional K (Dsp act (piRep ρV (Fin (finrank K C))) S) :=
    Module.finite_of_finrank_pos hpos
  have hfinpi : FiniteDimensional K (Fin (finrank K C) → Dsp act ρV S) :=
    LinearEquiv.finiteDimensional (DspPiEquiv act ρV S _)
  have hc : 0 < finrank K C := Module.finrank_pos
  have : FiniteDimensional K (Dsp act ρV S) :=
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : Fin (finrank K C) =>
      Dsp act ρV S) ⟨0, hc⟩) (fun x => ⟨fun _ => x, rfl⟩)
  rw [finrank_Dsp_pi, Fintype.card_fin] at hpos
  exact Nat.pos_of_mul_pos_left hpos

end OverF

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Galois.lean

/-!
# G9: the image of `G_F` in `G_{ℚ_p}`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

For a finite Galois extension `F/ℚ_p`, pkg-I4's map `gfToGqp p F : G_F → G_{ℚ_p}` (Mathlib's
`Field.absoluteGaloisGroup.map`, restriction along a chosen embedding `ℚ̄_p → F̄`) has image the
kernel of the restriction `G_{ℚ_p} → Gal(F'/ℚ_p)`, where `F' ⊆ ℚ̄_p` is a copy of `F`
(`range_gfToGqp`). `F'` is finite Galois over `ℚ_p` with `[F':ℚ_p] = [F:ℚ_p]`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 Module

noncomputable section

section Galois

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- An element of `G_F` as an automorphism of `F̄`. -/
abbrev galF (σ : Field.absoluteGaloisGroup F) : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ

/-- `gfToGqp` is restriction along an embedding `g : ℚ̄_p → F̄` over `ℚ_p`. -/
theorem exists_emb_gfToGqp : ∃ g : PadicAlgCl p →+* AlgebraicClosure F,
    (∀ c : ℚ_[p], g (algebraMap ℚ_[p] (PadicAlgCl p) c) =
      algebraMap F (AlgebraicClosure F) (algebraMap ℚ_[p] F c)) ∧
    ∀ (σ : Field.absoluteGaloisGroup F) (x : PadicAlgCl p), g (gfToGqp p F σ x) = galF F σ (g x) := by
  let _i1 : Algebra ℚ_[p] F := (algebraMap ℚ_[p] F).toAlgebra
  let g0 : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure F := IsAlgClosed.lift
  let _i2 : Algebra (AlgebraicClosure ℚ_[p]) (AlgebraicClosure F) := g0.toAlgebra
  refine ⟨g0.toRingHom, fun c => g0.commutes c, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars ℚ_[p] σ)
    (AlgebraicClosure ℚ_[p]) x

/-- The embedding `ℚ̄_p → F̄` behind `gfToGqp`. -/
def embF : PadicAlgCl p →+* AlgebraicClosure F := (exists_emb_gfToGqp p F).choose

theorem embF_algebraMap (c : ℚ_[p]) : embF p F (algebraMap ℚ_[p] (PadicAlgCl p) c) =
    algebraMap F (AlgebraicClosure F) (algebraMap ℚ_[p] F c) :=
  (exists_emb_gfToGqp p F).choose_spec.1 c

theorem embF_gfToGqp (σ : Field.absoluteGaloisGroup F) (x : PadicAlgCl p) :
    embF p F (gfToGqp p F σ x) = galF F σ (embF p F x) :=
  (exists_emb_gfToGqp p F).choose_spec.2 σ x

theorem embF_bijective : Function.Bijective (embF p F) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro y
  have : Algebra.IsIntegral ℚ_[p] (AlgebraicClosure F) :=
    Algebra.IsIntegral.trans (R := ℚ_[p]) F
  have hy : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  apply RingHom.IsIntegralElem.of_comp (f := algebraMap ℚ_[p] (PadicAlgCl p))
  have hc : (embF p F).comp (algebraMap ℚ_[p] (PadicAlgCl p)) =
      algebraMap ℚ_[p] (AlgebraicClosure F) := by
    ext c
    rw [RingHom.comp_apply, embF_algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [hc]
  exact hy

/-- `ℚ̄_p ≃ F̄`. -/
def embFEquiv : PadicAlgCl p ≃+* AlgebraicClosure F :=
  RingEquiv.ofBijective (embF p F) (embF_bijective p F)

theorem embFEquiv_apply (x : PadicAlgCl p) : embFEquiv p F x = embF p F x := rfl

/-- `F → ℚ̄_p`, `y ↦ g⁻¹(y)`. -/
def phiF : F →ₐ[ℚ_[p]] PadicAlgCl p where
  toRingHom := (embFEquiv p F).symm.toRingHom.comp (algebraMap F (AlgebraicClosure F))
  commutes' c := by
    apply (embFEquiv p F).injective
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_ofClass, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      Function.comp_apply, RingEquiv.apply_symm_apply, embFEquiv_apply, embF_algebraMap]

theorem embF_phiF (y : F) : embF p F (phiF p F y) = algebraMap F (AlgebraicClosure F) y := by
  rw [← embFEquiv_apply]
  exact (embFEquiv p F).apply_symm_apply _

/-- `F' ⊆ ℚ̄_p`, the copy of `F` with `G_F = G_{F'}` under `gfToGqp`. -/
def fieldF : IntermediateField ℚ_[p] (PadicAlgCl p) := (phiF p F).fieldRange

/-- `F ≃ F'`. -/
def equivFieldF : F ≃ₐ[ℚ_[p]] fieldF p F := (phiF p F).equivFieldRange

instance : FiniteDimensional ℚ_[p] (fieldF p F) :=
  LinearEquiv.finiteDimensional (equivFieldF p F).toLinearEquiv

theorem finrank_fieldF : finrank ℚ_[p] (fieldF p F) = finrank ℚ_[p] F :=
  (equivFieldF p F).toLinearEquiv.finrank_eq.symm

variable [IsGalois ℚ_[p] F]

instance : IsGalois ℚ_[p] (fieldF p F) := IsGalois.of_algEquiv (equivFieldF p F)

/-- The restriction `G_{ℚ_p} → Gal(F'/ℚ_p)`. -/
def gammaF : GQp p →* (fieldF p F ≃ₐ[ℚ_[p]] fieldF p F) :=
  AlgEquiv.restrictNormalHom (fieldF p F)

theorem gammaF_surjective : Function.Surjective (gammaF p F) :=
  AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)

theorem gammaF_apply_coe (τ : GQp p) (x : fieldF p F) :
    ((gammaF p F τ x : fieldF p F) : PadicAlgCl p) = τ (x : PadicAlgCl p) :=
  AlgEquiv.restrictNormal_commutes τ (fieldF p F) x

theorem mem_ker_gammaF (τ : GQp p) :
    τ ∈ (gammaF p F).ker ↔ ∀ y : F, τ (phiF p F y) = phiF p F y := by
  rw [gammaF, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y
    exact h _ ⟨y, rfl⟩
  · rintro h _ ⟨y, rfl⟩
    exact h y

/-- **The image of `G_F` is `ker(G_{ℚ_p} → Gal(F'/ℚ_p))`.** -/
theorem range_gfToGqp : (gfToGqp p F).range = (gammaF p F).ker := by
  ext τ
  rw [MonoidHom.mem_range, mem_ker_gammaF]
  constructor
  · rintro ⟨σ, rfl⟩ y
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp, embF_phiF]
    exact (galF F σ).commutes y
  · intro h
    -- `σ = g ∘ τ ∘ g⁻¹`, an `F`-automorphism of `F̄`
    let e := embFEquiv p F
    let σr : AlgebraicClosure F ≃+* AlgebraicClosure F :=
      (e.symm.trans τ.toRingEquiv).trans e
    have hσr : ∀ x, σr x = e (τ (e.symm x)) := fun _ => rfl
    let σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F :=
      { σr with
        commutes' := by
          intro y
          change σr (algebraMap F (AlgebraicClosure F) y) = _
          rw [hσr, ← embF_phiF p F y, ← embFEquiv_apply, RingEquiv.symm_apply_apply, h y,
            embFEquiv_apply, embF_phiF] }
    let σ' : Field.absoluteGaloisGroup F := σ
    refine ⟨σ', ?_⟩
    ext x
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp p F σ' x]
    change σr (embF p F x) = embF p F (τ x)
    rw [hσr, ← embFEquiv_apply, RingEquiv.symm_apply_apply]
    rfl

end Galois

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/BdRAct.lean

/-!
# G9: pkg-I4's actions of `G_{ℚ_p}` on `ℂ_p` and on `B_dR` are group actions

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

pkg-I4 (`I4Layer.lean`, verbatim) defines `cpAct p σ` on `ℂ_p` and `bdrAct p σ` on `B_dR` for each
`σ ∈ G_{ℚ_p}` separately. Here: `cpAct (σ τ) = cpAct σ ∘ cpAct τ`, `cpAct 1 = id`, the same for
`bdrAct` (functoriality of Mathlib's `B_dR` construction: mod `p`, tilt, Witt vectors,
localization, adic completion, localization), and the cyclotomic twists `cycPow` are
multiplicative. Packaged as monoid homomorphisms `htAct p i : G_{ℚ_p} →* End_{ℚ_p}(ℂ_p)`
(`c ↦ χ(σ)^i σ(c)`) and `drAct p : G_{ℚ_p} →* End_{ℚ_p}(B_dR)`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 Ideal

noncomputable section

namespace PkgI4.DR
open _root_.HDec.PkgI4.DR  -- (g0-assemble2) the root namespace holds Leaves.lean's `PkgI4.DR`

variable (p : ℕ) [Fact p.Prime] {O : Type*} [CommRing O]

theorem modPMap_comp (f g : O →+* O) :
    modPMap p (g.comp f) = (modPMap p g).comp (modPMap p f) := by
  ext x
  rfl

theorem modPMap_id : modPMap p (RingHom.id O) = RingHom.id _ := by
  ext x
  rfl

variable [Fact ¬IsUnit (p : O)]

theorem preTiltMap_comp (f g : O →+* O) :
    preTiltMap p (g.comp f) = (preTiltMap p g).comp (preTiltMap p f) := by
  ext x
  refine Perfection.ext fun n => ?_
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap, modPMap_comp]
  rfl

theorem preTiltMap_id : preTiltMap p (RingHom.id O) = RingHom.id _ := by
  ext x
  refine Perfection.ext fun n => ?_
  rw [coeff_preTiltMap, modPMap_id]
  rfl

theorem locMap_comp (f g : O →+* O) :
    locMap p (g.comp f) = (locMap p g).comp (locMap p f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt O p)))
  ext w
  simp only [RingHom.comp_apply, locMap, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq]
  congr 1
  ext n
  simp only [WittVector.map_coeff, preTiltMap_comp, RingHom.comp_apply]

theorem locMap_id : locMap p (RingHom.id O) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt O p)))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
    IsLocalization.Away.lift, IsLocalization.lift_eq]
  congr 1
  ext n
  simp only [WittVector.map_coeff, preTiltMap_id, RingHom.id_apply]

section AdicComp

variable {A : Type*} [CommRing A] (J : Ideal A)

theorem adicMap_comp' (g0 g : A →+* A) (h0 : J ≤ J.comap g0) (h : J ≤ J.comap g)
    (g' : A →+* A) (h' : J ≤ J.comap g') (hg' : g' = g.comp g0) :
    adicMap J J g' h' = (adicMap J J g h).comp (adicMap J J g0 h0) := by
  subst hg'
  refine RingHom.ext fun x => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [RingHom.comp_apply, adicMap_evalₐ, adicMap_evalₐ, adicMapAux, adicMapAux,
    RingHom.comp_apply, RingHom.comp_apply]
  erw [adicMap_evalₐ]
  rw [adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

theorem adicMap_id' (g' : A →+* A) (h' : J ≤ J.comap g') (hg' : g' = RingHom.id A) :
    adicMap J J g' h' = RingHom.id _ := by
  subst hg'
  refine RingHom.ext fun x => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ, adicMapAux, RingHom.comp_apply, RingHom.id_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

end AdicComp

variable [IsAdicComplete (span {(p : O)}) O]

theorem bdrPlusMap_comp (f g : O →+* O) :
    bdrPlusMap p (g.comp f) = (bdrPlusMap p g).comp (bdrPlusMap p f) :=
  adicMap_comp' _ (locMap p f) (locMap p g) (ker_le_comap_locMap p f) (ker_le_comap_locMap p g)
    _ _ (locMap_comp p f g)

theorem bdrPlusMap_id : bdrPlusMap p (RingHom.id O) = RingHom.id _ :=
  adicMap_id' _ _ _ (locMap_id p)

theorem bdrMap_comp (f g f' g' : O →+* O) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (hgf' : ∀ x, g' (f' x) = x) (hfg' : ∀ y, f' (g' y) = y)
    (h : O →+* O) (k : O →+* O) (hkh : ∀ x, k (h x) = x) (hhk : ∀ y, h (k y) = y)
    (hh : h = f'.comp f) :
    bdrMap p h k hkh hhk = (bdrMap p f' g' hgf' hfg').comp (bdrMap p f g hgf hfg) := by
  subst hh
  unfold bdrMap
  rw [IsLocalization.map_comp_map]
  apply IsLocalization.ringHom_ext (genMonoid p O)
  ext x
  simp only [RingHom.comp_apply, IsLocalization.map_eq, bdrPlusMap_comp]
  erw [IsLocalization.map_eq]
  rfl

theorem bdrMap_id (h : O →+* O) (k : O →+* O) (hkh : ∀ x, k (h x) = x) (hhk : ∀ y, h (k y) = y)
    (hh : h = RingHom.id O) :
    bdrMap p h k hkh hhk = RingHom.id _ := by
  subst hh
  unfold bdrMap
  apply IsLocalization.ringHom_ext (genMonoid p O)
  ext x
  simp only [RingHom.comp_apply, IsLocalization.map_eq, bdrPlusMap_id, RingHom.id_apply]

end PkgI4.DR

namespace PkgI4
open _root_.HDec.PkgI4  -- (g0-assemble2) the root namespace holds Leaves.lean's `PkgI4`

variable (p : ℕ) [Fact p.Prime]

theorem cpAct_mul_apply (σ τ : GQp p) (x : ℂ_[p]) :
    cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe]; rfl

theorem cpAct_one_apply (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe]; rfl

theorem oAct_mul (σ τ : GQp p) : oAct p (σ * τ) = (oAct p σ).comp (oAct p τ) := by
  ext x
  exact congrArg Subtype.val (Subtype.ext (cpAct_mul_apply p σ τ x) :
    oAct p (σ * τ) x = oAct p σ (oAct p τ x))

theorem oAct_one : oAct p 1 = RingHom.id _ := by
  ext x
  exact congrArg Subtype.val (Subtype.ext (cpAct_one_apply p x) : oAct p 1 x = x)

theorem bdrAct_mul (σ τ : GQp p) : bdrAct p (σ * τ) = (bdrAct p σ).comp (bdrAct p τ) :=
  DR.bdrMap_comp p _ _ _ _ _ _ _ _ _ _ _ _ (oAct_mul p σ τ)

theorem bdrAct_one : bdrAct p 1 = RingHom.id _ :=
  DR.bdrMap_id p _ _ _ _ (oAct_one p)

theorem cycPow_mul (σ τ : GQp p) (i : ℤ) : cycPow p (σ * τ) i = cycPow p σ i * cycPow p τ i := by
  have h : cyc p (σ * τ) = cyc p σ * cyc p τ := by
    simp only [cyc]
    rw [← map_mul]
    rfl
  simp only [cycPow, h, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_one (i : ℤ) : cycPow p 1 i = 1 := by
  have h : cyc p 1 = 1 := by
    simp only [cyc]
    rw [← map_one (cyclotomicCharacter (PadicAlgCl p) p)]
    rfl
  simp [cycPow, h]

/-- `σ ↦ (c ↦ χ(σ)^i σ(c))`, the action of `G_{ℚ_p}` on `ℂ_p(i)`, as a monoid homomorphism. -/
def htAct (i : ℤ) : GQp p →* (ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun σ :=
    { toFun := fun c => cycPow p σ i • cpAct p σ c
      map_add' := fun a b => by rw [map_add, smul_add]
      map_smul' := fun c a => by
        rw [Algebra.smul_def c a, map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]
        rfl }
  map_one' := by
    ext c
    simp [cycPow_one, cpAct_one_apply]
  map_mul' σ τ := by
    ext c
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, cycPow_mul,
      cpAct_mul_apply, mul_smul]
    rw [Algebra.smul_def (cycPow p τ i) (cpAct p τ c), map_mul, cpAct_algebraMap,
      ← Algebra.smul_def, smul_comm]

theorem htAct_apply (i : ℤ) (σ : GQp p) (c : ℂ_[p]) :
    htAct p i σ c = cycPow p σ i • cpAct p σ c := rfl

/-- `σ ↦ bdrAct σ`, the action of `G_{ℚ_p}` on `B_dR`, as a monoid homomorphism to
`ℚ_p`-linear endomorphisms. -/
def drAct : GQp p →* (BdR p →ₗ[ℚ_[p]] BdR p) where
  toFun σ :=
    { toFun := bdrAct p σ
      map_add' := map_add _
      map_smul' := bdrAct_smul p σ }
  map_one' := LinearMap.ext fun c => by
    change bdrAct p 1 c = c
    rw [bdrAct_one]
    rfl
  map_mul' σ τ := LinearMap.ext fun c => by
    change bdrAct p (σ * τ) c = bdrAct p σ (bdrAct p τ c)
    rw [bdrAct_mul]
    rfl

theorem drAct_apply (σ : GQp p) (c : BdR p) : drAct p σ c = bdrAct p σ c := rfl

end PkgI4

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/KerTheta.lean

/-!
# G9: `B_dR^+` is a complete DVR with residue map `θ⁺ : B_dR^+ → ℂ_p` (bdr-kertheta, restated)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

**Source.** `scratch/bdr-kertheta/KerTheta.lean` at fork main `883c4ddf` (task bdr-kertheta),
copied verbatim, wrapped in the namespace `ZInQ.Contrib.G9`, with one deletion: its section
`PkgI4.Cp` (lines 246-347 there) is byte-for-byte identical to the section `PkgI4.Cp` of
`I4Layer.lean` (checked with `diff`), so it is imported instead of repeated. Used here:
`isAdicComplete_BDeRhamPlus`, `isDomain_BDeRhamPlus`, `isLocalRing_BDeRhamPlus`,
`thetaPlusCp`, `thetaPlusCp_surjective`, `ker_thetaPlusCp`, `isFractionRing_BDeRham`.
-/

namespace ZInQ.Contrib.G9


/-!
# bdr-kertheta: `ker θ` is principal

Part A: a complete-Nakayama criterion for the kernel of a ring map out of a `p`-adically complete
ring. Part B: inverting `p`. Part C: Fontaine's `θ` for a general `p`-adically complete `O`,
reduced to one divisibility statement in the tilt.
-/

open Ideal

namespace BdrKer

section PartA

variable {A B : Type*} [CommRing A] [CommRing B] (p : ℕ)

theorem mem_span_pow_iff' (n : ℕ) (x : A) :
    x ∈ (span {(p : A)} ^ n • ⊤ : Submodule A A) ↔ ∃ c, x = (p : A) ^ n * c := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, mul_comm _ _⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, mul_comm _ _⟩

/-- **Part A.** If `A` is `p`-adically complete, `p` is a non-zero-divisor on `B`, and
`ker θ ⊆ ξ A + p A` for some `ξ ∈ ker θ`, then `ker θ = ξ A`. -/
theorem ker_eq_span_of_mod_p [IsAdicComplete (span {(p : A)}) A] (θ : A →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0) (ξ : A) (hξ : θ ξ = 0)
    (h : ∀ x, θ x = 0 → ∃ y z, x = ξ * y + p * z) :
    RingHom.ker θ = span {ξ} := by
  apply le_antisymm
  · intro x hx
    have h' : ∀ x : RingHom.ker θ, ∃ y : A, ∃ z : RingHom.ker θ, x.1 = ξ * y + p * z.1 := by
      intro x
      obtain ⟨y, z, hyz⟩ := h x.1 x.2
      refine ⟨y, ⟨z, ?_⟩, hyz⟩
      have : θ x.1 = 0 := x.2
      rw [hyz, map_add, map_mul, map_mul, hξ, zero_mul, zero_add, map_natCast] at this
      exact hB _ this
    choose Y Z hYZ using h'
    let s : ℕ → RingHom.ker θ := fun n => Nat.rec ⟨x, hx⟩ (fun _ w => Z w) n
    let S : ℕ → A := fun n => ∑ k ∈ Finset.range n, (p : A) ^ k * Y (s k)
    have hS : ∀ n, x = ξ * S n + (p : A) ^ n * (s n).1 := by
      intro n
      induction n with
      | zero => simp [S, s]
      | succ n ih =>
        have e : (s (n + 1)) = Z (s n) := rfl
        rw [ih, hYZ (s n), ← e]
        simp only [S, Finset.sum_range_succ]
        ring
    have hdiff : ∀ m d, ∃ c, S (m + d) - S m = (p : A) ^ m * c := by
      intro m d
      induction d with
      | zero => exact ⟨0, by simp⟩
      | succ d ih =>
        obtain ⟨c, hc⟩ := ih
        refine ⟨c + (p : A) ^ d * Y (s (m + d)), ?_⟩
        have : S (m + (d + 1)) = S (m + d) + (p : A) ^ (m + d) * Y (s (m + d)) := by
          simp only [S, ← add_assoc, Finset.sum_range_succ]
        rw [this, pow_add]
        linear_combination hc
    have hcauchy : ∀ {m n}, m ≤ n →
        S m ≡ S n [SMOD (span {(p : A)} ^ m • ⊤ : Submodule A A)] := by
      intro m n hmn
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [SModEq.sub_mem, mem_span_pow_iff']
      obtain ⟨c, hc⟩ := hdiff m d
      exact ⟨-c, by linear_combination -hc⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hcauchy
    have hx : x = ξ * L := by
      rw [← sub_eq_zero]
      apply IsHausdorff.haus' (I := span {(p : A)})
      intro n
      rw [SModEq.sub_mem, sub_zero, mem_span_pow_iff']
      have := hL n
      rw [SModEq.sub_mem, mem_span_pow_iff'] at this
      obtain ⟨c, hc⟩ := this
      refine ⟨ξ * c + (s n).1, ?_⟩
      linear_combination hS n + ξ * hc
    rw [hx]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ξ)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hξ

end PartA


section PartB

variable {A B : Type*} [CommRing A] [CommRing B] (p : ℕ)

theorem pow_mul_eq_zero {B : Type*} [CommRing B] {p : ℕ}
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0) (k : ℕ) (b : B) (h : (p : B) ^ k * b = 0) :
    b = 0 := by
  induction k generalizing b with
  | zero => simpa using h
  | succ k ih => exact ih b (hB _ (by rw [← h]; ring))

/-- **Part B.** Inverting `p`: if `ker θ = ξ A` and `p` is a non-zero-divisor on `B`, then the
kernel of `θ[1/p] : A[1/p] → B[1/p]` is generated by `ξ`. -/
theorem ker_awayLift_eq_span (θ : A →+* B) (hB : ∀ b : B, (p : B) * b = 0 → b = 0) (ξ : A)
    (hker : RingHom.ker θ = span {ξ})
    (hu : IsUnit (((algebraMap B (Localization.Away (p : B))).comp θ) (p : A))) :
    RingHom.ker (Localization.awayLift ((algebraMap B (Localization.Away (p : B))).comp θ)
      (p : A) hu) = span {algebraMap A (Localization.Away (p : A)) ξ} := by
  set L := Localization.awayLift ((algebraMap B (Localization.Away (p : B))).comp θ) (p : A) hu
  have hLa : ∀ a : A, L (algebraMap A _ a) = algebraMap B _ (θ a) := fun a =>
    IsLocalization.Away.lift_eq (p : A) hu a
  apply le_antisymm
  · intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : A)) z
    have hspec := IsLocalization.mk'_spec (Localization.Away (p : A)) a s
    have h1 : algebraMap B (Localization.Away (p : B)) (θ a) = 0 := by
      rw [← hLa, ← hspec, map_mul, RingHom.mem_ker.mp hz, zero_mul]
    obtain ⟨⟨m, k, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : B)) _ _).mp h1
    have h2 : θ a = 0 := pow_mul_eq_zero hB k _ hm
    have h3 : a ∈ span {ξ} := hker ▸ RingHom.mem_ker.mpr h2
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp h3
    refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' (Localization.Away (p : A)) c s, ?_⟩
    show _ = IsLocalization.mk' (Localization.Away (p : A)) (c * ξ) s
    rw [IsLocalization.mk'_eq_mul_mk'_one c, IsLocalization.mk'_eq_mul_mk'_one (c * ξ), map_mul]
    ring
  · have hξ : θ ξ = 0 := by
      rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ξ
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hLa, hξ,
      map_zero]

end PartB

section PartC

open WittVector

variable {O : Type*} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/-- **Part C.** For a `p`-adically complete, `p`-torsion-free ring `O` and `ϖ ∈ O♭` with
`ϖ♯ = p` such that every `c ∈ O♭` with `c♯ ∈ pO` is divisible by `ϖ`, the kernel of
Fontaine's `θ : W(O♭) → O` is generated by `p − [ϖ]`. -/
theorem ker_fontaineTheta_eq_span (hO : ∀ b : O, (p : O) * b = 0 → b = 0)
    (ϖ : PreTilt O p) (hϖ : ϖ.untilt = p)
    (hdiv : ∀ c : PreTilt O p, PreTilt.coeff 0 c = 0 → ∃ d, c = ϖ * d) :
    RingHom.ker (fontaineTheta O p) =
      span {(p : WittVector p (PreTilt O p)) - teichmuller p ϖ} := by
  apply ker_eq_span_of_mod_p p _ hO
  · simp [hϖ]
  · intro x hx
    have h0 : PreTilt.coeff 0 (x.coeff 0) = 0 := by
      rw [← mk_fontaineTheta, hx, map_zero]
    obtain ⟨d, hd⟩ := hdiv _ h0
    have hmem : x - teichmuller p (x.coeff 0) ∈ span {(p : WittVector p (PreTilt O p))} := by
      rw [← ker_constantCoeff, RingHom.mem_ker, map_sub]
      simp
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨-teichmuller p d, teichmuller p d + w, ?_⟩
    rw [hd, map_mul] at hw
    linear_combination -hw

/-- Part B specialised: the kernel of Mathlib's `fontaineThetaInvertP` is principal. -/
theorem ker_fontaineThetaInvertP_eq_span (hO : ∀ b : O, (p : O) * b = 0 → b = 0)
    (ξ : WittVector p (PreTilt O p)) (hker : RingHom.ker (fontaineTheta O p) = span {ξ}) :
    RingHom.ker (fontaineThetaInvertP O p) =
      span {algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ} :=
  ker_awayLift_eq_span p (fontaineTheta O p) hO ξ hker
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : O))

variable (O p) in
/-- The submonoid of `B_dR^+(O)` inverted in Mathlib's `BDeRham O p` (copied from its body). -/
noncomputable abbrev genMonoid : Submonoid (BDeRhamPlus O p) :=
  Submonoid.closure <| AdicCompletion.of ((RingHom.ker (fontaineThetaInvertP O p))) _ ''
      {a | (RingHom.ker (fontaineThetaInvertP O p)) = Ideal.span {a}}

variable (O p) in
noncomputable abbrev BdR := Localization (genMonoid O p)

example : BdR O p = BDeRham O p := rfl

/-- Consequence for `B_dR`: the generator set Mathlib inverts is non-empty, and the image of
`ξ` is a unit of `BDeRham`. -/
theorem isUnit_xi_BDeRham (hO : ∀ b : O, (p : O) * b = 0 → b = 0)
    (ξ : WittVector p (PreTilt O p)) (hker : RingHom.ker (fontaineTheta O p) = span {ξ}) :
    IsUnit (algebraMap (BDeRhamPlus O p) (BdR O p)
      (AdicCompletion.of (RingHom.ker (fontaineThetaInvertP O p)) _
        (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ))) :=
  IsLocalization.map_units (BdR O p) (⟨_, Submonoid.subset_closure
    ⟨_, (ker_fontaineThetaInvertP_eq_span hO ξ hker), rfl⟩⟩ : genMonoid O p)

variable (O p) in
/-- The canonical map `W(O♭)[1/p] → B_dR^+(O)`, typed into `BDeRhamPlus`. -/
noncomputable abbrev ofPlus (x : Localization.Away (p : WittVector p (PreTilt O p))) :
    BDeRhamPlus O p :=
  AdicCompletion.of (RingHom.ker (fontaineThetaInvertP O p)) _ x

theorem adicCompletion_of_mul {R : Type*} [CommRing R] (I : Ideal R) (x y : R) :
    AdicCompletion.of I R (x * y) = AdicCompletion.of I R x * AdicCompletion.of I R y :=
  show algebraMap R (AdicCompletion I R) (x * y) = algebraMap R _ x * algebraMap R _ y from
    map_mul _ x y

/-- **`B_dR = B_dR^+[1/ξ]`.** If `ker θ = (ξ)`, Mathlib's `BDeRham` (all generators of `ker θ[1/p]`
inverted) is the localization of `BDeRhamPlus` at the powers of the single element `ξ`:
`Localization.Away ξ` is a localization at Mathlib's submonoid. -/
theorem isLocalization_away_xi (hO : ∀ b : O, (p : O) * b = 0 → b = 0)
    (ξ : WittVector p (PreTilt O p)) (hker : RingHom.ker (fontaineTheta O p) = span {ξ}) :
    IsLocalization (genMonoid O p) (Localization.Away
      (ofPlus O p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ))) := by
  have hk := ker_fontaineThetaInvertP_eq_span hO ξ hker
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers
    (ofPlus O p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ)))
    (genMonoid O p) ?_ ?_
  · rw [Submonoid.powers_le]
    exact Submonoid.subset_closure ⟨_, hk, rfl⟩
  · intro n hn
    induction hn using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have : algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ ∈ span {a} := by
        rw [← (show _ = span {a} from ha), hk]; exact Ideal.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
      refine ⟨_, ⟨1, rfl⟩, ?_⟩
      show ofPlus O p a ∣
        ofPlus O p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ) ^ 1
      rw [pow_one, ← hc]
      exact ⟨ofPlus O p c, (adicCompletion_of_mul _ c a).trans (mul_comm _ _)⟩
    | one => exact ⟨1, ⟨0, pow_zero _⟩, one_dvd _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hx
      obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hy
      refine ⟨_, ⟨i + j, rfl⟩, ?_⟩
      show x * y ∣
        ofPlus O p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ) ^ (i + j)
      rw [pow_add]
      exact mul_dvd_mul hi hj

end PartC

end BdrKer


/-! ## Part D: `𝓞_ℂ_[p]`.
The section `PkgI4.Cp` below is copied unchanged from `scratch/pkg-I4/I4.lean` (instances:
`𝓞_ℂ_[p]` is `p`-adically complete). -/


namespace BdrKer.Cp

open Ideal PkgI4.Cp WittVector

variable (p : ℕ) [hp : Fact p.Prime]

local notation "O" => (𝓞_ℂ_[p] : Type)

/-- The `n`-th `p`-power root `x^{(n)} = (F^{-n} x)♯` of `x♯`. -/
noncomputable def root {R : Type*} [CommRing R] {q : ℕ} [Fact q.Prime] [Fact ¬IsUnit (q : R)]
    [IsAdicComplete (span {(q : R)}) R] (x : PreTilt R q) (n : ℕ) : R :=
  PreTilt.untilt (((frobeniusEquiv (PreTilt R q) q).symm^[n]) x)

section general
variable {R : Type*} [CommRing R] {q : ℕ} [Fact q.Prime] [Fact ¬IsUnit (q : R)]
    [IsAdicComplete (span {(q : R)}) R]

theorem root_pow (x : PreTilt R q) (n : ℕ) : root x n ^ q ^ n = x.untilt :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

theorem root_succ_pow (x : PreTilt R q) (n : ℕ) : root x (n + 1) ^ q = root x n := by
  rw [root, root, Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem mk_root (x : PreTilt R q) (n : ℕ) :
    Ideal.Quotient.mk (span {(q : R)}) (root x n) = PreTilt.coeff n x := by
  rw [root, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

end general

theorem p_ne_zero : (p : O) ≠ 0 := fun h => by
  have h1 := norm_p_pos p
  have : ((p : O) : ℂ_[p]) = 0 := by rw [h]; rfl
  push_cast at this
  rw [this, norm_zero] at h1
  exact lt_irrefl _ h1

theorem p_regular (b : O) (h : (p : O) * b = 0) : b = 0 :=
  (mul_eq_zero.mp h).resolve_left (p_ne_zero p)

theorem norm_le_one (x : O) : ‖(x : ℂ_[p])‖ ≤ 1 := (mem_O_iff p _).mp x.2

/-- **Divisibility in the tilt.** If `ϖ♯ = p`, every `c ∈ O♭` with `coeff 0 c = 0` is a multiple
of `ϖ`. -/
theorem dvd_of_coeff_zero (ϖ : PreTilt O p) (hϖ : ϖ.untilt = p) (c : PreTilt O p)
    (hc : PreTilt.coeff 0 c = 0) : ∃ d, c = ϖ * d := by
  -- `‖c♯‖ ≤ ‖p‖`
  have hc0 : ‖((c.untilt : O) : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ := by
    have : c.untilt ∈ span {(p : O)} ^ 1 := by
      rw [pow_one, ← Ideal.Quotient.eq_zero_iff_mem, PreTilt.mk_untilt_eq_coeff_zero, hc]
    simpa using (mem_span_pow_iff p _ 1).mp this
  have hϖn : ∀ n, ‖((root ϖ n : O) : ℂ_[p])‖ ^ p ^ n = ‖(p : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : O => ‖(z : ℂ_[p])‖) (root_pow ϖ n)
    rw [hϖ] at h
    simpa [norm_pow] using h
  have hcn : ∀ n, ‖((root c n : O) : ℂ_[p])‖ ^ p ^ n = ‖((c.untilt : O) : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : O => ‖(z : ℂ_[p])‖) (root_pow c n)
    simpa [norm_pow] using h
  have hne : ∀ n, ((root ϖ n : O) : ℂ_[p]) ≠ 0 := fun n h0 => by
    have := hϖn n
    rw [h0, norm_zero, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at this
    exact (ne_of_lt (norm_p_pos p)) this
  have hle : ∀ n, ‖((root c n : O) : ℂ_[p])‖ ≤ ‖((root ϖ n : O) : ℂ_[p])‖ := fun n => by
    have hpn : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn).mp ?_
    rw [hcn, hϖn]; exact hc0
  let e : ℕ → O := fun n => ⟨((root c n : O) : ℂ_[p]) / ((root ϖ n : O) : ℂ_[p]),
    (mem_O_iff p _).mpr (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have he : ∀ n, e (n + 1) ^ p = e n := fun n => by
    apply Subtype.ext
    simp only [e, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, root_succ_pow, root_succ_pow]
  have hce : ∀ n, root c n = root ϖ n * e n := fun n => by
    apply Subtype.ext
    simp only [e, MulMemClass.coe_mul]
    field_simp [hne n]
  let d : PreTilt O p := ⟨fun n => Ideal.Quotient.mk _ (e n), fun n => by
    rw [← map_pow, he]⟩
  refine ⟨d, ?_⟩
  apply Perfection.ext
  intro n
  change PreTilt.coeff n c = PreTilt.coeff n (ϖ * d)
  rw [map_mul]
  change PreTilt.coeff n c = PreTilt.coeff n ϖ * Ideal.Quotient.mk _ (e n)
  rw [← mk_root, ← mk_root, ← map_mul, hce]

/-- A compatible system of `p`-power roots of `p` in `ℂ_p`. -/
noncomputable def rootsOfP : ℕ → ℂ_[p]
  | 0 => p
  | n + 1 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (rootsOfP n) hp.out.pos)

theorem rootsOfP_succ_pow (n : ℕ) : rootsOfP p (n + 1) ^ p = rootsOfP p n :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (rootsOfP p n) hp.out.pos)

theorem rootsOfP_pow (n : ℕ) : rootsOfP p n ^ p ^ n = p := by
  induction n with
  | zero => simp [rootsOfP]
  | succ n ih => rw [pow_succ', pow_mul, rootsOfP_succ_pow, ih]

theorem norm_rootsOfP_le (n : ℕ) : ‖rootsOfP p n‖ ≤ 1 := by
  induction n with
  | zero => exact (mem_O_iff p _).mp (p : O).2
  | succ n ih =>
    rw [← rootsOfP_succ_pow] at ih
    rw [norm_pow] at ih
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp ih

/-- `p♭ = (p, p^{1/p}, p^{1/p²}, …) ∈ 𝓞_ℂ_p♭`. -/
noncomputable def pFlat : PreTilt O p :=
  ⟨fun n => Ideal.Quotient.mk _ ⟨rootsOfP p n, (mem_O_iff p _).mpr (norm_rootsOfP_le p n)⟩,
    fun n => by
      rw [← map_pow]
      congr 1
      exact Subtype.ext (by simpa using rootsOfP_succ_pow p n)⟩

theorem untilt_pFlat : (pFlat p).untilt = p := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : O)})]
  intro n
  rw [SModEq.sub_mem, mem_span_pow_iff']
  have h1 : root (pFlat p) n - ⟨rootsOfP p n, (mem_O_iff p _).mpr (norm_rootsOfP_le p n)⟩ ∈
      span {(p : O)} := by
    rw [← Ideal.Quotient.eq, mk_root]; rfl
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [root_pow] at h2
  have h3 : (⟨rootsOfP p n, (mem_O_iff p _).mpr (norm_rootsOfP_le p n)⟩ : O) ^ p ^ n = p :=
    Subtype.ext (by simpa using rootsOfP_pow p n)
  rw [h3] at h2
  obtain ⟨c, hc⟩ := h2
  exact ⟨p * c, by rw [hc]; ring⟩

/-- Fontaine's generator `ξ = p − [p♭] ∈ W(𝓞_ℂ_p♭)`. -/
noncomputable def xi : WittVector p (PreTilt O p) :=
  (p : WittVector p (PreTilt O p)) - teichmuller p (pFlat p)

/-- **Main theorem.** The kernel of Fontaine's `θ : W(𝓞_ℂ_p♭) → 𝓞_ℂ_p` is generated by
`ξ = p − [p♭]`. -/
theorem ker_fontaineTheta_Cp : RingHom.ker (fontaineTheta O p) = span {xi p} :=
  ker_fontaineTheta_eq_span (p_regular p) (pFlat p) (untilt_pFlat p)
    (dvd_of_coeff_zero p (pFlat p) (untilt_pFlat p))

/-- The image of `ξ` in `W(𝓞_ℂ_p♭)[1/p]`. -/
noncomputable def xi' : Localization.Away (p : WittVector p (PreTilt O p)) :=
  algebraMap _ _ (xi p)

/-- **Main theorem, Mathlib's form.** The kernel of `fontaineThetaInvertP` (θ with `p`
inverted, the ideal along which Mathlib completes to get `BDeRhamPlus`) is principal,
generated by the image of `ξ = p − [p♭]`. -/
theorem ker_fontaineThetaInvertP_Cp :
    RingHom.ker (fontaineThetaInvertP O p) = span {xi' p} :=
  ker_fontaineThetaInvertP_eq_span (p_regular p) _ (ker_fontaineTheta_Cp p)

/-- Hence `BDeRham 𝓞_ℂ_p` inverts `ξ` (Mathlib's generator set is non-empty). -/
theorem isUnit_xi_BDeRham_Cp :
    IsUnit (algebraMap (BDeRhamPlus O p) (BdR O p)
      (AdicCompletion.of (RingHom.ker (fontaineThetaInvertP O p)) _ (xi' p))) :=
  isUnit_xi_BDeRham (p_regular p) _ (ker_fontaineTheta_Cp p)

/-- **`B_dR(𝓞_ℂ_p) ≅ B_dR^+[1/ξ]`**, `ξ = p − [p♭]`: Mathlib's `BDeRham 𝓞_ℂ_[p] p` is
isomorphic, as a `BDeRhamPlus`-algebra, to the localization of `BDeRhamPlus` away from `ξ`. -/
noncomputable def bdREquivAway :
    BdR O p ≃ₐ[BDeRhamPlus O p] Localization.Away (ofPlus O p (xi' p)) :=
  haveI : IsLocalization (genMonoid O p) (Localization.Away (ofPlus O p (xi' p))) :=
    isLocalization_away_xi (p_regular p) (xi p) (ker_fontaineTheta_Cp p)
  IsLocalization.algEquiv (genMonoid O p) _ _

/-! ### Toward the DVR property: `(ξ')` is a maximal ideal of `W(𝓞_ℂ_p♭)[1/p]`. -/

theorem frobenius_surjective : Function.Surjective (frobenius (ModP O p) p) := by
  intro x
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x' : ℂ_[p]) hp.out.pos
  have hy1 : ‖y‖ ≤ 1 := by
    have h := norm_le_one p x'
    rw [← hy, norm_pow] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp h
  refine ⟨Ideal.Quotient.mk _ ⟨y, (mem_O_iff p _).mpr hy1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  congr 1
  exact Subtype.ext (by simpa using hy)

theorem fontaineTheta_surjective : Function.Surjective (fontaineTheta O p) :=
  surjective_fontaineTheta (frobenius_surjective p)

/-- `𝓞_ℂ_p[1/p]` is a field. -/
theorem isField_away_p : IsField (Localization.Away (p : O)) := by
  have h10 : (1 : Localization.Away (p : O)) ≠ 0 := by
    intro h
    rw [← map_one (algebraMap O (Localization.Away (p : O)))] at h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : O)) _ _).mp h
    exact pow_ne_zero k (p_ne_zero p) (by simpa using hk)
  refine ⟨⟨0, 1, h10.symm⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : O)) a
  have hx : (x : ℂ_[p]) ≠ 0 := by
    intro h0
    apply ha
    have : x = 0 := Subtype.ext h0
    simp [this]
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hx) (norm_p_lt_one p)
  have hc : ‖(p : ℂ_[p]) ^ m / (x : ℂ_[p])‖ ≤ 1 := by
    rw [norm_div, norm_pow]; exact div_le_one_of_le₀ hm.le (norm_nonneg _)
  let c : O := ⟨(p : ℂ_[p]) ^ m / (x : ℂ_[p]), (mem_O_iff p _).mpr hc⟩
  have hxc : x * c = (p : O) ^ m := by
    apply Subtype.ext
    simp only [c, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    field_simp
    rfl
  refine ⟨IsLocalization.mk' _ (c * s) (⟨(p : O) ^ m, m, rfl⟩ : Submonoid.powers (p : O)), ?_⟩
  rw [← IsLocalization.mk'_mul, ← mul_assoc, hxc, IsLocalization.mk'_eq_iff_eq_mul, one_mul]
  congr 1
  rw [Submonoid.coe_mul, mul_comm]

/-- `θ[1/p] : W(𝓞_ℂ_p♭)[1/p] → 𝓞_ℂ_p[1/p]` is surjective. -/
theorem fontaineThetaInvertP_surjective : Function.Surjective (fontaineThetaInvertP O p) := by
  intro t
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : O)) t
  obtain ⟨w, rfl⟩ := fontaineTheta_surjective p r
  refine ⟨IsLocalization.mk' _ w
    (⟨(p : WittVector p (PreTilt O p)) ^ n, n, rfl⟩ : Submonoid.powers _), ?_⟩
  have hL : ∀ a, fontaineThetaInvertP O p (algebraMap _ _ a) =
      algebraMap O (Localization.Away (p : O)) (fontaineTheta O p a) := fun a =>
    IsLocalization.Away.lift_eq _ (by simpa using IsLocalization.Away.algebraMap_isUnit (p : O)) a
  show _ = IsLocalization.mk' _ (fontaineTheta O p w) (⟨(p : O) ^ n, n, rfl⟩ : Submonoid.powers _)
  have hu : IsUnit (algebraMap O (Localization.Away (p : O)) ((p : O) ^ n)) :=
    IsLocalization.map_units _ (⟨(p : O) ^ n, n, rfl⟩ : Submonoid.powers (p : O))
  apply hu.mul_right_cancel
  have h1 := IsLocalization.mk'_spec (Localization.Away (p : WittVector p (PreTilt O p))) w
    (⟨(p : WittVector p (PreTilt O p)) ^ n, n, rfl⟩ : Submonoid.powers _)
  have h2 := IsLocalization.mk'_spec (Localization.Away (p : O)) (fontaineTheta O p w)
    (⟨(p : O) ^ n, n, rfl⟩ : Submonoid.powers (p : O))
  simp only at h1 h2
  rw [h2]
  have h3 := congrArg (fontaineThetaInvertP O p) h1
  rw [map_mul, hL, hL, map_pow, map_natCast] at h3
  exact h3

/-- **`ker θ[1/p] = (ξ')` is a maximal ideal** of `W(𝓞_ℂ_p♭)[1/p]` (residue field
`𝓞_ℂ_p[1/p]`). -/
theorem ker_fontaineThetaInvertP_isMaximal : (RingHom.ker (fontaineThetaInvertP O p)).IsMaximal :=
  letI := (isField_away_p p).toField
  RingHom.ker_isMaximal_of_surjective _ (fontaineThetaInvertP_surjective p)

/-! ### Step 1 of §3: `W(𝓞_ℂ_p♭)[1/p]` is a domain and `ξ'` is a non-zero-divisor. -/

instance isDomain_tilt : IsDomain (PreTilt O p) :=
  PreTilt.isDomain ℂ_[p] (PadicComplex.valued p).v O (PadicComplexInt.integers p) p

theorem witt_p_ne_zero : (p : WittVector p (PreTilt O p)) ≠ 0 := by
  intro h
  have : (1 : WittVector p (PreTilt O p)) = 0 :=
    WittVector.eq_zero_of_p_mul_eq_zero _ (by rw [one_mul, h])
  exact one_ne_zero this

instance isDomain_away : IsDomain (Localization.Away (p : WittVector p (PreTilt O p))) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (witt_p_ne_zero p))

theorem xi_ne_zero : xi p ≠ 0 := by
  intro h
  have h1 : WittVector.constantCoeff (xi p) = 0 := by rw [h, map_zero]
  rw [xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub, neg_eq_zero] at h1
  have h2 : pFlat p = 0 := by simpa using h1
  have h3 := untilt_pFlat p
  rw [← fontaineTheta_teichmuller, h2, WittVector.teichmuller_zero, map_zero] at h3
  exact p_ne_zero p h3.symm

theorem xi'_ne_zero : xi' p ≠ 0 := by
  intro h
  apply xi_ne_zero p
  exact (IsLocalization.injective (Localization.Away (p : WittVector p (PreTilt O p)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (witt_p_ne_zero p))) (by rw [map_zero]; exact h)

/-- `ξ'` is a non-zero-divisor of `W(𝓞_ℂ_p♭)[1/p]`. -/
theorem xi'_mem_nonZeroDivisors :
    xi' p ∈ nonZeroDivisors (Localization.Away (p : WittVector p (PreTilt O p))) :=
  mem_nonZeroDivisors_of_ne_zero (xi'_ne_zero p)

/-! ### Non-triviality: `ξ` is not nilpotent in `B_dR^+`, so `B_dR = B_dR^+[1/ξ] ≠ 0`. -/

set_option synthInstance.maxHeartbeats 200000 in
theorem ofPlus_xi'_pow_ne_zero (n : ℕ) : ofPlus O p (xi' p) ^ n ≠ 0 := by
  intro h
  set I := RingHom.ker (fontaineThetaInvertP O p)
  have h1 : AdicCompletion.evalₐ I (n + 1) (AdicCompletion.of I _ (xi' p ^ n)) = 0 := by
    have e : AdicCompletion.of I _ (xi' p ^ n) = ofPlus O p (xi' p) ^ n :=
      show algebraMap _ (AdicCompletion I _) (xi' p ^ n) = _ from map_pow _ _ _
    rw [e]; exact (congrArg _ h).trans (map_zero _)
  have hI : I = span {xi' p} := ker_fontaineThetaInvertP_Cp p
  rw [AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem, hI,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, hc⟩ := h1
  have hx := xi'_ne_zero p
  have h2 : c * xi' p = 1 := by
    have : xi' p ^ n * (c * xi' p - 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hx
    · exact sub_eq_zero.mp h
  have h3 : RingHom.ker (fontaineThetaInvertP O p) = ⊤ := by
    rw [ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_eq_top]
    exact isUnit_iff_exists_inv.mpr ⟨c, by rw [mul_comm]; exact h2⟩
  exact (ker_fontaineThetaInvertP_isMaximal p).ne_top h3

instance nontrivial_away_xi : Nontrivial (Localization.Away (ofPlus O p (xi' p))) := by
  refine ⟨0, 1, fun h => ?_⟩
  have h' : algebraMap (BDeRhamPlus O p) (Localization.Away (ofPlus O p (xi' p))) 1 = 0 := by
    rw [map_one]; exact h.symm
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (ofPlus O p (xi' p))) _ _).mp h'
  exact ofPlus_xi'_pow_ne_zero p k (by simpa using hk)

/-- **`BDeRham 𝓞_ℂ_[p] p` is not the zero ring.** -/
theorem nontrivial_BDeRham : Nontrivial (BdR O p) :=
  (bdREquivAway p).symm.injective.nontrivial

/-! ### `B_dR^+(𝓞_ℂ_p)` is a discrete valuation ring with uniformizer `ξ`. -/

theorem ker_fg : (RingHom.ker (fontaineThetaInvertP O p)).FG :=
  ⟨{xi' p}, by rw [Finset.coe_singleton, ker_fontaineThetaInvertP_Cp]⟩

theorem map_ker_eq :
    (RingHom.ker (fontaineThetaInvertP O p)).map
      (algebraMap _ (AdicCompletion (RingHom.ker (fontaineThetaInvertP O p))
        (Localization.Away (p : WittVector p (PreTilt O p))))) =
      (span {ofPlus O p (xi' p)} : Ideal (BDeRhamPlus O p)) := by
  have h1 := congrArg (Ideal.map (algebraMap _ (AdicCompletion (RingHom.ker
    (fontaineThetaInvertP O p)) (Localization.Away (p : WittVector p (PreTilt O p))))))
    (ker_fontaineThetaInvertP_Cp p)
  rw [Ideal.map_span, Set.image_singleton] at h1
  exact h1

instance isAdicComplete_BDeRhamPlus :
    IsAdicComplete (span {ofPlus O p (xi' p)} : Ideal (BDeRhamPlus O p)) (BDeRhamPlus O p) := by
  have := AdicCompletion.isAdicComplete_self _ (ker_fg p)
  rw [map_ker_eq] at this
  exact this

instance isMaximal_span_xi : (span {ofPlus O p (xi' p)} : Ideal (BDeRhamPlus O p)).IsMaximal := by
  have := ker_fontaineThetaInvertP_isMaximal p
  have := AdicCompletion.isMaximal_map_of_le _ _ le_rfl (ker_fg p)
  rw [map_ker_eq] at this
  exact this

/-- **`B_dR^+(𝓞_ℂ_p)` is a local ring.** -/
instance isLocalRing_BDeRhamPlus : IsLocalRing (BDeRhamPlus O p) :=
  isLocalRing_of_isAdicComplete_maximal (span {ofPlus O p (xi' p)})

/-- Its maximal ideal is `(ξ)`. -/
theorem maximalIdeal_BDeRhamPlus :
    IsLocalRing.maximalIdeal (BDeRhamPlus O p) = span {ofPlus O p (xi' p)} :=
  (IsLocalRing.eq_maximalIdeal (isMaximal_span_xi p)).symm

/-- Every non-zero element of `B_dR^+` is `ξⁿ · unit`. -/
theorem eq_xi_pow_mul_unit (x : BDeRhamPlus O p) (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : BDeRhamPlus O p, IsUnit u ∧ x = ofPlus O p (xi' p) ^ n * u := by
  set ϖ := ofPlus O p (xi' p)
  have hex : ∃ n, x ∉ (span {ϖ ^ n} : Ideal (BDeRhamPlus O p)) := by
    by_contra hcon
    push Not at hcon
    apply hx
    apply IsHausdorff.haus' (I := (span {ϖ} : Ideal (BDeRhamPlus O p))) x
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hcon n
  classical
  let N := Nat.find hex
  have hN : x ∉ (span {ϖ ^ N} : Ideal (BDeRhamPlus O p)) := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0
    apply hN
    rw [h0, pow_zero, Ideal.span_singleton_one]
    trivial
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxM : x ∈ (span {ϖ ^ M} : Ideal (BDeRhamPlus O p)) := by
    have := Nat.find_min hex (show M < N by omega)
    push Not at this
    exact this
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hxM
  refine ⟨M, u, ?_, by rw [← hu, mul_comm]⟩
  by_contra hnu
  have : u ∈ IsLocalRing.maximalIdeal (BDeRhamPlus O p) := hnu
  rw [maximalIdeal_BDeRhamPlus] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
  apply hN
  rw [hM, Ideal.mem_span_singleton']
  exact ⟨c, by rw [← hu, ← hc, Nat.succ_eq_add_one, pow_succ']; simp only [ϖ, mul_assoc]⟩

instance isDomain_BDeRhamPlus : IsDomain (BDeRhamPlus O p) := by
  have : NoZeroDivisors (BDeRhamPlus O p) := ⟨fun {x y} hxy => by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, u, hu, rfl⟩ := eq_xi_pow_mul_unit p x hcon.1
    obtain ⟨b, v, hv, rfl⟩ := eq_xi_pow_mul_unit p y hcon.2
    have : ofPlus O p (xi' p) ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact ofPlus_xi'_pow_ne_zero p (a + b) ((hu.mul hv).mul_left_eq_zero.mp this)⟩
  exact NoZeroDivisors.to_isDomain _

/-- **`B_dR^+(𝓞_ℂ_p)` (Mathlib's `BDeRhamPlus`) is a discrete valuation ring.** -/
theorem isDiscreteValuationRing_BDeRhamPlus : IsDiscreteValuationRing (BDeRhamPlus O p) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨ofPlus O p (xi' p), ?_, ?_⟩
  · exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (by simpa using ofPlus_xi'_pow_ne_zero p 1) (maximalIdeal_BDeRhamPlus p)
  · intro x hx
    obtain ⟨n, u, hu, rfl⟩ := eq_xi_pow_mul_unit p x hx
    exact ⟨n, ⟨hu.unit, rfl⟩⟩

/-! ### `B_dR(𝓞_ℂ_p)` is the fraction field of the DVR `B_dR^+`, hence a field. -/

/-- `B_dR^+[1/ξ]` is the fraction field of `B_dR^+`. -/
instance isFractionRing_away_xi :
    IsFractionRing (BDeRhamPlus O p) (Localization.Away (ofPlus O p (xi' p))) := by
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (ofPlus O p (xi' p)))
    (nonZeroDivisors _)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by simpa using ofPlus_xi'_pow_ne_zero p 1)) ?_
  intro n hn
  obtain ⟨k, u, hu, rfl⟩ := eq_xi_pow_mul_unit p n (nonZeroDivisors.ne_zero hn)
  exact ⟨_, ⟨k, rfl⟩, hu.mul_right_dvd.mpr (dvd_refl _)⟩

/-- **`BDeRham 𝓞_ℂ_[p] p` is a field**: it is isomorphic to the fraction field `B_dR^+[1/ξ]` of the
discrete valuation ring `BDeRhamPlus 𝓞_ℂ_[p] p`. -/
theorem isField_BDeRham : IsField (BdR O p) := by
  have hF : IsField (Localization.Away (ofPlus O p (xi' p))) :=
    (IsFractionRing.toField (BDeRhamPlus O p)).toIsField
  exact MulEquiv.isField hF (bdREquivAway p).toMulEquiv

/-- `BDeRham 𝓞_ℂ_[p] p` is a fraction field of `BDeRhamPlus 𝓞_ℂ_[p] p` (Mathlib's own structure map). -/
theorem isFractionRing_BDeRham : IsFractionRing (BDeRhamPlus O p) (BdR O p) := by
  have : IsLocalization (genMonoid O p) (Localization.Away (ofPlus O p (xi' p))) :=
    isLocalization_away_xi (p_regular p) (xi p) (ker_fontaineTheta_Cp p)
  exact (IsLocalization.isLocalization_iff_of_algEquiv (nonZeroDivisors _)
    (bdREquivAway p)).mpr inferInstance

/-! ### The residue map `θ⁺ : B_dR^+ → 𝓞_ℂ_p[1/p] ≅ ℂ_p` (Mathlib's TODO 1), with kernel `(ξ)`. -/

/-- `θ⁺ : B_dR^+ → 𝓞_ℂ_p[1/p]`: reduction modulo `ker θ[1/p]` followed by `θ[1/p]`. -/
noncomputable def thetaPlus : BDeRhamPlus O p →+* Localization.Away (p : O) :=
  (RingHom.quotientKerEquivOfSurjective (fontaineThetaInvertP_surjective p)).toRingHom.comp
    (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP O p))).toRingHom

theorem thetaPlus_ofPlus (x : Localization.Away (p : WittVector p (PreTilt O p))) :
    thetaPlus p (ofPlus O p x) = fontaineThetaInvertP O p x := rfl

theorem thetaPlus_surjective : Function.Surjective (thetaPlus p) := fun y => by
  obtain ⟨x, rfl⟩ := fontaineThetaInvertP_surjective p y
  exact ⟨ofPlus O p x, rfl⟩

/-- **`ker θ⁺ = (ξ)`**, the maximal ideal of the DVR `B_dR^+`. -/
theorem ker_thetaPlus : RingHom.ker (thetaPlus p) = span {ofPlus O p (xi' p)} := by
  have h1 : RingHom.ker (thetaPlus p) =
      RingHom.ker (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP O p))).toRingHom := by
    ext x
    exact map_eq_zero_iff (RingHom.quotientKerEquivOfSurjective (fontaineThetaInvertP_surjective p))
      (RingEquiv.injective _)
  rw [h1, AdicCompletion.ker_evalOneₐ_eq_map _ (ker_fg p)]
  exact map_ker_eq p

/-- `𝓞_ℂ_p[1/p]` is the fraction field of `𝓞_ℂ_p`. -/
instance isFractionRing_away_p : IsFractionRing O (Localization.Away (p : O)) := by
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (p : O)) (nonZeroDivisors _)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (p_ne_zero p)) ?_
  intro x hx
  have hx0 : (x : ℂ_[p]) ≠ 0 := fun h0 => nonZeroDivisors.ne_zero hx (Subtype.ext h0)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hx0) (norm_p_lt_one p)
  have hc : ‖(p : ℂ_[p]) ^ m / (x : ℂ_[p])‖ ≤ 1 := by
    rw [norm_div, norm_pow]; exact div_le_one_of_le₀ hm.le (norm_nonneg _)
  refine ⟨(p : O) ^ m, ⟨m, rfl⟩, ⟨⟨(p : ℂ_[p]) ^ m / (x : ℂ_[p]), (mem_O_iff p _).mpr hc⟩, ?_⟩⟩
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  field_simp
  rfl

/-- **`𝓞_ℂ_p[1/p] ≅ ℂ_p`**, so `θ⁺` takes values in `ℂ_p`. -/
noncomputable def awayEquivCp : Localization.Away (p : O) ≃ₐ[O] ℂ_[p] :=
  IsLocalization.algEquiv (nonZeroDivisors O) _ _

/-- The residue map `B_dR^+ → ℂ_p`, surjective with kernel `(ξ)`. -/
noncomputable def thetaPlusCp : BDeRhamPlus O p →+* ℂ_[p] :=
  (awayEquivCp p).toRingEquiv.toRingHom.comp (thetaPlus p)

theorem thetaPlusCp_surjective : Function.Surjective (thetaPlusCp p) :=
  (awayEquivCp p).surjective.comp (thetaPlus_surjective p)

theorem ker_thetaPlusCp : RingHom.ker (thetaPlusCp p) = span {ofPlus O p (xi' p)} := by
  rw [← ker_thetaPlus p]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  exact map_eq_zero_iff (awayEquivCp p) (AlgEquiv.injective _)

end BdrKer.Cp

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/LocalCore.lean

/-!
# G9, the local core: descent of de Rham and Hodge–Tate data from `F` to `ℚ_p`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Setting of N5's Lemma `lem:de-rham-descent` after the choice of the local field (h-trust C3,
Galois choice): `F/ℚ_p` finite Galois, `V` a `ℚ_p`-linear representation of `G_F`,
`E ⊆ ℚ̄_p` a finite coefficient field, `ρE : G_{ℚ_p} → GL₂(E)`, and an `E`-linear
`E ⊗_{ℚ_p} V ≅ E² × E²` intertwining `V|G_F` with `ρE|G_F ⊕ ρE|G_F`.

* `core_ht`: if `V` has Hodge–Tate multiplicities (over `F`, pkg-I4's `htMultOver`) `2` at `0`,
  `2` at `−1` and `0` elsewhere, then `ρE` has Hodge–Tate weights `{0, −1}` (pkg-I4's
  `HasHTWeights`).
* `core_dR`: if `V` is de Rham over `F` (pkg-I4's `IsDeRhamOver`) and `ℚ̄_p` embeds
  `G_{ℚ_p}`-equivariantly into `B_dR` (Fontaine; here a hypothesis), then `ρE` is de Rham
  (pkg-I4's `IsDeRham`).

Proof: count dimensions of spaces of equivariant maps through `E ⊗ V ≅ U ⊕ U`
(`overF_count_gen`), then descend from `G_F` to `G_{ℚ_p}` (`descent_finrank`, Speiser's lemma),
using `F' ⊆ ℚ̄_p ⊆ ℂ_p` (resp. `⊆ B_dR`); divisibility of `dim_{ℚ_p}` by `[F:ℚ_p]` comes from
the `F'`-structure. No closure property of de Rham representations (T23) is used.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

/-! ### Counting through `C ⊗ V ≅ U × U`, without finiteness hypotheses -/

section Count

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  (act : G → B →ₗ[K] B)

theorem map_arrowCongr_Dsp {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    (Dsp act ρ S).map ((LinearEquiv.arrowCongr e (LinearEquiv.refl K B) :
      (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B)) : (V →ₗ[K] B) →ₗ[K] (V' →ₗ[K] B)) = Dsp act ρ' S := by
  set L : (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B) := LinearEquiv.arrowCongr e (LinearEquiv.refl K B)
  have hL : ∀ φ v', L φ v' = φ (e.symm v') := fun _ _ => rfl
  have hL' : ∀ φ' v, L.symm φ' v = φ' (e v) := fun _ _ => rfl
  ext φ'
  constructor
  · rintro ⟨φ, hφ, rfl⟩ g hg v'
    have h1 : e.symm (ρ' g v') = ρ g (e.symm v') := by
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change L φ (ρ' g v') = act g (L φ v')
    rw [hL, hL, h1, hφ g hg]
  · intro hφ'
    refine ⟨L.symm φ', ?_, by simp⟩
    intro g hg v
    rw [hL', hL', he, hφ' g hg]

/-- An equivariant isomorphism `V ≅ V'` gives `Dsp(V) ≅ Dsp(V')`. -/
def dspCongr {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) : Dsp act ρ S ≃ₗ[K] Dsp act ρ' S :=
  ((LinearEquiv.arrowCongr e (LinearEquiv.refl K B)).submoduleMap (Dsp act ρ S)).trans
    (LinearEquiv.ofEq _ _ (map_arrowCongr_Dsp act ρ ρ' S e he))

/-- `Dsp(V^ι) ≅ Dsp(V)^ι`. -/
def dspPi {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Dsp act (piRep ρ ι) S ≃ₗ[K] (ι → Dsp act ρ S) :=
  have hsingle : ∀ g i (v : V), piRep ρ ι g (Pi.single i v) = Pi.single i (ρ g v) := by
    intro g i v
    funext j
    rw [piRep_apply]
    by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  { toFun := fun φ i => ⟨(φ : (ι → V) →ₗ[K] B) ∘ₗ LinearMap.single K (fun _ => V) i, by
        intro g hg v
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
        rw [← hsingle, φ.2 g hg]⟩
    map_add' := fun φ ψ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    map_smul' := fun c φ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    invFun := fun ψ => ⟨∑ i, ((ψ i : Dsp act ρ S) : V →ₗ[K] B) ∘ₗ LinearMap.proj i, by
        intro g hg v
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [piRep_apply, (ψ i).2 g hg]⟩
    left_inv := fun φ => by
        apply Subtype.ext
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          LinearMap.single_apply]
        rw [← map_sum, Finset.univ_sum_single v]
    right_inv := fun ψ => by
        funext i
        apply Subtype.ext
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
          LinearMap.single_apply]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji, map_zero]
        · intro h; exact absurd (Finset.mem_univ i) h }

/-- `Dsp(U × U) ≅ Dsp(U) × Dsp(U)`. -/
def dspProd {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G) :
    Dsp act (fun g => (ρ g).prodMap (ρ g)) S ≃ₗ[K] (Dsp act ρ S × Dsp act ρ S) :=
  { toFun := fun φ => (⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inl K V V, by
        intro g hg v
        have := φ.2 g hg (v, 0)
        simpa using this⟩,
      ⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inr K V V, by
        intro g hg v
        have := φ.2 g hg (0, v)
        simpa using this⟩)
    map_add' := fun φ ψ => by ext <;> simp
    map_smul' := fun c φ => by ext <;> simp
    invFun := fun ψ => ⟨(ψ.1 : V →ₗ[K] B).coprod (ψ.2 : V →ₗ[K] B), by
      intro g hg v
      simp only [LinearMap.coprod_apply, LinearMap.prodMap_apply, map_add]
      rw [ψ.1.2 g hg, ψ.2.2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      ext v <;> simp
    right_inv := fun ψ => by
      ext v <;> simp }

/-- `d · dim X = 2 · dim Y` from `X^d ≅ Y × Y` (`d > 0`), finite-dimensional or not. -/
theorem finrank_of_pi_equiv_prod {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y]
    [Module K Y] (d : ℕ) (hd : 0 < d) (Φ : (Fin d → X) ≃ₗ[K] Y × Y) :
    d * finrank K X = 2 * finrank K Y := by
  by_cases hX : FiniteDimensional K X
  · have h1 : FiniteDimensional K (Y × Y) := LinearEquiv.finiteDimensional Φ
    have h2 : FiniteDimensional K Y :=
      Module.Finite.of_surjective (LinearMap.fst K Y Y) LinearMap.fst_surjective
    have := Φ.finrank_eq
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Module.finrank_prod] at this
    omega
  · have hY : ¬ FiniteDimensional K Y := by
      intro hY
      have h1 : FiniteDimensional K (Y × Y) := inferInstance
      have h2 : FiniteDimensional K (Fin d → X) := LinearEquiv.finiteDimensional Φ.symm
      exact hX (Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : Fin d => X)
        ⟨0, hd⟩) (fun x => ⟨fun _ => x, rfl⟩))
    rw [Module.finrank_of_not_finite hX, Module.finrank_of_not_finite hY]
    simp

/-- **Counting through `C ⊗_K V ≅ U × U`** (no finiteness hypothesis). -/
theorem overF_count_gen {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x)) :
    finrank K C * finrank K (Dsp act ρV S) = 2 * finrank K (Dsp act ρU S) := by
  classical
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  let Φ1 : Dsp act ρCV S ≃ₗ[K] Dsp act (piRep ρV (Fin (finrank K C))) S :=
    dspCongr act ρCV _ S (tensorPiEquiv bC) (fun g x => tensorPiEquiv_baseChange bC (ρV g) x)
  let Φ2 : Dsp act ρCV S ≃ₗ[K] Dsp act (fun g => (ρU g).prodMap (ρU g)) S :=
    dspCongr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  let Φ : (Fin (finrank K C) → Dsp act ρV S) ≃ₗ[K] Dsp act ρU S × Dsp act ρU S :=
    ((dspPi act ρV S (Fin (finrank K C))).symm.trans Φ1.symm).trans (Φ2.trans (dspProd act ρU S))
  exact finrank_of_pi_equiv_prod (finrank K C) Module.finrank_pos Φ

/-- If `L` acts on `B` through `ι`, commuting with `act g` for `g ∈ S`, then `[L:K]` divides
`dim_K Dsp(S)`. -/
theorem finrank_dvd_Dsp_core {B : Type*} [CommRing B] [Algebra K B] (act : G → B →ₗ[K] B)
    {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G)
    {L : Type*} [Field L] [Algebra K L] (ι : L →ₐ[K] B)
    (h : ∀ g ∈ S, ∀ x b, act g (ι x * b) = ι x * act g b) :
    finrank K L ∣ finrank K (Dsp act ρ S) := by
  let _ : Algebra L B := ι.toRingHom.toAlgebra
  have : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq (fun k => (ι.commutes k).symm)
  have hLsmul : ∀ (x : L) (b : B), x • b = ι x * b := fun _ _ => rfl
  let DL : Submodule L (V →ₗ[K] B) :=
    { carrier := {φ | φ ∈ Dsp act ρ S}
      zero_mem' := (Dsp act ρ _).zero_mem
      add_mem' := fun ha hb => (Dsp act ρ _).add_mem ha hb
      smul_mem' := by
        intro x φ hφ g hg v
        simp only [Set.mem_ofPred_eq] at hφ
        simp only [LinearMap.smul_apply, hLsmul, hφ g hg v, h g hg] }
  have e2 : finrank K DL = finrank K (Dsp act ρ S) := rfl
  haveI : Module.Free L DL := Module.Free.of_divisionRing L DL
  rw [← e2, ← Module.finrank_mul_finrank K L DL]
  exact Dvd.intro _ rfl

end Count

/-! ### The local setting -/

section Local

variable (p : ℕ) [Fact p.Prime]

/-- `σ ↦ (v ↦ ρE(σ) v)` on `Eⁿ`, as `ℚ_p`-linear maps. -/
def matRep {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρE : GQp p →* GL (Fin n) E) :
    GQp p →* ((Fin n → E) →ₗ[ℚ_[p]] (Fin n → E)) where
  toFun σ := (Matrix.mulVecLin (ρE σ : Matrix (Fin n) (Fin n) E)).restrictScalars ℚ_[p]
  map_one' := LinearMap.ext fun v => by simp
  map_mul' σ τ := LinearMap.ext fun v => by simp [Matrix.mulVec_mulVec]

theorem matRep_apply {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρE : GQp p →* GL (Fin n) E) (σ : GQp p) (v : Fin n → E) :
    matRep p ρE σ v = Matrix.mulVec (ρE σ : Matrix (Fin n) (Fin n) E) v := rfl

variable {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E] {n : ℕ}

theorem ddrSpace_eq_DspMat (ρE : GQp p →* GL (Fin n) E) :
    ddrSpace p ρE = Dsp (drAct p) (matRep p ρE) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

theorem htSpace_eq_DspMat (ρE : GQp p →* GL (Fin n) E) (i : ℤ) :
    htSpace p ρE i = Dsp (htAct p i) (matRep p ρE) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

theorem ddrSpaceOver_eq_DspRep (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    ddrSpaceOver p ρ = Dsp (fun σ => drAct p (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

theorem htSpaceOver_eq_DspRep (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    htSpaceOver p ρ i = Dsp (fun σ => htAct p i (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

variable [IsGalois ℚ_[p] F]

theorem gammaF_gfToGqp (σ : Field.absoluteGaloisGroup F) : gammaF p F (gfToGqp p F σ) = 1 := by
  have : gfToGqp p F σ ∈ (gammaF p F).ker := by
    rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
  exact this

theorem Dsp_gf_eq {B : Type*} [AddCommGroup B] [Module ℚ_[p] B]
    {U : Type*} [AddCommGroup U] [Module ℚ_[p] U]
    (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ρU : GQp p →* (U →ₗ[ℚ_[p]] U)) :
    Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρU (gfToGqp p F σ)) Set.univ =
      Dsp act ρU ((gammaF p F).ker : Set (GQp p)) := by
  ext φ
  constructor
  · intro h τ hτ v
    rw [SetLike.mem_coe, ← range_gfToGqp] at hτ
    obtain ⟨σ, rfl⟩ := hτ
    exact h σ trivial v
  · intro h σ _ v
    exact h _ (by rw [SetLike.mem_coe, ← range_gfToGqp]; exact ⟨σ, rfl⟩) v

/-- **The count**, for an embedding of `F' ⊆ ℚ̄_p` into `B` semilinear for the action:
`[E:ℚ_p] · dim D_F(V) = 2 [F:ℚ_p] · dim D_{ℚ_p}(ρE)` and `[F:ℚ_p] ∣ dim D_F(V)`. -/
theorem core_count_F {B : Type*} [CommRing B] [Algebra ℚ_[p] B]
    (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ι' : fieldF p F →ₐ[ℚ_[p]] B)
    (hsemi : ∀ g x b, act g (ι' x * b) = ι' (gammaF p F g x) * act g b)
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x)) :
    finrank ℚ_[p] E * finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ)
      = 2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (matRep p ρE) Set.univ)) ∧
    finrank ℚ_[p] F ∣
      finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ) := by
  constructor
  · have h1 := overF_count_gen (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ)
      (fun σ => matRep p ρE (gfToGqp p F σ)) Set.univ eE he
    rw [h1, Dsp_gf_eq p F act (matRep p ρE),
      descent_finrank act (matRep p ρE) ι' (gammaF p F) (gammaF_surjective p F) hsemi,
      finrank_fieldF]
  · rw [← finrank_fieldF p F]
    refine finrank_dvd_Dsp_core _ _ _ ι' fun σ _ x b => ?_
    rw [hsemi, gammaF_gfToGqp]
    rfl

/-- **The count**, for an equivariant embedding of `ℚ̄_p` into `B`. -/
theorem core_count {B : Type*} [CommRing B] [Algebra ℚ_[p] B]
    (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ι : PadicAlgCl p →ₐ[ℚ_[p]] B)
    (hι : ∀ σ x b, act σ (ι x * b) = ι (σ x) * act σ b)
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x)) :
    finrank ℚ_[p] E * finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ)
      = 2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (matRep p ρE) Set.univ)) ∧
    finrank ℚ_[p] F ∣
      finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ) := by
  let ι' : fieldF p F →ₐ[ℚ_[p]] B := ι.comp (fieldF p F).val
  have hsemi : ∀ g x b, act g (ι' x * b) = ι' (gammaF p F g x) * act g b := by
    intro g x b
    simp only [ι', AlgHom.comp_apply, IntermediateField.coe_val, hι, gammaF_apply_coe]
  exact core_count_F p F act ι' hsemi ρ ρE eE he

/-- `ℚ̄_p → ℂ_p`. -/
def cpEmb : PadicAlgCl p →ₐ[ℚ_[p]] ℂ_[p] := IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]

theorem htAct_semi (i : ℤ) (σ : GQp p) (x : PadicAlgCl p) (b : ℂ_[p]) :
    htAct p i σ (cpEmb p x * b) = cpEmb p (σ x) * htAct p i σ b := by
  rw [htAct_apply, htAct_apply, map_mul, mul_smul_comm]
  congr 2
  change cpAct p σ ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p])
  exact cpAct_coe p σ x

theorem finrank_V_of_eE (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)) :
    finrank ℚ_[p] V = 4 := by
  have := eE.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at this
  omega

theorem count_two_zero : Multiset.count (0 : ℤ) {0, -1} = 1 := by decide
theorem count_two_neg_one : Multiset.count (-1 : ℤ) {0, -1} = 1 := by decide
theorem count_two_other (w : ℤ) (h0 : w ≠ 0) (h1 : w ≠ -1) : Multiset.count w {0, -1} = 0 := by
  simp [h0, h1]

/-- **G9 local core, Hodge–Tate part.** -/
theorem core_ht (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (h0 : htMultOver p ρ 0 = 2) (h1 : htMultOver p ρ (-1) = 2)
    (hw : ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p ρ w = 0) :
    HasHTWeights p ρE {0, -1} := by
  have hd : 0 < finrank ℚ_[p] E := Module.finrank_pos
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  -- the multiplicity at `w` is `M_w = dim H_{-w}(V) / [F:ℚ_p]`; then `htMult ρE w = M_w / 2`
  have key : ∀ w : ℤ, ∀ M : ℕ, htMultOver p ρ w = M →
      htMult p ρE w * 2 = M ∨ finrank ℚ_[p] E * M = 2 * finrank ℚ_[p] (htSpace p ρE (-w)) := by
    intro w M hM
    right
    obtain ⟨hc, hdvd⟩ := core_count p F (htAct p (-w)) (cpEmb p) (htAct_semi p (-w)) ρ ρE eE he
    rw [htMultOver, htSpaceOver_eq_DspRep] at hM
    rw [htSpace_eq_DspMat]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_cancel_left _ hf] at hM
    subst hM
    rw [hk] at hc
    have : finrank ℚ_[p] F * (finrank ℚ_[p] E * k) =
        finrank ℚ_[p] F * (2 * finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ)) := by
      rw [← mul_assoc, mul_comm (finrank ℚ_[p] F), mul_assoc, hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hf this
  intro w
  have hdiv : ∀ M : ℕ, finrank ℚ_[p] E * (2 * M) = 2 * finrank ℚ_[p] (htSpace p ρE (-w)) →
      htMult p ρE w = M := by
    intro M hM
    have : finrank ℚ_[p] (htSpace p ρE (-w)) = finrank ℚ_[p] E * M := by
      have := hM; rw [mul_left_comm] at this; omega
    rw [htMult, this, Nat.mul_div_cancel_left _ hd]
  by_cases hw0 : w = 0
  · subst hw0
    rw [count_two_zero]
    rcases key 0 2 h0 with h | h
    · omega
    · exact hdiv 1 (by simpa using h)
  by_cases hw1 : w = -1
  · subst hw1
    rw [count_two_neg_one]
    rcases key (-1) 2 h1 with h | h
    · omega
    · exact hdiv 1 (by simpa using h)
  rw [count_two_other w hw0 hw1]
  rcases key w 0 (hw w hw0 hw1) with h | h
  · omega
  · exact hdiv 0 (by simpa using h)

/-- **G9 local core, de Rham part**, given an embedding `F' → B_dR` with
`σ(ι x) = ι(σ|_{F'} x)` (task g9-derham's second run constructs one: `iotaDR`, `G9.lean`). -/
theorem core_dR_F (ι' : fieldF p F →ₐ[ℚ_[p]] BdR p)
    (hι' : ∀ (σ : GQp p) (x : fieldF p F), bdrAct p σ (ι' x) = ι' (gammaF p F σ x))
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (hdR : IsDeRhamOver p ρ) :
    IsDeRham p ρE := by
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hsemi : ∀ σ x b, drAct p σ (ι' x * b) = ι' (gammaF p F σ x) * drAct p σ b := by
    intro σ x b
    rw [drAct_apply, drAct_apply, map_mul, hι']
  obtain ⟨hc, -⟩ := core_count_F p F (drAct p) ι' hsemi ρ ρE eE he
  rw [IsDeRhamOver, ddrSpaceOver_eq_DspRep, finrank_V_of_eE p eE] at hdR
  rw [IsDeRham, ddrSpace_eq_DspMat]
  rw [hdR] at hc
  have : finrank ℚ_[p] F * (finrank ℚ_[p] (Dsp (drAct p) (matRep p ρE) Set.univ)) =
      finrank ℚ_[p] F * (2 * finrank ℚ_[p] E) := by
    have := hc; ring_nf at this ⊢; omega
  exact Nat.eq_of_mul_eq_mul_left hf this

/-- **G9 local core, de Rham part** (given an equivariant `ℚ̄_p → B_dR`). -/
theorem core_dR (ιB : PadicAlgCl p →ₐ[ℚ_[p]] BdR p)
    (hιB : ∀ (σ : GQp p) (x : PadicAlgCl p), bdrAct p σ (ιB x) = ιB (σ x))
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (hdR : IsDeRhamOver p ρ) :
    IsDeRham p ρE :=
  core_dR_F p F (ιB.comp (fieldF p F).val)
    (fun σ x => by
      simp only [AlgHom.comp_apply, IntermediateField.coe_val, hιB, gammaF_apply_coe])
    ρ ρE eE he hdR

end Local

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Local.lean

/-!
# G9: the local count (Hodge–Tate part, and the de Rham part modulo `ℚ̄_p ⊆ B_dR`)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

pkg-I4's spaces `htSpace`, `htSpaceOver`, `ddrSpace`, `ddrSpaceOver` are the spaces `Dsp` of
`Descent.lean` for the actions `σ ↦ χ(σ)^i · σ` on `ℂ_p` and `σ ↦ σ` on `B_dR`. From R10 over a
finite Galois `F/ℚ_p`, the decomposition `C ⊗ V_p(A) ≅ r|G_F ⊕ r|G_F` (G8's output), the count
`overF_count` and the descent `descent_finrank` give the conclusions of N5's Lemma
`lem:de-rham-descent` at `K = ℚ_p`.

Main results here:
* `htMult_eq_one_of_R10` (G9, Hodge–Tate part): `htMult p r 0 = 1` and `htMult p r (-1) = 1`.
* `isDeRham_of_R10_of_emb` (G9, de Rham part) under two hypotheses on `B_dR` that are proved in
  `BdREmb.lean`: `bdrAct` is multiplicative, and `F' ⊆ ℚ̄_p` embeds `G_{ℚ_p}`-equivariantly in
  `B_dR`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

/-! `GlueI3.repBaseChange` (Leaves.lean, section `PkgI3Sec`) comes from `I3Layer.lean`, the
verbatim restatement of that section. -/

/-! ### A divisibility lemma -/

/-- If `ι : L → B` commutes with the action of `S`, then `Dsp act ρ S` is an `L`-space, so its
`K`-dimension is divisible by `[L:K]`. -/
theorem finrank_dvd_Dsp_of_emb {K G B V L : Type*} [Field K] [Group G] [CommRing B] [Algebra K B]
    [AddCommGroup V] [Module K V] [Field L] [Algebra K L]
    (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V) (S : Set G) (ι : L →ₐ[K] B)
    (hlin : ∀ g ∈ S, ∀ x b, act g (ι x * b) = ι x * act g b) :
    finrank K L ∣ finrank K (Dsp act ρ S) := by
  let _ : Algebra L B := ι.toRingHom.toAlgebra
  have : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq (fun k => (ι.commutes k).symm)
  have hLsmul : ∀ (x : L) (b : B), x • b = ι x * b := fun _ _ => rfl
  let DL : Submodule L (V →ₗ[K] B) :=
    { carrier := {φ | φ ∈ Dsp act ρ S}
      zero_mem' := (Dsp act ρ _).zero_mem
      add_mem' := fun ha hb => (Dsp act ρ _).add_mem ha hb
      smul_mem' := by
        intro x φ hφ g hg v
        simp only [Set.mem_ofPred_eq] at hφ
        simp only [LinearMap.smul_apply, hLsmul, hφ g hg v, hlin g hg] }
  have hDL : DL.restrictScalars K = Dsp act ρ S := Submodule.ext fun _ => Iff.rfl
  have e2 : finrank K DL = finrank K (Dsp act ρ S) := by rw [← hDL]; rfl
  have : Module.Free L DL := Module.Free.of_divisionRing L DL
  rw [← e2, ← Module.finrank_mul_finrank K L DL]
  exact dvd_mul_right _ _

section Actions

variable (p : ℕ) [Fact p.Prime]

theorem cpAct_mul (σ τ : GQp p) (x : ℂ_[p]) : cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _)
      ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe]; rfl

theorem cpAct_one (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe]; rfl

theorem cpAct_smul (σ : GQp p) (c : ℚ_[p]) (x : ℂ_[p]) : cpAct p σ (c • x) = c • cpAct p σ x := by
  rw [Algebra.smul_def, map_mul, cpAct_algebraMap, ← Algebra.smul_def]

theorem cyc_mul (σ τ : GQp p) : cyc p (σ * τ) = cyc p σ * cyc p τ := by
  simp only [cyc]
  rw [← map_mul]
  rfl

theorem cyc_one : cyc p 1 = 1 := by
  simp only [cyc]
  rw [← map_one (cyclotomicCharacter (PadicAlgCl p) p)]
  rfl

theorem cycPow_mul (σ τ : GQp p) (i : ℤ) :
    cycPow p (σ * τ) i = cycPow p σ i * cycPow p τ i := by
  simp only [cycPow, cyc_mul, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_one (i : ℤ) : cycPow p 1 i = 1 := by
  simp [cycPow, cyc_one]

/-- `x ↦ χ(σ)^i · σ(x)` on `ℂ_p`, `ℚ_p`-linear. -/
def cpActL (i : ℤ) (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := cycPow p σ i • cpAct p σ x
  map_add' x y := by rw [map_add, smul_add]
  map_smul' c x := by
    rw [cpAct_smul, smul_comm]
    rfl

theorem cpActL_apply (i : ℤ) (σ : GQp p) (x : ℂ_[p]) :
    cpActL p i σ x = cycPow p σ i • cpAct p σ x := rfl

/-- The twisted action `σ ↦ χ(σ)^i · σ` as a representation on `ℂ_p`. -/
def cpActHom (i : ℤ) : GQp p →* (ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun := cpActL p i
  map_one' := by
    refine LinearMap.ext fun x => ?_
    rw [cpActL_apply, cpAct_one, cycPow_one, one_smul]
    rfl
  map_mul' σ τ := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, cpActL_apply, cpActL_apply, cpActL_apply, cpAct_mul, cpAct_smul,
      cycPow_mul, mul_smul]

variable {C : Type*} [Field C] [Algebra ℚ_[p] C] {n : ℕ}

/-- `r : G_{ℚ_p} → GL_n(C)` as a `ℚ_p`-linear representation on `Cⁿ`. -/
def rRep (r : GQp p →* GL (Fin n) C) : Representation ℚ_[p] (GQp p) (Fin n → C) where
  toFun σ := (Matrix.mulVecLin (r σ : Matrix (Fin n) (Fin n) C)).restrictScalars ℚ_[p]
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' σ τ := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mulVec_mulVec]

theorem rRep_apply (r : GQp p →* GL (Fin n) C) (σ : GQp p) (v : Fin n → C) :
    rRep p r σ v = Matrix.mulVec (r σ : Matrix (Fin n) (Fin n) C) v := rfl

variable [FiniteDimensional ℚ_[p] C]

theorem htSpace_eq_DspAct (r : GQp p →* GL (Fin n) C) (i : ℤ) :
    htSpace p r i = Dsp (cpActHom p i) (rRep p r) Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

theorem htSpaceOver_eq_DspAct (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    htSpaceOver p ρ i = Dsp ((cpActHom p i).comp (gfToGqp p F)) ρ Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

/-- `Dsp` over the kernel of `G_{ℚ_p} → Gal(F'/ℚ_p)` is `Dsp` over `G_F`. -/
theorem Dsp_ker_gammaF (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] {B W : Type*} [AddCommGroup B] [Module ℚ_[p] B] [AddCommGroup W]
    [Module ℚ_[p] W] (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ρ : Representation ℚ_[p] (GQp p) W) :
    Dsp act ρ ((gammaF p F).ker : Set (GQp p)) =
      Dsp (act.comp (gfToGqp p F)) (ρ.comp (gfToGqp p F)) Set.univ := by
  ext φ
  rw [← range_gfToGqp]
  constructor
  · intro h σ _ v
    exact h _ ⟨σ, rfl⟩ v
  · rintro h _ ⟨σ, rfl⟩ v
    exact h σ trivial v

/-- `F' → ℂ_p`. -/
def iotaCp (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] :
    fieldF p F →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp (fieldF p F).val

theorem cpAct_iotaCp (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] (σ : GQp p) (x : fieldF p F) :
    cpAct p σ (iotaCp p F x) = iotaCp p F (gammaF p F σ x) := by
  simp only [iotaCp, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  rw [← PadicComplex.coe_eq, ← PadicComplex.coe_eq, cpAct_coe]
  congr 1
  exact (gammaF_apply_coe p F σ x).symm

theorem cpActHom_semi (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] (i : ℤ) (σ : GQp p) (x : fieldF p F) (b : ℂ_[p]) :
    cpActHom p i σ (iotaCp p F x * b) = iotaCp p F (gammaF p F σ x) * cpActHom p i σ b := by
  change cpActL p i σ _ = _ * cpActL p i σ b
  rw [cpActL_apply, cpActL_apply, map_mul, cpAct_iotaCp, mul_smul_comm]

end Actions

/-! ### G9, Hodge–Tate part -/

section HT

variable (p : ℕ) [Fact p.Prime]

/-- From the counts: if `dim Dsp_{G_F}(V) = 2[F:ℚ_p]·m`-type data hold, conclude. The core
arithmetic of both parts: `c · d_V = 2 · d_U`, `d_U = [F:ℚ_p] · d_G` give `d_G`. -/
theorem descended_finrank (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρV : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] V ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C ρV σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2))
    {B : Type*} [CommRing B] [Algebra ℚ_[p] B] (act : GQp p →* (B →ₗ[ℚ_[p]] B))
    (ι : fieldF p F →ₐ[ℚ_[p]] B)
    (hsemi : ∀ σ x b, act σ (ι x * b) = ι (gammaF p F σ x) * act σ b)
    (hpos : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) ρV Set.univ)) :
    finrank ℚ_[p] C * finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) ρV Set.univ) =
      2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ)) := by
  have hcount := overF_count (act.comp (gfToGqp p F)) (C := C) (fun σ => ρV σ)
    (fun σ => rRep p r (gfToGqp p F σ)) Set.univ e (fun σ x => he σ x) hpos
  have hdes := descent_finrank act (rRep p r) ι (gammaF p F) (gammaF_surjective p F) hsemi
  rw [Dsp_ker_gammaF, finrank_fieldF] at hdes
  rw [hcount, ← hdes]
  rfl

/-- **G9, Hodge–Tate part.** Hypotheses: R10 (`PkgI4.DeRhamComparison`) and G8's output localized
at `p`: a finite Galois `F/ℚ_p`, an abelian surface `A/F`, a finite `C/ℚ_p`,
`r : G_{ℚ_p} → GL₂(C)` and a `C`-linear `G_F`-equivariant `C ⊗ V_p(A) ≅ r|G_F ⊕ r|G_F`.
Conclusion: `r` has Hodge–Tate multiplicity `1` at the weights `0` and `−1`. -/
theorem htMult_eq_one_of_R10 (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    htMult p r 0 = 1 ∧ htMult p r (-1) = 1 := by
  obtain ⟨-, h0, h1⟩ := hR10 p F A 2 hA
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hC : 0 < finrank ℚ_[p] C := Module.finrank_pos
  -- the common computation, for `i = -w`
  have key : ∀ w : ℤ, htMultOver p (A.galRep p) w = 2 → htMult p r w = 1 := by
    intro w hw
    set i := -w
    set act := cpActHom p i
    set nV := finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ)
    have hnV : finrank ℚ_[p] (htSpaceOver p (A.galRep p) i) = nV := by
      rw [htSpaceOver_eq_DspAct]
    have hdvd : finrank ℚ_[p] F ∣ nV := by
      have := finrank_dvd_Dsp_of_emb (act.comp (gfToGqp p F)) (fun σ => A.galRep p σ) Set.univ
        (iotaCp p F) (fun σ _ x b => by
          have hk : gfToGqp p F σ ∈ (gammaF p F).ker := by
            rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
          rw [MonoidHom.mem_ker] at hk
          change act (gfToGqp p F σ) _ = _
          rw [cpActHom_semi, hk]
          rfl)
      rwa [finrank_fieldF] at this
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : k = 2 := by
      have : htMultOver p (A.galRep p) w = k := by
        rw [htMultOver, hnV, hk, Nat.mul_div_cancel_left _ hF]
      rw [← this, hw]
    have hpos : 0 < nV := by rw [hk, hk2]; positivity
    have hd : finrank ℚ_[p] C * nV =
        2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ)) :=
      descended_finrank p F (A.galRep p) C r e he act (iotaCp p F) (cpActHom_semi p F i) hpos
    rw [hk, hk2] at hd
    have hG : finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) = finrank ℚ_[p] C := by
      have : finrank ℚ_[p] F * 2 * finrank ℚ_[p] C =
          finrank ℚ_[p] F * 2 * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
        linarith [hd]
      exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm
    rw [htMult, htSpace_eq_DspAct, hG, Nat.div_self hC]
  exact ⟨key 0 h0, key (-1) h1⟩

end HT

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/CoefDescent.lean

/-!
# G9: from `ℚ̄_p`-coefficients to a finite coefficient field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

`coef_descent`: let `F/ℚ_p` be finite Galois, `V` a `ℚ_p`-linear representation of `G_F`,
`R : G_{ℚ_p} → GL₂(ℚ̄_p)` a homomorphism, and `e' : ℚ̄_p ⊗ V ≅ ℚ̄_p² × ℚ̄_p²` (`ℚ̄_p`-linear)
intertwining `V|G_F` with `R|G_F ⊕ R|G_F`. Then there is a finite extension `E ⊆ ℚ̄_p` of `ℚ_p`
such that `R` takes values in `GL₂(E)` (`ρE`), and an `E`-linear `E ⊗ V ≅ E² × E²` intertwining
`V|G_F` with `ρE|G_F ⊕ ρE|G_F`. `E` is generated by the coordinates of `e'(1 ⊗ bₖ)` and of
`e'⁻¹` of the standard basis (`bₖ` a basis of `V`), and the entries of `R` at coset
representatives of `G_{ℚ_p}/G_F` (finite: `Gal(F'/ℚ_p)`). No topology is used (this replaces
the Baire argument of g0-mod-galois's docstring).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

section Lift

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {G : Type*} [Group G] {n : ℕ}

/-- A homomorphism to `GL_n(Ω)` with entries in an intermediate field `E` lifts to `GL_n(E)`. -/
def liftGL (E : IntermediateField K Ω) (f : G →* GL (Fin n) Ω)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) Ω) i j ∈ E) : G →* GL (Fin n) E :=
  let M : G → Matrix (Fin n) (Fin n) E := fun g i j => ⟨(f g : Matrix (Fin n) (Fin n) Ω) i j, h g i j⟩
  have hM : ∀ g, (M g).map (algebraMap E Ω) = (f g : Matrix (Fin n) (Fin n) Ω) := fun g => by
    ext i j; rfl
  have hinj : Function.Injective (fun A : Matrix (Fin n) (Fin n) E => A.map (algebraMap E Ω)) :=
    Matrix.map_injective (algebraMap E Ω).injective
  have hmul : ∀ g g', M (g * g') = M g * M g' := fun g g' => hinj (by
    simp only [Matrix.map_mul, hM, map_mul, Units.val_mul])
  have hone : M 1 = 1 := hinj (by simp only [hM, map_one, Units.val_one, Matrix.map_one,
    map_zero, map_one])
  { toFun := fun g => ⟨M g, M g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
      by rw [← hmul, inv_mul_cancel, hone]⟩
    map_one' := Units.ext hone
    map_mul' := fun g g' => Units.ext (hmul g g') }

theorem liftGL_map (E : IntermediateField K Ω) (f : G →* GL (Fin n) Ω)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) Ω) i j ∈ E) (g : G) :
    Matrix.GeneralLinearGroup.map (algebraMap E Ω) (liftGL E f h g) = f g := by
  ext i j; rfl

theorem liftGL_coe (E : IntermediateField K Ω) (f : G →* GL (Fin n) Ω)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) Ω) i j ∈ E) (g : G) (i j : Fin n) :
    ((liftGL E f h g : Matrix (Fin n) (Fin n) E) i j : Ω) = (f g : Matrix (Fin n) (Fin n) Ω) i j :=
  rfl

end Lift

section Pairs

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (E : IntermediateField K Ω)

/-- Pairs of vectors with coordinates in `E`, as a `K`-subspace of `Ω² × Ω²`. -/
def pairsIn : Submodule K ((Fin 2 → Ω) × (Fin 2 → Ω)) where
  carrier := {w | ∀ i, w.1 i ∈ E ∧ w.2 i ∈ E}
  zero_mem' := fun i => ⟨E.zero_mem, E.zero_mem⟩
  add_mem' := fun ha hb i => ⟨E.add_mem (ha i).1 (hb i).1, E.add_mem (ha i).2 (hb i).2⟩
  smul_mem' := fun c w hw i => ⟨by simpa using E.smul_mem (hw i).1 (x := c),
    by simpa using E.smul_mem (hw i).2 (x := c)⟩

theorem smul_mem_pairsIn {a : Ω} (ha : a ∈ E) {w : (Fin 2 → Ω) × (Fin 2 → Ω)}
    (hw : w ∈ pairsIn E) : a • w ∈ pairsIn E := fun i =>
  ⟨by simpa using E.mul_mem ha (hw i).1, by simpa using E.mul_mem ha (hw i).2⟩

/-- `E² × E² → Ω² × Ω²`. -/
def inclPair : (Fin 2 → E) × (Fin 2 → E) →ₗ[E] (Fin 2 → Ω) × (Fin 2 → Ω) :=
  ((Algebra.linearMap E Ω).compLeft (Fin 2)).prodMap ((Algebra.linearMap E Ω).compLeft (Fin 2))

theorem inclPair_apply (w : (Fin 2 → E) × (Fin 2 → E)) :
    inclPair E w = (fun i => (w.1 i : Ω), fun i => (w.2 i : Ω)) := rfl

theorem inclPair_injective : Function.Injective (inclPair E) := by
  intro w w' h
  rw [inclPair_apply, inclPair_apply, Prod.mk.injEq] at h
  ext i
  · exact congrFun h.1 i
  · exact congrFun h.2 i

end Pairs

section Coef

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [IsGalois ℚ_[p] F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

local notation "Ω" => PadicAlgCl p

theorem matMap_mulVec {E : IntermediateField ℚ_[p] Ω} (A : Matrix (Fin 2) (Fin 2) E)
    (v : Fin 2 → E) (i : Fin 2) :
    ((A.mulVec v) i : Ω) = ((A.map (algebraMap E Ω)).mulVec (fun k => (v k : Ω))) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

/-- **Finite coefficient field.** -/
theorem coef_descent (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (R : GQp p →* GL (Fin 2) Ω)
    (e' : Ω ⊗[ℚ_[p]] V ≃ₗ[Ω] (Fin 2 → Ω) × (Fin 2 → Ω))
    (he' : ∀ σ x, e' ((ρ σ).baseChange Ω x) =
      ((R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω).mulVec (e' x).1,
        (R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω).mulVec (e' x).2)) :
    ∃ (E : IntermediateField ℚ_[p] Ω) (_ : FiniteDimensional ℚ_[p] E)
      (ρE : GQp p →* GL (Fin 2) E) (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)),
      (∀ τ, Matrix.GeneralLinearGroup.map (algebraMap E Ω) (ρE τ) = R τ) ∧
      ∀ σ x, eE ((ρ σ).baseChange E x) =
        ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x) := by
  classical
  -- `dim V = 4`
  have hV4 : finrank ℚ_[p] V = 4 := by
    have := e'.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at this
    omega
  have : FiniteDimensional ℚ_[p] V := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasis ℚ_[p] V
  let bΩ := Algebra.TensorProduct.basis Ω b
  have hbΩ : ∀ k, bΩ k = (1 : Ω) ⊗ₜ b k := fun k => Algebra.TensorProduct.basis_apply b k
  -- `φ v = e'(1 ⊗ v)`
  let φ : V →ₗ[ℚ_[p]] (Fin 2 → Ω) × (Fin 2 → Ω) :=
    (e'.toLinearMap.restrictScalars ℚ_[p]).comp (TensorProduct.mk ℚ_[p] Ω V 1)
  have hφ : ∀ v, φ v = e' ((1 : Ω) ⊗ₜ v) := fun _ => rfl
  let y : Fin 2 → Ω ⊗[ℚ_[p]] V := fun j => e'.symm (Pi.single j 1, 0)
  let a : Fin 2 → Fin (finrank ℚ_[p] V) → Ω := fun j k => bΩ.repr (y j) k
  -- coset representatives of `G_{ℚ_p} / G_F`
  let s : (fieldF p F ≃ₐ[ℚ_[p]] fieldF p F) → GQp p := Function.surjInv (gammaF_surjective p F)
  have hs : ∀ γ, gammaF p F (s γ) = γ := Function.surjInv_eq (gammaF_surjective p F)
  -- the generating set
  let S1 : Set Ω := Set.range (fun ki : Fin (finrank ℚ_[p] V) × Fin 2 => (φ (b ki.1)).1 ki.2)
  let S2 : Set Ω := Set.range (fun ki : Fin (finrank ℚ_[p] V) × Fin 2 => (φ (b ki.1)).2 ki.2)
  let S3 : Set Ω := Set.range (fun jk : Fin 2 × Fin (finrank ℚ_[p] V) => a jk.1 jk.2)
  let S4 : Set Ω := Set.range (fun x : (fieldF p F ≃ₐ[ℚ_[p]] fieldF p F) × Fin 2 × Fin 2 =>
    (R (s x.1) : Matrix (Fin 2) (Fin 2) Ω) x.2.1 x.2.2)
  let S : Set Ω := S1 ∪ S2 ∪ S3 ∪ S4
  have hSfin : S.Finite :=
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)
  have : Finite S := hSfin.to_subtype
  let E : IntermediateField ℚ_[p] Ω := IntermediateField.adjoin ℚ_[p] S
  have hEfin : FiniteDimensional ℚ_[p] E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hSE : ∀ x ∈ S, x ∈ E := fun x hx => IntermediateField.subset_adjoin ℚ_[p] S hx
  -- C1: `φ(V) ⊆ E² × E²`
  have hC1 : ∀ v, φ v ∈ pairsIn E := by
    intro v
    have hspan : Submodule.span ℚ_[p] (Set.range b) ≤ (pairsIn E).comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩ i
      exact ⟨hSE _ (Or.inl (Or.inl (Or.inl ⟨(k, i), rfl⟩))),
        hSE _ (Or.inl (Or.inl (Or.inr ⟨(k, i), rfl⟩)))⟩
    rw [b.span_eq] at hspan
    exact hspan Submodule.mem_top
  have ha : ∀ j k, a j k ∈ E := fun j k => hSE _ (Or.inl (Or.inr ⟨(j, k), rfl⟩))
  -- C2: entries of `R` on `G_F` lie in `E`
  have hC2 : ∀ σ i j, (R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω) i j ∈ E := by
    intro σ i j
    have hy : y j = ∑ k, a j k • bΩ k := (bΩ.sum_repr (y j)).symm
    have h1 : e' ((ρ σ).baseChange Ω (y j)) =
        ((R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω).mulVec (Pi.single j 1),
          (R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω).mulVec 0) := by
      rw [he']
      simp only [y, LinearEquiv.apply_symm_apply]
    have h2 : e' ((ρ σ).baseChange Ω (y j)) = ∑ k, a j k • φ (ρ σ (b k)) := by
      rw [hy, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, map_smul, hbΩ, LinearMap.baseChange_tmul, hφ]
    have h3 : ∑ k, a j k • φ (ρ σ (b k)) ∈ pairsIn E :=
      Submodule.sum_mem _ fun k _ => smul_mem_pairsIn E (ha j k) (hC1 _)
    rw [← h2, h1] at h3
    have := (h3 i).1
    simpa [Matrix.mulVec_single_one] using this
  -- C3: entries of `R` everywhere lie in `E`
  have hC3 : ∀ τ i j, (R τ : Matrix (Fin 2) (Fin 2) Ω) i j ∈ E := by
    intro τ i j
    have hk : (s (gammaF p F τ))⁻¹ * τ ∈ (gfToGqp p F).range := by
      rw [range_gfToGqp, MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    obtain ⟨σ, hσ⟩ := hk
    have hτ : τ = s (gammaF p F τ) * gfToGqp p F σ := by rw [hσ]; group
    rw [hτ, map_mul, Units.val_mul, Matrix.mul_apply]
    refine IntermediateField.sum_mem _ fun l _ => IntermediateField.mul_mem _ ?_ (hC2 σ l j)
    exact hSE _ (Or.inr ⟨(gammaF p F τ, i, l), rfl⟩)
  -- the lift `ρE`
  let ρE : GQp p →* GL (Fin 2) E := liftGL E R hC3
  -- `φE : V → E² × E²`
  let φE : V →ₗ[ℚ_[p]] (Fin 2 → E) × (Fin 2 → E) :=
    { toFun := fun v => (fun i => ⟨(φ v).1 i, (hC1 v i).1⟩, fun i => ⟨(φ v).2 i, (hC1 v i).2⟩)
      map_add' := fun v w => by ext i <;> simp
      map_smul' := fun c v => by ext i <;> simp [Algebra.smul_def] }
  have hφE : ∀ v, inclPair E (φE v) = φ v := fun v => rfl
  let eE0 : E ⊗[ℚ_[p]] V →ₗ[E] (Fin 2 → E) × (Fin 2 → E) := φE.liftBaseChange E
  -- `E ⊗ V → Ω ⊗ V`
  let ιbc : E ⊗[ℚ_[p]] V →ₗ[ℚ_[p]] Ω ⊗[ℚ_[p]] V :=
    LinearMap.rTensor V ((Algebra.ofId E Ω).toLinearMap.restrictScalars ℚ_[p])
  have hιbc_inj : Function.Injective ιbc :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap E Ω).injective
  have hcompat : ∀ x, inclPair E (eE0 x) = e' (ιbc x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      simp only [eE0, LinearMap.liftBaseChange_tmul, map_smul, hφE, ιbc, LinearMap.rTensor_tmul]
      rw [show ((Algebra.ofId E Ω).toLinearMap.restrictScalars ℚ_[p]) c ⊗ₜ[ℚ_[p]] v =
          (c : Ω) • ((1 : Ω) ⊗ₜ[ℚ_[p]] v) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl]
      rw [map_smul, ← hφ]
      rfl
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have heE0_inj : Function.Injective eE0 := by
    intro x x' h
    apply hιbc_inj
    apply e'.injective
    rw [← hcompat, ← hcompat, h]
  have hdim : finrank E (E ⊗[ℚ_[p]] V) = finrank E ((Fin 2 → E) × (Fin 2 → E)) := by
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun, hV4]
  have : FiniteDimensional E (E ⊗[ℚ_[p]] V) := Module.finite_of_finrank_pos (by
    rw [Module.finrank_baseChange, hV4]; omega)
  have heE0_surj : Function.Surjective eE0 :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp heE0_inj
  let eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E) :=
    LinearEquiv.ofBijective eE0 ⟨heE0_inj, heE0_surj⟩
  refine ⟨E, hEfin, ρE, eE, fun τ => liftGL_map E R hC3 τ, fun σ x => ?_⟩
  apply inclPair_injective E
  change inclPair E (eE0 ((ρ σ).baseChange E x)) = _
  have hcomm : ιbc ((ρ σ).baseChange E x) = (ρ σ).baseChange Ω (ιbc x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => rfl
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  rw [hcompat, hcomm, he', ← hcompat]
  change _ = inclPair E ((matRep p ρE (gfToGqp p F σ)) (eE0 x).1,
    (matRep p ρE (gfToGqp p F σ)) (eE0 x).2)
  rw [inclPair_apply, inclPair_apply]
  simp only [Prod.mk.injEq]
  constructor <;> funext i <;> rw [matRep_apply, matMap_mulVec] <;> rfl

end Coef

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/BdREmb.lean

/-!
# G9: the action of `G_{ℚ_p}` on `B_dR`, and `F' ⊆ B_dR` equivariantly

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

* `bdrAct_mul`, `bdrAct_one`: pkg-I4's `bdrAct` is an action (functoriality of pkg-I4's
  `DR.bdrMap`, through the tilt, Witt vectors, `[1/p]` and the adic completion), packaged as the
  representation `bdrActHom : G_{ℚ_p} →* End_{ℚ_p}(B_dR)`.
* `thetaPlusCp_bdrPlusMap`: bdr-kertheta's residue map `θ⁺ : B_dR^+ → ℂ_p` is equivariant.
* `thetaPlusCp_qpToPlus`: `θ⁺` is `ℚ_p`-linear for pkg-I4's `ℚ_p ⊆ B_dR^+`.
* `iotaDR`, `bdrAct_iotaDR`: for a finite Galois `F/ℚ_p`, the copy `F' ⊆ ℚ̄_p` of `F` embeds in
  `B_dR` with `σ(ι x) = ι(σ x)`, by the Hensel lift (`HenselEmb.lean`) through `θ⁺`
  (`B_dR^+` is `(ξ)`-adically complete, local with maximal ideal `ker θ⁺ = (ξ)`, a domain:
  bdr-kertheta).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 Module Ideal

noncomputable section

namespace DRFunct

open _root_.HDec.PkgI4.DR ZInQ.Contrib.G9.PkgI4.DR

variable (p : ℕ) [Fact p.Prime]

section general

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem modPMap_comp (f : R →+* S) (g : S →+* T) :
    modPMap p (g.comp f) = (modPMap p g).comp (modPMap p f) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem modPMap_id : modPMap p (RingHom.id R) = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem wittMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) :
    WittVector.map (p := p) (g.comp f) = (WittVector.map g).comp (WittVector.map f) := by
  ext x n
  simp

theorem wittMap_id {A : Type*} [CommRing A] :
    WittVector.map (p := p) (RingHom.id A) = RingHom.id _ := by
  ext x n
  simp

variable [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [Fact ¬IsUnit (p : T)]

theorem preTiltMap_comp (f : R →+* S) (g : S →+* T) :
    preTiltMap p (g.comp f) = (preTiltMap p g).comp (preTiltMap p f) :=
  RingHom.ext fun x => Perfection.ext fun n => by
    rw [coeff_preTiltMap, RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, modPMap_comp]
    rfl

theorem preTiltMap_id : preTiltMap p (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => Perfection.ext fun n => by
    rw [coeff_preTiltMap, modPMap_id]
    rfl

theorem locMap_comp (f : R →+* S) (g : S →+* T) :
    locMap p (g.comp f) = (locMap p g).comp (locMap p f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, locMap, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq]
  rw [preTiltMap_comp, wittMap_comp]
  rfl

theorem locMap_id : locMap p (RingHom.id R) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
    IsLocalization.Away.lift, IsLocalization.lift_eq]
  rw [preTiltMap_id, wittMap_id]
  rfl

end general

section adic

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

theorem adicMap_congr (J : Ideal A) (J' : Ideal B) {g g' : A →+* B} (h : g = g')
    (hg : J ≤ J'.comap g) (hg' : J ≤ J'.comap g') : adicMap J J' g hg = adicMap J J' g' hg' := by
  subst h; rfl

theorem adicMap_comp_apply (J : Ideal A) (J' : Ideal B) (J'' : Ideal C) (g1 : A →+* B)
    (h1 : J ≤ J'.comap g1) (g2 : B →+* C) (h2 : J' ≤ J''.comap g2) (g3 : A →+* C)
    (h3 : J ≤ J''.comap g3) (hg : g3 = g2.comp g1) (x : AdicCompletion J A) :
    adicMap J J'' g3 h3 x = adicMap J' J'' g2 h2 (adicMap J J' g1 h1 x) := by
  subst hg
  refine AdicCompletion.ext_evalₐ fun n => ?_
  have hin := adicMap_evalₐ J J' g1 h1 n x
  rw [adicMap_evalₐ, adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply] at hin ⊢
  erw [hin]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

theorem evalOneₐ_adicMap (J : Ideal A) (J' : Ideal B) (g : A →+* B) (hg : J ≤ J'.comap g)
    (x : AdicCompletion J A) :
    AdicCompletion.evalOneₐ J' (adicMap J J' g hg x) =
      Ideal.quotientMap J' g hg (AdicCompletion.evalOneₐ J x) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J 1 x)
  have e1 : AdicCompletion.evalOneₐ J x =
      Ideal.Quotient.factor (show J ^ 1 ≤ J by simp) (AdicCompletion.evalₐ J 1 x) := rfl
  have e2 : AdicCompletion.evalOneₐ J' (adicMap J J' g hg x) =
      Ideal.Quotient.factor (show J' ^ 1 ≤ J' by simp)
        (AdicCompletion.evalₐ J' 1 (adicMap J J' g hg x)) := rfl
  rw [e1, e2, adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply]
  erw [← ha]
  rfl

theorem adicMap_id_apply (J : Ideal A) (g : A →+* A) (h : J ≤ J.comap g)
    (hg : g = RingHom.id A) (x : AdicCompletion J A) : adicMap J J g h x = x := by
  subst hg
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

end adic

section bdr

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [Fact ¬IsUnit (p : T)]
  [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
  [IsAdicComplete (span {(p : T)}) T]

theorem bdrPlusMap_comp (f : R →+* S) (g : S →+* T) :
    bdrPlusMap p (g.comp f) = (bdrPlusMap p g).comp (bdrPlusMap p f) :=
  RingHom.ext fun x => adicMap_comp_apply _ _ _ (locMap p f) (ker_le_comap_locMap p f)
    (locMap p g) (ker_le_comap_locMap p g) _ _ (locMap_comp p f g) x

theorem bdrPlusMap_id : bdrPlusMap p (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => adicMap_id_apply _ _ _ (locMap_id p) x

theorem bdrMap_comp (f1 : R →+* S) (g1 : S →+* R) (hgf1 : ∀ x, g1 (f1 x) = x)
    (hfg1 : ∀ y, f1 (g1 y) = y) (f2 : S →+* T) (g2 : T →+* S) (hgf2 : ∀ x, g2 (f2 x) = x)
    (hfg2 : ∀ y, f2 (g2 y) = y) (f3 : R →+* T) (g3 : T →+* R) (hgf3 : ∀ x, g3 (f3 x) = x)
    (hfg3 : ∀ y, f3 (g3 y) = y) (hf : f3 = f2.comp f1) :
    bdrMap p f3 g3 hgf3 hfg3 = (bdrMap p f2 g2 hgf2 hfg2).comp (bdrMap p f1 g1 hgf1 hfg1) := by
  apply IsLocalization.ringHom_ext (genMonoid p R)
  ext x
  simp only [RingHom.comp_apply, bdrMap, IsLocalization.map_eq]
  subst hf
  rw [bdrPlusMap_comp]
  rfl

theorem bdrMap_id (f : R →+* R) (g : R →+* R) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) (hf : f = RingHom.id R) :
    bdrMap p f g hgf hfg = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (genMonoid p R)
  ext x
  simp only [RingHom.comp_apply, bdrMap, IsLocalization.map_eq, RingHom.id_apply]
  subst hf
  rw [bdrPlusMap_id]
  rfl

end bdr

end DRFunct

section Action

variable (p : ℕ) [Fact p.Prime]

theorem oAct_mul (σ τ : GQp p) : oAct p (σ * τ) = (oAct p σ).comp (oAct p τ) :=
  RingHom.ext fun x => Subtype.ext (cpAct_mul p σ τ x)

theorem oAct_one : oAct p 1 = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (cpAct_one p x)

theorem bdrAct_mul (σ τ : GQp p) : bdrAct p (σ * τ) = (bdrAct p σ).comp (bdrAct p τ) :=
  DRFunct.bdrMap_comp p _ _ _ _ _ _ _ _ _ _ _ _ (oAct_mul p σ τ)

theorem bdrAct_one : bdrAct p 1 = RingHom.id _ :=
  DRFunct.bdrMap_id p _ _ _ _ (oAct_one p)

/-- `σ` acting `ℚ_p`-linearly on `B_dR`. -/
def bdrActL (σ : GQp p) : BdR p →ₗ[ℚ_[p]] BdR p where
  toFun := bdrAct p σ
  map_add' := map_add _
  map_smul' := bdrAct_smul p σ

/-- **The representation `G_{ℚ_p} → End_{ℚ_p}(B_dR)`.** -/
def bdrActHom : GQp p →* (BdR p →ₗ[ℚ_[p]] BdR p) where
  toFun := bdrActL p
  map_one' := LinearMap.ext fun x => by
    change bdrAct p 1 x = x
    rw [bdrAct_one]; rfl
  map_mul' σ τ := LinearMap.ext fun x => by
    change bdrAct p (σ * τ) x = bdrAct p σ (bdrAct p τ x)
    rw [bdrAct_mul]; rfl

theorem bdrActHom_apply (σ : GQp p) (x : BdR p) : bdrActHom p σ x = bdrAct p σ x := rfl

end Action

/-! ### `θ⁺` is equivariant and `ℚ_p`-linear -/

section Theta

variable (p : ℕ) [Fact p.Prime]

theorem thetaPlus_eq' (z : BDeRhamPlus 𝓞_ℂ_[p] p) : BdrKer.Cp.thetaPlus p z =
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) z) := rfl

theorem thetaPlus_mk (σ : GQp p) (x : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) :
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (Ideal.quotientMap _ (DR.locMap p (oAct p σ)) (DR.ker_le_comap_locMap p (oAct p σ))
        (Ideal.Quotient.mk _ x)) =
    DR.locMapBase p (oAct p σ) ((RingHom.quotientKerEquivOfSurjective
      (BdrKer.Cp.fontaineThetaInvertP_surjective p)) (Ideal.Quotient.mk _ x)) := by
  rw [Ideal.quotientMap_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [← RingHom.comp_apply, DR.fontaineThetaInvertP_naturality]
  rfl

theorem thetaPlus_quot (σ : GQp p)
    (q : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) ⧸
      RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) :
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (Ideal.quotientMap _ (DR.locMap p (oAct p σ)) (DR.ker_le_comap_locMap p (oAct p σ)) q) =
    DR.locMapBase p (oAct p σ) ((RingHom.quotientKerEquivOfSurjective
      (BdrKer.Cp.fontaineThetaInvertP_surjective p)) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact thetaPlus_mk p σ x

theorem thetaPlus_bdrPlusMap (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    BdrKer.Cp.thetaPlus p (DR.bdrPlusMap p (oAct p σ) y) =
      DR.locMapBase p (oAct p σ) (BdrKer.Cp.thetaPlus p y) := by
  have h := DRFunct.evalOneₐ_adicMap (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p))
    (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) (DR.locMap p (oAct p σ))
    (DR.ker_le_comap_locMap p (oAct p σ)) y
  rw [thetaPlus_eq', thetaPlus_eq']
  rw [show DR.bdrPlusMap p (oAct p σ) y = DR.adicMap _ _ (DR.locMap p (oAct p σ))
    (DR.ker_le_comap_locMap p (oAct p σ)) y from rfl, h]
  exact thetaPlus_quot p σ _

theorem awayEquivCp_locMapBase (σ : GQp p) (u : Localization.Away (p : 𝓞_ℂ_[p])) :
    BdrKer.Cp.awayEquivCp p (DR.locMapBase p (oAct p σ) u) =
      cpAct p σ (BdrKer.Cp.awayEquivCp p u) := by
  have h : (BdrKer.Cp.awayEquivCp p).toRingEquiv.toRingHom.comp (DR.locMapBase p (oAct p σ)) =
      (cpAct p σ).comp (BdrKer.Cp.awayEquivCp p).toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : 𝓞_ℂ_[p]))
    ext o
    simp only [RingHom.comp_apply, DR.locMapBase, Localization.awayLift,
      IsLocalization.Away.lift, IsLocalization.lift_eq]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.commutes]
    rfl
  exact congrArg (fun φ => φ u) h

/-- **`θ⁺` is `G_{ℚ_p}`-equivariant.** -/
theorem thetaPlusCp_bdrPlusMap (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    BdrKer.Cp.thetaPlusCp p (DR.bdrPlusMap p (oAct p σ) y) =
      cpAct p σ (BdrKer.Cp.thetaPlusCp p y) := by
  change BdrKer.Cp.awayEquivCp p (BdrKer.Cp.thetaPlus p _) =
    cpAct p σ (BdrKer.Cp.awayEquivCp p (BdrKer.Cp.thetaPlus p y))
  rw [thetaPlus_bdrPlusMap, awayEquivCp_locMapBase]

/-- `ℚ_p → B_dR^+` (pkg-I4's `ofLoc ∘ qpToLoc`). -/
def qpToPlus : ℚ_[p] →+* BDeRhamPlus 𝓞_ℂ_[p] p := (ofLoc p).comp (qpToLoc p)

theorem qpToBdR_eq (c : ℚ_[p]) :
    qpToBdR p c = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (qpToPlus p c) := rfl

theorem bdrPlusMap_qpToPlus (σ : GQp p) (c : ℚ_[p]) :
    DR.bdrPlusMap p (oAct p σ) (qpToPlus p c) = qpToPlus p c := by
  have h : (DR.bdrPlusMap p (oAct p σ)).comp (qpToPlus p) = qpToPlus p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply, qpToPlus]
    rw [qpToLoc_algebraMap, bdrPlusMap_ofLoc, locMap_algebraMap, wittMap_zpToW]
  exact congrArg (fun φ => φ c) h

theorem thetaPlusCp_zp_eq (z : ℤ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] z)) =
      ((WittVector.fontaineTheta (𝓞_ℂ_[p]) p (zpToW p z) : 𝓞_ℂ_[p]) : ℂ_[p]) := by
  simp only [qpToPlus, RingHom.comp_apply, qpToLoc_algebraMap]
  have e : ofLoc p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)))
      (zpToW p z)) = BdrKer.ofPlus _ p (algebraMap _ _ (zpToW p z)) := by
    rw [ofLoc]
    erw [AdicCompletion.algebraMap_apply]
    rfl
  rw [e]
  change BdrKer.Cp.awayEquivCp p (fontaineThetaInvertP _ p (algebraMap _ _ (zpToW p z))) = _
  simp only [fontaineThetaInvertP, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq, RingHom.comp_apply]
  rw [AlgEquiv.commutes]
  rfl

theorem norm_algebraMap_qp (c : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] c‖ = ‖c‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem thetaPlusCp_zp (z : ℤ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] z)) =
      algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] z) := by
  set g1 := (BdrKer.Cp.thetaPlusCp p).comp ((qpToPlus p).comp (algebraMap ℤ_[p] ℚ_[p]))
  set g2 := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  change g1 z = g2 z
  have hb1 : ∀ w, ‖g1 w‖ ≤ 1 := fun w => by
    change ‖BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] w))‖ ≤ 1
    rw [thetaPlusCp_zp_eq]
    exact (Cp.mem_O_iff p _).mp (Subtype.prop _)
  have hb2 : ∀ w, ‖g2 w‖ ≤ 1 := fun w => by
    change ‖algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] w)‖ ≤ 1
    rw [norm_algebraMap_qp]
    exact PadicInt.norm_le_one w
  by_contra hne
  have hd : 0 < ‖g1 z - g2 z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hd) (Cp.norm_p_lt_one p)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[p]) + w * (p : ℤ_[p]) ^ n := by
    rw [hw]; ring
  have hdiff : g1 z - g2 z = (g1 w - g2 w) * (p : ℂ_[p]) ^ n := by
    rw [hz, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    ring
  have hle : ‖g1 z - g2 z‖ ≤ 2 * ‖(p : ℂ_[p])‖ ^ n := by
    rw [hdiff, norm_mul, norm_pow]
    have : ‖g1 w - g2 w‖ ≤ 2 := by
      calc ‖g1 w - g2 w‖ ≤ ‖g1 w‖ + ‖g2 w‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hb1 w) (hb2 w)
        _ = 2 := by norm_num
    exact mul_le_mul_of_nonneg_right this (by positivity)
  linarith

/-- **`θ⁺` is `ℚ_p`-linear**: `θ⁺(c) = c` for `c ∈ ℚ_p ⊆ B_dR^+`. -/
theorem thetaPlusCp_qpToPlus (c : ℚ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p c) = algebraMap ℚ_[p] ℂ_[p] c := by
  have hext : (BdrKer.Cp.thetaPlusCp p).comp (qpToPlus p) = algebraMap ℚ_[p] ℂ_[p] := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply]
    exact thetaPlusCp_zp p z
  exact congrArg (fun φ => φ c) hext

end Theta

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/G9.lean

/-!
# G9: N5's appendix lemma — `r` is de Rham with Hodge–Tate weights `0, −1`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Glue step G9 of `docs/research/h-decomposition.md` (N5, Lemma `lem:de-rham-descent`,
`diophantine_zq.tex` L10939-11000), at `K = ℚ_p` with `F/ℚ_p` finite Galois (the case N5 uses:
`docs/research/h-trust.md` C3, "Galois choice of the field").

**`g9_deRham`.** Hypotheses: the leaf R10 (`PkgI4.DeRhamComparison`, restated verbatim in
`I4Layer.lean`) and G8's output localized at `p`: a finite Galois `F/ℚ_p`, an abelian surface
`A/F` (pkg-I3/I4's `AbVar`, `dim A = 2`), a finite `C/ℚ_p`, `r : G_{ℚ_p} → GL₂(C)` and a
`C`-linear isomorphism `e : C ⊗_{ℚ_p} V_p(A) ≅ C² × C²` intertwining `G_F` (acting through
pkg-I4's `gfToGqp`) with `r|G_F ⊕ r|G_F` (the form of G8's output in
`PkgI3.C2_absolutelyIrreducible`). Conclusion: `IsDeRham p r`, `htMult p r 0 = 1` and
`htMult p r (−1) = 1`.

T23 (Fontaine's closure properties) and T10 (Tate duality, an `opaque` placeholder) are not
used: R10's Lean form is already about `V_p(A)`, the subquotient step is a dimension count
(`overF_count`), and the finite descent is Speiser's lemma through `ℚ̄_p ⊆ B_dR^+`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 Module Ideal
open scoped TensorProduct

noncomputable section

section Emb

variable (p : ℕ) [Fact p.Prime]

/-- `B_dR^+` as a `ℚ_p`-algebra through pkg-I4's `ℚ_p ⊆ B_dR^+` (`ofLoc ∘ qpToLoc`). -/
@[instance_reducible] def algPlus : Algebra ℚ_[p] (BDeRhamPlus 𝓞_ℂ_[p] p) := (qpToPlus p).toAlgebra

attribute [local instance] algPlus

/-- `θ⁺ : B_dR^+ → ℂ_p` as a `ℚ_p`-algebra map. -/
def thetaAlg : BDeRhamPlus 𝓞_ℂ_[p] p →ₐ[ℚ_[p]] ℂ_[p] :=
  { BdrKer.Cp.thetaPlusCp p with commutes' := fun c => thetaPlusCp_qpToPlus p c }

theorem thetaAlg_apply (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    thetaAlg p y = BdrKer.Cp.thetaPlusCp p y := rfl

/-- `σ` acting on `B_dR^+`, as a `ℚ_p`-algebra map. -/
def sPlus (σ : GQp p) : BDeRhamPlus 𝓞_ℂ_[p] p →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p :=
  { DR.bdrPlusMap p (oAct p σ) with commutes' := fun c => bdrPlusMap_qpToPlus p σ c }

theorem ker_thetaAlg : RingHom.ker (thetaAlg p).toRingHom =
    span {BdrKer.ofPlus _ p (BdrKer.Cp.xi' p)} := BdrKer.Cp.ker_thetaPlusCp p

instance henselian_thetaAlg :
    HenselianRing (BDeRhamPlus 𝓞_ℂ_[p] p) (RingHom.ker (thetaAlg p).toRingHom) := by
  rw [ker_thetaAlg]
  infer_instance

theorem isUnit_of_thetaAlg_ne_zero (y : BDeRhamPlus 𝓞_ℂ_[p] p) (hy : thetaAlg p y ≠ 0) :
    IsUnit y := by
  by_contra hnu
  have hm : y ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := hnu
  rw [BdrKer.Cp.maximalIdeal_BDeRhamPlus, ← BdrKer.Cp.ker_thetaPlusCp] at hm
  exact hy (RingHom.mem_ker.mp hm)

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem exists_iotaPlus : ∃ ι₀ : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p,
    ∀ x, thetaAlg p (ι₀ x) = iotaCp p F x :=
  exists_hensel_lift (thetaAlg p) (BdrKer.Cp.thetaPlusCp_surjective p)
    (isUnit_of_thetaAlg_ne_zero p) (iotaCp p F)

/-- **`F' ⊆ B_dR^+`**: the Hensel lift of `F' ⊆ ℚ̄_p ⊆ ℂ_p` through `θ⁺`. -/
def iotaPlus : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p := (exists_iotaPlus p F).choose

theorem thetaAlg_iotaPlus (x : fieldF p F) : thetaAlg p (iotaPlus p F x) = iotaCp p F x :=
  (exists_iotaPlus p F).choose_spec x

theorem bdrPlusMap_iotaPlus (σ : GQp p) (x : fieldF p F) :
    DR.bdrPlusMap p (oAct p σ) (iotaPlus p F x) = iotaPlus p F (gammaF p F σ x) :=
  hensel_lift_natural (thetaAlg p) (iotaCp p F) (iotaPlus p F) (thetaAlg_iotaPlus p F)
    (sPlus p σ) (gammaF p F σ : fieldF p F ≃ₐ[ℚ_[p]] fieldF p F).toAlgHom (fun y => by
      change BdrKer.Cp.thetaPlusCp p (DR.bdrPlusMap p (oAct p σ) (iotaPlus p F y)) = _
      rw [thetaPlusCp_bdrPlusMap, ← thetaAlg_apply, thetaAlg_iotaPlus, cpAct_iotaCp]
      rfl) x

/-- **`F' ⊆ B_dR`**, a `ℚ_p`-algebra map for pkg-I4's `ℚ_p ⊆ B_dR`. -/
def iotaDR : fieldF p F →ₐ[ℚ_[p]] BdR p :=
  { (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp (iotaPlus p F).toRingHom with
    commutes' := fun c => by
      change algebraMap _ (BdR p) (iotaPlus p F (algebraMap ℚ_[p] _ c)) = qpToBdR p c
      rw [AlgHom.commutes]
      rfl }

theorem iotaDR_apply (x : fieldF p F) :
    iotaDR p F x = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (iotaPlus p F x) := rfl

/-- **Equivariance**: `σ(ι x) = ι(σ x)` in `B_dR`. -/
theorem bdrAct_iotaDR (σ : GQp p) (x : fieldF p F) :
    bdrAct p σ (iotaDR p F x) = iotaDR p F (gammaF p F σ x) := by
  rw [iotaDR_apply, iotaDR_apply, bdrAct, DR.bdrMap, IsLocalization.map_eq, bdrPlusMap_iotaPlus]

theorem bdrActHom_semi (σ : GQp p) (x : fieldF p F) (b : BdR p) :
    bdrActHom p σ (iotaDR p F x * b) = iotaDR p F (gammaF p F σ x) * bdrActHom p σ b := by
  rw [bdrActHom_apply, bdrActHom_apply, map_mul, bdrAct_iotaDR]

end Emb

section DeRham

variable (p : ℕ) [Fact p.Prime]

theorem ddrSpace_eq_DspAct {C : Type*} [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    {n : ℕ} (r : GQp p →* GL (Fin n) C) :
    ddrSpace p r = Dsp (bdrActHom p) (rRep p r) Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

theorem ddrSpaceOver_eq_DspAct (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    ddrSpaceOver p ρ = Dsp ((bdrActHom p).comp (gfToGqp p F)) ρ Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

/-- **G9, de Rham part.** Same hypotheses as `htMult_eq_one_of_R10`; conclusion `IsDeRham p r`. -/
theorem isDeRham_of_R10 (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r := by
  obtain ⟨hdr, -, -⟩ := hR10 p F A 2 hA
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hC : 0 < finrank ℚ_[p] C := Module.finrank_pos
  have hV : finrank ℚ_[p] (A.V p) = 4 := by
    have h := e.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h
    exact h
  set act := bdrActHom p
  have hnV : finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ) =
      finrank ℚ_[p] F * 4 := by
    rw [← ddrSpaceOver_eq_DspAct, ← hV]
    exact hdr
  have hpos : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ) := by
    rw [hnV]; positivity
  have hd := descended_finrank p F (A.galRep p) C r e he act (iotaDR p F)
    (bdrActHom_semi p F) hpos
  rw [hnV] at hd
  rw [IsDeRham, ddrSpace_eq_DspAct]
  have : finrank ℚ_[p] F * 2 * (2 * finrank ℚ_[p] C) =
      finrank ℚ_[p] F * 2 * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
    linarith [hd]
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm

/-- **G9 (N5's appendix lemma at `K = ℚ_p`, `F/ℚ_p` Galois).** From the leaf R10 and G8's output
localized at `p`: `r` is de Rham, with Hodge–Tate multiplicity `1` at the weights `0` and `−1`. -/
theorem g9_deRham (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r ∧ htMult p r 0 = 1 ∧ htMult p r (-1) = 1 :=
  ⟨isDeRham_of_R10 p hR10 F A hA C r e he, htMult_eq_one_of_R10 p hR10 F A hA C r e he⟩

/-- **G9 in the `ℚ̄_p`-valued form used by `PanBerger`** (`LocalIsDeRham`): if the coefficient
field is a finite `E ⊆ ℚ̄_p` and `ρ` is `r` viewed in `GL₂(ℚ̄_p)`, then `ρ` is de Rham. -/
theorem g9_localIsDeRham (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (r : GQp p →* GL (Fin 2) E) (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p))
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (r σ) = ρ σ)
    (e : E ⊗[ℚ_[p]] A.V p ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ v, e (GlueI3.repBaseChange E (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).2)) :
    LocalIsDeRham p 2 ρ :=
  ⟨E, inferInstance, r, hρ, isDeRham_of_R10 p hR10 F A hA E r e he⟩

end DeRham

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/G9Weights.lean

/-!
# G9 with the full weight multiset `{0, −1}`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

R10's Lean form (`PkgI4.DeRhamComparison`) fixes the Hodge–Tate multiplicities of `V_p(A)` at
the weights `0` and `−1` only. N5's conclusion "the Hodge–Tate weights of `r` are `0, −1`", in
pkg-I4's form `HasHTWeights p r {0, −1}` (every multiplicity), also needs the vanishing of the
other multiplicities of `V_p(A)`. That vanishing is part of the published theorem (the Hodge–Tate
decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g`, Faltings 1988 / Fontaine 1982 / Tate 1967,
together with Tate's `ℂ_p(i)^{G_F} = 0` for `i ≠ 0`; numbers UNVERIFIED), but not of R10's Lean
form. It is stated here as the separate Prop `DeRhamComparisonWeights` (a candidate strengthening
of R10's Lean form), and `g9_hasHTWeights` takes it as an extra hypothesis.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

/-- **R10, weight clause** (not in R10's Lean form; part of the published statement): `V_p(A)`
has no Hodge–Tate weight other than `0` and `−1`. -/
def DeRhamComparisonWeights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

section Weights

variable (p : ℕ) [Fact p.Prime]

theorem htMult_eq_zero_of_R10w (hR10w : DeRhamComparisonWeights) (F : Type) [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2))
    (w : ℤ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) : htMult p r w = 0 := by
  have hz := hR10w p F A 2 hA w hw0 hw1
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  set i := -w
  set act := cpActHom p i
  set nV := finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ)
  have hnV : finrank ℚ_[p] (htSpaceOver p (A.galRep p) i) = nV := by
    rw [htSpaceOver_eq_DspAct]
  have hdvd : finrank ℚ_[p] F ∣ nV := by
    have := finrank_dvd_Dsp_of_emb (act.comp (gfToGqp p F)) (fun σ => A.galRep p σ) Set.univ
      (iotaCp p F) (fun σ _ x b => by
        have hk : gfToGqp p F σ ∈ (gammaF p F).ker := by
          rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
        rw [MonoidHom.mem_ker] at hk
        change act (gfToGqp p F σ) _ = _
        rw [cpActHom_semi, hk]
        rfl)
    rwa [finrank_fieldF] at this
  obtain ⟨k, hk⟩ := hdvd
  have hnV0 : nV = 0 := by
    have : htMultOver p (A.galRep p) w = k := by
      rw [htMultOver, hnV, hk, Nat.mul_div_cancel_left _ hF]
    rw [hz] at this
    rw [hk, ← this, mul_zero]
  by_contra hne
  have hG : 0 < finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
    rw [htMult, htSpace_eq_DspAct] at hne
    exact Nat.pos_of_ne_zero fun h0 => hne (by rw [h0, Nat.zero_div])
  have hdes := descent_finrank act (rRep p r) (iotaCp p F) (gammaF p F) (gammaF_surjective p F)
    (cpActHom_semi p F i)
  rw [Dsp_ker_gammaF, finrank_fieldF] at hdes
  have hU : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F))
      (fun σ => rRep p r (gfToGqp p F σ)) Set.univ) := by
    change 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F))
      ((rRep p r).comp (gfToGqp p F)) Set.univ)
    rw [hdes]
    positivity
  have := overF_pos_rev (act.comp (gfToGqp p F)) (C := C) (fun σ => A.galRep p σ)
    (fun σ => rRep p r (gfToGqp p F σ)) Set.univ e (fun σ x => he σ x) hU
  change 0 < nV at this
  omega

/-- **G9 with the full weight multiset.** From R10, its weight clause
`DeRhamComparisonWeights`, and G8's local output: `r` is de Rham with Hodge–Tate weights exactly
`{0, −1}` (pkg-I4's `HasHTWeights`). -/
theorem g9_hasHTWeights (hR10 : DeRhamComparison) (hR10w : DeRhamComparisonWeights)
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r ∧ HasHTWeights p r {0, -1} := by
  obtain ⟨hdr, h0, h1⟩ := g9_deRham p hR10 F A hA C r e he
  refine ⟨hdr, fun w => ?_⟩
  by_cases hw0 : w = 0
  · subst hw0; rw [h0]; decide
  by_cases hw1 : w = -1
  · subst hw1; rw [h1]; decide
  rw [htMult_eq_zero_of_R10w p hR10w F A hA C r e he w hw0 hw1]
  simp [hw0, hw1]

/-- The `ℚ̄_p`-valued form (`LocalIsDeRham`, `LocalHasHTWeights`) for a coefficient field
`E ⊆ ℚ̄_p`. -/
theorem g9_local (hR10 : DeRhamComparison) (hR10w : DeRhamComparisonWeights)
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (r : GQp p →* GL (Fin 2) E) (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p))
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (r σ) = ρ σ)
    (e : E ⊗[ℚ_[p]] A.V p ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ v, e (GlueI3.repBaseChange E (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).2)) :
    LocalIsDeRham p 2 ρ ∧ LocalHasHTWeights p ρ {0, -1} := by
  obtain ⟨hdr, hht⟩ := g9_hasHTWeights p hR10 hR10w F A hA E r e he
  exact ⟨⟨E, inferInstance, r, hρ, hdr⟩, ⟨E, inferInstance, r, hρ, hht⟩⟩

end Weights

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Reduction.lean

/-!
# G9: `G9Glue` from three named bridge statements

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

g0-mod-galois's `G9Glue` (restated verbatim in `Statement.lean`) assumes R10
(`PkgI4.DeRhamComparison`) and T23 (`PkgI4.T23_FontaineClosure`). Its conclusion `G9Out r` needs
three facts that are neither among these hypotheses nor in Mathlib (docs/research/g9-derham.md,
findings F1-F3):

* `G9Bridge.LocalModel` (F2): base change of the abelian surface `A/K` to a finite Galois
  `F/ℚ_ℓ` (a completion of a Galois closure at a place above `ℓ`), as an abelian variety of
  pkg-I4's copy `PkgI4.I3.AbVar`, with `V_ℓ(A_F) ≅ V_ℓ(A)|G_F` (every `ℓⁿ`-torsion point of `A`
  over `F̄` is defined over `K̄`), and the decomposition group compatible with `resQ` up to
  conjugation. STANDARD (Mumford, *Abelian varieties*, §4 Thm/§6 Prop on `[n]`; UNVERIFIED
  locators).
* `G9Bridge.R10Weights` (F1): the Hodge–Tate multiplicities of `V_p(A)` vanish outside
  `{0, −1}`. This is part of the published R10 (Hodge–Tate decomposition
  `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g`, Tate 1967 / Faltings 1988, with Tate's
  `ℂ_p(j)^{G_F} = 0` for `j ≠ 0`); the Lean R10 records only the weights `0, −1`.
* `G9Bridge.BdRContainsQbar` (F3): `ℚ̄_p ⊆ B_dR` `G_{ℚ_p}`-equivariantly (Fontaine; Hensel's
  lemma in the complete DVR `B_dR^+`, whose residue field is `ℂ_p ⊇ ℚ̄_p`). STANDARD.

`g9Glue_of_bridges : LocalModel → R10Weights → BdRContainsQbar → G9Glue` is proved: the rest of
N5's argument (the finite coefficient field, the counting through `E ⊗ V ≅ r ⊕ r`, the Galois
descent from `F` to `ℚ_ℓ`) is in `CoefDescent.lean` and `LocalCore.lean`. T23 is not used.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 Module G0Galois
open scoped TensorProduct

noncomputable section

namespace G9Bridge

/-- **Bridge F2 (local model).** For an abelian surface `A` over a number field `K` and a prime
`ℓ`, there are a finite Galois extension `F/ℚ_ℓ`, an abelian surface `A'` over `F` (pkg-I4's copy
of pkg-I3's abelian varieties; `A' = A ×_K F` for an embedding `K → F`), a homomorphism
`j : G_F → G_K` (restriction along `K̄ → F̄`), a `ℚ_ℓ`-linear isomorphism `V_ℓ(A') ≅ V_ℓ(A)`
intertwining `G_F` with `G_K` through `j`, and `g ∈ G_ℚ` with
`resQ K (j σ) = g · decomp(σ) · g⁻¹` for `σ ∈ G_F` (the decomposition groups of `G_F` inside
`G_ℚ` through `K` and through `ℚ_ℓ` agree up to the choice of embeddings). -/
def LocalModel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], A.dim = 2 →
    ∃ (F : Type) (_ : Field F) (_ : Algebra ℚ_[ℓ] F) (_ : FiniteDimensional ℚ_[ℓ] F)
      (_ : IsGalois ℚ_[ℓ] F) (A' : PkgI4.I3.AbVar F)
      (j : Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup K)
      (c : A'.V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ) (g : PkgI4.GQ),
      A'.dim = 2 ∧ (∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (j σ) (c v)) ∧
      ∀ σ, resQ K (j σ) = g * PkgI4.decomp ℓ (PkgI4.gfToGqp ℓ F σ) * g⁻¹

/-- **Bridge F1 (the rest of R10).** For an abelian variety `A` over a finite `F/ℚ_p`, the
Hodge–Tate multiplicities of `V_p(A)` vanish at every weight other than `0` and `−1`. -/
def R10Weights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (w : ℤ), w ≠ 0 → w ≠ -1 → PkgI4.htMultOver p (A.galRep p) w = 0

/-- **Bridge F3.** `ℚ̄_p` embeds into `B_dR` as a `ℚ_p`-algebra, `G_{ℚ_p}`-equivariantly. -/
def BdRContainsQbar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ ι : PadicAlgCl p →ₐ[ℚ_[p]] PkgI4.BdR p,
    ∀ (σ : PkgI4.GQp p) (x : PadicAlgCl p), PkgI4.bdrAct p σ (ι x) = ι (σ x)

/-- `F' ⊆ B_dR` semilinearly, for every finite Galois `F/ℚ_p` (`F' = fieldF p F ⊆ ℚ̄_p`).
Not a bridge: implied by `BdRContainsQbar` (`fieldEmbBdR_of_bdRContainsQbar`) and proved outright
in `Final.lean` from the second run's `iotaDR` (`G9.lean`). -/
def FieldEmbBdR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F], ∃ ι' : fieldF p F →ₐ[ℚ_[p]] PkgI4.BdR p,
      ∀ (σ : PkgI4.GQp p) (x : fieldF p F), PkgI4.bdrAct p σ (ι' x) = ι' (gammaF p F σ x)

theorem fieldEmbBdR_of_bdRContainsQbar (h : BdRContainsQbar) : FieldEmbBdR := by
  intro p _ F _ _ _ _
  obtain ⟨ι, hι⟩ := h p
  exact ⟨ι.comp (fieldF p F).val, fun σ x => by
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, hι, gammaF_apply_coe]⟩

end G9Bridge

section Assembly

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem galoisRep_mat_mul (r : GaloisRep ℓ 2) (a b : PkgI4.GQ) :
    r.mat (a * b) = r.mat a * r.mat b := by
  simp [GaloisRep.mat, map_mul, Units.val_mul]

theorem galoisRep_mat_inv_mul (r : GaloisRep ℓ 2) (a : PkgI4.GQ) : r.mat a⁻¹ * r.mat a = 1 := by
  rw [← galoisRep_mat_mul, inv_mul_cancel]
  simp [GaloisRep.mat]

theorem galoisRep_mat_mul_inv (r : GaloisRep ℓ 2) (a : PkgI4.GQ) : r.mat a * r.mat a⁻¹ = 1 := by
  rw [← galoisRep_mat_mul, mul_inv_cancel]
  simp [GaloisRep.mat]

/-- Multiplication by `r(g)⁻¹` on both factors. -/
def twistPair (r : GaloisRep ℓ 2) (g : PkgI4.GQ) :
    ((Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) ≃ₗ[PadicAlgCl ℓ]
      ((Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) :=
  LinearEquiv.ofLinear
    ((Matrix.mulVecLin (r.mat g⁻¹)).prodMap (Matrix.mulVecLin (r.mat g⁻¹)))
    ((Matrix.mulVecLin (r.mat g)).prodMap (Matrix.mulVecLin (r.mat g)))
    (LinearMap.ext fun w => by
      change ((r.mat g⁻¹).mulVec ((r.mat g).mulVec w.1),
        (r.mat g⁻¹).mulVec ((r.mat g).mulVec w.2)) = w
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, galoisRep_mat_inv_mul, Matrix.one_mulVec,
        Matrix.one_mulVec])
    (LinearMap.ext fun w => by
      change ((r.mat g).mulVec ((r.mat g⁻¹).mulVec w.1),
        (r.mat g).mulVec ((r.mat g⁻¹).mulVec w.2)) = w
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, galoisRep_mat_mul_inv, Matrix.one_mulVec,
        Matrix.one_mulVec])

theorem twistPair_apply (r : GaloisRep ℓ 2) (g : PkgI4.GQ)
    (w : (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) :
    twistPair r g w = ((r.mat g⁻¹).mulVec w.1, (r.mat g⁻¹).mulVec w.2) := rfl

end Assembly

/-- **G9 (N5's Lemma `lem:de-rham-descent`), from `LocalModel`, `R10Weights` and an
embedding `F' ⊆ B_dR`.** -/
theorem g9Glue_of_fieldEmb (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights)
    (hB : G9Bridge.FieldEmbBdR) : G9Glue := by
  intro hR10 _hT23 K _ _ A ℓ _ r e hdim hint
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ := hLM K A ℓ hdim
  obtain ⟨hdR, h0, h1⟩ := hR10 ℓ F A' 2 (by rw [hdim']; rfl)
  obtain ⟨ιB, hιB⟩ := hB ℓ F
  let cb : PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A'.V ℓ ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A.V ℓ :=
    LinearEquiv.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ c
  let e' := (cb.trans e).trans (twistPair r g)
  have hcb : ∀ σ x, cb ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      tate A ℓ (j σ) (cb x) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      change cb (a ⊗ₜ (A'.galRep ℓ σ v)) = (A.galRep ℓ (j σ)).baseChange (PadicAlgCl ℓ) (cb (a ⊗ₜ v))
      simp only [cb, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, hc]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have he' : ∀ σ x, e' ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      ((r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec (e' x).1,
        (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec
          (e' x).2) := by
    intro σ x
    have hR : (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) := rfl
    have hconj : r.mat g⁻¹ * r.mat (resQ K (j σ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) * r.mat g⁻¹ := by
      rw [hg σ, galoisRep_mat_mul, galoisRep_mat_mul, ← mul_assoc, ← mul_assoc,
        galoisRep_mat_inv_mul, one_mul]
    simp only [e', LinearEquiv.trans_apply, hcb, twistPair_apply, hint _ (cb x), hR,
      Matrix.mulVec_mulVec, hconj]
  obtain ⟨E, hE, ρE, eE, hmap, he⟩ :=
    coef_descent ℓ F (A'.galRep ℓ) (r.restrictLocal ℓ) e' he'
  have hw : ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver ℓ (A'.galRep ℓ) w = 0 :=
    fun w hw0 hw1 => hW ℓ F A' w hw0 hw1
  exact ⟨⟨E, hE, ρE, hmap, core_dR_F ℓ F ιB hιB (A'.galRep ℓ) ρE eE he hdR⟩,
    ⟨E, hE, ρE, hmap, core_ht ℓ F (A'.galRep ℓ) ρE eE he h0 h1 hw⟩⟩

/-- **G9 from the three bridges.** -/
theorem g9Glue_of_bridges (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights)
    (hB : G9Bridge.BdRContainsQbar) : G9Glue :=
  g9Glue_of_fieldEmb hLM hW (G9Bridge.fieldEmbBdR_of_bdRContainsQbar hB)

end

end ZInQ.Contrib.G9


-- ===== ZInQKernel/Contrib/G9/Final.lean

/-!
# G9: `G9Glue` from two bridge statements

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

The embedding `F' ⊆ B_dR` (`G9Bridge.FieldEmbBdR`) is proved by the second run of this task
(`iotaDR`, `bdrAct_iotaDR` in `G9.lean`: Hensel's lemma in `B_dR^+` through bdr-kertheta's
`θ⁺ : B_dR^+ → ℂ_p`, `KerTheta.lean`, `HenselEmb.lean`, `BdREmb.lean`). Hence

`g9Glue_of_localModel : G9Bridge.LocalModel → G9Bridge.R10Weights → G9Glue`

with the standard axioms only. The two remaining hypotheses are findings F2 (base change of
`A/K` to a local field with its Tate module) and F1 (Hodge–Tate multiplicities outside `{0, −1}`
vanish, a clause of the published R10 missing from its Lean form).
-/

namespace ZInQ.Contrib.G9

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 G0Galois

theorem fieldEmbBdR : G9Bridge.FieldEmbBdR := by
  intro p _ F _ _ _ _
  exact ⟨iotaDR p F, bdrAct_iotaDR p F⟩

/-- **G9 (N5's Lemma `lem:de-rham-descent`, g0-mod-galois's `G9Glue`) from F2 and F1.** -/
theorem g9Glue_of_localModel (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights) :
    G9Glue :=
  g9Glue_of_fieldEmb hLM hW fieldEmbBdR

end ZInQ.Contrib.G9


-- ===== ZInQKernel/Contrib/G9/LocalModel.lean

/-!
# G9: the local model, reduced to base change of abelian varieties

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

`G9Bridge.LocalModel` (bridge F2 of `Reduction.lean`) mixes Galois theory with algebraic
geometry. Here the Galois theory is proved, and what remains is one statement about abelian
varieties, `G9Bridge.AbVarBaseChange`: for a field embedding `i : K → L` (characteristic 0) and an
abelian variety `A/K`, there is an abelian variety `A'/L` (pkg-I4's copy of pkg-I3's `AbVar`;
`A' = A ×_K L`) with `dim A' = dim A` and `V_ℓ(A') ≅ V_ℓ(A)` intertwining `G_L` with `G_K` through
Mathlib's `Field.absoluteGaloisGroup.map i`. STANDARD (base change of abelian varieties;
`A[ℓⁿ]` is finite étale over `K` in characteristic `≠ ℓ`, so its points over `K̄` and over `L̄`
agree: Mumford, *Abelian varieties*, §4 and §6, locators UNVERIFIED; dimension is invariant under
field extension, EGA IV 4.1.4, UNVERIFIED).

* `localModel_of_abVarBaseChange : AbVarBaseChange → LocalModel`: `K` embeds into a finite
  Galois `F/ℚ_ℓ` inside `ℚ̄_ℓ` (the normal closure of the `ℚ_ℓ`-span of the image of `K`), and
  the two maps `G_F → G_ℚ` (through `K` and through `ℚ_ℓ`) differ by conjugation, because any two
  embeddings `ℚ̄ → F̄` differ by an automorphism of `ℚ̄`.
* `g9Glue_of_abVarBaseChange : AbVarBaseChange → R10Weights → G9Glue`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 G0Galois Module

noncomputable section

namespace G9Bridge

/-- **Bridge F2' (base change of abelian varieties with their Tate modules).** -/
def AbVarBaseChange : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : PkgI3.AbVar K) (L : Type) [Field L] (i : K →+* L)
    (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ (A' : PkgI4.I3.AbVar L) (c : A'.V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ), A'.dim = A.dim ∧
      ∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)

end G9Bridge

section Conj

/-- An element of `G_K` as an automorphism of `K̄`. -/
abbrev galK {K : Type*} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `Field.absoluteGaloisGroup.map f` is restriction along an embedding `K̄ → L̄`. -/
theorem exists_emb_map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    ∃ κ : AlgebraicClosure K →+* AlgebraicClosure L,
      ∀ (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K),
        κ (galK (Field.absoluteGaloisGroup.map f σ) x) = galK σ (κ x) := by
  letI : Algebra K L := f.toAlgebra
  let g0 : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := g0.toAlgebra
  exact ⟨g0.toRingHom, fun σ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) (AlgebraicClosure K) x⟩

/-- Two embeddings of `k̄` into a field over `k` differ by an automorphism of `k̄`. -/
theorem exists_aut_comp {k M : Type*} [Field k] [Field M] [Algebra k M]
    (α1 α2 : AlgebraicClosure k →ₐ[k] M) :
    ∃ δ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, ∀ x, α2 x = α1 (δ x) := by
  letI : Algebra (AlgebraicClosure k) M := α1.toRingHom.toAlgebra
  haveI : IsScalarTower k (AlgebraicClosure k) M :=
    IsScalarTower.of_algebraMap_eq (fun c => (α1.commutes c).symm)
  let δ0 : AlgebraicClosure k →ₐ[k] AlgebraicClosure k :=
    α2.restrictNormal (K₁ := AlgebraicClosure k) (AlgebraicClosure k)
  have h : ∀ x, α1 (δ0 x) = α2 x := fun x =>
    AlgHom.restrictNormal_commutes (K₁ := AlgebraicClosure k) α2 (AlgebraicClosure k) x
  exact ⟨AlgEquiv.ofBijective δ0 (Algebra.IsAlgebraic.algHom_bijective δ0),
    fun x => (h x).symm⟩

/-- Restrictions along two embeddings `ℚ̄ → F̄` are conjugate. -/
theorem conj_of_two_embs {M : Type*} [Field M] [CharZero M] (G : Type*) [Group G] (act : G →* (M ≃+* M))
    (α1 α2 : AlgebraicClosure ℚ →+* M) (τ1 τ2 : G → PkgI4.GQ)
    (h1 : ∀ σ x, α1 (τ1 σ x) = act σ (α1 x)) (h2 : ∀ σ x, α2 (τ2 σ x) = act σ (α2 x)) :
    ∃ g : PkgI4.GQ, ∀ σ, τ1 σ = g * τ2 σ * g⁻¹ := by
  obtain ⟨δ, hδ⟩ := exists_aut_comp (k := ℚ) α1.toRatAlgHom α2.toRatAlgHom
  have hδ' : ∀ x, α2 x = α1 (δ x) := hδ
  refine ⟨δ, fun σ => ?_⟩
  apply AlgEquiv.ext
  intro x
  apply α1.injective
  rw [h1]
  change act σ (α1 x) = α1 (δ (τ2 σ (δ⁻¹ x)))
  rw [← hδ', h2, hδ']
  congr 2
  exact (AlgEquiv.apply_symm_apply δ x).symm

end Conj

section Model

variable (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]

/-- `K → ℚ̄_ℓ`. -/
def psiK : K →ₐ[ℚ] PadicAlgCl ℓ := IsAlgClosed.lift

/-- The `ℚ_ℓ`-span of the image of a `ℚ`-basis of `K`. -/
def spanK : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.adjoin ℚ_[ℓ] (Set.range fun k => psiK K ℓ (Module.finBasis ℚ K k))

instance : FiniteDimensional ℚ_[ℓ] (spanK K ℓ) :=
  have : Finite (Set.range fun k => psiK K ℓ (Module.finBasis ℚ K k)) := Set.finite_range _
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem psiK_mem (x : K) : psiK K ℓ x ∈ spanK K ℓ := by
  rw [← (Module.finBasis ℚ K).sum_repr x, map_sum]
  refine IntermediateField.sum_mem _ fun k _ => ?_
  rw [Algebra.smul_def, map_mul, AlgHom.commutes]
  refine IntermediateField.mul_mem _ ?_ (IntermediateField.subset_adjoin _ _ ⟨k, rfl⟩)
  rw [eq_ratCast]
  exact SubfieldClass.ratCast_mem _ _

/-- The local field: the normal closure of `spanK` in `ℚ̄_ℓ`. -/
def locF : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.normalClosure ℚ_[ℓ] (spanK K ℓ) (PadicAlgCl ℓ)

instance : FiniteDimensional ℚ_[ℓ] (locF K ℓ) := by
  unfold locF; infer_instance

instance : IsGalois ℚ_[ℓ] (locF K ℓ) := by
  unfold locF
  exact { }

/-- `K → F`. -/
def iK : K →+* locF K ℓ :=
  (psiK K ℓ).toRingHom.codRestrict (locF K ℓ) fun x =>
    IntermediateField.le_normalClosure (spanK K ℓ) (psiK_mem K ℓ x)

end Model

/-- `decomp ℓ` is restriction along an embedding `ℚ̄ → ℚ̄_ℓ`. -/
theorem exists_emb_decomp (ℓ : ℕ) [Fact ℓ.Prime] : ∃ κ : AlgebraicClosure ℚ →+* PadicAlgCl ℓ,
    ∀ (τ : GQp ℓ) (x : AlgebraicClosure ℚ), κ (decomp ℓ τ x) = τ (κ x) := by
  let g0 : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[ℓ] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[ℓ]) := g0.toAlgebra
  exact ⟨g0.toRingHom, fun τ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars ℚ τ) (AlgebraicClosure ℚ) x⟩

/-- `σ ↦ σ` as ring automorphisms. -/
def galRingEquivHom (F : Type*) [Field F] :
    Field.absoluteGaloisGroup F →* (AlgebraicClosure F ≃+* AlgebraicClosure F) where
  toFun σ := (galK σ).toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

set_option maxHeartbeats 2000000 in
/-- **The local model from base change of abelian varieties.** -/
theorem localModel_of_abVarBaseChange (h : G9Bridge.AbVarBaseChange) : G9Bridge.LocalModel := by
  intro K _ _ A ℓ _ hdim
  obtain ⟨A', c, hdim', hc⟩ := h K A (locF K ℓ) (iK K ℓ) ℓ
  obtain ⟨κ1, h1⟩ := exists_emb_map (algebraMap ℚ K)
  obtain ⟨κ2, h2⟩ := exists_emb_map (iK K ℓ)
  obtain ⟨κ3, h3⟩ := exists_emb_decomp ℓ
  let j : Field.absoluteGaloisGroup (locF K ℓ) →* Field.absoluteGaloisGroup K :=
    (Field.absoluteGaloisGroup.map (iK K ℓ) : _ →* _)
  have e1 : ∀ σ x, (κ2.comp κ1) (resQ K (j σ) x) =
      galRingEquivHom (locF K ℓ) σ ((κ2.comp κ1) x) := by
    intro σ x
    change κ2 (κ1 (galK (Field.absoluteGaloisGroup.map (algebraMap ℚ K) (j σ)) x)) =
      galK σ (κ2 (κ1 x))
    rw [h1]
    exact h2 σ (κ1 x)
  have e2 : ∀ σ x, ((embF ℓ (locF K ℓ)).comp κ3) (decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) x) =
      galRingEquivHom (locF K ℓ) σ (((embF ℓ (locF K ℓ)).comp κ3) x) := by
    intro σ x
    change embF ℓ (locF K ℓ) (κ3 (decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) x)) =
      galF (locF K ℓ) σ (embF ℓ (locF K ℓ) (κ3 x))
    rw [h3]
    exact embF_gfToGqp ℓ (locF K ℓ) σ (κ3 x)
  obtain ⟨g, hg⟩ := conj_of_two_embs (M := AlgebraicClosure (locF K ℓ))
    (Field.absoluteGaloisGroup (locF K ℓ)) (galRingEquivHom (locF K ℓ))
    (κ2.comp κ1) ((embF ℓ (locF K ℓ)).comp κ3) (fun σ => resQ K (j σ))
    (fun σ => decomp ℓ (gfToGqp ℓ (locF K ℓ) σ)) e1 e2
  have i3 : FiniteDimensional ℚ_[ℓ] (locF K ℓ) := inferInstance
  have i4 : IsGalois ℚ_[ℓ] (locF K ℓ) := inferInstance
  have hc' : ∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (j σ) (c v) := hc
  have hg' : ∀ σ, resQ K (j σ) = g * decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) * g⁻¹ := hg
  have hd2 : A'.dim = 2 := hdim'.trans hdim
  exact ⟨locF K ℓ, inferInstance, inferInstance, i3, i4, A', j, c, g, hd2, hc', hg'⟩

/-- **G9 from base change of abelian varieties and the weight clause of R10.** -/
theorem g9Glue_of_abVarBaseChange (hBC : G9Bridge.AbVarBaseChange) (hW : G9Bridge.R10Weights) :
    G9Glue :=
  g9Glue_of_localModel (localModel_of_abVarBaseChange hBC) hW

end

end ZInQ.Contrib.G9


-- ===== ZInQKernel/Contrib/G9/Partial.lean

/-!
# G9 without the weight clause: what R10's Lean form gives alone

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

`g9_partial`: from `G9Bridge.AbVarBaseChange` and R10 (`PkgI4.DeRhamComparison`) alone, i.e.
without `G9Bridge.R10Weights`, the data of `G9Glue` give: `r|G_{ℚ_ℓ}` is de Rham
(`LocalIsDeRham`), and over the same finite coefficient field its Hodge–Tate multiplicities at
`0` and at `−1` are `1`. What is missing for `HasHTWeightsAtSelf ℓ {0, −1}` is exactly the
vanishing of the multiplicities at the other weights (finding F1 of docs/research/g9-derham.md).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.HDec.PkgI4 ZInQ.Contrib.G9.PkgI4 G0Galois Module
open scoped TensorProduct

noncomputable section

section Mult

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [IsGalois ℚ_[p] F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]

/-- One Hodge–Tate multiplicity: `htMultOver ρ w = 2M ⇒ htMult ρE w = M`. -/
theorem core_htMult (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (w : ℤ) (M : ℕ) (hM : htMultOver p ρ w = 2 * M) : htMult p ρE w = M := by
  have hd : 0 < finrank ℚ_[p] E := Module.finrank_pos
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  obtain ⟨hc, hdvd⟩ := core_count p F (htAct p (-w)) (cpEmb p) (htAct_semi p (-w)) ρ ρE eE he
  rw [htMultOver, htSpaceOver_eq_DspRep] at hM
  rw [htMult, htSpace_eq_DspMat]
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Nat.mul_div_cancel_left _ hf] at hM
  rw [hk, hM] at hc
  have h1 : finrank ℚ_[p] F * (finrank ℚ_[p] E * (2 * M)) =
      finrank ℚ_[p] F * (2 * finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ)) := by
    calc finrank ℚ_[p] F * (finrank ℚ_[p] E * (2 * M))
        = finrank ℚ_[p] E * (finrank ℚ_[p] F * (2 * M)) := by ring
      _ = _ := hc
      _ = _ := by ring
  have h2 := Nat.eq_of_mul_eq_mul_left hf h1
  have h3 : finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ) =
      finrank ℚ_[p] E * M := by
    rw [mul_left_comm] at h2; omega
  rw [h3, Nat.mul_div_cancel_left _ hd]

end Mult

/-- **G9 from base change and R10 alone** (no weight clause): de Rham, and multiplicity `1` at
the weights `0` and `−1`. -/
theorem g9_partial (hBC : G9Bridge.AbVarBaseChange) (hR10 : PkgI4.DeRhamComparison)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hdim : A.dim = 2) (hint : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) :
    PkgI4.LocalIsDeRham ℓ 2 (r.restrictLocal ℓ) ∧
      ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
        (ρE : GQp ℓ →* GL (Fin 2) E),
        (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl ℓ)) (ρE σ) =
          r.restrictLocal ℓ σ) ∧
        htMult ℓ ρE 0 = 1 ∧ htMult ℓ ρE (-1) = 1 := by
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ :=
    localModel_of_abVarBaseChange hBC K A ℓ hdim
  obtain ⟨hdR, h0, h1⟩ := hR10 ℓ F A' 2 (by rw [hdim']; rfl)
  obtain ⟨ιB, hιB⟩ := fieldEmbBdR ℓ F
  let cb : PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A'.V ℓ ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A.V ℓ :=
    LinearEquiv.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ c
  let e' := (cb.trans e).trans (twistPair r g)
  have hcb : ∀ σ x, cb ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      tate A ℓ (j σ) (cb x) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      change cb (a ⊗ₜ (A'.galRep ℓ σ v)) = (A.galRep ℓ (j σ)).baseChange (PadicAlgCl ℓ) (cb (a ⊗ₜ v))
      simp only [cb, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, hc]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have he' : ∀ σ x, e' ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      ((r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec (e' x).1,
        (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec
          (e' x).2) := by
    intro σ x
    have hR : (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) := rfl
    have hconj : r.mat g⁻¹ * r.mat (resQ K (j σ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) * r.mat g⁻¹ := by
      rw [hg σ, galoisRep_mat_mul, galoisRep_mat_mul, ← mul_assoc, ← mul_assoc,
        galoisRep_mat_inv_mul, one_mul]
    simp only [e', LinearEquiv.trans_apply, hcb, twistPair_apply, hint _ (cb x), hR,
      Matrix.mulVec_mulVec, hconj]
  obtain ⟨E, hE, ρE, eE, hmap, he⟩ :=
    coef_descent ℓ F (A'.galRep ℓ) (r.restrictLocal ℓ) e' he'
  exact ⟨⟨E, hE, ρE, hmap, core_dR_F ℓ F ιB hιB (A'.galRep ℓ) ρE eE he hdR⟩,
    E, hE, ρE, hmap, core_htMult ℓ F (A'.galRep ℓ) ρE eE he 0 1 (by rw [h0]),
    core_htMult ℓ F (A'.galRep ℓ) ρE eE he (-1) 1 (by rw [h1])⟩

end

end ZInQ.Contrib.G9

