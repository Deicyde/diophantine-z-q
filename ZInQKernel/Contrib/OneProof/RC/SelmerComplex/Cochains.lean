import Mathlib

/-!
# Lane RC26: continuous inhomogeneous cochains in all degrees

Manuscript `diophantine_zq.tex`, §8, tex 2761–2830 and 3400–3500. The Selmer complexes of the text,
```
C_U = Cone(RΓ(G_{K,S}, M_i) ⊕ ⊕_{v∈S} U_v → ⊕_{v∈S} RΓ(K_v, M_i))[−1]          (4.3)
```
(tex 3455–3463), are built, following Nekovář (*Selmer complexes*, Astérisque 310, 2006, cited at
tex 3455 and 3829–3835), from the complexes `RΓ(G, M) = C^•_cont(G, M)` of continuous
inhomogeneous cochains of a profinite group `G` with values in a discrete module `M`.

This file constructs these complexes in **all degrees**, as Mathlib cochain complexes:

* `SubCx K`: a family of submodules of the terms of a complex `K` of `k`-modules stable under the
  differential; `SubCx.toCx` is the subcomplex and `SubCx.ι` its inclusion (a cochain map),
  `SubCx.map` the restriction of a cochain map preserving the submodules.
* `contCochain k G M n`: the continuous `n`-cochains, the submodule of continuous functions in the
  term `Gⁿ → M` of Mathlib's complex of inhomogeneous cochains
  `groupCohomology.inhomogeneousCochains (Rep.ofDistribMulAction k G M)`.
  (For a discrete module `M`, continuous means locally constant.)
* `contCochains k G M`: the complex `C^•_cont(G, M)` — the subcomplex of Mathlib's inhomogeneous
  cochains formed by the continuous cochains (the differential preserves continuity:
  `continuous_d`). `contCochainsι` is its inclusion into Mathlib's complex.
* `contCohomology k G M n`: its cohomology `Hⁿ_cont(G, M)`.
* `contCochainsMap φ f hf`: the cochain map `C^•_cont(G, M) → C^•_cont(H, N)`,
  `c ↦ f ∘ c ∘ φⁿ`, attached to a *compatible pair*: a continuous homomorphism `φ : H →ₜ* G` and a
  continuous `k`-linear map `f : M → N` with `f (φ h • m) = h • f m`. Restriction to a subgroup or
  along a decomposition map (`f = id`) and inflation along a quotient map (`f` the inclusion of the
  invariants) are the instances used in the text (localization maps in (4.3); inflation
  `G_{K,S∪q} → G_{K,S}` in the support change, tex 3470–3499). It is the restriction of Mathlib's
  `groupCohomology.cochainsMap`, and compatible with composition and identities.

Sanity checks (PROVED): for a discrete group `G` every cochain is continuous, the inclusion is an
isomorphism of complexes (`contCochainsι_isIso_of_discrete`), and `Hⁿ_cont(G, M)` is Mathlib's
`groupCohomology` (`contCohomologyIsoOfDiscrete`). The comparison with Tau Ceti's explicit
continuous `H⁰`, `H¹`, `H²` (and through it with Mathlib's homogeneous `continuousCohomology` in
degrees one and two) is in `TauCetiComparison.lean`.

References for the definitions: Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.,
Ch. I §2 (the inhomogeneous complex of continuous cochains of a profinite group with values in a
discrete module, and its functoriality in compatible pairs); Nekovář, *Selmer complexes*, §3.4
(continuous cochains `C^•_cont(G, M)`; locator as cited, UNVERIFIED).

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory

universe u

/-! ### Subcomplexes of cochain complexes of modules -/

section Sub

variable {k : Type u} [CommRing k]

/-- A family of submodules of the terms of a cochain complex `K` of `k`-modules, stable under the
differential. -/
structure SubCx (K : CochainComplex (ModuleCat.{u} k) ℕ) where
  /-- The submodule in degree `n`. -/
  P : ∀ n, Submodule k (K.X n)
  /-- Stability under the differential. -/
  d_mem : ∀ (n : ℕ) (x : K.X n), x ∈ P n → (K.d n (n + 1)).hom x ∈ P (n + 1)

variable {K L N : CochainComplex (ModuleCat.{u} k) ℕ}

/-- The differential restricted to the submodules. -/
def SubCx.dRes (P : SubCx K) (n : ℕ) : P.P n →ₗ[k] P.P (n + 1) :=
  (K.d n (n + 1)).hom.restrict (fun x hx => P.d_mem n x hx)

@[simp]
theorem SubCx.dRes_apply_coe (P : SubCx K) (n : ℕ) (x : P.P n) :
    ((P.dRes n x : P.P (n + 1)) : K.X (n + 1)) = (K.d n (n + 1)).hom x :=
  rfl

/-- **The subcomplex** with terms the submodules `P n` and the restricted differentials. -/
def SubCx.toCx (P : SubCx K) : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (P.P n)) (fun n => ModuleCat.ofHom (P.dRes n))
    (fun n => by
      ext x
      have h : ∀ y : K.X n, (K.d (n + 1) (n + 1 + 1)).hom ((K.d n (n + 1)).hom y) = 0 :=
        fun y => by
          rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
          rfl
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        SubCx.dRes_apply_coe, ModuleCat.hom_zero, LinearMap.zero_apply, ZeroMemClass.coe_zero]
      exact h _)

/-- Read an element of a term of the subcomplex as an element of the submodule. -/
abbrev SubCx.el (P : SubCx K) {n : ℕ} (x : P.toCx.X n) : P.P n := x

/-- Read an element of the submodule as an element of a term of the subcomplex. -/
abbrev SubCx.ofSub (P : SubCx K) {n : ℕ} (x : P.P n) : P.toCx.X n := x

theorem SubCx.toCx_X (P : SubCx K) (n : ℕ) : P.toCx.X n = ModuleCat.of k (P.P n) :=
  rfl

theorem SubCx.toCx_d (P : SubCx K) (n : ℕ) :
    P.toCx.d n (n + 1) = ModuleCat.ofHom (P.dRes n) := by
  simp [SubCx.toCx]

/-- The differential of the subcomplex is the restriction of the differential. -/
theorem SubCx.toCx_d_apply (P : SubCx K) (n : ℕ) (x : P.toCx.X n) :
    ((P.el ((P.toCx.d n (n + 1)).hom x) : P.P (n + 1)) : K.X (n + 1)) =
      (K.d n (n + 1)).hom (P.el x) := by
  rw [SubCx.toCx_d]
  rfl

/-- **The inclusion of the subcomplex**, a cochain map. -/
def SubCx.ι (P : SubCx K) : P.toCx ⟶ K where
  f n := ModuleCat.ofHom (P.P n).subtype
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    ext x
    change (K.d i (i + 1)).hom (P.el x) = ((P.el ((P.toCx.d i (i + 1)).hom x) : P.P (i + 1)) :
      K.X (i + 1))
    rw [SubCx.toCx_d_apply]

@[simp]
theorem SubCx.ι_f_apply (P : SubCx K) (n : ℕ) (x : P.toCx.X n) :
    (P.ι.f n).hom x = (P.el x : K.X n) :=
  rfl

/-- The inclusion is injective in every degree. -/
theorem SubCx.ι_f_injective (P : SubCx K) (n : ℕ) : Function.Injective (P.ι.f n).hom :=
  Subtype.val_injective

/-- **The restriction of a cochain map** `φ : K ⟶ L` carrying the submodules `P` into `Q`. -/
def SubCx.map (P : SubCx K) (Q : SubCx L) (φ : K ⟶ L)
    (hφ : ∀ (n : ℕ) (x : K.X n), x ∈ P.P n → (φ.f n).hom x ∈ Q.P n) : P.toCx ⟶ Q.toCx where
  f n := ModuleCat.ofHom ((φ.f n).hom.restrict (fun x hx => hφ n x hx))
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    ext x
    apply Subtype.ext
    have h := congrArg (fun ψ => ψ.hom (P.el x : K.X i)) (φ.comm i (i + 1))
    have e1 := SubCx.toCx_d_apply P i x
    have e2 := SubCx.toCx_d_apply Q i (Q.ofSub ⟨(φ.f i).hom (P.el x), hφ i _ (P.el x).2⟩)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    change ((Q.el ((Q.toCx.d i (i + 1)).hom (Q.ofSub ⟨(φ.f i).hom (P.el x), hφ i _ (P.el x).2⟩)) :
        Q.P (i + 1)) : L.X (i + 1)) =
      (φ.f (i + 1)).hom ((P.el ((P.toCx.d i (i + 1)).hom x) : P.P (i + 1)) : K.X (i + 1))
    rw [e1, e2]
    exact h

@[simp]
theorem SubCx.map_f_apply_coe (P : SubCx K) (Q : SubCx L) (φ : K ⟶ L)
    (hφ : ∀ (n : ℕ) (x : K.X n), x ∈ P.P n → (φ.f n).hom x ∈ Q.P n) (n : ℕ) (x : P.toCx.X n) :
    ((Q.el (((P.map Q φ hφ).f n).hom x) : Q.P n) : L.X n) = (φ.f n).hom (P.el x) :=
  rfl

/-- The restricted map commutes with the inclusions. -/
@[reassoc]
theorem SubCx.map_ι (P : SubCx K) (Q : SubCx L) (φ : K ⟶ L)
    (hφ : ∀ (n : ℕ) (x : K.X n), x ∈ P.P n → (φ.f n).hom x ∈ Q.P n) :
    P.map Q φ hφ ≫ Q.ι = P.ι ≫ φ := by
  ext n x
  rfl

/-- Restriction of the identity is the identity. -/
theorem SubCx.map_id (P : SubCx K) :
    P.map P (𝟙 K) (fun _ _ hx => hx) = 𝟙 P.toCx := by
  ext n x
  rfl

/-- Restriction is compatible with composition. -/
theorem SubCx.map_comp (P : SubCx K) (Q : SubCx L) (R : SubCx N) (φ : K ⟶ L) (ψ : L ⟶ N)
    (hφ : ∀ (n : ℕ) (x : K.X n), x ∈ P.P n → (φ.f n).hom x ∈ Q.P n)
    (hψ : ∀ (n : ℕ) (x : L.X n), x ∈ Q.P n → (ψ.f n).hom x ∈ R.P n) :
    P.map R (φ ≫ ψ) (fun n x hx => hψ n _ (hφ n x hx)) = P.map Q φ hφ ≫ Q.map R ψ hψ := by
  ext n x
  rfl

/-- The whole complex as a subcomplex. -/
def SubCx.top (K : CochainComplex (ModuleCat.{u} k) ℕ) : SubCx K where
  P _ := ⊤
  d_mem _ _ _ := Submodule.mem_top

/-- If the submodules are everything, the inclusion is an isomorphism of complexes. -/
theorem SubCx.ι_isIso_of_eq_top (P : SubCx K) (h : ∀ n, P.P n = ⊤) : IsIso P.ι := by
  have : ∀ n, IsIso (P.ι.f n) := fun n => by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨Subtype.val_injective, fun y => ⟨⟨y, by rw [h n]; trivial⟩, rfl⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components P.ι

end Sub

/-! ### Continuous inhomogeneous cochains -/

/-- A discrete space has continuous constant scalar multiplications (every map out of a discrete
space is continuous). Used so that the standing hypotheses below are automatic for a discrete
module. -/
instance (priority := 100) continuousConstSMul_of_discreteTopology {R X : Type*} [SMul R X]
    [TopologicalSpace X] [DiscreteTopology X] : ContinuousConstSMul R X :=
  ⟨fun _ => continuous_of_discreteTopology⟩

section Cochains

variable (k : Type u) [CommRing k] (G : Type u) [Group G]
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

/-- The `k`-linear representation of `G` on the `G`-module `M` (Mathlib's
`Rep.ofDistribMulAction`), whose inhomogeneous cochains are the functions `Gⁿ → M`. -/
abbrev rep : Rep.{u} k G := Rep.ofDistribMulAction k G M

/-- Read an inhomogeneous cochain of `rep k G M` as a function `Gⁿ → M`. -/
abbrev asFun {n : ℕ} (f : (groupCohomology.inhomogeneousCochains (rep k G M)).X n) :
    (Fin n → G) → M := f

section Compat

variable {H : Type u} [Group H]
  {N : Type u} [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
  {k G M}

/-- The morphism of Mathlib representations `Res_φ(M) ⟶ N` attached to a compatible pair
`(φ, f)`: `f (φ h • m) = h • f m`. -/
def compatHom (φ : H →* G) (f : M →ₗ[k] N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    Rep.res φ (rep k G M) ⟶ rep k H N :=
  Rep.ofHom (σ := Representation.ofDistribMulAction k H N)
    ⟨f, fun h => by ext m; exact hf h m⟩

/-- The cochain map on all inhomogeneous cochains attached to a compatible pair: Mathlib's
`groupCohomology.cochainsMap`, `c ↦ f ∘ c ∘ φⁿ`. -/
abbrev compatCochainsMap (φ : H →* G) (f : M →ₗ[k] N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    groupCohomology.inhomogeneousCochains (rep k G M) ⟶
      groupCohomology.inhomogeneousCochains (rep k H N) :=
  groupCohomology.cochainsMap φ (compatHom φ f hf)

theorem compatCochainsMap_apply (φ : H →* G) (f : M →ₗ[k] N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ)
    (c : (groupCohomology.inhomogeneousCochains (rep k G M)).X n) (x : Fin n → H) :
    asFun k H N (((compatCochainsMap φ f hf).f n).hom c) x = f (asFun k G M c (φ ∘ x)) :=
  rfl

end Compat

variable [TopologicalSpace G] [TopologicalSpace M]

/-- **The continuous `n`-cochains** `Cⁿ_cont(G, M)`: the continuous elements of the term
`Gⁿ → M` of Mathlib's inhomogeneous cochain complex (product topology on `Gⁿ = Fin n → G`). -/
def contCochain [ContinuousAdd M] [ContinuousConstSMul k M] (n : ℕ) :
    Submodule k ((groupCohomology.inhomogeneousCochains (rep k G M)).X n) where
  carrier := {f | Continuous (asFun k G M f)}
  add_mem' hf hg := hf.add hg
  zero_mem' := continuous_const
  smul_mem' c _ hf := hf.const_smul c

variable {k G M}

theorem mem_contCochain [ContinuousAdd M] [ContinuousConstSMul k M] {n : ℕ}
    {f : (groupCohomology.inhomogeneousCochains (rep k G M)).X n} :
    f ∈ contCochain k G M n ↔ Continuous (asFun k G M f) :=
  Iff.rfl

/-- `Fin.contractNth j (· * ·)` is continuous on `Gⁿ⁺¹`. -/
theorem continuous_contractNth [ContinuousMul G] {n : ℕ} (j : Fin (n + 1)) :
    Continuous (fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g) := by
  refine continuous_pi fun i => ?_
  simp only [Fin.contractNth]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).mul (continuous_apply _)
  · exact continuous_apply _

/-- **The inhomogeneous differential preserves continuity.** For a topological group `G`, a
topological module `M` with continuous addition and scalar multiplications and a jointly continuous
action `G × M → M` (for a discrete `M`: a discrete `G`-module in the sense of
Neukirch–Schmidt–Wingberg I §2), the differential of a continuous cochain is continuous. -/
theorem continuous_d [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M]
    [ContinuousSMul G M] (n : ℕ) {f : (groupCohomology.inhomogeneousCochains (rep k G M)).X n}
    (hf : Continuous (asFun k G M f)) :
    Continuous (asFun k G M
      (((groupCohomology.inhomogeneousCochains (rep k G M)).d n (n + 1)).hom f)) := by
  rw [groupCohomology.inhomogeneousCochains.d_def]
  have e : asFun k G M ((inhomogeneousCochains.d (rep k G M) n).hom f) =
      fun g => g 0 • asFun k G M f (fun i => g i.succ) + ∑ j : Fin (n + 1),
        (-1 : k) ^ ((j : ℕ) + 1) • asFun k G M f (Fin.contractNth j (· * ·) g) := rfl
  rw [e]
  refine Continuous.add ?_ ?_
  · exact (continuous_apply 0).smul
      (hf.comp (continuous_pi fun i => continuous_apply i.succ))
  · exact continuous_finsetSum _ fun j _ => (hf.comp (continuous_contractNth j)).const_smul _

variable (k G M)

/-- The continuous cochains form a subcomplex of Mathlib's inhomogeneous cochain complex. -/
def contSubCx [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M] :
    SubCx (groupCohomology.inhomogeneousCochains (rep k G M)) where
  P := contCochain k G M
  d_mem n _ hf := continuous_d n hf

/-- **The complex `C^•_cont(G, M)` of continuous inhomogeneous cochains**, in all degrees: the
subcomplex of Mathlib's `groupCohomology.inhomogeneousCochains (Rep.ofDistribMulAction k G M)`
formed by the continuous cochains `Gⁿ → M`. This is `RΓ(G, M)` of the text (tex 3455–3463) for a
profinite `G` and a discrete `M` (Neukirch–Schmidt–Wingberg I §2; Nekovář §3.4). -/
abbrev contCochains [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M]
    [ContinuousSMul G M] : CochainComplex (ModuleCat.{u} k) ℕ :=
  (contSubCx k G M).toCx

/-- The inclusion `C^•_cont(G, M) → C^•(G, M)` into Mathlib's inhomogeneous cochains. -/
abbrev contCochainsι [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M]
    [ContinuousSMul G M] :
    contCochains k G M ⟶ groupCohomology.inhomogeneousCochains (rep k G M) :=
  (contSubCx k G M).ι

/-- **Continuous cohomology** `Hⁿ_cont(G, M)`, the cohomology of `C^•_cont(G, M)`. -/
abbrev contCohomology [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M]
    [ContinuousSMul G M] (n : ℕ) : ModuleCat.{u} k :=
  (contCochains k G M).homology n

variable {k G M}

section Basic

variable [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- The terms of `C^•_cont(G, M)`. -/
theorem contCochains_X (n : ℕ) :
    (contCochains k G M).X n = ModuleCat.of k (contCochain k G M n) :=
  rfl

/-- The differential of `C^•_cont(G, M)` is the inhomogeneous differential
`(df)(g₀,…,gₙ) = g₀ • f(g₁,…,gₙ) + ∑_{j} (−1)^{j+1} f(…, g_j g_{j+1}, …)` (Mathlib's formula, with
the `j = n` term dropping the last argument). -/
theorem contCochains_d_apply (n : ℕ) (f : (contCochains k G M).X n) (g : Fin (n + 1) → G) :
    asFun k G M (((contSubCx k G M).el (((contCochains k G M).d n (n + 1)).hom f) :
      contCochain k G M (n + 1)) : (groupCohomology.inhomogeneousCochains (rep k G M)).X (n + 1)) g =
      g 0 • asFun k G M ((contSubCx k G M).el f : contCochain k G M n) (fun i => g i.succ) +
        ∑ j : Fin (n + 1), (-1 : k) ^ ((j : ℕ) + 1) •
          asFun k G M ((contSubCx k G M).el f : contCochain k G M n)
            (Fin.contractNth j (· * ·) g) := by
  rw [SubCx.toCx_d_apply, groupCohomology.inhomogeneousCochains.d_def]
  rfl

/-- The inclusion into Mathlib's inhomogeneous cochains is injective in every degree. -/
theorem contCochainsι_f_injective (n : ℕ) :
    Function.Injective ((contCochainsι k G M).f n).hom :=
  SubCx.ι_f_injective _ n

end Basic

/-! ### The discrete case: Mathlib's group cohomology -/

section Discrete

variable [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

omit [ContinuousMul G] [ContinuousSMul G M] in
/-- For a discrete group every cochain is continuous. -/
theorem contCochain_eq_top_of_discrete [DiscreteTopology G] (n : ℕ) :
    contCochain k G M n = ⊤ := by
  ext f
  simp only [Submodule.mem_top, iff_true]
  exact continuous_of_discreteTopology

/-- **Sanity check:** for a discrete group `G` the inclusion `C^•_cont(G, M) → C^•(G, M)` is an
isomorphism of complexes. PROVED. -/
theorem contCochainsι_isIso_of_discrete [DiscreteTopology G] : IsIso (contCochainsι k G M) :=
  SubCx.ι_isIso_of_eq_top _ contCochain_eq_top_of_discrete

/-- **Sanity check:** for a discrete group `G`, continuous cohomology is Mathlib's group
cohomology `Hⁿ(G, M)` of `Rep.ofDistribMulAction k G M`. PROVED. -/
def contCohomologyIsoOfDiscrete [DiscreteTopology G] (n : ℕ) :
    contCohomology k G M n ≅ groupCohomology (rep k G M) n :=
  haveI := contCochainsι_isIso_of_discrete (k := k) (G := G) (M := M)
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (asIso (contCochainsι k G M))

end Discrete

/-! ### Functoriality in compatible pairs: restriction and inflation -/

section Functoriality

variable {H : Type u} [Group H]
  {N : Type u} [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]

variable [TopologicalSpace H] [TopologicalSpace N]
  [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
  [ContinuousMul H] [ContinuousAdd N] [ContinuousConstSMul k N] [ContinuousSMul H N]

/-- **The cochain map `C^•_cont(G, M) → C^•_cont(H, N)` of a compatible pair** `(φ, f)`:
a continuous homomorphism `φ : H →ₜ* G` and a continuous `k`-linear `f : M → N` with
`f (φ h • m) = h • f m`, sending `c` to `f ∘ c ∘ φⁿ` (Neukirch–Schmidt–Wingberg I §5). For
`f = id` this is restriction along `φ` (localization `G_{K_v} → G_{K,S}` in (4.3)); for `φ` a
quotient map `G → G/U` and `f` the inclusion of `U`-invariants it is inflation. PROVED (a cochain
map: the restriction of Mathlib's `groupCohomology.cochainsMap`). -/
def contCochainsMap (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    contCochains k G M ⟶ contCochains k H N :=
  (contSubCx k G M).map (contSubCx k H N) (compatCochainsMap (φ : H →* G) f hf)
    (fun n c hc => by
      change Continuous (fun x : Fin n → H => f (asFun k G M c (φ ∘ x)))
      exact hfc.comp (hc.comp (continuous_pi fun i => φ.continuous.comp (continuous_apply i))))

theorem contCochainsMap_apply (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) (c : (contCochains k G M).X n)
    (x : Fin n → H) :
    asFun k H N (((contSubCx k H N).el (((contCochainsMap φ f hfc hf).f n).hom c) :
      contCochain k H N n) : (groupCohomology.inhomogeneousCochains (rep k H N)).X n) x =
      f (asFun k G M ((contSubCx k G M).el c : contCochain k G M n) (φ ∘ x)) :=
  rfl

/-- The cochain map of a compatible pair commutes with the inclusions into Mathlib's
inhomogeneous cochains. -/
@[reassoc]
theorem contCochainsMap_ι (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    contCochainsMap φ f hfc hf ≫ contCochainsι k H N =
      contCochainsι k G M ≫ compatCochainsMap (φ : H →* G) f hf :=
  SubCx.map_ι _ _ _ _

variable (k G M) in
/-- The identity pair induces the identity. PROVED. -/
theorem contCochainsMap_id :
    contCochainsMap (ContinuousMonoidHom.id G) (LinearMap.id : M →ₗ[k] M) continuous_id
      (fun _ _ => rfl) = 𝟙 (contCochains k G M) := by
  ext n c
  rfl

/-- Composition of compatible pairs. PROVED. -/
theorem contCochainsMap_comp {L : Type u} [Group L] [TopologicalSpace L] [ContinuousMul L]
    {P : Type u} [AddCommGroup P] [Module k P] [DistribMulAction L P] [SMulCommClass L k P]
    [TopologicalSpace P] [ContinuousAdd P] [ContinuousConstSMul k P] [ContinuousSMul L P]
    (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (ψ : L →ₜ* H) (g : N →ₗ[k] P) (hgc : Continuous g)
    (hg : ∀ (l : L) (n : N), g (ψ l • n) = l • g n) :
    contCochainsMap (φ.comp ψ) (g ∘ₗ f) (hgc.comp hfc)
        (fun l m => by
          change g (f (φ (ψ l) • m)) = l • g (f m)
          rw [hf, hg]) =
      contCochainsMap φ f hfc hf ≫ contCochainsMap ψ g hgc hg := by
  ext n c
  rfl

/-- The map on continuous cohomology `Hⁿ_cont(G, M) → Hⁿ_cont(H, N)` of a compatible pair. -/
abbrev contCohomologyMap (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) :
    contCohomology k G M n ⟶ contCohomology k H N n :=
  HomologicalComplex.homologyMap (contCochainsMap φ f hfc hf) n

end Functoriality

/-! ### Restriction along a continuous homomorphism with the same coefficients -/

end Cochains

section ResMod

variable {G : Type u} [Group G] [TopologicalSpace G] {H : Type u} [Group H] [TopologicalSpace H]

/-- The module `M` with the `H`-action obtained by restricting a `G`-action along `φ : H →ₜ* G`,
as a type synonym of `M` (to avoid instance clashes on `M`). -/
def ResMod (_φ : H →ₜ* G) (M : Type u) : Type u := M

variable (φ : H →ₜ* G) (M : Type u)

instance [AddCommGroup M] : AddCommGroup (ResMod φ M) := inferInstanceAs (AddCommGroup M)

instance {k : Type u} [Semiring k] [AddCommGroup M] [Module k M] : Module k (ResMod φ M) :=
  inferInstanceAs (Module k M)

instance [TopologicalSpace M] : TopologicalSpace (ResMod φ M) := inferInstanceAs (TopologicalSpace M)

instance [TopologicalSpace M] [DiscreteTopology M] : DiscreteTopology (ResMod φ M) :=
  inferInstanceAs (DiscreteTopology M)

instance [AddCommGroup M] [DistribMulAction G M] : DistribMulAction H (ResMod φ M) :=
  DistribMulAction.compHom M (φ : H →* G)

/-- The action of `h : H` on the restricted module is the action of `φ h`. -/
theorem ResMod.smul_def [AddCommGroup M] [DistribMulAction G M] (h : H) (m : ResMod φ M) :
    h • m = (show ResMod φ M from (φ h • (show M from m))) :=
  rfl

instance {k : Type u} [Semiring k] [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] : SMulCommClass H k (ResMod φ M) where
  smul_comm h c m := (smul_comm (φ h) c (show M from m) : _)

instance [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] : ContinuousAdd (ResMod φ M) :=
  inferInstanceAs (ContinuousAdd M)

instance {k : Type u} [Semiring k] [AddCommGroup M] [Module k M] [TopologicalSpace M]
    [ContinuousConstSMul k M] : ContinuousConstSMul k (ResMod φ M) :=
  inferInstanceAs (ContinuousConstSMul k M)

instance [AddCommGroup M] [DistribMulAction G M] [TopologicalSpace M] [ContinuousSMul G M] :
    ContinuousSMul H (ResMod φ M) where
  continuous_smul := by
    change Continuous (fun p : H × M => φ p.1 • p.2)
    exact (φ.continuous.comp continuous_fst).smul continuous_snd

end ResMod

section Restriction

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] {H : Type u} [Group H] [TopologicalSpace H] (φ : H →ₜ* G)

/-- The identity of `M`, read as a map into the restricted module. -/
def toResMod : M →ₗ[k] ResMod φ M := LinearMap.id

theorem toResMod_compat (h : H) (m : M) :
    toResMod (k := k) φ (φ h • m) = h • toResMod (k := k) φ m :=
  rfl

variable [ContinuousMul G] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
  [ContinuousMul H]

/-- **Restriction** `C^•_cont(G, M) → C^•_cont(H, M)` along a continuous homomorphism
`φ : H →ₜ* G` (with `H` acting on `M` through `φ`): `c ↦ c ∘ φⁿ`. For `φ` the localization map
`G_{K_v} → G_{K,S}` this is the restriction map `res_v` of (4.3) (Nekovář 3.4.1.6, 5.1). PROVED (a
cochain map). -/
abbrev resCochains : contCochains k G M ⟶ contCochains k H (ResMod φ M) :=
  contCochainsMap φ (toResMod (k := k) φ) continuous_id (toResMod_compat φ)

end Restriction


end ZInQ.Manuscript.RC.SelmerComplex
