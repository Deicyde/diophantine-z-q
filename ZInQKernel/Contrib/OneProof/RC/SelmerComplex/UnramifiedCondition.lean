import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances
import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.Places

/-!
# Lane RC26: the unramified complex as a genuine local condition

Manuscript `diophantine_zq.tex`, tex 3471–3481 ("at augmentation `g = 1`, this is the direct sum of
the unramified complex `[Φ−1]` in degrees zero and one …") and tex 3483–3487 (the unramified
condition at the new places of the support change); Nekovář, *Selmer complexes*, 7.8.8 and
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, I §1 (cohomology of `ℤ̂`).

For a topological group `G` (the decomposition group `G_{K_w}`), a topological group `H ≃ₜ* ℤ̂`
(`Gal(K_w^ur/K_w)`, with Frobenius `Frob`), a continuous homomorphism `π : G → H` (restriction
to `K_w^ur`), a finite discrete continuous representation `X` of `H` on `W` (Frobenius `Φ`), and a
`G`-equivariant `k`-linear map `f : W → M` into a discrete `G`-module (`f (π g • x) = g • f x`),
the cochain map

```text
urToLocal : [W --(Φ−1)--> W] ⟶ C^•_cont(G, M),
  degree 0:  x ↦ (the constant 0-cochain f x),
  degree 1:  x ↦ (g ↦ f (c_x (π g))),   c_x(Frob^n) = Σ_{j<n} Φ^j x   (the cocycle with c_x(Frob) = x),
```

is inflation along `π` (the cocycle `c_x` is the continuous `1`-cocycle of `ℤ̂` attached to `x`)
composed with `f`. It is a morphism of Mathlib `ℤ`-indexed cochain complexes into the genuine local
complex `(natCx (contCochains k G M)).toCC`, so `localConditionsOfCC` turns it into a genuine local
condition (`unramifiedLocalConditions`).

* `urCocycle`, `urCocycle_mem` (cocycle), `urCocycle_frob` (value `x` at the Frobenius),
  `urCocycle_frob_sub` (`c_{Φx − x}(h) = h • x − x`);
* `urToLocal`, `urToLocal_f₀`, `urToLocal_f₁` (the components);
* `unramifiedLocalConditions`, `allUnramifiedLocalConditions`: genuine Galois local conditions
  with the unramified complex `urCx K w X` (non-vacuity: the residual module `𝔽₂²`);
* `urToLocal_galois`: the map at a finite place `w` of a number field, with `G = G_{K_w}`,
  `H = Gal(K_w^ur/K_w)`, `π = resUr K w`.

Everything is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section Generic

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]

/-- A period of the Frobenius on the finite module `W`. -/
def urPeriod : ℕ := Classical.choose (exists_period e X)

theorem urPeriod_pos : 0 < urPeriod e X := (Classical.choose_spec (exists_period e X)).1

theorem urPeriod_spec : ∀ x : X.V, frobElt e ^ urPeriod e X • x = x :=
  (Classical.choose_spec (exists_period e X)).2

instance urPeriod_neZero : NeZero (period X (urPeriod e X)) :=
  ⟨(Nat.lt_trans Nat.zero_lt_one (one_lt_period X (urPeriod_pos e X))).ne'⟩

/-- **The continuous `1`-cocycle of `H ≃ ℤ̂` attached to `x ∈ W`**: `Frob^n ↦ Σ_{j<n} Φ^j x`
(the other group's `cocycleOf`, at the chosen period). -/
def urCocycle (x : X.V) : H → X.V := cocycleOf e X (urPeriod e X) x

theorem urCocycle_mem (x : X.V) : urCocycle e X x ∈ TauCeti.ContCohomology.Z1 H X.V :=
  cocycleOf_mem e X (urPeriod_spec e X) x

theorem urCocycle_frob (x : X.V) : urCocycle e X x (frobElt e) = x :=
  cocycleOf_frob e X (urPeriod_pos e X) x

theorem urCocycle_add (x y : X.V) :
    urCocycle e X (x + y) = urCocycle e X x + urCocycle e X y := by
  funext h
  simp only [urCocycle, cocycleOf, psum, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem urCocycle_smul (c : k) (x : X.V) : urCocycle e X (c • x) = c • urCocycle e X x := by
  funext h
  simp only [urCocycle, cocycleOf, psum, Pi.smul_apply, Finset.smul_sum, smul_comm _ c]

/-- **Telescoping**: the cocycle of `Φ x − x` is the coboundary of `x`, `h ↦ h • x − x`. -/
theorem urCocycle_frob_sub (x : X.V) (h : H) :
    urCocycle e X (frobElt e • x - x) h = h • x - x := by
  rw [smul_eq_chi e X (urPeriod_spec e X) h x]
  simp only [urCocycle, cocycleOf, psum]
  have key : ∀ j : ℕ, frobElt e ^ j • (frobElt e • x - x) =
      frobElt e ^ (j + 1) • x - frobElt e ^ j • x := by
    intro j
    rw [smul_sub, ← mul_smul, ← pow_succ]
  simp only [key]
  rw [Finset.sum_range_sub (fun j => frobElt e ^ j • x), pow_zero, one_smul]

/-- The cocycle identity `c(ab) = a • c(b) + c(a)` and continuity. -/
theorem urCocycle_cocycle (x : X.V) (a b : H) :
    urCocycle e X x (a * b) = a • urCocycle e X x b + urCocycle e X x a :=
  ((TauCeti.ContCohomology.mem_Z1_iff).1 (urCocycle_mem e X x)).2 a b

theorem urCocycle_continuous (x : X.V) : Continuous (urCocycle e X x) :=
  ((TauCeti.ContCohomology.mem_Z1_iff).1 (urCocycle_mem e X x)).1

variable {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)

/-- Degree `0` of `urToLocal`: `x ↦` the constant `0`-cochain `f x`. -/
def urLin₀ : X.V →ₗ[k] contCochain k G M 0 where
  toFun x := ⟨(fun _ => f x : (Fin 0 → G) → M), continuous_const⟩
  map_add' x y := Subtype.ext (funext fun _ => map_add f x y)
  map_smul' c x := Subtype.ext (funext fun _ => map_smul f c x)

/-- Degree `1` of `urToLocal`: `x ↦ (g ↦ f (c_x (π g)))`, the inflation of the cocycle `c_x`. -/
def urLin₁ : X.V →ₗ[k] contCochain k G M 1 where
  toFun x := ⟨(fun g => f (urCocycle e X x (π (g 0))) : (Fin 1 → G) → M),
    (continuous_of_discreteTopology (f := f)).comp
      ((urCocycle_continuous e X x).comp ((map_continuous π).comp (continuous_apply 0)))⟩
  map_add' x y := Subtype.ext (funext fun g => by
    change f (urCocycle e X (x + y) (π (g 0))) = f (urCocycle e X x (π (g 0))) +
      f (urCocycle e X y (π (g 0)))
    rw [urCocycle_add, Pi.add_apply, map_add])
  map_smul' c x := Subtype.ext (funext fun g => by
    change f (urCocycle e X (c • x) (π (g 0))) = c • f (urCocycle e X x (π (g 0)))
    rw [urCocycle_smul, Pi.smul_apply, map_smul])

/-- The `ℤ`-indexed genuine local complex `C^•_cont(G, M)`. -/
abbrev locCC : CochainComplex (ModuleCat.{0} k) ℤ := (natCx (contCochains k G M)).toCC

include hf in
/-- The first square commutes: `d⁰ ∘ φ₀ = φ₁ ∘ (Φ − 1)`. -/
theorem urToLocal_comm :
    ModuleCat.ofHom (urLin₀ (G := G) X f) ≫ (locCC (k := k) (G := G) (M := M)).d 0 1 =
      ModuleCat.ofHom (frob e X - 1) ≫ ModuleCat.ofHom (urLin₁ e π X f) := by
  ext x
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := k) (G := G) (M := M) 0
    ((contSubCx k G M).ofSub (urLin₀ X f x)) g
  refine h1.trans ?_
  change g 0 • f x + ∑ j : Fin 1, (-1 : k) ^ ((j : ℕ) + 1) • f x =
    f (urCocycle e X (frob e X x - x) (π (g 0)))
  rw [frob_apply, urCocycle_frob_sub, map_sub, hf]
  simp [sub_eq_add_neg]

include hf in
/-- The second square: `d¹ ∘ φ₁ = 0` (the inflated cocycle is a cocycle). -/
theorem urToLocal_cocycle (j : ℤ) (hj : (ComplexShape.up ℤ).Rel 1 j) :
    ModuleCat.ofHom (urLin₁ e π X f) ≫ (locCC (k := k) (G := G) (M := M)).d 1 j = 0 := by
  obtain rfl : j = 2 := by simpa using hj.symm
  ext x
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := k) (G := G) (M := M) 1
    ((contSubCx k G M).ofSub (urLin₁ e π X f x)) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • f (urCocycle e X x (π (g 1))) +
    ((-1 : k) ^ (0 + 1) • f (urCocycle e X x (π (g 0 * g 1))) +
      (-1 : k) ^ (1 + 1) • f (urCocycle e X x (π (g 0)))) = 0
  rw [map_mul, urCocycle_cocycle, map_add, hf]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

/-- **The unramified complex maps to the genuine local complex**: the cochain map
`[W --(Φ−1)--> W] ⟶ C^•_cont(G, M)` (inflation of the `ℤ̂`-cocycles along `π`, composed with `f`).
PROVED. -/
def urToLocal : frobCx (frob e X) ⟶ locCC (k := k) (G := G) (M := M) :=
  HomologicalComplex.mkHomFromDouble rel01 (by decide)
    (ModuleCat.ofHom (urLin₀ X f)) (ModuleCat.ofHom (urLin₁ e π X f))
    (urToLocal_comm e π X f hf) (urToLocal_cocycle e π X f hf)

theorem urToLocal_f₀ :
    (urToLocal e π X f hf).f 0 =
      (HomologicalComplex.doubleXIso₀ _ rel01).hom ≫ ModuleCat.ofHom (urLin₀ X f) :=
  HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _

theorem urToLocal_f₁ :
    (urToLocal e π X f hf).f 1 =
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).hom ≫ ModuleCat.ofHom (urLin₁ e π X f) :=
  HomologicalComplex.mkHomFromDouble_f₁ _ _ _ _ _ _

end Generic

/-! ### At a finite place of a number field -/

section Galois

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  {k : Type} [CommRing k] [TopologicalSpace k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The unramified condition at a place `w ∈ S`**, as a cochain map
`urCx K w X = [W --(Φ_w−1)--> W] ⟶ C^•_cont(G_{K_w}, M)` (the genuine local complex of the
Galois Selmer data): inflation along `resUr K w : G_{K_w} → Gal(K_w^ur/K_w)` composed with a
`G_{K_w}`-equivariant `f : W → M` (`f (resUr g • x) = locMap g • f x`; for `W = M` with the
inflated action, `f = id`). PROVED. -/
def urToLocal_galois (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x) :
    urCx K w.1 X ⟶ (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M w).toCC :=
  urToLocal (eUr K w.1) (resUr K w.1) X (M := ResMod (locMap K S w.1) M) f hf

/-- **Genuine Galois local conditions from Mathlib data**: local complexes `U_v` with cochain maps
into `C^•_cont(G_{K_v}, M)` — at the places where the coefficients are unramified, `urCx K v X_v`
with `urToLocal_galois` (the unramified condition); elsewhere any given condition — through
`localConditionsOfCC`. -/
def unramifiedLocalConditions (U : Places K S → CochainComplex (ModuleCat.{0} k) ℤ)
    (i : ∀ v, U v ⟶ (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M v).toCC) :
    GaloisLocalConditions K S k M :=
  localConditionsOfCC U i

/-- Non-vacuity: the local conditions that are unramified at every place (given unramified data
at every place). -/
def allUnramifiedLocalConditions
    (X : ∀ w : Places K S, TopRep.{0} k (GUr K w.1))
    [∀ w, ContinuousSMul (GUr K w.1) (X w).V] [∀ w, DiscreteTopology (X w).V] [∀ w, Finite (X w).V]
    (f : ∀ w, (X w).V →ₗ[k] M)
    (hf : ∀ w (g : Gloc K w.1) (x : (X w).V), f w (resUr K w.1 g • x) = locMap K S w.1 g • f w x) :
    GaloisLocalConditions K S k M :=
  unramifiedLocalConditions K S (fun w => urCx K w.1 (X w))
    (fun w => urToLocal_galois K S w (X w) (f w) (hf w))

/-- **Non-vacuity**: the residual module `W = 𝔽₂²` (tex 4479–4480) with trivial actions is
unramified at every place, giving genuine Galois local conditions that are the unramified
complex `[W --(Φ−1)--> W] = [W --0--> W]` at every place of `S`. -/
example : GaloisLocalConditions K S (ZMod 2) (TrivMod (GKS K S) (Fin 2 → ZMod 2)) :=
  haveI := fun w : Places K S => continuousSMul_W2 K w.1
  allUnramifiedLocalConditions K S (fun w => W2 K w.1)
    (fun _ => (LinearMap.id : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)))
    (fun _ _ _ => rfl)

end Galois

end ZInQ.Manuscript.RC.SelmerComplex
