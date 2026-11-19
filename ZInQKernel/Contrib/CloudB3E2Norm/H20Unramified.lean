import ZInQKernel.Contrib.CloudB3E2Norm.H20Genuine

/-!
# The coefficient push (H20) at the new place: the unramified condition

Manuscript `diophantine_zq.tex`, tex 3203–3215 and 3471–3487 (the unramified condition
`[W --(Φ_w − 1)--> W]` at the new place `w`, mapped to the local complex by inflation of the
`ℤ̂`-cocycles composed with `f_q : W → M`).

* `cocycle_unique` (PROVED): two continuous `1`-cocycles of a group `G ≃ ℤ̂` (into a discrete
  module) with the same value at the Frobenius are equal.
* `urCocycle_push` (PROVED): an additive `G`-equivariant map `g : W₁ → W₂` carries the cocycle
  `c_x` (`c_x(Frob) = x`) to `c_{g x}`, even though the two cocycles are built from independently
  chosen periods.
* `urG0`, `urG1`, `genuineιq_f0`, `genuineιq_f1`, `genuineUq_d01` (PROVED): the unramified
  condition and `ι_q` in coordinates.
* **`wPushUr`** (definition, all identities PROVED): the push `WPush` of the genuine unramified
  condition `genuineUq` along a `φ`-semilinear equivariant `g : W₁ → W₂` compatible with the maps
  `f_q` (`f_{q,2} ∘ g = f ∘ f_{q,1}`), compatible with the genuine `ι_q` (`genuineιq`) in degrees `0`
  and `1`.
* **`h20ConditionsPush_kummer_ur`** (PROVED): for the old Kummer conditions and the unramified
  condition at `w`, `H20ConditionsPush` holds as soon as the coefficient maps are compatible:
  `ι_{v,2} = f ∘ ι_{v,1}` at the old places and `f_{q,2} ∘ g = f ∘ f_{q,1}` at `w`.
* **`H20CoefficientCompat`** (Prop; the remaining input): the compatibility of the coefficient
  maps with (H20) (`ι_{v,2} = f ∘ ι_{v,1}` at the old places; an equivariant semilinear `g` with
  `f_{q,2} ∘ g = f ∘ f_{q,1}` at `w`); **`hzR_stage_of_shapiro_kummer_ur`** (PROVED): under it the
  Shapiro-level norm identity for the actual (Kummer + unramified) Selmer data gives the
  stage-level one with point factor `φ(e₁)`.
* Non-vacuity: `nonVacuity_wPushUr`, `nonVacuity_h20Compat`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open NumberField IsDedekindDomain

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

set_option linter.unusedSectionVars false

/-! ### Uniqueness of the `ℤ̂`-cocycles -/

section Unique

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (e : G ≃ₜ* TauCeti.zHat.{0}) {V : Type} [AddCommGroup V] [DistribMulAction G V]
  [TopologicalSpace V] [DiscreteTopology V]

/-- **Continuous `1`-cocycles of `G ≃ ℤ̂` are determined by their value at the Frobenius**
(PROVED). -/
theorem cocycle_unique {c₁ c₂ : G → V} (h1 : Continuous c₁) (h2 : Continuous c₂)
    (hc₁ : ∀ a b, c₁ (a * b) = a • c₁ b + c₁ a) (hc₂ : ∀ a b, c₂ (a * b) = a • c₂ b + c₂ a)
    (hF : c₁ (frobElt e) = c₂ (frobElt e)) : c₁ = c₂ := by
  set d : G → V := fun g => c₁ g - c₂ g with hd
  have hdc : ∀ a b, d (a * b) = a • d b + d a := by
    intro a b
    simp only [hd, hc₁, hc₂, smul_sub]
    abel
  have hd1 : d 1 = 0 := by
    have := hdc 1 1
    rw [mul_one, one_smul] at this
    exact left_eq_add.1 this
  have hdF : d (frobElt e) = 0 := sub_eq_zero.2 hF
  have hnat : ∀ n : ℕ, d (frobElt e ^ n) = 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero, hd1]
    | succ n ih => rw [pow_succ', hdc, ih, smul_zero, hdF, add_zero]
  have hint : ∀ n : ℤ, d (frobElt e ^ n) = 0 := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast, hnat]
    · have h := hdc (frobElt e ^ (-(m : ℤ))) (frobElt e ^ (m : ℤ))
      rw [← zpow_add, neg_add_cancel, zpow_zero, hd1, zpow_natCast, hnat, smul_zero,
        zero_add] at h
      exact h.symm
  have hcont : Continuous d := by
    have : Continuous fun g => (c₁ g, c₂ g) := h1.prodMk h2
    exact (continuous_of_discreteTopology (f := fun p : V × V => p.1 - p.2)).comp this
  have := eq_of_eq_zpow e hcont continuous_const (fun n => (hint n).trans rfl)
  funext g
  exact sub_eq_zero.1 (congrFun this g)

end Unique

/-! ### The cocycles `c_x` are natural -/

section Natural

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] [TopologicalSpace k₁] [TopologicalSpace k₂]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0})
  (X₁ : TopRep.{0} k₁ H) [ContinuousSMul H X₁.V] [DiscreteTopology X₁.V] [Finite X₁.V]
  (X₂ : TopRep.{0} k₂ H) [ContinuousSMul H X₂.V] [DiscreteTopology X₂.V] [Finite X₂.V]

/-- **An equivariant additive map carries `c_x` to `c_{g x}`** (PROVED). -/
theorem urCocycle_push (g : X₁.V →+ X₂.V) (hg : ∀ (h : H) (x : X₁.V), g (h • x) = h • g x)
    (x : X₁.V) : (fun h => g (urCocycle e X₁ x h)) = urCocycle e X₂ (g x) := by
  refine cocycle_unique e ?_ (urCocycle_continuous e X₂ (g x)) ?_ (urCocycle_cocycle e X₂ (g x))
    ?_
  · exact (continuous_of_discreteTopology (f := fun y : X₁.V => g y)).comp
      (urCocycle_continuous e X₁ x)
  · intro a b
    rw [urCocycle_cocycle, map_add, hg]
  · rw [urCocycle_frob, urCocycle_frob]

end Natural

/-! ### The unramified complex and `ι_q` in coordinates -/

section UrCoord

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (w : Places K S)

/-- The structural isomorphism of the unramified complex in degree `0`. -/
abbrev urE0 {k : Type} [CommRing k] [TopologicalSpace k] (X : TopRep.{0} k (GUr K w.1)) :=
  HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob (eUr K w.1) X - 1)) rel01

/-- The structural isomorphism of the unramified complex in degree `1`. -/
abbrev urE1 {k : Type} [CommRing k] [TopologicalSpace k] (X : TopRep.{0} k (GUr K w.1)) :=
  HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (frob (eUr K w.1) X - 1)) rel01 (by decide)

/-- `urE0` with domain the degree-`0` term of `genuineUq`. -/
abbrev urG0 {k : Type} [CommRing k] [TopologicalSpace k] (X : TopRep.{0} k (GUr K w.1)) :
    (genuineUq K S k w X).X 0 ≅ ModuleCat.of k X.V :=
  urE0 w X

/-- `urE1` with domain the degree-`1` term of `genuineUq`. -/
abbrev urG1 {k : Type} [CommRing k] [TopologicalSpace k] (X : TopRep.{0} k (GUr K w.1)) :
    (genuineUq K S k w X).X 1 ≅ ModuleCat.of k X.V :=
  urE1 w X

/-- `e.hom (e.inv z) = z` for an isomorphism of modules. Kind: PROVED. -/
theorem iso_inv_hom_apply' {k : Type} [Ring k] {A B : ModuleCat.{0} k} (e : A ≅ B) (z : B) :
    e.hom.hom (e.inv.hom z) = z := by
  simp

end UrCoord

/-! ### The push of the genuine unramified condition -/

section Ur

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] [TopologicalSpace k₁] [TopologicalSpace k₂]
  (φ : k₁ →+* k₂)
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M₁ : Type} [AddCommGroup M₁] [Module k₁ M₁] [DistribMulAction (GKS K S) M₁]
  [SMulCommClass (GKS K S) k₁ M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul (GKS K S) M₁]
  {M₂ : Type} [AddCommGroup M₂] [Module k₂ M₂] [DistribMulAction (GKS K S) M₂]
  [SMulCommClass (GKS K S) k₂ M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
  [ContinuousSMul (GKS K S) M₂]
  (f : M₁ →ₛₗ[φ] M₂) (hf : ∀ (g : GKS K S) (m : M₁), f (g • m) = g • f m)
  (w : Places K S)
  (X₁ : TopRep.{0} k₁ (GUr K w.1)) [ContinuousSMul (GUr K w.1) X₁.V] [DiscreteTopology X₁.V]
  [Finite X₁.V]
  (X₂ : TopRep.{0} k₂ (GUr K w.1)) [ContinuousSMul (GUr K w.1) X₂.V] [DiscreteTopology X₂.V]
  [Finite X₂.V]
  (fq₁ : X₁.V →ₗ[k₁] M₁)
  (hfq₁ : ∀ (g : Gloc K w.1) (x : X₁.V), fq₁ (resUr K w.1 g • x) = locMap K S w.1 g • fq₁ x)
  (fq₂ : X₂.V →ₗ[k₂] M₂)
  (hfq₂ : ∀ (g : Gloc K w.1) (x : X₂.V), fq₂ (resUr K w.1 g • x) = locMap K S w.1 g • fq₂ x)
  (gq : X₁.V →ₛₗ[φ] X₂.V) (hgq : ∀ (h : GUr K w.1) (x : X₁.V), gq (h • x) = h • gq x)
  (hcomp : ∀ x, fq₂ (gq x) = f (fq₁ x))

/-- The push in degree `n ∈ {0, 1}` through the structural isomorphisms. Kind: definition. -/
def urPushAt {A₁ : ModuleCat.{0} k₁} {A₂ : ModuleCat.{0} k₂} (e₁ : A₁ ≅ ModuleCat.of k₁ X₁.V)
    (e₂ : A₂ ≅ ModuleCat.of k₂ X₂.V) : A₁ →ₛₗ[φ] A₂ where
  toFun y := e₂.inv.hom (gq (e₁.hom.hom y))
  map_add' y y' := by simp only [map_add]
  map_smul' a y := by simp only [map_smul, LinearMap.map_smulₛₗ]

/-- The push in coordinates, by definition. Kind: PROVED. -/
theorem urPushAt_def {A₁ : ModuleCat.{0} k₁} {A₂ : ModuleCat.{0} k₂}
    (e₁ : A₁ ≅ ModuleCat.of k₁ X₁.V) (e₂ : A₂ ≅ ModuleCat.of k₂ X₂.V) (y : A₁) :
    urPushAt φ w X₁ X₂ gq e₁ e₂ y = e₂.inv.hom (gq (e₁.hom.hom y)) := rfl

/-- The push followed by the structural isomorphism is `g`. Kind: PROVED. -/
theorem urPushAt_apply {A₁ : ModuleCat.{0} k₁} {A₂ : ModuleCat.{0} k₂}
    (e₁ : A₁ ≅ ModuleCat.of k₁ X₁.V) (e₂ : A₂ ≅ ModuleCat.of k₂ X₂.V) (y : A₁) :
    e₂.hom.hom (urPushAt φ w X₁ X₂ gq e₁ e₂ y) = gq (e₁.hom.hom y) :=
  iso_inv_hom_apply' e₂ _

/-- `ι_q` in degree `0`: the constant cochain `f_q(x)`. Kind: PROVED. -/
theorem genuineιq_f0 {k : Type} [CommRing k] [TopologicalSpace k] {M : Type} [AddCommGroup M]
    [Module k M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (fq : X.V →ₗ[k] M)
    (hfq : ∀ (g : Gloc K w.1) (x : X.V), fq (resUr K w.1 g • x) = locMap K S w.1 g • fq x)
    (y : (genuineUq K S k w X).X 0) :
    (genuineιq K S k M w X fq hfq).f 0 0 rfl y =
      urLin₀ (G := Gloc K w.1) X (show X.V →ₗ[k] ResMod (locMap K S w.1) M from fq)
        ((urG0 (S := S) w X).hom.hom y) := by
  exact congrArg (fun g => ModuleCat.Hom.hom g y)
    (urToLocal_f₀ (eUr K w.1) (resUr K w.1) X
      (show X.V →ₗ[k] ResMod (locMap K S w.1) M from fq) hfq)

/-- `ι_q` in degree `1`: the inflated cocycle `σ ↦ f_q(c_x(π σ))`. Kind: PROVED. -/
theorem genuineιq_f1 {k : Type} [CommRing k] [TopologicalSpace k] {M : Type} [AddCommGroup M]
    [Module k M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (fq : X.V →ₗ[k] M)
    (hfq : ∀ (g : Gloc K w.1) (x : X.V), fq (resUr K w.1 g • x) = locMap K S w.1 g • fq x)
    (y : (genuineUq K S k w X).X 1) :
    (genuineιq K S k M w X fq hfq).f 1 1 rfl y =
      urLin₁ (G := Gloc K w.1) (eUr K w.1) (resUr K w.1) X
        (show X.V →ₗ[k] ResMod (locMap K S w.1) M from fq) ((urG1 (S := S) w X).hom.hom y) := by
  exact congrArg (fun g => ModuleCat.Hom.hom g y)
    (urToLocal_f₁ (eUr K w.1) (resUr K w.1) X
      (show X.V →ₗ[k] ResMod (locMap K S w.1) M from fq) hfq)

/-- The differential of the unramified condition is `Φ − 1`. Kind: PROVED. -/
theorem genuineUq_d01 {k : Type} [CommRing k] [TopologicalSpace k]
    (X : TopRep.{0} k (GUr K w.1)) (y : (genuineUq K S k w X).X 0) :
    (genuineUq K S k w X).d 0 1 rfl y =
      (urG1 (S := S) w X).inv.hom (frob (eUr K w.1) X ((urG0 (S := S) w X).hom.hom y) -
        (urG0 (S := S) w X).hom.hom y) := by
  exact congrArg (fun g => ModuleCat.Hom.hom g y) (frobCx_d01 (frob (eUr K w.1) X))

/-- **The push of the genuine unramified condition at `w`** (Kind: definition; all identities
PROVED): `g` in degrees `0` and `1` (through the structural isomorphisms of the double complex),
compatible with `Φ − 1` and with `ι_q`. -/
def wPushUr :
    WPush φ (locPush φ f hf w.1) (genuineιq K S k₁ M₁ w X₁ fq₁ hfq₁)
      (genuineιq K S k₂ M₂ w X₂ fq₂ hfq₂) where
  w0 := urPushAt φ w X₁ X₂ gq (urG0 (S := S) w X₁) (urG0 (S := S) w X₂)
  w1 := urPushAt φ w X₁ X₂ gq (urG1 (S := S) w X₁) (urG1 (S := S) w X₂)
  hw x := by
    rw [genuineUq_d01 w X₁, genuineUq_d01 w X₂, urPushAt_def, urPushAt_apply]
    refine congrArg (urG1 (S := S) w X₂).inv.hom ?_
    rw [iso_inv_hom_apply' (urG1 (S := S) w X₁), map_sub, frob_apply, frob_apply, hgq]
  hι0 x := by
    rw [genuineιq_f0 w X₁ fq₁ hfq₁, genuineιq_f0 w X₂ fq₂ hfq₂, urPushAt_apply]
    exact Subtype.ext (funext fun _ => (hcomp _).symm)
  hι1 x := by
    rw [genuineιq_f1 w X₁ fq₁ hfq₁, genuineιq_f1 w X₂ fq₂ hfq₂, urPushAt_apply]
    refine Subtype.ext (funext fun σ => ?_)
    change f (fq₁ (urCocycle (eUr K w.1) X₁ ((urG1 (S := S) w X₁).hom.hom x)
        (resUr K w.1 (σ 0)))) =
      fq₂ (urCocycle (eUr K w.1) X₂ (gq ((urG1 (S := S) w X₁).hom.hom x)) (resUr K w.1 (σ 0)))
    have h := congrFun (urCocycle_push (eUr K w.1) X₁ X₂ gq.toAddMonoidHom hgq
      ((urG1 (S := S) w X₁).hom.hom x)) (resUr K w.1 (σ 0))
    exact (hcomp _).symm.trans (congrArg fq₂ h)

end Ur

/-! ### The local conditions survive (H20) -/

section Final

variable {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] [TopologicalSpace k₁] [TopologicalSpace k₂]
  (φ : k₁ →+* k₂)
  {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {M₁ : Type} [AddCommGroup M₁] [Module k₁ M₁] [DistribMulAction (GKS K S) M₁]
  [SMulCommClass (GKS K S) k₁ M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul (GKS K S) M₁]
  {M₂ : Type} [AddCommGroup M₂] [Module k₂ M₂] [DistribMulAction (GKS K S) M₂]
  [SMulCommClass (GKS K S) k₂ M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
  [ContinuousSMul (GKS K S) M₂]
  (f : M₁ →ₛₗ[φ] M₂) (hf : ∀ (g : GKS K S) (m : M₁), f (g • m) = g • f m)

open scoped Classical in
/-- **The local conditions survive (H20)** (PROVED; tex 3262–3270): for the old Kummer conditions
at the places of `S₀` and the unramified condition at the new place `w`, `H20ConditionsPush` holds
given only the compatibility of the coefficient maps: `ι_{v,2} = f ∘ ι_{v,1}` and
`f_{q,2} ∘ g = f ∘ f_{q,1}` for a `φ`-semilinear equivariant `g : W₁ → W₂`. -/
theorem h20ConditionsPush_kummer_ur (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (ι₁ : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M₁)
    (hι₁ : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι₁ v (σ • t) = σ • ι₁ v t)
    (ι₂ : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M₂)
    (hι₂ : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι₂ v (σ • t) = σ • ι₂ v t)
    (hι : ∀ v t, ι₂ v t = resPush φ f v.1 (ι₁ v t)) (w : Places K S)
    (X₁ : TopRep.{0} k₁ (GUr K w.1)) [ContinuousSMul (GUr K w.1) X₁.V] [DiscreteTopology X₁.V]
    [Finite X₁.V]
    (X₂ : TopRep.{0} k₂ (GUr K w.1)) [ContinuousSMul (GUr K w.1) X₂.V] [DiscreteTopology X₂.V]
    [Finite X₂.V]
    (fq₁ : X₁.V →ₗ[k₁] M₁)
    (hfq₁ : ∀ (g : Gloc K w.1) (x : X₁.V), fq₁ (resUr K w.1 g • x) = locMap K S w.1 g • fq₁ x)
    (fq₂ : X₂.V →ₗ[k₂] M₂)
    (hfq₂ : ∀ (g : Gloc K w.1) (x : X₂.V), fq₂ (resUr K w.1 g • x) = locMap K S w.1 g • fq₂ x)
    (gq : X₁.V →ₛₗ[φ] X₂.V) (hgq : ∀ (h : GUr K w.1) (x : X₁.V), gq (h • x) = h • gq x)
    (hcomp : ∀ x, fq₂ (gq x) = f (fq₁ x)) :
    H20ConditionsPush φ f hf (kummerOldConditions K S₀ S k₁ M₁ m B ι₁ hι₁)
      (kummerOldConditions K S₀ S k₂ M₂ m B ι₂ hι₂) w (genuineιq K S k₁ M₁ w X₁ fq₁ hfq₁)
      (genuineιq K S k₂ M₂ w X₂ fq₂ hfq₂) :=
  h20ConditionsPush_kummer φ f hf m B ι₁ hι₁ ι₂ hι₂ hι w _ _
    (wPushUr φ f hf w X₁ X₂ fq₁ hfq₁ fq₂ hfq₂ gq hgq hcomp)

open scoped Classical in
/-- **The coefficient maps are compatible with (H20)** (Prop; the remaining input; kind
ELLIOT/GLUE: tex 3203–3215 with 3262–3270 and 3471–3487): at every old place the stage Kummer map
is the push of the Shapiro-level one, `ι_{v,2} = f ∘ ι_{v,1}`, and at the new place the stage
unramified module receives a `φ`-semilinear `Gal(K_w^{ur}/K_w)`-equivariant map `g` from the
Shapiro-level one with `f_{q,2} ∘ g = f ∘ f_{q,1}`. Kind: definition (Prop). -/
def H20CoefficientCompat (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K))
    (ι₁ : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M₁)
    (ι₂ : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M₂)
    (w : Places K S) (X₁ : TopRep.{0} k₁ (GUr K w.1)) (X₂ : TopRep.{0} k₂ (GUr K w.1))
    (fq₁ : X₁.V →ₗ[k₁] M₁) (fq₂ : X₂.V →ₗ[k₂] M₂) : Prop :=
  (∀ v t, ι₂ v t = resPush φ f v.1 (ι₁ v t)) ∧
    ∃ gq : X₁.V →ₛₗ[φ] X₂.V, (∀ (h : GUr K w.1) (x : X₁.V), gq (h • x) = h • gq x) ∧
      ∀ x, fq₂ (gq x) = f (fq₁ x)

include hf in
open scoped Classical in
/-- **The stage norm identity from the Shapiro-level one, for the actual conditions** (PROVED):
for the old Kummer conditions and the unramified condition at `w`, under
`H20CoefficientCompat`, the Shapiro-level norm identity with retained boundary gives stage
classes satisfying the norm identity with point factor `φ(e₁)` (e.g. `e₁ = a_q − [σ_q] − [σ_q]⁻¹`,
`φ(e₁) = a_q − θ(σ_q) − θ(σ_q)⁻¹` by `eq_transport`). -/
theorem hzR_stage_of_shapiro_kummer_ur (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
    (ι₁ : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M₁)
    (hι₁ : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι₁ v (σ • t) = σ • ι₁ v t)
    (ι₂ : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M₂)
    (hι₂ : ∀ (v : Places K S₀) (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) m),
      ι₂ v (σ • t) = σ • ι₂ v t) (w : Places K S)
    (X₁ : TopRep.{0} k₁ (GUr K w.1)) [ContinuousSMul (GUr K w.1) X₁.V] [DiscreteTopology X₁.V]
    [Finite X₁.V]
    (X₂ : TopRep.{0} k₂ (GUr K w.1)) [ContinuousSMul (GUr K w.1) X₂.V] [DiscreteTopology X₂.V]
    [Finite X₂.V]
    (fq₁ : X₁.V →ₗ[k₁] M₁)
    (hfq₁ : ∀ (g : Gloc K w.1) (x : X₁.V), fq₁ (resUr K w.1 g • x) = locMap K S w.1 g • fq₁ x)
    (fq₂ : X₂.V →ₗ[k₂] M₂)
    (hfq₂ : ∀ (g : Gloc K w.1) (x : X₂.V), fq₂ (resUr K w.1 g • x) = locMap K S w.1 g • fq₂ x)
    (hcompat : H20CoefficientCompat φ f m B ι₁ ι₂ w X₁ X₂ fq₁ fq₂)
    (zR₁ : (selCx (stageRelaxed K S₀ S k₁ M₁ (kummerOldConditions K S₀ S k₁ M₁ m B ι₁ hι₁) w)).X 1)
    (zP₁ : (selCx (selRestrict
      (stageRelaxed K S₀ S k₁ M₁ (kummerOldConditions K S₀ S k₁ M₁ m B ι₁ hι₁) w)
      (primToRel (stageOld K S₀ S k₁ M₁ (kummerOldConditions K S₀ S k₁ M₁ m B ι₁ hι₁))
        (stageRes K S k₁ M₁ w) (genuineιq K S k₁ M₁ w X₁ fq₁ hfq₁)))).X 1) (e₁ : k₁)
    (h₁ : ∃ b, zR₁ = e₁ • (changeMap _ _).f 1 1 rfl zP₁ + (selCx _).d 0 1 rfl b) :
    ∃ (zR₂ : (selCx (stageRelaxed K S₀ S k₂ M₂
        (kummerOldConditions K S₀ S k₂ M₂ m B ι₂ hι₂) w)).X 1)
      (zP₂ : (selCx (selRestrict
        (stageRelaxed K S₀ S k₂ M₂ (kummerOldConditions K S₀ S k₂ M₂ m B ι₂ hι₂) w)
        (primToRel (stageOld K S₀ S k₂ M₂ (kummerOldConditions K S₀ S k₂ M₂ m B ι₂ hι₂))
          (stageRes K S k₂ M₂ w) (genuineιq K S k₂ M₂ w X₂ fq₂ hfq₂)))).X 1),
      ∃ b, zR₂ = φ e₁ • (changeMap _ _).f 1 1 rfl zP₂ + (selCx _).d 0 1 rfl b := by
  obtain ⟨hι, gq, hgq, hcomp⟩ := hcompat
  exact hzR_stage_of_shapiro φ f hf _ _ w _ _
    (h20ConditionsPush_kummer_ur φ f hf m B ι₁ hι₁ ι₂ hι₂ hι w X₁ X₂ fq₁ hfq₁ fq₂ hfq₂ gq hgq
      hcomp) zR₁ zP₁ e₁ h₁

end Final

/-! ### Non-vacuity -/

/-- **Non-vacuity of the hypotheses of `wPushUr`**: the identity push of any unramified
condition (`φ = id`, `f = id`, `g = id`, `f_{q,2} = f_{q,1}`). Kind: PROVED. -/
theorem nonVacuity_wPushUr {k : Type} [CommRing k] [TopologicalSpace k] {K : Type} [Field K]
    [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] (w : Places K S)
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (fq : X.V →ₗ[k] M)
    (hfq : ∀ (g : Gloc K w.1) (x : X.V), fq (resUr K w.1 g • x) = locMap K S w.1 g • fq x) :
    Nonempty (WPush (RingHom.id k) (locPush (RingHom.id k) (LinearMap.id : M →ₗ[k] M)
      (fun _ _ => rfl) w.1) (genuineιq K S k M w X fq hfq) (genuineιq K S k M w X fq hfq)) :=
  ⟨wPushUr (RingHom.id k) LinearMap.id (fun _ _ => rfl) w X X fq hfq fq hfq LinearMap.id
    (fun _ _ => rfl) (fun _ => rfl)⟩

/-- **Non-vacuity of `H20CoefficientCompat`**: the identity push of any coefficient maps.
Kind: PROVED. -/
theorem nonVacuity_h20Compat {k : Type} [CommRing k] [TopologicalSpace k] {K : Type} [Field K] [NumberField K]
    {S₀ S : Set (HeightOneSpectrum (𝓞 K))} {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] (m : ℕ) [NeZero m]
    (B : ∀ v : Places K S₀, WeierstrassCurve (v.1.adicCompletion K))
    (ι : ∀ v : Places K S₀, TorsAlg (v.1.adicCompletion K) (B v) m →+ ResMod (locMap K S v.1) M)
    (w : Places K S) (X : TopRep.{0} k (GUr K w.1)) (fq : X.V →ₗ[k] M) :
    H20CoefficientCompat (RingHom.id k) (LinearMap.id : M →ₗ[k] M) m B ι ι w X X fq fq :=
  ⟨fun _ _ => rfl, LinearMap.id, fun _ _ => rfl, fun _ => rfl⟩

end ZInQ.Contrib.CloudB3E2.NormCochain
