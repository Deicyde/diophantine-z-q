import ZInQKernel.Contrib.RC53Assist.InnerLimit.Objects
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateChebotarev
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.HeightOne
import ZInQKernel.Contrib.CloudB3RC53.TameQuotient.TameCharacter
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Arithmetic realization of the inner-limit switching objects

The inner limit along moving derivative primes in the proof of Theorem 5.3. The objects here are
the actual continuous cochains `C^•_cont(G, M)`, the actual Galois groups `G_{K,S}`, `G_{K_q}`
and `G_ℚ`, the actual localization maps, the actual unramified local condition, the actual Selmer
complexes with their old local conditions, the actual coefficient module `𝕋 = T_2E ⊗ Λ(α)` and
the actual Tate representation of an elliptic curve over `ℚ`. They are compared with the tame
models, the separated completed coordinate product and the limit diagram of the inner-limit
objects, and they supply the detection field of the nonquadratic switch step.

Local comparison.
* Tame coordinates of continuous one-cocycles over any coefficient ring: the values at a Frobenius
  lift and at an inertia element. When both act trivially they kill coboundaries and descend to
  first cohomology. The actual unramified condition has tame coordinates `(x, 0)`, so its image is
  the finite axis; cocycles vanishing on inertia, respectively at the Frobenius lift, have tame
  coordinates on the finite, respectively singular, axis.
* At level `n`, the unramified character and the tame Kummer character of an `n`-th root of a
  uniformizer give actual cocycles with tame coordinates `(x, 0)` and `(0, m)`. When the local
  Galois group fixes the `n`-th roots of unity the tame coordinates of the actual local cohomology
  are onto; at a prime of a number field not dividing `2` this holds at every precision `2^i`;
  along the coefficient stages every limiting coordinate pair of the inner-limit local model, in
  both planes, is the limit of tame coordinates of actual local cocycles.

Localization and detection.
* At a prime outside `S`, the localization of a global continuous one-cocycle has tame
  coordinates `(c(Frob_q), 0)`.
* Every sequence of primes outside `S` is a moving label; its limit Frobenius is an actual element
  of the compact group `G_{K,S}`.
* The inner-limit local class of an actual `Λ`-adic cocycle, and of a sequence of retained stage
  cocycles, lies in the completed finite plane; its coordinate is the ultralimit of the Frobenius
  values, and for an actual cocycle the value at the limit Frobenius.
* The relaxed localization image of the limit diagram is the localization of the global
  one-cycles. Two global cycles with independent finite coordinates give the detection field
  `F ≤ U`, and a detecting pair can be chosen through any class with nonzero finite localization.
* A realization of a limit diagram by the actual Selmer complex with the old local conditions
  ties the limit localization of global cycles to the Frobenius values of stage Selmer cocycles.
  Independent limit Frobenius values then give the detection field of the fixed-`P` nonquadratic
  step.

Quadratic candidates.
* The identity (5.5b) `z(α(h) h) = z(h) ± T z(h)` for cocycles of sign `±1` under a conjugation;
  nonzero vectors of opposite signs are independent; mixed-sign detection at a moving label whose
  limit Frobenius is `α(h) h`.

Derivative stages.
* Actual derivative primes at every coefficient stage by finite Chebotarev, and the retained
  derivative matrices built from them: actual odd primes, the actual Frobenius on the twisted
  coefficient module, the actual Tate matrices of the rational Frobenius elements and of the
  conjugation. Their congruences are proved; `det J = -1`; the selected rational Frobenius
  elements tend to the Chebotarev representative.

Sources: the retained inner limit, lines 4391–4451; the common kernel and finite realization with
(5.4), lines 4748–4831; the derivative-condition lemma, lines 4834–4907; height-one regularity,
lines 4976–5135, in particular the local planes at a derivative prime, lines 5027–5037, and
(5.5b), lines 5086–5115; the unramified complex, lines 3478–3487.
-/

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimitArith

open CategoryTheory Filter Topology Module
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped PowerSeries.WithPiTopology

/-! ### Evaluation of continuous cochains over a coefficient ring -/

section Evaluation

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

variable (R M) in
/-- The value of a continuous zero-cochain. -/
def evalZero : (contCochains R G M).X 0 →ₗ[R] M where
  toFun a := asFun R G M (((contSubCx R G M).el a : contCochain R G M 0) :
    (groupCohomology.inhomogeneousCochains (rep R G M)).X 0) Fin.elim0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (R M) in
/-- The value of a continuous one-cochain at a group element. -/
def evalOne (g : G) : (contCochains R G M).X 1 →ₗ[R] M where
  toFun z := asFun R G M (((contSubCx R G M).el z : contCochain R G M 1) :
    (groupCohomology.inhomogeneousCochains (rep R G M)).X 1) (fun _ => g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coboundary of a zero-cochain: `(d a)(g) = g • a - a`. -/
theorem evalOne_d_zero (a : (contCochains R G M).X 0) (g : G) :
    evalOne R M g (((contCochains R G M).d 0 1).hom a) = g • evalZero R M a - evalZero R M a := by
  have h := contCochains_d_apply (k := R) (G := G) (M := M) 0 a (fun _ => g)
  have e1 : (fun i : Fin 0 => (fun _ : Fin (0 + 1) => g) i.succ) = Fin.elim0 :=
    Subsingleton.elim _ _
  have e2 : ∀ j : Fin (0 + 1), Fin.contractNth j (· * ·) (fun _ : Fin (0 + 1) => g) = Fin.elim0 :=
    fun _ => Subsingleton.elim _ _
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  simp only [e1, e2, Fin.val_zero, zero_add, pow_one, neg_smul, one_smul] at h
  rw [sub_eq_add_neg]
  exact h

/-- Evaluation of a continuous one-cochain is continuous in the group element. -/
theorem continuous_evalOne (z : (contCochains R G M).X 1) :
    Continuous fun g : G => evalOne R M g z :=
  ((contSubCx R G M).el z).2.comp (continuous_pi fun _ => continuous_id)

variable (R M) in
/-- The value of a continuous two-cochain at a pair of group elements. -/
def evalTwo (g h : G) : (contCochains R G M).X 2 →ₗ[R] M where
  toFun w := asFun R G M (((contSubCx R G M).el w : contCochain R G M 2) :
    (groupCohomology.inhomogeneousCochains (rep R G M)).X 2) ![g, h]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coboundary of a one-cochain: `(d z)(g, h) = g • z(h) - z(gh) + z(g)`. -/
theorem evalTwo_d (z : (contCochains R G M).X 1) (g h : G) :
    evalTwo R M g h (((contCochains R G M).d 1 2).hom z) =
      g • evalOne R M h z - evalOne R M (g * h) z + evalOne R M g z := by
  have hd := contCochains_d_apply (k := R) (G := G) (M := M) 1 z ![g, h]
  have e0 : (fun i : Fin 1 => (![g, h] : Fin 2 → G) i.succ) = fun _ => h := by
    funext i; fin_cases i; rfl
  have e1 : Fin.contractNth (0 : Fin 2) (· * ·) (![g, h] : Fin 2 → G) = fun _ => g * h := by
    funext i; fin_cases i; simp [Fin.contractNth]
  have e2 : Fin.contractNth (1 : Fin 2) (· * ·) (![g, h] : Fin 2 → G) = fun _ => g := by
    funext i; fin_cases i; simp [Fin.contractNth]
  rw [Fin.sum_univ_two, e0, e1, e2] at hd
  change evalTwo R M g h (((contCochains R G M).d 1 2).hom z) = g • evalOne R M h z +
      ((-1 : R) ^ ((0 : ℕ) + 1) • evalOne R M (g * h) z +
        (-1 : R) ^ ((1 : ℕ) + 1) • evalOne R M g z) at hd
  rw [show ((-1 : R) ^ ((0 : ℕ) + 1)) = -1 by norm_num,
    show ((-1 : R) ^ ((1 : ℕ) + 1)) = 1 by norm_num, neg_smul, one_smul, one_smul] at hd
  rw [hd]
  abel

variable (R G M) in
/-- The continuous one-cocycles. -/
abbrev Cocycles : Submodule R ((contCochains R G M).X 1) :=
  LinearMap.ker ((contCochains R G M).d 1 2).hom

/-- The cocycle identity `z(gh) = g • z(h) + z(g)`. -/
theorem evalOne_mul (z : Cocycles R G M) (g h : G) :
    evalOne R M (g * h) z = g • evalOne R M h z + evalOne R M g z := by
  have hd := contCochains_d_apply (k := R) (G := G) (M := M) 1 (z : (contCochains R G M).X 1)
    ![g, h]
  have hz : ((contCochains R G M).d 1 (1 + 1)).hom (z : (contCochains R G M).X 1) = 0 := z.2
  rw [hz] at hd
  have e0 : (fun i : Fin 1 => (![g, h] : Fin 2 → G) i.succ) = fun _ => h := by
    funext i; fin_cases i; rfl
  have e1 : Fin.contractNth (0 : Fin 2) (· * ·) (![g, h] : Fin 2 → G) = fun _ => g * h := by
    funext i; fin_cases i; simp [Fin.contractNth]
  have e2 : Fin.contractNth (1 : Fin 2) (· * ·) (![g, h] : Fin 2 → G) = fun _ => g := by
    funext i; fin_cases i; simp [Fin.contractNth]
  rw [Fin.sum_univ_two, e0, e1, e2] at hd
  change (0 : M) = g • evalOne R M h z +
      ((-1 : R) ^ ((0 : ℕ) + 1) • evalOne R M (g * h) z +
        (-1 : R) ^ ((1 : ℕ) + 1) • evalOne R M g z) at hd
  rw [show ((-1 : R) ^ ((0 : ℕ) + 1)) = -1 by norm_num,
    show ((-1 : R) ^ ((1 : ℕ) + 1)) = 1 by norm_num, neg_smul, one_smul, one_smul] at hd
  apply eq_of_sub_eq_zero
  rw [← neg_eq_zero]
  calc -(evalOne R M (g * h) z - (g • evalOne R M h z + evalOne R M g z))
      = g • evalOne R M h z + (-evalOne R M (g * h) z + evalOne R M g z) := by abel
    _ = 0 := hd.symm

/-- A one-cocycle vanishes at the identity. -/
theorem evalOne_one (z : Cocycles R G M) : evalOne R M (1 : G) z = 0 := by
  have h := evalOne_mul z 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_add.mp h

/-- **The square of a conjugated kernel element, sign `+1`** (manuscript (5.5b)): let `α` be the
conjugation by an involution, `H` a set of elements acting trivially on `M`, stable under `α` with
`α ∘ α = id` on `H`, and `T` the action of the involution on `M`. If `T(z(α g)) = z(g)` on `H`
(a sign `+1` cocycle; coboundaries vanish on `H`), then `z(α(h) h) = z(h) + T(z(h))`. -/
theorem evalOne_conj_mul_plus (z : Cocycles R G M) (α : G → G) (T : M →+ M) (H : Set G)
    (hH : ∀ g ∈ H, ∀ m : M, g • m = m) (hαH : ∀ g ∈ H, α g ∈ H) (hα2 : ∀ g ∈ H, α (α g) = g)
    (hsign : ∀ g ∈ H, T (evalOne R M (α g) z) = evalOne R M g z) {h : G} (hh : h ∈ H) :
    evalOne R M (α h * h) z = evalOne R M h z + T (evalOne R M h z) := by
  rw [evalOne_mul z (α h) h, hH (α h) (hαH h hh)]
  have e := hsign (α h) (hαH h hh)
  rw [hα2 h hh] at e
  rw [e]

/-- **The square of a conjugated kernel element, sign `-1`** (manuscript (5.5b)): with the same
data, if `T(z(α g)) = -z(g)` on `H`, then `z(α(h) h) = z(h) - T(z(h))`. -/
theorem evalOne_conj_mul_minus (z : Cocycles R G M) (α : G → G) (T : M →+ M) (H : Set G)
    (hH : ∀ g ∈ H, ∀ m : M, g • m = m) (hαH : ∀ g ∈ H, α g ∈ H) (hα2 : ∀ g ∈ H, α (α g) = g)
    (hsign : ∀ g ∈ H, T (evalOne R M (α g) z) = -evalOne R M g z) {h : G} (hh : h ∈ H) :
    evalOne R M (α h * h) z = evalOne R M h z - T (evalOne R M h z) := by
  rw [evalOne_mul z (α h) h, hH (α h) (hαH h hh)]
  have e := hsign (α h) (hαH h hh)
  rw [hα2 h hh] at e
  rw [e, sub_neg_eq_add]

variable (R G M) in
/-- The coboundary map from zero-cochains into one-cocycles. -/
def coboundary : (contCochains R G M).X 0 →ₗ[R] Cocycles R G M :=
  ((contCochains R G M).d 0 1).hom.codRestrict (Cocycles R G M) fun x => LinearMap.mem_ker.mpr (by
    have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) ((contCochains R G M).d_comp_d 0 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    exact h)

variable (R G M) in
/-- First continuous cohomology, presented as one-cocycles modulo coboundaries. -/
abbrev ContH1 : Type := Cocycles R G M ⧸ LinearMap.range (coboundary R G M)

end Evaluation

/-! ### Tame coordinates -/

section TameCoordinates

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

/-- The tame coordinates of a one-cocycle: its values at a Frobenius lift `φ` and at an inertia
element `σ`. -/
def tameCoord (φ σ : G) : Cocycles R G M →ₗ[R] M × M :=
  (evalOne R M φ ∘ₗ (Cocycles R G M).subtype).prod (evalOne R M σ ∘ₗ (Cocycles R G M).subtype)

theorem tameCoord_apply (φ σ : G) (z : Cocycles R G M) :
    tameCoord φ σ z = (evalOne R M φ z, evalOne R M σ z) :=
  rfl

/-- When `φ` and `σ` act trivially, the tame coordinates of a coboundary vanish. -/
theorem tameCoord_coboundary (φ σ : G) (hφ : ∀ m : M, φ • m = m) (hσ : ∀ m : M, σ • m = m)
    (a : (contCochains R G M).X 0) : tameCoord φ σ (coboundary R G M a) = 0 := by
  rw [tameCoord_apply]
  refine Prod.ext ?_ ?_
  · exact (evalOne_d_zero a φ).trans (by rw [hφ, sub_self]; rfl)
  · exact (evalOne_d_zero a σ).trans (by rw [hσ, sub_self]; rfl)

/-- The tame coordinates on first cohomology, when `φ` and `σ` act trivially. -/
def tameCoordH1 (φ σ : G) (hφ : ∀ m : M, φ • m = m) (hσ : ∀ m : M, σ • m = m) :
    ContH1 R G M →ₗ[R] M × M :=
  (LinearMap.range (coboundary R G M)).liftQ (tameCoord φ σ) (by
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_ker.mpr (tameCoord_coboundary φ σ hφ hσ a))

theorem tameCoordH1_mk (φ σ : G) (hφ : ∀ m : M, φ • m = m) (hσ : ∀ m : M, σ • m = m)
    (z : Cocycles R G M) :
    tameCoordH1 φ σ hφ hσ (Submodule.Quotient.mk z) = tameCoord φ σ z :=
  rfl

variable (R M) in
/-- The finite axis `M ⊕ 0` of the tame coordinates. -/
def tameFiniteAxis : Submodule R (M × M) := (⊤ : Submodule R M).prod ⊥

variable (R M) in
/-- The singular axis `0 ⊕ M` of the tame coordinates. -/
def tameSingularAxis : Submodule R (M × M) := (⊥ : Submodule R M).prod ⊤

omit [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] in
theorem mem_tameFiniteAxis {x : M × M} : x ∈ tameFiniteAxis R M ↔ x.2 = 0 := by
  simp [tameFiniteAxis, Submodule.mem_prod]

omit [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] in
theorem mem_tameSingularAxis {x : M × M} : x ∈ tameSingularAxis R M ↔ x.1 = 0 := by
  simp [tameSingularAxis, Submodule.mem_prod]

/-- The finite derivative condition: a cocycle vanishing on inertia has tame coordinates on the
finite axis. -/
theorem tameCoord_mem_finiteAxis (I : Subgroup G) (φ σ : G) (hσ : σ ∈ I) (z : Cocycles R G M)
    (hz : ∀ h ∈ I, evalOne R M h z = 0) : tameCoord φ σ z ∈ tameFiniteAxis R M :=
  mem_tameFiniteAxis.mpr (hz σ hσ)

/-- The singular derivative condition: a cocycle vanishing at the Frobenius lift has tame
coordinates on the singular axis. -/
theorem tameCoord_mem_singularAxis (φ σ : G) (z : Cocycles R G M)
    (hz : evalOne R M φ z = 0) : tameCoord φ σ z ∈ tameSingularAxis R M :=
  mem_tameSingularAxis.mpr hz

end TameCoordinates

/-! ### The actual unramified condition in tame coordinates -/

section Unramified

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {R : Type} [CommRing R] [TopologicalSpace R]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} R H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[R] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)

/-- The cocycle of the unramified quotient vanishes at the identity. -/
theorem urCocycle_one (x : X.V) : urCocycle e X x 1 = 0 := by
  have h := urCocycle_cocycle e X x 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_add.mp h

include hf in
/-- The degree-one cochains of the actual unramified condition are cocycles. -/
theorem urLin₁_mem_cocycles (x : X.V) :
    ((contSubCx R G M).ofSub (urLin₁ e π X f x) : (contCochains R G M).X 1) ∈
      Cocycles R G M := by
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := R) (G := G) (M := M) 1
    ((contSubCx R G M).ofSub (urLin₁ e π X f x)) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • f (urCocycle e X x (π (g 1))) +
    ((-1 : R) ^ (0 + 1) • f (urCocycle e X x (π (g 0 * g 1))) +
      (-1 : R) ^ (1 + 1) • f (urCocycle e X x (π (g 0)))) = 0
  rw [map_mul, urCocycle_cocycle, map_add, hf]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

/-- The actual unramified condition in degree one, as a map into the one-cocycles. -/
def urCondCocycle : X.V →ₗ[R] Cocycles R G M where
  toFun x := ⟨(contSubCx R G M).ofSub (urLin₁ e π X f x), urLin₁_mem_cocycles e π X f hf x⟩
  map_add' x y := Subtype.ext (map_add (urLin₁ e π X f) x y)
  map_smul' c x := Subtype.ext (map_smul (urLin₁ e π X f) c x)

/-- **The actual unramified condition has tame coordinates `(x, 0)`**: at a Frobenius lift
`φ` (`π φ = Frob`) and an inertia element `σ` (`π σ = 1`), the inflated cocycle of `x` takes the
value `f x` at `φ` and `0` at `σ`. -/
theorem tameCoord_urCondCocycle (φ σ : G) (hφ : π φ = frobElt e) (hσ : π σ = 1) (x : X.V) :
    tameCoord φ σ (urCondCocycle e π X f hf x) = (f x, 0) := by
  rw [tameCoord_apply]
  refine Prod.ext ?_ ?_
  · change f (urCocycle e X x (π φ)) = f x
    rw [hφ, urCocycle_frob]
  · change f (urCocycle e X x (π σ)) = 0
    rw [hσ, urCocycle_one, map_zero]

/-- The image of the actual unramified condition in tame coordinates is contained in the finite
axis, and equals it when the coefficient map is onto. -/
theorem tameCoord_urCond_range (φ σ : G) (hφ : π φ = frobElt e) (hσ : π σ = 1) :
    LinearMap.range (tameCoord φ σ ∘ₗ urCondCocycle e π X f hf) ≤ tameFiniteAxis R M ∧
      (Function.Surjective f →
        LinearMap.range (tameCoord φ σ ∘ₗ urCondCocycle e π X f hf) = tameFiniteAxis R M) := by
  have hle : LinearMap.range (tameCoord φ σ ∘ₗ urCondCocycle e π X f hf) ≤
      tameFiniteAxis R M := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.comp_apply, tameCoord_urCondCocycle e π X f hf φ σ hφ hσ]
    exact mem_tameFiniteAxis.mpr rfl
  refine ⟨hle, fun hsurj => le_antisymm hle ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y.1
  refine ⟨x, ?_⟩
  rw [LinearMap.comp_apply, tameCoord_urCondCocycle e π X f hf φ σ hφ hσ, hx]
  exact Prod.ext rfl (mem_tameFiniteAxis.mp hy).symm

end Unramified

/-! ### Tame characters at level `n`: the tame coordinates are onto -/

section TameKummer

open TauCeti ValuativeRel IntermediateField
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {K : Type} [Field K] {n : ℕ}

/-- A multiple of the exponent does not change an `n`-torsion element's multiples. -/
theorem nsmul_mod_eq_of {M : Type} [AddCommGroup M] {x : M} (hx : n • x = 0) (a : ℕ) :
    (a % n) • x = a • x := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [add_nsmul, mul_nsmul, hx, nsmul_zero, zero_add]

/-- When `G_K` fixes the `n`-th roots of unity, the Kummer value of an `n`-th root is
multiplicative on all of `G_K`. -/
theorem kummerVal_mul_of_fixed {a : K} {β : AlgebraicClosure K}
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hμ : ∀ (g : Gal(AlgebraicClosure K/K)) (ζ : AlgebraicClosure K), ζ ^ n = 1 → g ζ = ζ)
    (g h : Gal(AlgebraicClosure K/K)) :
    kummerVal β (g * h) = kummerVal β g * kummerVal β h := by
  have hh : h β = kummerVal β h * β := apply_eq_kummerVal_mul hβ0 h
  have hg := hμ g _ (kummerVal_pow hβ hβ0 h)
  have e : (g * h) β = kummerVal β h * g β := by
    rw [AlgEquiv.mul_apply, hh, map_mul, hg]
  change (g * h) β / β = g β / β * kummerVal β h
  rw [e]
  ring

variable [NeZero n]

/-- The discrete logarithm of the Kummer value, in base a primitive Kummer value. -/
def kummerLog {a : K} {β : AlgebraicClosure K} (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a)
    (hβ0 : β ≠ 0) {σ₀ : Gal(AlgebraicClosure K/K)} (hζ : IsPrimitiveRoot (kummerVal β σ₀) n)
    (g : Gal(AlgebraicClosure K/K)) : ZMod n :=
  ((Classical.choose (hζ.eq_pow_of_pow_eq_one (kummerVal_pow hβ hβ0 g)) : ℕ) : ZMod n)

theorem pow_kummerLog {a : K} {β : AlgebraicClosure K}
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {σ₀ : Gal(AlgebraicClosure K/K)} (hζ : IsPrimitiveRoot (kummerVal β σ₀) n)
    (g : Gal(AlgebraicClosure K/K)) :
    kummerVal β σ₀ ^ (kummerLog hβ hβ0 hζ g).val = kummerVal β g := by
  have hs := Classical.choose_spec (hζ.eq_pow_of_pow_eq_one (kummerVal_pow hβ hβ0 g))
  unfold kummerLog
  rw [ZMod.val_natCast_of_lt hs.1]
  exact hs.2

theorem kummerLog_eq_iff {a : K} {β : AlgebraicClosure K}
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {σ₀ : Gal(AlgebraicClosure K/K)} (hζ : IsPrimitiveRoot (kummerVal β σ₀) n)
    (g : Gal(AlgebraicClosure K/K)) (k : ZMod n) :
    kummerLog hβ hβ0 hζ g = k ↔ kummerVal β σ₀ ^ k.val = kummerVal β g := by
  constructor
  · rintro rfl
    exact pow_kummerLog hβ hβ0 hζ g
  · intro hk
    apply ZMod.val_injective
    exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((pow_kummerLog hβ hβ0 hζ g).trans hk.symm)

/-- The tame character is additive when `G_K` fixes the `n`-th roots of unity. -/
theorem kummerLog_mul {a : K} {β : AlgebraicClosure K}
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {σ₀ : Gal(AlgebraicClosure K/K)} (hζ : IsPrimitiveRoot (kummerVal β σ₀) n)
    (hμ : ∀ (g : Gal(AlgebraicClosure K/K)) (ζ : AlgebraicClosure K), ζ ^ n = 1 → g ζ = ζ)
    (g h : Gal(AlgebraicClosure K/K)) :
    kummerLog hβ hβ0 hζ (g * h) = kummerLog hβ hβ0 hζ g + kummerLog hβ hβ0 hζ h := by
  rw [kummerLog_eq_iff, ZMod.val_add]
  have hmod := pow_mod_orderOf (kummerVal β σ₀)
    ((kummerLog hβ hβ0 hζ g).val + (kummerLog hβ hβ0 hζ h).val)
  rw [← hζ.eq_orderOf] at hmod
  rw [hmod, pow_add, pow_kummerLog, pow_kummerLog, kummerVal_mul_of_fixed hβ hβ0 hμ]

theorem kummerLog_of_fix {a : K} {β : AlgebraicClosure K}
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {σ₀ : Gal(AlgebraicClosure K/K)} (hζ : IsPrimitiveRoot (kummerVal β σ₀) n)
    {g : Gal(AlgebraicClosure K/K)} (hg : g β = β) : kummerLog hβ hβ0 hζ g = 0 := by
  rw [kummerLog_eq_iff, ZMod.val_zero, pow_zero]
  change 1 = g β / β
  rw [hg, div_self hβ0]

theorem kummerLog_self [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {σ₀ : Gal(AlgebraicClosure K/K)} (hζ : IsPrimitiveRoot (kummerVal β σ₀) n) :
    kummerLog hβ hβ0 hζ σ₀ = 1 := by
  rw [kummerLog_eq_iff, ZMod.val_one, pow_one]

/-- The tame character is continuous: it is trivial on the open fixing subgroup of `K(β)`. -/
theorem continuous_kummerLog {a : K} {β : AlgebraicClosure K}
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    {σ₀ : Gal(AlgebraicClosure K/K)} (hζ : IsPrimitiveRoot (kummerVal β σ₀) n)
    (hμ : ∀ (g : Gal(AlgebraicClosure K/K)) (ζ : AlgebraicClosure K), ζ ^ n = 1 → g ζ = ζ) :
    Continuous (kummerLog hβ hβ0 hζ) := by
  let f : Gal(AlgebraicClosure K/K) →* Multiplicative (ZMod n) :=
    { toFun := fun g => Multiplicative.ofAdd (kummerLog hβ hβ0 hζ g)
      map_one' := by
        rw [kummerLog_of_fix hβ hβ0 hζ (AlgEquiv.one_apply β)]
        rfl
      map_mul' := fun g h => by rw [kummerLog_mul hβ hβ0 hζ hμ, ofAdd_add] }
  have : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  have hopen := IntermediateField.fixingSubgroup_isOpen K⟮β⟯
  have hf : ContinuousAt f 1 := by
    refine (continuousAt_const (y := (1 : Multiplicative (ZMod n)))).congr ?_
    filter_upwards [hopen.mem_nhds (K⟮β⟯).fixingSubgroup.one_mem] with g hg
    have hgβ : g β = β := hg ⟨β, IntermediateField.mem_adjoin_simple_self K β⟩
    change (1 : Multiplicative (ZMod n)) = Multiplicative.ofAdd (kummerLog hβ hβ0 hζ g)
    rw [kummerLog_of_fix hβ hβ0 hζ hgβ]
    rfl
  exact (continuous_of_discreteTopology
    (f := (Multiplicative.toAdd : Multiplicative (ZMod n) → ZMod n))).comp
    (continuous_of_continuousAt_one f hf)

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K n) in
/-- The unramified character at level `n`: the `ℤ̂`-coordinate of the restriction to `K^ur`,
modulo `n`. -/
def urCharN (g : Gal(AlgebraicClosure K/K)) : ZMod n :=
  Multiplicative.toAdd ((zHat.lift (Multiplicative.ofAdd (1 : ZMod n)) :
    zHat →ₜ* Multiplicative (ZMod n))
    (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
      (restrictMaximalUnramifiedHom K g)))

theorem urCharN_mul (g h : Gal(AlgebraicClosure K/K)) :
    urCharN K n (g * h) = urCharN K n g + urCharN K n h := by
  simp only [urCharN]
  rw [show restrictMaximalUnramifiedHom K (g * h) =
    restrictMaximalUnramifiedHom K g * restrictMaximalUnramifiedHom K h from map_mul _ _ _,
    map_mul, map_mul, toAdd_mul]

theorem continuous_urCharN : Continuous (urCharN K n) :=
  (continuous_of_discreteTopology
    (f := (Multiplicative.toAdd : Multiplicative (ZMod n) → ZMod n))).comp
    ((zHat.lift (Multiplicative.ofAdd (1 : ZMod n))).continuous.comp
      ((maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).continuous.comp
        (continuous_restrictMaximalUnramifiedHom K)))

theorem urCharN_frobenius {φ : Gal(AlgebraicClosure K/K)} (hφ : IsArithFrobeniusLift K φ) :
    urCharN K n φ = 1 := by
  simp only [urCharN]
  rw [show restrictMaximalUnramifiedHom K φ = maximalUnramifiedFrobenius K (AlgebraicClosure K)
    from hφ, maximalUnramifiedGaloisGroupEquivZHat_apply_frobenius, zHat.lift_gen, toAdd_ofAdd]

theorem urCharN_inertia {g : Gal(AlgebraicClosure K/K)} (hg : g ∈ inertiaSubgroup K) :
    urCharN K n g = 0 := by
  have hk : restrictMaximalUnramifiedHom K g = 1 := by
    rw [← ker_restrictMaximalUnramifiedHom] at hg
    exact hg
  simp only [urCharN, hk]
  rw [show (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)) 1 = 1 from map_one _,
    show ((zHat.lift (Multiplicative.ofAdd (1 : ZMod n)) : zHat →ₜ* Multiplicative (ZMod n))) 1 = 1
      from map_one _]
  rfl

/-- **The tame coordinates of the actual local cohomology are onto** at level `n`: for a
nonarchimedean local field whose absolute Galois group fixes the `n`-th roots of unity (`n` prime
to the residue characteristic, `n > 1`), and a discrete coefficient module with trivial action
killed by `n`, there are a Frobenius lift `φ` and an inertia element `σ` for which every pair
`(x, m)` is the tame coordinate pair of an actual continuous one-cocycle, namely
`g ↦ u(g) x + κ(g) m` with the unramified character `u` and the tame Kummer character `κ`. -/
theorem exists_tameCoord_surjective [Fact (1 < n)] (hn : n.Coprime (ringChar 𝓀[K]))
    (hμ : ∀ (g : Gal(AlgebraicClosure K/K)) (ζ : AlgebraicClosure K), ζ ^ n = 1 → g ζ = ζ)
    {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    [DistribMulAction Gal(AlgebraicClosure K/K) M] [SMulCommClass Gal(AlgebraicClosure K/K) R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousAdd M]
    [ContinuousSMul Gal(AlgebraicClosure K/K) M]
    (htriv : ∀ (g : Gal(AlgebraicClosure K/K)) (m : M), g • m = m)
    (hnM : ∀ m : M, n • m = 0) :
    ∃ φ σ : Gal(AlgebraicClosure K/K), IsArithFrobeniusLift K φ ∧ σ ∈ inertiaSubgroup K ∧
      Function.Surjective (tameCoord (R := R) (M := M) φ σ) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  have hπv : (normalizedValuation K (Units.mk0 (π : K) π.ne_zero)).toAdd = 1 := by
    rw [show Units.mk0 (π : K) π.ne_zero = π from Units.ext rfl, (isUniformizer_def π).1 hπ,
      toAdd_ofAdd]
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (π : K))
    (Nat.pos_of_ne_zero (NeZero.ne n))
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne n)] at hβ
    exact π.ne_zero ((map_eq_zero _).1 hβ.symm)
  obtain ⟨σ, hσI, hζ⟩ := exists_tame_generator hn hβ hβ0 π.ne_zero hπv
  obtain ⟨φ, hφF, hφβ⟩ := exists_frobeniusLift_fix hn hβ hβ0 π.ne_zero hπv
  refine ⟨φ, σ, hφF, hσI, ?_⟩
  rintro ⟨x, m⟩
  let F : Gal(AlgebraicClosure K/K) → M := fun g =>
    (urCharN K n g).val • x + (kummerLog hβ hβ0 hζ g).val • m
  have hFmul : ∀ g h, F (g * h) = F g + F h := by
    intro g h
    simp only [F, urCharN_mul, kummerLog_mul hβ hβ0 hζ hμ, ZMod.val_add,
      nsmul_mod_eq_of (hnM x), nsmul_mod_eq_of (hnM m), add_nsmul]
    abel
  have hFc : Continuous fun g : Fin 1 → Gal(AlgebraicClosure K/K) => F (g 0) :=
    ((continuous_of_discreteTopology (f := fun p : ZMod n × ZMod n => p.1.val • x + p.2.val • m)).comp
      ((continuous_urCharN (K := K) (n := n)).prodMk
        (continuous_kummerLog hβ hβ0 hζ hμ))).comp (continuous_apply 0)
  let c : (contCochains R Gal(AlgebraicClosure K/K) M).X 1 :=
    (contSubCx R Gal(AlgebraicClosure K/K) M).ofSub
      ⟨(fun g : Fin 1 → Gal(AlgebraicClosure K/K) => F (g 0)), hFc⟩
  have hc : c ∈ Cocycles R Gal(AlgebraicClosure K/K) M := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    funext g
    have h1 := contCochains_d_apply (k := R) (G := Gal(AlgebraicClosure K/K)) (M := M) 1 c g
    refine h1.trans ?_
    rw [Fin.sum_univ_two]
    change g 0 • F (g 1) + ((-1 : R) ^ (0 + 1) • F (g 0 * g 1) + (-1 : R) ^ (1 + 1) • F (g 0)) = 0
    rw [htriv, hFmul]
    simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
      one_smul]
    abel
  refine ⟨⟨c, hc⟩, ?_⟩
  rw [tameCoord_apply]
  refine Prod.ext ?_ ?_
  · change F φ = x
    simp only [F, urCharN_frobenius hφF, ZMod.val_one, one_smul,
      kummerLog_of_fix hβ hβ0 hζ hφβ, ZMod.val_zero, zero_smul, add_zero]
  · change F σ = m
    simp only [F, urCharN_inertia hσI, ZMod.val_zero, zero_smul, kummerLog_self hβ hβ0 hζ,
      ZMod.val_one, one_smul, zero_add]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [NeZero n] in
/-- **At a prime of a number field not dividing `2`, the tame coordinates of the actual local
cohomology at precision `2^i` are onto**: if the local Galois group fixes the `2^i`-th roots of
unity, every pair `(x, m)` of a discrete module with trivial action killed by `2^i` is the tame
coordinate pair of an actual continuous one-cocycle of `G_{K_q}`. -/
theorem exists_tameCoord_surjective_at {K₀ : Type} [Field K₀] [NumberField K₀]
    (q : HeightOneSpectrum (𝓞 K₀)) (h2 : (2 : 𝓞 K₀) ∉ q.asIdeal) {i : ℕ} (hi : i ≠ 0)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K₀)/q.adicCompletion K₀))
      (ζ : AlgebraicClosure (q.adicCompletion K₀)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    [DistribMulAction Gal(AlgebraicClosure (q.adicCompletion K₀)/q.adicCompletion K₀) M]
    [SMulCommClass Gal(AlgebraicClosure (q.adicCompletion K₀)/q.adicCompletion K₀) R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousAdd M]
    [ContinuousSMul Gal(AlgebraicClosure (q.adicCompletion K₀)/q.adicCompletion K₀) M]
    (htriv : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K₀)/q.adicCompletion K₀)) (m : M),
      g • m = m) (hnM : ∀ m : M, (2 ^ i) • m = 0) :
    ∃ φ σ : Gal(AlgebraicClosure (q.adicCompletion K₀)/q.adicCompletion K₀),
      IsArithFrobeniusLift (q.adicCompletion K₀) φ ∧
      σ ∈ inertiaSubgroup (q.adicCompletion K₀) ∧
      Function.Surjective (tameCoord (R := R) (M := M) φ σ) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi⟩
  have hp : (ringChar 𝓀[q.adicCompletion K₀]).Prime :=
    (CharP.char_is_prime_or_zero 𝓀[q.adicCompletion K₀] _).resolve_right
      (CharP.char_ne_zero_of_finite 𝓀[q.adicCompletion K₀] _)
  have hnd : ¬ ringChar 𝓀[q.adicCompletion K₀] ∣ 2 := by
    rw [IsDedekindDomain.HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
    exact_mod_cast h2
  have hcop : (2 ^ i).Coprime (ringChar 𝓀[q.adicCompletion K₀]) :=
    Nat.Coprime.pow_left i ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  exact exists_tameCoord_surjective (K := q.adicCompletion K₀) (n := 2 ^ i) hcop hμ htriv hnM

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [NeZero n] in
open ZInQ.Manuscript.RC.Limits hiding Lambda in
open ZInQ.Manuscript.RC.Uniform (Lambda) in
/-- **The inner-limit local model is realized by actual local cohomology in both planes**: for
local fields `K_i` at the coefficient stages whose Galois groups fix the `2^i`-th roots of unity
(`2^i` prime to the residue characteristics), and stage coefficient modules `M_i ≅ (Λ/I_i)²` with
trivial action, there are Frobenius lifts and inertia elements for which every limiting coordinate
pair, finite and singular, is the coefficient-stage limit of the tame coordinates of actual
continuous one-cocycles. -/
theorem innerLimit_local_surjective {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (K : ℕ → Type) [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)]
    [∀ i, IsNonarchimedeanLocalField (K i)]
    (hn : ∀ i, i ≠ 0 → (2 ^ i).Coprime (ringChar 𝓀[K i]))
    (hμ : ∀ i, i ≠ 0 → ∀ (g : Gal(AlgebraicClosure (K i)/K i)) (ζ : AlgebraicClosure (K i)),
      ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (Lambda ⧸ stageIdeal i) (M i)]
    [∀ i, DistribMulAction Gal(AlgebraicClosure (K i)/K i) (M i)]
    [∀ i, SMulCommClass Gal(AlgebraicClosure (K i)/K i) (Lambda ⧸ stageIdeal i) (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, DiscreteTopology (M i)] [∀ i, ContinuousAdd (M i)]
    [∀ i, ContinuousSMul Gal(AlgebraicClosure (K i)/K i) (M i)]
    (htriv : ∀ i (g : Gal(AlgebraicClosure (K i)/K i)) (m : M i), g • m = m)
    (e : ∀ i, M i ≃ₗ[Lambda ⧸ stageIdeal i] Vec2 (Lambda ⧸ stageIdeal i)) :
    ∃ (φ σ : ∀ i, Gal(AlgebraicClosure (K i)/K i)),
      (∀ i, IsArithFrobeniusLift (K i) (φ i) ∧ σ i ∈ inertiaSubgroup (K i)) ∧
      ∀ y : Coords Lambda, ∃ z : ∀ i,
        Cocycles (Lambda ⧸ stageIdeal i) Gal(AlgebraicClosure (K i)/K i) (M i),
        stageLimit stageIdeal_tendsToZero hU (fun i =>
          (e i (tameCoord (φ i) (σ i) (z i)).1, e i (tameCoord (φ i) (σ i) (z i)).2)) = y := by
  have hst : ∀ i, ∃ φ σ : Gal(AlgebraicClosure (K i)/K i), IsArithFrobeniusLift (K i) φ ∧
      σ ∈ inertiaSubgroup (K i) ∧
      Function.Surjective (tameCoord (R := Lambda ⧸ stageIdeal i) (M := M i) φ σ) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      obtain ⟨φ, hφ⟩ := exists_isArithFrobeniusLift (K 0)
      refine ⟨φ, 1, hφ, (inertiaSubgroup (K 0)).one_mem, ?_⟩
      have htop : stageIdeal 0 = ⊤ := by
        rw [Ideal.eq_top_iff_one]
        have h1 := Ideal.subset_span (Set.mem_insert ((2 : Lambda) ^ 0)
          {(PowerSeries.X : Lambda) ^ 0})
        rwa [pow_zero] at h1
      have : Subsingleton (Lambda ⧸ stageIdeal 0) := Ideal.Quotient.subsingleton_iff.mpr htop
      have : Subsingleton (M 0) := Module.subsingleton (Lambda ⧸ stageIdeal 0) (M 0)
      intro y
      exact ⟨0, Subsingleton.elim _ _⟩
    · have : NeZero (2 ^ i) := ⟨pow_ne_zero _ two_ne_zero⟩
      have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi⟩
      have hnM : ∀ m : M i, (2 ^ i) • m = 0 := by
        intro m
        rw [← Nat.cast_smul_eq_nsmul (Lambda ⧸ stageIdeal i)]
        have h0 : ((2 ^ i : ℕ) : Lambda ⧸ stageIdeal i) = 0 := by
          rw [Nat.cast_pow, Nat.cast_ofNat,
            ← map_ofNat (Ideal.Quotient.mk (stageIdeal i)) 2, ← map_pow,
            Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (Set.mem_insert _ _)
        rw [h0]
        exact zero_smul (Lambda ⧸ stageIdeal i) m
      exact exists_tameCoord_surjective (hn i hi) (hμ i hi) (htriv i) hnM
  choose φ σ hφ hσ hsurj using hst
  refine ⟨φ, σ, fun i => ⟨hφ i, hσ i⟩, fun y => ?_⟩
  obtain ⟨s, rfl⟩ := stageLimit_surjective stageIdeal_tendsToZero hU y
  choose z hz using fun i => hsurj i ((e i).symm (s i).1, (e i).symm (s i).2)
  refine ⟨z, ?_⟩
  congr 1
  funext i
  rw [hz i]
  simp

end TameKummer

/-! ### Localization at a prime outside `S` -/

section NewPrime

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The Frobenius at a prime `q` outside `S`, as an element of `G_{K,S}`, for a factorization of
the localization through `Gal(K_q^ur/K_q)`. -/
def frobAt {q : HeightOneSpectrum (𝓞 K)} (ψ : GUr K q →ₜ* GKS K S) : GKS K S :=
  ψ (frobElt (eUr K q))

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul (GKS K S) M]

/-- Localization of continuous one-cochains at a prime `q`: restriction along `G_{K_q} → G_{K,S}`. -/
abbrev localize (q : HeightOneSpectrum (𝓞 K)) :
    (contCochains R (GKS K S) M).X 1 →ₗ[R]
      (contCochains R (Gloc K q) (ResMod (locMap K S q) M)).X 1 :=
  ((resCochains (k := R) (M := M) (locMap K S q)).f 1).hom

/-- The localization of a cochain evaluates through the localization map. -/
theorem evalOne_localize (q : HeightOneSpectrum (𝓞 K)) (z : (contCochains R (GKS K S) M).X 1)
    (g : Gloc K q) :
    evalOne R (ResMod (locMap K S q) M) g (localize K S q z) = evalOne R M (locMap K S q g) z :=
  rfl

/-- Localization sends one-cocycles to one-cocycles. -/
def localizeCocycle (q : HeightOneSpectrum (𝓞 K)) :
    Cocycles R (GKS K S) M →ₗ[R] Cocycles R (Gloc K q) (ResMod (locMap K S q) M) :=
  (localize K S q ∘ₗ (Cocycles R (GKS K S) M).subtype).codRestrict _ fun z => by
    rw [LinearMap.mem_ker]
    have h := congrArg (fun φ => ModuleCat.Hom.hom φ (z : (contCochains R (GKS K S) M).X 1))
      ((resCochains (k := R) (M := M) (locMap K S q)).comm 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [LinearMap.comp_apply, Submodule.coe_subtype, h, LinearMap.mem_ker.mp z.2, map_zero]

variable {K S}

omit [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M] in
/-- Inertia acts trivially on the localized coefficients at a prime outside `S`. -/
theorem inertia_smul_eq {q : HeightOneSpectrum (𝓞 K)} {ψ : GUr K q →ₜ* GKS K S}
    (hψ : ∀ g, locMap K S q g = ψ (urRes K q g)) {σ : Gloc K q} (hσ : urRes K q σ = 1)
    (m : ResMod (locMap K S q) M) : σ • m = m := by
  rw [ResMod.smul_def]
  change locMap K S q σ • (show M from m) = m
  rw [hψ, hσ, map_one, one_smul]

omit [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M] in
/-- A Frobenius lift acts on the localized coefficients as the Frobenius at `q`. -/
theorem frobLift_smul_eq {q : HeightOneSpectrum (𝓞 K)} {ψ : GUr K q →ₜ* GKS K S}
    (hψ : ∀ g, locMap K S q g = ψ (urRes K q g)) {φ : Gloc K q}
    (hφ : urRes K q φ = frobElt (eUr K q)) (m : ResMod (locMap K S q) M) :
    φ • m = (show ResMod (locMap K S q) M from frobAt K S ψ • (show M from m)) := by
  rw [ResMod.smul_def, hψ, hφ]
  rfl

/-- **Localization at a prime outside `S` in tame coordinates**: the finite coordinate of the
localization of a global continuous one-cocycle is its value at the Frobenius, and its singular
coordinate vanishes. -/
theorem tameCoord_localizeCocycle {q : HeightOneSpectrum (𝓞 K)} {ψ : GUr K q →ₜ* GKS K S}
    (hψ : ∀ g, locMap K S q g = ψ (urRes K q g)) {φ σ : Gloc K q}
    (hφ : urRes K q φ = frobElt (eUr K q)) (hσ : urRes K q σ = 1)
    (z : Cocycles R (GKS K S) M) :
    tameCoord φ σ (localizeCocycle K S q z) =
      ((show ResMod (locMap K S q) M from evalOne R M (frobAt K S ψ) z), 0) := by
  rw [tameCoord_apply]
  refine Prod.ext ?_ ?_
  · change evalOne R M (locMap K S q φ) z = evalOne R M (frobAt K S ψ) z
    rw [hψ, hφ]
    rfl
  · change evalOne R M (locMap K S q σ) z = 0
    rw [hψ, hσ, map_one]
    exact evalOne_one z

/-- **The derivative congruence makes the localized class well defined in tame coordinates**:
if the Frobenius at `q` acts trivially on `M`, the tame coordinates of the localization descend
to cohomology, and the class of the localization of `z` has coordinates `(z(Frob_q), 0)`. -/
theorem tameCoordH1_localize {q : HeightOneSpectrum (𝓞 K)} {ψ : GUr K q →ₜ* GKS K S}
    (hψ : ∀ g, locMap K S q g = ψ (urRes K q g)) {φ σ : Gloc K q}
    (hφ : urRes K q φ = frobElt (eUr K q)) (hσ : urRes K q σ = 1)
    (htriv : ∀ m : M, frobAt K S ψ • m = m) (z : Cocycles R (GKS K S) M) :
    tameCoordH1 φ σ (fun m => (frobLift_smul_eq hψ hφ m).trans (htriv m))
        (fun m => inertia_smul_eq hψ hσ m)
        (Submodule.Quotient.mk (localizeCocycle K S q z)) =
      ((show ResMod (locMap K S q) M from evalOne R M (frobAt K S ψ) z), 0) :=
  tameCoord_localizeCocycle hψ hφ hσ z

end NewPrime

/-! ### Moving derivative labels and the inner limit -/

section MovingLabel

open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- `G_{K,S}` is compact. -/
instance gks_compactSpace : CompactSpace (GKS K S) :=
  inferInstanceAs (CompactSpace (GaloisGroupS K S))

/-- `G_{K,S}` is Hausdorff. -/
instance gks_t2Space : T2Space (GKS K S) :=
  inferInstanceAs (T2Space (GaloisGroupS K S))

variable (K S) in
/-- **A moving derivative label**: one prime outside `S` at every coefficient stage, with the
factorization of its localization through the unramified quotient and a Frobenius lift. A
derivative label denotes this sequence of primes, not one place. -/
structure MovingLabel where
  /-- The prime selected at each coefficient stage. -/
  q : ℕ → HeightOneSpectrum (𝓞 K)
  /-- The selected primes lie outside `S`. -/
  notMem : ∀ i, q i ∉ S
  /-- The factorization of the localization through `Gal(K_q^ur/K_q)`. -/
  ψ : ∀ i, GUr K (q i) →ₜ* GKS K S
  hψ : ∀ i g, locMap K S (q i) g = ψ i (urRes K (q i) g)
  /-- A Frobenius lift in the local Galois group. -/
  φ : ∀ i, Gloc K (q i)
  hφ : ∀ i, urRes K (q i) (φ i) = frobElt (eUr K (q i))

/-- **Every sequence of primes outside `S` is a moving label**: the localizations factor through
the unramified quotients because `K_S/K` is unramified outside `S`, and Frobenius lifts exist
because restriction to `K_q^ur` is onto. -/
def MovingLabel.ofPrimes (q : ℕ → HeightOneSpectrum (𝓞 K)) (hq : ∀ i, q i ∉ S) :
    MovingLabel K S where
  q := q
  notMem := hq
  ψ i := Classical.choose (unramifiedAtFactorization K S (q i) (hq i))
  hψ i := Classical.choose_spec (unramifiedAtFactorization K S (q i) (hq i))
  φ i := Classical.choose (urRes_surjective K (q i) (frobElt (eUr K (q i))))
  hφ i := Classical.choose_spec (urRes_surjective K (q i) (frobElt (eUr K (q i))))

theorem MovingLabel.ofPrimes_q (q : ℕ → HeightOneSpectrum (𝓞 K)) (hq : ∀ i, q i ∉ S) :
    (MovingLabel.ofPrimes q hq).q = q :=
  rfl

/-- The Frobenius elements of a moving label, in `G_{K,S}`. -/
def MovingLabel.frob (L : MovingLabel K S) (i : ℕ) : GKS K S := frobAt K S (L.ψ i)

/-- The limit Frobenius of a moving label along the ultrafilter: an actual element of the compact
group `G_{K,S}`. -/
def MovingLabel.limitFrob (L : MovingLabel K S) (U : Ultrafilter ℕ) : GKS K S :=
  ulim U L.frob

theorem MovingLabel.tendsto_limitFrob (L : MovingLabel K S) (U : Ultrafilter ℕ) :
    Tendsto L.frob (U : Filter ℕ) (𝓝 (L.limitFrob U)) :=
  tendsto_ulim U L.frob

variable {W : WeierstrassCurve K} {α : GKS K S →* Lambdaˣ} [W.IsElliptic]
  [HasFullTwoTorsion K S W] [IsContChar α]

variable (W α) in
/-- The continuous one-cocycles of `G_{K,S}` with values in the `Λ`-adic Tate module. -/
abbrev TateCocycles : Submodule Lambda ((contCochains Lambda (GKS K S) (TLam K S W α)).X 1) :=
  Cocycles Lambda (GKS K S) (TLam K S W α)

/-- The coordinates of an element of the localized `Λ`-adic Tate module. -/
def tlamCoords {q : HeightOneSpectrum (𝓞 K)} (x : ResMod (locMap K S q) (TLam K S W α)) :
    Vec2 Lambda :=
  tlamHomeomorph (K := K) (S := S) (W := W) (α := α) (show TLam K S W α from x)

/-- The stage-`i` tame coordinates, in the `Λ`-coordinates of the Tate module, of the localization
of a global cocycle at the prime of a moving label, for a choice of inertia elements `σ`. -/
def stageCoords (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i)) (z : TateCocycles W α) (i : ℕ) :
    Coords Lambda :=
  (tlamCoords (tameCoord (L.φ i) (σ i) (localizeCocycle K S (L.q i) z)).1,
    tlamCoords (tameCoord (L.φ i) (σ i) (localizeCocycle K S (L.q i) z)).2)

/-- **The stage coordinates are the Frobenius values**: at every stage the finite coordinate is
the value of the cocycle at the Frobenius of the stage prime and the singular coordinate is zero,
for every inertia element. -/
theorem stageCoords_eq (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) (z : TateCocycles W α) (i : ℕ) :
    stageCoords L σ z i =
      (tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (L.frob i) z), 0) := by
  unfold stageCoords
  rw [tameCoord_localizeCocycle (L.hψ i) (L.hφ i) (hσ i) z]
  refine Prod.ext rfl ?_
  change tlamHomeomorph (K := K) (S := S) (W := W) (α := α) 0 = 0
  exact map_zero (tlamBasis (K := K) (S := S) (W := W) (α := α)).equivFun

/-- The inner-limit local class of a global `Λ`-adic cocycle at a moving label: the class of its
sequence of stage tame coordinates in the separated completed coordinate product. -/
def innerLocalClass (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i)) (U : Ultrafilter ℕ)
    (z : TateCocycles W α) : CompletedH1 Lambda U :=
  Submodule.Quotient.mk (stageCoords L σ z)

/-- **The inner-limit localization of a global class is evaluation at the limit Frobenius**: the
limiting coordinates of the inner-limit local class are `(z(Frob_∞), 0)`, with `Frob_∞` the
limit Frobenius of the label in `G_{K,S}`. -/
theorem completedEquiv_innerLocalClass (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) (U : Ultrafilter ℕ) (z : TateCocycles W α) :
    completedEquiv (R := Lambda) U (innerLocalClass L σ U z) =
      (tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (L.limitFrob U) z), 0) := by
  rw [innerLocalClass, completedEquiv_mk]
  have hs : stageCoords L σ z = fun i =>
      (tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (L.frob i) z), (0 : Vec2 Lambda)) :=
    funext fun i => stageCoords_eq L σ hσ z i
  rw [hs]
  have hcont : Continuous fun g : GKS K S =>
      tlamHomeomorph (K := K) (S := S) (W := W) (α := α) (evalOne Lambda (TLam K S W α) g z) :=
    (tlamHomeomorph (K := K) (S := S) (W := W) (α := α)).continuous.comp
      (continuous_evalOne (z : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1))
  have ht := (hcont.tendsto (L.limitFrob U)).comp (L.tendsto_limitFrob U)
  refine Prod.ext ?_ ?_
  · exact ulimVec_eq_of_tendsto ht
  · exact ulimVec_zero U

/-- The inner-limit local class of a global class lies in the completed finite plane. -/
theorem innerLocalClass_mem_finite (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) (U : Ultrafilter ℕ) (z : TateCocycles W α) :
    innerLocalClass L σ U z ∈ completedFinite (R := Lambda) U := by
  change completedEquiv (R := Lambda) U (innerLocalClass L σ U z) ∈ finiteAxis Lambda
  rw [completedEquiv_innerLocalClass L σ hσ U z, mem_finiteAxis]

/-- The inner-limit local class does not depend on the choice of inertia elements. -/
theorem innerLocalClass_indep (L : MovingLabel K S) (σ σ' : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) (hσ' : ∀ i, urRes K (L.q i) (σ' i) = 1)
    (U : Ultrafilter ℕ) (z : TateCocycles W α) :
    innerLocalClass L σ U z = innerLocalClass L σ' U z := by
  apply (completedEquiv (R := Lambda) U).injective
  rw [completedEquiv_innerLocalClass L σ hσ U z, completedEquiv_innerLocalClass L σ' hσ' U z]

/-- Only the stage reductions of the Frobenius values matter: two global cocycles whose values at
the stage Frobenius elements agree modulo the stage ideals on a `U`-large set have the same
inner-limit local class. -/
theorem innerLocalClass_eq_of_stage (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (z z' : TateCocycles W α)
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ a,
      tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
          (evalOne Lambda (TLam K S W α) (L.frob i) z) a -
        tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
          (evalOne Lambda (TLam K S W α) (L.frob i) z') a ∈ stageIdeal i) :
    innerLocalClass L σ U z = innerLocalClass L σ U z' := by
  unfold innerLocalClass
  apply completed_mk_eq_of_stage_congruence stageIdeal stageIdeal_tendsToZero hU
  refine h.mono fun i hi => ⟨fun a => ?_, fun a => ?_⟩
  · rw [stageCoords_eq L σ hσ z i, stageCoords_eq L σ hσ z' i]
    exact hi a
  · rw [stageCoords_eq L σ hσ z i, stageCoords_eq L σ hσ z' i]
    simp

omit [IsContChar α] in
/-- The coordinates of an element of `I_i 𝕋` lie in the stage ideal. -/
theorem tlamHomeomorph_mem_stageIdeal {i : ℕ} {x : TLam K S W α} (hx : x ∈ tlamNbhd K S W α i)
    (c : Fin 2) : tlamHomeomorph (K := K) (S := S) (W := W) (α := α) x c ∈ stageIdeal i := by
  rw [tlamHomeomorph_apply]
  refine Submodule.smul_induction_on (p := fun y =>
    (tlamBasis (K := K) (S := S) (W := W) (α := α)).repr y c ∈ stageIdeal i) hx ?_ ?_
  · intro r hr m _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  · intro x y hx hy
    rw [map_add, Finsupp.add_apply]
    exact Ideal.add_mem _ hx hy

variable (W α) in
/-- **Retained stage cocycles**: a continuous `Λ`-adic one-cochain is a cocycle at the precision
of stage `i` when its coboundary takes values in `I_i 𝕋`. -/
def IsStageCocycle (i : ℕ) (z : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) : Prop :=
  ∀ g h : GKS K S, evalOne Lambda (TLam K S W α) (g * h) z -
    (g • evalOne Lambda (TLam K S W α) h z + evalOne Lambda (TLam K S W α) g z) ∈
      tlamNbhd K S W α i

omit [W.IsElliptic] [HasFullTwoTorsion K S W] in
/-- An actual cocycle is a stage cocycle at every precision. -/
theorem isStageCocycle_of_cocycle (z : TateCocycles W α) (i : ℕ) :
    IsStageCocycle W α i (z : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) := by
  intro g h
  rw [evalOne_mul z g h, sub_self]
  exact Submodule.zero_mem _

omit [W.IsElliptic] [HasFullTwoTorsion K S W] in
/-- A stage cocycle takes a value in `I_i 𝕋` at the identity. -/
theorem IsStageCocycle.eval_one_mem {i : ℕ} {z : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1}
    (hz : IsStageCocycle W α i z) :
    evalOne Lambda (TLam K S W α) (1 : GKS K S) z ∈ tlamNbhd K S W α i := by
  have h := hz 1 1
  rw [mul_one, one_smul] at h
  have h' : -evalOne Lambda (TLam K S W α) (1 : GKS K S) z ∈ tlamNbhd K S W α i := by
    convert h using 1
    abel
  simpa using (tlamNbhd K S W α i).neg_mem h'

omit [W.IsElliptic] [HasFullTwoTorsion K S W] in
/-- A one-cochain whose coboundary lies in `I_i C²` is a stage cocycle at precision `i`. -/
theorem isStageCocycle_of_d_mem {i : ℕ} {z : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1}
    (hz : ((contCochains Lambda (GKS K S) (TLam K S W α)).d 1 2).hom z ∈
      (stageIdeal i • ⊤ : Submodule Lambda ((contCochains Lambda (GKS K S) (TLam K S W α)).X 2))) :
    IsStageCocycle W α i z := by
  intro g h
  have hev : evalTwo Lambda (TLam K S W α) g h
      (((contCochains Lambda (GKS K S) (TLam K S W α)).d 1 2).hom z) ∈ tlamNbhd K S W α i := by
    refine Submodule.smul_induction_on (p := fun w =>
      evalTwo Lambda (TLam K S W α) g h w ∈ tlamNbhd K S W α i) hz ?_ ?_
    · intro r hr m _
      rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  rw [evalTwo_d] at hev
  have e : evalOne Lambda (TLam K S W α) (g * h) z -
      (g • evalOne Lambda (TLam K S W α) h z + evalOne Lambda (TLam K S W α) g z) =
      -(g • evalOne Lambda (TLam K S W α) h z - evalOne Lambda (TLam K S W α) (g * h) z +
        evalOne Lambda (TLam K S W α) g z) := by abel
  rw [e]
  exact Submodule.neg_mem _ hev

/-- The stage-`i` tame coordinates of the localization, at the prime of the label, of the stage-`i`
member of a sequence of cochains. -/
def seqStageCoords (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) (i : ℕ) : Coords Lambda :=
  (tlamCoords (evalOne Lambda (ResMod (locMap K S (L.q i)) (TLam K S W α)) (L.φ i)
      (localize K S (L.q i) (z i))),
    tlamCoords (evalOne Lambda (ResMod (locMap K S (L.q i)) (TLam K S W α)) (σ i)
      (localize K S (L.q i) (z i))))

/-- The finite stage coordinate is the value at the Frobenius of the stage prime. -/
theorem seqStageCoords_fst (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) (i : ℕ) :
    (seqStageCoords L σ z i).1 =
      tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (L.frob i) (z i)) := by
  change tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
    (evalOne Lambda (TLam K S W α) (locMap K S (L.q i) (L.φ i)) (z i)) = _
  rw [L.hψ i, L.hφ i]
  rfl

/-- The singular stage coordinate is the value at the identity. -/
theorem seqStageCoords_snd (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) (i : ℕ) :
    (seqStageCoords L σ z i).2 =
      tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (1 : GKS K S) (z i)) := by
  change tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
    (evalOne Lambda (TLam K S W α) (locMap K S (L.q i) (σ i)) (z i)) = _
  rw [L.hψ i, hσ i, map_one]

/-- The inner-limit local class at a moving label of a sequence of retained stage cocycles. -/
def innerLocalClassSeq (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i)) (U : Ultrafilter ℕ)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) : CompletedH1 Lambda U :=
  Submodule.Quotient.mk (seqStageCoords L σ z)

/-- **The inner-limit localization of retained stage cocycles**: the class is that of the
sequence of Frobenius values on the finite axis; the singular coordinates vanish at the retained
precision. -/
theorem innerLocalClassSeq_eq (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hz : ∀ i, IsStageCocycle W α i (z i)) :
    innerLocalClassSeq L σ U z = Submodule.Quotient.mk (fun i =>
      (tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (L.frob i) (z i)), (0 : Vec2 Lambda))) := by
  apply completed_mk_eq_of_stage_congruence stageIdeal stageIdeal_tendsToZero hU
  refine Eventually.of_forall fun i => ⟨fun a => ?_, fun a => ?_⟩
  · rw [seqStageCoords_fst, sub_self]
    exact Submodule.zero_mem _
  · rw [seqStageCoords_snd L σ hσ z i]
    simp only [Pi.zero_apply, sub_zero]
    exact tlamHomeomorph_mem_stageIdeal (hz i).eval_one_mem a

/-- The limiting coordinates of the inner-limit local class of retained stage cocycles are the
ultralimit of their Frobenius values, on the finite axis. -/
theorem completedEquiv_innerLocalClassSeq (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hz : ∀ i, IsStageCocycle W α i (z i)) :
    completedEquiv (R := Lambda) U (innerLocalClassSeq L σ U z) =
      (ulimVec U (fun i => tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (L.frob i) (z i))), 0) := by
  rw [innerLocalClassSeq_eq L σ hσ hU z hz, completedEquiv_mk]
  exact Prod.ext rfl (ulimVec_zero U)

/-- The inner-limit local class of retained stage cocycles lies in the completed finite plane. -/
theorem innerLocalClassSeq_mem_finite (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)
    (hz : ∀ i, IsStageCocycle W α i (z i)) :
    innerLocalClassSeq L σ U z ∈ completedFinite (R := Lambda) U := by
  change completedEquiv (R := Lambda) U (innerLocalClassSeq L σ U z) ∈ finiteAxis Lambda
  rw [completedEquiv_innerLocalClassSeq L σ hσ hU z hz, mem_finiteAxis]

/-- For a constant sequence of an actual cocycle the two constructions agree. -/
theorem innerLocalClassSeq_const (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i))
    (U : Ultrafilter ℕ) (z : TateCocycles W α) :
    innerLocalClassSeq L σ U (fun _ => (z : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)) =
      innerLocalClass L σ U z :=
  rfl

end MovingLabel

/-! ### The relaxed localization image of the limit diagram and detection -/

section LimitImage

open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.Uniform (finPlane mem_finPlane)

variable {k : Type} [Field k]

/-- On a complex concentrated in degree one, the coordinate of the class of a cocycle is the
cocycle. -/
theorem h1Equiv_clsAt (W : GCx k) (hW : ConcDegOne W) (x : LinearMap.ker (W.d 1 2 rfl)) :
    h1Equiv W hW (clsAt W 1 2 rfl x) = x.1 := by
  rw [h1Equiv_apply]
  have h := congrArg (fun f => ModuleCat.Hom.hom f
    ((liftCycAt W.toCC 1 2 rfl).hom (kerToCC W 1 2 rfl x))) (homologyπ_h1Iso W hW)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change (h1Iso W hW).hom.hom ((W.toCC.homologyπ 1).hom
    ((liftCycAt W.toCC 1 2 rfl).hom (kerToCC W 1 2 rfl x))) = x.1
  rw [h]
  exact iCycles_clsAt W 1 2 rfl x

variable (G : GCx k) (res : GHom G (splitLocalComplex k))

/-- **The relaxed localization image of the limit diagram is the localization of the global
one-cycles**: `U = res¹(Z¹(G))`. -/
theorem limitRelaxed_U_eq :
    (limitRelaxed G res).U = (LinearMap.ker (G.d 1 2 rfl)).map (res.f 1 1 rfl) := by
  apply le_antisymm
  · rintro _ ⟨w, ⟨v, rfl⟩, rfl⟩
    obtain ⟨z, rfl⟩ := clsAt_surjective (selCx (limitRelaxed G res).D) 1 2 rfl v
    have hq := homologyMap_clsAt (quotMap (limitRelaxed G res).D (limitRelaxed G res).gR) 1 2 rfl
      z (by exact LinearMap.mem_ker.mpr rfl)
    have hG := congrArg (fun c : selT (limitRelaxed G res).D 2 => c.1) z.2
    have hL := congrArg (fun c : selT (limitRelaxed G res).D 2 => c.2.2) z.2
    change (show Coords k from res.f 1 1 rfl z.1.1) -
      ((show ↥(⊤ : Submodule k (Coords k)) from z.1.2.1) : Coords k) - 0 = 0 at hL
    rw [sub_zero, sub_eq_zero] at hL
    have hval : (limitRelaxed G res).eR ((HomologicalComplex.homologyMap
        (GHom.toCC (quotMap (limitRelaxed G res).D (limitRelaxed G res).gR)) 1).hom
          (clsAt (selCx (limitRelaxed G res).D) 1 2 rfl z)) =
        (show Coords k from res.f 1 1 rfl z.1.1) := by
      rw [hq]
      exact (h1Equiv_clsAt (oneComplex k (Coords k)) (oneComplex_concentrated _) _).trans hL.symm
    exact ⟨z.1.1, hG, hval.symm⟩
  · rintro _ ⟨a, ha, rfl⟩
    let c : (selCx (limitRelaxed G res).D).X 1 :=
      ((a, (⟨res.f 1 1 rfl a, Submodule.mem_top⟩ : ↥(⊤ : Submodule k (Coords k))),
        (0 : Vec2 k)) : selT (limitRelaxed G res).D 1)
    have hc : c ∈ LinearMap.ker ((selCx (limitRelaxed G res).D).d 1 2 rfl) := by
      refine LinearMap.mem_ker.mpr (Prod.ext ha (Prod.ext rfl ?_))
      change (show Coords k from res.f 1 1 rfl a) - (show Coords k from res.f 1 1 rfl a) -
        (0 : Coords k) = 0
      rw [sub_zero]
      exact sub_self _
    have hq := homologyMap_clsAt (quotMap (limitRelaxed G res).D (limitRelaxed G res).gR) 1 2 rfl
      ⟨c, hc⟩ (by exact LinearMap.mem_ker.mpr rfl)
    have hval : (limitRelaxed G res).eR ((HomologicalComplex.homologyMap
        (GHom.toCC (quotMap (limitRelaxed G res).D (limitRelaxed G res).gR)) 1).hom
          (clsAt (selCx (limitRelaxed G res).D) 1 2 rfl ⟨c, hc⟩)) =
        (show Coords k from res.f 1 1 rfl a) := by
      rw [hq]
      exact h1Equiv_clsAt (oneComplex k (Coords k)) (oneComplex_concentrated _) _
    exact ⟨_, ⟨clsAt (selCx (limitRelaxed G res).D) 1 2 rfl ⟨c, hc⟩, rfl⟩, hval⟩

/-- The finite coordinates of the global one-cycles that localize into the finite plane. -/
def finiteDetections : Set (Vec2 k) :=
  {f | ∃ a ∈ LinearMap.ker (G.d 1 2 rfl), res.f 1 1 rfl a = (f, (0 : Vec2 k))}

/-- **Detection by global cycles**: if the finite coordinates of the global one-cycles localizing
into the finite plane span `k²`, the relaxed localization image contains the finite plane. -/
theorem finPlane_le_limitRelaxed_U_of_span
    (hspan : Submodule.span k (finiteDetections G res) = ⊤) :
    finPlane k (Vec2 k) (Vec2 k) ≤ (limitRelaxed G res).U := by
  rw [limitRelaxed_U_eq]
  have hle : Submodule.span k (finiteDetections G res) ≤
      ((LinearMap.ker (G.d 1 2 rfl)).map (res.f 1 1 rfl)).comap (LinearMap.inl k (Vec2 k) (Vec2 k)) := by
    rw [Submodule.span_le]
    rintro f ⟨a, ha, hf⟩
    exact ⟨a, ha, hf⟩
  rw [hspan] at hle
  intro x hx
  have hx2 : x.2 = 0 := mem_finPlane.mp hx
  have hmem := hle (Submodule.mem_top : x.1 ∈ (⊤ : Submodule k (Vec2 k)))
  have hxe : LinearMap.inl k (Vec2 k) (Vec2 k) x.1 = x := Prod.ext rfl hx2.symm
  have hm := Submodule.mem_comap.mp hmem
  rwa [hxe] at hm

/-- **Rank-two detection by two global cycles**: two global one-cycles localizing into the finite
plane with linearly independent finite coordinates give the detection field `F ≤ U`. -/
theorem finPlane_le_limitRelaxed_U {a b : G.X 1} (ha : G.d 1 2 rfl a = 0) (hb : G.d 1 2 rfl b = 0)
    {fa fb : Vec2 k} (hra : res.f 1 1 rfl a = (fa, 0)) (hrb : res.f 1 1 rfl b = (fb, 0))
    (hdet : (Matrix.of ![fa, fb]).det ≠ 0) :
    finPlane k (Vec2 k) (Vec2 k) ≤ (limitRelaxed G res).U := by
  apply finPlane_le_limitRelaxed_U_of_span
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp)
  apply top_unique
  rw [← hsp, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  fin_cases i
  · exact ⟨a, ha, hra⟩
  · exact ⟨b, hb, hrb⟩

/-- **The detecting pair can contain any class with nonzero finite localization**: when the
finite detections span `k²`, every nonzero detected coordinate has a detected partner with
nonzero determinant. This is the form in which the primitive class enters the selection. -/
theorem exists_detecting_partner (hspan : Submodule.span k (finiteDetections G res) = ⊤)
    {f : Vec2 k} (hf : f ≠ 0) : ∃ g ∈ finiteDetections G res, (Matrix.of ![f, g]).det ≠ 0 := by
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  let l : Vec2 k →ₗ[k] k := f 0 • LinearMap.proj (R := k) (φ := fun _ : Fin 2 => k) 1 -
    f 1 • LinearMap.proj (R := k) (φ := fun _ : Fin 2 => k) 0
  have hl : ∀ g : Vec2 k, l g = (Matrix.of ![f, g]).det := by
    intro g
    rw [Matrix.det_fin_two]
    simp only [l, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have htop : (⊤ : Submodule k (Vec2 k)) ≤ LinearMap.ker l := by
    rw [← hspan, Submodule.span_le]
    intro g hg
    rw [SetLike.mem_coe, LinearMap.mem_ker, hl]
    exact hno g hg
  have h0 := LinearMap.mem_ker.mp (htop (Submodule.mem_top : (Pi.single 0 1 : Vec2 k) ∈ ⊤))
  have h1 := LinearMap.mem_ker.mp (htop (Submodule.mem_top : (Pi.single 1 1 : Vec2 k) ∈ ⊤))
  simp only [l, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
    Pi.single_apply] at h0 h1
  norm_num at h0 h1
  apply hf
  funext j
  fin_cases j
  · exact h1
  · exact h0

end LimitImage

/-! ### The nonquadratic step with detection supplied by global cycles -/

section DetectedStep

open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Uniform (finPlane mem_finPlane)

variable {k : Type} [Field k] (G : GCx k) (res : GHom G (splitLocalComplex k))
  {A F : Type} [CommRing A] [Field F] {ι : A →+* F}

/-- The existing nonquadratic consumer, with its detection field supplied by two detecting
global cycles of the limit diagram. The duality and the two side-to-stage equivalences remain
the named inputs of the limit diagram. -/
def detectedLimitNonquadStep (ρ : A →+* k) (S₀ S₁ : TwoTermStage ι)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (hdual : LimitSwitchDuality G res ε σ J hε hσ hJ)
    {a b : G.X 1} (ha : G.d 1 2 rfl a = 0) (hb : G.d 1 2 rfl b = 0)
    {fa fb : Vec2 k} (hra : res.f 1 1 rfl a = (fa, 0)) (hrb : res.f 1 1 rfl b = (fb, 0))
    (hdet : (Matrix.of ![fa, fb]).det ≠ 0)
    (φ : (selCx (finiteLimitSide G res).Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S₀)
    (φ' : (selCx (singularLimitSide G res).Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S₁) :
    QuasiNonquadStep ρ S₀ S₁ :=
  limitNonquadStep G res ρ S₀ S₁ ε σ J hε hσ hJ hdual
    (finPlane_le_limitRelaxed_U G res ha hb hra hrb hdet) φ φ'

end DetectedStep

/-! ### Detection at a moving label from retained stage cocycles -/

section RealizedDetection

open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane mem_finPlane)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} {α : GKS K S →* Lambdaˣ} [W.IsElliptic]
  [HasFullTwoTorsion K S W] [IsContChar α]

/-- Specialization of integral coordinates at a prime of `Λ`, coordinatewise. -/
def specializeCoords (P : Ideal Lambda) [P.IsPrime] (x : Coords Lambda) : Coords (ResAt P) :=
  (fun j => algebraMap Lambda (ResAt P) (x.1 j), fun j => algebraMap Lambda (ResAt P) (x.2 j))

/-- The specialized limit Frobenius values of a sequence of stage cochains at a moving label. -/
def limitFrobValue (P : Ideal Lambda) [P.IsPrime] (L : MovingLabel K S) (U : Ultrafilter ℕ)
    (z : ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1) : Vec2 (ResAt P) :=
  fun j => algebraMap Lambda (ResAt P) (ulimVec U (fun i =>
    tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
      (evalOne Lambda (TLam K S W α) (L.frob i) (z i))) j)

variable (W α) in
/-- **A degree-one realization of a limit diagram at a moving label**: every global one-cycle of
the limit model carries a sequence of retained stage cocycles with values in the `Λ`-adic Tate
module, and the limit localization of the cycle is the specialization at `P` of the inner-limit
local class of that sequence at the label. This is the degree-one part of the retained comparison
between the limit model and the actual global cochains: it is the identity that the realized
finite free models must satisfy, not a consequence of the switch. -/
structure DegreeOneRealization (P : Ideal Lambda) [P.IsPrime] (G : GCx (ResAt P))
    (res : GHom G (splitLocalComplex (ResAt P))) (L : MovingLabel K S)
    (σ : ∀ i, Gloc K (L.q i)) (U : Ultrafilter ℕ) where
  /-- The retained stage cochains attached to a global one-cycle of the limit model. -/
  cocycle : LinearMap.ker (G.d 1 2 rfl) → ℕ → (contCochains Lambda (GKS K S) (TLam K S W α)).X 1
  /-- They are cocycles at the precision of their stage. -/
  stage : ∀ a i, IsStageCocycle W α i (cocycle a i)
  /-- The limit localization of the cycle is the specialized inner-limit local class. -/
  loc : ∀ a, res.f 1 1 rfl a.1 =
    specializeCoords P (completedEquiv (R := Lambda) U (innerLocalClassSeq L σ U (cocycle a)))

/-- Under a degree-one realization, the limit localization of a global cycle is the
specialization of the ultralimit of the Frobenius values of its stage cocycles, in the finite
plane. -/
theorem DegreeOneRealization.res_eq {P : Ideal Lambda} [P.IsPrime] {G : GCx (ResAt P)}
    {res : GHom G (splitLocalComplex (ResAt P))} {L : MovingLabel K S}
    {σ : ∀ i, Gloc K (L.q i)} (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite)
    (R : DegreeOneRealization W α P G res L σ U) (a : LinearMap.ker (G.d 1 2 rfl)) :
    res.f 1 1 rfl a.1 = (limitFrobValue P L U (R.cocycle a), 0) := by
  rw [R.loc a, completedEquiv_innerLocalClassSeq L σ hσ hU (R.cocycle a) (R.stage a)]
  refine Prod.ext rfl ?_
  funext j
  exact map_zero (algebraMap Lambda (ResAt P))

/-- For retained stage cocycles that are a constant actual cocycle, the specialized limit value is
the value of the cocycle at the limit Frobenius of the label. -/
theorem limitFrobValue_const (P : Ideal Lambda) [P.IsPrime] (L : MovingLabel K S)
    (U : Ultrafilter ℕ) (z : TateCocycles W α) :
    limitFrobValue P L U (fun _ => (z : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1)) =
      fun j => algebraMap Lambda (ResAt P) (tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (L.limitFrob U) z) j) := by
  have hcont : Continuous fun g : GKS K S =>
      tlamHomeomorph (K := K) (S := S) (W := W) (α := α) (evalOne Lambda (TLam K S W α) g z) :=
    (tlamHomeomorph (K := K) (S := S) (W := W) (α := α)).continuous.comp
      (continuous_evalOne (z : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1))
  have ht := (hcont.tendsto (L.limitFrob U)).comp (L.tendsto_limitFrob U)
  have hv : ulimVec U (fun i => tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
      (evalOne Lambda (TLam K S W α) (L.frob i) z)) =
      tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
        (evalOne Lambda (TLam K S W α) (L.limitFrob U) z) :=
    ulimVec_eq_of_tendsto ht
  funext j
  change algebraMap Lambda (ResAt P) (ulimVec U (fun i =>
    tlamHomeomorph (K := K) (S := S) (W := W) (α := α)
      (evalOne Lambda (TLam K S W α) (L.frob i) z)) j) = _
  rw [hv]

/-- **Detection at a moving label from retained stage cocycles**: if two global one-cycles of a
realized limit diagram have stage cocycles whose specialized limit Frobenius values have nonzero
determinant, the relaxed localization image contains the finite plane. -/
theorem DegreeOneRealization.finPlane_le_U {P : Ideal Lambda} [P.IsPrime] {G : GCx (ResAt P)}
    {res : GHom G (splitLocalComplex (ResAt P))} {L : MovingLabel K S}
    {σ : ∀ i, Gloc K (L.q i)} (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite)
    (R : DegreeOneRealization W α P G res L σ U) (a b : LinearMap.ker (G.d 1 2 rfl))
    (hdet : (Matrix.of ![limitFrobValue P L U (R.cocycle a),
      limitFrobValue P L U (R.cocycle b)]).det ≠ 0) :
    finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤ (limitRelaxed G res).U :=
  finPlane_le_limitRelaxed_U G res a.2 b.2 (R.res_eq hσ hU a) (R.res_eq hσ hU b) hdet

variable (W α) in
/-- **A degree-one realization by the actual Selmer complex with the old local conditions**: every
global one-cycle of the limit model carries, at every coefficient stage, a one-cochain of the
actual `Λ`-adic Selmer complex of `G_{K,S}` with the unchanged old local conditions `Δ` at the
places of `S`, whose coboundary vanishes at the precision of the stage; and the limit
localization of the cycle at the moving label is the specialized inner-limit local class of the
global components. -/
structure SelmerRealization (Δ : GaloisLocalConditions K S Lambda (TLam K S W α))
    (P : Ideal Lambda) [P.IsPrime] (G : GCx (ResAt P))
    (res : GHom G (splitLocalComplex (ResAt P))) (L : MovingLabel K S)
    (σ : ∀ i, Gloc K (L.q i)) (U : Ultrafilter ℕ) where
  /-- The stage Selmer cochains attached to a global one-cycle of the limit model. -/
  selmerCochain : LinearMap.ker (G.d 1 2 rfl) → ℕ →
    (selCx (galoisSelData K S Lambda (TLam K S W α) Δ)).X 1
  /-- They are Selmer cocycles at the precision of their stage. -/
  stage : ∀ a i, (selCx (galoisSelData K S Lambda (TLam K S W α) Δ)).d 1 2 rfl
    (selmerCochain a i) ∈ (stageIdeal i • ⊤ :
      Submodule Lambda ((selCx (galoisSelData K S Lambda (TLam K S W α) Δ)).X 2))
  /-- The limit localization of the cycle is the specialized inner-limit local class of the global
  components. -/
  loc : ∀ a, res.f 1 1 rfl a.1 = specializeCoords P (completedEquiv (R := Lambda) U
    (innerLocalClassSeq L σ U fun i =>
      (show (contCochains Lambda (GKS K S) (TLam K S W α)).X 1 from (selmerCochain a i).1)))

/-- The global component of a stage Selmer cocycle is a stage cocycle. -/
theorem SelmerRealization.global_stage {Δ : GaloisLocalConditions K S Lambda (TLam K S W α)}
    {P : Ideal Lambda} [P.IsPrime] {G : GCx (ResAt P)}
    {res : GHom G (splitLocalComplex (ResAt P))} {L : MovingLabel K S}
    {σ : ∀ i, Gloc K (L.q i)} {U : Ultrafilter ℕ}
    (R : SelmerRealization W α Δ P G res L σ U) (a : LinearMap.ker (G.d 1 2 rfl)) (i : ℕ) :
    IsStageCocycle W α i
      (show (contCochains Lambda (GKS K S) (TLam K S W α)).X 1 from (R.selmerCochain a i).1) := by
  apply isStageCocycle_of_d_mem
  have h := R.stage a i
  refine Submodule.smul_induction_on (p := fun v :
      (selCx (galoisSelData K S Lambda (TLam K S W α) Δ)).X 2 =>
      (show (contCochains Lambda (GKS K S) (TLam K S W α)).X 2 from v.1) ∈
        (stageIdeal i • ⊤ :
          Submodule Lambda ((contCochains Lambda (GKS K S) (TLam K S W α)).X 2))) h ?_ ?_
  · intro r hr m _
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

/-- A Selmer realization is a degree-one realization. -/
def SelmerRealization.toDegreeOne {Δ : GaloisLocalConditions K S Lambda (TLam K S W α)}
    {P : Ideal Lambda} [P.IsPrime] {G : GCx (ResAt P)}
    {res : GHom G (splitLocalComplex (ResAt P))} {L : MovingLabel K S}
    {σ : ∀ i, Gloc K (L.q i)} {U : Ultrafilter ℕ}
    (R : SelmerRealization W α Δ P G res L σ U) : DegreeOneRealization W α P G res L σ U where
  cocycle a i := (show (contCochains Lambda (GKS K S) (TLam K S W α)).X 1 from
    (R.selmerCochain a i).1)
  stage a i := R.global_stage a i
  loc a := R.loc a

/-- **The fixed-`P` nonquadratic step with detection at a moving label**: the existing fixed-`P`
consumer for a realized limit diagram, with the detection field supplied by two global cycles
whose retained stage cocycles have independent limit Frobenius values. -/
def realizedFibreLimitNonquadStep (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] (C : ComplexStages (R := Lambda) stageIdeal U)
    (res : GHom (fibreLimitGlobal U hU P C) (splitLocalComplex (ResAt P)))
    (L : MovingLabel K S) (σ : ∀ i, Gloc K (L.q i)) (hσ : ∀ i, urRes K (L.q i) (σ i) = 1)
    (R : DegreeOneRealization W α P (fibreLimitGlobal U hU P C) res L σ U)
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} (S₀ S₁ : TwoTermStage ι)
    (ε σ' : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ' : σ' ≠ 0)
    (hJ : J * J = 1) (hdual : FibreInnerLimitDuality U hU P C res ε σ' J hε hσ' hJ)
    (a b : LinearMap.ker ((fibreLimitGlobal U hU P C).d 1 2 rfl))
    (hdet : (Matrix.of ![limitFrobValue P L U (R.cocycle a),
      limitFrobValue P L U (R.cocycle b)]).det ≠ 0)
    (φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) res).Dside).toCC.homology 1 ≃ₗ[ResAt P]
      fiberH1 (resAt P) S₀)
    (φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C) res).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) S₁) :
    QuasiNonquadStep (resAt P) S₀ S₁ :=
  fibreLimitNonquadStep U hU P C res S₀ S₁ ε σ' J hε hσ' hJ hdual
    (R.finPlane_le_U hσ hU a b hdet) φ φ'

end RealizedDetection

/-! ### Quadratic candidates: the two signs at a moving label -/

section QuadraticSigns

open Matrix
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane mem_finPlane)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)

/-- **Opposite signs are independent**: for an involution `J` of `k²` with `2 ≠ 0`, nonzero
vectors in the `+1` and `-1` eigenspaces have nonzero determinant. -/
theorem det_ne_zero_of_signs {k : Type} [Field k] (h2 : (2 : k) ≠ 0)
    (J : Matrix (Fin 2) (Fin 2) k) {u v : Vec2 k} (hu : J *ᵥ u = u) (hv : J *ᵥ v = -v)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) : (Matrix.of ![u, v]).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hlin : w 0 • u + w 1 • v = 0 := by
    rw [← hw]
    funext j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  have hJ : w 0 • u - w 1 • v = 0 := by
    have e := congrArg (fun x => J *ᵥ x) hlin
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hu, hv, Matrix.mulVec_zero, smul_neg] at e
    rw [sub_eq_add_neg]
    exact e
  have h0 : (2 * w 0) • u = 0 := by
    have e : (w 0 • u + w 1 • v) + (w 0 • u - w 1 • v) = 0 := by rw [hlin, hJ, add_zero]
    rw [mul_smul, two_smul]
    rw [← e]
    abel
  have ha : w 0 = 0 := by
    rcases smul_eq_zero.mp h0 with h | h
    · exact (mul_eq_zero.mp h).resolve_left h2
    · exact absurd h hu0
  rw [ha, zero_smul, zero_add] at hlin
  have hb : w 1 = 0 := (smul_eq_zero.mp hlin).resolve_right hv0
  apply hw0
  funext j
  fin_cases j
  · exact ha
  · exact hb

/-- `x + J x` lies in the `+1` eigenspace of an involution. -/
theorem mulVec_add_self {k : Type} [CommRing k] (J : Matrix (Fin 2) (Fin 2) k) (hJ : J * J = 1)
    (x : Vec2 k) : J *ᵥ (x + J *ᵥ x) = x + J *ᵥ x := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec, add_comm]

/-- `x - J x` lies in the `-1` eigenspace of an involution. -/
theorem mulVec_sub_self {k : Type} [CommRing k] (J : Matrix (Fin 2) (Fin 2) k) (hJ : J * J = 1)
    (x : Vec2 k) : J *ᵥ (x - J *ᵥ x) = -(x - J *ᵥ x) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec, neg_sub]

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} {α : GKS K S →* Lambdaˣ} [W.IsElliptic]
  [HasFullTwoTorsion K S W] [IsContChar α]

/-- Specialized `Λ`-coordinates of an element of the Tate module at a prime of `Λ`. -/
def specTate (P : Ideal Lambda) [P.IsPrime] (x : TLam K S W α) : Vec2 (ResAt P) :=
  fun j => algebraMap Lambda (ResAt P) (tlamHomeomorph (K := K) (S := S) (W := W) (α := α) x j)

omit [IsContChar α] in
theorem specTate_add (P : Ideal Lambda) [P.IsPrime] (x y : TLam K S W α) :
    specTate P (x + y) = specTate P x + specTate P y := by
  funext j
  simp only [specTate, tlamHomeomorph_apply, map_add, Finsupp.add_apply, Pi.add_apply]

omit [IsContChar α] in
theorem specTate_sub (P : Ideal Lambda) [P.IsPrime] (x y : TLam K S W α) :
    specTate P (x - y) = specTate P x - specTate P y := by
  funext j
  simp only [specTate, tlamHomeomorph_apply, map_sub, Finsupp.sub_apply, Pi.sub_apply]

/-- **Mixed-sign detection at a moving label** (manuscript lines 5086–5115): two global cycles of
a realized limit diagram carry actual cocycles `z₊`, `z₋` of opposite signs for the conjugation
`α`, `T` on a kernel set `H` acting trivially. If the limit Frobenius of the label is `α(h) h`
for some `h ∈ H`, the action of the involution on the specialized fibre coordinates is an
involution `J̄`, `P` is a height-one prime other than `(2)` (so `2 ≠ 0` in the residue field),
and the sign components `(1 + J̄) z₊(h)` and `(1 - J̄) z₋(h)` are nonzero, then the relaxed
localization image contains the finite plane. -/
theorem DegreeOneRealization.finPlane_le_U_of_signs {P : Ideal Lambda} [P.IsPrime]
    {G : GCx (ResAt P)} {res : GHom G (splitLocalComplex (ResAt P))} {L : MovingLabel K S}
    {σ : ∀ i, Gloc K (L.q i)} (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite)
    (R : DegreeOneRealization W α P G res L σ U) (a b : LinearMap.ker (G.d 1 2 rfl))
    {zp zm : TateCocycles W α}
    (ha : R.cocycle a = fun _ => (zp : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1))
    (hb : R.cocycle b = fun _ => (zm : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1))
    (conj : GKS K S → GKS K S) (T : TLam K S W α →+ TLam K S W α) (H : Set (GKS K S))
    (hH : ∀ g ∈ H, ∀ m : TLam K S W α, g • m = m) (hαH : ∀ g ∈ H, conj g ∈ H)
    (hα2 : ∀ g ∈ H, conj (conj g) = g)
    (hsp : ∀ g ∈ H, T (evalOne Lambda (TLam K S W α) (conj g) zp) =
      evalOne Lambda (TLam K S W α) g zp)
    (hsm : ∀ g ∈ H, T (evalOne Lambda (TLam K S W α) (conj g) zm) =
      -evalOne Lambda (TLam K S W α) g zm)
    {h : GKS K S} (hh : h ∈ H) (hFrob : L.limitFrob U = conj h * h)
    (Jb : Matrix (Fin 2) (Fin 2) (ResAt P)) (hJb : Jb * Jb = 1)
    (hT : ∀ x, specTate P (T x) = Jb *ᵥ specTate P x) (hP : P.height = 1)
    (hne : P ≠ Ideal.span {2})
    (hp0 : specTate P (evalOne Lambda (TLam K S W α) h zp) +
      Jb *ᵥ specTate P (evalOne Lambda (TLam K S W α) h zp) ≠ 0)
    (hm0 : specTate P (evalOne Lambda (TLam K S W α) h zm) -
      Jb *ᵥ specTate P (evalOne Lambda (TLam K S W α) h zm) ≠ 0) :
    finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤ (limitRelaxed G res).U := by
  have hva : limitFrobValue P L U (R.cocycle a) =
      specTate P (evalOne Lambda (TLam K S W α) h zp) +
        Jb *ᵥ specTate P (evalOne Lambda (TLam K S W α) h zp) := by
    rw [ha, limitFrobValue_const, hFrob,
      evalOne_conj_mul_plus zp conj T H hH hαH hα2 hsp hh]
    change specTate P _ = _
    rw [specTate_add, hT]
  have hvb : limitFrobValue P L U (R.cocycle b) =
      specTate P (evalOne Lambda (TLam K S W α) h zm) -
        Jb *ᵥ specTate P (evalOne Lambda (TLam K S W α) h zm) := by
    rw [hb, limitFrobValue_const, hFrob,
      evalOne_conj_mul_minus zm conj T H hH hαH hα2 hsm hh]
    change specTate P _ = _
    rw [specTate_sub, hT]
  apply R.finPlane_le_U hσ hU a b
  rw [hva, hvb]
  exact det_ne_zero_of_signs (isUnit_two_resAt hP hne).ne_zero Jb (mulVec_add_self Jb hJb _)
    (mulVec_sub_self Jb hJb _) hp0 hm0

/-- **Single-sign detection at a moving label** (manuscript lines 5124–5136): a global cycle of a
realized limit diagram carrying an actual cocycle of sign `+1`, at a label whose limit Frobenius
is `α(h) h` with `h ∈ H`, localizes to the vector `(1 + J̄) z(h)` of the finite plane, a `+1`
eigenvector of `J̄`; when it is nonzero, the relaxed localization image meets the finite `+1` axis
nontrivially. -/
theorem DegreeOneRealization.exists_plus_detection {P : Ideal Lambda} [P.IsPrime]
    {G : GCx (ResAt P)} {res : GHom G (splitLocalComplex (ResAt P))} {L : MovingLabel K S}
    {σ : ∀ i, Gloc K (L.q i)} (hσ : ∀ i, urRes K (L.q i) (σ i) = 1) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite)
    (R : DegreeOneRealization W α P G res L σ U) (a : LinearMap.ker (G.d 1 2 rfl))
    {zp : TateCocycles W α}
    (ha : R.cocycle a = fun _ => (zp : (contCochains Lambda (GKS K S) (TLam K S W α)).X 1))
    (conj : GKS K S → GKS K S) (T : TLam K S W α →+ TLam K S W α) (H : Set (GKS K S))
    (hH : ∀ g ∈ H, ∀ m : TLam K S W α, g • m = m) (hαH : ∀ g ∈ H, conj g ∈ H)
    (hα2 : ∀ g ∈ H, conj (conj g) = g)
    (hsp : ∀ g ∈ H, T (evalOne Lambda (TLam K S W α) (conj g) zp) =
      evalOne Lambda (TLam K S W α) g zp)
    {h : GKS K S} (hh : h ∈ H) (hFrob : L.limitFrob U = conj h * h)
    (Jb : Matrix (Fin 2) (Fin 2) (ResAt P)) (hJb : Jb * Jb = 1)
    (hT : ∀ x, specTate P (T x) = Jb *ᵥ specTate P x)
    (hp0 : specTate P (evalOne Lambda (TLam K S W α) h zp) +
      Jb *ᵥ specTate P (evalOne Lambda (TLam K S W α) h zp) ≠ 0) :
    ∃ u ∈ (limitRelaxed G res).U, u.2 = 0 ∧ u.1 ≠ 0 ∧ Jb *ᵥ u.1 = u.1 := by
  have hva : limitFrobValue P L U (R.cocycle a) =
      specTate P (evalOne Lambda (TLam K S W α) h zp) +
        Jb *ᵥ specTate P (evalOne Lambda (TLam K S W α) h zp) := by
    rw [ha, limitFrobValue_const, hFrob,
      evalOne_conj_mul_plus zp conj T H hH hαH hα2 hsp hh]
    change specTate P _ = _
    rw [specTate_add, hT]
  refine ⟨(show Coords (ResAt P) from res.f 1 1 rfl a.1), ?_, ?_, ?_, ?_⟩
  · rw [limitRelaxed_U_eq]
    exact ⟨a.1, a.2, rfl⟩
  · change (show Coords (ResAt P) from res.f 1 1 rfl a.1).2 = 0
    rw [R.res_eq hσ hU a]
  · change (show Coords (ResAt P) from res.f 1 1 rfl a.1).1 ≠ 0
    rw [R.res_eq hσ hU a, hva]
    exact hp0
  · change Jb *ᵥ (show Coords (ResAt P) from res.f 1 1 rfl a.1).1 =
      (show Coords (ResAt P) from res.f 1 1 rfl a.1).1
    rw [R.res_eq hσ hU a, hva]
    exact mulVec_add_self Jb hJb _

end QuadraticSigns

/-! ### Actual derivative primes and the retained derivative matrices -/

section DerivativeStages

open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix tateMatrix_mul tateMatrix_one det_tateMatrix)
open ZInQ.Manuscript.RC.GlueSweep.Tate (torsField exists_frob_congr det_tateRep_eq_of_isFrobAt
  tateMatrix_congr_of_eqOn_torsField toZModPow_det_eq_of_frob)

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **Actual derivative primes along the coefficient stages**: at stage `i`, an odd rational prime
`ℓ_i` outside the excluded finite set, with an arithmetic Frobenius `Fr_i ∈ G_ℚ` at `ℓ_i` that
realizes the representative `τ h_i` on the stage field `F_i` and whose Tate matrix on `T₂E` agrees
with that of `τ h_i` modulo `2^i`. -/
structure DerivativePrimes (τ : GalQ) (h : ℕ → GalQ) (F : ℕ → IntermediateField ℚ Qbar)
    (excl : ℕ → Finset ℕ) where
  /-- The rational prime selected at each coefficient stage. -/
  ell : ℕ → ℕ
  prime : ∀ i, (ell i).Prime
  odd : ∀ i, ell i ≠ 2
  /-- The previously used primes are avoided. -/
  avoid : ∀ i, ell i ∉ excl i
  /-- An arithmetic Frobenius in `G_ℚ` at the selected prime. -/
  frob : ℕ → GalQ
  isFrob : ∀ i, ZInQ.Contrib.ChebFD.C10.IsFrobAt (frob i) (ell i)
  /-- The Frobenius realizes the representative on the stage field. -/
  agree : ∀ i, ∀ x ∈ F i, frob i x = (τ * h i) x
  /-- The Tate matrices agree at the stage precision. -/
  tate : ∀ i, (PadicInt.toZModPow i).mapMatrix (tateMatrix E (frob i)) =
    (PadicInt.toZModPow i).mapMatrix (tateMatrix E (τ * h i))

/-- **Finite Chebotarev at every stage**: for every conjugation `τ`, every sequence of
representatives `h_i`, finite stage fields and excluded finite sets, actual derivative primes exist
at every coefficient stage. -/
theorem exists_derivativePrimes (τ : GalQ) (h : ℕ → GalQ) (F : ℕ → IntermediateField ℚ Qbar)
    [∀ i, FiniteDimensional ℚ (F i)] (excl : ℕ → Finset ℕ) :
    Nonempty (DerivativePrimes E τ h F excl) := by
  choose fr ℓ hp hS h2 hF hagree htate _ using
    fun i => exists_frob_congr E (τ * h i) i (F i) (excl i)
  exact ⟨⟨ℓ, hp, h2, hS, fr, hF, hagree, htate⟩⟩

/-- A finite-dimensional subextension of `ℚ̄` lies in one member of an increasing exhausting
sequence of subextensions. -/
theorem exists_le_of_exhausting {F : ℕ → IntermediateField ℚ Qbar} (hmono : Monotone F)
    (hexh : ∀ x : Qbar, ∃ i, x ∈ F i) (E' : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ E'] : ∃ j, E' ≤ F j := by
  let b := Module.finBasis ℚ E'
  choose jb hjb using fun k => hexh (b k : Qbar)
  refine ⟨Finset.univ.sup jb, fun x hx => ?_⟩
  have hs := b.sum_repr ⟨x, hx⟩
  have hx' : x = ∑ k, (b.repr ⟨x, hx⟩ k) • (b k : Qbar) := by
    have := congrArg (fun y : E' => (y : Qbar)) hs
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
    exact this.symm
  rw [hx']
  refine IntermediateField.sum_mem _ fun k _ => IntermediateField.smul_mem _ ?_
  exact hmono (Finset.le_sup (Finset.mem_univ k)) (hjb k)

/-- **The selected rational Frobenius elements converge to the representative**: if the stage
fields increase and exhaust `ℚ̄` and the representative `τ h` is the same at every stage, the
selected Frobenius elements tend to `τ h` in `G_ℚ` along every nonprincipal ultrafilter; hence
their squares tend to `(τ h)²`, the element whose evaluation matrix appears in (5.4). -/
theorem DerivativePrimes.tendsto_frob {τ h₀ : GalQ} {F : ℕ → IntermediateField ℚ Qbar}
    {excl : ℕ → Finset ℕ} (D : DerivativePrimes E τ (fun _ => h₀) F excl) (hmono : Monotone F)
    (hexh : ∀ x : Qbar, ∃ i, x ∈ F i) {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) :
    Tendsto D.frob (U : Filter ℕ) (𝓝 (τ * h₀)) ∧
      Tendsto (fun i => D.frob i * D.frob i) (U : Filter ℕ) (𝓝 ((τ * h₀) * (τ * h₀))) := by
  have h1 : Tendsto (fun i => (τ * h₀)⁻¹ * D.frob i) (U : Filter ℕ) (𝓝 1) := by
    intro A hA
    obtain ⟨E', hfin, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar A).mp hA
    obtain ⟨j, hj⟩ := exists_le_of_exhausting hmono hexh E'
    have hsup : {i | j ≤ i} ⊆ (fun i => (τ * h₀)⁻¹ * D.frob i) ⁻¹' A := by
      intro i hi
      apply hsub
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hxF : x ∈ F i := hmono hi (hj hx)
      rw [AlgEquiv.mul_apply, D.agree i x hxF, ← AlgEquiv.mul_apply, inv_mul_cancel,
        AlgEquiv.one_apply]
    rw [Filter.mem_map]
    refine Filter.mem_of_superset (hU ?_) hsup
    rw [Filter.mem_cofinite]
    have he : {i | j ≤ i}ᶜ = Set.Iio j := by
      ext i
      simp
    rw [he]
    exact Set.finite_Iio j
  have h2 : Tendsto D.frob (U : Filter ℕ) (𝓝 (τ * h₀)) := by
    have := h1.const_mul (τ * h₀)
    simp only [mul_inv_cancel_left, mul_one] at this
    exact this
  exact ⟨h2, h2.mul h2⟩

/-- A constant of `ℤ₂` vanishing modulo `2^i` lies in the stage ideal. -/
theorem algebraMap_mem_stageIdeal {i : ℕ} {c : ℤ_[2]} (hc : PadicInt.toZModPow i c = 0) :
    algebraMap ℤ_[2] Lambda c ∈ stageIdeal i := by
  have hmem : c ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ i} := by
    rw [← PadicInt.ker_toZModPow]
    exact hc
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hmem
  rw [map_mul, map_pow, map_natCast, Nat.cast_ofNat]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

/-- The conjugation inverts the `2`-power roots of unity, so its Tate determinant is `-1`. -/
theorem det_tateMatrix_conj {τ : GalQ}
    (hτμ : ∀ (M : ℕ) (ζ : Qbar), ζ ^ (2 ^ M) = 1 → τ ζ = ζ ^ (2 ^ M - 1)) :
    (tateMatrix E τ).det = -1 := by
  rw [det_tateMatrix, ← PadicInt.ext_of_toZModPow]
  intro M
  rw [toZModPow_det_eq_of_frob E τ (hτμ M), map_neg, map_one,
    Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have h0 : ((2 : ZMod (2 ^ M))) ^ M = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ M)
  rw [h0, zero_sub]

variable {E}

/-- Agreement on the `2^i`-torsion field transports the Tate congruence from `τ h_i` to `τ`. -/
theorem DerivativePrimes.tate_conj {τ : GalQ} {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar}
    {excl : ℕ → Finset ℕ} (D : DerivativePrimes E τ h F excl)
    (hh : ∀ i, ∀ x ∈ torsField E i, h i x = x) (i : ℕ) :
    (PadicInt.toZModPow i).mapMatrix (tateMatrix E (D.frob i)) =
      (PadicInt.toZModPow i).mapMatrix (tateMatrix E τ) :=
  (D.tate i).trans (tateMatrix_congr_of_eqOn_torsField E fun x hx => by
    change τ (h i x) = τ x
    rw [hh i x hx])

/-- **The selected primes are `-1` modulo the stage precision**: from `det ρ(Fr_i) = ℓ_i`, the
Tate congruence with the conjugation and `det ρ(τ) = -1`. -/
theorem DerivativePrimes.ell_mod {τ : GalQ} {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar}
    {excl : ℕ → Finset ℕ} (D : DerivativePrimes E τ h F excl)
    (hτμ : ∀ (M : ℕ) (ζ : Qbar), ζ ^ (2 ^ M) = 1 → τ ζ = ζ ^ (2 ^ M - 1))
    (hh : ∀ i, ∀ x ∈ torsField E i, h i x = x) (i : ℕ) :
    PadicInt.toZModPow i ((D.ell i : ℕ) : ℤ_[2]) = -1 := by
  have hdet : (tateMatrix E (D.frob i)).det = ((D.ell i : ℕ) : ℤ_[2]) := by
    rw [det_tateMatrix]
    exact det_tateRep_eq_of_isFrobAt E (D.odd i) (D.isFrob i)
  rw [← hdet, RingHom.map_det, D.tate_conj hh i, ← RingHom.map_det, det_tateMatrix_conj E hτμ,
    map_neg, map_one]

/-- **The retained derivative matrices of a realized label**, built from actual data:
`ℓ_i` the actual primes (with retained integral inverse `ℓ_i` itself, since `ℓ_i² ≡ 1`), `Φ_i`
the matrix of the actual Frobenius of the stage prime of `K` on the actual twisted coefficient
module `T_2E ⊗ Λ(α)`, the rational Frobenius matrices `ρ(Fr_i)` on `T₂E`, and `J = ρ(τ)`. The
congruences are proved from the stage data: the derivative congruence for the twisted module
(including the character constraint) gives `Φ_i ≡ 1`, and Chebotarev with the determinant gives
`ℓ_i ≡ -1` and `ρ(Fr_i) ≡ J`. -/
def realizedDerivative {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    {W : WeierstrassCurve K} {α : GKS K S →* Lambdaˣ} [W.IsElliptic] [HasFullTwoTorsion K S W]
    (L : MovingLabel K S) {τ : GalQ} {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar}
    {excl : ℕ → Finset ℕ} (D : DerivativePrimes E τ h F excl) (hτ2 : τ * τ = 1)
    (hτμ : ∀ (M : ℕ) (ζ : Qbar), ζ ^ (2 ^ M) = 1 → τ ζ = ζ ^ (2 ^ M - 1))
    (hh : ∀ i, ∀ x ∈ torsField E i, h i x = x)
    (htriv : ∀ i (x : TLam K S W α), L.frob i • x - x ∈ tlamNbhd K S W α i)
    (U : Ultrafilter ℕ) : DerivativeMatrices (R := Lambda) stageIdeal U where
  ell i := ((D.ell i : ℕ) : Lambda)
  ellInv i := ((D.ell i : ℕ) : Lambda)
  phi i := LinearMap.toMatrix (tlamBasis (K := K) (S := S) (W := W) (α := α))
    (tlamBasis (K := K) (S := S) (W := W) (α := α)) (TLam.act (α := α) (L.frob i))
  rationalFrob i := (tateMatrix E (D.frob i)).map (algebraMap ℤ_[2] Lambda)
  J := (tateMatrix E τ).map (algebraMap ℤ_[2] Lambda)
  ell_congr := Eventually.of_forall fun i => by
    have hc : PadicInt.toZModPow i (((D.ell i : ℕ) : ℤ_[2]) + 1) = 0 := by
      rw [map_add, D.ell_mod hτμ hh i, map_one, neg_add_cancel]
    have := algebraMap_mem_stageIdeal hc
    rwa [map_add, map_natCast, map_one] at this
  inv_congr := Eventually.of_forall fun i => by
    have hc : PadicInt.toZModPow i (((D.ell i : ℕ) : ℤ_[2]) * ((D.ell i : ℕ) : ℤ_[2]) - 1) = 0 := by
      rw [map_sub, map_mul, D.ell_mod hτμ hh i, map_one, neg_mul_neg, one_mul, sub_self]
    have := algebraMap_mem_stageIdeal hc
    rwa [map_sub, map_mul, map_natCast, map_one] at this
  phi_congr := Eventually.of_forall fun i a b => by
    have hmem := htriv i (tlamBasis (K := K) (S := S) (W := W) (α := α) b)
    rw [TLam.smul_def] at hmem
    have hrepr : ∀ {x : TLam K S W α}, x ∈ tlamNbhd K S W α i →
        ∀ c, (tlamBasis (K := K) (S := S) (W := W) (α := α)).repr x c ∈ stageIdeal i := by
      intro x hx c
      refine Submodule.smul_induction_on (p := fun y =>
        (tlamBasis (K := K) (S := S) (W := W) (α := α)).repr y c ∈ stageIdeal i) hx ?_ ?_
      · intro r hr m _
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy
        rw [map_add, Finsupp.add_apply]
        exact Ideal.add_mem _ hx hy
    have hab := hrepr hmem a
    rw [map_sub, Finsupp.sub_apply, Basis.repr_self] at hab
    rw [Matrix.sub_apply, LinearMap.toMatrix_apply, Matrix.one_apply]
    convert hab using 2
    rw [Finsupp.single_apply]
    by_cases hba : b = a
    · simp [hba]
    · simp [hba, Ne.symm hba]
  rational_congr := Eventually.of_forall fun i a b => by
    have he := congrFun (congrFun (D.tate_conj hh i) a) b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at he
    have hc : PadicInt.toZModPow i (tateMatrix E (D.frob i) a b - tateMatrix E τ a b) = 0 := by
      rw [map_sub, he, sub_self]
    have := algebraMap_mem_stageIdeal hc
    rwa [map_sub] at this
  J_square := by
    rw [← Matrix.map_mul, ← tateMatrix_mul, hτ2, tateMatrix_one, Matrix.map_one _ (map_zero _)
      (map_one _)]

section RealizedDerivativeFacts

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} {α : GKS K S →* Lambdaˣ} [W.IsElliptic] [HasFullTwoTorsion K S W]
  (L : MovingLabel K S) {τ : GalQ} {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar}
  {excl : ℕ → Finset ℕ} (D : DerivativePrimes E τ h F excl) (hτ2 : τ * τ = 1)
  (hτμ : ∀ (M : ℕ) (ζ : Qbar), ζ ^ (2 ^ M) = 1 → τ ζ = ζ ^ (2 ^ M - 1))
  (hh : ∀ i, ∀ x ∈ torsField E i, h i x = x)
  (htriv : ∀ i (x : TLam K S W α), L.frob i • x - x ∈ tlamNbhd K S W α i)
  (U : Ultrafilter ℕ)

/-- The retained residue characteristics of the realized label are actual odd primes outside the
excluded sets. -/
theorem realizedDerivative_ell (i : ℕ) :
    (realizedDerivative L D hτ2 hτμ hh htriv U).ell i = ((D.ell i : ℕ) : Lambda) ∧
      (D.ell i).Prime ∧ D.ell i ≠ 2 ∧ D.ell i ∉ excl i :=
  ⟨rfl, D.prime i, D.odd i, D.avoid i⟩

/-- **The orientation of the realized conjugation**: `det J = -1`. -/
theorem realizedDerivative_J_det : (realizedDerivative L D hτ2 hτμ hh htriv U).J.det = -1 := by
  have h := RingHom.map_det (algebraMap ℤ_[2] Lambda) (tateMatrix E τ)
  rw [det_tateMatrix_conj E hτμ, map_neg, map_one] at h
  exact h.symm

/-- The rational Frobenius determinants are exactly the selected primes, at every stage. -/
theorem realizedDerivative_rationalFrob_det (i : ℕ) :
    ((realizedDerivative L D hτ2 hτμ hh htriv U).rationalFrob i).det -
      (realizedDerivative L D hτ2 hτμ hh htriv U).ell i ∈ stageIdeal i := by
  have h := RingHom.map_det (algebraMap ℤ_[2] Lambda) (tateMatrix E (D.frob i))
  rw [det_tateMatrix, det_tateRep_eq_of_isFrobAt E (D.odd i) (D.isFrob i), map_natCast] at h
  change ((tateMatrix E (D.frob i)).map (algebraMap ℤ_[2] Lambda)).det -
    ((D.ell i : ℕ) : Lambda) ∈ stageIdeal i
  rw [← RingHom.mapMatrix_apply, ← h, sub_self]
  exact Submodule.zero_mem _

/-- The realized residue characteristics tend to `-1`, the residue sizes to `1`, and the
conjugation of the inner limit has determinant `-1`, along every nonprincipal ultrafilter. -/
theorem realizedDerivative_limits (hU : (U : Filter ℕ) ≤ cofinite) :
    ulim U (realizedDerivative L D hτ2 hτμ hh htriv U).ell = -1 ∧
      ulim U (fun i => (realizedDerivative L D hτ2 hτμ hh htriv U).ell i ^ 2) = 1 ∧
      ulimMat U (realizedDerivative L D hτ2 hτμ hh htriv U).phi = 1 ∧
      (realizedDerivative L D hτ2 hτμ hh htriv U).J.det = -1 :=
  ⟨ell_limit stageIdeal_tendsToZero hU _, residueSize_limit stageIdeal_tendsToZero hU _,
    phi_limit stageIdeal_tendsToZero hU _,
    limitJ_det stageIdeal_tendsToZero hU _
      (Eventually.of_forall (realizedDerivative_rationalFrob_det L D hτ2 hτμ hh htriv U))⟩

/-- The limiting local action of the realized label: the rational Frobenius matrices tend to the
conjugation `J = ρ(τ)` on the finite plane and the tame pullbacks to `-J` on the singular plane. -/
theorem realizedDerivative_localAction (hU : (U : Filter ℕ) ≤ cofinite) :
    (Matrix.toLin' (ulimMat U (realizedDerivative L D hτ2 hτμ hh htriv U).rationalFrob)).prodMap
      (Matrix.toLin' (ulimMat U (fun i => (realizedDerivative L D hτ2 hτμ hh htriv U).ellInv i •
        (realizedDerivative L D hτ2 hτμ hh htriv U).rationalFrob i))) =
      localLimitAction ((tateMatrix E τ).map (algebraMap ℤ_[2] Lambda)) :=
  localLimitAction_from_stages stageIdeal_tendsToZero hU _

/-- The limiting tame cochain model of the realized label has rank-four first cohomology. -/
theorem realizedDerivative_limitTame_finrank (hU : (U : Filter ℕ) ≤ cofinite) :
    Module.finrank Lambda
      ((limitTameComplex (realizedDerivative L D hτ2 hτμ hh htriv U)).homology 1) = 4 := by
  rw [(limitTameH1Equiv stageIdeal_tendsToZero hU
    (realizedDerivative L D hτ2 hτμ hh htriv U)).finrank_eq]
  simp [Coords, Vec2]

variable (E K S W α τ h F excl) in
/-- **A realized derivative label**: a moving label of primes of `K`, actual rational derivative
primes below them, and the derivative congruence for the twisted coefficient module at every
stage (the Frobenius of the stage prime acts trivially on `𝕋 / I_i 𝕋`, which includes the
character constraint). -/
structure RealizedLabel where
  /-- The primes of `K` at the coefficient stages. -/
  label : MovingLabel K S
  /-- The rational derivative primes and their Frobenius elements. -/
  primes : DerivativePrimes E τ h F excl
  /-- The stage prime of `K` lies above the rational prime. -/
  above : ∀ i, ((primes.ell i : ℕ) : 𝓞 K) ∈ (label.q i).asIdeal
  /-- The derivative congruence for the twisted coefficient module. -/
  congr : ∀ i (x : TLam K S W α), label.frob i • x - x ∈ tlamNbhd K S W α i

/-- The retained derivative matrices of a realized derivative label. -/
def RealizedLabel.derivative (X : RealizedLabel E K S W α τ h F excl) (hτ2 : τ * τ = 1)
    (hτμ : ∀ (M : ℕ) (ζ : Qbar), ζ ^ (2 ^ M) = 1 → τ ζ = ζ ^ (2 ^ M - 1))
    (hh : ∀ i, ∀ x ∈ torsField E i, h i x = x) (U : Ultrafilter ℕ) :
    DerivativeMatrices (R := Lambda) stageIdeal U :=
  realizedDerivative X.label X.primes hτ2 hτμ hh X.congr U

end RealizedDerivativeFacts

end DerivativeStages

end ZInQ.Contrib.RC53Assist.InnerLimitArith
