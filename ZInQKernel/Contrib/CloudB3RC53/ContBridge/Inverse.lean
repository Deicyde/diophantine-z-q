import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Continuous cochains, Route A: the inverse map (A2) and the degreewise inverse identities (A3)

Mathlib's homogeneous continuous cochains of `X : TopRep k G` (`TopRep.homogeneousCochains`) in
degree `n` are the `G`-invariants of the iterated coinduction `resolutionX X (n + 1)` =
`C(G, C(G, …, C(G, X)))`, with `n + 1` factors. Mathlib's TODO: "the usual description of cochains
in terms of `n`-ary functions for locally compact groups". For a locally compact `G` and an action
`G × X → X` that is jointly continuous (all `PROVED`):

* `curryIt X n : C(C(Gⁿ⁺¹, X), resolutionX X (n + 1))`: iterated currying, continuous (Mathlib's
  `ContinuousMap.continuous_curry`). `evalIt X n` is iterated evaluation, with:
  * `evalIt_curryIt`: evaluation after currying is the identity;
  * `evalIt_ext`: elements are determined by their evaluations;
  * `evalIt_smul`: `evalIt (g • F) x = g • evalIt F (g⁻¹x)`;
  * `continuous_evalIt`: evaluation is jointly continuous;
  * `evalIt_add`, `evalIt_kSmul`: evaluation is linear.
* **(A2)** `invMap hcont n c`: the iterated currying of `homog c = ((x₀, …, xₙ) ↦
  x₀ • c(x₀⁻¹x₁, …, xₙ₋₁⁻¹xₙ))`, a `G`-invariant element (`invMap`, with its invariance proof).
* `fwdMap n F = ((g₁, …, gₙ) ↦ F(1)(g₁)(g₁g₂)…(g₁⋯gₙ))` as a continuous map (`Fin.partialProd`).
  This is this file's own form of the forward map, to be identified with the forward map of stage
  (A1) once its signatures are posted.
* **(A3)** `fwdMap_invMap` and `invMap_fwdMap`: the two maps are mutually inverse in each degree.
  `cochainEquiv hcont n : C(Fin n → G, X) ≃ₗ[k] (resolutionX X (n + 1)).ρ.invariants` packages them
  as a `k`-linear equivalence.

The joint continuity of the action is a hypothesis (`hcont`): `TopRep` only asks each `ρ g` to be
continuous. It holds for a discrete module with continuous action.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ContBridge.Inv

open CategoryTheory ContRepresentation TopRep

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- `(a, xs) ↦ (a, xs₀, …)`. -/
def consMap (n : ℕ) : C(G × (Fin (n + 1) → G), Fin (n + 2) → G) where
  toFun p := Fin.cons p.1 p.2
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using continuous_fst
    · simp only [Fin.cons_succ]
      exact (continuous_apply j).comp continuous_snd

/-- `a ↦ (a)`. -/
def singleMap : C(G, Fin 1 → G) where
  toFun a := fun _ => a
  continuous_toFun := continuous_pi fun _ => continuous_id

variable (X : TopRep k G)

/-- **Iterated currying** `C(Gⁿ⁺¹, X) → C(G, C(G, …, C(G, X)))`, continuous (locally compact `G`). -/
def curryIt [LocallyCompactSpace G] : (n : ℕ) →
    C(C(Fin (n + 1) → G, X.V), (resolutionX X (n + 1)).V)
  | 0 => ⟨fun f => f.comp singleMap, ContinuousMap.continuous_precomp _⟩
  | n + 1 => ⟨fun f => (curryIt n).comp (ContinuousMap.curry (f.comp (consMap n))),
      (ContinuousMap.continuous_postcomp (curryIt n)).comp
        (ContinuousMap.continuous_curry.comp (ContinuousMap.continuous_precomp (consMap n)))⟩

/-- Iterated evaluation `F ↦ ((x₀, …, xₙ) ↦ F x₀ … xₙ)`. -/
def evalIt : (n : ℕ) → (resolutionX X (n + 1)).V → (Fin (n + 1) → G) → X.V
  | 0 => fun F x => (F : C(G, X.V)) (x 0)
  | n + 1 => fun F x => evalIt n ((F : C(G, (resolutionX X (n + 1)).V)) (x 0)) (Fin.tail x)

theorem evalIt_curryIt [LocallyCompactSpace G] (n : ℕ) (f : C(Fin (n + 1) → G, X.V))
    (x : Fin (n + 1) → G) : evalIt X n (curryIt X n f) x = f x := by
  induction n with
  | zero =>
    show f (fun _ => x 0) = f x
    congr 1; funext i; rw [Fin.fin_one_eq_zero i]
  | succ n ih =>
    show evalIt X n (curryIt X n (ContinuousMap.curry (f.comp (consMap n)) (x 0))) (Fin.tail x) = _
    rw [ih]
    show f (Fin.cons (x 0) (Fin.tail x)) = f x
    rw [Fin.cons_self_tail]

theorem evalIt_ext (n : ℕ) {F F' : (resolutionX X (n + 1)).V}
    (h : ∀ x, evalIt X n F x = evalIt X n F' x) : F = F' := by
  induction n with
  | zero =>
    show (F : C(G, X.V)) = F'
    ext a
    exact h (fun _ => a)
  | succ n ih =>
    show (F : C(G, (resolutionX X (n + 1)).V)) = F'
    ext1 a
    refine ih fun xs => ?_
    have := h (Fin.cons a xs)
    simpa [evalIt] using this

theorem evalIt_smul (n : ℕ) (g : G) (F : (resolutionX X (n + 1)).V) (x : Fin (n + 1) → G) :
    evalIt X n ((resolutionX X (n + 1)).ρ g F) x = X.ρ g (evalIt X n F (fun i => g⁻¹ * x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show evalIt X n ((resolutionX X (n + 1)).ρ g ((F : C(G, _)) (g⁻¹ * x 0))) (Fin.tail x) = _
    rw [ih]
    rfl

theorem rho_mul_apply (g h : G) (v : X.V) : X.ρ g (X.ρ h v) = X.ρ (g * h) v := by
  rw [map_mul]; rfl

theorem continuous_partialProd (n : ℕ) :
    Continuous fun g : Fin n → G => (Fin.partialProd g : Fin (n + 1) → G) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.induction with
  | zero => simp only [Fin.partialProd_zero]; exact continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)

theorem continuous_evalIt [LocallyCompactSpace G] (n : ℕ) :
    Continuous fun p : (resolutionX X (n + 1)).V × (Fin (n + 1) → G) => evalIt X n p.1 p.2 := by
  induction n with
  | zero =>
    show Continuous fun p : C(G, X.V) × (Fin 1 → G) => p.1 (p.2 0)
    exact continuous_eval.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
  | succ n ih =>
    show Continuous fun p : C(G, (resolutionX X (n + 1)).V) × (Fin (n + 2) → G) =>
      evalIt X n (p.1 (p.2 0)) (Fin.tail p.2)
    refine ih.comp (Continuous.prodMk ?_ ?_)
    · exact continuous_eval.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
    · exact continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd

variable {X}

/-- **The homogenization** `c ↦ ((x₀, …, xₙ) ↦ x₀ • c(x₀⁻¹x₁, …, xₙ₋₁⁻¹xₙ))` (the action jointly
continuous). -/
def homog (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2) (n : ℕ) (c : C(Fin n → G, X.V)) :
    C(Fin (n + 1) → G, X.V) where
  toFun x := X.ρ (x 0) (c (fun i => (x i.castSucc)⁻¹ * x i.succ))
  continuous_toFun := hcont.comp (Continuous.prodMk (continuous_apply 0)
    (c.continuous.comp (continuous_pi fun i =>
      ((continuous_apply i.castSucc).inv).mul (continuous_apply i.succ))))

theorem homog_apply (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2) (n : ℕ)
    (c : C(Fin n → G, X.V)) (x : Fin (n + 1) → G) :
    homog hcont n c x = X.ρ (x 0) (c (fun i => (x i.castSucc)⁻¹ * x i.succ)) := rfl

/-- **(A2) The inverse map**: the iterated currying of the homogenization of an inhomogeneous
continuous cochain is a `G`-invariant element of `C(G, C(G, …, C(G, X)))`, i.e. a homogeneous
continuous cochain. -/
def invMap [LocallyCompactSpace G] (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2) (n : ℕ)
    (c : C(Fin n → G, X.V)) : (resolutionX X (n + 1)).ρ.invariants :=
  ⟨curryIt X n (homog hcont n c), fun g => evalIt_ext X n fun x => by
    rw [evalIt_smul, evalIt_curryIt, evalIt_curryIt, homog_apply, homog_apply, rho_mul_apply,
      mul_inv_cancel_left]
    congr 2
    funext i
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]⟩

theorem evalIt_invMap [LocallyCompactSpace G] (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2)
    (n : ℕ) (c : C(Fin n → G, X.V)) (x : Fin (n + 1) → G) :
    evalIt X n (invMap hcont n c : (resolutionX X (n + 1)).V) x =
      X.ρ (x 0) (c (fun i => (x i.castSucc)⁻¹ * x i.succ)) :=
  evalIt_curryIt X n _ x

/-- The forward evaluation `F ↦ ((g₁, …, gₙ) ↦ F(1)(g₁)(g₁g₂)…(g₁⋯gₙ))` (locally compact `G`). -/
def fwdMap [LocallyCompactSpace G] (n : ℕ) (F : (resolutionX X (n + 1)).V) : C(Fin n → G, X.V) where
  toFun g := evalIt X n F (Fin.partialProd g)
  continuous_toFun := (continuous_evalIt X n).comp (continuous_const.prodMk (continuous_partialProd n))

/-- **(A3), first half**: forward after inverse is the identity on inhomogeneous cochains. -/
theorem fwdMap_invMap [LocallyCompactSpace G] (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2)
    (n : ℕ) (c : C(Fin n → G, X.V)) : fwdMap n (invMap hcont n c : (resolutionX X (n + 1)).V) = c := by
  ext g
  show evalIt X n (invMap hcont n c : (resolutionX X (n + 1)).V) (Fin.partialProd g) = c g
  rw [evalIt_invMap, Fin.partialProd_zero, map_one]
  simp only [Fin.partialProd_right_inv]
  rfl

/-- **(A3), second half**: inverse after forward is the identity on homogeneous cochains. -/
theorem invMap_fwdMap [LocallyCompactSpace G] (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2)
    (n : ℕ) (F : (resolutionX X (n + 1)).ρ.invariants) :
    invMap hcont n (fwdMap n (F : (resolutionX X (n + 1)).V)) = F := by
  apply Subtype.ext
  refine evalIt_ext X n fun x => ?_
  rw [evalIt_invMap]
  have hF : evalIt X n (F : (resolutionX X (n + 1)).V) x =
      evalIt X n ((resolutionX X (n + 1)).ρ (x 0) F) x := by rw [F.2 (x 0)]
  rw [hF, evalIt_smul]
  show X.ρ (x 0) (evalIt X n F (Fin.partialProd fun i => (x i.castSucc)⁻¹ * x i.succ)) = _
  congr 2
  funext i
  have := congrFun (Fin.partialProd_left_inv x) i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [eq_inv_mul_iff_mul_eq, this]


variable (X) in
theorem evalIt_add (n : ℕ) (F F' : (resolutionX X (n + 1)).V) (x : Fin (n + 1) → G) :
    evalIt X n (F + F') x = evalIt X n F x + evalIt X n F' x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _ _ _

variable (X) in
theorem evalIt_kSmul (n : ℕ) (a : k) (F : (resolutionX X (n + 1)).V) (x : Fin (n + 1) → G) :
    evalIt X n (a • F) x = a • evalIt X n F x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _ _

/-- **(A2)+(A3) degreewise**: the inverse map is a `k`-linear equivalence between inhomogeneous
continuous `n`-cochains and homogeneous continuous `n`-cochains (`G`-invariants of the iterated
coinduction), with inverse the forward evaluation (locally compact `G`, jointly continuous
action). -/
def cochainEquiv [LocallyCompactSpace G] (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2)
    (n : ℕ) : C(Fin n → G, X.V) ≃ₗ[k] (resolutionX X (n + 1)).ρ.invariants where
  toFun := invMap hcont n
  invFun F := fwdMap n (F : (resolutionX X (n + 1)).V)
  map_add' c c' := Subtype.ext (evalIt_ext X n fun x => by
    show evalIt X n (invMap hcont n (c + c') : (resolutionX X (n + 1)).V) x =
      evalIt X n ((invMap hcont n c : (resolutionX X (n + 1)).V) +
        (invMap hcont n c' : (resolutionX X (n + 1)).V)) x
    rw [evalIt_add, evalIt_invMap, evalIt_invMap, evalIt_invMap, ContinuousMap.add_apply, map_add])
  map_smul' a c := Subtype.ext (evalIt_ext X n fun x => by
    show evalIt X n (invMap hcont n (a • c) : (resolutionX X (n + 1)).V) x =
      evalIt X n (a • (invMap hcont n c : (resolutionX X (n + 1)).V)) x
    rw [evalIt_kSmul, evalIt_invMap, evalIt_invMap, ContinuousMap.smul_apply, map_smul])
  left_inv c := fwdMap_invMap hcont n c
  right_inv F := invMap_fwdMap hcont n F


end ZInQ.Contrib.CloudB3RC53.ContBridge.Inv
