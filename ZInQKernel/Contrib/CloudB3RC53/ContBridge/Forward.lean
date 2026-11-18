import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Homogeneous to inhomogeneous continuous cochains, all degrees: the forward map

Route A of the bridge between Mathlib's `continuousCohomology` (the homology of
`TopRep.homogeneousCochains`) and the inhomogeneous complex of continuous cochains.

A homogeneous `n`-cochain of `X : TopRep k G` is an invariant element `F` of the iterated
coinduced representation `TopRep.resolutionX X (n + 1) = C(G, C(G, …, C(G, X)))`. Its iterated
evaluation `evIt X (n + 1) F (y₀, …, yₙ) = F y₀ y₁ ⋯ yₙ` is the classical homogeneous function, and
the forward map sends `F` to the inhomogeneous cochain

```text
toInhom X n F (g₁, …, gₙ) = F 1 g₁ (g₁ g₂) ⋯ (g₁ ⋯ gₙ) = evIt X (n + 1) F (Fin.partialProd g)
```

(NSW, *Cohomology of Number Fields*, I §2). Main statements (all PROVED):

* `evIt` and its `k`-linearity in the cochain (`evIt_add`, `evIt_smul`, `evIt_zero_cochain`,
  `evIt_sub`, `evIt_neg`);
* `continuous_evIt`: for locally compact `G`, `(F, y) ↦ evIt X m F y` is jointly continuous;
* `evIt_ρ`: equivariance, `evIt X m (ρ g F) y = X.ρ g (evIt X m F (g⁻¹ • y))`;
* `evIt_d`: the iterated evaluation of the recursive differential `TopRep.d X m` is the
  alternating sum of the face values, `∑ᵢ (-1)^i evIt X m F (y ∘ i.succAbove)`;
* `toInhom`: the forward map, `k`-linear, from `(TopRep.homogeneousCochains X).X n`, and
  `continuous_toInhom`: its values are continuous functions `(Fin n → G) → X.V`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ContBridge

open CategoryTheory ContRepresentation

universe u v

variable {k : Type u} {G : Type v} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G]

section evIt

variable (X : TopRep.{v} k G)

/-- Iterated evaluation: `evIt X m F (y₀, …, y_{m-1}) = F y₀ ⋯ y_{m-1}`. -/
def evIt : (m : ℕ) → (TopRep.resolutionX X m).V → (Fin m → G) → X.V
  | 0, v, _ => v
  | m + 1, F, y => evIt m ((show C(G, (TopRep.resolutionX X m).V) from F) (y 0)) (Fin.tail y)

theorem evIt_zero (v : X.V) (y : Fin 0 → G) : evIt X 0 v y = v := rfl

theorem evIt_succ (m : ℕ) (F : (TopRep.resolutionX X (m + 1)).V) (y : Fin (m + 1) → G) :
    evIt X (m + 1) F y =
      evIt X m ((show C(G, (TopRep.resolutionX X m).V) from F) (y 0)) (Fin.tail y) := rfl

theorem evIt_add (m : ℕ) (F F' : (TopRep.resolutionX X m).V) (y : Fin m → G) :
    evIt X m (F + F') y = evIt X m F y + evIt X m F' y := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _ _ _

theorem evIt_smul (m : ℕ) (a : k) (F : (TopRep.resolutionX X m).V) (y : Fin m → G) :
    evIt X m (a • F) y = a • evIt X m F y := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _ _

theorem evIt_zero_cochain (m : ℕ) (y : Fin m → G) :
    evIt X m (0 : (TopRep.resolutionX X m).V) y = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

theorem evIt_neg (m : ℕ) (F : (TopRep.resolutionX X m).V) (y : Fin m → G) :
    evIt X m (-F) y = -evIt X m F y := by
  rw [eq_neg_iff_add_eq_zero, ← evIt_add, neg_add_cancel, evIt_zero_cochain]

theorem evIt_sub (m : ℕ) (F F' : (TopRep.resolutionX X m).V) (y : Fin m → G) :
    evIt X m (F - F') y = evIt X m F y - evIt X m F' y := by
  rw [sub_eq_add_neg, evIt_add, evIt_neg, ← sub_eq_add_neg]

/-- `evIt` peels off the first variable. -/
theorem evIt_cons (m : ℕ) (F : (TopRep.resolutionX X (m + 1)).V) (a : G) (z : Fin m → G) :
    evIt X (m + 1) F (Fin.cons a z) =
      evIt X m ((show C(G, (TopRep.resolutionX X m).V) from F) a) z := by
  rw [evIt_succ, Fin.cons_zero, Fin.tail_cons]

/-- **Joint continuity of the iterated evaluation** (locally compact `G`). -/
theorem continuous_evIt [LocallyCompactSpace G] (m : ℕ) :
    Continuous (fun p : (TopRep.resolutionX X m).V × (Fin m → G) => evIt X m p.1 p.2) := by
  induction m with
  | zero => exact continuous_fst
  | succ m ih =>
    have h1 : Continuous (fun p : (TopRep.resolutionX X (m + 1)).V × (Fin (m + 1) → G) =>
        (show C(G, (TopRep.resolutionX X m).V) from p.1) (p.2 0)) :=
      continuous_eval.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
    have h2 : Continuous (fun p : (TopRep.resolutionX X (m + 1)).V × (Fin (m + 1) → G) =>
        Fin.tail p.2) :=
      continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd
    exact ih.comp (h1.prodMk h2)

/-- Equivariance of the iterated evaluation. -/
theorem evIt_ρ (m : ℕ) (g : G) (F : (TopRep.resolutionX X m).V) (y : Fin m → G) :
    evIt X m ((TopRep.resolutionX X m).ρ g F) y = X.ρ g (evIt X m F (fun i => g⁻¹ * y i)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [evIt_succ, evIt_succ]
    exact ih _ _

/-- **The iterated evaluation of the recursive differential is the alternating face sum.** -/
theorem evIt_d (m : ℕ) (F : (TopRep.resolutionX X m).V) (y : Fin (m + 1) → G) :
    evIt X (m + 1) ((TopRep.d X m).hom F) y =
      ∑ i : Fin (m + 1), ((-1 : ℤ) ^ (i : ℕ)) • evIt X m F (fun j => y (i.succAbove j)) := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
    rfl
  | succ m ih =>
    rw [Fin.sum_univ_succ, evIt_succ]
    change evIt X (m + 1) (F - (TopRep.d X m).hom
      ((show C(G, (TopRep.resolutionX X m).V) from F) (y 0))) (Fin.tail y) = _
    rw [evIt_sub, ih, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_smul]
      rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, ← evIt_cons]
      congr 2
      refine congrArg (evIt X (m + 1) F) (funext fun j => ?_)
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.tail]

end evIt

section toInhom

variable (X : TopRep.{v} k G)

theorem continuous_partialProd (n : ℕ) (i : Fin (n + 1)) :
    Continuous (fun g : Fin n → G => Fin.partialProd g i) := by
  induction i using Fin.induction with
  | zero => simpa using continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)

/-- **The forward map** `F ↦ (g ↦ F 1 g₁ (g₁g₂) ⋯ (g₁⋯gₙ))` on homogeneous `n`-cochains. -/
def toInhom (n : ℕ) : (TopRep.homogeneousCochains X).X n →ₗ[k] ((Fin n → G) → X.V) where
  toFun F g := evIt X (n + 1) (F : (TopRep.resolutionX X (n + 1)).ρ.invariants).1
    (Fin.partialProd g)
  map_add' F F' := by
    funext g
    exact evIt_add X (n + 1) _ _ _
  map_smul' a F := by
    funext g
    exact evIt_smul X (n + 1) a _ _

theorem toInhom_apply (n : ℕ) (F : (TopRep.homogeneousCochains X).X n) (g : Fin n → G) :
    toInhom X n F g =
      evIt X (n + 1) (F : (TopRep.resolutionX X (n + 1)).ρ.invariants).1 (Fin.partialProd g) :=
  rfl

/-- **Continuity of the forward map's values** (locally compact `G`). -/
theorem continuous_toInhom [LocallyCompactSpace G] (n : ℕ)
    (F : (TopRep.homogeneousCochains X).X n) : Continuous (toInhom X n F) :=
  (continuous_evIt X (n + 1)).comp (continuous_const.prodMk
    (continuous_pi fun i => continuous_partialProd n i))

end toInhom

end ZInQ.Contrib.CloudB3RC53.ContBridge
