import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Forward
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Inverse
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# The forward map commutes with the differentials, all degrees (Route A, stage A4)

For `X : TopRep k G` let `repOf X : Rep k G` be its underlying (abstract) representation. The
forward map `toInhom X n` of `Forward.lean` intertwines the recursive differential of Mathlib's
`TopRep.homogeneousCochains X` with the differential `inhomogeneousCochains.d (repOf X) n` of
Mathlib's inhomogeneous cochains (`toInhom_d`, PROVED):

```text
toInhom (d F) (g₀, …, gₙ) = g₀ • toInhom F (g₁, …, gₙ)
    + ∑ⱼ (-1)^(j+1) toInhom F (g₀, …, gⱼ gⱼ₊₁, …, gₙ).
```

Proof: `evIt_d` expands the recursive differential into the alternating face sum; the `0`-th face
of `Fin.partialProd g` is `g₀ • Fin.partialProd (Fin.tail g)` (`Fin.partialProd_succ'`), which
invariance of `F` turns into `g₀ • toInhom F (Fin.tail g)` (`evIt_ρ`); the `(j+1)`-st face is
`Fin.partialProd (Fin.contractNth j (· * ·) g)` (`Fin.partialProd_contractNth`).

The same statement for the inverse of lane L2's degreewise equivalence `Inv.cochainEquiv`
(`Inverse.lean`), whose inverse is `Inv.fwdMap`: `evIt_succ_eq_evalIt` and `fwdMap_eq_toInhom`
identify the two forward maps, and `cochainEquiv_symm_d` is (A4) in that form (PROVED).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ContBridge

open CategoryTheory ContRepresentation

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- The underlying abstract representation of a topological representation. -/
abbrev repOf (X : TopRep.{u} k G) : Rep.{u} k G := Rep.of X.ρ.toRepresentation

variable (X : TopRep.{u} k G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem zsmul_neg_one_pow (m : ℕ) (v : X.V) : ((-1 : ℤ) ^ m) • v = ((-1 : k) ^ m) • v := by
  rw [← Int.cast_smul_eq_zsmul k]
  simp

/-- Invariant cochains: translating all arguments by `a` acts by `a`. -/
theorem evIt_invariant (m : ℕ) (F : (TopRep.resolutionX X m).V)
    (hF : ∀ g, (TopRep.resolutionX X m).ρ g F = F) (a : G) (z : Fin m → G) :
    evIt X m F (fun i => a * z i) = X.ρ a (evIt X m F z) := by
  conv_lhs => rw [← hF a]
  rw [evIt_ρ]
  simp only [inv_mul_cancel_left]

/-- **(A4) The forward map commutes with the differentials.** -/
theorem toInhom_d (n : ℕ) (F : (TopRep.homogeneousCochains X).X n) :
    toInhom X (n + 1) (((TopRep.homogeneousCochains X).d n (n + 1)).hom F) =
      (inhomogeneousCochains.d (repOf X) n).hom (toInhom X n F) := by
  funext g
  rw [toInhom_apply, TopRep.homogeneousCochains.d_apply, evIt_d, Fin.sum_univ_succ,
    inhomogeneousCochains.d_hom_apply]
  congr 1
  · rw [Fin.val_zero, pow_zero, one_smul, toInhom_apply]
    have e : (fun j => Fin.partialProd g ((0 : Fin (n + 2)).succAbove j)) =
        fun j => g 0 * Fin.partialProd (Fin.tail g) j := by
      funext j
      rw [Fin.succAbove_zero, Fin.partialProd_succ']
    rw [e, evIt_invariant X (n + 1) _ (F : (TopRep.resolutionX X (n + 1)).ρ.invariants).2]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.val_succ, zsmul_neg_one_pow, toInhom_apply, Fin.partialProd_contractNth]
    rfl

/-- The two iterated evaluations agree. -/
theorem evIt_succ_eq_evalIt (n : ℕ) (F : (TopRep.resolutionX X (n + 1)).V)
    (x : Fin (n + 1) → G) : evIt X (n + 1) F x = Inv.evalIt X n F x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _ _

/-- The two forward maps agree. -/
theorem fwdMap_eq_toInhom [LocallyCompactSpace G] (n : ℕ)
    (F : (TopRep.homogeneousCochains X).X n) :
    (Inv.fwdMap n (F : (TopRep.resolutionX X (n + 1)).ρ.invariants).1 :
      (Fin n → G) → X.V) = toInhom X n F := by
  funext g
  exact (evIt_succ_eq_evalIt X n _ _).symm

/-- **(A4) for lane L2's cochain equivalence**: its inverse intertwines Mathlib's recursive
homogeneous differential with Mathlib's inhomogeneous differential. -/
theorem cochainEquiv_symm_d [LocallyCompactSpace G]
    (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2) (n : ℕ)
    (F : (TopRep.homogeneousCochains X).X n) :
    ((Inv.cochainEquiv hcont (n + 1)).symm
        (((TopRep.homogeneousCochains X).d n (n + 1)).hom F) : (Fin (n + 1) → G) → X.V) =
      (inhomogeneousCochains.d (repOf X) n).hom
        ((Inv.cochainEquiv hcont n).symm F : (Fin n → G) → X.V) := by
  have h1 := fwdMap_eq_toInhom X (n + 1) (((TopRep.homogeneousCochains X).d n (n + 1)).hom F)
  have h2 := fwdMap_eq_toInhom X n F
  change (Inv.fwdMap (n + 1) _ : (Fin (n + 1) → G) → X.V) = _
  rw [h1, toInhom_d]
  exact congrArg _ h2.symm

end ZInQ.Contrib.CloudB3RC53.ContBridge
