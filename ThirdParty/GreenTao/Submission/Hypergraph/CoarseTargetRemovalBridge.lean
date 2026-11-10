import Submission.Hypergraph.CoarseOrderedRemovalTheorem
import Submission.Hypergraph.CoarseTargetRegularity

/-!
# Coarse-target regularity bridge to ordered removal

The coarse-target certificate was designed to match the two semantic
interfaces used by coarse ordered removal:

* its fine boundary is directly regular against each coarse upper atom;
* its energy increment is the coarse-upper atom-energy gap that occurs in
  the cleaning estimate.

Consequently neither counting nor cleaning pays a fine-upper complexity
conversion factor.  This file records those exact bridges and a sharp
constant-threshold deletion estimate.
-/

namespace Submission.GreenTao

open scoped BigOperators

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- The certificate's mixed regularity field is exactly the hypothesis of
coarse-configuration counting. -/
theorem isFullyMixedPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    IsFullyMixedPreliminaryOrderedRegular
      R.toCoarseFine
      (selectedOrderedComplexTolerance ε R.index) := by
  intro j
  exact R.mixedRegular j

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## Local coarse-upper gaps inject into the global gap -/

namespace OrderedCoarseFineComplex

/-- Below a fixed top face, the coarse-upper face gaps at one rank inject
into the complete coarse-upper layer gap. -/
theorem sum_coarseUpperFaceAtomEnergyGap_trans_le_layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r) (j : Fin r) :
    (∑ d : OrderedFace r (j.1 + 1),
      P.coarseUpperFaceAtomEnergyGap
        j (d.trans e)) ≤
      P.coarseUpperLayerAtomEnergyGap j := by
  classical
  rw [P.coarseUpperLayerAtomEnergyGap_eq_sum_face j]
  let φ : OrderedFace r (j.1 + 1) →
      OrderedFace k (j.1 + 1) :=
    fun d => d.trans e
  have hφ : Function.Injective φ := by
    intro d₁ d₂ h
    ext i
    exact congrArg Fin.val
      (e.injective
        (congrArg
          (fun f : OrderedFace k (j.1 + 1) => f i) h))
  calc
    (∑ d : OrderedFace r (j.1 + 1),
        P.coarseUpperFaceAtomEnergyGap j (φ d)) =
        ∑ f ∈
            (Finset.univ :
              Finset (OrderedFace r (j.1 + 1))).image φ,
          P.coarseUpperFaceAtomEnergyGap j f := by
      rw [Finset.sum_image hφ.injOn]
    _ ≤
        ∑ f : OrderedFace k (j.1 + 1),
          P.coarseUpperFaceAtomEnergyGap j f := by
      exact
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
          (fun f _ _ =>
            P.coarseUpperFaceAtomEnergyGap_nonneg j f)

/-- All coarse-upper face gaps occurring below one top face cost at most
the global coarse-target gap. -/
theorem sum_coarseUpperFaceAtomEnergyGap_trans_le_total
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r) :
    (∑ q : OrderedPositiveSubface r,
      P.coarseUpperFaceAtomEnergyGap
        q.1 (q.2.trans e)) ≤
      P.totalCoarseUpperAtomEnergyGap := by
  unfold totalCoarseUpperAtomEnergyGap
  let E :=
    Equiv.psigmaEquivSigma
      (fun j : Fin r => OrderedFace r (j.1 + 1))
  calc
    (∑ q : OrderedPositiveSubface r,
        P.coarseUpperFaceAtomEnergyGap
          q.1 (q.2.trans e)) =
        ∑ q : (Σ j : Fin r,
          OrderedFace r (j.1 + 1)),
          P.coarseUpperFaceAtomEnergyGap
            q.1 (q.2.trans e) := by
      rw [← E.sum_comp
        (fun q : (Σ j : Fin r,
            OrderedFace r (j.1 + 1)) =>
          P.coarseUpperFaceAtomEnergyGap
            q.1 (q.2.trans e))]
      rfl
    _ =
        ∑ j : Fin r,
          ∑ d : OrderedFace r (j.1 + 1),
            P.coarseUpperFaceAtomEnergyGap
              j (d.trans e) := by
      exact
        Fintype.sum_sigma'
          (fun (j : Fin r)
            (d : OrderedFace r (j.1 + 1)) =>
            P.coarseUpperFaceAtomEnergyGap
              j (d.trans e))
    _ ≤
        ∑ j : Fin r,
          P.coarseUpperLayerAtomEnergyGap j := by
      exact Finset.sum_le_sum fun j _ =>
        P.sum_coarseUpperFaceAtomEnergyGap_trans_le_layer e j

/-! ## Sharp constant-threshold cleaning -/

/-- With a uniform coarse complexity bound, the low-density losses are
charged once per positive subface while all defect losses are charged only
once to the global coarse-target energy gap. -/
theorem faceDeletionDensity_orderedCoarseBadBase_constant_coarseTarget_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r M : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hcoarse :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (P.coarse.partition j.succ e) ≤ M)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (M : ℝ) * α +
        P.totalCoarseUpperAtomEnergyGap / β := by
  have hbase :=
    faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le
      P (fun _ => α) (fun _ => β)
      (fun _ => hα) (fun _ => hβ) e
  calc
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) / β) :=
      hbase
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((M : ℝ) * α +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) / β) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (hcoarse q.1 (q.2.trans e))) hα)
        le_rfl
    _ =
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
            (M : ℝ) * α +
          (∑ q : OrderedPositiveSubface r,
            P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e)) / β := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    _ ≤
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
            (M : ℝ) * α +
          P.totalCoarseUpperAtomEnergyGap / β := by
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_right
          (P.sum_coarseUpperFaceAtomEnergyGap_trans_le_total e)
          hβ.le)

end OrderedCoarseFineComplex

end Submission.GreenTao
