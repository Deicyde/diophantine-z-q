# hecke-glue results log

## Plan (route chosen)
ConstOnTauPoints is proved over ℚ (no base change to ℂ, no geometric irreducibility):
the x_ρ point lands on a closed point of X (jX(x_ρ)=j(ρ)=0, jX≠0); q = g(p_ρ) is closed
(Mathlib closedPoints_subset_preimage_closedPoints); F = g⁻¹{q} closed contains all p_τ;
if η ∉ F then F finite (CloudW07 IsOpen.finite_compl_of_topologicalKrullDim_le_one, dim ≤ 1 from
CloudW07 topologicalKrullDim_le_of_smoothOfRelativeDimension), so finitely many x_τ (finitely many
ℂ-points over a closed point: κ(p) finite over ℚ), so j has finite range on ℍ: contradiction.
So g(η)=q, q closed ⇒ q = g(P₀)=e, κ(e)=ℚ ⇒ g and 1 agree on Spec κ(η) ⇒ g = 1
(Mathlib ext_of_fromSpecResidueField_eq).

## 03:55 ConstOnTauPoints
- VERIFIED (compiles, `lake env lean scratch/hecke-glue/ConstOnTau.lean`, no sorry):
  `constOnTauPoints_of_x1TauPoints : X1TauPoints → ConstOnTauPoints`.
  Inputs: Mathlib (closedPoints_subset_preimage_closedPoints, SpecToEquivOfField,
  ext_of_fromSpecResidueField_eq, finite_of_finite_type_of_isJacobsonRing, AlgHom.fintype),
  CloudW07 (topologicalKrullDim_le_of_smoothOfRelativeDimension, eq_genericPoint_of_not_isClosed,
  IsOpen.finite_compl_of_topologicalKrullDim_le_one), WeberField (Jf, diffOn_Jf, Jf_I, Jf_ρ,
  exists_good_point, Dlf_ne), HeckePin (const_of_countable).
- Note: ConstOnTauPoints is not provable without the points: with no x_τ its hypothesis is vacuous.
  So the theorem takes X1TauPoints; isHeckeT_unique / isDiamond_unique then need X1TauPoints only.
