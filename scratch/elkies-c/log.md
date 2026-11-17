# elkies-c results log

Base: wip/x6-coarse 0dc0c1fa, merged origin/main (5c7d9ba7) as 63d3efec.

## Statements
- Target: step (c) of `ElkiesX6StarEvery` / `X6ALIdeal.ElkiesX6StarEveryIdeal` (CM clause at every point), copied in
  `Statement.lean` (as `rfl` examples against the tree's definitions).
- Reviewer's deciding step (queue10, as named in the task): "HasCM containment read as Elkies' CM points needs the
  structure of CM points on Qbar-points" = exactness `HasCM_D P.q → End_𝒪(A) ≅ R_D` (R_D the order of disc D).

## Findings (tree inventory, VERIFIED by reading)
- `EichlerBound.r5fpCountLe_proof` (R5fpCountLe.lean): `#CM(R) ≤ 2^{inertCount6 k}·#Pic R` from the textbook fields.
- `RayClassCFT` (RayClassShimura.lean): `K24 = ℚ(s6)`, `y24`, `ringOfIntegersGen_K24` (𝓞 = ℤ[√−6]), `liftQuad`,
  `exists_rat_repr`, `finrank_K24`, `IsTotallyComplex K24`; same for K4 (y4 = ζ₄), K3 (y3 = −ζ₃).
- `Pi0X6` (LPrefix.lean): `galPt`, `galPt_eq_self_iff`, `val_galPt`, `pic_R4`, `pic_R3`, `inertCount6_K4/K3`,
  `conductor_R4`.
- `GR56.com_equiv_of_eig` + `GR56.datQ`, `com_bcQ`, `LatData.exists_O`: End_𝒪 from an optimal embedding.
- Not in the tree: `#Pic(ℤ[√−6])`, `inertCount6 K24`.
