# g8-tate results log

## Step 0 (2026-11-13 09:28-09:45 PST): setup
- Fresh start (no earlier log). Merged origin/wip/alg-frob-red (94799bde) into wip/g8-tate.
- `lake build ZInQKernel.Main` (5m16s; needed for the upstream `ZInQ.*` helper modules: without
  it `lake env lean scratch/alg-frob-red/AlgFrobRed.lean` fails with "unknown module prefix 'ZInQ'").
- Read: g8-object report/part_split (OnL, WildTateTrivial, LinkedTateObjS, G7Data lacks [L:ℚ] ≤ D),
  frob-trace report/part_frob (TateBridge35 from I3.M0 + AlgFrobLink; operators
  `Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`, scalars `aQ g = βQ g / γQ(hgh⁻¹)`), alg-frob-red report
  (AlgFrobRed from GoodRedCofinite, SmoothGeomConnIntegral, I2-Red, FExtendGen, AbsFrob).

## Plan (Lean)
- `TateBridge35OnL`: TateBridge35's conclusion plus `ψ₅, ψ₃` and `G8Object.OnL` for frob-trace's
  operators. Math: for σL ∈ G_L, g = resQ L σL ∈ G_L. Λ = trPt κ : A(L̄) ≅ A(ℚ̄) (κ : L̄ ≃ₐ[L] ℚ̄),
  t = κ ∘ g_L ∈ G_ℚ (g_L the embedding of resQ), so Λ ∘ σL = m_{tgt⁻¹} ∘ Λ. X = Θ ∘ m_{ht⁻¹} ∘ Λ
  (isogeny-level; quasi-inverse Λ⁻¹ ∘ m_{th⁻¹} ∘ Θ⁻¹ by the cocycle clause and m₁ = id).
  m_{hgh⁻¹} m_{ht⁻¹} = m_{hgt⁻¹} = m_{ht⁻¹} m_{tgt⁻¹} (coset clauses of DescentDatum).
  ψ⁻¹ = ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(X) (bijective). Scalar clause: aQ = 1 on G_L since a = 1 on G_L and
  β(hgh⁻¹) = β(g) (ε trivial when one argument is in G_L).
