# composite-out log

## 2026-11-15 06:20 start
- Base: origin/main 43513d87 + merge origin/wip/qmrec-printed (a05c57ef, contains shimura-split2) + merge
  origin/wip/dcy3-used (36240662). Merges clean (VERIFIED, git).

## Findings (reading)
- `shimuraFamilyAb` needs a holomorphic map `ℍ → Y(ℂ)` (`ShimuraSplit.IsHolFamily`: preimages of Zariski opens
  open, regular functions pull back to analytic functions). None of MainTheoremCM, HomLatticeCorr,
  uniformizationLeafAll, gagaMorphism, the X6 leaves, R1fpPropsAb states any dependence of a point of Y on τ:
  they speak of single objects / algebraic morphisms. VERIFIED by reading the definitions (TailZ35 bundle,
  ShimuraSplit2, QMRecPrinted, TailZ16 R1fpPropsAb). So (b) needs an analytic leaf (SPECULATIVE judgement that
  no Lean route avoids one; it is the content of Shimura MT I, complex part).
- `Y3Connected` (dcy3-used's proof) reads the openness clause of `IsHolFamily` (step 1, `tind`): also analytic.
- shimura-split2's `ShimuraHolFamilyAb`/`ShimuraHolModAll` give a holomorphic family whose object is ℂ²/Λ_τ as a
  QM PAIR only (level structure unspecified, may jump with τ). With an unknown level the dcy3 argument does not
  go through directly (the B^×_+-relation becomes `F(x) = F(x ε_{γτ} γ ε_τ⁻¹)` with unknown ε's).
- Plan: leaf `ShimuraHolFamilyL3` = ShimuraHolFamilyAb with the level structure fixed (`MIsAt P τ g₀` for one
  `g₀ ∈ 𝒪̂^×`, all τ). Then: two families A_τ = y_τ, B_τ = y_τ ≫ e_c (c ∈ 𝒪^× from R1heckeProps, c ≡ (1+i+j)⁻¹
  mod 3); every ℂ-point is A or B (ComplexUnifL3 + dcy3 decomp3 + DCRelTransport + UnifDetermines); reciprocity
  at √2+i (QMReciprocityL3 ⇐ MainTheoremCM) sends A_z to B_z; clopen indicator constant.
