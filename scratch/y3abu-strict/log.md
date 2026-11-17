# y3abu-strict log

Base 579a89bb (wip/y3abu-print); origin/main c1e4ed1b already an ancestor (merge: up to date).
Build tree: reflink copy of ~/dzq-wt/y3abu-print/.lake/build and lean/.lake/build (same HEAD 579a89bb).

## 17:35 (b) split compiles (VERIFIED)
- ZInQKernel/Contrib/OneProof/ShimuraY3Strict.lean (namespace Y3ABUStrict, imports ShimuraY3Print):
  `lake env lean` OK, no errors, no sorry.
  - ModuliLevelAtUnits Y Φ Ψ: ModuliAtUnits clause + level: ∃ w ∈ 𝒪, bEmb w = u⁻¹ + 3y (y ∈ 𝒪̂), and
    toMul (P.e.eta a) = Φu ((1/3) • ι(a*w)(τ,1)ᵀ) for all a ∈ 𝒪.
  - ModuliInterpAt = onto ∧ DCRel fibres (iff) ∧ holomorphic ∀ g ∧ ModuliLevelAtUnits.
  - ReciprocityAt = last clause of DeligneBodyAt, verbatim.
  - leaves DeligneModuliY3Every (∀ fine witness, ∃ Ψ, ModuliInterpAt), DeligneReciprocityY3Every
    (∀ fine witness, ∀ Ψ, ModuliInterpAt → ReciprocityAt).
  - glue: one_mem_OhatU, moduliAtUnits_of_level, body_of_split, deligneCanonicalModelY3Every_of_split,
    shimuraMainThmIDeligneY3AbU_of_strict (discharge from Y3FineModuliAb + the two leaves).
