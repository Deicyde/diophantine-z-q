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

## 17:45 build, #discharges, autofold (VERIFIED)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraY3Strict`:
  success (14103 jobs); frozenTarget standard axioms.
- discharges.txt: `DISCHARGES [OpenResearchLeaves28.shimuraMainThmIDeligneY3AbU] by Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict
  still assumes: [Y3ABUPrint.Y3FineModuliAb, Y3ABUStrict.DeligneModuliY3Every, Y3ABUStrict.DeligneReciprocityY3Every]`,
  standard axioms; `#discharges: 45 open hypotheses, 6699 theorems checked, 15 discharge one`.
- autofold.json (3 leaves, all kind published, flags "locator UNVERIFIED: ...") --dry-run:
  strict 16/21 on 37 -> 19/20 on 39; strictest same (-1 GLUE). FoldCheck.lean compiles,
  sixContactMin_of_open39 standard axioms (foldcheck.txt).
- autofold-combined.json (with grx6ab-print, elkies-print; their argument
  (Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print ...) replaced by (Y3ABUStrict.shimuraMainThmIDeligneY3AbU_of_strict ...)):
  16/21 on 37 -> 22/18 on 40 (-3 GLUE). FoldCheckCombined.lean compiles, standard axioms (foldcheck-combined.txt).
