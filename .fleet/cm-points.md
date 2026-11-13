# cm-points (fleet report)

**Main result.** `TYZGenusPackage` is split into leaves over pinned objects plus proved glue:
`Package.tyzThm35ReadingA_of_cmLeaves` (compiles; axioms propext, Classical.choice, Quot.sound)
derives `Literature.TYZThm35ReadingA` from the three 𝓛-leaves of tyz-decomp plus
`CMFieldOfDefinitionTYZ` (the Heegner point of `[16(n+1), −8, 1]` lies in `A(H_{n,4})`: Shimura/Gross),
`IInH4` (`i ∈ H_{n,4}`: genus theory), `TYZSigmaFixesZn` (`σ_{1+2ϖ}` fixes `z_n`: TYZ Cor 3.9 = Shimura
reciprocity in TYZ's form), `HprimeNormal` (`H'_d/ℚ` normal: TYZ Prop 3.2(1) + Cox 9.3),
`Lemma318Literal HHprime` (TYZ Lemma 3.18, literally) and one bundled leaf `GenusPointLeafCM`. That leaf
is existential only over TYZ's choice of `Φ₀`, the class-7 genus points, `ε` and the lift `β'`. Here
`M = A(ℍ'_n)`, `τ`, `β` (Galois action of a `β₁`-lift), `P` (the recursion) and the class-5 genus points
(Heegner points through x0-32's `X0.phiC`) are genuine definitions. The caveats stay visible:
reading A is not printed in any refereed text; TYZ was read in arXiv v1 only; Proposition N is
AI-reviewed only; the translation `z_n = (1 − [i])f₀(P_n)` comes from tyz-t1 (AI, numerics).

**What compiles.** New files `ZInQKernel/Contrib/TYZGenus/CM.lean` and `Package.lean`
(`lake build ZInQKernel.Contrib.TYZGenus.Package`). x0-32 and ring-class were merged and both of their
files build with mine, including x0-32's `X0CM.lean` and `X0Pkg.lean`. No sorry, no axiom; no
existing file was edited; diffcheck2 reports MOD-UNNOTED 0 and NOTE-ONLY 0. `scratch/cm-points/Audit.lean`
checks 33 declarations, all on the standard three axioms.

**Proved (exact names).**
- `CM`: `mem_ptsOver_iff`, `iPt_mem`, `galPt_mem`, `galPt_iPt` (F4), `ιC_iQ`, `toC_injective`,
  `toC_heegnerPt`, `heegnerPt_eq`, `cmPoint_im`, `genusSum_mem`, `eta_conj`, `xC_conj`, `yC_conj`,
  `phiC_conj`, `toC_galPt`, `cmComplexConj` (the former leaf CM-4).
- `Package`: `Module GaussianInt PtA`, `ptT_add_self`, `four_zsmul_ptT`, `tauG_eq_zero`,
  `ptT_add_iPt_ptT`, `isTorsI3_mem_range`, `lemma318_iff_literal`, `galPt_tauG`,
  `fixes_i_of_isBetaOneLift`, `Pseq_eq`, `Pseq_mem`, `genusData_of`, `genusPackage_of_genusPointLeaf`,
  `genusPointLeaf_of_split`, `genusPackage_of_split`, `tyzThm35ReadingA_of_split`, `iContained_HHprime`,
  `normal_Lni`, `normalFields_HHprime`, `genusPackage_of_ringClass`, `tyzThm35ReadingA_of_ringClass`,
  `cmFieldTYZ_of`, `Lni_mono`, `tyzGenusSum_mem`, `genusPtsDefined_of`, `genusPackage_of_cm`,
  `tyzThm35ReadingA_of_cm`, `tyzThm35ReadingA_of_cm'`, `exists_actsAsArtin4`, `mem_Hprimebar_of_fixed`
  (Galois descent `H_{d,4} → H'_d`), `tyzZnOverHprime_of`, `tyzThm35ReadingA_of_cmLeaves`.

**Stated, not proved.** `CMAlgebraic`, `CMFieldOfDefinition H`, `ShimuraReciprocity` (Frobenius at
`𝔭` acts on the pair `(⟨1,τ⟩, ⟨1/32,τ⟩)` through multiplication by `𝔭̄`; the direction was re-derived
by an AI review but not checked numerically, since this host has no PARI), `CMFieldOfDefinitionTYZ`,
`IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`, `Lemma318Literal`, `GenusPointLeafCM`.

**What remains.** TYZ's class-7 base CM point is recorded in no note on this host, so the class-7
genus points are not pinned. Once they are, `GenusPointLeafCM` splits into `GenusPtsDefined`,
`Thm35First` and `Lemma321` via `genusPointLeaf_of_split`. Proposed to ring-class: prove
`HprimeNormal` and `IInH4`. Report: `docs/research/cm-points.md`; log: `scratch/cm-points/log.md`.
