# holfam (2026-11-15)

**Result.** `ShimuraSplit2.ShimuraHolFamilyAb` (the holomorphic moduli map on the fine witness `Y₃`) is reduced to
one new leaf, `HolFamilyPrinted.PELHolFamily`. The leaf is stated on the printed object only: Deligne's PEL moduli
curve `M_{K₃}/ℚ` with its universal QM abelian scheme (level 3) and a holomorphic `τ ↦ [τ,1]` whose fibre is
`ℂ²/ι(𝒪)(τ,1)ᵀ` as a QM pair. It does not mention the project's fine witness `(Y, Φ)`. The transport to every fine
witness is proved in Lean (`shimuraHolModAll_of_pel`: `R1univAbProps` classifies the family, and `isHolFamily_comp`
does the rest), so the `V_S → Y₃` identification that kept shimura-split2's leaf "pending reading" is now glue. The
converse `pelHolFamily_of_hol` is proved too, so the new leaf is not stronger. The three uses of the composite
`shimuraMainThmIDeligneY3AbU` follow from `PELHolFamily` + `MainTheoremCM` + the existing fields
(`compositeUses_of_pel`).

**Why not from the bundle fields alone:** they all speak of single abelian varieties or points, or of algebraic
families over ℚ-curves. Holomorphy in `τ` needs a relative analytic comparison that is not available (SPECULATIVE
judgement, same as composite-out).

**Compiles (VERIFIED):** `ZInQKernel/Contrib/OneProof/HolFamilyPrinted.lean` (0 errors, 0 warnings; standard axioms
for all 7 theorems); lake build of Main + Discharges + the file; `#discharges` (`scratch/holfam/Discharges-output.txt`;
no open field matched, as expected for a bypass); the bypass fold dry run `scratch/holfam/BypassFold.lean`
(`frozenTarget_holfam`, standard axioms); autofold spec `scratch/holfam/autofold.json` (replaces composite-out's).

**Count:** composite out, `mainTheoremCM` (LEAF) in, `pelHolFamily` in. Under the strict rating in the spec ("pending
reading of the analytic clause") the count is 0 now and −1 when the reading clears. If the leaf is rated the way
kinds.tsv rates `deligneComponentsX6PrintedAb` (published, locator UNVERIFIED), it is −1 strict GLUE now.

**Remains:** the hand fold; the reading of the analytic clause (Deligne 389 §§4.9–4.17 / Ex. 5.8, Milne ISV §§8, 14;
locators UNVERIFIED); the locators.md row proposed in docs/research/holfam.md §5. unif-printed had not reported, so
nothing was merged.
