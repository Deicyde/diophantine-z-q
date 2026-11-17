# pb-fix2 (2026-11-16)

**Result.** `r11r12 : HDec.PkgI4.PanBerger` is discharged by `panBerger_of_printedU`
(`ZInQKernel/Contrib/OneProof/PanBergerPrinted.lean`). It uses two new leaves, both rated **printed form**,
plus the existing bundle leaves `DSThm965`/`DSThm966`. The fold is **−1 GLUE**: strict 46/10 on 56 → 48/9 on 57,
strictest 45/11 → 47/10. The dry-run fold compiles with standard axioms.

* `BergerPrintedU` (Berger 2002, Thm 0.7): de Rham ⇒ pst on the underlying `V`, in Fontaine's tensor form.
  `K_0` is defined as printed, `W(k_K)[1/p]` (Mathlib Witt vectors of the residue field of `K`). Lean proves
  `[W(k)[1/p] : ℚ_p] = [k : 𝔽_p]`, `k_K` finite, `|k_K| = p^{[K_0:ℚ_p]}` and `[K_0(ℚ_p):ℚ_p] = 1`. Flags: the
  `B_st` reading (abstract `B_cris[X]`) and the normalization (`ℚ_p`-dimensions times `[K_0:ℚ_p]`).
* `PanPrintedU` (Pan 2022, Thm 1.0.4): stated for one `ρ`. Pst and "HT with distinct weights" are printed on `V`;
  the conclusion uses Pan's `ι_p` and geometric Frobenius. Flags: the eigenform reading, and irreducibility in
  Burnside form (a stronger hypothesis).
* Glue: apply both leaves to the contragredient `ρ^∨`. pkg-I4's `LocalIsDeRham`/`DistinctHTWeights` become the
  printed conditions for `ρ^∨` by the trace pairing alone, with no `AxSenTate`/`TateTwistInvariants`.
  Irreducibility, oddness and finite ramification pass to `ρ^∨`. Algebraicity comes from DS 9.6.5/9.6.6.

**Compiles (VERIFIED).** The new file, 18 declarations with only `propext`, `Classical.choice`, `Quot.sound`;
`#discharges` (r11r12 by `panBerger_of_printedU`); the autofold dry-run output; the contribution scan has 0 hits.
Deliverables: `scratch/pb-fix2/{autofold.json, discharges-output.txt, axioms-output.txt, log.md}` and
`docs/research/pb-fix2.md`.

**Remains.** Statement checks of both leaves against the prints: Berger's `K_0 = W(k)[1/p]` wording is from
memory (UNVERIFIED), and the JAMS locator for Pan is UNVERIFIED. Fontaine's `B_st^{G_K} = K_0` is not in Lean,
so no representation can yet be shown pst in Lean; this does not affect the fold. locators.md rows R11/R12 are
proposed in the report, not added.
