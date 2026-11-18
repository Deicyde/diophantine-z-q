# logp-transc (fleet note)

**Verdict: scoped stop on both co-steps. Everything around the two missing theories is proved.** Report:
`docs/research/logp-transc.md`.

**Main result** (compiled, no sorry, standard axioms): `logPTildeTranscendental_iff_notInFrac` says
`BergerBst.LogPTildeTranscendental ↔ ∀ p, log [p̃] ∉ Frac(B_max)`, in the form
`NotInFrac p (Bmax p) (toBdR p (logPTilde p))`. The proof is the Galois half of Fontaine's argument, the
minimal-polynomial argument with `σ(log [p̃]) = log [p̃] + log [u_σ]`. It is proved for any `G`-stable `B ⊆ B_dR`
(`transcendental_of_logCore`), together with the tree's `B_dR^{G_{ℚ_p}} = ℚ_p`, put in element form here.

Also proved:
* `B_cris ⊆ B_max` for every `w ∈ ker θ` (`bcrisOf_le_bmax`; also `B_cris^+ ⊆ B_max^+` and `BstFOf ⊆ Bst`).
* Given the transcendence: Brinon-Conrad Thm 9.2.10's injectivity `B_cris[X] ↪ B_dR` at `K = ℚ_p`
  (`transcendental_bcrisOf`) and `BstFOf ≅ B_cris[X]` (`bcrisPolyEquiv`).
* The `B_cris` version: the weaker `log [p̃] ∉ Frac(B_cris)` already gives the transcendence over `B_cris`.

**What compiles:** two new files, checked with `lake env lean`. 34 declarations, all
`[propext, Classical.choice, Quot.sound]`. Neither file imports `ZInQKernel.OneProof.Main`, and nothing imports them.
* `ZInQKernel/Contrib/OneProof/LogPTranscendence.lean`, which imports `PanBergerFontaine`;
* `ZInQKernel/Contrib/OneProof/LogPTranscendenceBdR.lean`, which also imports `BdRInvariants`.

**What remains:**
* **(i)** The single Prop `log [p̃] ∉ Frac(B_max)` (or `∉ Frac(B_cris)`). The Galois action alone cannot give it:
  for units `v`, the elements `log([ṽ]/v)` lie in `A_max` and have the same Galois shape. The known proofs need
  three things the tree lacks, which together are a large missing theory:
  * an abstract `A_max` injecting into `B_dR^+`, the `A_max` analogue of co-step (ii);
  * the Frobenius on `B_max`;
  * an arithmetic separation of `p` from the units (the fundamental exact sequence plus Kummer theory, or
    `D_cris` with Bloch-Kato).
* **(ii)** BC's abstract `A_cris`: Mathlib v4.35 has no divided-power envelope (verified), so nothing was built. The
  report's §5 gives the smallest faithful statement (`range j = AcrisOf` and `j` injective) and notes a smaller
  version through BC's concrete `A_inf[ξ^n/n!]`.

**Ratings:** nothing is re-rated (`panPrintedF` and `bergerSurveyF` unchanged). Co-step (i) is now one concrete Prop.

**Manuscript:** no error found. L738-741 and L755-758: unverified, because they rest on the `B_st` identification,
which is reduced here and not proved. BC is cited in the bibitem only at Thm 5.2.1 and Props 6.3.3 and 6.3.8; the §9
definitions are provenance (b).

**Proof only:** no field, statement, kinds row or fold changed.
