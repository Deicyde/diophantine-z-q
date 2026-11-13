import ZInQKernel.Hypotheses.CR3Literature
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.RouteK.RankVariants
import ZInQKernel.RouteK.PropN

/-!
# Main-theorem variants from the literature forms of H and CR₃

Theorem 1.1 of the manuscript (`FrozenTarget`) from the reductions of the two hypotheses:

* CR₃ replaced by three literature Props over Mathlib's L-series
  (`Hypotheses/CR3Literature.lean`): `Literature.TYZRow5b`, `Literature.FunctionalEquation5`
  and `Literature.GrossZagier`;
* `Literature.TYZRow5b` replaced in turn by two leaves, Tian–Yuan–Zhang's Theorem 3.5(2) in
  reading A (`Literature.TYZThm35ReadingA`) and Hecke's continuation
  (`Literature.HeckeContinuation`), through `Literature.tyzRow5b_of_readingA`;
* `Literature.TYZRow5b` replaced alternatively by `PropN.TYZInputs`
  (`Hypotheses/TYZInputs.lean`), the Tian–Yuan–Zhang inputs of Proposition N, proved in
  `RouteK/PropN.lean` (supporting evidence for `Literature.TYZThm35ReadingA`);
* H replaced by its `j`-form `JHeight.JHeightBound Mult.S_mul` (`Hypotheses/JHeight.lean`),
  which implies `SixContactMin` in Lean.

Each variant is proved from
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk`
(`RouteK/RankVariants.lean`).
-/

namespace ZInQ

/-- **Theorem 1.1 from `SixContactMin` and three literature statements for CR₃.** Assumes H in
its minimal form `SixContactMin`, Tian–Yuan–Zhang's row 5b `Literature.TYZRow5b` (TYZ
Theorem 3.5(2) in reading A, via Proposition N), the functional equation of `L(C_d, s)` with
root number `−1` on the strip `0 < Re s < 2` (`Literature.FunctionalEquation5`), and the
positive-rank half of Gross–Zagier `Literature.GrossZagier`; Lean derives `CertifiedRankTYZClRk`
from the three (`Literature.rootNumberVanishing_of_functionalEquation`, then
`Literature.certifiedRankTYZClRk_of_literature`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier
    (hH : SixContactMin) (hT : Literature.TYZRow5b) (hF : Literature.FunctionalEquation5)
    (hG : Literature.GrossZagier) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk hH
    (Literature.certifiedRankTYZClRk_of_literature hT
      (Literature.rootNumberVanishing_of_functionalEquation hF) hG)

/-- **Theorem 1.1 from `SixContactMin`, TYZ Theorem 3.5(2) in reading A, Hecke's continuation and
two textbook statements.** As the `TYZRow5b` variant above, with `Literature.TYZRow5b` replaced by
the two leaves `Literature.TYZThm35ReadingA` (Tian–Yuan–Zhang, Theorem 3.5(2) for `n ≡ 5 (mod 8)`
in reading A, in the case `𝓛(n) = 0` of its hypothesis: `ord_{s=1} L(C_d, s) ≥ 2` makes `T5aCl d`
and `T5bCl d` even) and `Literature.HeckeContinuation` (the entire continuation of `L(C_d, s)`).
Lean derives `TYZRow5b` from the two (`Literature.tyzRow5b_of_readingA`). Proposition N
(`PropN.tyzThm35ReadingA_of_tyzInputs`, `RouteK/PropN.lean`) derives `TYZThm35ReadingA` from
unambiguous results of the paper and is supporting evidence for the first leaf, not a hypothesis
here. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
    (hH : SixContactMin) (hA : Literature.TYZThm35ReadingA) (hC : Literature.HeckeContinuation)
    (hF : Literature.FunctionalEquation5) (hG : Literature.GrossZagier) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier
    hH (Literature.tyzRow5b_of_readingA hA hC) hF hG

/-- **Theorem 1.1 from `SixContactMin`, the Tian–Yuan–Zhang inputs and two textbook statements.**
As the `TYZRow5b` variant above, with `Literature.TYZRow5b` replaced by `PropN.TYZInputs`
(`Hypotheses/TYZInputs.lean`), the encoding of the results I1–I7 of Tian–Yuan–Zhang
(arXiv:1411.4728v1) that Proposition N of `docs/research/nt-tyz.md` uses. Lean derives
`TYZRow5b` from it (`PropN.tyzRow5b_of_tyzInputs`, `RouteK/PropN.lean`: the kernel-checked proof
of Proposition N), so the remaining CR₃ hypotheses are the functional equation
`Literature.FunctionalEquation5` and the positive-rank half of Gross–Zagier
`Literature.GrossZagier`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzInputs_functionalEquation5_grossZagier
    (hH : SixContactMin) (hT : PropN.TYZInputs) (hF : Literature.FunctionalEquation5)
    (hG : Literature.GrossZagier) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier
    hH (PropN.tyzRow5b_of_tyzInputs hT) hF hG

/-- **Theorem 1.1 from the `j`-form of H and `CertifiedRankTYZClRk`.** Assumes
`JHeight.JHeightBound Mult.S_mul`, the bound on the height of the Hauptmodul value `J(u)` that
steps A1-F3 of `docs/research/h-trust.md` give (not a published theorem), and CR₃ in the form
`RouteK.Rank.CertifiedRankTYZClRk`. Lean derives `SixContactMin` from the first
(`JHeight.sixContactMin_of_jHeightBound`: step F4 and the final numerics). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_jHeightBound_certifiedRankTYZClRk
    (hJ : JHeight.JHeightBound Mult.S_mul) (hCR : RouteK.Rank.CertifiedRankTYZClRk) :
    FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    (JHeight.sixContactMin_of_jHeightBound hJ) hCR

/-- **Theorem 1.1 from the `j`-form of H and three literature statements for CR₃.** Assumes
`JHeight.JHeightBound Mult.S_mul` (steps A1-F3 of `docs/research/h-trust.md`; not a published
theorem), `Literature.TYZRow5b` (TYZ Theorem 3.5(2) in reading A, via Proposition N),
`Literature.FunctionalEquation5` (functional equation with root number `−1` on the strip
`0 < Re s < 2`) and `Literature.GrossZagier` (positive-rank half of Gross–Zagier). Lean derives
`SixContactMin` and `CertifiedRankTYZClRk` from them. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_jHeightBound_tyzRow5b_functionalEquation5_grossZagier
    (hJ : JHeight.JHeightBound Mult.S_mul) (hT : Literature.TYZRow5b)
    (hF : Literature.FunctionalEquation5) (hG : Literature.GrossZagier) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    (JHeight.sixContactMin_of_jHeightBound hJ)
    (Literature.certifiedRankTYZClRk_of_literature hT
      (Literature.rootNumberVanishing_of_functionalEquation hF) hG)

end ZInQ
