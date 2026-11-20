**Scoped stop: `t10TateDuality` remains GLUE.** The row's cohomology is pro-étale; the cited classical étale comparison is absent as a Lean statement.

**Citation gap (UNVERIFIED):** `diophantine_zq.tex:10967–10972` cites the 2008 notes' Part I, Theorem 12.1(a) alone for equivariance. The local audit points separately to Remark 12.5 (UNVERIFIED). The identification itself is not known to be wrong.

`ZInQKernel/Contrib/OneProof/T10Milne86/Printed.lean` builds with Lake. It defines classical integral étale `H¹` from the finite constant coefficient tower and states `T10Milne86.Milne86Thm15_1a`, the degree-one Milne identification natural for homomorphisms over `K`. The print locator and wording are UNVERIFIED. The two helper lemmas, pullback, and proposition report only `propext`, `Classical.choice`, and `Quot.sound`.

The minimum remaining comparison is a linear isomorphism between the two degree-one cohomologies on `A_Kbar` that commutes with transport along `1 × Spec(σ⁻¹)`. The same Milne isomorphism must also commute with the étale pullback of `1 × Spec(σ)` and the corresponding contragredient map. That square is outside ordinary naturality over `K`. No comparison or extra GLUE assumption was introduced, and there is no focused `#discharges` output.

See `docs/research/t10-milne86.md` for the exact squares, the source comparison, and the manuscript check. Results: `scratch/t10-milne86/log.md`.

Implementation commit: `4743458db76a75048ba9175fc3fefbda4060cc66`. The final SHA is returned by `git log -1 --format=%H -- .fleet/t10-milne86.md`; this file is part of the commit that command identifies, so it cannot embed that commit's literal hash.
