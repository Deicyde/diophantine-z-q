# rv-barrier: review of the CR₃ barrier statements

Full report: `docs/research/rv-cr3-barrier.md`. Scripts: `scratch/rv-barrier/`.

**Verdicts**
- **Theorem G** (el-gadget): **holds after repairs R1–R3.**
  - R1: define "rationally connected generic fibre" via a smooth proper model, and use the density of
    sections to land in the open gadget fibre.
  - R2: run Graber–Harris–Starr over the function field of an algebraic transversal curve, not over
    `Q̄((s))`.
  - R3: state the model conditions in (G-a).

  The column property holds (VERIFIED, E2 rerun 600/600, including `v_p(R₀) = 3` and `−1`). The Stein
  remark's "square-class only" is an overreach (R4). el-gadget's **global-soundness paragraph is refuted
  as stated** (R5): its premise that the total space is rationally connected is false, because the data
  space contains points of `E/K₀`. Theorem G does not depend on it.
- **Lemma G** (el-special): **holds as stated.**
  - R6: `γ₀` may lie on the closure of `Γ`.
  - Corollaries 1 and 3 hold after R1 and an explicit definition of "uniform construction" (R7).
  - Corollary 2 is VERIFIED (C5 rerun 30/30). `q` can even stay fixed: pole order 11.
  - The proof extends to any base `P′ → P` on which `B` keeps an odd pole (Lemma G′).
- Reruns: E1 (G1 witnesses at exactly the primes `p ≡ 1 (mod 4)`; G2, G3, G5 at 30/30 primes), E2, C3,
  C5 all agree with the notes.
- The Lean soundness (`poleSystem_no_negative_odd_valuation`) is purely valuative, hence local: the
  hypothesis matches the real design (VERIFIED by reading the code).

**Most important scope gap.** The barriers exclude only gadgets with rationally connected fibres and
explicit (rationally connected) witness families, both under local soundness uniform in all large primes.
They do **not** prove that a sound redesign needs positive rank or finiteness of Ш. They prove only that it
needs per-instance rational points on non-rationally-connected varieties, over a cover where `B` has only
even poles (N1). "CR₃'s kind" is SPECULATIVE. Global soundness (N2) is also not excluded, even
conditionally. The report should say "no rationally connected or explicit pole gadget can work", not "CR₃
cannot be removed by redesigning the pole gadget".

**Single next step.** Test the only concrete design that is not excluded: el-gadget's E4 redesign (`Θ`
independent of `q`, genus-1 quartic `h² = m(mΘ₀² − R₀(1 − R₀q²)²)`). Check its soundness (Lemma 5.1-style
valuation argument), and run a 2-descent with `ellrank` on about 30 instance quartics to see whether
everywhere-local solubility is forced by the instance structure.
