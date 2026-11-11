# el-global: global soundness through a label on E(K₀): verdict

Note: `docs/research/el-global.md`; log and scripts in `scratch/el-global/`. No Lean was run, and nothing
under ZInQKernel/ or blueprint/ was edited.

**The proposal.** Give the pole predicate an extra witness `L ∈ E(K₀) = ℤP₀ + E[2]`, tied to the data
by a correspondence. Soundness would come from the integer behind L being the same at every place, and
completeness would be free because the prover already holds a label.

**Global Theorem G holds for free completeness (Theorem GG; VERIFIED as proofs from STANDARD inputs).**
The bad event cannot be seen through the labels: a bad rational point can be built with the labels of an
honest instance, or with labels shifted by δu for a fixed isogeny degree δ.
- **Algebraic completeness** (labels and witnesses algebraic over the data, e.g. reusing a test label, the
  only budget-free option): bad rational witnesses exist unconditionally. They keep t = n and replace κ
  by κ' = κ₀j₀ + δu. The proof uses CDJLZ's theorem on ramified covers of abelian varieties (rational
  points miss a finite-index coset) plus isogeny lifting.
- **Rationally connected (RC) witness fibres:** freeze the labels at an honest global point and use
  Colliot-Thélène's conjecture on the rational (t, q)-slice. This gives bad rational points close to an
  honest one at every place except p, so even `Close` holds. It is unconditional if the slice is
  ℚ-rational. This repairs the step that rv-barrier R5 refuted.
- **Labels depending on (t, q):** the dependence is a twist of a constant isogeny (twist lemma L4).
  Either completeness fails for all n outside a thin set (rs-global C3 in general form), or the gadget
  reduces to the cases above, or it needs a point on a genus ≥ 1 curve per instance.

**The proposal's own label is dead.** The deep κ is already a data label. Replacing it by κ' = 1 keeps
every algebraic relation satisfied and gives v_p(B) = −11 at every odd contact prime p > 324: 30/30 (E3).

**Mordell–Weil sieve:** not uniform in p. Local conditions at fixed places restrict k modulo a fixed M,
and depth at a bad prime π only needs m_π | k. These are compatible whenever gcd(m_π, M) = 1, which E2
finds for 59% of primes (M = 2) and 28% (M = 210). That is rv-barrier N3. Beyond the adelic closure ẐP₀,
the integer behind L carries only its archimedean size, i.e. a height bound. That is SixContactMin's
kind of hypothesis, not a replacement for CR₃.

**E1** (VERIFIED): with genuine label coordinates, B has a pole of order 11 along t = c in 30/30 cases,
so the odd-divisor hypothesis holds on every slice used.

**Residual:** non-RC witness fibres, honest rules that work only for sparse κ, and isolated Mordell–Lang
points. Each needs a per-instance rational point on a non-RC variety (in column form a genus ≥ 1 curve:
el-cert M1 / el-e4, where the Hasse principle fails). This is rv-barrier N1/N4.

**Chance that a label gadget eliminates CR₃: very low.**

**Single next step:** none for elimination. In the project report, close N2 for label gadgets with the
wording in note §6. Before quoting CDJLZ in a blueprint, check its Thm 1.3 against the paper (it is cited
here as recalled).
