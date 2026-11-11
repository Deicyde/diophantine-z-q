# rv-elim3: adversarial review of el-cert, el-k3 and el-qfree

Full note: `docs/research/rv-cr3-elim3.md`. Log and scripts: `scratch/rv-elim3/`. No Lean was run,
and no protected file was edited.

## Outcome

None of the three notes is refuted. All three main claims hold after minor repairs, and the
verdict "very low" stands for each.

## el-cert: verified after repairs

- **M1 soundness: VERIFIED** against `prime_dvd_of_test` and `common_group_of`. It is the
  original proof at q = 0, plus `v(a) ≤ 0`.
  - Repair: the Lean change is not a literal substitution. `pole_step` and `hex` must allow the
    numerator to differ from the argument of W.
- **Local lemma (`(−m/p) = −1`): VERIFIED.** I proved it independently, and it agreed with
  brute force on 26/26 new cases.
- **New check on real data.** On 12 Lean-formula instances (κ = 1), primes p with
  `(R₀/p) = −1` divide Θ₀ in 32 of 70 cases. One instance already excludes all 64 signed
  divisors of 2730.
- **X1/X2 reproduced:** genus 49 / 517 in the original design, genus 1 under M1.
- **L-B** holds only for witnesses that are rational functions of the instance data.

## el-k3: verified after repairs

- **NS computation reproduced for β ∈ {7, 15, 23, −7, 39}:**
  - rank 20, discriminant −16;
  - `NS^G` has rank 8, discriminant −1024, and is even with `D² ≡ 0 (mod 4)`;
  - `H¹ = 0`.
- **Independent PARI recomputation agrees.** It also covers θ = −β, which el-k3 omitted; that case
  gives the same even lattice.
- **Case B parity argument: checked.**
- **Repairs:**
  - even index means a torsor of even index, not necessarily a 2-covering;
  - the θ-uniformity argument is heuristic (SPECULATIVE).

## el-qfree: verified after repairs

- **Multiplier window: VERIFIED and strengthened.**
  - Sufficiency: the L7 argument does not need `v_p(B) < 0`, so it also proves directly that
    `v_p(m) = 0` wherever `v_p(B) = 1`.
  - Necessity, which earlier notes claimed only "for this proof": I found explicit global
    solutions with `v_p(B) = −1` when `v_p(m)` ∈ {1, −2, 3} (9/9 cases).
- **"M finite": repaired to SPECULATIVE.** An infinite M would need an infinite diophantine set
  of S-integers, which is an open question.
- **The Hom(Jac Y_θ, C₁) claim:** VERIFIED for constant N only. A q-dependent N needs
  `Hom(Jac Y_N) ⊕ Hom(Jac Y_{Nθ})`, which E3 does not test.
- **E3 reproduced and extended:** 4 genus-33 instances (1 new) and new primes 43 and 71 all give
  `[]`; the positive controls are detected.
