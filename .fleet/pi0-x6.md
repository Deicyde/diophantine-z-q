# pi0-x6: `π₀(X₆) = 1` (rv-blueprints Q4) as glue

**Verdict.**

- rv-blueprints' sketch is **not glue as written**. Its parity step forbids exactly three branch
  points but not four. It therefore needs "no branch values outside `{0, ∞, −16/27}`", and no
  clause of `R1R2fpRep` gives that. Repairing it would take an extra leaf: the fixed points of `W`
  lie over the three values (Baba–Granath §3.1 table, or Ogg; locators UNVERIFIED).
- A **different argument** (`docs/research/pi0-x6.md` §2; SPECULATIVE until reviewed) needs no
  new literature leaf. It uses the Galois action on the components of `X₆_ℚ̄`:
  - the residue fields over `0` and `∞` are `ℚ(i)` and `ℚ(√−3)` (`R5ptProps`);
  - there are 2 points over `0` (`R5fpCount`);
  - one `σ` fixes `√−3` and moves `i`.

  If there were two components, `σ` would identify them.

**What compiles** (`scratch/pi0-x6/Pi0X6.lean`; exit 0, no errors or warnings, no `sorry`; all 10
audited declarations use only `propext`, `Classical.choice`, `Quot.sound`):

- `Pi0X6.r1pi0Props_of_X6Props : X6Props … → R5ptProps X Ψ → R5fpCount → R2X6CMExact Ψ π₆ →
  AGInputs π₆ → GeometricallyConnected X.hom`. The conclusion is exactly
  `LeafAdopt.R1pi0Props X`, and the statement is over the genuine definitions of
  `ZInQKernel/HDecomp/QM`.
- Proved inside it:
  - the Galois core (`subsingleton_of_galois`);
  - stabilizers of `ℚ̄`-points are the fixing groups of their residue fields;
  - the closed facts for `ℚ(i) = ℚ(ζ₄)`: `GaussianInt ≃+* 𝓞`, `inertCount6 = 1`, `#Pic = 1`,
    conductor 1;
  - the same closed facts for `ℚ(ζ₃)`;
  - the Galois action on `X ×_ℚ Spec ℚ̄` and its compatibility with connected components
    (`compOf_galois`).

**What remains.**

1. `AGInputs.over0` and `AGInputs.overInf`: every connected component of `X_ℚ̄` contains a
   `ℚ̄`-point over `0` and one over `∞`. This needs curves over `ℚ̄`, nonconstant maps onto `P¹`,
   and finite fibres from `W = Aut(𝒪)/Inn ≅ (ℤ/2)²`.
2. `AGInputs.descend`: connected over `ℚ̄` implies `GeometricallyConnected`.
3. These are standard algebraic geometry that Mathlib v4.35 lacks. They are open glue, not leaves.
4. `R2X6CMExact`, "CM exactly by `ℤ[i]` / `ℤ[ζ₃]`". This is Baba–Granath's clause in its printed
   meaning (option c1). Alternatively it can be derived from `QMDichotomyYu` (option c2, not done).

**Recommendation:** keep `R1pi0Props` as a clause counted inside R1 until (1)–(2) exist. It is now
justified by González–Rotger and Baba–Granath plus standard algebraic geometry, not only by
Deligne §2.
