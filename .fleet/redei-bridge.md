# redei-bridge report (Rédei plan, step 8)

## Proved (no sorry; axioms propext, Classical.choice, Quot.sound)

New module `ZInQKernel/RouteK/Redei/Bridge.lean` (imported by the root `ZInQKernel/RouteK/Redei.lean`;
it imports `Redei/Kernel.lean`, `Redei/Entry.lean`, `Rank5b/Sec3/RedeiStatement.lean` and
`Rank/Statements.lean`). Namespace `ZInQ.RouteK.Redei`.

- `OddGClStatement : Prop`: the statement `odd_gCl_iff` from Probe §3.6, quantified as
  `∀ (n : ℕ) [NeZero n], Odd n → Squarefree n → (Odd (gCl n) ↔ ∀ e : ramSet n → ZMod 2,
  (∀ q, ∑ p, redeiEntry n q p * e p = 0) → e = 0 ∨ e = fun p => if ↑p ∈ n.primeFactors then 1 else 0)`.
  The step-6 task can discharge it with `fun n _ hn hsq => odd_gCl_iff n hn hsq`, provided its
  `odd_gCl_iff` keeps the Probe form, with `n` explicit and `[NeZero n]`.
- `redeiFormula_of_oddGClStatement : OddGClStatement → RedeiFormula`, via
  `gCl_dProd_eq_gBit (h : OddGClStatement) (hd : Odd d) (hB : B.Nonempty) :
  ((gCl (dProd B) : ℕ) : ZMod 2) = gBit d B`. This holds for every nonempty `B`: it needs neither
  `Squarefree d` nor the mod-8 restriction.
- `certifiedRankTYZ_iff_of_oddGClStatement : OddGClStatement → (CertifiedRankTYZCl ↔ CertifiedRankTYZ)`.
- `certifiedRankTYZRk_of_oddGClStatement : OddGClStatement → Rank.CertifiedRankTYZClRk →
  Rank.CertifiedRankTYZRk` (through `T5bCl_eq_T5b`).

Helper lemmas (all prefixed `redeiB_`):
- `redeiB_primeFactors`: `(dProd B).primeFactors = B.map (Embedding.subtype _)`, from `Nat.primeFactors_prod`.
- `redeiB_odd`, `redeiB_squarefree`, `redeiB_two_not_mem`.
- Membership in `ramSet (dProd B)`: `redeiB_mem_ramSet`, `redeiB_two_mem_ramSet_iff`,
  `redeiB_mem_ramSet_cases`.
- `redeiB_mod4_iff`: `Σ_B yBit = 1 ↔ dProd B % 4 = 3`, from `sum_yBit_eq`, i.e. `lam8_prod`.
- `redeiB_div_eq`: `d_B / q = Π_{B∖q} k`.
- `redeiB_entry_eq_lapl`: the Rédei entries on the columns in `B` are `lapl (aBit d) B`; the
  diagonal uses `legBit_prod`.
- `redeiB_sum_entry`: `Σ_{p ∈ ramSet d_B} R_{qp} F p = Σ_{p∈B} (L_B)_{qp} F p + [d_B ≢ 3 (4)] z_q F 2`.
  The column at 2 is `legBit q 2 = muBit q = zBit d q`, which holds by definition.
- `redeiB_kernel_iff`: the kernel condition of the Probe matches the kernel condition of
  `kernel_trivial_iff_redeiG` for `a = aBit d`, `y = yBit d`, `z = zBit d`; the reciprocity input is
  `recip_bits`.

Builds: `lake build ZInQKernel.RouteK.Redei.Bridge` passes with no warnings. `lake build ZInQKernel` passes.

## Left
- `OddGClStatement` itself, which is steps 3–6 (siblings redei-amb and redei-genus, then FourRank).
- Not done, as optional: a main-theorem wrapper `SixContactMin → CertifiedRankTYZClRk →
  OddGClStatement → FrozenTarget`. It would be a one-line composition of
  `certifiedRankTYZRk_of_oddGClStatement` with
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZRk`
  (`RouteK/RankVariants.lean`). I left it out so that the Redei tree does not import the
  main-theorem files; it belongs in `RankVariants.lean`, or next to it.
- `scripts/print_axioms.lean` is unchanged, because the task names no lines in it.

## Notes
- In Lean v4.35, `if_pos`, `if_neg`, `dif_pos` and `dif_neg` are deprecated in favour of
  `ite_eq_left`, `ite_eq_right`, `dite_eq_left` and `dite_eq_right`, which take the same arguments.
- `Redei/Kernel.lean` is still not imported directly by `Redei.lean`; it now comes in through `Bridge`.
