# pb-sanity (fleet summary)

**Verdict: pb-bypass's two new leaves `panPrinted` (Pan 2022 Thm 1.0.4, `p ≥ 5`) and `bergerPrinted`
(Berger 2002 Thm 0.7) can be rated printed form.** Their definitions (`A_cris`, `B_cris`, `B_st`, `LocalIsPst`)
are not degenerate, and both statements are consequences of the prints, not stronger (Pan applied to `ρ^∨`,
Berger applied to `V^∨`). Report: `docs/research/pb-sanity.md`.

**What compiles.** `ZInQKernel/Contrib/OneProof/PanBergerSanity.lean` builds with `lake build +…`, has no
warnings and no sorry, uses only the standard axioms (22 theorems checked), and the contribution scan finds no
hits. It proves:
* `p^m · ∏ log[ε_i] · y ≠ 0` in `A_cris`, so `B_cris^+`, `B_cris` and `B_st` are nonzero, `t` is not
  nilpotent, and `A_inf → B_st` is injective. The argument stays in `A_inf` and uses no `B_dR`.
* `G_{ℚ_p}` acts on `B_cris` and on `B_st` by ring automorphisms (`bcrisAut`, `stAut`). This includes a
  proof of `log[xy] = log[x] + log[y]` in `A_cris` via a truncated identity in `ℚ[B][A]`.
* For every finite `K`, `u = log[p♭]` is not `G_K`-invariant (the monodromy variable is genuine).
* `K_0 ⊆ B_st^{G_K}` in dimension form, via Teichmüller lifts of roots of unity of order prime to `p`.
* Representations trivial on some `G_K` (finite `K`) are pst. The quadratic character of a root of unity of
  order prime to `p` (for example the unramified one) is semistable over `ℚ_p`, and it is nontrivial when the
  root is not in `ℚ_p`.
* `#discharges` shows no new discharge, as expected for a sanity file; `r11r12` is still discharged by
  `panBerger_of_printed`. The fold spec is `scratch/pb-sanity/autofold.json`, with the flags updated; its dry
  run compiles (strict count 46/10 → 48/9).

**What remains.** `B_st^{G_K} ⊆ K_0`, in particular that `B_st^{G_K}` is finite-dimensional. `IsSemistableOver`
means Fontaine's condition only because of this. It needs `B_st ⊆ B_dR`, Ax–Sen–Tate and Tate's theorem.
For the same reason no representation failing `LocalIsPst` is exhibited. Unramified characters of infinite
order are not covered (that needs Lang's theorem over `W(k̄)`).
