# pn-final: `finalStep` proved

**Proved.** `ZInQ.PropN.finalStep` in `scratch/pn-design/PropN.lean` (nt-tyz §4.4) now has a proof.
The statement is unchanged and has no `sorry`. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]`.

**Route** (pn-design §6.A, all in the abstract module `G.M`):
1. `P n` is torsion (`torsion_of_zero`), so `P n = τ y` (`tors_mem_range`).
2. Apply `f = β + id` to `hX`. `f (τ y) = τ (2y)` (`β_τ`).
3. Split the filter `e ≡ 5 ∨ 7` into `F5 ∪ F7` (`filter_or`, `sum_union`). Insert `beta_five`
   (`choose!` gives `k : ℕ → ℤ`) and `beta_seven`. This gives `τ(2y) = τ A5 + τ A7 + 2•W`, where
   `W = f X` and `A5, A7 ∈ ℤ[i]` are explicit.
4. `8•W = 4•τ(2y − A5 − A7) = 0`, because `4 = (2+2i)(1−i)`. So `W` is torsion and `W = τ w`.
5. `τ(2y − A5 − A7 − 2w) = 0`, so `2+2i` divides that element (`τ_eq_zero`), and both its
   components are even. The real part is `2y.re − (a + 2K) − N − 2w.re` and the imaginary part is
   `2y.im + a − 2w.im`. `omega` then gives `2 ∣ a` and `2 ∣ N`, and `ZMod.intCast_zmod_eq_zero_iff_dvd`
   converts that to the `ZMod 2` statement.

**Size.** 103 lines inserted, 1 deleted (the `sorry`). Six helpers (lines 175–203, prefix `final_`):
`final_reHom`, `final_imHom`, `final_reHom_apply`, `final_imHom_apply`, `final_two_dvd_of_dvd`
(multiples of `2+2i` have even components) and `final_four_nsmul_τ` (`4 • τ z = 0`). The proof
itself is about 73 lines. Nothing else in the file was changed or reordered.

**Final compile** (`lake env lean scratch/pn-design/PropN.lean`):
```
PropN.lean:154:8: warning: declaration uses `sorry`   (lemmaN1_core)
PropN.lean:168:8: warning: declaration uses `sorry`   (lemmaN2)
PropN.lean:207:59: warning: Variable name `hn` is not explicitly referenced.
PropN.lean:290:8: warning: declaration uses `sorry`   (matching)
```
No errors. The remaining `sorry`s belong to the other three agents' theorems.

**Statement remark.** None of the statement is false. The proof does not use the hypothesis
`hn : n % 8 = 5` of `finalStep`, so the linter warns that it is unused. It is harmless, and I left
the statement unchanged.

**Build note.** This worktree had no build of the `lean/` (`ZInQ`) package, so the first
`lake env lean` failed with "unknown module prefix 'ZInQ'". One `lake build ZInQKernel` fixed it by
building the project packages only, not Mathlib.
