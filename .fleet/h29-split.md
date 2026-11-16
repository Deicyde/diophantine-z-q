# h29-split (fleet summary)

**Verdict.** The top hypothesis `h29 = ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` of `ZInQ.OneProof.frozenTarget` is
proved in Lean from four statements over genuine definitions:
`tyzLemma29Mod2_of_printedLeaves_threeSquares (LegendreJonesPall) (TYZTestVectorExists) (TYZLemma29Printed)
(TYZProp23Printed) : TYZLemma29Mod2`, axioms `[propext, Classical.choice, Quot.sound]`. `#discharges` reports
`DISCHARGES [h29]` for it (and for the variant with `TYZTauExists` in place of the three-square leaf).

**Leaves.** TYZ Lemma 2.9 (L1062–1066) and Proposition 2.3 (L580–585) in printed form (restricted to
`n ≡ 1, 3 (mod 8)`; Lemma 2.9 admits the factor `w_K = 3` at `n = 3` that TYZ's own proof produces), the
existence of the test vector `f_n` (TYZ §2.1 with Theorem 2.6 at `χ = 1`; flagged pending reading because
`π^{U_n}` is pinned by its Hecke eigenvalues `a_p(E)`, a standard but unprinted bridge), and Legendre's
three-square theorem with the `4 ∣ c` refinement TYZ cite (Jones–Pall Thm 5, not read). Every statement was
checked against `~/tyz-src/Period7.tex` (now on the host) line by line; a fresh agent's second read found no
false, vacuous or too-strong leaf.

**Genuine objects (Lean).** `B = ℍ[ℚ]`, Hurwitz `O_B`, `B̂ = ℍ[𝔸ᶠ_ℚ]`, `τ`, `τ̂` through Tau Ceti's base change
`𝔸ᶠ_{K_n} ≅ 𝔸ᶠ_ℚ ⊗ K_n`, `R̂_n`, `K_{n,2}^×`, `U_n`, `π_ℤ^{U_n}`, `f_n`, `Cl_n` via Tau Ceti's `toClassGroup`, `Q(n)`.
Glue proved: mod-2 reduction, `Q(n) ≡ g(n)` from oddness on squares (class-group step via `ker_toClassGroup`), and
`TYZTauExists` from the three-square statement (explicit `τ`, `τ(O_K) ⊂ O_B` from trace/norm integrality).

**What compiles.** `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` (the contribution, the only file added
under ZInQKernel), `scratch/h29-split/H29Split.lean` (plus run 1's inertness and Thm 1.1 checks), `Tau.lean`;
`lake build` of Main + Discharges + the contribution succeeded; outputs in `scratch/h29-split/`.

**What remains.** The fold is by hand: `autofold.py` folds bundle fields only and `h29` is a plain argument
(`scratch/h29-split/autofold.json` gives the term and leaves; report §5 gives the Main.lean edit). Leaves unread
by a human; Jones–Pall Theorem 5 unread. Report: `docs/research/h29-split.md`; log: `scratch/h29-split/log.md`.
