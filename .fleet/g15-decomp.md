# g15-decomp (fleet note)

**Main result.** The G15 transport "`D_P ≅ Gal(L_P/ℚ_p)` with the lower ramification filtrations"
(STANDARD, not in Lean in `h-decomposition.md`) is now proved in Lean, closed, with axioms
`[propext, Classical.choice, Quot.sound]` only. It is proved for both readings of `L_P`:
- **Mathlib's completion `L_w`** (`ZInQ.Contrib.G15`): `decompEquiv : decompGroup L P ≃* Gal(L_w/ℚ_v)`,
  `map_ramGroup_decompEquiv` (sends `ramGroup L P i` onto Tau Ceti's `lowerRamificationGroup i`),
  `ramCard_eq_card_localRam`, and `card_decompGroup_eq_finrank`. The intermediate-field forms
  `index_localSub_eq_finrank` and `normalCore_localSub_eq_bot` turn `D1_local`'s hypotheses into
  statements about completions. `D1_completion` is closed.
- **The kernel's `LadicCond` local field `Lj j = ℚ_p(j L)`**, for any `j : L →+* ℚ̄_p`, which is
  what `G15RamG` uses (`ZInQ.Contrib.G15.Ladic`):
  - `mem_ramSet_iff`: `σ ∈ ramSet (Lj j) i ↔ τ ∈ ramGroup L P i` when `j ∘ τ = σ ∘ j`, with
    `P = primeOf j`;
  - `ramCard_Lj_eq`;
  - `decompEquivLj : Gal(Lj/ℚ_p) ≃* D_P`;
  - `isFinGal_Lj`;
  - `phiAt_Lj_eq` / `phiAt_Lj_natCast` (`φ` equals the kernel's `GlueConductor.phi`);
  - `mem_upperSet_iff`;
  - the ℚ̄-form via `PkgI4.decomp` (`decomp_spec`, `tauOf_eq_restrictNormal`);
  - `D1_Lj` (D1 stated in `LadicCond` terms);
  - `apply_j_eq_of_mem_upperAbs` / `restrictNormal_decomp_eq_one_of_mem_upperAbs`: if `e ≤ a!`
    and `v > 4a²`, every `σ ∈ G_{ℚ_p}^v` fixes `L`. This is clause (i) of G15 for one number field.
- `Combined.lean` shows the two readings agree: `LadicCond.ramCard (Lj j) i = |G_i(L_w/ℚ_v)|`,
  `[Lj : ℚ_p] = |D_P| = [L_w : ℚ_v]`, plus a tame criterion.

**Compiles.** These six new files under `ZInQKernel/Contrib/G15/` compile (132 declarations):
- `Transport.lean`
- `D1Completion.lean`
- `LadicBridge.lean`
- `LadicD1.lean`
- `LadicUpper.lean`
- `Combined.lean`

`lake build` of the leaf modules succeeds. `scratch/g15-decomp/Axioms.lean` checks every
declaration; its output is in `axioms-out.txt`. No new Tau Ceti modules were needed, and no
existing file was edited.

**Remains.**
- Krasner's choice of the number field. This was not part of the task.
- Clauses (ii) and (i) of G15RamG on the actual `r_ℓ`. These belong to g15-ram.
- The relation `wildSet ⊆ ramSet (Lj j) 1`, which was not proved. D2 in the kernel is already
  stated over `ℚ̄_p`, so this relation is probably not needed.

**Report:** `docs/research/g15-decomp.md` lists the exact types of all main declarations. The
log is `scratch/g15-decomp/log.md`.
