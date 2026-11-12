# pn-n2 log: `lemmaN2` in scratch/pn-design/PropN.lean

## Setup
- The worktree had no build of the `lean/` (z_in_q) dependency: `lake env lean` failed with
  "unknown module prefix 'ZInQ'". `lake build ZInQKernel.Hypotheses.CR3Literature` built it
  (3 min; Mathlib untouched). Build output is not tracked by git.

## Step 1: scratch proof (scratch/pn-n2/N2.lean = head.lean + body.lean + main.lean)
Statements (prefix `n2_`):
- `n2_c ε L e d` : ℤ[i], the coefficient of Z(e) in P(d), by well-founded recursion
  `n2_c e d = [e = d] − Σ_{q ∣ d, 1<q, q≡1,3} ε(d/q,q) L(q) n2_c e (d/q)`; `n2_c_eq` unfolds it.
- `n2_P_eq` : for d ∣ n, d ≡ 5,7: `P d = Σ_{e ∣ n, e ≡ 5,7} n2_c e d • Z e` (strong induction;
  fixed index set, so the swap is `Finset.sum_comm`).
- `n2_c_mod` : in R = ℤ[i]/(2), `π(n2_c e d) = if e ∣ d then φ(d%8, e%8) · L(d/e) else 0`
  (strong induction; case e = d; case e ∣ d, e ≠ d: split off q = m = d/e, cancel the rest by
  `Finset.sum_involution` with q ↦ m/q; squarefree n gives m/q ≠ q).
- finite residue checks `n2_kappa` (κ(q) = κ(m/q)), `n2_last` (ε(e, m) ≡ φ(d, e)), `n2_eps`
  (π ε from `eps_53`/`eps_pm1`; −i ≡ i mod 2).
- `lemmaN2`: specialize to d = n (φ = 1), write `n2_c e n = L(n/e) + 2 w_e`, X = Σ w_e • Z e.
Compile: first run 3 errors (norm_num `at h ⊢` "no goals"; `mul_smul` direction; omega on
`m / q`), fixed. Second run: no errors, no warnings. `#print axioms lemmaN2`:
[propext, Classical.choice, Quot.sound]. Size: 259 lines helpers + 26 lines lemmaN2.
