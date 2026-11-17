# etaw32-proof log

Base wip/leaf-fold33b 0e3c3125; `git merge origin/main`: already up to date. Build tree copied (reflink) from
~/dzq-wt/leaf-fold33b (byte-identical Main.lean).

## Target
`ZInQ.CdOpt.EtaW32Character` (ZInQKernel/Contrib/OneProof/CdOptimal/Level32.lean:56), copied verbatim in
`Target.lean` (`same : EtaW32Character = ZInQ.CdOpt.EtaW32Character := rfl`). VERIFIED (compiled).

## Results (all VERIFIED: compiled with `lake env lean` / `lake build`, Lean 4.35.0, Mathlib v4.35.0)
- `ZInQKernel/Contrib/OneProof/EtaW32Character.lean`: `ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof :
  ZInQ.CdOpt.EtaW32Character`. Axioms [propext, Classical.choice, Quot.sound]. `lake build
  +ZInQKernel.Contrib.OneProof.EtaW32Character`: success (13 s). No sorry, no native_decide, no new hypothesis.
- `#discharges` (Discharges.lean, output discharges-output.txt line 198):
  `DISCHARGES [hW] by ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof / still assumes: [] /
  axioms: [propext, Classical.choice, Quot.sound]`.
- `FoldCheck.lean`: `ZInQ.OneProof.frozenTarget_etaW32` (Main's frozenTarget body verbatim with the binder hW removed
  and filled) and `frozenTarget_etaW32'` (from Main's theorem) prove `ZInQ.FrozenTarget`; axioms standard
  (foldcheck-output.txt).
- `EtaW32Scratch.lean`: the scratch version of the proof (namespace ZInQ.CdOpt.EtaW32Proof), compiles.

## Proof steps (lemma names in the Contrib file)
1. `eta_add_int`: η(z+n) = e^{πin/12} η(z) (from Mathlib's definition of η).
2. `sqrt_mul_branch`: √y√z = i√w for y,z,w ∈ ℍ with yz = −w (both sides have Im > 0).
3. `eta_lower`: η(z/(nz+1)) = e^{−πin/12} √(nz+1) η(z), n ≥ 1, from Mathlib's `eta_comp_eq_csqrt_I_inv`.
4. `etaD_c32`, `vC_c32`: for γ = (4A+1, b; 32, 4B+1): v(γτ) = e^{πi(A+B)/4} v(τ) (the √(32τ+d) factors cancel,
   1 + 2 − 3 = 0).
5. `exp_eq_chi8`: e^{πi(A+B)/4} = χ₈(4B+1) from (4A+1)(4B+1) − 32b = 1 (A+B = 4(2b − AB), A ≡ B mod 2).
6. `P_c32`: all γ with c = 32 (a ≡ 3 mod 4 through −γ⁻¹); `P_c32_abs`: c = ±32; `P_c0`: c = 0 (`vC_add_int`).
7. `P_of_mem`: strong induction on |c|: c = 32k, |k| ≥ 2 ⇒ k ∤ a ⇒ odd s with |a + sk| < |k| (`exists_odd_s`);
   g = (u, −v; 32, s) (`exists_row32`, Bezout) gives gγ ∈ Γ₀(32) with |c(gγ)| = 32|a+sk| < |c|; `P_cancel`
   (χ₈ multiplicative on lower-right entries of Γ₀(32)).

No generating set, no numerics: the reduction uses the infinite family of elements with c = 32, each handled
symbolically.
