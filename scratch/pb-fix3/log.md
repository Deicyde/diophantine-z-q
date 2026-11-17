# pb-fix3 results log

Base: wip/bst-construct fe8b30667, merged origin/main c0f3d085c (merge commit 28894b5f2).

## Inputs read (VERIFIED: read in the named files)

* `BergerBst.PanPrintedB` (ZInQKernel/Contrib/OneProof/BergerBst.lean:402): pb-fix2's `PanPrintedU` with
  `LocalIsPstB`; hypothesis `LocalDistinctHTU` (htMultU = finrank_Qp (ℂ_p(w) ⊗ V)^G / finrank_Qp E, a Nat
  division), conclusion with kernel `IsNormalizedEigenform g χ` and the trace form.
* `BergerBst.BergerPrintedB` (BergerBst.lean:394): `Continuous ρ → LocalIsDeRhamU → LocalIsPstB`.
* Current bundle `OpenResearchLeaves31` (TailZ50): fields `r11r12 : PkgI4.PanBerger`,
  `dsThm965Printed : DSCoeffExt.DSThm965Printed`, `eigenformCoeffFieldFinite`, `dsThm966Printed :
  DSThm966EV.DSThm966Printed`. `dsThm965Weak`/`dsThm966` are no longer fields: bst-construct's
  `panBerger_of_printedB_weak` must be rerouted through `DSCoeffExt.dsThm965Weak_of_printed` and
  `DSThm966EV.dsThm966_of_printed`.
* Dictionary already in the tree: `DSCoeffExt.isNormalizedEigenform_iff_DS` (kernel coefficient form ⇔ DS Def
  5.8.1 over Tau Ceti `Eigenform`); Tau Ceti `EigenformAwayFromLevel.exists_newform_eigenvalue_eq`
  (DS Prop 5.8.4 existence half), `Newform.toEigenform`.
* Pan's printed wording (rv-h-a011 §2, VERIFIED there from FM.tex L226-233, L253, L268, L270): continuous
  irreducible ρ : G_Q → GL_2(Q̄_p), finitely ramified, pst at p, odd, distinct HT weights of ρ|G_Qp; conclusion
  "comes from a cuspidal eigenform up to twist"; ρ_g attached through the fixed ι_p; geometric Frobenius; ε has
  HT weight −1. The TeX is not on this host.

## Steps
1. Built `BergerBst`, `DSThm966EV` (and their closure, 3.5 min) and Tau Ceti `Newforms.Decomposition`,
   `Newforms.FullEigenform`. VERIFIED (lake build).
2. `scratch/pb-fix3/PanDict.lean` (namespace `HDec.PkgI4.PanDict`) compiles with no errors or warnings; axioms of
   `panBerger_of_printedPV`, `localDistinctHTP_iff`, `exists_normalized_of_eigenform`,
   `exists_eigenform_of_normalized`: [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
   * `htMultE ρE w := finrank E (V ⊗_{ℚ_p} ℂ_p(w))^{G}` (printed: dim over the coefficient field);
     `htMultE_eq_htMultU` (= pb-fix2's finrank_Qp/[E:Q_p]); `localDistinctHTP_iff : LocalDistinctHTP ↔
     LocalDistinctHTU`.
   * `IsIrreducibleP` (no stable subspace but 0, all) and `isIrreducibleP_of` (Burnside form ⇒ printed).
   * `one_le_weight` (nonzero cusp form on Γ₁(N) has k ≥ 1, from Mathlib's isZero_of_neg_weight,
     eq_const_of_weight_zero and vanishing at i∞).
   * `IsAttachedVia ιp g ρg` (tr ρg(σ⁻¹) = ιp⁻¹ λ_q(g) for almost all q ∤ N, unramified there), `IsTwistOf ρ ρg ψ`
     (ρ(σ) = ψ(σ) P ρg(σ) P⁻¹), `trace_of_twist`.
   * `exists_normalized_of_eigenform` (EigenformAwayFromLevel ⇒ normalized newform at M ∣ N in kernel form,
     same a_q for q ∤ N) and converse `exists_eigenform_of_normalized`.
   * Leaves: `PanPrintedP` (Pan 1.0.4, printed hypotheses and conclusion), `BergerPrintedV` (Berger 0.7 for one
     continuous ρE : G_Qp → GL_n(E)); glue `panPrintedB_of_printedP`, `continuous_model`, `bergerPrintedB_of_V`,
     `panBerger_of_printedPV (PanPrintedP) (BergerPrintedV) (DSThm965Printed) (EigenformCoeffFieldFinite)
     (DSThm966EV.DSThm966Printed) : PanBerger`.
3. Contribution `ZInQKernel/Contrib/OneProof/PanBergerDict.lean` (mkcontrib.py). `lake build
   +…PanBergerDict +…OneProof.Main +…OneProof.Discharges`: success, 13062 jobs, 15.5 min; PanBergerDict built in
   7.5 s, no warnings. VERIFIED. (build2.txt in the repo is a mid-build snapshot; the end lines were checked.)
4. Axioms (Axioms.lean, 11 decls): standard only. VERIFIED.
5. #discharges: `DISCHARGES [OpenResearchLeaves31.r11r12] by HDec.PkgI4.PanDict.panBerger_of_printedPV`, still
   assumes PanPrintedP, BergerPrintedV, DSThm965Printed, EigenformCoeffFieldFinite, DSThm966EV.DSThm966Printed;
   standard axioms; "35 open hypotheses, 10328 theorems checked, 39 discharge one". VERIFIED.
6. Autofold dry run: "strict count: 11/18 on 29 -> 13/17 on 30; strictest 11/18 -> 13/17"; FoldDryRun.lean
   compiles, sixContactMin_of_open49 standard axioms. VERIFIED. scan_contrib: 0 hits.
7. Ratings: panPrintedP printed form (hypotheses and conclusion transcribed; dictionaries proved); bergerPrintedV
   printed form (one p-adic representation V = E^n, continuous). Flags: Pan L253 attachment formula recalled,
   JAMS numbering UNVERIFIED; Berger §1.2 wording UNVERIFIED.
