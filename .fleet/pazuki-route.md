# pazuki-route (fleet note)

**Verdict: target GLUE −1 not met; main result: the arithmetic half of `pazukiCor13Upper` is proved in Lean, and the
fine fold is GLUE-neutral (18 → 18 strict GLUE, +2 LEAF, no `--allow-rise`), with `RiemannPPAV` as its only glue.**

* **New file** `ZInQKernel/Contrib/OneProof/PazukiRoute.lean` (~44 KB, no sorry/axiom/instance, never imports Main):
  * `pazukiCor13Upper_of_fields : GAGAMorphism → PazukiCor13UpperPP → RiemannPPAV → PicRepresentableAbVar →
    KleimanPicZeroProper → MumfordTorsionAlgClosed → AmpleDescendsFieldExt → PazukiCor13Upper`;
  * `symmPrincipalDefinedOver_of_fields`: pazuki-inputs' composite core (a symmetric principal polarization of A_ℂ
    comes from a number field) from the three existing LEAF fields + the new leaf `AmpleDescendsFieldExt`
    (EGA IV 2.7.2, printed form restricted to proper f; locator UNVERIFIED).
  * Proved on the way: h⁰ descends along bcMap (flat base change); the symmetric locus of the Picard scheme is LFT and
    its C-points are the symmetric classes (Kleiman 9.2.5); `SymmetricClassesCountable` (λ_L ∈ Hom(A_ℂ, Pic⁰), free of
    finite rank; fibres in Pic⁰[2]); `CountablePointsDefinedOver` (Mathlib only: C-automorphisms from transcendence
    bases).
* **Checks (VERIFIED):** build +Main +Discharges +PazukiRoute succeeds (14231 jobs); standard axioms;
  `#discharges`: pazukiCor13Upper discharged by `PazukiRoute.pazukiCor13Upper_of_fields` (35 open, 39 discharge one);
  autofold dry run `11/18 on 29 -> 13/18 on 31`, FoldCheck.lean compiles (sixContactMin_of_open49, standard axioms).
* **(A) consumer audit:** negative. The only reader chain is r22_of_upper → R22_Pazuki → thetaPazuki with
  ThetaPointOfFibre; the fibres (QML3) carry no polarization, Ω(τ) and the theta point are analytic, and no open field
  bounds a moduli/theta height by h_F. The analytic-to-algebraic step must stay on the chain.
* **What remains:** `RiemannPPAV` (Riemann's theorem for Ω ∈ 𝔥₂ in scheme form with the theta line bundle). It cannot
  be proved in the tree (no analytic line bundles / GAGA for sheaves). It becomes LEAF only with a reading of a
  scheme-form print (Mumford AV §§2–3 + GAGA; Milne AV notes I.2.8–2.9; Birkenhake–Lange 4.5.1, 8.1, 8.5; all
  UNVERIFIED), and the 11-16 dictionary ruling may still rate it GLUE. With it rated LEAF, this spec gives the −1.
* Report: docs/research/pazuki-route.md; scratch/pazuki-route/ (Route.lean, CP.lean, autofold.json, outputs, log.md).
