# atkin-li (fleet note)

**Main result: the leaf `ZInQ.GZDecomp.HeckeThetaNewform` is proved outright** (its exact type,
no hypotheses, axioms `[propext, Classical.choice, Quot.sound]`). So `Literature.GrossZagier` is
down to gz-decomp's two leaves `FHNonvanishing` and `GrossZagierHeegner`. **Also proved: gz-theta's
`AtkinLiTwistNew`** (Atkin–Li's twist theorem, weight 2), via strong multiplicity one across levels,
which was backported from Tau Ceti main.

Branch `wip/atkin-li`: merged `origin/wip/gz-theta` 9720252a and `origin/main` 54cc2893. Report:
`docs/research/atkin-li.md`. Log: `scratch/atkin-li/log.md`. Axiom checks:
`scratch/atkin-li/Check{,2,3}.lean`, with outputs `out_check_axioms{,2,3}.txt`.

Declarations proved (all compile; `#print axioms` gives the standard three for each):
```lean
-- ZInQKernel/Contrib/GZTheta/NewCMFinal.lean
theorem ZInQ.GZTheta.newCM : NewCM
theorem ZInQ.GZTheta.heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner :
    ZInQ.SixContactMin → ZInQ.Literature.TYZThm35ReadingA → ZInQ.GZDecomp.FHNonvanishing →
      ZInQ.GZDecomp.GrossZagierHeegner → ZInQ.FrozenTarget
-- ZInQKernel/Contrib/GZTheta/ALFinal.lean
theorem ZInQ.GZTheta.newformUniqueAcrossLevels : NewformUniqueAcrossLevels  -- Miyake 4.6.19/4.6.20
theorem ZInQ.GZTheta.atkinLiTwistNew : AtkinLiTwistNew
theorem ZInQ.GZTheta.heckeThetaNewform_via_atkinLi : ZInQ.GZDecomp.HeckeThetaNewform
-- ZInQKernel/Contrib/GZTheta/ALMain.lean
theorem ZInQ.GZTheta.atkinLiTwistNew_of_newformUniqueAcrossLevels :
    NewformUniqueAcrossLevels → AtkinLiTwistNew
```

How it was proved:
* **`NewCM`.** Take gz-theta's `f_d`. Tau Ceti attaches to it a newform of level `M ∣ 32d²`
  (Diamond–Shurman 5.8.4). gz-theta's `level_eq_of_assoc` forces `M = 32d²`, and multiplicity one
  (DS 5.8.2) gives `f_d = g`, which is new.
* **Atkin–Li in general** (`ALFricke`, `ALBasic`, `ALRep`, `ALArith`, `ALMain`):
  1. A Fricke identity for quadratic twists at any level.
  2. A twist-back step through strong multiplicity one.
  3. The decomposition `h = ∑_{e∣P} c_e g'(eτ)`.
  4. A local argument with the Dirichlet inverse of the newform's coefficients.

  Finding: the Fricke identity alone does not exclude a p-stabilization at p ∥ M. Excluding it
  needs the twist-back step, or Ramanujan.
* **Backport** (Tau Ceti main 4d91513e, under `ZInQKernel/Contrib/TauCeti/Backport/`, NOTICE
  updated):
  - whole modules `Newforms/{OldAtPrime,PrimeDecomposition,SupportAwayFromLevel}`;
  - partial backports of 8 modules;
  - `Newforms/StrongMultiplicityOne/Across.lean`.

  `diffcheck2.py`: MOD-UNNOTED 0, NOTE-ONLY 0.

What remains: nothing for this target. The headline still needs `SixContactMin`,
`TYZThm35ReadingA`, `FHNonvanishing` and `GrossZagierHeegner`. No existing project file was
edited; the only shared file touched is `ThirdParty/TauCeti/NOTICE`, by merge resolution and the
atkin-li entry.
