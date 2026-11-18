# c8-conrad2 (fleet note)

**Result.** In a compiled dry run (standard axioms), the Picard rows `picRepresentableAbVar` and
`kleimanPicZeroProper954SiteQ` feed only consumer (iii) (`hodgeTateDecompAbVar → r10`). Consumers (i) C8 and
(ii) Poincaré reducibility are rerouted. Report: `docs/research/c8-conrad2.md`.

**What compiles** (`ZInQKernel/Contrib/OneProof/`, lake build ok, standard axioms, no `sorry`):
- `C8LocAlg.lean`: `LocAlgExponentEqWeight` proved from the new leaf `TateTwistInvariantsInertia` (Tate 1967 §3.3
  Thm 2 for the completed `K^{ur}`) and Tau Ceti's local class field theory.
- `C8CFT.lean`: `FiniteOfLocAlgTrivialQ` proved from two dictionary glue Props, `InertiaAtPDecomp` and
  `MinkowskiInertiaQ`. The class field theory itself is proved: Krull, a torsion-free open subgroup of `ℚ̄_p^×`, Tau
  Ceti local CFT at every `q`, and the pro-`q` isometry argument (N5's unstated "finite inertia at every other
  prime"). Also `c8TwistFinite_of_leaves`.
- `C8Poincare.lean`: `t8_of_poincareComplement` (T8 from the restored ELLIOT leaf `PoincareComplement`, Milne 1986
  Prop. 12.1, weakened); `C8Inputs` and `g12DetPZ_of_inputs`.
- Dry run `scratch/c8-conrad2/C8DryRun.lean` / `C8FoldDryRun.lean`: generated copy reroute (`gen/gen.py`).
  `frozenTarget_c8` and `sixContactMin_of_open72C8` use the standard axioms; field taint in
  `dryrun_taint_out.txt`.
- `#discharges`: 35 open, 16111 checked, 19 discharge one, none from these files (expected).

**What remains.**
- `TwistCharHTWt0`: the Hodge–Tate half of c8-conrad's `TwistCharHT0`; the unramified half is no longer needed.
  On-the-spot glue with a sketch (HT stable under Hom and semisimplification); unproved.
- The dictionaries `InertiaAtPDecomp` and `MinkowskiInertiaQ` (glue, STANDARD) are unproved.
- Locators: Milne 1986 / Milne AV v2.00 and Tate 1967 are unread on this host (fetch refused). Conrad App. B stays
  unread.
- No fold yet: alone it adds 6 rows and removes none. Fold together with derham-scholze's reroute of (iii); the
  hand-fold spec is in `scratch/c8-conrad2/autofold.json`.
- Known issue: h-trust E1's supplier (Mumford §19, over an algebraically closed field) does not cover `L'`; the leaf
  is stated as Milne's (over any field).
