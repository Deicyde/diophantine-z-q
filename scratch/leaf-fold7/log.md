# leaf-fold7 results log

## 2026-11-14 06:40 PST start
- Base debc37b4 (wip/w56). OneProof top: HDec.HSyn.sixContactMin_of_open6 (68 fields: 26 + 21 + 20 + 1).
- Read reports: av-glue, curve-split, av-split, height-split, hodge-split, qm-split, mcr-glue, frontier r3.
- Plan (strict decision rule): side modules (kernel imports only) for av-glue, av-split, curve-split, hodge-split;
  qm-split pieces over the chain (import TailO); final bundle module importing TailO and the side modules.
- 06:45 started `lake build +ZInQKernel.OneProof.Main` (TailL-TailO and ~36 kernel modules were out of date).
- 07:01 base build done (`lake build +ZInQKernel.OneProof.Main`, exit 0; the chain LPrefix..TailO was rebuilt since
  kernel modules it imports were out of date, ~15 min). DumpCompact (copy in scratch/leaf-fold7/) before any change:
  8594 OneProof constants hashed -> hashes_before.txt; frozenTarget axioms standard.
- 07:05-07:40 side modules compiled one at a time with `lake build ZInQKernel.OneProof.H.TailX` for X = P (av-glue,
  20 s), Q (av-split, with the kernel module FrobChain.Rigidity imported in place of its verbatim MulRigidity copy,
  27 s), R (curve-split, 12 s), S+T (hodge-split halves, 71 s), U (qm-split over the chain, 57 s), W (mcr-glue
  parts 1-3 over the chain, 11 s): all exit 0 at the first try.
- TailV (hodge transports): FiniteImageHT, SenTwist, R14Det, T23 accepted by unfolding (GaloisRep/GaloisChar
  converted field by field). R10 (`DeRhamComparisonHT`) timed out at whnf (4M heartbeats): the chain's
  `PkgI4.I3.AbVar.galRep` and G9's are on Tate modules with separately defined `Module ℤ_[p]` instances; the
  predicates `IsDeRhamOver`/`htMultOver` agree for the same representation (Iff.rfl, fast), but the two `galRep`s do
  not unify in reasonable time. r10 left unfolded for now.
- TailX (bundles, `sixContactMin_of_open7`) compiled at the first try; Main switched to it.
  `lake build +ZInQKernel.OneProof.Main`: exit 0; `#print axioms ZInQ.OneProof.frozenTarget`: propext,
  Classical.choice, Quot.sound. DumpCompact after: 9934 constants; cmp_hashes.py: 0 removed, 1 changed
  (frozenTarget itself, the statement change), 1340 new, all in TailP-TailX (cmp_hashes_out.txt).
- 07:40-08:00 r10 (H-8) folded: TailV proves `IsDeRhamOver`/`htMultOver` (G9's) invariant under an isomorphism of
  representations (`isDeRhamOver_congr`, `htMultOver_congr`, via `ddrSpaceOver`/`htSpaceOver` ≃ φ ↦ φ ∘ e), and
  that the identity `vEquiv : (toG9AbVar A).V p ≃ₗ A.V p` intertwines the two `galRep`s (pure tensors: `congr 1`
  closes by unfolding `galT`). `HodgeLF7.r10 : ZInQ.Contrib.R10.DeRhamComparisonHT → PkgI4.DeRhamComparisonHT`.
  TailX: `r10` → `hodgeTateDecompAbVar`, `deRhamH1AbVarT`. Main builds, axioms standard; DumpCompact/cmp_hashes
  rerun (cmp_hashes_out.txt).
- 08:05 two more folds: `x0Transitive` (H-41, consequence) → the kernel leaf `ZInQ.RLeaf.IgusaGL2` (Igusa's theorem
  as printed; curve-split's X0Split.lean appended to TailR); `r13` (H-10, consequence of Kato) → hodge-split's
  `EigenformHTNew` (the newform case, a strictly smaller statement of the same form), with T25 from the kernel's
  `T25.newformOfEigenform_leaf` (accepted on G9's copy by unfolding) and the DS leaves already fields. Main builds,
  axioms standard, DumpCompact/cmp_hashes rerun.
- 08:15 `shimuraGoodReduction` (H-83) → curve-split's `ShimuraGoodReductionNoGuard`, stated in TailW inside
  `namespace HDec` over the chain's own vert-witness definitions (curve-split's root copies of `IsShimuraModel` etc.
  not used); `shimuraGoodReduction_of_noGuard` with `R1R2fp` from the field `r1r2`. Main builds, axioms standard,
  DumpCompact rerun.
- 08:20 Check7.lean (closure 186483 constants, no sorryAx; 69 fields, 33 kernel heads) -> check7_result.txt;
  verbatim_check7.py -> verbatim_check7_out.txt (only documented removals; one docstring line of X0Split that my
  generator had dropped was restored in TailR, then rebuilt and rechecked).
- 08:40 report docs/research/leaf-fold7.md written (head + generated field tables + tail in scratch/leaf-fold7/).
