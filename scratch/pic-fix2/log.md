# pic-fix2 results log

Base: wip/pic-fix be79cb5b; origin/main 2880fef1e already an ancestor (merge: nothing to do). Build copied from
~/dzq-wt/pic-fix (same commit).

## Consumers of `phiAmpleIsogeny` (VERIFIED, grep of ZInQKernel/OneProof)
* Bundle field in OpenAddedLeaves13 (TailZ24) .. OpenAddedLeaves17 (TailZ34), passed `n.phiAmpleIsogeny` by every
  generation map; the only reader is `addedLeaves12_of_open13` (TailZ24:808) via
  `T09Pic.t09SymmIsogenyExists_of_four` -> `t09SymmIsogenyExists_of_mumford veryAmpleIsAmple` ->
  `phiVeryAmpleIsogeny_of_printed h0 h3`, i.e. the chain only uses very ample L.
* Contrib readers (not in the chain): PicDictionary `weilPairingMumford_of_printed/_of_ac/_of_mumford/_final` take
  `h3 : PhiAmpleIsogeny`.
* No bundle field of type `PhiVeryAmpleIsogeny` exists (grep). Narrowing the field = changing the binder of
  `t09SymmIsogenyExists_of_four`/`addedLeaves12_of_open13` (existing constants) or a bypass fold through
  OpenAddedLeaves13..17 and the top chain: a hand fold, outside this task's edit rights.

## Lean (scratch/pic-fix2/Reading.lean), VERIFIED compiled, axioms [propext, Classical.choice, Quot.sound]
* `divisorClass D hD := Pic.mk (D.toModulesᵛ)` = 𝒪(D) for D : IdealSheafData with D.IsInvertible.
* `exists_divisor_of_veryAmple`: IsVeryAmple X c → ∃ D hD, divisorClass D hD = c (D = Z(i^*X_m), vendored
  isInvertible_zeroLocus + nonempty_iso_dual_toModules_tensorObj).
* Leaves: `MumfordKLFiniteDivisorAC` (Mumford 6 App. 1, D effective Cartier, IsAmple ∧ IsVeryAmple),
  `MumfordPhiSurjectiveVAC` (Mumford 8 Thm 1, IsAmple ∧ IsVeryAmple), `AmplePowVeryAmple` (Stacks 01VU (1)=>(5) /
  EGA II 4.5.10; UNVERIFIED numbering).
* `phiAmpleIsogeny_of_reading : MumfordKLFiniteDivisorAC → MumfordPhiSurjectiveVAC → AmplePowVeryAmple →
  PhiAmpleIsogeny` (field as is; surjectivity for L from L^d via λ_L homomorphism, no theorem-of-square leaf).
* `isVeryAmple_bcPic`: very ample base-changes to K̄ (vendored liftBaseChange + pullbackMapTwistIso).
* `phiVeryAmpleIsogeny_of_reading : MumfordKLFiniteDivisorAC → MumfordPhiSurjectiveVAC → PhiVeryAmpleIsogeny`.
* `t09SymmIsogenyExists_of_four_va` (h3 : PhiVeryAmpleIsogeny): the consumer term for a narrowing fold.

## Contribution file, #discharges, autofold (VERIFIED)
* ZInQKernel/Contrib/OneProof/PhiAmpleIsogenyReading.lean (namespace PicFix2; imports PicDictionary and the vendored
  ZeroLocusTensor, EffectiveCartier; not Main). `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyReading`: success, 13700 jobs.
* #discharges (scratch/pic-fix2/discharges.txt):
  DISCHARGES [OpenAddedLeaves17.phiAmpleIsogeny] by PicFix2.phiAmpleIsogeny_of_reading
    still assumes: [PicFix2.MumfordKLFiniteDivisorAC, PicFix2.MumfordPhiSurjectiveVAC, PicFix2.AmplePowVeryAmple]
    axioms: [propext, Classical.choice, Quot.sound]
* autofold.json dry run: `strict count: 34/11 on 45 -> 37/10 on 47; strictest 34/11 -> 37/10` (-1 both).
  FoldDryRun.lean (line 1 stripped) compiles: sixContactMin_of_open36 axioms standard.

## Fold B (narrowing) test on a throwaway copy /tmp/pf2n (reflinked worktree copy, no .git, never committed) — VERIFIED
* `patch -p1 < scratch/pic-fix2/narrow.patch` (TailZ24/26/30/31/34), kinds.tsv row renamed phiAmpleIsogeny ->
  phiVeryAmpleIsogeny, then `autofold.py scratch/pic-fix2/autofold-narrow.json` (real run):
  `strict count: 34/11 on 45 -> 36/10 on 46; strictest 34/11 -> 36/10`; wrote TailZ43 (copy:
  scratch/pic-fix2/NarrowFold-TailZ43.lean.txt), Main switched to sixContactMin_of_open36.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyReading`: success, 13700 jobs,
  3 min 54 s (rebuild from TailZ24 on). `#print axioms ZInQ.OneProof.frozenTarget`: [propext, Classical.choice,
  Quot.sound]. OpenAddedLeaves17.phiVeryAmpleIsogeny : T09Pic.PhiVeryAmpleIsogeny; OpenAddedLeaves18 has the leaves.
* Not run: hash guard (DumpCompact/cmp_hashes), OpenStatements/render_open (integrator steps).

## autofold-both.json (fold A + pic-fix's picZeroAbVar entry) — VERIFIED
* dry run `34/11 on 45 -> 40/10 on 50; strictest 34/11 -> 40/10`; FoldDryRunBoth.lean compiles, axioms standard.
## autofold-picfix-strictest.json (pic-fix's spec, KLSection flagged "strictest reading") — dry run
* `34/11 -> 36/10; strictest 34/11 -> 35/11` (pic-fix's fold is 0 in strictest under the review's rating).
