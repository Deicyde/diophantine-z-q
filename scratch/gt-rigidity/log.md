# gt-rigidity results log

Target: `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (ZInQKernel/OneProof/H/TailZ16.lean L463).

## Setup
- Base a454ad64. Build tree copied from ~/dzq-wt/gt-qm (same base, no ZInQKernel diff). `lake build +Main +Discharges`: only Main rebuilt (96 s). VERIFIED.

## Plan (decided)
- GIT Thm 6.14 (existence of the group law) is not provable from Mathlib 4.35 (needs deformation theory of the group law, Grothendieck existence). Kept as leaf `MumfordGroupLaw` (Core minus clause (a)).
- Clause (a) (GIT Cor. 6.4) to be PROVED in Lean from the printed rigidity lemma (GIT Prop. 6.1, leaf `RigidityLemma`, S connected).

## Step 1 (11-14 23:20): reduction compiled — VERIFIED
- scratch/gt-rigidity/MR.lean (imports TailZ16): `mumfordRigidityCore_of_printed : MumfordGroupLaw → RigidityLemma → MumfordRigidityCore`; `#print axioms` = [propext, Classical.choice, Quot.sound].
- Glue proved on the way: noetherian space ⇒ connected components open; locally noetherian scheme ⇒ connected components open; `eq_of_rigidity` (rigidity on each connected component, via restriction to the open component and `Scheme.hom_ext_of_forall`); `isPullback_jr` (x ↦ (x,1) is the base change of η along snd); `fibre_value`; `defect_eq_one`; `isMonHom_of_rigidity` (GIT Cor. 6.4 for endomorphisms of a group object proper smooth geometrically connected over a locally noetherian base).

## Step 2 (11-14 23:40): contribution file — VERIFIED
- ZInQKernel/Contrib/OneProof/MumfordRigidity.lean (imports TailZ16 only). `lake build +Main +Discharges +MumfordRigidity`: success.
- #discharges (scratch/gt-rigidity/Discharges.lean; output in discharges-output.txt):
  DISCHARGES [OpenResearchLeaves16.mumfordRigidityCore] by ZInQ.Contrib.MumfordRigidity.mumfordRigidityCore_of_printed
    still assumes: [MumfordGroupLaw, RigidityLemma]; axioms: [propext, Classical.choice, Quot.sound]
  (67 open hypotheses, 514 theorems checked, 1 discharge one)
- `mumfordGroupLaw_of_core : MumfordRigidityCore → MumfordGroupLaw` compiled (the existence leaf is strictly weaker).

## Step 3 (11-15 ~00:30): second route — VERIFIED
- New leaf `PushforwardStructureSheaf`: p proper, smooth, geometrically connected over locally noetherian S ⇒ `Function.Bijective (p.app U)` for all opens U (EGA III 7.8.6 / Stacks 0E0L / Mumford AV §5; numbers UNVERIFIED).
- Proved: `eq_of_pushforward` (local rigidity: f' over p with section j, f'(X_t) a point for every t ⇒ f' = p ≫ j ≫ f'), `fibre_point_of_field` (defect constant on every fibre of pr₂, via base change to the residue field and `MulRigidity.isMonHom_of_geometricallyIntegral`), `defect_eq_one_of_pushforward`, `isMonHom_of_pushforward`, `geometricallyIntegral_of_isAbVarFibre`, `mumfordRigidityCore_of_pushforward : MumfordGroupLaw → PushforwardStructureSheaf → MumfordRigidityCore`.
- Merged into ZInQKernel/Contrib/OneProof/MumfordRigidity.lean (545 lines). Build OK, no warnings from the file.
- #discharges: 2 theorems discharge `OpenResearchLeaves16.mumfordRigidityCore`:
  - `mumfordRigidityCore_of_printed` still assumes [MumfordGroupLaw, RigidityLemma]
  - `mumfordRigidityCore_of_pushforward` still assumes [MumfordGroupLaw, PushforwardStructureSheaf]
  both axioms [propext, Classical.choice, Quot.sound]; "67 open hypotheses, 521 theorems checked, 2 discharge one".

## Step 4: wrap-up
- docs/research/gt-rigidity.md written (verdict first). scratch/gt-rigidity/MR.lean and MR2.lean are the development copies, superseded by the contribution file (same declarations).
- Not done: `MumfordGroupLaw` in printed form (S connected, one fibre) + Lean gluing of GrpObj over components; global half of `RigidityLemma` from `PushforwardStructureSheaf`.
