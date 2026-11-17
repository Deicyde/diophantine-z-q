# goodmodel-iso results log

## 11-16 16:10 setup
- Base wip/group-law-dvr 3ab4d8eb; merged origin/main (already ancestor, c1e4ed1b) and origin/wip/neron-ext (901a0efd), no conflicts.
- Top bundle on this tree: TailZ45 `sixContactMin_of_open38 (r : OpenResearchLeaves28) (t : OpenTextbookLeaves13) (l : OpenAddedLeaves19)`;
  `mumfordGroupLawConn` in r (TailZ45:58 region), `neronSchemeExtensionExists` in t (TailZ44:110). VERIFIED (read).
- group-law-dvr's F2 patch generator scratch/group-law-dvr/fold/make_patch.py targets this same TailZ45 (main unchanged since). VERIFIED (read).

## Route analysis
- Suggested step (1) "F is a Néron model (BLR 1.2/8)" needs a group law on F: the tree's proof
  (NeronExt.isNeronModelOver_of_grpObj, NeronExtAb.lean) takes `[GrpObj X]`; its Weil-extension step
  `RelativeGroupLaw.exists_opens_diagonal_difference_extension` uses the target's group law. In
  NeronGoodModelIso, F has no group law (constructing it is the point of MumfordGroupLawDVR). So (1) is circular. VERIFIED (read).
- Build: copied (reflink) ~/dzq-wt/group-law-dvr/.lake/build and lean/.lake/build (same base commit 3ab4d8eb).

## Plan (purity-free route, all tools located; VERIFIED by reading statements)
NeronGoodModelIso for an arbitrary smooth separated N follows from the case where N carries a group law with
e ≫ ψ = η_N, given a Néron model over R (NeronSchemeExtensionDVR): χ : N → N' (Néron), χψ iso by the group case,
then ψ has a left inverse and ψ ∘ (χψ)⁻¹ χ = id_N by density. Group case:
 A. V ⊂ N open, v : V → F (FLT `NeronModelInfra.exists_opens_extension_of_isProper_of_smooth`, target F proper):
    V ⊇ generic fibre, V meets every irreducible component of N_k.
 B. ψ ∘ v = ι_V and v ∘ ψ = id on ψ⁻¹V (density: flat source, separated target).
 C. ψ injective on points: on ψ⁻¹V by B; on F_k by rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`,
    FrobChain/Rigidity.lean: pointed map AbVar → separated lft group scheme over any field is a hom) and a
    translation argument with field-valued points (no k̄, no descent).
 D. For z ∈ N: ψ⁻¹{z} ⊆ affine Y; U' ∋ z affine with ψ⁻¹U' ⊆ Y (ψ closed).
 E. Hartogs (`existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk`, stalks normal by
    `Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing`, dim ≤ 1 points in V by
    `mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing`): v|U'∩V extends to U' → Y.
 F. ψ iso over each U' ; G. iso is local on the target.
- 16:45 Part1.lean compiles: genMap_ne_closedPoint, ext_of_generic_open, exists_inverse_open (steps A-B: V, v, B1 v≫ψ=ι, B2 (ψ∣V)≫v=ι). VERIFIED (lake env lean, no errors).
- 17:10 Part1.lean: eq_of_comp_eq and isIso_of_injective (steps D-G: injective ψ ⇒ iso via Hartogs) compile, no sorry. VERIFIED.
- 17:45 fibreMap_isMonHom (rigidity on a field fibre via MulRigidity.isMonHom_of_geometricallyIntegral) and fibre_injective (translation by field-valued points) compile. VERIFIED.
- 18:05 isIso_of_grp (group case: N smooth sep qc with GrpObj, e≫ψ=η) compiles, no sorry. VERIFIED.
- 18:15 **NeronGoodModelIso PROVED from NeronSchemeExtensionDVR** (scratch/goodmodel-iso/GoodModel.lean, was Part1.lean):
  `neronGoodModelIso_of_dvr : NeronSchemeExtensionDVR → NeronGoodModelIso`,
  `neronGoodModelIso_of_dedekind`, `mumfordGroupLawDVR_of_dedekind : NeronSchemeExtensionDedekind → MumfordGroupLawDVR`.
  `#print axioms` both: [propext, Classical.choice, Quot.sound]. VERIFIED (lake env lean).
  Note: the glue is proved from the leaf that F2 already carries (NeronSchemeExtensionDVR, the DVR case of the
  Dedekind leaf), not from Mathlib alone: the general-N statement is reduced to the Néron-model case.
- 18:40 Contribution file ZInQKernel/Contrib/OneProof/NeronGoodModelIso.lean (global `instance` replaced by a theorem +
  local haveI); `lake build ZInQKernel.Contrib.OneProof.NeronGoodModelIso` OK (12803 jobs), axioms standard. VERIFIED.
- Fold G: scratch/goodmodel-iso/fold/make_patch.py (16 files: narrowing of group-law-dvr in TailZ23..44, TailZ34;
  TailZ45 research field mumfordGroupLawConn -> neronSchemeExtensionDedekind; new OpenTextbookLeaves14 without
  neronSchemeExtensionExists; sixContactMin_of_open39; Main.lean switched). Overlay compile running
  (compile_overlay.sh /tmp/gmifold/G, 42 modules).
- 19:20 Fold G overlay: 42/42 modules OK; frozenTarget standard axioms; #discharges on folded tree: 44 open (was 45); MumfordGroupLawConn out of closure; NeronSchemeExtensionExists only a proved intermediate. Contributor #discharges recorded (scratch/goodmodel-iso/discharges.txt). VERIFIED.
