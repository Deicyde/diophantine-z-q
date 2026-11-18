# c8-conrad3 results log

Base: wip/c8-conrad3 = origin/wip/c8-conrad2 5938de123 (origin/main is an ancestor: checked below).
Build: copied c8-conrad2's .lake/build and lean/.lake/build (cp -a); `lake build ZInQKernel.Contrib.OneProof.C8CFT` no-op.

## Targets (verbatim, ZInQKernel/Contrib/OneProof/C8LocAlg.lean, C8CFT.lean)
- InertiaAtPDecomp (C8LocAlg L173), MinkowskiInertiaQ (C8CFT L192), TwistCharHTWt0 (C8CFT L488).

## Plan (tree inputs found, VERIFIED by reading)
- B3b (HDecomp/B3Unram/B3b.lean, namespace GlueB3Unram): places of Qbar vs primes of B = integralClosure ℤ Qbar;
  le_of_center, exists_smul_eq (profinite transitivity), inertia_conj, mem_inertia_of_center,
  inertia_le_of_unramifiedAt, exists_inertia_neg (stabilizerHom_surjective_of_profinite template).
- G15.Ladic (Contrib/G15/LadicBridge.lean): decomp_spec (jQ), decompEquivLj : Gal(L_j/Q_p) ≃* D_P, tauOf_eq_restrictNormal.
- TauCeti: inertiaSubgroup = fixing subgroup of K^ur; mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self.
- HodgeSplit (OneProof/H/TailS, TailT): Ysp, Ysp_linearIndependent, htMult_eq_finrank_Ysp (E Galois),
  htMult_eq_of_lifts, liftGL; tateTwistInvariants_proof, axSenTate_proof (Contrib, proved).
- Chebotarev: ZInQ.Contrib.frobeniusDense; C9Rhof.eq_of_eq_on_arithFrob.
- Mathlib: NumberField.exists_not_isUnramifiedAt_int_of_isGalois; IsAlgClosed ℂ_[p].
Merged origin/main b1615c9b1 (igusa-drop fold: TailZ79, Main, IgusaDrop only).

## MinkowskiInertiaQ — PROVED (VERIFIED, compiled: scratch/c8-conrad3/C8Mink.lean, 10:40)
`MinkDict.minkowskiInertiaQ_proof : MinkowskiInertiaQ`, #print axioms = [propext, Classical.choice, Quot.sound].
Proof: F = normalClosure ℚ(x); conjugates of x are fixed by all inertia groups (inertia_conj), so F is;
if [F:ℚ] > 1, Mathlib exists_not_isUnramifiedAt_int_of_isGalois gives p; P = center of a place over p in 𝓞 F;
every σ ∈ I(P) lifts to an inertia element of a place of ℚ̄ (exists_inertia_lift: profinite transitivity +
stabilizerHom_surjective_of_profinite for G_F on B = algebraic integers, as in B3b.exists_inertia_neg),
which fixes F, so I(P)=1, e(P)=1 (card_inertia_eq_ramificationIdxIn), IsUnramifiedAt (ramificationIdx_eq_one_iff): contradiction.

## InertiaAtPDecomp — PROVED (VERIFIED, compiled: scratch/c8-conrad3/C8Dec.lean, ~11:15)
`DecDict.inertiaAtPDecomp_proof : InertiaAtPDecomp`, #print axioms = [propext, Classical.choice, Quot.sound].
Helper: ZInQKernel/Contrib/OneProof/C8Ladic.lean = verbatim copy of G15 LadicBridge §1, §2, jField, §5, decomp_spec
(namespace HDec.G0Galois.C8Conrad.Ladic). Reason: importing ZInQKernel.Contrib.G15.LadicBridge next to C8CFT fails:
"import ZInQKernel.Contrib.Different.Local failed, environment already contains 'PkgI6.TraceContainsRamificationIdx'
from ZInQKernel.HDecomp.Textbook.Different" (VERIFIED).
Proof: v₀ = {‖jQ ·‖ ≤ 1}; v = g•v₀ (B3b center lemma + profinite transitivity); τ' = g⁻¹τg ∈ I_{v₀};
finite Galois K: τ'|_K stabilizes primeOf(jQ|K), lifts to G_{Q_p} (G15 exists_lift = Tau Ceti
exists_algEquiv_apply_eq_of_norm_apply_eq); compactness of G_{Q_p} (IsCompact.inter_iInter_nonempty) gives σ with
decomp σ = τ'; σ ∈ I_{Q_p} via Tau Ceti mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self + Padic.natCard_residueField:
roots of X^{p^f}-X are jQ(ζ), ζ^{p^f-1}=1, fixed by τ' (inertia_fix_root, core of B3b cycUnram).

## TwistCharHTWt0 — PROVED (VERIFIED, compiled: scratch/c8-conrad3/C8Twist.lean, ~12:30)
`TwistHT.twistCharHTWt0_proof : TwistCharHTWt0`, #print axioms = [propext, Classical.choice, Quot.sound].
No new cited input. Inputs: R14 (hyp EigenformRepExists), R13 (hyp EigenformHT), Chebotarev (ZInQ.Contrib.frobeniusDense,
proved), Tate's two theorems (tateTwistInvariants_proof, axSenTate_proof, proved), hodge-split's Ysp machinery (proved).
Steps: (1) tr r = ψ tr ρ_g on G_ℚ (eq_of_eq_on_arithFrob); det r = ψ² det ρ_g (2 det M = tr² M − tr M²);
(2) values of ψ|G_Q5 in a finite Galois E (open G_M where tr ρ_g ≠ 0 + coset representatives; no Baire);
(3) Y_0, Y_1 vectors of r and ρ_g over G_E: d = det(y0,y1) ≠ 0 (Tate–Sen independence), d·det ρ(σ) = χ(σ)σ(d);
y = d_r/d_g has σ(y) = ψ(σ)² y; (4) c = √y in ℂ_p (IsAlgClosed): σ(c) = ±ψ(σ)c; sign continuous (orbit map
continuity proved), so σ(c) = ψ(σ)c on G_{E'}; (5) htMult_eq_finrank_Ysp + Tate–Sen: weights of ψ_{E'} are {0}.
No semisimplicity of r needed (determinant route).

## Contrib files (VERIFIED: lake build ZInQKernel.Contrib.OneProof.C8Printed, 13413 jobs, OK)
- C8Ladic.lean (G15 copy), C8Dicts.lean (minkowskiInertiaQ_proof, inertiaAtPDecomp_proof), C8Twist.lean
  (twistCharHTWt0_proof), C8Printed.lean (C8Leaves {conradAppBQp, tateTwistInvariantsInertia}, c8Inputs_of_leaves,
  c8TwistFinite_of_printed, g12DetPZ_of_printed). None imports OneProof.Main.

## Dry run (VERIFIED: scratch/c8-conrad3/C8FoldDryRun.lean, dryrun_out.txt)
c8-conrad2's generated copy (unchanged) + sixContactMin_of_open72_c8 (copy of igusa-drop's top) + frozenTarget_c8
(hP, hC, hTT in place of c8 : C8Inputs) + fold shape sixContactMin_of_open73C8 (OpenTextbookLeaves19C8 = {poincareComplement},
OpenAddedLeaves28C8 = OpenAddedLeaves27 + {conradAppBQp, tateTwistInvariantsInertia}). All #print axioms standard.

## #discharges (VERIFIED: scratch/c8-conrad3/discharges_out.txt)
34 open hypotheses, 16233 theorems checked, 19 discharge one; none from the C8 files (expected: G12DetPZ, DetTate,
poincareComplement, t8 are not open hypotheses of frozenTarget).

## PR #86 (VERIFIED by git show, not merged, not compiled)
origin/proof/poincare-complement-native-20261117 6984d6078: ZInQKernel/Contrib/CloudR2Poincare/FinalUnconditional.lean:24
`theorem poincareComplement_proof : ZInQ.Contrib.AVB1.PoincareComplement`; AVB1/Poincare.lean unchanged on that branch
(git diff HEAD...branch -- ZInQKernel/Contrib/AVB1/ empty); t8_of_poincareComplement takes
`hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement`: same constant, matches.

## Provenance (VERIFIED by reading diophantine_zq.tex)
- conradAppBQp: CITED. L760-762 "Local algebraicity \cite[Appendix B, pp.~32--33]{conrad-local-characters}";
  bibitem L11046-11049 (author preprint Dec 11 2011).
- tateTwistInvariantsInertia: DEPARTURE. No Tate (p-divisible groups / Driebergen) in the bibliography (grep: none);
  the step it proves, L763-764 "removing its integral local Hodge--Tate weight", cites nothing.
- poincareComplement: ELLIOT. L864-865 "Absolute simplicity and Poincar\'e reducibility give an $L'$-isogeny" names the
  theorem, cites nothing. milne-av (v2.00, "Part I, Theorem 12.1(a)", bibitem L11024-11026) is cited only at L10968 for
  V_ℓ(A) ≅ H^1_et(A,Q_ℓ)^∨, and at L564 (Part I, Thms 2.8-2.9) — not for Poincaré reducibility. The leaf's source
  "Milne 1986 Prop. 12.1" (Cornell–Silverman) is not in the bibliography.
- Brinon–Conrad (bibitem L11019-11023) is cited at L10975, L10994 (de Rham closure under duals/subquotients) — the
  natural cited input for the manuscript's L758-759 sentence; not used (TwistCharHTWt0 proved without it).

## Field taint (VERIFIED: scratch/c8-conrad3/C8DryRunTaint.lean, dryrun_taint_out.txt)
From frozenTarget_c8: closure 304467, 18 iterations; tainted fields [hodgeTateDecompAbVar, kleimanPicZeroProper954SiteQ,
kleimanPicZeroProper954, r10, picZeroAbVar, picRepresentableAbVar] — same as c8-conrad2; terminal readers via r10 only
(consumer (iii)).
