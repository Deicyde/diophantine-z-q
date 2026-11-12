# hdec-elementary log

## Step 1 (read sources)
- Read: h-trust.md §§0-2 (36 steps A1-F4), wk-h.md (whole), rv-lit.md §4-5, prereq-survey.md,
  Lean: Hypotheses/Height.lean (SixContactEstimate, contactSupport, heightH6, heightD, heightE0),
  HeightMin.lean (SixContactMin), JHeight.lean (JHeightBound S; sixContactMin_of_jHeightBound proved).
- Facts: SixContactMin = ∀ u ∉ 𝒞, ratHeight u ≤ heightH6 D * M_{S_mul}(u)^24.
  JHeightBound S = ∀ u ∉ 𝒞, ratHeight (Jmap u) ≤ (40·10⁴·2²⁴+22) * heightX D * M_S(u)^24,
  Jmap u = −57600 F(u)²/G(u)⁶.
- wk-h §4.3: abstract signature (ArakelovSig) admits a fake model ⇒ the packaged hypothesis is a
  j-height bound in disguise. Must avoid that in this task.

## Step 2 (read N5 §4 L377-972; design)
- Read N5 L377-964 (proof of Thm 4.1) in full; rv-h-cm §7.2 (NoCM), rv-up §3 (BG record).
- Design decisions (recorded for the note):
  1. Route K for modularity: replace C2-C10 (Pan, Scholze/Faltings-Tsuji, Berger, Fontaine,
     HT of eigenforms, Deligne-Serre, Kronecker-Weber, Li/Shimura/Eichler-Shimura, C10) by
     Khare-Wintenberger+Ribet (GL2-type AV over Q are modular) and Carayol for A_f, with two
     new glue lemmas: GL2 (the r_l-isotypic Q-simple factor B of Res_{L'/Q} A is GL2-type:
     Frobenius reciprocity + Faltings + freeness of V_l(B) over F⊗Q_l) and Cond (Glazer's break
     bound applied to V_l(Res_{L'/Q} A) = Ind V_l(A): f_p(B) <= 2 dim B (1+U0)). Removes all
     p-adic Hodge theory definitions. Pan route kept as alternative.
  2. Good reduction defined Galois-theoretically (I_v trivial on T_l); Grothendieck's monodromy
     theorem + B_3 division argument gives potentially good; level 3 + 1+3M_4(Z_3) torsion-free
     gives good. Removes Neron models, SGA7 IX 3.6, Serre-Tate as separate leaves.
  3. Theta nulls replaced by Thomae point T_S = Delta(S)Delta(S^c) (cheap, roots of the sextic);
     Pazuki leaf stated in Thomae form (Pazuki 2012 Cor 1.3(2) + Thomae).
  4. F1 becomes algebra: on the QM locus [I2:I4:I6:I10] = [96(j+1):576j:4608j(5j+4):4096j^3]
     and j = 3779136 I10^2/I4^5.
- Script scratch/hdec-elementary/igusa_thomae_check.py (output saved): (2) True; (3) 30 random
  root sets: sum T_S^2 = B'/a^4, prod T_S^2 = (D'/a^10)^4: True.
- Normalization cross-check (by hand): Thomae theta^4 ∝ T_S with psi4 = Σθ^8/4, chi10 = -Πθ^2/2^14
  gives chi10^2/psi4^5 = ±2^-18 I10^2/I4^5; with chi10 = -J10/4, psi4 = I4/4 this forces
  J10 = ±I10/4096, consistent with the conversion used.

## Step 3 (Lean draft Leaves.lean)
- Import: JHeight.lean cannot be imported (HeightMin needs upstream `lean/` package, not built:
  "unknown module prefix 'ZInQ'"). File imports ZInQKernel.Hypotheses.Height only; copies
  JHeight lines 31-232 (Fh, Gh, Jmap, certificates, F4) verbatim, restates JHeightBoundAt S and
  SixContactMinAt S (= SixContactMin at S = Mult.S_mul by rfl).
- Contents: IC2/IC4/IC6/IC10 from roots (sums over S6 / 48, 72, 12; product), OnQMLocus,
  thomae (10 triple-splittings), actSextic, sextic, Igusa1960 (Prop, genuine defs), absLogHeight;
  placeholder `Objects` (AV, dim, prod, Isog, deg, hF, jac, J1) with leaves Javanpeykar,
  GaudronRemond, FaltingsHeightVariation, BostLower, PazukiThomae; ModularityOutput S;
  jHeightBoundAt_of_leaves (sorry); sixContactMinAt_of_jHeightBoundAt (proved);
  sixContactMinAt_of_leaves (from the two).
- Compile: `lake env lean scratch/hdec-elementary/Leaves.lean`: OK, one `sorry` warning (line 485,
  jHeightBoundAt_of_leaves). #print axioms: j_eq_of_onQMLocus and
  sixContactMinAt_of_jHeightBoundAt: [propext, Classical.choice, Quot.sound];
  sixContactMinAt_of_leaves: adds sorryAx.

## Step 4 (Lean refinement)
- `Objects.jac` now takes a sextic f ∈ K[X]; PazukiThomae quantifies over an extension ι : K → K₂
  where f splits (stable-height invariance folded into L12); ModularityOutput gives f over K
  ([K:Q] ≤ QM, N5's L') with roots in K₂ on the QM locus. Reason: the curve C with Jac C ≅ A is
  defined over L' (genus-2 descent, F-e) but its Weierstrass points are not; GR14 must be applied
  over L' with d' ≤ QM.
- Compile OK; same axioms output; one sorry (jHeightBoundAt_of_leaves).
- Check: |GL4(Z/4)| = 20160·2^16 = 1321205760 ≤ G0 = 116064000000 (route K uses A[4] at p = 3).

## Step 5 (note written)
- docs/research/hdec-elementary.md: §1 verdict (12 research leaves L1-L12, foundations F-a..F-e,
  glue G1-G23), §2 graph (36 nodes; route K §2.2; route P §2.3), §3 leaves + faithfulness table,
  §4 glue table, §5 definitions D1-D17, §6 risks R1-R8, §7 first steps.
