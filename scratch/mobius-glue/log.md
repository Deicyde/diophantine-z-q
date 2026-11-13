# mobius-glue results log

Base: 2dd83306 + merge origin/wip/qm-pin. Target: `LeafQM.AV.Pin.MobiusGlue`, copied verbatim
from `scratch/qm-pin/QMPin.lean` (lines 553-567).

## Build
- `lake build ZInQKernel.HDecomp.QM.Leaves`: success, 2m18s (build0.txt). VERIFIED.

## RatInj.lean (imports Mathlib only)
- `MobiusGlueDev.natDegree_le_one_of_injective`: K algebraically closed, char 0, F G coprime,
  `t ↦ [F(t) : G(t)]` injective on K → natDegree F ≤ 1 ∧ natDegree G ≤ 1 (Wronskian argument).
  run 3: 0 errors. VERIFIED (compiled).

## MobiusGlue.lean (imports ZInQKernel.HDecomp.QM.Leaves)
- §0: QMFamily, IsFibreOf, R1famProps, R1fpPropsPin, R1univProps, R1fpPropsU, MobiusGlue copied
  from scratch/qm-pin/QMPin.lean; text of each declaration identical (python string compare). VERIFIED.
- §1 Mob.ratEval, Mob.natDegree_le_one_of_injective (from RatInj.lean), Mob.ratEval_eq_self
  (deg ≤ 1, no finite pole, fixes 0 and c ≠ 0 ⇒ identity on K). compiled.
- §2 named facts (defs): CurveRatFactor, CurveSurj, TwistClassFinite.
- §3 mobiusGlue_of_curveFacts : CurveRatFactor → CurveSurj → TwistClassFinite → MobiusGlue. compiled.
- §4 AutOInnerFinite (def); exists_liftO_congr; level3_finite (TorsionStructure → Finite (Level3 q),
  char 0, via kernel Level3.torsor); transportLevel, QML3.isoTransport, conjUnitIso;
  twistClassFinite_of : TorsionStructure → AutOInnerFinite → TwistClassFinite. compiled.
- §5 mobiusGlue_of_named : CurveRatFactor → CurveSurj → ObjBridge.TorsionStructure →
  AutOInnerFinite → MobiusGlue. compiled.
- run (04:50): 0 errors, 0 warnings; 6 `#print axioms`, all [propext, Classical.choice, Quot.sound]. VERIFIED.
- §6 phi_part, SameTripleMor, transfer_pointwise_mor, sameTripleMor_of_mobius, pointwise_of_witness_mor
  copied from QMPin.lean (identical text, python compare, VERIFIED); new sameTripleMor_of_named,
  pointwise_of_witness_named (named facts in place of MobiusGlue). run (05:10): 0 errors; 8
  `#print axioms` all [propext, Classical.choice, Quot.sound]. VERIFIED.
- Hypotheses of MobiusGlue actually used by the proof: h1' (Y' proper, smooth rel. dim 1, has a
  ℚ̄-point), h2, h2', hCM, hg, and Φ' Qbar bijective. h1 (R1fpPropsU Y Φ), R1fam/R1univ of Y' unused.

## AutO.lean (imports ZInQKernel.HDecomp.QM.Structures, ZInQKernel.HDecomp.Textbook.SkolemNoether)
- `lake build ZInQKernel.HDecomp.Textbook.SkolemNoether`: success, 51 s (build1.txt). VERIFIED.
- Extension of α : O ≃+* O to `extAlgEquiv α : B ≃ₐ[ℚ] B` (α̃ b = m⁻¹ α(m b); exists_nat_smul_mem,
  extFun_eq (independent of m), extFun_add, extFun_mul, extFun_algebraMap, extAlgHom_symm_comp).
- NormalizerFinite (def): ∃ finite T ⊆ Bˣ, every u ∈ Bˣ with u O u⁻¹ = O is q·v·t (q ∈ ℚ^×, v ∈ O^×, t ∈ T).
- conj_of_skolem (from kernel `TSkolemKW.leafSkolemNoether` + `GlueDescent.B6_inner`), conjUnit,
  key_conj, autOInnerFinite_of_normalizer : NormalizerFinite → AutOInnerFinite.
- runs: several fix iterations (whnf timeouts from Nat.cast defeq after rw, fixed with `show`);
  final run 0 errors, 1 deprecation warning; axioms of extAlgEquiv, autOInnerFinite_of_normalizer:
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- MobiusGlue.lean §7 = AutO.lean content (namespace LeafQM.AV.Pin.AutOExt, new import
  ZInQKernel.HDecomp.Textbook.SkolemNoether) + `mobiusGlue_of_normalizer : CurveRatFactor → CurveSurj →
  ObjBridge.TorsionStructure → AutOExt.NormalizerFinite → MobiusGlue`. run (04:52): 0 errors;
  10 `#print axioms` all [propext, Classical.choice, Quot.sound]. VERIFIED.

## Normalizer.lean (imports ZInQKernel.HDecomp.QM.Structures)
- py/normalizer_identity.py (~/pyenv/bin/python -I): mulCoord n m = coordinates of ofInt n * ofInt m
  (symbolic check); nrd(ofInt x) = x0²+x0x2−2x1²−2x1x3+x2²−2x3²; conj = (x0+x2, −x1, −x2, −x3);
  the 16 forms coord_l(x e_k x̄) have Smith form diag (1,1,1,1,1,6,6,6,6,6) on the 10 monomials;
  PARI matsolvemod gives integer λ with 6 x_l² = Σ λ·forms (checked symbolically, 0 residue);
  x·i ∈ 2O when 2 | nrd(x) (all 16 residues), x·j ∈ 3O when 3 | nrd(x) (all 81 residues). VERIFIED (computed).
- Lean: units ui, uj; T = {1, i, j, ij}; IsNorm (closed under *, ⁻¹, ℚ^×; i, j normalize O);
  nrdZ_ne_zero, inv_eq (u⁻¹ = nrd⁻¹ ū); nrd_dvd_coords; six_sq_identities (ring);
  dvd_of_prime_dvd_nrd (p ∤ 6); two_dvd_mulCoord_ei, three_dvd_mulCoord_ej (decide over ZMod 2, ZMod 3);
  T_mul_ui, T_mul_uj; descent (strong induction on |nrd|); normalizerFinite : NormalizerFinite.
  run (05:00): 0 errors; axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
