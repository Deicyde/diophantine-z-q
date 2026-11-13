# curve-glue results log

## 1. CM points for MobiusGlue (`CMPoints.lean`)
- Compiled 06:3x, 0 errors 0 warnings; axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
- `cm_points_of_objects : R2fpProps Y Φ π → CMObjects → CMPoints Y Φ π` (Φ onto; one-way clauses suffice).
- `cm_points_of_R1R2fp`, `cm_points_of_R1R2fpRep` (CMExists from R2X6PropsIff + X6Surj.1; level-3 from X6Surj.2).
- `mobiusGlue_noCM_of(_rep) : MobiusGlue → bundle → MobiusGlueNoCM`.
- Finding: kernel `MobiusGlue` already has the CM objects as a premise; consumers already supply them
  (`cm_objects_of_R1R2fp`, pin-apply `sameTripleMor_of_leaves`). Gap is closed; no statement changes.

## 2. C2K from the leaf (L) GlobalFunctionsConst (`C2K.lean`)
- `theorem constOrOntoAlgClosed_of (hL : GlobalFunctionsConst) : ConstOrOntoAlgClosed` — compiled,
  0 errors 0 warnings, axioms [propext, Classical.choice, Quot.sound] (VERIFIED, `run_c2k.txt`).
- (L) `GlobalFunctionsConst`: K alg. closed, X → Spec K proper + smooth rel. dim 1, W clopen preconnected open,
  s ∈ Γ(X,W) ⇒ ∃ c : K, IsNilpotent (s − cst f W c). Textbook leaf (consequence of finiteness of Γ for
  proper schemes / Γ = K for proper connected reduced; numbering UNVERIFIED).
- Lean proof: values `ev p` of sections at K-points (ring hom; `ev_cst`: constants evaluate to themselves,
  via Mathlib `germ_stalkClosedPointTo`); units detected by values at K-points (Jacobson + `pointOfClosedPoint`);
  missed value ∞: W ⊆ U, f|_W constant; missed value a: glue 1/(f−a) and g/(1−ag) with
  `objSupIsoProdEqLocus`, apply (L), case analysis on c.
