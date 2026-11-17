# homfree-noemb log

## Setup
- Merged origin/main (c1e4ed1b8, top `sixContactMin_of_open38`, TailZ45) into wip/homfree-noemb: c9ddaeda0.
- Build: reflink copy of leaf-fold33b's .lake/build and lean/.lake/build; `lake build +ZInQKernel.OneProof.Main`
  OK (14100 jobs), frozenTarget standard axioms. VERIFIED.

## Taint analysis (scratch/homfree-noemb/Taint.lean -> taint_out.txt), VERIFIED
- Closure of `ZInQ.OneProof.frozenTarget`: 268,654 constants.
- Seeds: projections `*.t6`, `*.homFreeFiniteAlgClosed`. Carriers (structures with such a field):
  TextbookLeaves, OpenTextbookLeaves2,3,4,6,7,8,9,10,11,12,13.
- Constants whose value depends transitively on a seed: 60 (lines `T`). These are: the projections; the
  conversions that copy/produce the field; the top wrappers `sixContactMin_of_open4..38`; `frozenTarget`;
  the readers `gluePieces_of_open4`, `fibreSimple_of_leaves`, `g8_g12_of_leaves3`, `afterG7_of3`;
  SGRFold.added12_of_open29 / heckeSqrtBranchAny_of_open29 and openGlue7_of_OpenGlue8 (through
  openTextbookLeaves10_of_OpenTextbookLeaves11).
- `sixContactMin_of_leavesR3` is NOT tainted (does not read t.t6), but takes a carrier.
- Untainted constants whose type mentions a carrier (lines `S`, excluding mk/projections): 29.

## Reroute (option (b)) — VERIFIED (compiled)
- Generator scratch/homfree-noemb/gen/{copylib.py,gen.py,header*.lean}: copies each declaration verbatim with its
  scope context (namespace/section/open/variable/set_option lines in force; one-line `namespace X export … end X`
  alias lines skipped, aliases persist), renames copied names `X ↦ X_hf` (structures/Props `X ↦ XHF`), replaces
  `PkgI3.HomFreeFinite` by `HomFreeC.HomFreeFiniteC`, applies per-declaration edits (σ binders / σ at ℚ̄, number
  fields, AlgebraicClosure L'), expands TailC's `local notation "Kd[" d "]"` (no notation commands in a contribution).
- Copied: 39 consumer declarations (Consumers.lean: the 35 T6-typed lemmas of homfree-proof §5.1 + fibreSimple_of_pieces,
  EndDivisionOfEnd0DivisionHF, CentralizerOfMatrixEnd0HF, QMSplitCaseRankHF) and 92 chain declarations (12 carrier
  structures, 4 TextbookLeaves dot-helpers, 76 tainted/carrier-typed functions incl. sixContactMin_of_open4..38).
- Carrier structures: t6 field (TextbookLeaves, OTL2-4) retyped to HomFreeFiniteC; homFreeFiniteAlgClosed field
  (OTL6-12) retyped to HomFreeFiniteC; OTL13HF = OTL13 without the field; the top conversion supplies
  `homFreeFiniteC uniformizationLeafAll_proof n.mumfordTorsionAlgClosed`; textbookLeaves4_of_open6_hf: t6 := t.homFreeFiniteAlgClosed.
- First compile: 6 errors (missing TextbookLeaves.{frobeniusDense,leafSqrtCrit,x1ModelExists,belyiX1} helpers); added;
  second compile clean (lake env lean, 1m37s).
- lake build +ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosedReroute: OK (13372 jobs).
- scratch/homfree-noemb/FoldCheck.lean: `ZInQ.OneProof.frozenTarget_hf` (frozenTarget's hypotheses with
  t : OpenTextbookLeaves13HF) and `sixContactMin_of_open38_hf`: axioms [propext, Classical.choice, Quot.sound].
  `openTextbookLeaves13HF_of_13` checks OTL13HF's fields are OTL13's minus the field.
- ClosureCheck.lean: closure of sixContactMin_of_open38_hf (241,494 constants) contains none of
  AVB1.HomFreeFiniteAlgClosed, PkgI3.HomFreeFinite, HomFreeFiniteAlgClosedNoEmb, sorryAx, t6_of_algClosed5;
  contains HomFreeFiniteC.
- #discharges (Discharges.lean -> discharges.txt): 45 open hypotheses, 51 discharge lines; the lines
  "DISCHARGES [OpenTextbookLeaves13.x] by OpenTextbookLeaves10HF.x / still assumes OpenTextbookLeaves10HF" are
  projections of the new bundle copies (spurious, they assume the bundle). #discharges does not express a reroute.

## Other pending readers of homFreeFiniteAlgClosed (read in branch sources)
- faltings-cm (origin/wip/faltings-cm ce696e14): faltingsTate_of_surj uses it only at a number field K ->
  can take homFreeFiniteC (σ = sigmaNF K). Compatible.
- deg-det (ecf7da39) degEqDetTate_of_degHomogPoly / charPolyIndepOfEllAlgClosed_of_degHomogPoly: uses
  `Module.Finite ℤ (End A)` at every algebraically closed k of DegEqDetTate, including char p -> cannot take the
  C form. degpoly-proof (0a9e6698) found T7 is applied in characteristic p (FrobTraceLink), so charPolyIndepOfEllAlgClosed
  stays over all alg. closed fields; deg-det's fold would need `homFreeFiniteAlgClosed_of_noEmb HL HT HR` (adds the
  leaf HomFreeFiniteAlgClosedNoEmb). degpoly-proof's recommended fold (CharPolyIndepOfEllAlgClosedNoEmb via
  CharPolyLattice) does not read homFreeFiniteAlgClosed: compatible.
