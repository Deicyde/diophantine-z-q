# charpoly-hf results log

## Setup (2026-11-16 18:30 PST)
- Base wip/leaf-fold33b 968b59ef8; origin/main c1e4ed1b8 already an ancestor (merge: "Already up to date").
- Build: reflink copy of ~/dzq-wt/leaf-fold33b/.lake/build and lean/.lake/build (that tree is at 4da8d4f32 =
  base + hP23 fold; H chain identical).
- Copied charpoly-charp's sources (origin/wip/charpoly-charp 512080e4) into scratch/charpoly-hf/cc/ for reference.

## Reading findings (VERIFIED by reading)
- charpoly-charp's only char-p input: `exists_minpoly_endE (hH : PkgI3.HomFreeFinite) (hT : TateModuleFree) Ab α`
  (CommonTraceHomFree.lean), applied at FrobTraceLink's `Ab : AbVar k`, `CharP k p`, for ℓ = 3, 5 and
  E = PadicAlgCl ℓ. It uses `hH k Ab Ab` (End free finite + ℤ_ℓ ⊗ End ↪ End T_ℓ) and `hT` (basis of T_ℓ).
- FrobTraceLink (TailC L8674) is existential in (k, Ab, α): no property of α beyond FrobCompare at 3, 5 is available.
- Blueprint names `HDec.HSyn.OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed`
  (blueprint/roadmap/height-decomposition/abelian-varieties/characteristic-polynomial.md L6).

## Lean (VERIFIED, Lean 4.35.0 / Mathlib v4.35.0, axioms propext, Classical.choice, Quot.sound: axioms_out.txt)
- scratch/charpoly-hf/MinpolyCharP.lean (imports TailC) = ZInQKernel/Contrib/OneProof/MinpolyIndepCharP.lean:
  `CharpolyHF.MinpolyIndepOfEllCharP` (def), `minpoly_baseChange_iff`, `exists_minpoly_endE_charP`,
  `HDec.G14Trace.common_trace_of_minpolyCharP`, `g14TraceCompat_of_link_minpolyCharP`,
  `HDec.HSyn.G0AssembleMod.linkedTateData_of_local_minpolyCharP (hM) (hT : TateModuleFree) : LinkedTateLocal → LinkedTateData`.
  Pitfall: `Fintype.linearIndependent_iff.mp h` timed out (whnf) for vectors in `Module.End E (E ⊗[K] W)`;
  explicit `(R := E) (v := …)` fixed it.
- scratch/charpoly-hf/Consequence.lean = ZInQKernel/Contrib/OneProof/MinpolyIndepCharPThm3.lean:
  `HomFreeFiniteAlgClosedCharP` (Mumford §19 Thm 3 printed form, k alg. closed of char p) and
  `minpolyIndepOfEllCharP_of_homFree (hH) (hT) : MinpolyIndepOfEllCharP`.
- Copied verbatim from wip/charpoly-charp: ZInQKernel/Contrib/OneProof/CharPolyLattice.lean (degpoly-proof),
  R16PrintedC.lean (`R16Split.r16_of_printedC`, T7 only at ℚ). All four modules build (lake build, 11765 jobs).

## Taint of the T7 field on the base route (scratch/charpoly-hf/Taint.lean -> taint_out.txt), VERIFIED
- frozenTarget closure 270,833 constants; seeds `*.t7`, `*.charPolyIndepOfEllAlgClosed`; 65 tainted.
- Carriers on the route: TextbookLeavesHF? no — OTL2HF, 3HF, 4HF, 6HF–14HF (homfree reroute copies) and OTL15 (TailZ48).
- Every tainted constant is in Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean (61), TailZ48 (3), Main (frozenTarget).
  Direct readers: gluePieces_of_open4_hf (t.t7), textbookLeaves4_of_open6_hf (t7 := t7_of_algClosed5 …),
  openResearchLeaves21_of_OpenResearchLeaves22_hf (R16: r16_of_printed … t.charPolyIndepOfEllAlgClosed).
  The original OTL13 (named by the blueprint) is not on the route.
