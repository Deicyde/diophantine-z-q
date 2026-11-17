# hodgetate-from-dr results log

## 2026-11-16 15:00 setup
- Merged origin/main: already up to date; origin/wip/integrate-w82 already in HEAD (5e235a40a).
- lean/.lake/build was missing (unknown module prefix 'ZInQ'); copied from ~/dzq/lean/.lake/build (lean/ZInQ identical, diff -rq empty).

## Consumers of the field (VERIFIED by grep)
- `HodgeTateDecompAbVar` (ZInQKernel/OneProof/H/TailS.lean:347) is read in exactly one place:
  TailX.lean:195, `deRhamComparisonHT_of_leavesT r.hodgeTateDecompAbVar l.tateTwistInvariants l.axSenTate r.deRhamH1AbVarT`
  (all other occurrences are bundle-to-bundle copies in TailZ*).
- `deRhamComparisonHT_of_leavesT` uses it for (i) `htMultOver w = g([w=0]+[w=-1])` (via `htMultOver_of_decomp`)
  and (ii) `FiniteDimensional ℚ_p V_p(A)` (via `finiteDimensional_of_decomp`). So the consumer needs the HT
  multiplicities and finite-dimensionality, i.e. the full numerical content; nothing smaller.

## Kernel inventory (VERIFIED by reading)
- No Hodge filtration on D_dR, no H^1_dR, no gr^i B_dR = C_p(i) in the kernel (grep "Fil", "Hodge filtration").
- KerTheta: B_dR^+ DVR with uniformizer xi, theta^+ : B_dR^+ -> C_p surjective with kernel (xi). No t = log[eps].
- `deRhamH1AbVarT` gives only dim_F D_dR(V^vee) = dim V (no filtration data).
- kinds.tsv flag of hodgeTateDecompAbVar: GLUE only because the coordinate form C(1)^g + C^g needs dim t*_{A'} = g.

## 15:45 HTPairing.lean §1-§2 (import TailS only) — COMPILES (VERIFIED, lake env lean, no errors)
- §1: TailS §6 generalized from (g,g) to (a,b): `htSpaceOver_eq_map2`, `finrank_htSpaceOver_of_decomp2`, `finrank_PSub2`.
- §2: `eq_of_pairing`: given e : C_p ⊗ V ≅ C_p^a × C_p^b (G_F-equivariant, first factor twisted by χ) and a
  nondegenerate B on V with B(ρσx, ρσy) = χ(σ) B(x,y), then a = b (from Tate's two theorems).
  Proof: Hom_{G_F}(V, C_p(1)) = Ψ_B((C_p ⊗ V)^{G_F}); count the left side via e (a·[F:Q_p]) and the right side via e (b·[F:Q_p]).
  `add_eq_finrank`: a + b = dim V.
- Importing TailX instead of TailS makes the same file time out in typeclass search (Module.Free, IsTorsionFree): keep the
  linear algebra in a module importing TailS only.

## 17:05 Core theorem COMPILES (VERIFIED: lake build ZInQKernel.Contrib.OneProof.HodgeTateDecompAbVarCore, 11800 jobs, success)
- `ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_leaves
   (hHT : HodgeTateDecompExists) (hT : TateTwistInvariants) (hA : AxSenTate)
   (h9 : HDec.WeilPairing.T09_SymmIsogenyExists) (hQ : HDec.WeilPairing.IsogenyQuasiInverse)
   (hT5 : HDec.PkgI2.TorsionStructure) : HodgeSplit.HodgeTateDecompAbVar`; axioms [propext, Classical.choice, Quot.sound].
- Modules: Contrib/OneProof/HodgeTateDecompAbVarDecomp.lean (imports TailS + AbVarBC.G9Instance: leaf, counts,
  a = b, cyclotomic naturality), HodgeTateDecompAbVarWeil.lean (imports TailK: Weil pairing over any field with l != 0),
  HodgeTateDecompAbVarCore.lean (assembly; needs maxHeartbeats 1000000 for the G9-copy/kernel-copy transport).
- New leaf: `HodgeTateDecompExists` = the field with `∃ a b` in place of the dimension g (no dims). Proved
  `hodgeTateDecompExists_of_field : HodgeTateDecompAbVar → HodgeTateDecompExists` (leaf not stronger than the field).
- `cyc_gfToGqp`: pkg-I4's χ(gfToGqp σ) = Mathlib's cyclotomicCharacter (AlgebraicClosure F) p σ (naturality, VERIFIED compiled).

## 18:10 final file, #discharges, dry-run fold (all VERIFIED)
- Files renamed to Contrib/OneProof/HodgeTatePairing{,Decomp,Weil,Core}.lean (dict-galois, origin/wip/dict-galois,
  already uses HodgeTateDecompAbVar.lean for its own leaf C_p(1)^g + C_p^b, which still needs dim t_A = g).
- `hodgeTateDecompAbVar_of_printed` (leaf + mumfordTorsionAlgClosed + 5 added Pic/Weil fields) compiles, standard axioms.
- lake build HodgeTatePairing +Main +Discharges: 14105 jobs, success.
- #discharges: both theorems discharge OpenResearchLeaves28.hodgeTateDecompAbVar; standard axioms; 45 open, 6739 checked, 15 discharge one.
- autofold --dry-run: strict 16/21 -> 17/20, strictest 16/21 -> 17/20 (GLUE -1). Dry-run module compiles; sixContactMin_of_open39 standard axioms.
- Statement.lean (verbatim copy of the field, Iff.rfl against TailS) compiles (VERIFIED).
