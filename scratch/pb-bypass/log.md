# pb-bypass results log

Base 9a100aa7 (leaf-fold22). Field: research `r11r12 : HDec.PkgI4.PanBerger` (LPrefix.lean l. 2250),
kinds.tsv: composite, GLUE.

## Step 1. Consumers (VERIFIED by grep of ZInQKernel/, 11-15)
- Every `.r11r12` occurrence in ZInQKernel/ is a bundle-to-bundle assignment `r11r12 := r.r11r12`, except one:
  `HDec.G0Galois.g8_g12_of_leaves3` (TailD.lean l. 139) passes `r.r11r12` to `g8_g12` (TailA l. 2255),
  which passes it to `g12` (TailA l. 2211).
- `g12` applies it once: `hPB 5 (le_refl 5) r hirr (finitelyRamified_of_g11 h11) h9.1 h10 ⟨0, -1, _, h9.2⟩`
  (TailA l. 2220): **only p = 5**, ρ = `r : GaloisRep 5 2`, the 2-dim constituent r₅ of the QM abelian surface A
  over the descent field L' (Galois over ℚ, `dim A = 2`, `Intertwines (tate A 5) (r|G_{L'}) e` with
  V₅(A)⊗ℚ̄₅ ≅ r ⊕ r). Hypotheses fed: irreducible (G8), finitely ramified (G11), `LocalIsDeRham` (G9),
  odd (G10), HT weights {0,−1} (G9). A is not CM (NoCM branch), so r₅ is not induced from a Hecke character.
- `g8_g12_of_leaves3` is called once, by `HSyn.G0AssembleMod.afterG7_of3` (TailD l. 171), on the route to
  `sixContactMin_of_open28` / `ZInQ.OneProof.frozenTarget`.

## Step 2. Weakest form the consumers need (VERIFIED by reading TailA l. 2211-2235)
`PanBerger` restricted to `p = 5` (`PanBerger5`, scratch only): g12 never uses another prime. Pan at `p = 5`
has no residual proviso. Further restriction to the Tate-module instance (r₅ ⊕ r₅ ≅ V₅(A)⊗ℚ̄₅ on G_{L'}) would
let pst replace de Rham via semistable reduction (SGA 7 IX) + Breuil 2000 Cor. 5.3.4, but those also need B_st.

## Step 3. Proof from other fields: not possible (STANDARD)
The other fields (R9 Faltings, R10 de Rham comparison, R7a NOS, R16 Eichler–Shimura, R6 Raynaud, CM/Tate leaves)
go from forms to representations or describe local properties; none gives modularity of a 2-dim G_ℚ-rep.
r₅ is not CM-induced (NoCM branch; End⁰(A_Q̄) = B indefinite quaternion division algebra), so Hecke's theorem
does not apply. Route K (Khare–Wintenberger + Ribet/Kisin Cor. 0.3) would replace more than this field and add
Weil-restriction glue (h-decomposition §1). So the field stays a research input; the deliverable splits it.

## Step 4. Main result: B_cris, B_st, LocalIsPst defined; PanBerger split into two printed leaves
- scratch/pb-bypass/FontainePst.lean (first version) and ZInQKernel/Contrib/OneProof/PanBerger.lean (final):
  `lake env lean ZInQKernel/Contrib/OneProof/PanBerger.lean` compiles with no error and no warning (11-15 05:48,
  1 min 46 s), axioms of `panBerger_of_printed`, `isPst_trivial`: [propext, Classical.choice, Quot.sound]
  (VERIFIED in the scratch copy by #print axioms).
- Definitions (namespace HDec.PkgI4.PanBergerSplit): Acris0 = Subring.closure (A_inf ∪ {x^n/n! : θx = 0}) in
  A_inf[1/p]; Acris = AdicCompletion (span{p}) Acris0; BcrisPlus = Acris[1/p]; logT = p-adic limit of the
  partial sums of log(1+x) (Cauchy proof: p^n ∣ (j-1)! for j-1 ≥ p^n); Bcris = localization at all log[ε],
  ε^♯ = 1, ε ≠ 1; Bst = Bcris[X]; G_{ℚ_p}-action by functoriality (locMap/adicMap/IsLocalization.map, proofs that
  A_cris^0 and the t-generators are preserved), σ(X) = X + log[σ(p♭)/p♭]; dstSpace (Hom form, as ddrSpace),
  bstInv = B_st^{G_K}, IsSemistableOver, IsPst, LocalIsPst.
- Leaves: PanPrinted := PanFor LocalIsPst; BergerPrinted := BergerDR LocalIsPst.
  `panBerger_of_printed : PanPrinted → BergerPrinted → PanBerger` (VERIFIED, compiles).
- Sanity: `isSemistableOver_trivial` (trivial 1-dim rep semistable over every K, via D_st ≅ B_st^{G_K}),
  `isPst_trivial` (VERIFIED, compiles). Not proved (as for pkg-I4's IsDeRham): B_st^{G_K} = K_0, B_cris ≠ 0,
  group-action property.

## Step 5. Checks (VERIFIED, 11-15 06:00-06:20)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PanBerger`:
  success, 12986 jobs (build copied from h33-sign by reflink, partial rebuild); frozenTarget axioms standard.
- `lake env lean scratch/pb-bypass/Discharges.lean` (scratch/pb-bypass/discharges-output.txt):
  `DISCHARGES [OpenResearchLeaves21.r11r12] by HDec.PkgI4.PanBergerSplit.panBerger_of_printed`,
  still assumes `[PanPrinted, BergerPrinted]`, axioms `[propext, Classical.choice, Quot.sound]`
  (the other five lines are contributions already in the tree).
- `autofold.py scratch/pb-bypass/autofold.json --dry-run`: "strict count: 46/10 on 56 -> 48/9 on 57; strictest
  45/11 -> 47/10"; the printed TailZ35 (scratch/pb-bypass/FoldDryRun.lean, line 1 stripped) compiles in 6 s,
  `sixContactMin_of_open29` standard axioms.
- scratch/pb-bypass/Weakest.lean: `PanBerger5`, `panBerger5_of_panBerger`, `g12_of_panBerger5` (g12 verbatim with
  hPB : PanBerger5) compile; axioms standard.
