# triage2 agent G — packet R7: r9a, r9b, hodgeTateDecompAbVar, deRhamH1AbVarT, dsThm965

Read-only, worktree wip/triage2 (HEAD 9a100aa7). No Lean run. V = VERIFIED (read, file:line); S = SPECULATIVE.

## Chain (common to all five) — V
`OpenResearchLeaves21` (TailZ34.lean:17-23) passes all five unchanged (TailZ34:86-92, ... TailZ23:783-789, TailZ17,
TailZ15:103-109, TailZ9:101-107, TailZ4:192) to `researchLeaves5_of_open7` (TailX.lean:191), which builds
- `r10 := deRhamComparisonHT_of_leavesT hodgeTateDecompAbVar tateTwistInvariants axSenTate deRhamH1AbVarT` (TailX:202; def TailS.lean:2059),
- `r13 := eigenformHT_of_kato_ds eigenformHTNew newformOfEigenformG9 dsThm965 dsThm966` (TailX:205; TailT.lean:1549),
- `r14 := r14Det_of_printed dsThm965 dsThm966` (TailX:207; TailT.lean:1532);
`r9a/r9b` pass on (TailN:110 `faltingsSemisimple_ofK5` is an identity cast, TailM:473) to `researchLeaves3_of_open2`
(TailE:6569; `r10 := deRhamComparison_of_HT r.r10` :6580, `r14 := eigenformRepExists_of_r14Det` :6583) and to
`gluePieces_of_open4` (TailK:285) which also builds `g9GlueNoT23_of_deRhamComparisonHT r.r10` (TailK:332) and puts
`r.r14` (R14Det) into `GaloisPieces` (TailK:323). Live consumers: TailD.lean `g8_g12_of_leaves3` (:127),
`afterG7_of3` (:156; ℓ=3 call :172 discards G9, G10: `obtain ⟨r₃, h8₃, -, -, h11₃⟩`), `newformLeaves_of3` (:150),
`hom_of_common3` (:191). (`GaloisPieces.deRham` is built at TailK:324 but never read by TailD — S-free plumbing.)

Objects (V, TailD/TailA): `A : PkgI3.AbVar K` = model over a Galois number field of the fibre QM abelian surface at a
rational u (dim 2, rank End = 4, End division, noncommutative); one per u, infinitely many; glueOutputs always takes the
non-CM branch `Or.inl` (TailD:223). Primes ℓ ∈ {3, 5}.

---
## r9a `PkgI3.FaltingsSemisimple` (HDecomp/Objects.lean:423)
1. ∀ number field K, A : AbVar K, prime ℓ: `(A.galRep ℓ).IsSemisimpleRepresentation`.
2. Consumers (all V):
 - C2 `PkgI3.C2_absolutelyIrreducible` (HDecomp/I3Linalg/C2.lean:728, use :751) inside `g8` (TailA:2108) ← `g8_g11`
   (:2231) ← (a) `g8_g12` ℓ=5 (TailD:138) (b) `g8_g11` ℓ=3 (TailD:173; G8 output h8₃ IS used, :176). Object: the QM
   surface A over Galois K, ℓ ∈ {3,5}. Purpose: the quotient r of V⊗Q̄_ℓ ≅ r⊕r is semisimple.
 - E1 `PkgI3.E1_exists_hom_ne_zero` (C2.lean:768, use :784) ← `hom_of_common3` (TailD:196): A over L', ℓ=5 (the ℓ of
   CommonConstituent, produced at ℓ=5 by `g13` → `commonConstituent_of_attached ... 5`, TailA:3452). Used only to
   project V_ℓ(A)⊗E onto the constituent U.
 - G13 via NewformLeaves.r9a (TailA:3717 `g13`): `c9_core` (HDecomp/ModCurves/C9.lean:252, :296-298) on A_f/ℚ;
   `rhoF_subrep_of_surj` (E1Sub.lean:338, :356) on J₁(N)/ℚ; `homVK_surjective` (E1Sub.lean:121, :135) on A_f/ℚ;
   all at ℓ=5.
3. Weakest used: semisimplicity of V_ℓ for {QM surface A over a Galois number field, ℓ=3,5} ∪ {A over L', ℓ=5} ∪
   {A_f, J₁(N) over ℚ, ℓ=5}.
4. Bypasses (S): E1 instance removable by carrying a complement in `CommonConstituent` (U comes from G8's r⊕r split,
   which has one); G13 instances replaceable by Poincaré quasi-sections (T8 field `t.t8`) + the θ(K_f)-eigenspace
   decomposition + "r₅ irreducible ⇒ ρ_f irreducible". But the C2 instance (QM surface A, non-CM, all u) is the core of
   G8 and has no substitute: with only Tate (r9b), r could be a non-split extension of two characters (commutant still
   scalar). CM/abelian-image shortcut does not apply (non-CM branch, varying u). r9a does not follow from r9b.
5. Tier T4 (keep). No removal found. Narrowing to "dim 2, End rank 4, ℓ∈{3,5}" is possible but is still Satz 3.

## r9b `PkgI3.FaltingsTate` (Objects.lean:430)
1. ∀ K, A, B, ℓ: `tateHomZl ℓ A B` injective ∧ range = Galois-equivariant maps.
2. Consumers (V), and which half:
 - C2 via `finrank_equivEnd` (Objects.lean:639; .1 at :681, .2 at :683), pair (A,A), ℓ=3,5. C2 only needs
   `finrank ≤ 4` (C2.lean:744) ⇒ mathematically only the range-⊇ (surjectivity) half.
 - G10 `g10Glue_of_conjTwist` (TailB:1832) → `g10Out_of_conjTwist` (TailB:1815) → `conjTwistNontrivial_of_latticeInj`
   (TailB:2970, `faltingsV hF` :2996; `faltingsV` TailB:2020 uses only `.2`, :2057). Pair (A, A^c = conjVar A s),
   ℓ=5 live (G10Out feeds Pan in `g12`, TailA:2224); ℓ=3 output discarded.
 - E1 `exists_hom_ne_zero_of_equivariant` (Objects.lean:552, only `.2` at :610): pair (A, J₁(N)_{L'}), ℓ=5.
 - G13 `jSide` (TailA:3333) → `vSurjOfSurjective` (E1Sub.lean:216) → `homVK_surjective`: `.2` on (A_f, A_f) and
   `.1` (injectivity) on (J₁(N), A_f) over ℚ (E1Sub.lean:188-191), ℓ=5.
3. Weakest used: surjectivity half for (A,A) ℓ∈{3,5}, (A,A^c) ℓ=5, (A,J₁(N)_{L'}) ℓ=5, (A_f,A_f) ℓ=5; injectivity
   only for (J₁(N),A_f) in G13 (and in the unneeded ≥ direction of finrank_equivEnd).
4. Answer to "only injectivity?": NO — the surjectivity (Faltings) half is used in C2, G10, E1. Injectivity is used
   once (vSurj), and that whole vSurj use is replaceable by Poincaré (T8: quasi-section s with π∘s an isogeny) (S).
   No narrowing removes Faltings.
5. Tier T4 (keep). Optional T1-T2 cleanups: `finrank_equivEnd_le` from `.2` only; split the leaf into
   `FaltingsTateSurj` so injectivity becomes a separate (classical, Mumford §19 Thm 3, UNVERIFIED) leaf.

## hodgeTateDecompAbVar `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (OneProof/H/TailS.lean:347)
1. ∀ p, F/ℚ_p finite, A : PkgI4.I3.AbVar F, dim g: G_F-equivariant ℂ_p⊗V_p(A) ≅ ℂ_p(1)^g × ℂ_p^g.
2. Consumers (V): only `deRhamComparisonHT_of_leavesT` (TailS:2059) → `deRhamComparisonHT_of_leaves` (TailS:730):
   (i) HT multiplicities via `htMultOver_of_decomp ... hT hA` (:736-737, with tateTwistInvariants, axSenTate);
   (ii) finite-dimensionality of V_p(A) for the dual de Rham transfer (:2063-2064). Resulting r10 is used in
   `g9GlueNoT23_of_fieldEmb` (TailC:14120: `hR10 ℓ F A' 2` gives htMult 0 = 2, htMult (−1) = 2; `hW` = R10Weights,
   other weights 0) → G9Out = de Rham ∧ HT weights {0,−1} → `g12` (TailA:2220: Pan's distinct weights) and
   `G12Weight` (`hw`). A' = base change of the QM surface A to a finite Galois F/ℚ_ℓ from `LocalModel`
   (Contrib/G9/Reduction.lean:50, proved `g9AbVarBaseChange_proved`). Live only at ℓ=5; ℓ=3 call is syntactic
   (TailD:172-175 discards G9).
3. Weakest: ∀ F/ℚ_5 finite Galois, A' : PkgI4.I3.AbVar F, dim A' = 2 → htMult 0 = 2 ∧ htMult (−1) = 2 ∧ others 0
   (+ V_5(A') finite-dim, available from `dim_finite_I4`/T26).
4. Bypass? NO. tateTwistInvariants/axSenTate are complements (they compute ℂ_p(j)^G), not substitutes.
   eigenformHTNew gives HT of eigenform reps, but G9 is an input to Pan (G12) which produces the eigenform — circular.
   det r (T9) only gives a+b = −1, which yields "distinct" but not the {0,−1} G12Weight needs (S).
5. T4 (Tate 1967 for good reduction + potential good reduction of QM surfaces would be T3-T4; no p-divisible groups
   in tree). T1 narrowing: copy `g8_g11` at ℓ=3 as g8+g11 only (drop G9/G10 there) and restrict G9GlueNoT23/R10 to
   p=5; does not remove the field.

## deRhamH1AbVarT `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (TailS.lean:1992)
1. ∀ p, F/ℚ_p finite, A : PkgI4.I3.AbVar F: `IsDeRhamTensorOver p (A.galRep p).dual`.
2. Consumer (V): only TailS:2065 (`isDeRhamOver_iff_tensor_dual`, TailS:2023) → `IsDeRhamOver` clause of R10 →
   `hdR` in `g9GlueNoT23_of_fieldEmb` (TailC:14123, `core_dR_F` :14156) → G9Out.1 = `LocalIsDeRham 5 2 r` → Pan
   (`hPB 5 ... h9.1`, TailA:2220). Same A', p=5 live.
3. Weakest: ∀ F/ℚ_5 finite Galois, A' of dim 2: IsDeRhamTensorOver 5 (A'.galRep 5).dual.
4. No field supplies de Rham for abelian varieties; HT (from the previous field) does not imply de Rham. Disappears
   only if Pan∘Berger (r11r12) were replaced by a modularity input with geometric hypotheses (S, research).
5. T4. Same ℓ=3 narrowing as above.

## dsThm965 `ZInQ.Contrib.HodgeSplit.DSThm965` (TailS.lean:1110)
1. Deligne (DS 9.6.5): for a normalized eigenform g ∈ S_k(N,χ), k ≥ 2, some ρ : G_ℚ → GL₂(Q̄_ℓ) unramified at p∤Nℓ
   with arithmetic-Frobenius charpoly X² − a_p X + χ(p)p^{k−1}.
2. Consumers (V), via R14Det (TailT:1532) / EigenformRepExists / EigenformHT:
 - `G12Weight` (`g12Weight_of`, TailB:4998, `hR 5 ...` :5001): ℓ=5, g = Pan's eigenform, ANY level N and weight k
   (k ≥ 2 here; k=1 is DS966's).
 - `eigenformHT_of_new` (TailS:1282, `hR`) inside r13 → `hHT 5 ...` (TailB:5023): ℓ=5, any N, k ≥ 2.
 - `g12Det_of` (TailA:2447, `hR 5 ... N 2`): ℓ=5, k=2, eigenform of arbitrary level.
 - `iso_R14` (TailA:3460) via `g14`: ℓ=5 and ℓ=3, k=2, newform f of level N (≤ Q_D·M_S(u)², unbounded in u).
3. Weakest: DSThm965 for ℓ=5 (all k ≥ 2) and ℓ=3 (k=2 only). Not one specific form: eigenforms vary with u.
4. Bypass via r16 (`R16_EichlerShimuraJ1'`, HDecomp/ModCurves/Leaves.lean:179: A_f, eigenFun dim 2, Frobenius trace
   a_p and det χ(p)p at p∤Nℓ): could give the k=2 newform instances, but (i) it lacks unramifiedness at p∤Nℓ (needs
   good reduction of J₁(N) outside N + NOS), (ii) G12Det is for eigenforms (needs t25), (iii) the k ≥ 3 instances in
   G12Weight/r13 remain. Possible restructure (S): restate eigenformHTNew with hypothesis "traces a_p outside a finite
   S" (Kato + Chebotarev + BN) and feed it ρ' = r⊗ψ⁻¹ (irreducible ⇒ semisimple), removing the k ≥ 3 uses; then
   k=2 from r16 + an extra good-reduction leaf. That swaps one T4 leaf for a statement change plus another leaf — not
   a one-agent removal.
5. T4 (keep). No cheap removal.

## Bottom line
None of the five can be removed by a one-agent task. All are used for the varying QM surface A (and J₁(N), A_f,
A^c), never a single object. Only T1-T2 narrowings exist (ℓ=3 G9 plumbing; Faltings surjectivity half; E1/G13
semisimplicity bypasses via a complement / Poincaré), and none removes a field.
