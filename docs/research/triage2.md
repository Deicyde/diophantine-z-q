# triage2: re-triage of the unheld open statements (base 9a100aa7, leaf-fold22b)

Task triage2, read-only. Base: fork main 9a100aa7. All file:line references are at this base. Paths are relative to
`ZInQKernel/` unless they start with `docs/` or `scratch/`.

Marks:
- **VERIFIED**: read in the code at the cited line, or compiled.
- **STANDARD**: published, with an exact reference.
- **SPECULATIVE**: my or an agent's judgement.
- **UNVERIFIED**: a theorem number given from memory (there is no network here).

Working files are in `scratch/triage2/`:
- `log.md`: the results log.
- `agent-{R,H,G,X,W,T,Y}.md`: per-packet reading notes, with file:line for each claim.
- `Pi0Use.lean` and `Pi0Use_out3.txt`: the compiled probe behind task 1.
- `ProbeA.lean`: the probe for task 2.

## 1. First pass (11-15, 06:00 PST): ranked one-agent tasks

Four tasks remove a field outright. A fifth removes a field by a narrow route through an open GLUE field. The sixth
is a narrowing that removes no field.

### Task 1 (−2 fields, T2). Semantic prune: `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure`

**Finding (VERIFIED, compiled).** The single proof uses these two fields only to produce the clause
`HDec.LeafAdopt.R1pi0Props X` (X₆ is geometrically connected), and nothing reads that clause.
- The chain: `deligneComponentsX6_of_printed` (TailZ12:1372) gives the π₀ bijection. Together with the proved
  `pi0_Kfull_eq_one` (TailZ12:984) it gives X₆/ℚ̄ connected. `geomConnX6_of hD hE` (TailZ20:1847) then applies
  `GeomConnOfAlgClosure`, which yields `GeomConnX6` (TailZ20:1770).
- From there the clause passes through `canonicalCoarseX6_of` and `coarseX6OfFine_of` to the last conjunct of
  `R1R2fpRep` (LPrefix:5223).
- The probe `scratch/triage2/Pi0Use.lean` (compiled, 80 s) walks every constant in the closure of
  `ZInQ.OneProof.frozenTarget` (244,035 constants). Only three constants use a binder of type exactly
  `R1pi0Props`: `r1r2fpRep_of`, `canonicalCoarseX6_of` and `coarseX6OfFine_of`, and all three are producers.
- Every destructurer drops the clause: `R1R2fp_of_rep` (LPrefix:5229), `r5fp_of_rep`, `r1rec_of_rep`,
  `pairsLift_of_rep` and `pairsLift_of_canonical`.
- The other two constants that mention it, `descend_main` (TailO:1245) and `canonicalModelY3_of_coarse`
  (TailZ20:1724), also drop it by pattern (read).
- A consumer that reached the clause by projection would pass `R1pi0Props` as an explicit argument of `And.right`, so
  it would mention the constant and appear in the probe's list. No such consumer exists.

**What remains used.** `GeomConnX6` also supplies the base witness `(Y, Φ, X, Ψ, fY)` with `R1fpProps ∧ X6Props`
(TailZ20:1855-1857). Other leaves supply such a witness too: `gonzalezRotgerX6Ab` (TailZ22:64: `R1fpPropsAb ∧ X6Props
∧ R5ptProps`), `elkiesEquationsX6Ab` and `babaGranathRationalAb`. The witnesses are compared by the existing canonical
glue (`compare_iso`, as in `conicOfWitness_of_elkies`, TailZ20:1891).

**Statement to prove.**
- Define `R1R2fpRepW`, which is `LeafAdopt.R1R2fpRep` (LPrefix:5218) without its last conjunct `R1pi0Props X`.
- Prove `r1r2_of_publishedW : TorsionStructure → BabaGranathRational → RayClassCM → GonzalezRotgerX6 → R1R2fpRepW`,
  which is `r1r2_of_published` (TailZ21:1429) without `hD` and `hE`.
- Rethread `R1R2fpRepW` through the consumers, which never read the dropped conjunct.

**Plan (sem-prune recipe; memory note "semantic prune recipe").**
1. Copy `r1r2fpRep_of_split6/5` and `r1r2fpRep_of` (TailU:1922) with `GeomConnX6W := ∃ Y Φ X Ψ fY, R1fpProps ∧
   X6Props`, taking the witness from `hG`.
2. Prove `R1R2fp_of_repW` with the same proof as `R1R2fp_of_rep`.
3. Rethread the bundle field `r1r2`: TailD:42, TailE:6460, TailN:67, TailX:72, TailZ4:67, TailZ9:26, TailZ15:26,
   LPrefix:11590 and LPrefix:13624, together with the `∀ h : R1R2fpRep` consumers. Agent-X counted about 80
   occurrences.
4. Alternative P1′: drop the conjunct from the def `R1R2fpRep` itself. That edits a chain definition, so ask the lead
   whether the hash guard allows it. If it does, the change is one producer plus four or five patterns.

**Risks.**
- Plumbing volume, mostly in LPrefix.
- **Coordination:** `geomConnOfAlgClosure` is **held** (claims.tsv line 23, cloud batch 2, claimed 02:14Z). If this
  prune lands, that work is unnecessary for the single proof. The lead should decide before both run.

### Task 2 (−1 field, T2, risk T3). `semistablePersistsSHcp` from the second assertion of SGA 7 IX 3.3

**Finding (VERIFIED, read).** `r.semistablePersistsSHcp` has one reader, `ss1_ss3_of14` (TailZ23:767). Through
`ss1_ss3_of_cp` it feeds:
- SS1, `semistableReductionThm_of_leaves_nf` (TailZ23:509), applied at TailZ23:555 and :562;
- SS3, `semistablePersists_final_nf`.

Both need only `ReductB.SemistablePersistsDVRnf` (TailZ23:425), and `persistsNF_of_general` (TailZ23:436) gives that
from `ReductSplit.SemistablePersistsDVR` (TailZ7:711, any field K). The chain already proves
`CToPrinted.identityComponentBaseChangeDVRRange_of` (TailZ19:1595) from three things already on the chain:
`SGA3_VIB_3_10`, `SGA7_IX_3_3` (= `sga7_IX_3_3_of_SH r.sga7_IX_3_3_SH r.neronBaseChangeStrictHenselization …`,
SGA7PersistsNF:379) and `GeomConnOfRationalPoint`. For the identity component U of a Néron model 𝒩 at O, it gives an
open-immersion homomorphism `j : U ×_O O' → 𝒩'`. gt-sga7 §1 notes that the first assertion does not imply the
second. The converse is what is used here: the second implies the first (SPECULATIVE argument, VERIFIED ingredients).

**Statement to prove (exact).**
```lean
theorem semistablePersistsDVR_of_printed (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : CToPrinted.SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) : ReductSplit.SemistablePersistsDVR
```
The fold then uses `persistsNF_of_general (semistablePersistsDVR_of_printed …)` in `semistableReductionThm_of_leaves_nf`
and `semistablePersists_final_nf`, in place of `ss1_ss3_of_cp r.semistablePersistsSHcp r.strictHenselizationPair …`.
That is a field replacement, with no bypass.

**Plan.** Semistability is `HasSemiAbelianIdentityComponent` of the geometric special fibre (TailZ7:197; def
TailY:79): an open connected subgroup U_s with a flat surjective homomorphism onto an abelian variety B, whose kernel
is a split torus in the functor of points.
1. Take a semistable Néron model 𝒩 from the hypothesis, its open identity component W (`OpenSub` construction,
   TailZ19:852-974), and `j : W ×_O O' → 𝒩'` from `identityComponentBaseChangeDVRRange_of`.
2. U_s is connected, contains e and lies in the closed fibre. Hence it lies in `idCompSet 𝒩` (TailZ19:191), and so
   it factors through W_{κ̄} (`IsOpenImmersion.lift`).
3. Fix κ̄(O) → κ̄(O') over the residue map (`IsAlgClosed.lift`). Then
   (U_s)_{κ̄'} → (W_{κ̄})_{κ̄'} ≅ (W ×_O O')_{κ̄'} → 𝒩'_{κ̄'} is an open-immersion homomorphism.
4. Connectedness of (U_s)_{κ̄'} comes from `GeomConnOfRationalPoint` (TailP:910; U_s has the point e, and is
   quasi-compact and locally of finite type).
5. The rest is base change: B_{κ̄'}, flatness and surjectivity (stable under base change), and the torus map e(R)
   restricted along κ̄ → κ̄'.

**Risks.**
- Pullback-pasting identifications of geometric fibres. The memory notes warn of defeq-object rewrite failures
  ("Over.pullback points / germ calculus pitfalls").
- The torus clause has to be transported in the functor of points.
- No new field is needed.

### Task 3 (−1 field, T2–T3). `babaGranathRationalAb` from Elkies plus the existence of the three CM pairs

**Finding (VERIFIED, read).** The only live reader is `babaGranathX6'_of_rational'` (TailZ21:760), which builds
`R2X6PropsIff`. `R1R2fp_of_rep` (LPrefix:5230) splits it into the forward clauses and `CMExists` (HDecomp/QM/Leaves:141).
So the reverse ("↔") direction is used only to get `CMExists`: points with HasCM4, HasCM3 and HasCM24 exist.

The derived `ElkiesEquationsX6Ab` (TailZ22:72, from the open field `elkiesX6StarPrinted`) already gives:
- the same fibre clause (the fibres of t are the Aut(𝒪)-twist classes);
- the forward CM clauses, at the three distinct values t = 0, 1, ∞.

`BabaGranathRationalAb` follows from these and `CMPairsExist` (SPECULATIVE glue, T1). Take t₄ = 1, t₃ = ∞, t₂₄ = 0.
The reverse direction is the argument of `cm_of_val` (Leaves.lean:205): equal t-values give twist-isomorphic pairs,
and HasCM is twist- and iso-invariant (Pairs.lean:148-183).

**Statement to prove.**
- `CMPairsExist : (∃ P : QMPair Qbar, HasCM4 P.q) ∧ (∃ P, HasCM3 P.q) ∧ (∃ P, HasCM24 P.q)`.
- Then `babaGranathRationalAb_of_elkies : ElkiesEquationsX6Ab → CMPairsExist → BabaGranathRationalAb`.

**Plan** for `CMPairsExist` (agent-X; SPECULATIVE, ingredients VERIFIED):
1. Over ℂ, take the uniformized QM surfaces of `ModuliAtUnits` (RayClassShimura:1135) of `shimuraMainThmIDeligneY3AbU`
   at u = 1 (`OhatQ_one`, :1235), at τ = √2+i, i√3 (`z3`, :795) and i(√3+√6).
2. Lift multiplication by the CM eigenvalue to an endomorphism. This uses the second clause of `HomLatticeCorr`
   (HomUnify/Corr:84), available through `h69` (TailQ:2380) from `uniformizationLeafAll` and `gagaMorphism`, which are
   already used.
3. Descend to ℚ̄ with a copy of `descend_main` (TailO:1176) on a bare `R1fpProps` witness.

**Risks.**
- The route uses the composite GLUE field `shimuraMainThmIDeligneY3AbU`, which another host is working on. If that
  field is split, use whichever clause replaces `ModuliAtUnits`.
- **Fallback (T1):** replace the field by the much weaker leaf `CMPairsExist` (existence of CM points on X₆; Shimura,
  UNVERIFIED locator). This does not lower the count, but it removes BG's §3.1 table-reading risk.

### Task 4 (−1 field, T3). `gonzalezRotgerProp56X6` by a bypass: identify the CM order instead of counting

**Finding (VERIFIED, read).** The count `R5fpCount` has one reader, `nocm_on_witness` (TailC:1371-1456, hC at :1403).
It is applied to a single order R of conductor prime to 6, with 2^b·#Pic R = 2, at a point with residue field ℚ(i)
(TailC:1390-1400). Chain: TailZ27:110 → TailZ9:96 `r5count` → TailK:294.

**Statement to prove.** The order R is ℤ[i] or ℤ[√−6]. Then HasCM4 or HasCM24, together with the `R2X6Props` clause
(TailC:1386), gives π₆(x) ∈ {0, −16/27}, which contradicts J(u) ∉ {0, −16/27} (TailC:1393). This yields
`nocm_on_witness'` without `hC`.

**Plan.** Three elementary lemmas on norm forms (SPECULATIVE):
- **L1:** an order of conductor f > 1, prime to 6, in ℚ(i) has nontrivial `CommRing.Pic`. Use an ideal above 5 or
  13 that is not principal.
- **L2:** 2 and 3 do not split in k, from `CMOptimalEmbedding` (TailC:2270) and local anisotropy
  (`aniso_int`/`aniso_rat`, HDecomp/Descent/B1Quat:77,106).
- **L3:** if 2 and 3 ramify and #Pic R = 2, then R = ℤ[√−6]. Some ideal of norm 2, 3 or 6 is principal, so x² + dy²
  ∈ {2, 3, 6}.

Then `fibreComTrivialFull_of_leaves'''` and `gluePieces_of_open4'` without `r.r5count`, threaded up to
`sixContactMin_of_open28` (TailZ34:171) as a bypass fold.

**Risks.**
- Tau Ceti's Picard group of orders (Orders/Picard.lean:35) is not bridged to Mathlib's `CommRing.Pic`.
- The plumbing runs over several generations.

### Task 5 (−1 field, T3; depends on a GLUE field). `deligneComponentsY3PrintedAb` narrowed to `Y3Connected`

**Finding (VERIFIED by agent-Y, spot-checked).** The field reaches the proof only as
`TSHecke.Y3Connected := ∃ Y Φ, R1fpProps Y Φ ∧ ConnectedSpace Y.left` (TailG:8352), via `y3Connected_of_deligne`
(TailZ12:1207, 1346). Its single real use is `propTSAll_of_pieces3` at TailK:317. The π₀ count, the Galois action
and ℚ(ζ₃) are never used.

**Plan** (SPECULATIVE): Y₃ is connected over ℚ by the following argument from `shimuraMainThmIDeligneY3AbU`.
1. Take a clopen U of Y₃. Its indicator is constant in τ: preimages are open (`IsHolFamily`) and ℍ is connected.
2. The indicator is invariant under the double coset relation and under the reciprocity clause.
3. The proved `classNumberOneB_proof` (RayClassShimura:2851) reduces it to a function on (𝒪/3)^×.
4. A `decide` shows that (𝒪/3)^× is generated by the image of 𝒪¹ and q(s₃) at K = ℚ(i).

The fold is a bypass to the `OpenAddedLeaves8.y3Connected` generation (TailZ4:128).

**Risks.**
- The converse Artin step.
- q̂ of an idele supported at one place.
- Like task 3, the route goes through a GLUE field held elsewhere.

This route avoids the Deligne 389 §5 / Milne §14 reading.

### Task 6 (0 fields, T1–T2; narrowing). `gaudronRemondThm14` to one direction

**Finding (VERIFIED, agent-H, read).** The second conjunct of R19 (the reverse isogeny) is used only for existence,
in `isogenyReverseExists_of_r19` (TailA:945). The open field `milneIsogenyQuasiInverse` (held) can supply it.

**Plan.**
1. Use `mulIsogeny_proved` (TailE:6376) and the end of `end0Division_of_homFree` (TailA:1290-1327) to show that the
   Milne g is an isogeny.
2. Then GR can be stated for one direction only.

This removes the reading risk κ(A) versus κ(B) for the reverse bound, but no field. Rank it below tasks 1–5.

### Table: one line per in-scope statement

| statement | weakest use on the live path (VERIFIED unless marked) | tier | route |
|---|---|---|---|
| r9a | V_ℓ semisimple for the fibre QM surface A/Galois K (ℓ=3,5) in C2 (C2.lean:751); also E1 and G13 at ℓ=5 | T4 | keep; E1/G13 uses can be bypassed (S), C2 cannot |
| r9b | surjective half for (A,A) at ℓ=3,5, (A,A^c) and (A,J₁(N)) at ℓ=5; injective half once (G13) | T4 | keep; optional split into surjective and injective halves (T1) |
| hodgeTateDecompAbVar | HT multiplicities {0:2, −1:2} for A' over F/ℚ₅ (TailC:14120); the ℓ=3 call is syntactic | T4 | keep; ℓ=3 plumbing narrowing (T1) |
| deRhamH1AbVarT | A'/F, F/ℚ₅ de Rham (TailC:14123 → Pan) | T4 | keep |
| dsThm965 | Deligne's ρ_g for ℓ=5 (all k≥2) and ℓ=3 (k=2); g varies with u | T4 | keep |
| bostLowerBound | h_F(Z) ≥ −2·g_Z for Z a factor of J₁(N)_L (transfer_core, LPrefix:12153) | T4 | keep |
| javanpeykarBound | h_F(J₁(N)/ℚ) ≤ C·N¹² (Genus/Bridge.lean:59); exponent tight | T4 | keep; K=ℚ narrowing |
| pazukiCor13Upper | theta height ≤ c₁·max(1,h_F) + c₂ on the fibre QM surfaces (LPrefix:12080) | T4 | keep |
| gaudronRemondThm14 | first conjunct (J→P, degree ≤ κ) at J=J₁(N)_L; second only for existence | T4 | task 6 (narrowing) |
| babaGranathRationalAb | only `CMExists` beyond Elkies' clauses | T2–T3 | **task 3** |
| gonzalezRotgerX6Ab | [ℚ(x):ℚ] ≥ c(b)·#Pic R and k ↪ ℚ(x) at one point with residue field ℚ(i) (TailC:1390) | T4 | keep |
| gonzalezRotgerProp56X6 | #CM(R) ≤ 2 for one R with 2^b·h(R)=2 (TailC:1403) | T3 | **task 4** (bypass) |
| raynaudSemistableSH | r6 at QM surfaces over number fields; K1 → SS1 for every A (incl. J₁(N)) | T4 | keep; cp narrowing = integrator work |
| semistablePersistsSHcp | SemistablePersistsDVRnf for SS1, SS3 (TailZ23:509, 425) | T2 | **task 2** |
| sga7_IX_3_3_SH | SS2 for every A in the height rows (J₁(N) excludes good-reduction shortcuts) | T4 | keep |
| sga7_IX_3_5_ForwardGeom | r6 only: unipotent inertia for QM surfaces over number fields (r8 dead, TailD:55) | T3–T4 | keep; Galois bypass (S) |
| deligneComponentsY3PrintedAb | only `Y3Connected` (TailG:8352, TailK:317) | T3 | task 5 |
| deligneComponentsX6PrintedAb | **none in substance** (R1pi0Props unread; probe) | T2 | **task 1** (prune) |
| hCM | Shimura 5.4 at N=32 Heegner lattices, u=(k+1)/32, in ℚ(√−n) for all n ≡ 5,7 (8) (RingClassLattice:1128) | T4 | keep; N=32 narrowing (T2) |
| h33 | both conjuncts, modulo torsion, over the infinite CR₃ family (TYZSplit:520-547) | T4 | keep; hygiene narrowings (T1) |

Notes on the GLUE fields (agent-Y; not proposed tasks):
- `shimuraMainThmIDeligneY3AbU` is used at TailZ34:84 (R1b family: clauses 2–3) and TailZ34:106 (RayClassCM:
  clauses 1, 4 and units). It becomes a LEAF with no new Lean if one reading confirms that a single printed theorem
  states all its clauses: Deligne, Bourbaki 389 §4, or Milne 2005 §§12–14 (UNVERIFIED). The same reading clears the
  flag on `deligneComponentsY3PrintedAb`.
- `shimuraIntegralModelRep` is used only as `VertUnramWitness E p` for p > 324 (TailG:10216 → TailK:318). It becomes
  a LEAF by a reading of Buzzard 1997 §§1–4 (full level 3 with 3 | D allowed; UNVERIFIED). An alternative is a printed
  good-reduction theorem for tame covers (Beckmann 1989; UNVERIFIED), via a bypass to `heckeVertWitness`.
