# agent-W: packet R4, X6 Shimura curve (gonzalezRotgerX6Ab, gonzalezRotgerProp56X6)

Read-only triage, base 9a100aa7. No Lean was run. VERIFIED = read in code at the file:line given. SPECULATIVE = my
judgement. UNVERIFIED = literature from memory. Paths are relative to the worktree root.
scratch/triage2/Trace_out.txt is empty, so I followed the chain by grep. The earlier notes reach the same verdict
(scratch/gap-triage/agent-A.md §3, docs/research/gap-triage.md:495, docs/research/gt-grcount.md §1).

## 0. Shared consumer: NoCM on the X6 witness (VERIFIED)

Both fields have exactly one semantic consumer, `HDec.FS5NoCM.nocm_on_witness` (TailC.lean:1371-1456).
- The setting: `y` is a Q̄-point of `Y3` over `J(u)` with `u ∉ contactSet`, `x = fY(y)`, and `π6(x) = J(u)` lies in
  ℚ \ {0, -16/27} (TailC:1392-1393, `J_ne_zero hu`, `J_ne_branch u`). Elkies' identities give `ℚ(x) = ℚ(i)`, so
  `[ℚ(x):ℚ] = 2` (TailC:1396-1401). `X6KummerFibre` gives four distinct points `f j` in the fibre (TailC:1391).
- Suppose `End_O(A_x) ≅ R` for an order `R` of an imaginary quadratic `k` with conductor prime to 6 (TailC:1387-1389).
- **R5ptProps** (from X6Ab) is read once (TailC:1390): `obtain ⟨hdeg, hemb⟩ := h5 k hk2 R hR hcop (y ≫ fY) P.forget hx ⟨e⟩`.
  It is used for this one point and this one `R`.
  - Case `b = 0`: it gives `h(R) = 2`.
  - Case `b ≥ 1`: it gives `h(R) = 1` and `k ↪ ℚ(i)`, hence `b = 1` (TailC:1424-1446, `two_not_prime_of_sqrt_neg_one`).
- **R5fpCount** (from Prop56X6) is read once (TailC:1403): `hcount := hC k hk2 R hR hcop ⟨P.forget, ⟨e⟩⟩`.
  It is used only to get `#CM(R) = 2` (TailC:1417), which contradicts the injection `Fin 4 ↪ CM(R)` (TailC:1453-1456).
  The four points are twists of `x` (`R2X6Props` fibre clause, TailC:1404-1411).
- The call chain:
  `gluePieces_of_open4` (TailK.lean:283; `r.r5count` at TailK:294)
  → `fibreComTrivialFull_of_leaves''` (TailC:2288)
  → `_leaves'` (TailC:2070)
  → `fibreComTrivialFull_of` (TailC:1480)
  → `fibreComTrivialOwn_of` (TailC:1458)
  → `nocm_on_witness`.
  `fibreComTrivialFull_of_own` (TailC:1464-1475) applies it to the witness of `hL = r1r2fpFull_of r3` (TailD:535),
  so the `h5` that is read is the `R5ptProps` clause of the row `r1r2 : R1R2fpRep` (LPrefix.lean:5218-5223).
- `r5count` has no other reader: grep of `.r5count` finds only copies (TailD:95, TailE:6574, TailN:106, TailZ4:188,
  TailX:196, LPrefix:13690) and the consumer at TailK:294.

## 1. gonzalezRotgerX6Ab

1. **Statement.** `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (TailZ22.lean:64). It asserts that some witness
   `(Y, Φ, X, Ψ, fY)` satisfies `R1fpPropsAb ∧ X6Props ∧ R5ptProps X Ψ`. `R5ptProps` (HDecomp/QM/Leaves.lean:191)
   says: for every CM point `x` of X6 by an order `R` of conductor prime to 6,
   `[ℚ(x):ℚ] = (b=0 ? 1 : 2)·#Pic R`, and if `b ≠ 0` then `k ↪ ℚ(x)`. This is González–Rotger Thm 5.12 (UNVERIFIED).
2. **Consumers** (VERIFIED):
   - (a) The **model role.** TailZ27.lean:110 builds `gonzalezRotgerCountX6Ab_of_printed n.gonzalezRotgerProp56X6
     n.gonzalezRotgerX6Ab` (GRCountX6.lean:111). It only takes the witness and discards `R5ptProps` (`-` at
     GRCountX6:113). This use is syntactic: `gonzalezRotgerCountX6Ab_of_printed'` (GRCountX6.lean:117) does the same
     with `DeligneComponentsX6PrintedAb`, which is already a field.
   - (b) The **R5 role.** The chain is:
     `x6Rows_of_open14` (TailZ23.lean:711, field read at :722; TailZ22:274 is the older copy)
     → `x6Rows_of_leaves` (TailZ21.lean:1453)
     → `r1r2_of_published` (TailZ21:1429)
     → `r1r2fpRep_of_printed` (TailZ20.lean:1855-1859, `r5fp_of_point` at TailZ20:1359)
     → `r1r2fpRep_of_split` (TailZ20:1749, `residueOfX6_of_r5fp` at TailZ20:1719)
     → the `R5ptProps` clause of `R1R2fpRep` → the NoCM read at TailC:1390.
   - (c) **Syntactic carries.**
     - `r5 := r5fp_of_rep r.r1r2` (TailZ9.lean:95) is never read. `.r5` appears only in copies: TailD:94,
       TailE:6573, TailN:105, TailZ4:187, TailX:195, LPrefix:13689.
     - `x6ConicModel_of_published` (TailZ21:1437-1441) stores the same row in `X6ConicModel`. Its reader
       `kummerFibreEquiv_transport` reads only `.1`, `.2.2.1` and `.2.2.2.2.2.2.1` (X6Surj) (TailE.lean:711-717).
       So `R5ptProps` is not read there.
     - The π0 core `r1pi0Props_of_bundle` (LPrefix:9504) reads R5ptProps, but grep finds no caller outside LPrefix.
       SPECULATIVE: it is not on the live path, since `R1pi0Props` now comes from Deligne via `geomConnX6_of`
       (TailZ20:1840).
3. **Weakest form used** (SPECULATIVE sketch, VERIFIED against TailC:1390-1446). On the r1r2 witness, for the one
   CM point `x` with `ℚ(x) = ℚ(i)` and `π6(x) ∈ ℚ \ {0, -16/27}`:
   `[ℚ(x):ℚ] ≥ (b=0 ? 1 : 2)·#Pic R  ∧  (b ≠ 0 → k ↪ ℚ(x))`.
   Only this lower-bound direction is needed when the count is weakened to `#CM(R) ≤ 2^b·h(R)`.
   The containment is essential: it rules out `b = 2` (k = ℚ(√-19): h = 1, 4 points; LPrefix:5122 and the R5fp
   docstring at Leaves.lean:556-560).
4. **Provable or bypass?** No.
   - It is not implied by Prop56X6, which is about counts only (GRCountX6:72).
   - It does not follow from `babaGranathRationalAb` (fibres and the 3 CM values), `deligneComponentsX6PrintedAb` (π0)
     or `elkiesX6StarPrinted` (charts).
   - `shimuraMainThmIDeligneY3AbU` (Shimura reciprocity at CM points on Y3) could in principle give `ℚ(x)·k = H_R`
     and the `b`-dependent descent. That amounts to reproving GR Thm 5.12 on X6 (SPECULATIVE).
   - `hCM` (T5Glue.ShimuraMainCM) is about elliptic curves and does not apply.
   - Without residue-field information the count alone gives `2^b h ≥ 4`, which is no contradiction.
5. **Tier T4.** Only weakening is possible: restrict `R5ptProps` in the leaf to the one-direction form. That is a
   consumer-restricted specialization, and it does not remove the field. The model role (a) can already be moved to
   Deligne, but that moves nothing out of the open list.

## 2. gonzalezRotgerProp56X6

1. **Statement.** `GRCountX6.GonzalezRotgerProp56X6` (Contrib/OneProof/GRCountX6.lean:72). For every witness and
   every order `R` that occurs (conductor prime to 6), `#{x ∈ X(Q̄) : End_O(A_x) ≅ R} = 2^{inertCount6 k}·#Pic R`.
   This is González–Rotger Prop. 5.6 at (6,1). It is equivalent to `R5fpCount` given a witness
   (`prop56X6_of_r5fpCount` :97, `r5fpCount_of_prop56X6` :103).
2. **Consumers** (VERIFIED): the chain is
   TailZ27:110 → `gonzalezRotgerCountX6Ab`
   → TailZ23:804-806 (`gonzalezRotgerCountX6_iff_ab`, TailZ17:93)
   → TailZ9:96 `r5count := r5fpCount_of_points` (TailZ8:57)
   → TailK:294 → `nocm_on_witness` TailC:1403.
   It is used for one `R`: the CM order of the point over `J(u)`, which after R5pt satisfies `2^b·h(R) = 2`.
   Only `#CM(R) ≤ 3` plus finiteness is needed (TailC:1450-1456).
3. **Weakest form used:** for orders with `(b = 0 ∧ h(R) = 2) ∨ (k ≅ ℚ(i) ∧ h(R) = 1)` (conductor prime to 6,
   occurring): no injection `Fin 4 ↪ CM(R)`.
   Mathematically these `R` are exactly ℤ[i] and ℤ[√-6] (SPECULATIVE, classical):
   - `b = 1`, `h = 1` in ℚ(i) with `f` prime to 6 forces `f = 1`.
   - `b = 0` forces 2 and 3 to ramify, because they cannot split in `k` (optimal embedding into the division algebra
     ramified at 2 and 3). Genus theory then forces `d = -6`, and `h = 2` forces `f = 1`.
4. **Bypass, removing the count entirely** (SPECULATIVE, elementary).
   - Once `R ∈ {ℤ[i], ℤ[√-6]}` is known, NoCM needs no count and no four points:
     - `e⁻¹(i)` gives `HasCM4`, and `e⁻¹(√-6)` gives `HasCM24` (defs at HDecomp/QM/Pairs.lean:86, :90).
     - The R2X6Props clause `h2` (destructured at TailC:1386) then gives `π6(x) = 0` or `-16/27`. This contradicts
       `J(u) ∉ {0, -16/27}` (TailC:1393).
   - The missing lemmas are pure arithmetic of imaginary quadratic orders:
     - (L1) `k ≅ ℚ(i)`, `R` with conductor `f > 1` prime to 6 ⇒ `CommRing.Pic R` is nontrivial. Use the
       contraction of `α𝒪_k` with `N(α) = p ≡ 1 (4)`, `p ∤ f`, `p < f²`. It is non-principal because
       `a² + f²b² = p` has no solution.
     - (L2) 2 and 3 do not split in `k` when `R = O.comap φ` for `φ : k →ₐ B` (from `CMOptimalEmbedding`,
       TailC:2270, already given at TailK:292). This is a local descent on `2b² - 3c² + 6e² = d`, in the style of
       `aniso_int`/`aniso_rat` (HDecomp/Descent/B1Quat.lean:77, :106).
     - (L3) 2 and 3 ramified and `#Pic R = 2` ⇒ `d = -6` and `f = 1`. Genus classes: the contractions of
       𝔭2, 𝔭3, 𝔭2𝔭3 have norms 2, 3, 6 < |d|·f², so `#Pic ≥ 4` unless `d = -6`. For `d = -6`, `f > 1`, use 𝔭2
       and a split 𝔭p, p ∤ f.
     - Tau Ceti has `Pic O = ClassGroup` for `NumberFieldOrder` (Contrib/TauCeti/.../Orders/Picard.lean:35). It has
       no class-number formula, and grep finds no bridge to Mathlib's `CommRing.Pic`, which R5ptProps uses.
       TYZGenus has genus fields only for `O4 d` (Contrib/TYZGenus/RingClass.lean:296).
   - The fold is a bypass/semantic prune, not a proof of the field: the field's type (counts for all `R`) stays
     unproved. Steps:
     - write `nocm_on_witness'` without `hC`, taking `CMOptimalEmbedding`;
     - write `fibreComTrivialFull_of_leaves'''` and `gluePieces_of_open4'` (TailK:283) without `r.r5count`;
     - thread the change up the generations to `sixContactMin_of_open28` (TailZ34:171), following the
       sem-prune/bypass recipe.
   - The alternative route already split in gt-grcount §3 is `EichlerOptEmbCount6` + `CMPointsOptEmb6`
     (`r5fpCount_of_eichler`, GRCountX6:~230). Both parts are leaves, so that route is T4.
5. **Tier T3** for the bypass (several days: L1-L3 with the CommRing.Pic API, plus threading). T4 for proving the
   printed count. Neither field implies the other at the use.

## 3. Answers to the specific questions
- Discriminants used: one unknown CM order at a non-elliptic rational fibre with residue field ℚ(i). The count is
  needed only because the tree does not identify `R` with ℤ[i] or ℤ[√-6] (discriminants -4, -24). Disc -3 never
  occurs here. "Residue field = ℚ" is not used.
- Direction: R5pt needs only `[ℚ(x):ℚ] ≥ c(b)h(R)` plus the containment. The count needs only `#CM(R) ≤ 2^b h(R)`
  for `2^b h = 2`.
- Syntactic uses:
  - the X6Ab model role at TailZ27:110 (replaceable by Deligne, GRCountX6:117);
  - `r5` (TailZ9:95, never read);
  - the R5pt clause carried inside `X6ConicModel`.
- Implication between the two fields: none (different contents). They act jointly at one place, TailC:1390-1456.
