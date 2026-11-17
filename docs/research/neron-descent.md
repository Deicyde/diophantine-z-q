# neron-descent: `neronSchemeExtensionDedekind` cannot be removed with no new leaf on this host; the missing step is a non-finite effective descent (Raynaud's quasi-projectivity)

Task neron-descent, 2026-11-17. Base: wip/leaf-fold33b d879bb73 (fork main), merged with origin/wip/dedekind-free
0718c946. Results log: `scratch/neron-descent/log.md`. Checked file: `scratch/neron-descent/NeronDescent.lean`.
This is model work with no human review.

Marks: **VERIFIED** (compiled, or read in a named file on this host), **STANDARD** (published, with a reference),
**SPECULATIVE** (a judgement not checked), **UNVERIFIED** (a theorem number recalled without a source; there is no
network here).

## 1. Verdict

**Target not reached.** The research field `neronSchemeExtensionDedekind`
(`ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind`, BLR 1.4 Thm 3 over an affine Dedekind scheme) cannot be
removed with no new leaf using what exists in Mathlib 4.35, the vendored FLT library or the tree. Neither route works:

* **Route (a), descent, fails at effectivity.** The step it needs is the effective descent of the Néron model from
  `R^h` (or `R^sh`) to a non-henselian DVR `R = (𝓞_L)_v`:
  * that map is not finite, and cannot be replaced by a finite one (§3.2, §3.4);
  * the only effective descent of objects on this host is the vendored FLT library's, along *finite étale* maps;
  * Mathlib 4.35 descends morphisms and properties of morphisms, but no objects.

  For an étale neighbourhood, effectivity comes down to one condition: every point of the special fibre must have an
  affine neighbourhood whose generic fibre is defined over `K` (§3.3). That is the content of Raynaud's
  quasi-projectivity of Néron models (BLR 6.4 Thm 1, UNVERIFIED), together with descent of quasi-projective schemes
  (BLR 6.1 Thm 7 / SGA 1 VIII 7.7, UNVERIFIED). Neither is in the tree, and formalizing them is a project of its own
  (§3.5).
* **Route (b), rerouting the consumers through the strict henselization, fails for the height rows (T41).** They need
  global Néron group models over `Spec 𝓞_L` at every number field `L`:
  * the stable height is an infimum over global models;
  * `stableFaltingsHeight_add_le` applies the Néron leaf at the field of an arbitrary model.

  A global model is glued from models over the non-henselian `(𝓞_L)_v`, which brings back route (a). Restating the
  heights locally would change the statements of the printed height leaves. r6, SS1 and SS3 also read
  `HasSemistableReduction A O`, which is defined through a Néron model over a non-henselian DVR (§4).

**What stands.** dedekind-free's count-neutral narrowing is the best fold available:
* the Dedekind field is replaced by `NeronExt.NeronDVRLocal` (BLR 1.4 Thm 3 at the DVRs `(𝓞_L)_v`, printed form);
* GIT 6.14 needs no Néron leaf (`mumfordGroupLawDVR_proof`).

It is recompiled here (§5). `NeronDVRLocal` is a genuine literature leaf, not glue in disguise: its henselian case
is proved (FLT), and what remains is a published but deep theorem, Raynaud's quasi-projectivity plus descent.

No new Prop, leaf or glue is introduced by this task. No statement was changed. The field is neither false nor
vacuous: the Néron model exists over every Dedekind scheme (BLR 1.4 Thm 3, UNVERIFIED), and the Lean form asks for
less (existence of extensions, finite type as smooth plus quasi-compact).

## 2. Who reads the field (VERIFIED: dedekind-free's closure scan `scratch/dedekind-free/readers.txt`, reread here)

| reader | needs | after dedekind-free |
| --- | --- | --- |
| GIT 6.14, `MumfordGroupLawDVR` | Néron model over an arbitrary DVR | **proved without Néron leaf** (`GroupLawDescent.mumfordGroupLawDVR_proof`) |
| T41 height rows: `t41_of_extension5` (TailM L387) → `H5Neron.NeronModelExists` (H5Neron.lean L205), read by `r18`–`r22`, `exists_semistable_neron` (TailY L199), `stableFaltingsHeight_add_le` | a `GroupModel A L` over `Spec 𝓞_L` with `IsNeronModel`, for **every** number field `L` | needs `NeronDVRLocal` (via neron-ext's gluing) |
| r6, SS1, SS3: `GapNeron.neronSchemeModelExistsNF` (NeronDVR.lean L89) | a Néron model over **every DVR** `O` of a number field; `HasSemistableReduction A O` is defined through one | needs `NeronDVRLocal` |

## 3. Route (a): descent of the Néron model to a non-henselian DVR

Notation:
* `R = (𝓞_L)_v` is a DVR with fraction field `K` and residue field `k`;
* `R^h ⊆ R^sh` are its henselization and strict henselization;
* `N^h` is the Néron model of `A` over `R^h` (FLT: `NeronFLT.exists_neron_of_henselian`, any henselian DVR, VERIFIED).

### 3.1 Descent tools on this host (VERIFIED by reading the sources; statements `#check`ed in `NeronDescent.lean`)

**Mathlib 4.35.**
* Descent of *properties* of morphisms: `Morphisms/FlatDescent.lean`, `LocalFlatDescent.lean`, `Morphisms/Descent.lean`.
  These include open immersions, smooth, étale and locally of finite type.
* Descent of *morphisms*: fpqc maps are effective epimorphisms (`Sites/Fpqc`). dedekind-free used this for GIT 6.14.
* `RingTheory/Flat/FaithfullyFlat/Descent.lean` descends only injectivity, surjectivity and bijectivity of ring maps.
* There is no effective descent of objects: not of schemes, not of algebras, not of modules.

**Vendored FLT** (`ZInQKernel/Contrib/OneProof/NeronFLT/Vendor/AnthropicFLT/Theorems/`):
* `DescentAction.effective_of_finiteEtale`: for `R → R'` finite étale and faithfully flat, a descent action on `X'` is
  effective if every finite set of points of `X'` lies in an affine open (the AF condition).
* `DescentAction.effective_of_isPullback_of_flat_surjective`: effectivity when the quotient `Y` and a flat surjective
  qc map `X' → Y` are already given.
* `exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing`: over any DVR, a smooth
  separated qc scheme has one affine open containing every fibre-generic point.
* `RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing`: AF for smooth group schemes over
  a henselian DVR.
* Quotients of affine schemes by finite locally free equivalence relations.
* The Néron existence theorem itself assumes `[HenselianLocalRing R]`. Its group construction lifts points of the
  special fibre to finite étale local extensions, which needs Hensel's lemma.

So the FLT library already covers `R^sh → R^h` (finite étale steps plus AF). Only `R^h → R` is missing.

### 3.2 The descent `R^h → R` cannot be made finite (VERIFIED reasoning)

* For `R = (𝓞_L)_v`, every finite local extension `R'` of `R` is a localization of the ring of integers of a number
  field `M` at a finite place. Such an `R'` is never henselian (VERIFIED reasoning). The henselization of `M` at a
  finite place is `M̂ ∩ M̄`, which is infinite over `M`: for `n` prime to `p` and prime, `x^n = 1 + p` has a root in
  `ℚ_p` but `x^n − (1+p)` is irreducible over `ℚ`. So no finite cover of `R` carries a Néron model from FLT. For a
  general DVR the same holds by the descent of henselianity along finite extensions whose fraction field is not
  separably closed (STANDARD; Engler–Prestel, *Valued fields*, §4.4, UNVERIFIED number); the chain needs only number
  fields.
* `R^h` is a filtered colimit of étale *neighbourhoods* `(B', q)`, essentially étale with `k(q) = k`. These are not
  finite over `R`.
* A Néron model over `R^h` is of finite presentation. By spreading out (EGA IV 8.8.2, in the tree as
  `SpreadOut.EGAIV_8_8_2_ii_proof`) it comes from a scheme `N'` over one neighbourhood `B'`. `B'` is a DVR with
  fraction field `K₁ ⊆ K^h` finite separable over `K`, `B' = C_{q₁}` for `C` the integral closure of `R` in `K₁`.

### 3.3 Descent along an étale neighbourhood is "trivial on the special fibre", and effectivity is exactly a stable-affine condition

Let `S'' = Spec(B' ⊗_R B')`.

* **Shape of `S''` (VERIFIED reasoning).** `S''` has a single point over the closed point of `Spec R`, since
  `k ⊗_k k = k`. Because `B'` is étale, the diagonal is open and closed, and `S''` is the diagonal plus a part `W`
  lying entirely over the generic point.
* **The descent datum.** The canonical datum on `N'` (from the Néron mapping property, as in dedekind-free) is the
  identity on the diagonal. On `W` it is the generic datum induced by `A`.
* **Stable opens.** An open `U ⊆ N'` is stable under the datum if and only if its generic fibre `U_η ⊆ A_{K₁}` is
  defined over `K`. In particular every open containing the whole generic fibre is stable. But no such open is
  affine when `dim A > 0`, because `A` is proper.
* **Effectivity.** Suppose descent of affine schemes along `R → B'` is available (Beauville–Laszlo-type patching
  `P₀ = P ×_{P[1/π]} Q`), and gluing of the descended pieces with the open-immersion descent of Mathlib. Then the datum
  is effective as soon as:

  **(SA)** every point of `N'_s` has an affine open neighbourhood `U ⊆ N'` with `U_η = V ⊗_K K₁` for an open
  `V ⊆ A`.

  Conversely, (SA) holds whenever the Néron model over `R` exists: take base changes of its affine opens. So (SA) is
  the exact content of the missing step.

**Natural attempts at (SA), and why they fail (SPECULATIVE beyond the cited facts):**
* *Intersections of conjugates.* `V := A ∖ f(A_{K₁} ∖ U_η)`, with `f : A_{K₁} → A`, is defined over `K`, and
  `V_{K₁} ⊆ U_η`. But `U ∖ closure(U_η ∖ V_{K₁})` need be neither affine nor a neighbourhood of `x`. Making it affine
  needs the removed set to be the support of a Cartier divisor cut out compatibly with the conjugates, and making it
  contain `x` needs control of closures of conjugate divisors at `x`. Both are ampleness statements on `N'`.
* *Translates by points.* A translate `σ·U` of a stable `U` by `σ ∈ N(R^h) = A(K^h)` is stable only if `σ^ρ − σ`
  stabilizes `U_η` for every conjugation `ρ`. For an affine `U_η` that stabilizer is finite, so in effect `σ ∈ A(K)`.
  But `A(K) → N_s(k)` is not surjective in general: `A(K)` can be trivial while `N_s(k) ≠ 0`. So "a union of
  translates of a quasi-projective open" does not give stable opens either.
* *Sections of an extended ample bundle.* `U = N'_{s̃}`, for `s̃` the extension of a section of an ample `L^m` on `A`.
  This is affine and contains `x` only if the extension of `L` is ample on `N'`. That is Raynaud's theorem
  (BLR 6.4 Thm 1, UNVERIFIED).
* *Quasi-projectivity of `N^h`, the task's route.* It is not in the tree: FLT proves AF only. Even granted, the
  descent would need an ample bundle compatible with the datum, plus descent of quasi-coherent algebras along the
  non-finite `R → R^h` (SGA 1 VIII 7.7 / BLR 6.1 Thm 7, UNVERIFIED). Neither exists on this host.

### 3.4 Passing to the finite closure does not help (VERIFIED reasoning)

`Spec B' → Spec R` factors as an open immersion `Spec B' ⊆ Spec C`, `Spec C = {q₁, …, q_r, η}` minus
`{q₂, …, q_r}`, followed by the finite flat map `Spec C → Spec R`. Descent along `Spec C → Spec R` could use FLT's
finite-flat tools (when it is étale) or quotients by finite locally free relations. But it needs the object over all of
`Spec C`:
* the descent datum forces its restriction to `C_{q_i}` to be the descent of `N' ⊗_{B'} E` along the étale
  neighbourhood `C_{q_i} → E = (C ⊗_R C)_{(q₁, q_i)}`, whose residue field is `k(q₁) ⊗_k k(q_i) = k(q_i)`;
* that is the same problem as §3.3, at `q_i`. The construction is circular.

### 3.5 What removing the field would take (SPECULATIVE estimate)

Either one of:
* Raynaud's quasi-projectivity of Néron models. Its proof needs Weil divisors being Cartier on the regular `N'`
  (regular local rings are UFDs, Auslander–Buchsbaum, not in Mathlib) and the theorem of the square on the smooth
  group `N'`. On top of that, descent of quasi-projective schemes with an ample descent datum along a faithfully flat
  map, which needs faithfully flat descent of quasi-coherent algebras (absent).
* Algebraic spaces: `N^h` descends as an algebraic space, and a smooth group algebraic space over a DVR is a scheme
  (Anantharaman; BLR 6.6, UNVERIFIED). Algebraic spaces are absent from Mathlib.

Each is weeks of formalization, not a task-sized step. A Lean proof of (SA) alone would still need the affine patching
and gluing infrastructure of §3.3, which is also absent.

## 4. Route (b): rerouting the consumers (VERIFIED by reading the Lean)

* **T41.** `H5Neron.stableFaltingsHeight_add_le` (H5Neron.lean, after L205) proves `h(A)+h(B) ≤ h(C)` by
  `rw [stableFaltingsHeight_eq_iInf_height C]`. It then takes an arbitrary field `E.L` and model `𝒢`, and applies
  `hN1 K A E.L` and `hN1 K B E.L`. `exists_semistable_neron` and `isStableFaltingsHeight_iff` (TailY L199–214) apply
  `hN1` at the field `L₀` supplied by `hSS1`. In each case the conclusion is about global `GroupModel`s over `𝓞_L`,
  and the leaves `hSS2` (SemistableNeronBaseChange) and `hMet` (NeronMetrizable) are stated for global models. No
  henselian substitute exists without restating the height and the printed height leaves (Bost, Pazuki,
  Gaudron–Rémond, Javanpeykar): that is outside the brief and would change leaf statements.
  * The lattices `ω_v` themselves would descend by easy linear algebra (a stable `R^h`-lattice in `V ⊗ K^h` is
    `M^h ∩ V`). The obstruction is the scheme-level definition of the height, not the mathematics of heights.
    SPECULATIVE.
* **r6, SS1, SS3.** These read `HasSemistableReduction A O`, which is "some Néron model over `O` is semistable"
  (NeronDVR.lean L129 per dedekind-free), at the non-henselian DVRs of number fields. Rerouting them through
  `HasSemistableReductionRes` or the strictly henselian leaves would not help: T41 keeps the field alive anyway.

## 5. What compiles (VERIFIED)

* **`scratch/neron-descent/NeronDescent.lean`** compiles with no errors (`lake env lean`; output in
  `NeronDescent.out.txt`). It contains:
  * `NeronDescent.NeronSchemeExtensionDedekind`, the target Prop copied verbatim, with
    `copy_iff : NeronDescent.NeronSchemeExtensionDedekind ↔ ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind := Iff.rfl`;
  * `NeronDescent.neronDVRLocal_of_dedekind`: dedekind-free's proof, with the argument `¬ IsField Rv` supplied;
  * `neronSchemeExtensionExists_of_dvrLocal`;
  * the readers `H5Neron.NeronModelExists` (T41) and `GapNeron.NeronSchemeModelExistsDVRNF` (r6, SS1, SS3) from
    `NeronDVRLocal`;
  * `NeronDescentSH → NeronDVRLocal`;
  * `#check`s of the descent tools of §3.1.

  All axiom lists are `[propext, Classical.choice, Quot.sound]`.
* **Integration bug in dedekind-free's contribution.** `ZInQKernel/Contrib/OneProof/MumfordGroupLawDescent.lean`
  (merged from dedekind-free) **does not build on fork main d879bb73**:
  * `lake build` gives one error, at L855 (`scratch/neron-descent/build_MumfordGroupLawDescent.err.txt`);
  * `neronDVRLocal_of_dedekind` applies the field without the hypothesis `¬ IsField D` that 00f923e24 (reviewer
    fix) added to `NeronSchemeExtensionDedekind`. dedekind-free was built on c0f3d085, before that fix;
  * the fix is one line:
    `obtain ⟨N, hS, hSep, hQC, ε, hext⟩ := h Rv L (A.baseChange L) (IsDiscreteValuationRing.not_isField Rv)`.
  * `scratch/neron-descent/GroupLawDescentFixed.lean` is the whole file with that fix. It compiles with no errors,
    and `mumfordGroupLawDVR_proof`, `neronDVRLocal_of_dedekind` and `neronSchemeExtensionExists_of_dvrLocal` have
    standard axioms (`GroupLawDescentFixed.out.txt`). So dedekind-free's result holds on fork main once fixed.
  * Files under `ZInQKernel/` are not edited by this task.

## 6. Recommendation for the integrator

* **Apply the one-line fix of §5** to `MumfordGroupLawDescent.lean` when integrating dedekind-free.
* **Rebase dedekind-free's fold** (`scratch/dedekind-free/fold/`) before integrating it. It is written over
  `OpenResearchLeaves31` and `sixContactMin_of_open37_hf_gm_pz`, while fork main's bundle is now
  `OpenResearchLeaves38` (TailZ62/TailZ63). The fold is count-neutral and its new leaf `neronDVRLocal` is strictly
  weaker. It also drops `NeronGoodModelIso` and the DVR reading from the closure.
* **For the announcement**, list `NeronDVRLocal` as a literature leaf: BLR 1.4 Thm 3 at the DVR `(𝓞_L)_v`, locator
  UNVERIFIED. Formalization path:
  1. the henselian case is proved (FLT, neron-flt);
  2. contributors need Raynaud's quasi-projectivity (BLR 6.4/1) plus descent of quasi-projective schemes along
     `R → R^h`. Equivalently, they can prove (SA) of §3.3 together with affine patching along `R → R^h`.
* No new Prop is introduced; no statement is changed.
