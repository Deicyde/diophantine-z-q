# agent-T: top arguments hCM (`T5Glue.ShimuraMainCM`) and h33 (`TYZSplit.TYZThm33`)

Read-only triage, no Lean run. VERIFIED = read in code at file:line (paths relative to the worktree root);
SPECULATIVE = judgement; UNVERIFIED = literature from memory.

Top theorem (VERIFIED, ZInQKernel/OneProof/Main.lean:58-70): `hCM`, `hX` enter only through
`T5Glue.shimuraReciprocityModFn_of_printed hCM hX` (Main.lean:68), and `h33` only through
`TYZSplit.tyzThm33Pinned_of_tyzThm33 h33` (Main.lean:68). Both results go into
`TYZChain.tyzThm35ReadingA_of_leaves` (TYZChain/Main.lean:56-66).

---------------------------------------------------------------------------------------------------
## 1. hCM : `T5Glue.ShimuraMainCM`

### 1.1 Statement (VERIFIED, Contrib/OneProof/RingClassLattice.lean:911-924; ArtinCond :881)
For every squarefree `m`, a normalized `e : Kˢ → ℚ̄` (K = ℚ(√−m)), `σ ∈ Aut ℂ` and an idele `s` with
`σ = [s,K]` on every finite abelian F/K (`ArtinCond`), every `𝔞 ⊂ K`, and period pairs P, P' with lattices
κ(𝔞) and κ(s⁻¹𝔞): ∃ μ with `IsConjModel σ P P' μ`, and for every u ∉ 𝔞 and every v ≡ s⁻¹u, σ(℘_P(u)) = μ²℘_{P'}(v)
and σ(℘'_P(u)) = μ³℘'_{P'}(v). This is Shimura's Thm 5.4 with torsion (UNVERIFIED number).

### 1.2 Consumer chain (all VERIFIED)
- `shimuraReciprocityModFn_of_printed` (RingClassLattice.lean:3352) = `_of_t5'' hCM hX ringClassLattice` (:2762)
  → `_of_t5'` (:2754) → `_of_t5` (:2741) → `shimuraReciprocityModFn_of_split (cmModuli_of_t5 hCM hS) (x0RatStructure_of_leaf hX)`
  (:2686). `cmModuli_of_t5` (:2735) → `cmModuli_of_final` → `cmModuli_of_leaf` (:2722) → **`cmModuli_of`** (:1128).
  The rest of the glue is proved: `absArtinSurjectiveQNeg` (:2124), `latHatInter` (:1732), `strongApprox` (:1753),
  `ringClassLattice` (:3192), `invertibleColon` (:2519).
- **`cmModuli_of` is the only theorem that applies hCM.** It applies it twice:
  - **Step A** (:1164): `hL m hsq e he σ₀ 1 hs1 𝔞 (pp τ_Q) (pp τ_Q)`, with σ₀ fixing ιC(ℚ̄) and s = 1. It shows that
    j(τ_Q) and the Weber values at u = (k+1)/N are algebraic.
  - **Step B** (:1208): `hL m hsq e he σ s hs 𝔞 (pp τ_Q) (ppScale c' τ_{Q'})`. Here σ is any extension of ρ (`hA`),
    and s comes from `ArtinLift` (:1201), with ring class `[J∩O]` (`ringClass_of_artin`).
  - In both steps `𝔞 = κ⁻¹⟨1,τ_Q⟩` for a Heegner form Q of level N and discriminant D = discOf m f, and the only
    torsion points used are **u = (k+1)/N ∈ ℚ, 0 ≤ k < N−1** (`hu`, :1137).
- Through `ShimuraReciprocityModFn`, every use downstream is at **N = 32, g ∈ {x_C, y_C}** (the eta-model
  coordinates):
  - `shimuraReciprocityPic_of` (TYZGenus/ShimuraModFn.lean:122-127: `hS 32 _ hx …`, `hS 32 _ hy …`);
  - `cmValueRingClass_of_modFn` (ShimuraMain.lean:131), which consumers use only at `hV 32 _ (x/y)`
    (ShimuraMain.lean:58-59; TYZChain/Bridge.lean:3105-3107).
- The live consumers in TYZChain (L321.lean:2114-2162, Bridge.lean:3134-3144) are
  `cmFieldOfDefinition_of_shimuraModFn`, `shimuraReciprocityPic_of_shimuraModFn` (ShimuraTheta.lean:335,341) and
  `cmValueRingClass_of_modFn`. `ShimuraReciprocityPic` is applied with a nontrivial class only here:
  - ShimuraZn.lean:592: m = n (n ≡ 5 mod 8, squarefree), f = 4, J = (3+2√−n), Q = tyzForm n = [16(n+1),−8,1],
    Q' = tyzForm' n. Gives `TYZSigmaFixesZn`.
  - L321.lean:1137: m = n (n ≡ 5), f = 4, J = ϖ-ideal, Q = tyzForm n, Q' = tyzFormW n. Gives `TYZThm36OneFive`.
  - Bridge.lean:2976, 3024: m = n (n ≡ 7), f = 1, J = Jub n (class [𝔭₂]^{−5}), Q = tyzForm7 n and its conjugate.
    Gives `TYZThm36Seven`.
  - The trivial class (J = 1, Q' = Q) is used, through `CMValueRingClass`, for the fields of definition of TYZ's
    CM points: `znOverH4_of` (L321.lean:1988), `cmFieldOfDefinition7_of` and `cmAlgebraic_of_cmValue`
    (Bridge.lean:3101).

### 1.3 Answers to the key questions
- **The specialization is not K = ℚ(i).** `A : y² = x³+4x ≅ X₀(32)` is the *modular curve*, and its CM by ℤ[i] plays
  no role here. The CM curves are E_τ = ℂ/⟨1,τ_Q⟩ for TYZ's Heegner forms. These have CM by orders of conductor 4
  or 1 in **K = ℚ(√−n), for every squarefree n ≡ 5, 7 (mod 8)** (and the divisors e of n in those classes, through
  `znOverH4_of` at `tyzZn e`). That is infinitely many fields, so explicit computation on y² = x³+4x is
  impossible (VERIFIED by the call sites above).
- **The j-part alone is not enough.** `MainTheoremCMj` is itself an unproved leaf def (TYZChain/ModFn.lean:105), and
  Tau Ceti has no CM theory: I grepped `Contrib/TauCeti` for complex multiplication and j-invariant and found
  nothing relevant. The compiled split `ShimuraReciprocityModFn ⇐ MainTheoremCMj ∧ RatX0Rep ∧ …Singular`
  (ModFn.lean:392) still needs the level-structure part at non-isolated points:
  - for the class-7 forms tyzForm7 n, the 32 values n = 7, 15, 47, …, 4087;
  - for class 5, unknown in general; every sampled case was isolated
    (docs/research/shimura-modfn.md:44, :217-237).
- **Tau Ceti CFT (VERIFIED by name):**
  - `globalArtinMap_isArithFrobAt` (TauCeti/NumberTheory/ClassFieldTheory/Global/LocalArtin/Frobenius.lean:154);
  - `isArithFrobAt_of_globalArtinMap_ofAdicCompletion_eq` (:138);
  - `ringClassArtinEquiv_ringClassIdeleQuotient` (…/ClassFields/RingClass/Field.lean:197).

  These, together with absArtinSurjectiveQNeg and ringClassLattice, already make up all the CFT glue. What is
  missing is purely the elliptic-curve CM content: Deuring reduction and the action on torsion.
- No other open field gives hCM. `shimuraTaniyamaQbar` (OneProof/H/TailX.lean:170) covers only abelian *surfaces*
  over ℂ and has no reciprocity.

### 1.4 Weakest form used (precise sketch)
```
ShimuraMainCM32 : ∀ m sqfree, ∀ e normalized, ∀ σ s, ArtinCond m e σ s →
  ∀ (D) (hD : D = discOf m f) (Q : HeegnerForm 32 D) (P' : PeriodPair),
    let 𝔞 := κ⁻¹⟨1,τ_Q⟩;  P'.lattice = κ(s⁻¹𝔞) →
    ∃ μ, IsConjModel σ (pp τ_Q) P' μ ∧ ∀ k < 31, ∀ v, s_f v − (k+1)/32 ∈ 𝔞̂ →
      σ(℘_{τ_Q}((k+1)/32)) = μ²℘_{P'}(κ v) ∧ σ(℘'…) = μ³℘'_{P'}(κ v)
```
The `∀ σ s` is needed in two forms: (i) s = 1 with σ trivial on ℚ̄; (ii) s with [s] = [J∩O] (SPECULATIVE whether
you could restrict further to J ∈ {α, ϖ, Jub, 1}: the generic chain CMModuli → ModFn quantifies over all J). A
restriction of m to n ≡ 5, 7 (mod 8) and f ∈ {1,4} would need `CMFieldOfDefinition ringClassFieldD` (∀ D) to be
narrowed at its consumers too (SPECULATIVE; not traced).

### 1.5 Provability and tier
- **T4.** It is the main theorem of CM with level-32 structure for infinitely many K. There is no bypass and no
  ignoring consumer.
- Step A (algebraicity) alone would follow from "j(τ) algebraic for CM τ" plus Tau Ceti's division polynomials
  (DivisionPolynomial/*). But that does not remove Step B (SPECULATIVE).
- **Plan:** keep cited.
  - Optional narrowing (T2, removes nothing): thread an N = 32-only chain, i.e.
    `CMModuli32 → ShimuraReciprocityModFn32 → shimuraReciprocityPic_of / cmValueRingClass at 32`, with the leaf
    `ShimuraMainCM32` restricted to Heegner lattices of level 32 and u ∈ (1/32)ℤ. The reading risk drops: the leaf
    only ever speaks about Γ₀(32)-level structure.
  - Alternative (already compiled): MainTheoremCMj + RatX0Rep + the Singular part. This shrinks the CM content to
    the j-form outside a finite class-7 set, but replaces hX by RatX0Rep. Shimura-modfn recommended keeping
    the single leaf.

---------------------------------------------------------------------------------------------------
## 2. h33 : `TYZSplit.TYZThm33`

### 2.1 Statement (VERIFIED, OneProof/TYZSplit.lean:157-181)
For every sign choice ℓ of 𝓛: ∃ Q m ε with
- m > 0;
- InMinus d (Q d);
- ε in TYZ's classes (EpsTYZ);
- Q d torsion when the L-order is > 1 (d ≡ 5, 6, 7);
- for all squarefree n ≡ 5, 7 (mod 8), all Φ (IsPhi) and all χ : Cl_n → ±1:
  - (a) P_χ non-torsion ⇒ χ = χ_{d₀,d₁} (the excluded part);
  - (b) for χ = χ_{d₀,d₁}: m(d₀)·P_χ − ε·2^{h₂}·ℓ(d₁)·Q(d₀) is torsion (the formula).

### 2.2 Consumers (VERIFIED)
- `tyzThm33Pinned_of_tyzThm33` (TYZSplit.lean:520-547):
  - **InMinus is discarded** (`-` at :522);
  - the ε classes are kept only for (5,3), (5,1), (7,1), (7,3) (:524-527);
  - Q-torsion is used only at **d = n ≡ 5 with ℓ n = 0** (:528-529);
  - (b) is used only for **χ = chiT(pairSet n d₀ d₁)**, d₁ ≡ 1, 3 (:537-541);
  - (a) is used only for **n ≡ 5 and χ = chiT(pairSet n d₀ d₁) with d₁ ≡ 5, 7** (:542-547; excluded genus characters).
- `TYZ35.thm35First_of_thm33` (TYZChain/Thm35.lean:617-716):
  - it uses only `ℓ 1 = 1` from ℓ (:617);
  - `level_identity` (:541) uses (b) and (a) for **one** lift family f, the one from `exists_liftFamily` (:569-570);
    (a) is used only when n ≡ 5 (:579-584);
  - the strong induction runs over all squarefree d ≡ 5, 7 dividing n (:624-694);
  - Q-torsion is used only at the final n (:710-715).
- `thm35First_of_lcal_thm33` (:718) → `T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First`
  (L321.lean:2156) → Bridge.lean:3134 → `tyzThm35ReadingA_of_pinnedLeaves` (Bridge.lean:566) as `h35`.
- Downstream: ReadingA (Hypotheses/CR3Literature.lean:141) holds for all d ≡ 5 (mod 8) squarefree of analytic rank
  ≥ 2. The final chain uses only its `.2` (T5bCl d = 0; CR3Literature.lean:157, via GZDecomp/Scope.lean:57-62).
  The d range is the infinite CR₃ family (CertifiedRank, Hypotheses/CertifiedRank.lean:56: d has a divisor
  ≡ 7 mod 8), so there is **no finite specialization of n** (SPECULATIVE beyond that: I did not trace how many
  primes d has).

### 2.3 Weakest form used
Literally `∀ ℓ, IsTYZLcal ℓ → Package.Thm35First ℓ tyzZ` (Package.lean:289: for n ≡ 5, ℓ n = 0 ⇒ Pseq torsion).
That is TYZ Thm 3.5(1) and is no easier. The most economical form that is still close to the print is the leaf with:
- InMinus dropped;
- classes 6 and 2 dropped;
- (a) restricted to n ≡ 5 and the genus characters χ_T with d₁ ≡ 5, 7;
- Q-torsion restricted to d ≡ 5;
- "∀ Φ" weakened to "∃ a lift family" (only the one from exists_liftFamily is used).

The coefficient formula **is** used, modulo torsion only, with Q and m existential (the value 2^{−1−ρ}𝓛 of 𝒫 is
already forgotten). The exact 2^{h₂(n)} matters because it cancels against 2^k = (1|2)·2^{h₂}
(Thm35.lean:597-610), and so do ℓ(d₁) and the ε classes.

### 2.4 Provability and tier
- **T4.** Both (a) and (b) are Gross–Zagier (YZZ) consequences: excluded characters are torsion by GZ plus the
  root-number vanishing of L(E_{d₁},1) for d₁ ≡ 5, 7 (UNVERIFIED reading of TYZ Lemma 3.14).
- Nothing in Contrib/TYZ* proves torsion of any P_χ. A grep for `IsOfFinAddOrder (Pchi` finds only the leaf
  statements (Thm35.lean:118, :548; TYZSplit.lean:166). The numerics (tyz-t1 `tmany.py`) are evidence, not proof.
- Tau Ceti has `Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder`
  (TauCeti/AlgebraicGeometry/EllipticCurve/CanonicalHeight/Basic.lean:333), but there are no Heegner-point heights
  and no GZ.
- **Plan:** keep cited. Optional statement hygiene (T1): drop the unused InMinus and the 6/2 classes, and restrict
  (a) as above. This lowers the reading risk but removes nothing. Weakening to Thm35First is possible but not a
  printed display (same verdict as scratch/gap-triage/agent-TOP.md:197-240).
