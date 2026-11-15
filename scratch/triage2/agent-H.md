# agent-H: height group, packet R5 (bostLowerBound, javanpeykarBound, pazukiCor13Upper, gaudronRemondThm14)

Read-only triage. No Lean was run. Marks: VERIFIED = read in code at the given file:line; SPECULATIVE = my judgement;
UNVERIFIED = literature recalled from memory. All paths are relative to /home/jackmccarthy/dzq-wt/triage2.
The earlier triage scratch/gap-triage/agent-CD.md §§172-260 and :598-601 reaches the same verdicts. This file
re-checks them against the current tree and adds the slack analysis (§0.3) and the type details of the GR bypass (§4).

## 0. Common chain (VERIFIED)

### 0.1 From the bundle to the consumers
- The fields sit in OpenResearchLeaves21 (TailZ34.lean:28-35) and are passed unchanged down the generations:
  open28→27→26→25→24→23→22→21→20→19→18→17→**11**→10→9→8→7→6→4→`sixContactMin_of_leavesR3`. I got this list by
  scanning every `sixContactMin_of_openN` body.
- `heightRowsNo20_of8` (TailZ4.lean:153) is the combining theorem. It builds the rows from the fields:
  - R18 = `r18_of_leaves javanpeykarBound hN1 SS1 SS2 hMet` (TailY.lean:535);
  - R19 = `r19_of_leaves gaudronRemondThm14 …` (TailY.lean:842);
  - R21 = `r21_of_leaves' bostLowerBound … gl.an3Unique` (TailY.lean:498);
  - R22 = `r22_of_upper pazukiCor13Upper …` (TailY.lean:812).
  - The other inputs: `hN1` comes from `t.neronSchemeExtensionExists`; `gl` and `hMet` come from
    `heightGlue_of_t35 (h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)`.
- `researchLeaves7_of_open8` (TailZ4.lean:181, lines 203-207) puts R18, R19, R21, R22 and `h5fin` into
  OpenResearchLeaves7. They reach `HSyn.ResearchLeaves3` (TailD.lean:71-82) through `researchLeaves3_of_open2`
  (TailE.lean:6569).

### 0.2 The only consumers on the live path
- **`glueOutputs_of_leaves3`** (TailD.lean:201-253):
  - r18 → `r18Concrete_of` (:206) → `javanpeykarJ1_of_le` (Genus/Bridge.lean:55; call at TailD:244);
  - r22 → `r22Concrete_of` (:207) → `thetaPazuki` (LPrefix.lean:12080; call at TailD:221);
  - r19 and r21 → `transfer_core r.r19 h20 r.r21 …` (TailD:251; theorem at LPrefix.lean:12153).
- **`reverseIsogeny_of_leaves3`** (TailD.lean:117) → `isogenyReverseExists_of_r19` (TailA.lean:945). It uses r19.
  It is called from `gluePieces_of_open4` (TailK.lean:308).

### 0.3 What the target needs
- The target `ZInQ.SixContactMin` (Hypotheses/HeightMin.lean:50) is an **explicit, uniform** inequality:
  `ratHeight u ≤ heightH6 D · M(u)^24`. The docstring (:35-37) says the consumers need a bound that is effective and
  uniform in u.
- So no non-effective result (Faltings, Shafarevich, Masser–Wüstholz without a polynomial exponent) can replace these.
- Every object is a member of a family (u ∈ ℚ, N ≥ 1, [L:ℚ] ≤ Q·M), so no finite computation can supply the bounds.

**Slack** (VERIFIED, HDecomp/Assembly.lean):
- `transfer_numerics` (:221) already accepts weaker inputs than `transfer_of_level` (:319) feeds it:
  - `hFJ ≤ Q^13·M^24` (Javanpeykar supplies 1.3e7·N^12 ≤ 1.3e7·Q^12·M^24);
  - `hZ ≥ −2g` (Bost supplies −(3/2)g);
  - `g ≤ Q^3·M^4`.
- `max_one_hA_le_noncm` (:604) concludes `hA ≤ Q^17·M^24`, where `Q = D^(D·E0) ≥ 10^12`.
- So the constants have enormous slack, but the **M-exponents are tight**:
  - the total N-exponent of the Javanpeykar bound must stay ≤ 12;
  - GR's `log deg` must stay `O(g^6)` with no extra log factor;
  - Pazuki must stay linear in h_F.
- Changing these constants would only edit glue (`NonCMOutput`, numerics). None of the four becomes easy with crude
  constants (§1-§4).

### 0.4 Semantic prune check
- Every output is read:
  - `jHeightBound_of_glueOutputs` (LPrefix.lean:2977) uses both `PazukiOutput` and `NonCMOutput`;
  - `transfer_core` uses every conjunct of `NonCMOutput`;
  - the CM branch is never taken (the proof always uses `Or.inl`, TailD:223).
- The finiteness clauses R18 ⇒ `h ≠ ⊤` and R21 ⇒ `h ≠ ⊥` are redundant at the consumers, because heights arrive as
  reals through `faltingsHeight_coe hfin`. Their glue (`hMet`, `an3Unique`) is needed anyway for `h5fin`
  (`stableHeightFinite_of'`), so dropping the clauses saves no field.
- The one discarded piece is **GR's second conjunct** (§4).

## 1. bostLowerBound — `ZInQ.HeightSplit.BostLowerBound` (TailY.lean:443)

1. **Statement.** For an abelian variety A of dimension g over a number field, with published stable height x:
   `−(g/2)·log 2π ≤ x + (g/2)·log π` (Bost, Deligne normalization). R21 needs only the derived `GRBostBound`
   (TailY:452), `h_F ≥ −(3/2)g`.
2. **Consumers.**
   - `r21_of_leaves'` (TailY:498) → R21 → `transfer_core` (LPrefix:12153-12168): `hB := r21 L Z gZ hZd`, giving
     `-(3/2)·gZ ≤ z`.
   - It is applied to one object: **Z**, the Poincaré complement of the fibre surface A in J₁(N)_L. Z is produced by
     `t.t8` (TailD:229). Its dimension `gZ ≤ g = dim J₁(N) ≤ N²`; L is a number field that varies with u.
   - Only the lower bound is used, on a real height z.
3. **Weakest form.**
   `∀ L Z gZ z, Z.dim = gZ → stableFaltingsHeight Z = z → −2·gZ ≤ z`
   (the constant −2 is the slack in `transfer_numerics`). Z is in effect an arbitrary abelian variety, an isogeny factor
   of J₁(N)_L.
4. **Provable?** No (SPECULATIVE). Any lower bound on h_F needs Bost's argument or Moret-Bailly's formule clé
   (Arakelov theory, theta norms; UNVERIFIED). No bypass found:
   - h(A) + h(Z) ≤ h(P) needs a lower bound on one factor;
   - Pazuki's lower half covers only principally polarized surfaces.
5. **Tier.** T4. No narrowing that removes the field. A cosmetic option is to state it as GRBostBound restricted to
   real heights; this saves nothing.

## 2. javanpeykarBound — `ZInQ.HeightSplit.JavanpeykarBound` (TailY.lean:522)

1. **Statement.**
   - Setting: a pointed curve X over a number field K, with Jacobian J of dimension g ≥ 1 and a K-rational Belyi
     function t of degree d.
   - Bound: the published stable height x of J satisfies `x ≤ 13·10⁶·g·d⁵`. This is Javanpeykar ANT 2014 Thm 1.1.1,
     specialized.
2. **Consumers.**
   - `r18_of_leaves` (TailY:535) → `r18_lf8` (TailZ4:46) → `r18Concrete_of` (LPrefix:12024) → `javanpeykarJ1_of_le`
     (Genus/Bridge.lean:55-73).
   - It is applied **only at K = ℚ** (`hR18 ℚ X …`, Bridge.lean:59): X is the model of X₁(N) from `X1BelyiOnModel`,
     J = J₁(N), t = j/1728, with d ≤ N² and g ≤ N². The output is `h_F(J₁(N)) ≤ 1.3e7·N¹²` (`JavanpeykarJ1`,
     LPrefix:11879), and it feeds `hJav` of `transfer_core`.
   - The upper bound is the only direction used.
3. **Weakest form.** `∀ N ≥ 1, J₁(N)/ℚ, x real, h_F(J₁(N)) = x → x ≤ C·N¹²`. Per §0.3, C up to about Q·(1/1.3e7)
   would do after a numerics edit. The exponent 12 must not grow.
4. **Provable?** No (SPECULATIVE).
   - Specialized results such as Ullmo / Jorgenson–Kramer bounds for h_F(J₀(N)), or Kramer-type bounds for J₁(N)
     (UNVERIFIED), are also research-scale.
   - Nothing in Mathlib or the vendored libraries computes Faltings heights of modular Jacobians.
   - Restricting to K = ℚ and X₁(N) narrows the statement but does not remove it.
5. **Tier.** T4. Optional weakening: K = ℚ only. Also note r18's `≠ ⊤` clause is unneeded by the consumer (§0.4).

## 3. pazukiCor13Upper — `ZInQ.HeightSplit.PazukiCor13Upper` (TailY.lean:778)

1. **Statement.**
   - Setting: an abelian surface A/K with published height x, a uniformization, a Siegel period matrix Ω, and an
     algebraic representative z of the ten even theta nulls.
   - Bound: `max(1, h_ℓ²(z)) − max(1, x + log π)/2 ≤ C₂·log(min(…) + 2)`.
   - This is the upper half of Pazuki 2012 Cor. 1.3(2) with g = r = 2.
2. **Consumers.**
   - `r22_of_upper` (TailY:812) → `r22_lf8` (TailZ4:53) → `r22Concrete_of` (LPrefix:12033) → `thetaPazuki`
     (LPrefix:12080-12097).
   - `thetaPazuki` takes X = max(1, x + 3). It is applied to **A = the fibre QM surface over J(u)**: g = 2,
     `FibreOver`, z from `ThetaPointOfFibre`.
   - The output `PazukiOutput` (LPrefix:2962) is used in `jHeightBound_of_glueOutputs` (LPrefix:2983, through
     `pazuki_numerics`).
3. **Weakest form.** For the QM fibre surfaces only: `h(z) ≤ c₁·max(1, h_F(A)) + c₂`. This would need a numerics
   edit; c₁ can be large only if it is absorbed by the Q-slack (Q^17 vs Q^13), and the bound must stay linear in h_F.
4. **Provable?** No (SPECULATIVE). This is the comparison of theta height with Faltings height through Moret-Bailly's
   key formula (UNVERIFIED). Restricting to QM surfaces does not obviously help. A direct route through the Shimura
   curve X6 (Arakelov height of the Hauptmodul) would be a different research proof.
5. **Tier.** T4. No narrowing. The open reading risk (θ[a;0](0,2Ω) vs classical constants, about log 4; TailY
   docstring above :759) remains.

## 4. gaudronRemondThm14 — `ZInQ.HeightSplit.GaudronRemondThm14` (TailY.lean:834)

1. **Statement.** If A and B are isogenous over K, with g = dim A and published height x, then there are isogenies
   **in both directions** of degree ≤ κ = ((14g)^{64g²}·[K:ℚ]·max(x, log[K:ℚ], 1)²)^{1024g³}.
   - Source: Gaudron–Rémond, Duke 2014, Thm 1.4.
   - κ is `grKappa` (HDecomp/Faltings/Leaves.lean:52).
2. **Consumers** (two, both via R19 from `r19_of_leaves`, TailY:842):
   - (a) `transfer_core` (LPrefix:12168) uses `obtain ⟨⟨ψ, hψ, hdeg⟩, -⟩ := r19 L J P g x hJd hx ⟨φ, hφ⟩`. This is
     **only the first conjunct** (same direction J → P, with the degree bound), at J = J₁(N)_L (base change from ℚ,
     g ≥ 2) and P ≅ A × Z. `log deg ψ` feeds `NonCMOutput.L`.
   - (b) `isogenyReverseExists_of_r19` (TailA:945-953) uses `obtain ⟨-, ψ, hψ, -⟩`: **only the existence** of a
     reverse isogeny; the degree is discarded. It reaches the chain through `reverseIsogeny_of_leaves3` (TailD:117),
     called from `gluePieces_of_open4` (TailK:308).
3. **Weakest form.**
   `∀ L J P g x, J.dim = g → h(J) = x → (∃ J→P isogeny) → ∃ ψ : J → P, IsIsogeny ψ ∧ deg ψ ≤ grKappa g [L:ℚ] x`
   - This is one direction only, with J = J₁(N)_L.
   - Use (b) can be served by the open field `milneIsogenyQuasiInverse` (OpenAddedLeaves17, TailZ34.lean:120),
     which is kept anyway for `detTate`.
4. **Bypass for (b): T1, glue only.**
   - Caveat: the leaf `MilneIsogenyQuasiInverse` (TailQ.lean:1207) drops "g is an isogeny"; it gives
     `g : Hom B A` with `f≫g = [d]` and `g≫f = [d]`.
   - So the glue must prove that g is finite and surjective. This is exactly the end of `end0Division_of_homFree`
     (TailA.lean:1290-1327):
     - `mulIsogeny_proved` (TailE.lean:6376) gives `[d]` finite and surjective (char 0);
     - Mathlib's `IsFinite.of_comp` and `Surjective.of_comp` do the rest;
     - `IsSeparated.of_comp` handles separatedness;
     - `IsMonHom` comes from the `Hom` structure.
   - Then write `IsogenyReverseExists` (TailA:819) through `LeafAdopt.abVarEquiv` (LPrefix:5286, defeq on `.X`).
   - Then `gluePieces_of_open4` uses `reverseIsogeny_of_exists (that)` in place of `reverseIsogeny_of_leaves3`, with
     the leaf threaded from `l.isogenyQuasiInverse`.
   - Snag: `l.isogenyQuasiInverse` is the weaker `WeilPairing.IsogenyQuasiInverse` (TailB:3765, on K̄-points only).
     The Milne form must be threaded down from `isogenyQuasiInverse_lf7 l.milneIsogenyQuasiInverse` (TailX:52/255),
     or a points-to-morphism argument must be added. Expect about 6 generations of signature plumbing:
     TailX→TailO→TailK.
   - After that, R19's second conjunct is unused and `GaudronRemondThm14` can be weakened to one direction. This
     **does not remove the field**.
   - Side benefit: it removes the risk that the printed GR Thm 1.4 bounds the reverse direction by κ(B) rather than
     κ(A) (UNVERIFIED; the agent-CD triage did not check this either).
5. **Provable?** The first conjunct is not provable (SPECULATIVE). Isogeny estimates with log deg = O(g^6) need
   GR / Bost–David period theorems; Masser–Wüstholz-type exponents in g (UNVERIFIED) would break the M^24 exponent.
   **Tier:** T4 for the field; T1–T2 for the one-direction weakening.
