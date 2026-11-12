# glue-assembly: the assembly glue of H (steps C8, C10, E1, E3, E4, F2)

Status: research note (task glue-assembly, 2026-11-11). It works out the glue clusters that join
the modularity half and the Arakelov half of the proof of `ZInQ.SixContactMin` (h-trust steps
C8, C10, E1, E3, E4 and F2), together with the assembly of the constants into `H₆(D)`. For each
step it states the claim precisely, lists the literature inputs, and decides what Lean can state
and prove over genuine definitions. Drafts: `scratch/glue-assembly/` (all compile with
`lake env lean`, none contains `sorry`). Log: `scratch/glue-assembly/log.md`. No file under
`ZInQKernel/`, `blueprint/` or other notes was edited.

Marks: **VERIFIED** means read in a source in the repository, computed, or compiled. **STANDARD**
means a published theorem with a reference; locators recalled from memory are marked UNVERIFIED
(there was no network). **SPECULATIVE** means an assessment. N5 Lnnn are lines of
`diophantine_zq.tex`.

## 0. Summary

1. **The Arakelov half and the final constant are assembled in Lean (VERIFIED: compiled).**
   `GlueAssembly.sixContactMinAt_of_glueOutputs : GlueOutputs S → SixContactMinAt S`
   (`scratch/glue-assembly/GlueAssembly.lean`, about 900 lines, built from five part files by
   `build.sh`). `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound`.
   `SixContactMinAt Mult.S_mul` is `ZInQ.SixContactMin` word for word (the scratch file cannot
   import `HeightMin`; §1.3). The theorem checks, in one chain:
   - **F2 over Mathlib's genuine Weil height** (`logHeight_Phi_le`): for every field `K` with
     admissible absolute values and `z ∈ K¹⁰`,
     `h_K([3779136(∏z_m)⁴ : (∑z_m⁸)⁵]) ≤ 40·h_K(z) + n_K·log 3779136`, `n_K = [K:ℚ]` for number
     fields. `log 3779136 < 16`, so N5's `+22` holds with room.
   - **The height of a rational number does not change in a number field**
     (`logHeight₁_algebraMap_rat`): `h_K(q) = [K:ℚ]·log max(|num q|, den q)`. Mathlib lacks this,
     and wk-h §4.2 named it as the missing piece for F2.
   - **E2-E4 arithmetic from the level** (`transfer_of_level`): from `N ≤ QM²`, Javanpeykar's
     bound, `[L':ℚ] ≤ QM`, the Gaudron–Rémond degree bound, Faltings' height variation with
     additivity and Bost's lower bound, it gives `h_F(A) ≤ Q¹⁷M²⁴`.
   - **The CM-branch arithmetic** (`cm_numerics`): `h_F(A) ≤ C_cm`.
   - **F3 arithmetic** (`pazuki_numerics`), **F4** (JHeight's `twelve_mul_ratHeight_le`, copied),
     and **the final constant** `(40·10⁴·2²⁴ + 22)·max(1, C_cm, Q_D¹⁷)·M²⁴`, which turns into
     `h(u) ≤ H₆(D)·M_S(u)²⁴`.
2. **What `GlueOutputs S` assumes, and what it is not.** For each `u ∉ 𝒞` it asks for:
   - a number field `K` and a point `z ∈ K¹⁰` with `Φ(z) = J(u)`. This part is genuine: real
     field elements with their real Weil height;
   - one real number `h_A` (meant: the stable Faltings height of `A`) satisfying Pazuki's bound
     for `h(z)`;
   - the numerical outputs of the non-CM transfer or of the CM branch.

   Mathlib has no abelian varieties with Faltings heights, so these outputs enter as real
   numbers with the inequalities the theorems give. **As a Lean Prop, `GlueOutputs` is therefore
   a height bound in disguise, not a faithful statement of the literature** (as wk-h §4.3 found
   for its signature). Its value is the contract it fixes: each conjunct is exactly what one leaf
   or one upstream step must deliver (§1.2). Once a Faltings-height object layer exists
   (pkg-I5 §5), each conjunct is replaced by its leaf applied to concrete objects, and the
   theorem above needs no change. Unlike wk-h's `ArakelovSig`, no abstract structure is invented.
3. **Elementary glue of C8, F3 and the statable leaves (VERIFIED: compiled).**
   - C8 (`C8.lean`): the Hodge–Tate weight comparison in both normalizations
     (`weight_match`, `weight_match_coh`), and the determinant argument for the finiteness of the
     twisting character as group theory over an arbitrary group with values in a field's units
     (`twist_finite`).
   - F3 (`F3Glue.lean`): N5's normalization sentences. The Euclidean projective height dominates
     the sup height (`mulHeight_le_mulHeightL2`). Adjoining the six zero odd theta constants does
     not change the height. Multiplying coordinates by roots of unity does not change it either.
   - E2 (`E2Index.lean`): `[SL₂(ℤ) : Γ₁(N)] ≤ N²` over Mathlib's `Gamma1`. This is N5's "the
     index of `Γ₁(N)` is at most `N²`".
   - Leaves statable in Mathlib today (`Leaves.lean`): `KroneckerWeber` (proved in Tau Ceti,
     per prereq-survey) and `BrauerNesbittCharZero` (not proved anywhere we found). These are
     the only leaves of the cluster that Mathlib can state.
4. **Verdict on the six steps.**
   - **F2**, and the E3, E4 and CM arithmetic, are now proved in Lean. F2 is proved as a
     statement about genuine Weil heights.
   - **E1** splits into a linear-algebra lemma, now proved (invariants commute with extension
     of the coefficient field, `E1Lin.lean`), and Faltings' Hom theorem with Poincaré
     reducibility. Those two cannot be stated without Tate modules of abelian
     varieties.
   - **C8** keeps three leaves that cannot be stated today: (HT) for eigenforms, Deligne–Serre,
     and the Weil pairing. Kronecker–Weber can be stated and is proved in Tau Ceti. Its glue is
     proved.
   - **C10** needs ℓ-adic Galois representations of `G_ℚ` with Frobenius elements, Néron models
     and Mumford §19 Thm 4. Only its Brauer–Nesbitt input can be stated.
5. **Biggest obstacle.** It is the same object layer wk-h and pkg-I5 identified:
   - abelian varieties over number fields, with isogeny degrees, the stable Faltings height and
     Tate modules (for E1-E4);
   - ℓ-adic Galois representations of `G_ℚ` with Frobenius and Hodge–Tate conditions (for C8,
     C10).

   Within this cluster nothing else blocks: every step that can be stated over Mathlib's objects
   is proved.

## 1. The assembly theorem

### 1.1 Statement (VERIFIED: compiled)

```
def GlueOutputs (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ∃ (K : NF) (z : Fin 10 → K.K) (hA : ℝ),
    3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K.K (Jmap u) ∧
    PazukiOutput (logHeight z / Module.finrank ℚ K.K) hA ∧
    (NonCMOutput (heightQ heightD) (contactSupport S u) hA ∨ CMOutput hA)

theorem sixContactMinAt_of_glueOutputs {S} (h : GlueOutputs S) : SixContactMinAt S
```

`NF` bundles a number field. `Jmap u = −57600F(u)²/G(u)⁶` (JHeight). `logHeight` is Mathlib's
relative projective Weil height on `K`. Dividing it by `[K:ℚ]` gives the absolute height, which
is the one N5 uses.

### 1.2 The contract: who supplies each conjunct

| Conjunct | Meaning | Supplier |
| --- | --- | --- |
| `Φ(z) = J(u)` in `K` | `z` = the ten even theta nulls of the QM surface `A` over `J(u)`, after a field extension for the theta structure | A1-A4, A7 (the surface `A` over the Hauptmodul value `j = J(u)`, h-b1 M7) and F1 (Lin–Yang Ex. 30, LNY §2.2, Igusa 1967, `igusa_check.py`) |
| `PazukiOutput (h(z)) hA` | `h(z) ≤ X_D/2 + C₂ log(X_D+2)`, `X_D = max(1, h_A + log π)`, `C₂ = 1000·2⁴(log 2⁴)⁵` | F3: Pazuki 2012 Cor. 1.3(2), `g = r = 2`, Deligne metric, read through the normalization glue of §2.7 |
| `NonCMOutput Q M hA`: `1 ≤ N ≤ QM²` | the level of the newform | A-D (modularity half): C9 and D1-D5, with Carayol for D5 |
| `hFJ ≤ 1.3·10⁷N¹²`, `2 ≤ g ≤ N²` | `h_F(J₁(N))` and `g = dim J₁(N)` | E2: Javanpeykar Thm 1.1.1 at `X₁(N)` with `g, deg_B ≤ N²`; `g ≥ 2` from E1 |
| `1 ≤ d ≤ QM` | `d = [L':ℚ]` | B3 |
| `L ≤ 1024g³(64g² log 14g + log d + 2 log max(hFJ, log d, 1))` | `L = log deg φ`, `φ : J₁(N)_{L'} → A × Z` | E1 (an isogeny exists) and E3 (GR14 Thm 1.4 with source `J`) |
| `hA + hZ ≤ hFJ + L/2` | | E4: Faltings Lemma 5 (`h_F(A×Z) ≤ h_F(J) + ½ log deg φ`) and additivity |
| `−(3/2)g ≤ hZ` | | E4: Bost, `h_F(Z) ≥ −(3/2) dim Z`, with `dim Z ≤ g` |
| `CMOutput hA` | `d ≤ D`, `h_F(E) ≤ B_cm`, GR14 with source `E²`, `h_F(A) ≤ 2h_F(E) + L/2` | CM branch, N5 L581-628. h-trust replaces it by NoCM (the branch is empty), so the right disjunct is never used on that route |

### 1.3 Two technical findings (VERIFIED)

- **Scratch files cannot import `ZInQKernel.Hypotheses.JHeight` or `HeightMin` in this
  worktree.** `lake env lean` reports "unknown module prefix 'ZInQ'": the import chain of
  `HeightMin` reaches the upstream package `lean/`, which is not built here. Hence:
  - `F4Copy.lean` copies JHeight's F4 part verbatim;
  - the conclusion is `SixContactMinAt S`. Its body is that of `ZInQ.SixContactMin` with
    `Mult.S_mul` replaced by `S`.

  `ZInQKernel.Compiler.Precision.HeightConstant` imports only `Hypotheses.Height`, so it can be
  imported; it supplies `ten_pow_twelve_le_heightD`, `heightE0_eq`, `heightBcm_eq` and
  `heightCcm_eq`. A task that may edit `ZInQKernel/` can move the file under
  `ZInQKernel/Hypotheses/`, import `JHeight`, delete the copy, and get
  `GlueOutputs Mult.S_mul → SixContactMin` directly.
- **Kernel trap.** `rw [heightCcm_eq_ccmFn, ccmFn_eq]` under a cast to `ℝ` elaborates, but the
  kernel then refuses with "Nat.pow … does not fit in a 32-bit unsigned integer". The fix was to
  prove the CM bound over variables (`cm_branch_nat`) and apply it to `heightBcm_eq` and
  `heightCcm_eq` (the memory note on huge constants describes the same mechanism).

## 2. The steps

### 2.1 C8: the twist and the weight (N5 L757-768)

**Statement.** Let `r₅ : G_ℚ → GL₂(\bar ℚ₅)` be the representation of C1-C7 (Hodge–Tate weights
`{0, −1}` in the Tate convention, `χ` of weight `−1`). Pan's theorem gives `r₅ ≅ ρ_g ⊗ ψ` for a
cuspidal eigenform `g` of weight `k ≥ 1` and a continuous character `ψ`. Then `k = 2`, and `ψ` is a
finite-order character, hence a Dirichlet character. So `r₅ ≅ ρ_{g⊗ψ}` (Tate normalization) for a
weight-2 eigenform `g ⊗ ψ`.

**Proof (h-trust C8, with the determinant argument of V16 L660-667).**
1. Weights. `ρ_g` is Hodge–Tate with weights `{0, 1−k}` (input (HT)). If `k = 1`, Deligne–Serre
   gives finite image, so all weights of `ρ_g ⊗ ψ` are equal, against `{0, −1}`. The `ψ`-line in
   `Hom(ρ_g, r₅)` is Hodge–Tate of some integer weight `n` (Hodge–Tate is closed under `Hom` and
   subobjects). So `{n, n+1−k} = {0, −1}`, which forces `k = 2` and `n = 0`.
2. Finiteness. Take `F/ℚ` finite Galois with `A`, its endomorphisms and a polarization defined
   over `F`. The Weil pairing gives `det V₅(A) = χ²` on `G_F`. With `V₅(A) ⊗ E ≅ r₅ ⊕ r₅` this
   gives `(det r₅)² = χ²` on `G_F`. Since `det r₅ = ε_g χ ψ²`, `ψ` has finite image.
3. Kronecker–Weber makes `ψ` a Dirichlet character.

**Leaves.**

| Leaf | Statement used | Statable in Lean today? |
| --- | --- | --- |
| (HT) Saito 1997, or Scholl 1990 with Scholze 2013 Cor. 1.8, or Kato 2004 §9.4 (locators UNVERIFIED; h-trust C8) | for every cuspidal eigenform `g` of weight `k ≥ 2` and every level, `ρ_g|G_{ℚ₅}` is Hodge–Tate with weights `{0, 1−k}` | no: needs Galois representations of eigenforms and Hodge–Tate representations |
| Deligne–Serre 1974, Thm 4.1 (UNVERIFIED) | a weight-one newform has a Galois representation with finite image | no |
| Weil pairing (Mumford §§20, 23, UNVERIFIED) | `e(σx, σy) = χ(σ)e(x, y)`, so `det V_ℓ(A) = χ^{dim A}` on `G_F` | no: no Tate modules of abelian varieties |
| Kronecker–Weber (Washington, Thm 14.1, UNVERIFIED) | a finite abelian extension of `ℚ` lies in a cyclotomic field | **yes**: `GlueAssembly.KroneckerWeber` (`Leaves.lean`); Tau Ceti has a proof (prereq-survey), whose statement was not compared with ours |

**Glue, with Lean status.**
- Weight comparison. **Proved**: `weight_match`, and `weight_match_coh` for Pan's cohomological
  normalization `{n, n+k−1} = {0, −1}` ⇒ `k = 2`, `n = −1`, which matches rv-h-c8's `weights.py`.
- Determinant argument as group theory. **Proved**:
  - `finite_range_of_finiteIndex`: a homomorphism with finite image on a finite-index subgroup
    has finite image;
  - `finite_range_of_sq`: `ψ : G →* Eˣ` with `ψ²` of finite image has finite image;
  - `twist_finite`: from `r = εχψ²`, `r² = χ²` on a finite-index `H`, and `ε` of finite image, it
    concludes that `ψ` has finite image.

  These hold for any group `G` and any field `E`. For C8, `G = G_ℚ`, `H = G_F`, `E = \bar ℚ₅`, and
  the maps are `det r₅`, the nebentypus `ε_g`, `χ` and `ψ`.
- Duality `U^∨ ≅ U ⊗ det(U)^{−1}` for 2-dimensional `U`, which changes Pan's normalization into
  the Tate one (h-trust C8). Elementary linear algebra, provable in Mathlib; not written.
- "Finite image ⇒ Dirichlet character". Kronecker–Weber plus infinite Galois theory: the kernel
  of `ψ` is open, its fixed field is finite abelian, hence inside some `ℚ(ζ_m)`, and `ψ` factors
  through `(ℤ/m)ˣ`. It can be stated over Mathlib's `Field.absoluteGaloisGroup ℚ` with the Krull
  topology. Provable from `KroneckerWeber` with Mathlib's infinite Galois theory (SPECULATIVE:
  a few hundred lines); not written.
- Assembling these into C8 needs `r₅`, `ρ_g` and Hodge–Tate weights: blocked.

### 2.2 C10: one compatible system at 3 and 5 (N5 L776-795)

**Statement.** With `f` the newform of C9 and `C ⊇ K_f` a number field with fixed embeddings
`ι₃, ι₅` into `\bar ℚ₃`, `\bar ℚ₅`: `r₃ ≅ ρ_{f,ι₃}`. Here `ρ_{f,ι₃}` is the representation on the
`ι₃`-component of `V₃(A_f) ⊗ \bar ℚ₃`. So the conductor at 5 may be computed with `r₃`, and at
`p ≠ 5` with `r₅`.

**Proof.**
1. Take `p ∉ T ∪ {3, 5} ∪ supp(N)`, a place `v | p` of `L` and a Frobenius lift `σ` in the
   decomposition group. `L_v/ℚ_p` is unramified and `A` has good reduction at `v`. So `μ_σ`
   reduces (Néron mapping property), and `α_σ := \bar μ_σ ∘ F_rel` is an endomorphism (in
   `End⁰`) of `Ā_v`.
2. Under the specialization `V_ℓ(A) ≅ V_ℓ(Ā_v)` (good reduction), `ρ_ℓ(σ)` corresponds to
   `β(σ)⁻¹a_σ·α_σ`. Its characteristic polynomial lies in `C[x]` and does not depend on `ℓ`
   (Mumford §19 Thm 4 for `α_σ`; `a_σ, β(σ) ∈ C`).
3. `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`, so `tr r_ℓ(σ) = ½ tr ρ_ℓ(σ)`. Hence there is one `t_p ∈ C` with
   `tr r_ℓ(Frob_p) = ι_ℓ(t_p)` for `ℓ = 3, 5`.
4. `r₅ ≅ ρ_{f,ι₅}` (C9) and Eichler–Shimura give `ι₅(t_p) = ι₅(a_p(f))`, so `t_p = a_p(f)` in `C`.
   Hence `tr r₃(Frob_p) = ι₃(a_p(f)) = tr ρ_{f,ι₃}(Frob_p)` for all `p` outside a finite set.
5. Chebotarev makes these Frobenii dense. Both sides are semisimple: `r₃` is absolutely
   irreducible (C2 at `ℓ = 3`), and `V₃(A_f)` is semisimple by Faltings Satz 3. Brauer–Nesbitt in
   characteristic 0 then gives `r₃ ≅ ρ_{f,ι₃}`.

**Leaves.**

| Leaf | Statement used | Statable today? |
| --- | --- | --- |
| Néron mapping property (BLR 1990 §1.2 Def. 1, Prop. 8; UNVERIFIED) | `μ_σ` extends to the Néron models and reduces | no: no Néron models in Mathlib (Anthropic FLT has a special case, prereq-survey) |
| Serre–Tate 1968 / Néron–Ogg–Shafarevich (UNVERIFIED) | good reduction ⇒ `V_ℓ(A)` unramified and `V_ℓ(A) ≅ V_ℓ(Ā_v)` Frobenius-equivariantly | no |
| Mumford 1970 §19 Thm 4 (UNVERIFIED) | for `α ∈ End(B)`, `B` over any field and `ℓ ≠ char`, the characteristic polynomial of `α` on `V_ℓ(B)` is in `ℤ[x]` and independent of `ℓ` | no (no Tate modules of abelian varieties) |
| Faltings 1983 Satz 3 (ASTRA-READ) | `V_ℓ(B)` is semisimple | no |
| Eichler–Shimura (Shimura 1971 Thm 7.9; UNVERIFIED) | `tr ρ_{f,λ}(Frob_p) = a_p(f)` for `p ∤ Nℓ` | no |
| Chebotarev (Neukirch VII.13.4; UNVERIFIED) | Frobenius elements are dense in `G_ℚ`/its finite quotients | in Mathlib only for finite Galois extensions, not in the form "dense in `G_ℚ`"; Tau Ceti proves a density version (prereq-survey) |
| Brauer–Nesbitt, characteristic 0 (Curtis–Reiner (30.12)/(30.16); UNVERIFIED) | semisimple finite-dimensional representations with equal characters are equivalent | **yes**: `GlueAssembly.BrauerNesbittCharZero` (`Leaves.lean`); not proved in any library we found |

**Glue.**
- Step 3: `tr(r ⊕ r) = 2 tr r`, then division by 2 in characteristic 0. Elementary linear
  algebra.
- The "half its trace times a scalar" bookkeeping: elementary once the objects exist.
- Steps 4-5 (from equal traces on a dense set to an isomorphism, by continuity of traces): needs
  ℓ-adic representations of `G_ℚ` with Frobenius elements. **Blocked.**

N5's argument is complete as stated, with one point worth making explicit. The embedding at 3
must be extended from `C` to `C(K_f)` (N5: "Enlarge `C` … retaining the chosen embedding at
five"). Step 4 works for any extension of `ι₃`, because `t_p = a_p(f)` is an identity in `C`
(VERIFIED as reasoning).

### 2.3 E1: the isogeny `A × Z → J₁(N)` over `L'` (N5 L861-867)

**Statement.** With `A/L'` the QM surface (non-CM case) and `f` of level `N` with `r₅` a
constituent of `V₅(A_f)`: there are an abelian variety `Z/L'` and an `L'`-isogeny
`A × Z → J₁(N)_{L'}`. In particular `dim J₁(N) ≥ 2`.

**Proof.**
1. `V₅(A) ⊗ E ≅ r₅ ⊕ r₅` on `G_{L'}` (C1), and `r₅ ⊂ V₅(A_f) ⊗ E ⊂ V₅(J₁(N)) ⊗ E`. So
   `Hom_{G_{L'}}(V₅A ⊗ E, V₅J ⊗ E) ≠ 0`.
2. Invariants commute with extension of the coefficient field:
   `Hom_{G_{L'}}(V, W) ⊗ E = Hom_{G_{L'}}(V ⊗ E, W ⊗ E)` for finite-dimensional `V, W`. Hence
   `Hom_{G_{L'}}(V₅A, V₅J) ≠ 0`.
3. Faltings' Hom theorem gives `Hom_{L'}(A, J) ⊗ ℚ₅ ≅ Hom_{G_{L'}}(V₅A, V₅J)`, so there is a
   nonzero `L'`-homomorphism `A → J`.
4. `A` is absolutely simple: `End⁰(A_{\bar ℚ})` is the division algebra `B` (A9, non-CM), and a
   nontrivial decomposition up to isogeny would give zero divisors. So `A → J` has finite
   kernel, and its image `A'` is isogenous to `A`.
5. Poincaré reducibility gives `Z ⊂ J` with `A' × Z → J` an isogeny.

**Leaves.**
- Faltings 1983 Satz 4 / Korollar 1, the Hom theorem (ASTRA-READ, pp. 360-361). Not statable
  today (no Tate modules of abelian varieties).
- Poincaré reducibility (Mumford §19 Thm 1, UNVERIFIED). Not statable in Mathlib. Tau Ceti has
  abelian varieties and their Hom groups, but no complements (prereq-survey: "Poincaré
  reducibility … not found").

**Glue.**
- Step 2. **Proved** (`E1Lin.lean`): `baseChange_invariant_eq_zero` and
  `invariants_ne_bot_of_baseChange`. For a representation `W` of a group `G` over a field `F` and
  a field extension `E/F`: if `W^G = 0`, every `G`-invariant vector of `E ⊗_F W` is `0`. The proof
  takes coordinates in an `F`-basis of `E` (`finsuppScalarLeft`), which are natural in `W`; no
  finiteness is needed. To apply it to `Hom_{G_{L'}}(V₅A ⊗ E, V₅J ⊗ E)`, one still needs the
  identification `E ⊗ Hom_F(V, V') ≅ Hom_E(E ⊗ V, E ⊗ V')` for finite-dimensional `V`, which is
  standard Mathlib linear algebra; not written.
- Steps 1, 4 and 5 as stated need abelian varieties with Tate modules. **Blocked.**
- E1 is also where `g = dim J₁(N) ≥ 2` comes from. `GlueOutputs` assumes `2 ≤ g`. The bound
  `g ≤ N²` comes from E2: genus and Belyi degree are at most `[PSL₂(ℤ) : ±Γ₁(N)] ≤ N²`. The
  index bound is **proved** over Mathlib's `CongruenceSubgroup.Gamma1`: `index_Gamma1_le`
  (`E2Index.lean`) shows `[SL₂(ℤ) : Γ₁(N)] ≤ N²`, because the first column mod `N` separates
  left cosets. `[PSL₂(ℤ) : ±Γ₁(N)]` is at most this. The genus and Belyi bounds need modular
  curves as curves (absent).

### 2.4 E3: the explicit isogeny bound (N5 L878-892)

**Statement.** There is an `L'`-isogeny `φ : J₁(N)_{L'} → A × Z` with
`log deg φ ≤ 1024g³(64g² log(14g) + log d' + 2 log max(h_F(J), log d', 1))`, `g = dim J₁(N)`,
`d' = [L':ℚ]`.

**Leaf.** Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4 (ASTRA-READ), with
`κ(A) = ((14g)^{64g²}[k:ℚ]·max(h_F(A), log[k:ℚ], 1)²)^{1024g³}`, both directions, no
polarization hypothesis. It is applied to `J` and `A × Z`, which are isogenous by E1 (isogeny is
symmetric, and GR14 gives both directions). Not statable today: it needs the Faltings height,
isogeny degrees and abelian varieties over number fields (pkg-I5 §2).

**Glue (proved).** The arithmetic from `log κ` to N5's display is inside `transfer_numerics`.
N5 bounds the three logarithms by `5QM⁴`, `2QM⁴` and `19QM⁴`. The Lean proof uses the sharper
`4P`, `P` and `13P` (`P = QM⁴`; wk-h's bounds, re-proved here). The total is
`log deg φ ≤ 289792·Q¹⁶M²⁴ ≤ Q¹⁷M²⁴` (N5: `368640·Q¹⁶M²⁴`).

### 2.5 E4: height variation, additivity, lower bound (N5 L893-905)

**Statement.** `h_F(A) ≤ Q¹⁷M²⁴`, so `max(1, h_F(A)) ≤ max(1, C_cm, Q¹⁷)·M²⁴` in the non-CM
case. In the CM case `h_F(A) ≤ C_cm` (N5 L606-628).

**Leaves** (none statable today: Faltings height):
- Faltings 1983 Lemma 5, in the form `|h_F(A) − h_F(B)| ≤ ½ log deg φ`. That is a consequence of
  the lemma's exact formula (pkg-I5 §1); locator UNVERIFIED.
- Additivity `h_F(A × B) = h_F(A) + h_F(B)`. Uncited in N5; Faltings 1983 §1 or Deligne,
  Bourbaki 616 (UNVERIFIED).
- Bost's lower bound `h_F(Z) ≥ −(3/2)·dim Z`, as recorded in GR14 §9 (ASTRA-READ). The CMH
  version `≥ −log(π√2)·dim` is stronger, since `log(π√2) = 1.4913 < 3/2` (h-trust E4).

**Glue (proved, VERIFIED: compiled).**
- `transfer_of_level` (non-CM). Its hypotheses: `Q ≥ 10¹²`, `M ≥ 1`, `1 ≤ N ≤ QM²`,
  `h_F(J) ≤ 1.3·10⁷N¹²`, `2 ≤ g ≤ N²`, `1 ≤ d ≤ QM`, the GR14 bound,
  `h_A + h_Z ≤ h_F(J) + L/2` and `h_Z ≥ −(3/2)g`. Its conclusion: `h_A ≤ Q¹⁷M²⁴`.
- `cm_numerics` / `cm_branch_nat` (CM). Its hypotheses: `1 ≤ d ≤ D`, `h_E ≤ B_cm`,
  `L ≤ 8192(256 log 28 + log d + 2 log max(2h_E, log d, 1))` (GR14 with source `E²`, `g = 2`) and
  `h_A ≤ 2h_E + L/2`. Its conclusion: `h_A ≤ C_cm`. The proof uses `log 28 ≤ 4` and
  `log(2B_cm) ≤ 2 + 2D + 42000D²`, as in N5.
- `heightQ_heightD_ge`: `Q_D ≥ D ≥ 10¹²`, from `ten_pow_twelve_le_heightD` and `E₀ ≥ 1`.
- `max_one_hA_le`: both branches give `max(1, h_A) ≤ X(D)·M²⁴`.

### 2.6 F2: `h(Φ(z)) ≤ 40 h(z) + 22` (N5 L928-932)

**Statement (as proved).** For a number field `K` and `z ∈ K¹⁰`, write
`Φ(z) = 3779136(∏z_m)⁴/(∑z_m⁸)⁵ ∈ K` and let `h` be the absolute logarithmic Weil height. Then
`h(Φ(z)) ≤ 40·h([z]) + log 3779136 < 40·h([z]) + 16`. If moreover `Φ(z) = j ∈ ℚ`, then
`log max(|num j|, den j) ≤ 40·h_K(z)/[K:ℚ] + log 3779136` (`ratHeight_le_of_theta`).

**Leaves.** None. Mathlib's `Height` library suffices.

**Lean (VERIFIED: compiled, no `sorry`).**
- `logHeight_Phi_le` (`F2.lean`), over any field with `AdmissibleAbsValues`. The proof applies
  Mathlib's `logHeight_eval_le` to the two degree-40 forms (defined over `ℕ`, then mapped). It
  bounds `mulHeightBound ≤ 3779136^{n_K}`: at an archimedean place the `ℓ¹`-norm of the
  coefficients is at most the value at `1` (`3779136` and `10⁵`); at a nonarchimedean place the
  factor is `1`.
- `logHeight₁_algebraMap_rat` (`Ext.lean`). Write `q = a/b` in lowest terms. At each finite place
  `max(|a|_v, |b|_v) = 1`, since `sa + tb = 1`. At each infinite place it is `max(|a|, |b|)`, and
  `∑ mult = [K:ℚ]`.
- N5's constant `22` is generous: `log 3779136 = 15.145…` (`log_3779136_le`).

### 2.7 F3 normalization glue (N5 L934-947; adjacent to F2)

Proved (`F3Glue.lean`, `Transfer.lean`):
- the Euclidean projective height dominates the sup height (`mulHeight_le_mulHeightL2`; the
  `L²` height is defined in the file);
- the six zero odd theta constants do not change the height;
- coordinatewise roots of unity do not change it;
- the arithmetic `X_D ≤ 3X`, `log(X_D + 2) ≤ 2X_D`, `C₂ ≤ 1000·2⁴·243`, giving
  `h(z) ≤ 10⁴·2²⁴·X` (`pazuki_numerics`; pkg-I5's `f3_numerics` proves the same independently).

Whether `mulHeightL2` is exactly Pazuki's `h_Θ` normalization is UNVERIFIED (Pazuki 2012 not
readable here). Since the comparison goes in the safe direction (sup ≤ `L²`), any normalization
whose archimedean factor dominates the sup norm works.

### 2.8 Assembly of the constants into `H₆(D)` (N5 L957-964)

Proved: `jHeightBound_of_glueOutputs`, then JHeight's `sixContactMin_of_jHeightBound` (copied as
`sixContactMinAt_of_jHeightBound`). The chain:
`h(J(u)) ≤ 40h(z) + 16 ≤ 40·10⁴·2²⁴·X·M²⁴ + 16 ≤ (40·10⁴·2²⁴ + 22)·X·M²⁴`, using `X·M²⁴ ≥ 1`.
F4 (`12h(u) ≤ h(J(u)) + 450`) then gives `h(u) ≤ 2·10¹³·X·M²⁴ = H₆(D)·M²⁴`.

## 3. Leaf list for the cluster

| # | Leaf (published) | Used in | Statable in Lean today | In a Lean library |
| --- | --- | --- | --- | --- |
| 1 | Faltings 1983 Satz 4 / Kor. 1 (Hom theorem) | E1 | no (Tate modules) | no |
| 2 | Faltings 1983 Satz 3 (semisimplicity) | C10 | no | no |
| 3 | Poincaré reducibility (Mumford §19 Thm 1) | E1 | no | no |
| 4 | Gaudron–Rémond 2014 Thm 1.4 | E3, CM | no (Faltings height) | no |
| 5 | Faltings 1983 Lemma 5 (inequality form) + additivity | E4, CM | no | no |
| 6 | Bost (GR14 §9) | E4 | no | no |
| 7 | Javanpeykar 2014 Thm 1.1.1 at `X₁(N)` | E2 (consumed by E4's arithmetic) | no | no |
| 8 | (HT) eigenform Hodge–Tate weights (Saito / Scholl+Scholze / Kato) | C8 | no | no |
| 9 | Deligne–Serre 1974 Thm 4.1 | C8 | no | no |
| 10 | Weil pairing Galois-equivariance | C8 | no | no |
| 11 | Kronecker–Weber | C8 | **yes** (`KroneckerWeber`) | Tau Ceti (proved) |
| 12 | Néron mapping property (BLR §1.2) | C10 | no | special case (Anthropic FLT) |
| 13 | Serre–Tate / NOS for abelian varieties | C10 | no | elliptic curves only (Tau Ceti) |
| 14 | Mumford §19 Thm 4 | C10 | no | no |
| 15 | Eichler–Shimura (Shimura 1971 Thm 7.9) | C10 (and C9) | no | no |
| 16 | Chebotarev | C10 | partly (finite extensions) | Tau Ceti (proved) |
| 17 | Brauer–Nesbitt, characteristic 0 | C10 (and C9) | **yes** (`BrauerNesbittCharZero`) | no |
| 18 | Pazuki 2012 Cor. 1.3(2) | F3 (consumed by the assembly) | no; special cases in pkg-I5 | no |

Rows 1-2, 5 and 12-15 are shared with other packages (I2, I3, I4). Rows 4-7 and 18 are pkg-I5's.

## 4. Glue list for the cluster, with Lean status

| Glue | Step | Status |
| --- | --- | --- |
| Hodge–Tate weight comparison (both normalizations) | C8 | **proved** (`weight_match`, `weight_match_coh`) |
| Determinant argument: `ψ` of finite image | C8 | **proved** as group theory (`twist_finite`) |
| `U^∨ ≅ U ⊗ det⁻¹` (dimension 2) | C8 | provable today; not written |
| finite-image character of `G_ℚ` is Dirichlet (from Kronecker–Weber) | C8 | statable and provable over Mathlib's infinite Galois theory; not written |
| trace bookkeeping `tr(r ⊕ r) = 2 tr r`, scalars | C10 | elementary; not written |
| equal traces on dense Frobenii ⇒ isomorphic | C10 | blocked (ℓ-adic representations of `G_ℚ`) |
| invariants commute with extension of coefficients | E1 | **proved** (`baseChange_invariant_eq_zero`); the `Hom`-space identification is not written |
| simplicity + Hom theorem + Poincaré ⇒ isogeny | E1 | blocked (abelian varieties) |
| `[SL₂(ℤ) : Γ₁(N)] ≤ N²` | E2 | **proved** (`index_Gamma1_le`) |
| genus, Belyi degree `≤` index | E2 | blocked (modular curves) |
| E3-E4 arithmetic, from the level | E3, E4 | **proved** (`transfer_numerics`, `transfer_of_level`) |
| CM arithmetic | CM | **proved** (`cm_numerics`, `cm_branch_nat`) |
| F2 on genuine Weil heights | F2 | **proved** (`logHeight_Phi_le`) |
| height of a rational number in a number field | F2/F4 | **proved** (`logHeight₁_algebraMap_rat`) |
| F3 normalizations (`L²` vs sup, zeros, roots of unity) and arithmetic | F3 | **proved** |
| final constant and F4 | F4 | **proved** (assembly; F4 is JHeight's) |
| whole Arakelov assembly `GlueOutputs S → SixContactMinAt S` | E-F | **proved** |

## 5. Recommendations

1. Adopt the assembly under `ZInQKernel/Hypotheses/` (a task allowed to edit it). Import
   `JHeight`, drop `F4Copy`, and state `sixContactMin_of_glueOutputs : GlueOutputs Mult.S_mul →
   SixContactMin`. Keep the docstring's warning that `GlueOutputs` is a numerical shadow, not a
   leaf.
2. For the crowdsourcing announcement, the cluster contributes:
   - two leaves that can be stated now, `KroneckerWeber` (already proved in Tau Ceti; a port)
     and `BrauerNesbittCharZero`;
   - one small, self-contained Mathlib-level task: the "finite-image character is Dirichlet"
     lemma (C8). Two others are done here: the index of `Γ₁(N)` (E2), and invariants under
     field extension (E1).

   Everything else in the cluster waits on the object layer (abelian varieties with Tate
   modules and Faltings heights; ℓ-adic representations of `G_ℚ`).
3. When pkg-I5's object layer exists, instantiate `GlueOutputs`. Each conjunct of §1.2 becomes
   the conclusion of one leaf applied to `A`, `Z` and `J₁(N)`, and the assembly theorem is used
   unchanged.

## Files

- `scratch/glue-assembly/F2.lean`: F2 on Mathlib heights.
- `scratch/glue-assembly/Ext.lean`: the height of rationals in number fields.
- `scratch/glue-assembly/Transfer.lean`: the E2-E4, CM and F3 arithmetic.
- `scratch/glue-assembly/F4Copy.lean`: JHeight's F4, copied.
- `scratch/glue-assembly/Assembly.lean`: `GlueOutputs` and the assembly.
- `scratch/glue-assembly/build.sh`: concatenates the five files above into
  `scratch/glue-assembly/GlueAssembly.lean`, the checked whole.
- `scratch/glue-assembly/C8.lean`: C8 glue.
- `scratch/glue-assembly/F3Glue.lean`: F3 normalizations.
- `scratch/glue-assembly/Leaves.lean`: the two statable leaves.
- `scratch/glue-assembly/E2Index.lean`: `[SL₂(ℤ) : Γ₁(N)] ≤ N²`.
- `scratch/glue-assembly/E1Lin.lean`: invariants and extension of scalars.
- `scratch/glue-assembly/log.md`: results log.
