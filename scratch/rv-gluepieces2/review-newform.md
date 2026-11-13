# rv-gluepieces2: adversarial review of the newform/conductor fields of `GluePieces2`

Reviewer task, 2026-11-13. File under review: `scratch/g0-assemble/G0Assemble.lean` (42 049 lines;
`structure GluePieces2` L41938-41998). I did not run Lean (the slot was held by another process).
Markers: **VERIFIED** means read or diffed here. **STANDARD** means published, with a reference.
**SPECULATIVE** means my own judgement. Theorem numbers quoted from memory are **UNVERIFIED** (no
network access).

| field | class | verdict |
|---|---|---|
| `dirichletOfFinite : G0ModNewform.DirichletOfFinite` (L40845) | GLUE | **TRUE** |
| `carayolR17 : LadicCond.CarayolR17'` (L38453) | LEAF | **TRUE**; a standard corollary of Carayol's Théorème (A), not stronger in content (see the labelling remark) |
| `swanIndependent` (L38410) | GLUE | **TRUE** (proof exists over byte-identical definitions) |
| `swanIntegral` (L38481) | GLUE | **TRUE** (same) |
| `adaptedExists` (L38424) | GLUE | **TRUE** (same) |
| `linkedTateData : G0AssembleMod.LinkedTateData` (L41654) | GLUE (new) | **TRUE as a form; truth conditional on N5 L719-852**. No refutation found: the quantifier structure is sound (details in §4). |

---

## 1. `G0ModNewform.DirichletOfFinite` (L40845-40852): TRUE

**Statement.** Take a prime `ℓ`, a continuous character `ψ : G_ℚ → ℚ̄_ℓ^×` with finite image, and
embeddings `ιC`, `ιL`. Then there exist `m > 0`, a Dirichlet character `ψD mod m` and a finite set
`S` such that for every prime `p ∉ S` some `β ∈ ℚ̄` satisfies `ιC β = ψD(p)` and `ψ(τ) = ιL β` at
every arithmetic Frobenius `τ` above `p`.

**Unfolding (VERIFIED).**
- `GaloisChar` (L3991) is a continuous `G_ℚ →* (PadicAlgCl ℓ)ˣ`.
- `IsArithFrob` (L3981) and `LiesOver` (L3978) are the genuine notions: decomposition group plus
  `x ↦ x^p` on the residue ring; `p` is a non-unit of `v`.
- In `namespace G0ModNewform`, `Qbar` and `GQ` resolve to `PkgI4`. `LeafModCurves` is opened with
  these names hidden (L40136-40142), so there is no clash.

**Argument (STANDARD).**
1. Finite image plus continuity gives an open kernel. So `ψ` factors through a finite abelian
   `Gal(F/ℚ)`, and Kronecker–Weber puts `F` inside `ℚ(ζ_m)`.
2. The values of `ψ` are roots of unity. `ιL(ℚ̄)` is the relative algebraic closure of `ℚ` in
   `ℚ̄_ℓ`, so it contains them.
3. Set `ψ' = ιL⁻¹ ∘ ψ ∘ Art` and `ψD = ιC ∘ ψ'`. Take `β = ψ'(p)` and `S = {p ∣ m}`.

I found no edge case: `p ∣ m` goes into `S`, and the value at an unramified Frobenius does not
depend on the choice of `τ`.

**Proof transfer (VERIFIED).**
- The block L40845-40852 is identical to `scratch/x1-dirichlet/Dirichlet.lean` L37-44
  (`diff` is empty).
- That file imports `ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`, which imports
  `Conductor/LadicCond.lean`. Its Part A (`PkgI4`: `Qbar`, `GQ`, `LiesOver`, `IsArithFrob`,
  `GaloisChar`, ...) is block-for-block identical to G0Assemble's `PkgI4` at L3971-4047 and
  L4469-4514. I checked 24 definitions with a Python block comparison; all match.
- So x1-dirichlet's `dirichletOfFinite_of_kroneckerWeberCyclic` transfers. Its compile log is
  reported in the docs; I did not recompile it.

## 2. `LadicCond.CarayolR17'` (L38453-38457): TRUE, not stronger than the published mathematics

**Statement.** Let `f ∈ S₂(Γ₁(N))` with `IsNewform f χ`, let `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` be semisimple
with `ρ.AttachedTo ιC ιL f`, and let `p ≠ ℓ`. Then `condExp (ρ|G_{ℚ_p}) = v_p(N)`.

**Unfolding (VERIFIED, L4469-4520 and L38177-38300).**
- `IsNewform` means: q-expansion Hecke relations for all `m, n`, including `U_p` for `p ∣ N`
  (`χ(d) = 0` there); `a₁ = 1`; nebentypus `χ`; and not in the span of the oldforms `f(dτ)`.
  - For a normalized eigenform of all `T_n`, "not in oldSpace" is equivalent to being a newform.
    This uses strong multiplicity one: old eigensystems span old generalized eigenspaces
    (Li 1975, UNVERIFIED locator). So `IsNewform` does not admit extra forms.
- `AttachedTo` gives traces of arithmetic Frobenius `= ιL(α)` with `ιC α = a_p`, for `p ∤ Nℓ`.
  This is the dual of Deligne's normalization.
- `IsSemisimple` (L4024) is genuine.
- `restrictLocal` composes with Mathlib's `absoluteGaloisGroup.map` (a genuine decomposition
  group).
- `condExp = codim V^{I} + swan` with `inertiaSet` equal to `I_p` and `wildSet` equal to `P_p`.

**Is it stronger than the published theorem?** Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A)
(UNVERIFIED locator) is local–global compatibility for Deligne's `ρ_{f,λ}` at `p ≠ ℓ`. The Lean
form adds four standard steps, each of which preserves truth:
1. Chebotarev density plus Brauer–Nesbitt: a semisimple continuous `ρ` with these traces is
   `≅ ρ_{f,λ}^∨ ⊗ ℚ̄_ℓ`. Continuity and Baire put the image in `GL₂(E)` with `[E:ℚ_ℓ] < ∞`.
2. `a(ρ^∨) = a(ρ)`. Swan is dual-invariant, and `dim V^I = dim V_I` by Grothendieck's monodromy
   theorem.
3. The Serre–Tate conductor equals the WD conductor, since `V^{ρ(I)} = (ker N)^{I}`. It is also
   insensitive to Frobenius semisimplification.
4. Casselman 1973: `a(π_p) = v_p(N)` for newforms.

The quantifiers (every `ℓ`, including 2; every `p ≠ ℓ`, including `p ∣ N`) match the locator
audit's reading (docs/research/locators.md L71, rv-loc-leaves.md §(f)).

**Verdict.** TRUE, and no stronger than the published mathematics. The quantifiers over
`ιC, ιL, χ` cost nothing.
- **Labelling remark (not a defect of truth).** Strictly, this is a *corollary* of Théorème (A)
  together with Casselman, not Carayol's printed sentence. The docstring L38440-38452 says so
  ("with `a(π_p) = v_p(N)` ... Casselman"). g0-mod-newform.md L224 lists the extra steps. I would
  label it "LEAF (published corollary: Carayol (A) + Casselman + Chebotarev/BN)".
- **Copy check (VERIFIED).** L38177-38762 is byte-identical to the kernel file
  `ZInQKernel/HDecomp/Conductor/LadicCond.lean` L180-765 (`diff` is empty). Its dependencies
  (`CF`, `coeff`, `IsNewform`, `AttachedTo`, `GaloisRep`, `restrictLocal`, `GQp`) are identical
  to the kernel's Part A (block diff).

## 3. `SwanIndependent` (L38410), `SwanIntegral` (L38481), `AdaptedExists` (L38424): TRUE

**Statements.**
- `SwanIndependent` (per `p`): for every field `k`, every homomorphism `ρ : G_{ℚ_p} →* GL_n(k)`
  (continuity not required) and any two adapted `L, L'`, `swanAt L ρ = swanAt L' ρ`.
- `SwanIntegral`: for continuous `ρ` into `GL_n(ℚ̄_ℓ)` with `p ≠ ℓ` and adapted `L`,
  `swanAt L ρ = ∫_{(0,∞)} codim V^{upperAbs p u} du`.
- `AdaptedExists` (per `p`): every continuous `ρ` into `GL_n(ℚ̄_ℓ)` with `ℓ ≠ p` has an adapted
  `L`, meaning `L/ℚ_p` is finite Galois and `ρ` is trivial on `P_p ∩ G_L`.

**Refutation attempts.**
- *`SwanIndependent` for arbitrary `k` or non-continuous `ρ`.*
  - Adaptedness already factors `ρ|_{P}` through `P/(P∩G_L) = G_1(L/ℚ_p)`.
  - `swanAt L` only sees `ρ` on `ramSet L (i+1) ∩ wildSet`, whose image is `G_{i+1}(L)`.
  - Comparing `L ⊆ LL'` reduces to Herbrand's theorem for upper groups `v > 0`, together with
    `G^v ⊆ G_1`.
  - The change of variables `Σ_{i≥1} g_i c_i / g_0 = ∫ codim V^{G^u}` does not depend on the
    characteristic.
  - Result: TRUE (Serre, *Corps locaux* IV §3 and VI §2, numbering UNVERIFIED).
- *`SwanIntegral`.*
  - The integrand is a step function with compact support: it vanishes for `u > u_max(L)`
    because `upperAbs p u ⊆ P ∩ G_L` there.
  - So it is integrable, and Bochner's "0 if not integrable" convention never applies.
  - `upperAbs p u ⊆ wildSet` for `u > 0`.
- *`AdaptedExists`.*
  - `ρ(G_{ℚ_p}) ⊆ GL_n(𝓞_E)` (Baire plus compactness).
  - The kernel of reduction is pro-`ℓ` and `P_p` is pro-`p`, so `ρ(P_p)` is finite and the kernel
    is open in `P_p`.
  - Result: TRUE.
- I checked the definitions against Serre's (VERIFIED by reading L38188-38300):
  - `ramSet` is `i_G(σ) ≥ i+1`;
  - `ramSetR` is `G_⌈t⌉`;
  - `phiAt` is `∫₀ᵘ g_t/g_0`;
  - `upperSet` is `G_{ψ(v)}`;
  - `upperAbs` is the intersection over all finite Galois `L`.

**Proof transfer (VERIFIED by reading; not recompiled).**
- `scratch/swan/final_part.lean` proves exactly `LadicCond.SwanIndependent (p := p)`,
  `LadicCond.SwanIntegral` and `LadicCond.AdaptedExists (p := p)`.
- The proof imports the kernel `LadicCond`, whose Parts A-D are byte-identical to G0Assemble's
  copies (§2). The kernel file was last changed 2026-11-12, before swan's commit `efee8156`
  (2026-11-13).
- `grep sorry` finds nothing in `Swan.lean`, `Bridge.lean`, `final_part.lean` or `All.lean`.
- The compile logs `*.out` named in docs/research/swan.md are not in the tree.

---

## 4. `G0AssembleMod.LinkedTateData` (L41654-41692): TRUE as a form, truth conditional

### 4.1 Full unfolding (VERIFIED)

The statement has this shape:

```
∀ Y Φ π u P, FibreCtx Y Φ π u P →                                   (L39149: R1, R2, u ∉ 𝒞, P over J(u))
∀ L A ε N χ β L' hLL', G7Data u P L A ε N χ β L' hLL' →             (L39677)
∃ (Tm₅ c₅ ε₅ a₅ β₅ u₅) (Tm₃ c₃ ε₃ a₃ β₃ u₃),
  G7Out A' 5 … ∧ G7Out A' 3 … ∧                                    (G0Galois.G7Out, L37299; A' = A_{L'})
  ∀ r₅ r₃, G8Out A' 5 (rho Tm₅ a₅ β₅) r₅ → G8Out A' 3 (rho Tm₃ a₃ β₃) r₃ →   (L37325)
   ∀ i ιC ι5, ∃ ι3, G14TraceCompat ⟨i,ιC,ι5,ι3,r₅,r₃⟩ ∧ G15RamWild ⟨…⟩      (L40310, L41625)
```

- **Name resolution.**
  - `G0Galois.G7Out` resolves to root `G0Galois` (L37299), not to the copy
    `G0ModField.GaloisCopy.G7Out` at L39953. The namespaces are `HSyn.G0AssembleMod` with
    `open G0ModField`; there is no `G0ModField.G0Galois`.
  - `PkgI4.GaloisRep` is written fully qualified. The shadowing `HSyn.GaloisRep` (L21365) is
    therefore avoided.
- **`G7Out`** asks for:
  - `dim A' = 2` and `rank_ℤ End_{L'}(A') = 4`;
  - the cocycle relations for `Tm, c, a, β, ε`;
  - `Tm = tate`, `a = β = 1` on `G_{L'}`;
  - matrix units commuting with every `Tm g`;
  - continuity of `ρ = β⁻¹ a Tm` (`GlueDescent.rho`, L7656).
- **`G8Out`** asks for `ρ = tate` on `G_{L'}`, an `e` with `e ρ(g) = (r(g) ⊕ r(g)) e` for all
  `g ∈ G_ℚ`, and Burnside generation by `r(G_{L'})`.
- **`G15RamWild D`** means `LocalRamWild p r₅` for `p ≠ 5` and `LocalRamWild 5 r₃`. Here:
  - `LocalRamWild`, case `p ≤ D`: `r(G^t_{ℚ_p}) = 1` for every `t > U₀ = 4(D·G₀)²` (L40636);
  - `LocalRamWild`, case `p > D`: `r(P_p) = 1`.
  - `D = heightD = F₀·3^{256F₀⁴}`, which is at least `10¹²`. So `p = 2, 3, 5` all fall under
    clause (i), and every `p > D` is odd and at least 7.
- **What the data are tied to.** The data concern Glazer's actual fibre:
  - `G7Data` has `IsQMModel L A P`, so `A` is the base change of a `QML3 K` object (L14393: QM by
    `𝒪` over `K`). Hence `End_K(A) ⊇ 𝒪`.
  - `IsModelOver L' A' P` holds.
  - `DescentDatum` (L39198) requires `m_σ` to commute with every `L`-endomorphism.

### 4.2 The tests asked for

**(a) Is `∀ r₅ r₃` too loose? No (VERIFIED as an argument).**
- `G8Out` fixes `r` up to isomorphism, given the existentially chosen data.
- `r ⊕ r ≅ ρ ≅ r' ⊕ r'` as `G_ℚ`-representations, and both `r, r'` are absolutely irreducible
  (Burnside on `G_{L'}`; compare `hirr` in `g12Spec_of_galois`, L40930). So
  `Hom(r', r) ≠ 0`, which gives `r' ≅ r`.
- `G14TraceCompat` uses only Frobenius traces, and `G15RamWild` asks only `r(σ) = 1` on subsets
  of `G_{ℚ_p}`. Both are invariant under conjugation.
- So the `∀` ranges over a single isomorphism class.
- The twist attack of g14-trace F2 (`a ↦ χa`) changes `r` only through the *existential* choice.
  The prover picks the untwisted data.

**(b) Are `ι₅` and `ι₃` tied to a common `γ`? Yes, and the order of quantifiers works.**
- The prover takes G7Data's own algebraic scalars `a_σ = deg(μ_σ)^{-1/4}`, `β_σ` (with `β² = χ`)
  and `c ∈ ℚ^×`. It maps them by fixed `τ₅ : ℚ̄ → ℚ̄₅` and `τ₃ : ℚ̄ → ℚ̄₃`. This is
  g14-trace's `TateBridge35`; F1 is satisfied because the existential is joint.
- The trace link gives `tr r_ℓ(Frob) = τ_ℓ(x)` with one `x ∈ ℚ̄`: g14-trace §4, proved from T7
  through the endomorphism `μ̄_σ∘F` of the reduction.
- For an arbitrary `ι5`, write `ι5 = τ₅∘g` with `g ∈ Aut(ℚ̄)` (both images are the relative
  algebraic closure of `ℚ`). Put `ι3 := τ₃∘g`. Then `tr r₅ = ι5 c` forces `x = g c`, so
  `tr r₃ = ι3 c`.
- `S` is chosen after `ι3` and may contain `T(u) ∪ {3,5}`.

**(c) Can an admissible `G7Data` other than Glazer's (exotic `L`, `L'`, `K`, `β`, `χ`) break
`G15RamWild`?** No, if Glazer's own `r⁰_ℓ` satisfies it (SPECULATIVE but checked step by step):
- *The projective representation is intrinsic.*
  - NoCM (the fibre is not a CM point) gives `End⁰_{ℚ̄}(A) = B`, and `End_K(A) ⊇ 𝒪` with
    `K ⊆ L`. So `m_σ` commutes with all of `End_{ℚ̄}(A)`.
  - B-equivariant isogenies `^σA → A` are therefore unique up to `ℚ^×`.
  - Two QM models differ by a twist with values in `Aut_𝒪 = {±1}`.
  - Hence any admissible data give `r_ℓ ≅ r⁰_ℓ ⊗ μ` for a character `μ` of `G_ℚ`.
- *The determinant pins `μ`.*
  - The relations force `σ ↦ a_σ⁴ deg μ_σ` to be a positive finite-order character, hence
    trivial.
  - Polarization compatibility of `μ_σ` gives `det m_σ = deg μ_σ · cyc²`.
  - So `det ρ = β⁻⁴cyc² = χ⁻²cyc²`, and `μ² = χ₀χ⁻¹·(quadratic)`.
  - `χ` and `χ₀` have level `chiLevel` (`lev p = p` or 4). So `μ` is tame at every odd `p`, and
    has conductor dividing 16 at 2 (upper break at most 3, far below `U₀`).
  - Twisting by such a `μ` preserves both clauses: `P_p` and `G^t` for `t > 0` are pro-`p`, and
    `μ` kills them at odd `p`.
- *Why it matters.* An exotic `L ⊇ L₀·F` with `F` wildly ramified at some `p > D` in
  `supp M(u)` is admissible by the degree bound `[L':ℚ] ≤ Q_D·M(u)`. It does not change `r`
  beyond such a `μ`.
- `G7Out`'s `rank End = 4` and the matrix units both need NoCM. This is the same QM-pin as
  `fibreComTrivial` and `ModelG3G6`'s `G6Out`, so it is not a new assumption.

**(d) The conductor-type clauses at `p = 2, 3, 5` and at `p ∈ T(u)`.**
- `LinkedTateData` contains no conductor bound, only (i) and (ii). Clause (iii) comes from G11
  (`g15RamG_of_wild`, L41633).
- (ii) at `p > D`, including `p ∈ supp M(u)`:
  - QM surfaces have potentially good reduction, and for `p > 2g+1 = 5` wild inertia acts
    trivially on `V_ℓ` (Serre–Tate 1968, UNVERIFIED numbering).
  - So `r(P_p ∩ G_{L'}) = 1`. The rest is the twist analysis in (c).
- (i) at `p = 2, 3, 5`: `r(G^t) = 1` for `t > U₀` follows if `r|I_p` trivializes over some `F`
  with `e(F) ≤ (DG₀)!`. Upper breaks grow like `O(log e)`, far below `U₀`.
  - This is N5 L819-844, with D1-D4 in the kernel as reported in g15-ram.md §135-176.
  - The p = 5 case uses `r₃`, so `ℓ ≠ p` everywhere.

### 4.3 Verdict and residual risk

- **TRUE as a form.** The `∀` over `r` covers one isomorphism class. `ι₃` comes after `ι₅`. The
  data are tied to the fibre `P`. Exotic `G7Data` change `r` only by harmless twists.
- **Truth is conditional** on Glazer's local analysis (N5 L719-852) for his own descent, and on
  the trace link and `TateBridge35` (g14-trace) at both primes.
- The weakest point I see is the determinant step in (c). It uses polarization compatibility of
  `μ_σ` (`μ_σ^*λ = d_σ·^σλ`, with `λ` fixed by Lemma P's `μ`). This is standard for QM surfaces
  with Rosati type fixed, but it is not formalized anywhere I could find (SPECULATIVE).
  - If it failed, `μ` would still be a character of `Gal(L'L₀'/ℚ)`. Clause (ii) could then fail
    at some `p > D` where an exotic `L'` is wild, so a future proof must establish this step.
- **Cosmetic.** The docstring of the `linkedTateData` field (L41993) says `G15RamG`; the field
  actually uses `G15RamWild` (clauses (i)-(ii) only).

### 4.4 Lean sanity check (optional; not run)

This check confirms the claim in (a) that `G15RamWild` depends only on `r₅` and `r₃` (and not on
`i`, `ιC`, `ι5`, `ι3`). Append it after G0Assemble.lean's content:

```lean
example {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D D' : G0ModNewform.ModData L A) (h5 : D.r5 = D'.r5) (h3 : D.r3 = D'.r3) :
    HSyn.G0AssembleMod.G15RamWild D ↔ HSyn.G0AssembleMod.G15RamWild D' := by
  unfold HSyn.G0AssembleMod.G15RamWild; rw [h5, h3]
```

## 5. Summary of evidence

- **VERIFIED.**
  - `diff` of LadicCond Parts B-D (kernel L180-765 against G0Assemble L38177-38762): identical.
  - Block diff of 24 `PkgI4` Part A definitions: identical.
  - `DirichletOfFinite` against x1-dirichlet's proved statement: identical.
  - swan's `final_part.lean` targets the kernel Props exactly; no `sorry`.
  - Name resolution of `G0Galois.G7Out` and `PkgI4.GaloisRep` in `LinkedTateData`.
  - `G8Out` determines `r` up to isomorphism.
- **STANDARD.** Kronecker–Weber; Carayol (A), Casselman, Chebotarev/Brauer–Nesbitt, Grothendieck
  monodromy; Herbrand and Serre CL IV-VI; Serre–Tate (wild inertia for `p > 2g+1`).
- **SPECULATIVE.** Truth of `LinkedTateData` on Glazer's construction, in particular the
  determinant/polarization step in §4.2(c).
