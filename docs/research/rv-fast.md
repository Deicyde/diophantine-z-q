# rv-fast: adversarial review of curve-infra, lg-kerwild, unram-roots, afr-absfrob, ring-class

Task rv-fast, 2026-11-13. Base `wip/rv-fast` (b7cdba8e), merged with origin/wip/curve-infra, lg-kerwild
(both already in the base), unram-roots (b066d686) and afr-absfrob (2ffcf322). Check files:
`scratch/rv-fast/` (results log `log.md`). This is model review only; no human has checked it.

Marks: **VERIFIED** = compiled, computed, or read in a file here. **STANDARD** = published, with a
reference. **SPECULATIVE** = my judgement. Theorem numbers recalled without a source are
**UNVERIFIED** (no network).

## 0. Verdicts (most serious first)

| result | verdict | one line |
|---|---|---|
| lg-kerwild | **CONCERN** (core results SOUND) | `TateBridgeK`, `KerWild`, `DescentPts` are right; but the every-`ℓ` LocalGlue theorem keeps a hypothesis `G7Clauses β' ε' L` about data that `TateBridgeK` hides behind `∃`, so no consumer can discharge it; and the committed file can no longer be rebuilt from the current local-glue source |
| ring-class | **SOUND** (citation note) | `hprimeNormal`, `iInH4`, `ringClassFieldD_tyz` have exactly cm-points' types; the fields are non-degenerate; the new leaf `CM.CMFieldOfDefinition ringClassFieldD` is true, but it is a consequence of Shimura's reciprocity law, not the printed statement of Gross 1984 §3 |
| unram-roots | **SOUND** | unconditional theorem; statement byte-identical to local-glue's; no hidden leaf |
| afr-absfrob | **SOUND** | `AbsFrob` proved from Mathlib with a genuine Frobenius; `FExtendGen` from I2-NMP only; statements byte-identical |
| curve-infra | **SOUND** | unconditional; `ffAlgebra` is `fnFieldAlgebra` by `rfl`; the statements give the right values on `K[X]` and `K` |

(Section 6 records the compile runs and axioms; see there for anything left unchecked.)

## 1. lg-kerwild — CONCERN (core results SOUND)

**What was claimed.** `scratch/lg-kerwild/KerWild.lean`:
- `UnramTate.tateBridgeK_of_tateModuleFree : PkgI3.TateModuleFree → LGKerWild.TateBridgeK`;
- `LGKerWild.descentPts_of_g7` (`DescentPts (A_{L'}) L` for G7Data's model `A/L`);
- `LGKerWild.localGlue_of_tateBridge35` (ℓ = 5, 3) and `exists_localGlue_of_tateModuleFree` (every ℓ).

**(a) Compile.** See §6: KW-RESULT.

**(b, c) Statements: what is right.**
- `TateBridgeK` is g0-mod-field's `TateBridge` with one more conjunct, `KerWild L' β' L`, in the
  output (VERIFIED: read l.8311-8329; `tateBridge_of_K : TateBridgeK → TateBridge` compiles).
- `KerWild` is a real constraint, not a tautology. Unfolded, it says: every `g ∈ G_L` with
  `β'(g) = 1` lies in `G_{L'}` (my check: `KerWild … ↔ ∀ g, g ∈ G_L → β' g = 1 → g ∈ L'.fixingSubgroup`,
  by `resQ_range`). For the constant `β' = 1` it forces `G_L ≤ G_{L'}`, i.e. `L' ≤ L` (VERIFIED, check
  file).
- The proof of `KerWild` for unram-tate's witness (`β'(g) = γ(hgh⁻¹)`) uses G7Data's clause 9,
  `G_{L'} = G_L ∩ ker β`. The argument (§3 of the report) is correct, and Lean checks it.
- `DescentPts`, `KerWild`, `LocalGlue`, `G7Clauses` and `UnramRoots` in `KerWild.lean` are
  textually local-glue's (VERIFIED: the definitions are outside the diff against the current source).
- `descentPts_of_g7` is right and cheap. It takes the model `A₀ := A` (or its conjugate) and the
  base change of points. `DescentPts` asks only for a Galois-compatible group isomorphism, so it
  holds for a base change by construction.
- I3.M0 (`PkgI3.TateModuleFree`: `T_ℓ A` free of rank `2 dim A` for `ℓ ≠ char k`) is a pre-existing kernel leaf and Mumford's
  theorem (STANDARD; Mumford, *Abelian varieties*, §4 and §18; section numbers UNVERIFIED). It is not stronger.

**The concern: the every-`ℓ` LocalGlue result is inert.**
`exists_localGlue_of_tateModuleFree` concludes
`∃ Tm c ε' a β' uu, G7Out … ∧ ∀ p ≠ ℓ, G7Clauses β' ε' L → LocalGlue p Tm a β' L`.
1. `G7Clauses β' ε' L` is a property of the data hidden behind `∃`. `TateBridgeK`'s output says
   nothing about local constancy of `β'`, `β'² = ι ∘ χ`, `ε' = 1` on `G_L × G_L`, or
   `[L:ℚ] ≤ D`. So no consumer can discharge it from `TateBridgeK`.
2. For the witness that proves `TateBridgeK`, the hypothesis is false whenever the descent
   datum is non-trivial. VERIFIED by reading and by two lemmas compiled in
   `scratch/rv-fast/KerWildCheck.lean`:
   - `tateBridgeK_of_piecesK` (like unram-tate's `tateBridge_of_pieces`) returns
     `⟨Tm, c', c', a', β', uu, …⟩` with `a' = fun _ => 1` and `ε' = c' = n/d`. Here `n/d` is the
     rational cocycle `m_σ m_τ = (n/d) m_{στ}` of G7Data's descent datum, conjugated by `h`
     (KerWild.lean l.6669-6672, 6705, 8729).
   - `rvf_g7Clauses_eps_sq` (new, compiled): `G7Clauses β ε L → ∀ g k, ε g k ^ 2 = 1`. The reason
     is that `β² = ι ∘ galChar χ` is a homomorphism, so `(∂β)² = 1`.
   - `rvf_c_sq_of_a_one` (new, compiled): `G7Out … c ε a β u`, `a ≡ 1` and `G7Clauses β ε L`
     together give `c g k ^ 2 = 1` for all `g, k`.
   - `DescentDatum` (KerWild.lean l.5486-5526) has `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}`, with `ε` a sign
     cocycle and `a > 0` inflated from `Gal(L/ℚ)`; its docstring says `a_σ = (deg μ_σ)^{-1/4}`.
   - Hence `c = ±1` holds iff `a` is a homomorphism `Gal(L/ℚ) → ℝ_{>0}`, iff `a ≡ 1`, i.e. iff
     every conjugacy isogeny `μ_σ` has `a_σ = 1`. If any `a_σ ≠ 1`, the witness has
     `G7Clauses β' ε' L` false, and the implication `G7Clauses → LocalGlue` holds vacuously.
3. The root cause is the normalization. unram-tate puts the real factor into `ε'` (`a' = 1`,
   `ε' = c`). Glazer and local-glue's `G7Clauses` put it into `a` (`ε = ±1`, `ν = aμ`).
   `G7Out` accepts both normalizations; `G7Clauses` accepts only the second.

So report claim K1, "TateBridgeK … can replace TateBridge … with no new hypothesis", is right
for `KerWild`. It is wrong for the purpose of reaching `LocalGlue`: through `TateBridgeK`'s data,
local-glue's route cannot be completed. The ℓ = 5, 3 route, `localGlue_of_tateBridge35`, uses
`TateBridge35`'s data. There `a = j ∘ aQ` is not forced to be 1 and `β' = j ∘ βQ` with
`ι_ℂ ∘ βQ = β`, so `G7Clauses` can in principle be transported from G7Data. Two inputs are still
missing on that route: `[L:ℚ] ≤ D` (local-data F3, absent from G7Data) and `ε5 = 1` on `G_L × G_L`.
The report lists both as remaining (its K2).

**Smaller points.**
- The committed `KerWild.lean` cannot be rebuilt from today's sources. `build.sh` re-run gives a
  different file: local-glue later added a verbatim g0-dim block, `localGlue_of_baseChange'`, and
  dropped `A₀.dim = 2` from `G7LocalPackBC` (commits b582bf03, d2f6d6d1). A rebuild would
  duplicate the `G0Dim` declarations, which lg-kerwild also splices in. This is an integration
  issue, not a soundness issue.
- local-glue's newer `localGlue_of_baseChange'` already derives `dim A₀ = 2` the same way as
  lg-kerwild's `dim_model_of_bc`.

**Recommendation (not done).** Either export from `TateBridgeK` the transport
(`TateBridgeT`: `β' = j ∘ βQ`, `ι_ℂ ∘ βQ = β`) and an `a` carrying the real factor, or restate the
every-`ℓ` theorem without the hidden-data hypothesis. Until then, record `LocalGlue` at general `ℓ`
as open.

## 2. ring-class — SOUND (citation note)

**What was claimed.** `ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean`:
- `hprimeNormal : Package.HprimeNormal`;
- `iInH4 : Package.IInH4`;
- `RingClass.ringClassFieldD_tyz : ringClassFieldD (−64n) = H4bar n`;
- the main-theorem variants `tyzThm35ReadingA_of_cmLeaves_ringClass(D)`.

**(a) Compile.** RC-RESULT (§6).

**(b, c) Statements.**
- The proved theorems have cm-points' Prop types by `rfl` (check file). `HprimeNormal` unfolds to
  `∀ d, d % 8 = 5 → Squarefree d → Normal ℚ (Hprimebar d)`, and `IInH4` to
  `∀ n, n % 8 = 5 → Squarefree n → iQ ∈ H4bar n`.
- Both are proved for every `d` (resp. `n ≥ 1`), with more than was asked; there is no
  hypothesis to be vacuous.
- **Non-degeneracy** (VERIFIED, check file):
  - `(Hprime 5).relfinrank (H4 5) = 2` and `Hprime 13 ≠ H4 13`. So `sigmaClass` is not its junk
    `else 1` branch, and `H'_d` is a proper index-2 subfield of `H_{d,4}`.
  - `H4bar 5 ≠ ⊥`, since it contains `i` and `i ∉ ℚ`.
- **The ring class field is Tau Ceti's genuine class field**, not a placeholder (VERIFIED, read):
  - `ringClassField O := classField K (globalClassField (ringClassNormSubgroup O)).1`, built from
    the global existence theorem (`globalAbelianExistence`, proved in the vendored Tau Ceti);
  - `ringClassArtinEquiv` and `finrank_ringClassField` (`[H:K] = #Pic O`) are theorems;
  - no `axiom` or `sorry` occurs under `ZInQKernel/Contrib/TauCeti/`. The only grep hits are the
    word "opaque" in two docstrings of `HeckeRing/Multiplicity/Basic.lean`.
- **`ringClassFieldD` is the ring class field of discriminant `D`.**
  - `condD_spec` proves `|D| = f²|d_K|`.
  - My differential check against PARI (`condD_check.py`, 30 discriminants, conductors 1-8) gives
    the right `d_K` and conductor in 30/30 cases (VERIFIED, computed).
  - A `HeegnerForm 32 D` always has `D = B² − 4AC < 0` with `D ≡ 0, 1 (mod 4)`, so the junk
    branches of `ringClassFieldD` are never reached.
- TYZ's form `[16(n+1), −8, 1]` with `N = 32`: `(A/N, B, NC) = ((n+1)/2, −8, 32)` is primitive,
  because `(n+1)/2` is odd for `n ≡ 5 (mod 8)`. So both curves of the Heegner point have CM by
  `ℤ + 4𝓞_K`, and `ringClassFieldD_tyz` picks the right field (VERIFIED by hand).

**(d) The new leaf `CM.CMFieldOfDefinition ringClassFieldD`.** It says: for every primitive positive
`[A, B, C]` with `32 ∣ A` and discriminant `D`, the Heegner point lies in `A(H_D)`.
- It is true (SPECULATIVE, standard argument). The CM point `(ℂ/⟨1,τ⟩ → ℂ/⟨1/N,τ⟩)` has
  `End(E) = 𝒪_D ⊆ End(E')`. An idele in `K^× · Ô_D^×` moves both lattices by the same scalar,
  so by Shimura's reciprocity law the point is rational over the ring class field of `𝒪_D`. This
  covers forms where `(A/N, B, NC)` is imprimitive (`End(E') ⊋ End(E)`), and conductors sharing a
  prime with `N`.
- As cited, it is a consequence of the main theorem of complex multiplication (Shimura 1971,
  Thm. 5.4 / Ch. 6, UNVERIFIED numbers). It is not the printed statement of Gross 1984 §3. As I
  recall (UNVERIFIED), Gross's Heegner points have `End(E) = End(E')` and conductor prime to `N`;
  TYZ's case has `gcd(4, 32) ≠ 1`.
- The leaf is not stronger than a published theorem. Its citation should name Shimura's
  reciprocity law, as the docstring partly does. It is true only if x0-32's `X0.phiC` is the
  `ℚ`-rational modular parametrization; that leaf belongs to x0-32 and was not reviewed here.
- The TYZ definitions (`H'_d` as the fixed field of `σ_{1+2ϖ}`) could not be compared with the
  source: `~/tyz-src/Period7.tex` is not on this host (VERIFIED: path missing). ring-class's own
  `Hprime_sup_sqrt_two` (`H'_d(√2) = H_{d,4}`, TYZ Prop. 3.2(1) as quoted in the notes) is
  consistent evidence.

## 3. unram-roots — SOUND

**What was claimed.** `UnramRootsTask.unramRoots : G15Ram.UnramRoots p ℓ`, for all `p`, `ℓ`, with no
hypothesis (`scratch/unram-roots/UnramRoots.lean`).

- **(a) Compile.** UR-RESULT (§6).
- **(c)** The `def UnramRoots` block is byte-identical to local-glue's `part_twist.lean` and to
  the copy in `KerWild.lean` (VERIFIED, `diff`).
  - The names it uses (`Fld`, `fixSet`, `inertiaSet`, `GQp`) come from `LadicCond.lean` and are
    shadowed nowhere: there is no `def fixSet`, `inertiaSet`, `Fld` or `GQp` in local-glue's files,
    `KerWild.lean` or `UnramRoots.lean` (VERIFIED, grep).
  - The assembled file is reproducible from its parts (VERIFIED, `cmp`).
- **(b)** The statement is the true textbook fact: an unramified character of `G_F` with finite
  image has an unramified fourth root.
  - `inertiaSet` is metric inertia (`|σx − x| < 1` on the unit ball of `ℚ̄_p`), which is the
    inertia group.
  - The hypotheses are satisfiable (`ψ = 1`), and the conclusion is not automatic.
  - Check (compiled): the Frobenius lift `φ` of the intermediate `UnramProcyclic` lies outside
    inertia (`χ φ = 1` in `ℤ/2`, while `χ = 0` on inertia), so the interface is not met by a
    degenerate `φ`.
- **(d)** No leaf. The only external input is the vendored Tau Ceti (unramified extensions,
  Frobenius generating `Gal(L/K)`, residue cardinality). It is proved, and its axioms are standard.

## 4. afr-absfrob — SOUND

**What was claimed.**
- `AlgFrobRedRed.absFrob : AbsFrob`, from Mathlib only (`AbsFrobDef.lean`);
- `fExtendGen_of_nmp : PkgI2.NeronMappingAbelianScheme.{0} → FExtendGen` (`AfrAbsFrob.lean`).

- **(a) Compile.** AF-RESULT (§6).
- **(c)** Both statements are alg-frob-red's, byte for byte:
  - `src_AlgFrobRed.lean` is `cmp`-identical to `scratch/alg-frob-red/AlgFrobRed.lean`;
  - the `AbsFrob` block of `AbsFrobDef.lean` is `cmp`-identical to `part_red.lean`'s;
  - `AfrAbsFrob.lean` is reproducible from `build.sh` (all VERIFIED).
- **(b)** `AbsFrob` is an existence statement. The witness is the genuine absolute Frobenius:
  - its base map is the identity (`fr_base`, `rfl`);
  - on sections it is `s ↦ s^p`;
  - on `Spec R` it is `Spec(r ↦ r^p)` (`fr_Spec`, re-checked in my file).
- **(b)** In `FExtendGen`, the proof uses only `f 0 = 0` and `σ ∈ D(v)`. `IsFinite F`,
  `Surjective F` and the Frobenius clause are unused, which alg-frob-red's review had already
  noted. Unused hypotheses weaken nothing.
  - The key algebraic lemma `ringHom_eq_of_normal` is a correct statement. Two maps `L → R`
    (`L/ℚ` normal, `R` a domain) that agree after some `R → Q` are equal: `ψ₂(ℓ)` is a root of
    `minpoly ℓ`, which splits in `L`, and `χ ∘ ψ₁` is injective.
- **(d)** I2-NMP (`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` bijective for abelian schemes over a DVR) is a
  pre-existing kernel leaf. It is a consequence of BLR, *Néron models*, §1.2 (an abelian scheme is
  the Néron model of its generic fibre; Néron mapping property for the smooth source `𝒜`;
  numbering UNVERIFIED). It is not stronger.
- `algFrobRed_of_nmp` still rests on alg-frob-red's leaf candidates `GoodRedCofinite` and
  `SmoothGeomConnIntegral` and on I2-Red. These were not in this task's scope; on a read they are
  true and not vacuous (empty schemes are excluded by Mathlib's `ConnectedSpace`).

## 5. curve-infra — SOUND

**What was claimed.** `scratch/curve-infra/CurveInfraAll.lean`:
- `dim X = trdeg_K K(X)` for an integral `X` locally of finite type over a field (`dimEqTrdeg`);
- the algebraic form, two-element dependence, and the smooth forms;
- the `Over` forms with the kernel's `ZInQ.LeafPush2.ffAlgebra`.

- **(a) Compile.** CI-RESULT (§6).
- **(c)** `ZInQ.LeafPush2.ffAlgebra X = CurveInfra.fnFieldAlgebra K X.left X.hom` holds by `rfl`.
  `DimEqTrdegOver` is `DimEqTrdeg` on `Over` objects, by `Iff.rfl` (VERIFIED, check file). The
  copied infra-smooth-dim and g0-dim code is verbatim (their `verbatim.txt`), and the assembled
  file is reproducible (`cmp`).
- **(b)** No hypotheses, no structures. Universes are `Scheme.{0}` and `K : Type`; the
  universe-polymorphic `dim_eq_trdeg` underlies them. Concrete values (VERIFIED, check file):
  - `DimEqTrdegAlg` at `R = K[X]`, together with Mathlib's `dim K[X] = 1`, yields
    `trdeg_K Frac K[X] = 1`;
  - at `R = K` it yields `0`.

  These are the right values, so the statement is not degenerate.
- **(d)** No leaf. Noether normalization is Mathlib's.

## 6. Compile record

COMPILE-RECORD

## 7. Files

- `scratch/rv-fast/RingClassCheck.lean`: imports the built `RingClassBridge`; `rfl` checks,
  non-degeneracy, axioms.
- `scratch/rv-fast/CurveInfraCheck.lean`, `KerWildCheck.lean`, `UnramRootsCheck.lean`,
  `AfrCheck.lean`, `AbsFrobCheck.lean`: copies of each task's main file, minus its `#print` lines,
  with my checks and `#print axioms` appended. Scratch files cannot import each other, so these
  are copies.
- `scratch/rv-fast/condD_check.py`: the PARI differential check.
- `scratch/rv-fast/log.md`: results log.

