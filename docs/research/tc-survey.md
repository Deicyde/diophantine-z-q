# tc-survey: the open leaves of the H decomposition against Tau Ceti

Status: research note (task tc-survey, 2026-11-13). Read-only survey. Results log
`scratch/tc-survey/log.md`; one statement-comparison file `scratch/tc-survey/Compare.lean`; closure
helper `scratch/tc-survey/clos.py`. Base: fork main 883c4ddf, with origin/wip/tc-port (f22bb604)
merged for its vendored modules. No existing file was edited and no Tau Ceti file was vendored.

Sources: `~/tc-main` (Tau Ceti main, 4d91513e, 2026-11-13, Lean v4.36.0-rc2, 31,443 files),
`~/tc-oct16` (5a01f5fe, Lean v4.35.0, 15,755 files); the leaf statements in
`scratch/h-decomposition/Leaves.lean` and `ZInQKernel/HDecomp/`; `docs/research/h-decomposition.md`
§2-§3.

Marks: **VERIFIED** means read in the source or compiled; **STANDARD** means a published theorem
with its reference; **SPECULATIVE** means an assessment. The porting-effort grades and the bridge
sizes are SPECULATIVE. Tau Ceti declarations quoted below were read in the source (VERIFIED) unless
marked "(docstring)". Theorem numbers from memory are UNVERIFIED.

## 0. Main result

**1. Compiled (VERIFIED).** `lake env lean scratch/tc-survey/Compare.lean` exits 0. It imports the
kernel's `ZInQKernel.HDecomp.Conductor.I6Base` and Tau Ceti's degree-two cochain comparison, which
tc-port vendored (`ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison`).
It proves:

```lean
noncomputable def TCSurvey.h2Equiv (K : Type) [Field K] [CharZero K] :
    H2 (Field.absoluteGaloisGroup K) (PkgI6.Z2 K).V ≃+ continuousCohomology 2 (PkgI6.Z2 K) :=
  (PkgI6.Z2 K).explicitH2AddEquivContinuousCohomologyOfDiscrete
theorem TCSurvey.mem_Z2_iff (ε : G_K → G_K → ZMod 2) :
    ((fun q => ε q.1 q.2) ∈ TauCeti.ContCohomology.Z2 G_K (PkgI6.Z2 K).V) ↔ PkgI6.IsCocycle2 ε
theorem TCSurvey.mem_B2_iff (ε : G_K → G_K → ZMod 2) :
    ((fun q => ε q.1 q.2) ∈ TauCeti.ContCohomology.B2 G_K (PkgI6.Z2 K).V) ↔ PkgI6.IsCoboundary2 ε
```

(`G_K` abbreviates `Field.absoluteGaloisGroup K`.) The `#print axioms` output for each of the three
is `[propext, Classical.choice, Quot.sound]`. So Tau Ceti's explicit `H²` uses exactly the
kernel's cochain convention: the `d1` and `d2` formulas are the same. Mathlib's
`continuousCohomology 2` of the kernel's `Z2 K` is the quotient of the kernel's cocycles by its
coboundaries. This is the bridge that links the leaves' cochain forms T14a′, T14b′, T15′
(`PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`) to the `continuousCohomology` forms,
which are where Tau Ceti's Brauer-group theorems land. Naturality under restriction is Tau Ceti's
`TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_map` (oct16). Every module the bridge
needs is already vendored: the closure has 49 modules at oct16, none new.

**2. Survey verdict.** None of the 23 research-level leaves (R1-R22, H5) is in Tau Ceti. A grep of
tc-main finds no file for any of them, for instance no p-adic Hodge theory and no Faltings height
(§2). Among the open textbook leaves, the cheap Tau Ceti closures are the ones other tasks already
own: T17, T18, T20, T21, and T14/T15 on the other host. The best candidates nobody owns are:

- **T25** (`PkgI4.NewformOfEigenform`). Tau Ceti proves the same theorem for its own `Newform` and
  eigenforms, over Mathlib's `CuspForm` on `Γ₁(N)`, at oct16. The bridge is medium: about 205
  unvendored modules (46k lines), plus a dictionary between coefficient-defined and Hecke-defined
  eigenforms, for which Tau Ceti has the key lemmas.
- **T31** (`LeafUnramified`). Tau Ceti proves at oct16 that unit-valued cocycles of an unramified
  layer vanish in `H²(G_K, (Kˢ)ˣ)`, and that `H²(μ_n) ↪ Br`. The bridge is medium (7 unvendored
  modules).
- **Two open glue transports**:
  - the cochain comparison above (compiled);
  - G15's "`D_P ≅ Gal(L_P/ℚ_p)` with ramification filtrations". This is `decompositionEquiv` plus
    `map_ramificationGroup_decompositionHom` at oct16, and the closure is already vendored.

The other candidates are weaker than their leaves:
- T24: Tau Ceti's twist is a newform of level dividing `N·m²`, not an eigenform of every `T_n` at
  exact level `N·m²`.
- T16b: Tau Ceti has only the kernel-level upper-numbering statement.
- T1: purity in dimension 2 only, at main only.
- T5, T9, T26, R7a, R7b, T11a, T35: elliptic curves (`g = 1`) only.

## 1. Table, sorted by value

Effort: **cheap** means the closure is already vendored (or under 20 new modules) and the bridge
is short; **medium** means up to about 300 new oct16 modules or a bridge of a few hundred lines;
**large** means the code exists only after oct16 (a backport from Lean v4.36), or needs more than
300 new modules, or the bridge needs new theory. "new" counts the modules of the closure that are
not already vendored on origin/wip/kw-new (1,162 files: tc-port's 1,119 oct16 files plus kw-new's 44
nov01 files). Closure sizes were computed by `clos.py` (VERIFIED).

| # | Leaf / glue | Tau Ceti declaration (file) | Leaf vs Tau Ceti | Verdict | oct16? | Closure (modules / new) | Effort |
|---|---|---|---|---|---|---|---|
| 1 | WP3 bridge: cochain forms T14a′/b′, T15′ ⇔ `continuousCohomology` forms | `TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete`, `…_map` (RepresentationTheory/Homological/ContCohomology/CohomologyComparison.lean:545, :571) | `IsCocycle2`/`IsCoboundary2` on `G × G → ZMod 2` vs TC `Z2`/`B2`/`H2` | **SAME** (compiled, §0) | yes | 49 / 0 | **cheap** (done in scratch) |
| 2 | G15 transport: `D_P ≅ Gal(L_P/ℚ_p)` with lower filtrations | `IsDedekindDomain.HeightOneSpectrum.decompositionEquiv` (NumberField/LocalGlobal/DecompositionGroup.lean:391); `map_ramificationGroup_decompositionHom` (…/RamificationGroup.lean:127): image of global `G_i` is local `lowerRamificationGroup … i`; `card_ramificationGroup_eq_card_lowerRamificationGroup` (:139) | h-decomposition G15: "STANDARD, not in Lean" | **SAME** (transport); Krasner's lemma NOT FOUND | yes | 114 / 0 | **cheap** |
| 3 | T20 global (diff-bridge) | `multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one` (LocalGlobal/Different/Exponent.lean:239) | leaf: `∃ n, G_n = ⊥ ∧` exact power `∑_{i<n}(\|G_i\|−1)`; TC: `multiplicity = ∑ᶠ i, (\|G_i\| − 1)` | DIFFERENT OBJECTS (TC `ramificationGroup` vs leaf `(P^(i+1)).inertia`; finsum vs exact divisibility) | yes | 156 / 0 (Exponent+Permutation) | cheap |
| 4 | T21 global (diff-bridge) | `multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span` (LocalGlobal/Different/Wild.lean:47) | leaf: `¬ P^(e−1+e·v_p(e)+1) ∣ 𝔇`; TC: `mult ≤ e − 1 + mult_w(span{e})` | SAME after `mult_P(e) = e·v_p(e)` | yes | 177 / 11 | cheap |
| 5 | T18 `ChebotarevExists` (cheb-bridge) | `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet` (Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean:108); main also `infinite_frobeniusPrimeSet` | density `#C/#G` of `frobeniusPrimeSet` vs `∃ p ∉ S`, `Q ∣ p` unramified, `IsArithFrobAt σ Q` | STRONGER, DIFFERENT OBJECTS | yes | 292 / 0 | cheap |
| 6 | T17 `KroneckerWeber` (kw-new) | `TauCeti.ClassFieldTheory.kroneckerWeber (E) [NumberField E] [IsAbelianGalois ℚ E] : ∃ n, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)` (ClassFields/KroneckerWeber.lean:178) | leaf: `IsGalois` + commuting automorphisms, `n : ℕ+` | SAME | no (nov01) | nov01 949 / 0; main 1035 / 86 | cheap (vendored by kw-new) |
| 7 | T15 at `ℚ_p` (other host) | `TauCeti.ClassFieldTheory.natCard_cohomFp_two_absoluteGaloisGroup_of_isPrimitiveRoot {ζ : F} (hζ : IsPrimitiveRoot ζ n) : Nat.card (cohomFp n (Field.absoluteGaloisGroup F) 2) = n` (ClassFieldTheory/Brauer/RootsOfUnity.lean:238; `F` a nonarchimedean local field; Mathlib has `IsNonarchimedeanLocalField ℚ_[p]`); `h2MuEquivZMod` (:89) | leaf `H2TwoClasses G_{ℚ_p}` (cochains) | DIFFERENT OBJECTS: `trivialFp 2` vs `TopRep.res … (Z2 ℚ)`, then row 1 | yes | 296 / 8 | cheap-medium |
| 8 | **T31** `GlueDescent.B2Q.LeafUnramified` | `TauCeti.ClassFieldTheory.mk_eq_zero_of_forall_mem_unitFiltration_zero`, `brBaseChange_relBrInfl_eq_zero` (ClassFieldTheory/Brauer/Unramified.lean:416, :433): a cocycle inflated from an unramified layer with values in `U(L,0)` has trivial class in `H²(G_K,(Kˢ)ˣ)`; `h2MuToBr_injective` (Brauer/Torsion.lean:114): `H²(G_F, μ_n) ↪ Br F` | leaf: a `±1 ⊂ ℂˣ` sign cocycle inflated from finite Galois `L/ℚ` unramified at `p` restricts to a coboundary on `G_{ℚ_p}` | DIFFERENT OBJECTS: `±1 ⊂ ℂˣ` ↔ `μ₂ ⊂ (ℚ_pˢ)ˣ`; the global layer `L` ↔ a local unramified layer; Kummer injectivity; rows 1, 2 | yes | Unramified 253 / 0; Torsion 159 / 7 | **medium**; not owned by any task |
| 9 | T14a, T14b (other host) | main: `brLocalization_injective : Function.Injective (brLocalization K)` (Global/Brauer/SumFormula.lean:71), `sumLocalInv_brLocalization_eq_zero` (:102); oct16 has only the conditional forms `…_of_brLocalization_injective`, `…_of_subsingleton_h1_globalFormation` | `Br ℚ → ⊕_v Br ℚ_v` injective, sum of invariants 0, vs `H²(G_ℚ, ℤ/2)` cochains | DIFFERENT OBJECTS: `h2MuToBr`, local base change `brBaseChange` vs `loc`/`resC`, then row 1 | **no** (unconditional Hasse is main-only) | main 919 / 45 | large (backport) |
| 10 | **T25** `PkgI4.NewformOfEigenform` | `HeckeRing.GL2.EigenformAwayFromLevel.exists_newform_eigenvalue_eq [NeZero N] (f : EigenformAwayFromLevel N k) : ∃ (M : ℕ) (_ : NeZero M) (hM : M ∣ N) (g : Newform M k), ∀ p (hp : p.Prime) (hpN : p.Coprime N), g.eigenvalue ⟨p, _⟩ _ = f.eigenvalue ⟨p, _⟩ hpN` (ModularForms/Newforms/Decomposition.lean:222) | leaf: `IsNormalizedEigenform g χ` (coefficient identities, all `T_n`) ⇒ `∃ N ∣ M`, `IsNewform f χ'` (eigenform ∧ ∉ `oldSpace`), `a_p(f) = a_p(g)` for `p ∤ M` | **SAME up to a medium bridge**: (i) the `Γ₁` subgroup coercions (`(Gamma1 N : Subgroup GL₂ℝ)` vs `(Gamma1 N).map (mapGL ℝ)`); (ii) `HasNebentypus` ↔ `cuspFormCharSpace`; (iii) coefficients ⇒ `T_p` eigen: `heckeTNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul` (HeckeSlash/Nebentypus/Eigenvector.lean:120); (iv) `Newform` ⇒ the all-`m,n` identity: `Newform.toEigenform`, `toEigenform_eigenvalue_eq_qExpansion_coeff`, `Eigenform.eigenvalue_mul`, `eigenvalue_prime_pow_add_two`, plus elementary multiplicative-function algebra; (v) ∉ `oldSpace`: TC `cuspFormsOld` = span of `levelRaise d` images (Newforms/Basic.lean:105), `disjoint_cuspFormsOld_cuspFormsNew` | yes | oct16 216 / 204 (45.6k lines) | **medium**; not owned by any task |
| 11 | T24 `EigenformTwist` | `HeckeRing.GL2.Newform.exists_newform_qExpansion_coeff_prime_eq_twist (f : Newform N k) (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L) (hML : M * M ∣ L) : ∃ R (_ : NeZero R) (hR : R ∣ L) (g : Newform R k), g.χ… = … ∧ ∀ p, p.Prime → p.Coprime L → a_p(g) = ψ p * a_p(f)` (Newforms/Twist.lean:59) | leaf: from an eigenform of level `N`, a normalized eigenform of **all** `T_n` at exact level `N·m²` with `a_p(g') = ψ(p)a_p(g)`, `p ∤ Nm` | **WEAKER**: level `R ∣ N·m²`; raising to exact level `N·m²` as an all-`T_n` eigenform needs `p`-stabilization at primes dividing `N m²/R`, which is not in TC. Alternative (SPECULATIVE): restate T24 as "a newform of level dividing `N m²`" if G12/G13 use only good-prime coefficients (to check) | yes | oct16 219 / 207 | medium (with T25) |
| 12 | T16b `LocalReciprocityUpper` | `localArtinEquiv` (ClassFieldTheory/Local/Reciprocity.lean:85); main: `unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot (v : ℕ) : unitFiltration K v ≤ normGroup K M ↔ upperRamificationGroup K M ⟨v,_⟩ = ⊥` (Local/Conductor/UpperNumbering.lean:64) | leaf: surjective `θ` with norm kernel, Frobenius clause, and `θ '' U^{⌈v⌉} = G^v` | **WEAKER**: the image identity was not found (grep), only the kernel-level case `U^v ⊆ N ⇔ G^v = 1` | partly (Reciprocity yes, UpperNumbering no) | main UpperNumbering 521 / 56 | large |
| 13 | T16a `LocalKroneckerWeber` (lkw) | no statement (grep `local.*kronecker` empty); ingredients `localAbelianExistence` (LocalExistence/Existence.lean:159, main), Local/Cyclotomic.lean (docstring: `localArtinMap_cyclotomic_padic`, `range_localCyclotomicCharacter`) | — | NOT FOUND as a statement | Cyclotomic yes | Cyclotomic oct16 512 / 0 | (task lkw) |
| 14 | T1 `PkgI2.PurityBranchLocus` (other host) | `TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two (hdim : ringKrullDim A = 2) : PurityHolds A` (AlgebraicGeometry/FiniteEtale/Purity.lean:53); `Algebra.etale_of_isUnramifiedAt_height_eq_one_of_purityHolds` (FiniteEtale/BranchPurity.lean:126, finite torsion-free `B`) | leaf: any dimension, local at `q`, quasi-finite | **WEAKER** (dimension 2; finite algebras). SPECULATIVE: G2's Prop TS lives on a regular 2-dimensional base (`ℙ¹` over `ℤ` localized), so a dimension-≤2 form of T1 might suffice | no | main Purity 222 / 204, BranchPurity 103 / 93 | large |
| 15 | Nonzero abelian variety (WP4; "Mathlib cannot construct one") | `AlgebraicGeometry.AbelianVariety` (AbelianVariety/Basic.lean:77: `toOver`, `grpObj`, `isProper`, `geometricallyIntegral`; smoothness derived), oct16+main; main: `WeierstrassCurve.toAbelianVariety` (EllipticCurve/Scheme/AbelianVariety.lean:65), `dim_toAbelianVariety : W.toAbelianVariety.dim = 1`, `dim_prod_toAbelianVariety : … = 2` | `PkgI3.AbVar` / `PkgI2.IsAbelianVariety` carry the same data (with `Smooth` as a field) | DIFFERENT OBJECTS, cheap bridge (TC derives `Smooth`) | AbelianVariety yes; elliptic example no | main 342 / 325 | large (backport) |
| 16 | T5, T26, T9 | `card_ker_mulByIntIsogeny` (EllipticCurve/Isogeny/MulByInt/IsSepClosed.lean:59), `free_tateModule`, `natCard_tateModuleLevel` (EllipticCurve/TateModule/Basic.lean:62, :80), `tateModuleWeilPairing` (TateModule/WeilPairing.lean:116) | leaves: every abelian variety, every `g` | **WEAKER** (elliptic curves, `g = 1`, separably closed base) | yes | 206 / 188; 212 / 192; 351 / 311 | n/a (no use for the QM surface) |
| 17 | R7a, R7b | `hasGoodReduction_iff_tateModuleGaloisRepresentation_eq_one` (EllipticCurve/TateModule/GoodReduction.lean:205, main); `HasPotentialGoodReduction.finite_image_tateModuleGaloisRepresentation` (PotentialGoodReduction.lean, docstring) | leaves: abelian varieties over a DVR | **WEAKER** (`g = 1`) | R7a no, R7b yes | main 716 / 473 | n/a |
| 18 | T11a, T35 | `ContMDiff.exists_apply_mk_eq_mul_add` (Analysis/Complex/RiemannSurface/ComplexTorus.lean:71); `PeriodPair.weierstrassCurve` (Analysis/SpecialFunctions/Elliptic/Uniformization.lean:164) | leaves: `ℂ^g/Λ` for every `A/K`, `σ : K → ℂ` | **WEAKER** (`g = 1`, not `AbelianVariety`) | no | — | n/a |
| 19 | G13 `X1ModelExists` | `yOne N` (AlgebraicGeometry/ModularCurve/YOne.lean): the fine moduli scheme `Y₁(N)` over `ℤ` for `N ≥ 4` (Tate normal form) | leaf: a smooth projective model of `X₁(N)` over `ℚ` via the function field `K_N` | DIFFERENT OBJECTS (affine moduli scheme over `ℤ`, no compactification or function-field identification) | yes | oct16 569 / 533 | large |
| 20 | T34 `DimJ1Genus` | main `EisensteinSeries/WeightTwo/Dimension.lean` (docstring): `dim M₂(Γ₁(N)) = dim S₂(Γ₁(N)) + ε∞ − 1` | leaf: `dim J₁(N)` = genus formula | DIFFERENT (no genus of `Γ₁(N)`, no `J₁(N)`) | no | main 487 / 446 | n/a |

**NOT FOUND in Tau Ceti main** (each checked by grep of tc-main plus reading of the
nearest files; VERIFIED absent as searched):

- **Textbook leaves**: T3 (Néron mapping property for abelian schemes: TC abelian varieties are
  over fields only); T4 (abelian-variety form; elliptic torsion reduction exists,
  EllipticCurve/Affine/Point/TorsionReduction.lean, docstring); T6, T7 (no `T_ℓ`/`V_ℓ` of abelian
  varieties; TC's `TateModule` is generic, Algebra/Module/Torsion/TateModule.lean); T8 (no Poincaré
  reducibility); T10 (no ℓ-adic cohomology of abelian varieties); T11b (only `Hom.baseChange`,
  with no descent); T23 (no B_dR or de Rham representations; the 61 "DeRham" files are manifold de
  Rham cohomology); T27; T28 (no "Igusa" anywhere); T29a/b (no maximal quaternion orders); T33
  (PicardFunctor/Abel/Jacobi.lean says representability "is not treated here").
- **Research-level leaves**: R1-R5 (Shimura curves, QM, CM points: the 161 "Shimura" hits are
  Hecke-operator files); R6, R8 (the 23 "Raynaud" hits are citations of Bosch–Lütkebohmert–Raynaud,
  *Néron Models*, in Weil-restriction and rigidified-line-bundle files; no semistable reduction
  of abelian varieties); R9a/b (no Faltings); R10-R13 (no Hodge–Tate, no B_dR); R14,
  R15 (no Galois representations of eigenforms); R16 (only the level-one period-polynomial
  Eichler–Shimura); R17 (no "Carayol"); R18-R22 and H5 (no Faltings height: the 2 hits are a
  polynomial lemma; `NumberTheory/Height/Arakelov` is Weil-type heights of points).
- **Glue**: `SemisimpleBaseChange`, `LeafConj` as stated (TC has `decompositionHom_conj` for finite
  layers only), Krasner's lemma, Weil restriction of abelian varieties (TC
  `Algebra/HopfAlgebra/WeilRestriction.lean` is for affine group schemes), G10/T12 complex
  conjugation on `V_ℓ(A)`, G17's Poincaré step, `BelyiX1` (generic Belyi theory exists:
  FieldTheory/FunctionField/Belyi/GaloisAction.lean, Analysis/Complex/RiemannSurface/BelyiPair.lean).

Leaves proved elsewhere before this survey (not surveyed): T2 (t-brauer-purity), T13, T19
(t-skolem-kw), T20/T21 local and T22a/b (t-different), T30 as glue from T16 (t30-adelic), the
real-place half of T15 (t-brauer-purity). For T13, Tau Ceti also has `skolemNoether`; T19 is
proved anyway.

## 2. Open glue steps that Tau Ceti could replace

| Glue | Tau Ceti | Status |
|---|---|---|
| WP3 / T14-T15 forms: cochains ⇔ `continuousCohomology` | `explicitH2AddEquivContinuousCohomologyOfDiscrete` (+ `_map`) | compiled against the kernel's `Z2` (§0); vendored |
| G15: `D_P ≅ Gal(L_P/ℚ_p)` with lower ramification filtrations (h-decomposition: "STANDARD, not in Lean") | `decompositionEquiv`, `map_ramificationGroup_decompositionHom`, `card_ramificationGroup_eq_card_lowerRamificationGroup` | vendored (oct16, 114 modules, 0 new) |
| G15: Krasner's choice of the local field | not found | open |
| G15 D4 / upper numbering | main `conductorExponent_le_iff_upperRamificationGroup_eq_bot` (Local/Conductor/UpperNumbering.lean:121) | main only; D4 is already proved in the kernel |
| G7: `ℚ_p(μ_n)`, unramified extensions of `ℚ_p` | Local/Cyclotomic.lean, LocalField/Unramified (docstrings: `unramifiedExtension`, `irreducible_cyclotomic_prime_pow_ratPadic`) | not checked in detail; HDecomp/Sqrt/Disj.lean already covers the disjointness |
| G2: Prop TS (purity on the arithmetic surface) | FiniteEtale/BranchPurity.lean + Purity.lean (dimension 2) | main only, large; see row 14 |
| G13: `X1ModelExists` | `yOne N` | different objects, large |
| WP4: a nonzero abelian variety | `WeierstrassCurve.toAbelianVariety` | main only, large |

## 3. Notes on method

- The three code-search subagents could not grep the checkouts. Every NOT FOUND above was
  re-checked here with `grep -r` on tc-main (term counts and file lists in the log).
- The "no `sorry`" status of the Tau Ceti files is by Tau Ceti's axiom policy
  (`scripts/Axioms.lean`: only the three standard axioms). For the 1,119 files vendored by tc-port,
  tc-port's build log reports no `declaration uses sorry`. The newform files (rows 10-11) are not
  vendored, so their status here rests on the policy only.
- oct16 is close to our Mathlib pin. tc-port built its 1,119 oct16 files with five one-line fixes
  (`scratch/tc-port/log.md`), so oct16 candidates are realistic ports. Main-only candidates need a
  backport from Lean v4.36.
