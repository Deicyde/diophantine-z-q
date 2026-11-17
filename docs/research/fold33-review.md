# fold33-review: review of the new leaves that wip/leaf-fold33b brings into `frozenTarget`

Task fold33-review, 2026-11-16. Base: wip/leaf-fold33b 667e0aed (origin/main is already an ancestor, so no merge was
needed). Scratch, checks and log: `scratch/fold33-review/`. Nothing under `ZInQKernel/` or `blueprint/` was edited.

Marks. **VERIFIED**: compiled, computed, or read in a file named here. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no network and no copies of the sources. So every claim
about a print is **UNVERIFIED**, except what `docs/research/locators.md` records as read (only the Gross–Zagier row).

## 0. Verdict

**All three new leaves pass this review, and none needs a statement change.** No leaf is false as stated, none is
vacuous, and none is inert. The reroutes are clean: the hypotheses of `frozenTarget` are the 37 statements listed in
`docs/one-proof/open-statements.json`. Apart from hCM, each has the same full type as before the fold, plus exactly
one new field, `neronSchemeExtensionDedekind`. No removed Prop occurs anywhere in the constant closure of
`frozenTarget`. Its axioms are `[propext, Classical.choice, Quot.sound]` (VERIFIED).

| leaf (binder / field) | Lean statement | source cited | differences from the print | vacuity / inertness (Lean) | verdict |
| --- | --- | --- | --- | --- | --- |
| `hCM : ZInQ.Contrib.HCMDict.ShimuraThm54` | `ShimuraMainCM.lean:426` | Shimura 1971 Thm 5.4; Lang, *Elliptic functions* Ch. 10 Thm 3 (UNVERIFIED, unread) | all are direct instances, or dictionary steps that Lean proves (§1) | hypotheses hold together at `m = 1, σ = id, s = 1, 𝔞 = κ⁻¹⟨1,i⟩` (`shimuraThm54_hyps_satisfiable`, VERIFIED); used through `shimuraMainCM_of_printed` (in the closure) | **LEAF**, pending a reading of the locator |
| `neronSchemeExtensionDedekind : ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind` | `MumfordGroupLawNeron.lean:56` | BLR, *Néron models* (1990) §1.4 Thm 3 with §1.2 Def. 1 (UNVERIFIED, unread) | all are direct instances (§2) | inhabited at `(ℤ, ℚ, AbVar.zero ℚ)`; DVR instances exist; used through `mumfordGroupLawDVR_of_neron`, `neronGoodModelIso_of_dedekind` and `neronSchemeExtensionExists_of_dedekind` (all in the closure, VERIFIED) | **LEAF**, pending a reading of the locator |
| `hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd` | `GrossZagierAlgebraic.lean:138` (`GrossZagierAlgOptAt`, l. 108) | Gross–Zagier, Invent. Math. 84 (1986), I (6.3) p.230 and V §2 p.312 (locators.md read these places) | direct instances, plus three standard dictionary steps that Lean does not prove (D1–D3, §3) | gzopt-dict's bridge produces the leaf's extra hypotheses from gz-optimal's (`grossZagierModuliOptCd_of_alg`, with the proved `gamma0QExpansion_proof`); used through `core_selfOptimal` / `core_isog` (in the closure, VERIFIED) | **LEAF (printed form through a dictionary), needs-reading**: under the strictest rule D1–D3 are unproved translation steps |

What the hGZ caveat means. D1–D3 are not steps of Gross–Zagier's proof. They identify the leaf's objects with the
print's objects:

* **D1**: a `ℚ`-embedding of function fields is a morphism of curves.
* **D2**: the value of φ at a Heegner point is read through `q`-expansions.
* **D3**: `IsOptimalParam` describes the strong Weil parametrization.

Lean proves none of them. D2 could be proved from what the tree already contains (§3.3). D3 matters only if GZ V §2
is stated for the strong Weil parametrization alone. That reading question is open: locators.md records the page, not
the hypotheses on φ. The kinds row (`published / unread / LEAF / LEAF`) is consistent with this. I recommend keeping
the flag "unread" until someone reads GZ V §2 for its hypotheses on φ.

## 1. `hCM : HCMDict.ShimuraThm54` (Shimura 1971 Thm 5.4, printed form)

**Statement** (`ZInQKernel/Contrib/OneProof/ShimuraMainCM.lean:426`). The setting:

* `m` squarefree, `K = ℚ(√−m)`;
* `e : Kˢ → ℚ̄` normalized by `ιC(e(ω)) = i√m`;
* `σ ∈ Aut(ℂ)` and an idele `s` with `ArtinCond m e σ s` (σ = [s, K] on `K^ab`, Tau Ceti's arithmetic Artin map);
* `𝔞 ⊂ K` with `κ(𝔞)` the lattice of a period pair;
* `E/ℂ` a short Weierstrass model;
* `ξ` with `IsAnalyticUnif E κ(𝔞) ξ`.

The conclusion: there is ξ′ with `IsAnalyticUnif (E.map σ) κ(s⁻¹𝔞) ξ′` and `ξ(κu)^σ = ξ′(κv)` whenever
`s_f v − u ∈ 𝔞̂`.

**Clause by clause** (print as recalled in hcm-dict's report, UNVERIFIED):

| clause | Lean | classification |
| --- | --- | --- |
| `K ⊂ ℂ`, `σ ∈ Aut(ℂ/K)`, `σ = [s,K]` on `K^ab` | `kappa`, normalization of `e`, `ArtinCond` (taking `F = K` forces σ to fix `κ(K)`) | inherited unchanged from `ShimuraMainCM`. The direction is Tau Ceti's arithmetic Frobenius, with `j(𝔞)^{Frob 𝔭} = j(𝔭⁻¹𝔞)` (`docs/research/shimura-modfn.md` §1, Cox Cor. 11.37 as cited there; UNVERIFIED here, and PARI is not installed on this host) |
| `𝔞` a lattice in `K` | `∃ L : PeriodPair, L.lattice = κ '' 𝔞` | direct instance: every ℤ-lattice of `K` gives a period pair |
| `E` an elliptic curve over `ℂ` | short models `a₁ = a₂ = a₃ = 0` only | direct instance (special case) |
| `ξ : ℂ/𝔞 → E(ℂ)` an analytic isomorphism | `IsAnalyticUnif` | **dictionary proved in Lean**: `exists_lattice_eq` and `isAnalyticUnif_iff` show that the maps satisfying it are exactly `z ↦ ξ_{L₀}(αz)` with `L₀ = α·κ(𝔞)`. So the hypothesis is not weaker than the print's. In the conclusion, the print's ξ′ is holomorphic into `E^σ(ℂ) ⊂ ℙ²`, hence holomorphic in the affine chart; it sends 0 to O (take `u = 0`), so it is additive |
| `s⁻¹𝔞`, `s⁻¹u` | `sInvLat m s 𝔞 = {x : s_f x ∈ 𝔞̂}` with `latHat` the closure of `𝔞` in `𝔸_{K,f}`; "`v` represents `s⁻¹u`" is `s_f v − u ∈ 𝔞̂` | inherited from `ShimuraMainCM`. Checked here: `(s⁻¹𝔞)_p = s_p⁻¹𝔞_p` holds iff `s_f x ∈ 𝔞̂`, and `𝔞̂ = 𝔞 ⊗ ℤ̂` is the closure of `𝔞`, also for lattices that are not `𝒪_K`-ideals (SPECULATIVE argument, standard) |
| uniqueness of ξ′ | dropped | direct instance (and-elimination) |

**Vacuity** (VERIFIED, `scratch/fold33-review/Vacuity.lean`). `Fold33Review.shimuraThm54_hyps_satisfiable` exhibits
all hypotheses at once, using only standard axioms:

* `m = 1`;
* `e` from `exists_normalized_embed_any 1`;
* `σ = RingEquiv.refl ℂ`, `s = 1`, with `ArtinCond` by `map_one`, the same `s = 1` instance the TYZ chain uses at
  `RingClassLattice.lean:1154`;
* `𝔞 = κ⁻¹⟨1, i⟩`, `L = pp I`;
* `E = L.weierstrassCurve`, which is short and elliptic;
* `ξ = L.toPoint`.

**Not inert.** `frozenTarget` reads the leaf only through `shimuraMainCM_of_printed`, which is in its closure. The
chain derives from it non-trivial facts, for example the algebraicity of the moduli coordinates of CM points (Step A in
`RingClassLattice.lean`), which Mathlib does not prove.

**Relation to the old binder.** Lean proves `ShimuraThm54 → ShimuraMainCM`. The converse is not proved. It would also
need that `s⁻¹𝔞` is a lattice: `ShimuraMainCM` takes a period pair `P'` with lattice `κ(s⁻¹𝔞)` as a hypothesis,
whereas `ShimuraThm54` asserts that `κ(s⁻¹𝔞)` is the kernel of ξ′. That is a true adelic fact (Shimura §5.2,
UNVERIFIED) and a consequence of the print, so the new leaf is slightly stronger than the old binder as a Lean
statement, but still not stronger than the print. The retyping does not change any convention: the Artin direction,
`sInvLat`, `latHat` and the representative convention are the definitions of `ShimuraMainCM`, unchanged, which an
earlier review found faithful (hcm-dict.md §2 item 4).

## 2. `neronSchemeExtensionDedekind` (BLR §1.4 Thm 3, existence of Néron models over a Dedekind base)

**Statement** (`ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean:56`). The data: `D` a Dedekind domain, `L` its
fraction field, and `A : PkgI3.AbVar L`. `AbVar` is a group object over `Spec L` that is proper, smooth and
geometrically integral (`G9/I3Layer.lean:622`; a genuine definition). The leaf asserts that there exist `N` over
`Spec D` and `ε : N_L ≅ A` with:

* `N` smooth, separated and quasi-compact;
* for every smooth `Y` over `Spec D`, every `L`-morphism `Y_L → A` of the form `f_L ≫ ε` for some `f : Y → N`.

| clause of the print (BLR as recalled, UNVERIFIED) | Lean | classification |
| --- | --- | --- |
| `S` a Dedekind scheme, `K` its function field | `S = Spec D` affine, `D` a Dedekind domain (Mathlib's notion includes fields, as BLR's normal noetherian dimension ≤ 1 does) | direct instance (special case) |
| `A_K` an abelian variety | `AbVar L` (proper, smooth, geometrically integral group scheme) | genuine definition; same objects |
| Néron model: smooth, separated, of finite type | smooth, separated, quasi-compact | direct instance (weakening: finite type implies quasi-compact) |
| `N_K ≅ A_K` | `ε : (Over.pullback (genMap D L)).obj N ≅ A.X` | same |
| mapping property: every `u_K : Y_K → A_K`, `Y` smooth, extends **uniquely** | surjectivity of `f ↦ f_L ≫ ε` (existence only) | direct instance (and-elimination; uniqueness is in any case proved in Lean, `NeronC.pullback_map_injective`) |
| group structure on `N` | not asked | direct instance (and-elimination) |

**Vacuity** (VERIFIED, `Vacuity.lean` §2). The hypotheses are inhabited at `(ℤ, ℚ, PkgI3.AbVar.zero ℚ)`, where `ℤ` is
not a field. The DVR instances `ℤ_[p]` / `ℚ_[p]` exist; the DVR case is the one `mumfordGroupLawDVR_of_neron` reads.

**Not trivially provable.** For a field `D` the statement is trivial (`N = A`). For `D = ℤ` and an abelian variety
with bad reduction it asserts the existence of a Néron model of finite type, which is outside Mathlib (SPECULATIVE;
Lean cannot prove that a statement is unprovable).

**Not inert.** The leaf enters through three theorems, all in the closure of `frozenTarget` (VERIFIED):

* `GoodModelIso.neronGoodModelIso_of_dedekind`, which proves the glue `NeronGoodModelIso` from the leaf alone;
* `mumfordGroupLawDVR_of_neron`, which gives *GIT* 6.14 over a DVR;
* `neronSchemeExtensionExists_of_dedekind`, which gives the removed textbook field (the case `D = 𝓞_L`).

## 3. `hGZ : GZAlg.GrossZagierAlgOptCd` (Gross–Zagier 1986, strong Weil parametrization, algebraic `φ`)

**Statement** (`GrossZagierAlgebraic.lean:108, 138`). The leaf applies to every short model `E'` in the isogeny class
of `C_d`, `d ≡ 5 (mod 8)` squarefree. The data and conditions:

* `f` a newform of level `N`, trivial character, with `a_n(f) = a_n(E')`;
* `φ^* : ℚ(E') →ₐ[ℚ] ℚ(j, j_N) ⊂ ℚ((q))` with `ord_q φ^*(x) < 0`;
* `X, Y` meromorphic on `ℍ` with `q`-expansions `φ^*(x)`, `φ^*(y)`, and `IsOptimalParam N f E' X Y`;
* `D < −4` an odd fundamental discriminant, with the Heegner hypothesis and `4N ∣ D − β²`;
* `τ` a complete set of Heegner points (`IsHeegnerPointReps`);
* `K = ℚ(δ)`, `δ² = D`, `ι(δ) = i√|D|`;
* `y ∈ E'(K)` with `ι(y) = n·Σ φ(τ_r)`, `n ≠ 0`;
* `F, G` the entire continuations of `L(f, s)` and `L(f ⊗ χ_D, s)`.

The conclusion: `(FG)'(1) = κ·ĥ(y)` for some `κ > 0`.

### 3.1 Clause by clause

| clause | Lean | classification |
| --- | --- | --- |
| `E/ℚ` modular of conductor `N`, newform `f` | `f : Newform N 2` (Tau Ceti: in the new subspace, `a₁ = 1`, a genuine newform), `f.χ = 1`, `coeff f n = E.LFunction n` (Mathlib's Euler product, local minimal models) | direct instance; modularity is assumed, as in GZ (locators.md: "the primary section assumes modularity") |
| `φ : X₀(N) → E` over `ℚ`, `φ(∞) = O` | `φ^*` into `X0Field N = ℚ(jq, jq(q^N))`; `ord_q φ^*(x) < 0` | **D1 (dictionary, not proved in Lean)**: ℚ-embeddings of function fields of smooth projective curves are morphisms (Hartshorne I.6.12 / Silverman AEC II.2.5, UNVERIFIED). That `ℚ(X₀(N)) = ℚ(j, j_N)` is Shimura 1971 §6.7 / Prop. 6.9, UNVERIFIED. Lean proves `X0Field N ≃+* Frac(ℚ[X,Y]/(Φ_N))` (gzopt-dict `X0Model.lean`) and, now, the `q`-expansion principle (`gamma0QExpansion_proof`). `φ(∞) = O` iff `ord_q φ^*x < 0` because `x` has its only pole at `O` and `q` is a local parameter at `∞`. |
| φ at the Heegner points | `X, Y` with `HasQExp` and meromorphy; `modPt E X Y τ` (limits on punctured neighbourhoods) | **D2 (dictionary, not proved in Lean)**: `X = R(j(τ), j(Nτ))` off a discrete set, by the identity theorem. `MeromorphicAt` at every point makes the singular set closed and discrete, and the convergent `q`-series agrees with `R(j, j_N)` on `Im τ > T`. So `modPt` is φ at the point `(j(τ), j(Nτ))` of the model, and `pairOf N τ = (⟨1,τ⟩, ⟨1/N,τ⟩)` is the moduli point `(ℂ/𝔞 → ℂ/𝔫⁻¹𝔞)` of GZ's Heegner point (SPECULATIVE argument, standard). The leaf does not assume Γ₀(N)-invariance, but the condition is implied, not dropped. |
| φ is the strong Weil parametrization | `IsOptimalParam`: `L = c·Λ_f` (`c ∈ ℚ`) and `φ(τ) = ξ_L(c·φ_f(τ))` | **D3 (dictionary, not proved in Lean)**: `L = cΛ_f` iff `φ_*` maps `H₁(X₀(N))` onto `H₁(E)` iff `J₀(N) → E` has connected kernel (gz-optimal; Mathlib has no `J₀(N)`). Needed only if GZ V §2 is restricted to the strong Weil parametrization. If the formula holds for every φ (with the constant `c`), the optimal case is a direct instance (special case). **needs-reading** |
| Heegner data `(𝒪_K, 𝔫, [𝔞])`, `y_K = Σ_σ φ(x^σ)` | `IsHeegnerPointReps N D β τ` (all Heegner pairs with `End = 𝒪_D` and `𝔫 = (N, (−β+√D)/2)` killing the kernel, up to homothety); `ι(y) = n·Σ_r modPt(τ_r)` | inherited from gz-moduli / gz-optimal. Both signs of `β` are quantified, so the orientation convention is immaterial. `y = n·y_K` with `ĥ(n y_K) = n² ĥ(y_K)`: Lean proves this step in the consumers (`core_selfOptimal`) |
| `D` odd fundamental, `D < −4`, Heegner hypothesis | `IsOddImagFundDisc`, `D < -4`, `HeegnerHyp` (`jacobiSym p |D| = 1` for `p ∣ N`) | direct instance (special case: odd `D`, `u = 1`) |
| `L(E/K, s) = L(f, s) L(f⊗χ_D, s)` | `F·G` with `IsEntireCont (coeff f) 2 F`, `IsEntireCont (twistCoeff f D) 2 G` | folded identity: `(D, N) = 1` by the Heegner hypothesis. `chiD D n = (n/|D|)` is the Kronecker character `(D/n)`: checked on 30 pairs, 0 mismatches (VERIFIED, `py/chiD_check.py`), and by Jacobi reciprocity with `|D| ≡ 3 (mod 4)` |
| `L'(E/K,1) = (‖ω‖²/(c²u²√|D|))·ĥ(y_K)` | `∃ κ > 0, (FG)'(1) = κ·ĥ(y)`; `ĥ` = Tau Ceti's canonical height (genuine: `canonicalHeight_eq_zero_iff_isOfFinAddOrder`) | direct instance (exists-introduction; the constant is forgotten) |

### 3.2 Vacuity and inertness

* **The new hypotheses are satisfiable at the chain's instances** (VERIFIED, compiled). gzopt-dict's bridge
  `grossZagierModuliOptAt_of_alg` takes gz-optimal's data (`IsModularParam`, `IsOptimalParam`, Heegner data). It then
  builds `φ^* = phiOf x' y'`, proves `ord_q φ^*(x) < 0`, and passes the same `X, Y`. With the proved principle
  `gamma0QExpansion_proof` this holds unconditionally: `GrossZagierAlgOptCd → GZOptimal.GrossZagierModuliOptCd`
  (`Vacuity.lean` §3).
* **The chain's instances.** `core_selfOptimal` and `PeriodOdd.core_isog` (both in the closure) apply the leaf with:
  * `X = xPar E L f c₀`, `Y = yPar E L f c₀` (`℘_L(c₀φ_f)`, `℘′_L(c₀φ_f)/2`);
  * `IsModularParam` by `isModularParam_of`;
  * `IsOptimalParam` by `⟨L, c₀, hL, hlat, modPt_eq⟩`, at `E' = C_d` or at the 2-isogenous `E'_d`.
* **Not shown in Lean: the whole hypothesis list at a concrete `d`.** That would need a newform for `C_5`, a complete
  set of Heegner points, the point `y` and the period identity `L = c₀Λ_f`. These come from heegner-32 and
  period-odd's chain, and `y` from hCM. This is the one vacuity question left open (SPECULATIVE: not expected to
  fail).
* **Not trivially provable.** The conclusion links `(FG)'(1)` (genuine L-functions: `IsEntireCont` determines `F, G`
  uniquely, `IsEntireCont.eq`) to the genuine canonical height. Nothing in the hypotheses forces either side to vanish
  trivially (SPECULATIVE).

### 3.3 Recommendation for D2

D2 can be stated and proved in the tree. The lemma would say: for `x ∈ X0Field N` there is a meromorphic `X` on `ℍ`
with `HasQExp X x`, unique off a discrete set. The pieces are `hasQExp_j`, `hasQExp_jN`, closure of `HasQExp` under
field operations, and the identity theorem. With that lemma the leaf's `X, Y` would be determined by `φ^*` inside Lean.
Only D1 (curves versus function fields) and D3 (optimality) would remain as dictionary steps.

## 4. Reroutes: homFreeFiniteAlgClosed, sga3_VIB_3_10_Nbhd, mumfordGroupLawConn

These were checked in `scratch/fold33-review/Closure.lean` (2 min 16 s, output in `Closure-output.txt`). All results
below are VERIFIED.

* **Hypotheses of `frozenTarget`.** My copy of `OpenStatements.lean` writes `scratch/fold33-review/open-statements.json`:
  37 hypotheses, identical (name and full type) to the lead's `docs/one-proof/open-statements.json` at 667e0aed.
* **Comparison with the list at 3e66542b6** (before the homfree reroute, 44 hypotheses):
  * removed: `homFreeFiniteAlgClosed`, `sga3_VIB_3_10_Nbhd`, `mumfordGroupLawConn`, `neronSchemeExtensionExists`, and
    the four binders proved outright (`hW`, `hfx`, `hQ`, `hP23`);
  * added: only `neronSchemeExtensionDedekind`;
  * retyped: only `hCM`.

  Every other hypothesis has the same full type string. So no stronger statement can enter under another name.
* **Constant closure of `frozenTarget`** (271,096 constants, through definitions and proofs). Neither of the following
  occurs: `SGA3_VIB_3_10`, `SGA3_VIB_3_10_Nbhd`, `MumfordGroupLawConn`, `GZDecomp.GrossZagierHeegner`. The names that
  do match are all derived or proved:
  * `T5Glue.ShimuraMainCM` (from hCM);
  * `NeronC.NeronSchemeExtensionExists` (from the new leaf);
  * `GZOptimal.GrossZagierModuliOptAt/Cd` and `GZStatements.GrossZagierHeegnerCd` (from hGZ);
  * `HomFreeC.HomFreeFiniteC` / `homFreeFiniteC` (proved);
  * the projections `OpenTextbookLeaves{6..13}HF.homFreeFiniteAlgClosed`, whose field type is the proved
    `HomFreeC.HomFreeFiniteC` (`HomFreeFiniteAlgClosedReroute.lean:729, :2018`);
  * `AVB1.HomFreeFiniteAlgClosed._proof_4`, an auxiliary proof term that the elaborator shares (it is the only hit in
    any hypothesis's statement closure, under `charPolyIndepOfEllAlgClosed`; it is not the Prop).
* **Grep of the copies** (`NoSGA3Copy.lean`, `GoodModelIsoCopy.lean`, `TailZ48`–`50`,
  `HomFreeFiniteAlgClosedReroute.lean`). The old names occur only in three places:
  * docstrings and comments ("field `sga3_VIB_3_10` not copied");
  * the superseded bundle `OpenResearchLeaves30` (`TailZ49`), which is not an argument of `frozenTarget`;
  * the HF field `homFreeFiniteAlgClosed`, whose type is the proved `HomFreeFiniteC`.

  The copied intermediate generations narrow `mumfordGroupLaw` to `GroupLaw.MumfordGroupLawDVR` and fill it from the
  top bundle through `GoodModelIso.mumfordGroupLawDVR_of_dedekind`. That is a proof, not a hypothesis.
* `#print axioms ZInQ.OneProof.frozenTarget`: `[propext, Classical.choice, Quot.sound]`.

## 5. What was not checked

* None of the three prints was read: no network and no copies. The theorem numbers for Shimura 5.4, Lang Ch. 10 Thm 3
  and BLR 1.4 Thm 3 are UNVERIFIED. For GZ, locators.md records reads of I (6.3) p.230 and V §2 p.312, but not the
  hypotheses on φ that D3 needs.
* The direction of the Artin map was not re-checked numerically: PARI/cypari2 is not installed on this host. The
  repository's statement is in `docs/research/shimura-modfn.md` §1.
* The whole hypothesis list of `hGZ` at a concrete `d` (§3.2) was not checked.
* The other open hypotheses were outside this review: unchanged types, earlier folds.

## 6. Files

All files are in `scratch/fold33-review/`:

* `Closure.lean`, `Closure-output.txt`, `open-statements.json`: the hypothesis list, the closure search and the axioms;
* `Vacuity.lean`, `Vacuity-output.txt`: the satisfiability instances and the use sites;
* `py/chiD_check.py`, `py/chiD_check-output.txt`;
* `log.md`.

To run them: copy the leaf-fold33b build tree (`.lake/build` and `lean/.lake`) into the worktree, then run
`lake env lean scratch/fold33-review/<file>.lean`.
