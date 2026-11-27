# Level-one fixes, the JetchevKane split, and the level-N Deuring correspondence in Lean

> **Fixup (rc-hcm-v21g-fixup).** The review (docs/research/review-rc-hcm-v21g.md) found one error: `VoightThm4232Etale` quantified over all supersingular `E, E′` with nothing saying they are reached from `E₀`, and injectivity applied it to arbitrary curves, so it carried hidden GLUE; `VoightCor4237` had the same gap.
> - **Fix.** Both candidates now carry reach premises (`∃ φ₀ : Hom E₀ E, IsSeparableIsogeny φ₀`, Silverman §II.2 representations), conclusions unchanged. `nonempty_enhancedIso_of_translate` takes `rX`, `rY`; `levelDeuringClass_injective` takes `hR : SeparableReach E₀`.
> - **What the theorems rest on.** Injectivity rests on `hEt` (with its five separable-scope inputs, audit table), `hInv` and `SeparableReach E₀` (a specialization of Voight p. 786, GLUE). The order lemma rests on `hInv`, `hT` and `hV` only (inclusion plus maximality, ON THE SPOT; `VoightCor4237` is stated but unused; the fallback of item 2(iv) was not needed). `separableReach_of_primeModel` built, so the injectivity corollary `levelDeuringClass_injective_primeModel` (reference `A_k`, `A` over `F_q`) rests on `SilvermanII212PrimeModel` (UNVERIFIED, rating UNCERTAIN), `hEt`, `hInv`, `hT` and `hV`.
> - **Why the invertibility route fails.** The placement is `O₀`-linear and degree is multiplicative, so `deg ψ = c · nrd(emb ψ)` for a positive rational `c`, and the invertibility clause does not determine the `q`-adic valuation of `c`, which is exactly what separability needs.
> - **O-threading.** `RC/GoodRowWire/Assembly.lean` takes the `OperatorComparison` family `O` after `J` and passes it through; `oddStagedOfSamePlace` builds again (`lake build ZInQKernel.Contrib.OneProof.RC.GoodRowWire.Assembly`).
> - Section "Fixup: the reach from a model over `F_q`" below gives item 3; the warns are fixed in place (audit table with file:line, the 9136–9142 verdict, doc nits).

**Result: scoped stop after injectivity.** Parts (0) and (1) are complete. Part (2) fixes a supersingular reference pair `(E₀, ⟨P₀⟩)`. For it, part (2) builds in Lean:
- the map `levelDeuringClass` from isomorphism classes of supersingular enhanced elliptic curves of level `N` to `ClassSet (levelOrder q h N hN)`;
- its reference lemma;
- its order lemma (`End(E, C)` is isomorphic to the left ring of every representative of its class);
- its injectivity.

The level-one inputs are the permitted Voight candidates, stated in separable scope. Every step at level `N` is a Lean proof. Surjectivity, and hence the `Equiv`, remains (see "What remains"). Injectivity takes the reach binder `hR : SeparableReach E₀` (a specialization of Voight p. 786, GLUE); the order lemma rests on `hInv`, `hT` and `hV` only (see the fixup block).

`#print axioms` was run on 61 declarations (the 34 of the original run and 27 new or changed in the fixup; `scratch/rc-hcm-v21g/Check.lean`); every one depends only on `propext`, `Classical.choice` and `Quot.sound` (`scratch/rc-hcm-v21g-fixup/axioms.txt`). The named GLUE and print hypotheses appear as binders, never as axioms.

## Part (0): level-one fixes

New file `ZInQKernel/Contrib/OneProof/RC/HCMV21/DeuringRankFour.lean`.

| Declaration | Status |
|---|---|
| `VoightThm4219` | Printed candidate, UNVERIFIED. Voight, *Quaternion Algebras*, GTM 288 (Springer numbering), Thm 42.1.9, p. 784. The print is quoted in the docstring. Representation: `k : Type`, `[Field k]`, `[CharP k q]` (no algebraic closedness), `A : PkgI3.AbVar k` with `A.dim = 1`, and the rank hypothesis as printed, `Module.finrank ℤ A.End = 4`. The conclusion has the shape of `DeuringSupersingularEndOrder`. "Ramified at p = char F and ∞" is read as `AppF.RamifiedExactlyAtEll0Infty` (`Ram(B) = {p, ∞}`). This follows the proof on p. 785 (Main Thm 14.1.3) and Voight's own citation in §42.2, p. 787. The docstring records that the proof uses an uncited Frobenius factorization (Silverman II.2.12) and that `[p]` is purely inseparable (Silverman V.3.1). |
| `SupersingularTorsionRankFour` | GLUE bridge: trivial geometric `q`-torsion implies rank four over an algebraically closed field. This is Voight Prop. 42.1.7(ii) ⇒ rank 4, whose list Voight proves only by citing Silverman V.3.1. It is not proved in the tree: it is Deuring's rank theorem, and the tree has no dual isogenies or degrees. It is never part of a print. |
| `deuringSupersingularEndOrder_of_rankFour` | Proved: `VoightThm4219 → SupersingularTorsionRankFour → DeuringSupersingularEndOrder`. Every existing `hD`/`h : DeuringSupersingularEndOrder` is reached from the two (`DeuringHomRank.lean:50`, `GeometricTateChain.lean:26`, `RationalTateCoordinates.lean:117`, `ReferenceOrder.lean:41`, `ReferenceSpecialization.lean:75`, `ReferenceTateLevel.lean:154`). No signature changed. |
| `exists_referenceEndOrder_of_rankFour` | Proved: the rank-four variant of `exists_referenceEndOrder` (Thm 42.1.9 candidate + `QuaternionRamificationUniqueness`). |

Docstring-only edits:
- `ZInQKernel/Contrib/OneProof/RC/HCMV21/GeometricOrders.lean`: the module docstring, and `DeuringSupersingularEndOrder`, which now says its hypothesis is Voight 42.1.7(ii), not that of 42.1.9, and names `deuringSupersingularEndOrder_of_rankFour`.
- `ZInQKernel/Contrib/OneProof/RC/HCMV21/ReferenceOrder.lean`: `QuaternionRamificationUniqueness` is re-cited to Voight Main Thm 14.1.3, p. 218, restricted to `Ram B = {q, ∞}`, UNVERIFIED.

`AppF.VoightMainThm1461` is unchanged.

## Part (1): the JetchevKane split

In `ZInQKernel/Contrib/OneProof/RC/PMAdelic/Comparison.lean`:

- `JetchevKane ell h N hN hcop X` keeps only `classes`, unchanged. `hcop` is bound explicitly in the header. `#check @PMAdelic.JetchevKane` shows the same parameter list as at the base (`scratch/rc-hcm-v21g/arity.txt`). The new docstring says:
  - GLUE; tex 8465–8474;
  - cited as Jetchev–Kane §§1.1–1.2 and 2.5 (arXiv v1; journal version unread);
  - N ≥ 1 with ell prime to N, no squarefreeness;
  - Ribet 1990 Prop. 3.3 reports it without proof; a Lean proof is in progress;
  - the source's order is the endomorphism ring of a fixed enhanced curve, whereas here it is the explicit `levelOrder`, and `ell % 4 = 3` narrows the source.
- The new `OperatorComparison ell h N hN hcop X J : Prop` is declared right after it. It holds `hecke`, `atkin` and `frobenius`, with statements unchanged and `classes` read as `J.classes`. Docstring: ELLIOT; asserted in the manuscript; to be proved in Lean; tex 8480–8487, 9042, 9067–9078 / 8487–8489, 9331–9341 / 8489–8492, 9343–9358.
- `idealClasses` stays in `JetchevKane`.
- `hecke_compare`, `atkin_compare`, `frobenius_compare` and `frobenius_ss` move to `OperatorComparison`, using `include O in` with `J` implicit.

Consumers: an `O` binder is added immediately after each `J` binder (a family `∀ i` where `J` is a family), and each call site passes it. Files edited in part (1), all under `ZInQKernel/Contrib/OneProof/RC/`:

`AtkinPin/Assembly.lean`, `AtkinSign/Family.lean`, `CMScope/Selector.lean`, `O7Assemble/ActualFamily.lean`, `O7Assemble/At.lean`, `O7Assemble/Join.lean`, `O7Assemble/Stage.lean`, `O7Normalizers/Assembly.lean`, `O7Residual/Artin.lean`, `O7Residual/At.lean`, `O7Residual/Family.lean`, `Odd/Statements.lean` (docstring), `Odd/ThetaLocal.lean` (docstring), `PM/Stage.lean` (docstring), `PMAdelic/Comparison.lean`, `PMAdelic/Geometry.lean` (`geometricInput` and `geometry` take `C` and `O`; `O.frobenius_ss` etc.), `PMGeometry/Geometry.lean` (docstring), `PMQuotient/Assembly.lean`, `PMQuotient/CM.lean`, `PMQuotient/Cusps.lean`, `PMQuotient/Operators.lean`, `PMWire/Assembly.lean`, `PMWire/Fibre.lean` (`adaptComparison` is split into `adaptComparison` and `adaptOperators`), `SelectorTotal/Assembly.lean`.

The first `PMQuotient.Assembly` build flagged `AtkinSign/Family.lean:49` and `AtkinPin/Assembly.lean:81,93`; both are fixed.

The readers of `model.classes` read `GeometricInput.classes`, whose shape did not change. They were checked and not edited:
- `HCMV21/Consumer.lean:27,49`
- `HCMV21/ParametrizationSquare.lean:69`
- `PMGeometry/Heegner.lean:41,57`
- `StageKummer/Reference.lean:106,172`
- the internal readers in `PMGeometry/Geometry.lean`

Builds, one at a time (`scratch/rc-hcm-v21g/builds.txt`):
- the four sinks `AtkinPin.Specialization`, `CMScope.Selector`, `PMQuotient.Assembly` and `PMWire.Assembly`: OK;
- the nine modules edited in part (1) outside the four sinks (some only in docstrings, some in code, e.g. `PMAdelic.Comparison`, `PMAdelic.Geometry`, `PMWire.Fibre`): OK;
- `ZInQKernel.OneProof.Main` (19896 jobs) and `ZInQKernel.OneProof.Discharges`: OK.

Scratch files from other runs were left unchanged; both lists are in `builds.txt`:
- six name `JetchevKane`, two of them Lean: `scratch/rc-good-reduction/Consumers.lean`, and `scratch/rc-lane-batch-1120/AxCheck.lean`, whose lines 1307–1311 print `hecke_compare` etc., now `OperatorComparison.*`;
- twelve scratch modules import the reverse closure.

## Part (2): the level-N class correspondence

### Setting and objects

All new files are in `ZInQKernel/Contrib/OneProof/RC/HCMV21/` (namespace `ZInQ.Manuscript.RC.HCMV21`).

- `EnhancedObjects.lean`:
  - `IsSupersingular A := A.dim = 1 ∧ Module.finrank ℤ A.End = 4`. This is Voight's Def. 42.1.6 (`End(E)_ℚ` is a quaternion algebra) in rank form. Over `k = F_q^al`, the Thm 42.1.9 candidate gives the algebra from rank four, and a quaternion algebra has `ℚ`-dimension four.
  - `SupersingularEnhanced q k N`: a curve, supersingularity, a cyclic subgroup of `A.Pt k` of order `N`. It lives in `Type 1`, with `q`, `[Fact q.Prime]`, `[Algebra (ZMod q) k]`, `[IsAlgClosure (ZMod q) k]` in the header.
  - `EnhancedIso`, its equivalence relation `enhancedSetoid`, and `EnhancedClasses := Quotient`.
  - `SupersingularEnhanced.exists_generator`: `C = Subgroup.zpowers P` with `orderOf P = N`.
  - `referenceEnhanced`.
  - `exists_referenceFrame`: from the Thm 42.1.9 candidate and `QuaternionRamificationUniqueness` with `explicit_ramifiedExactlyAtEll0Infty`. No torsion bridge is used.
  - `CharP k q` and `IsAlgClosed k` are derived from `IsAlgClosure`.
- The reference pair `(E₀, P₀)` and its frame `(S, j, hmax)` are explicit parameters of every part (2) result. No existence of supersingular curves or of `P₀` is stated or assumed. Supplying a reference is outside part (2).
- `TateModuleFree` is discharged by `HDec.CMSerreTate.P1.originalTateModuleFree_proved`: in `LevelIdealTate.nonempty_tateBasis` and in `LevelDeuringMap.exists_enhancedReferenceCoordinates`.

### Arithmetic (step 8)

- `LeftIdealMirror.lean`:
  - `two_re_int_of_isIntegral` (Gauss's lemma) and `order_star_mem`: orders are stable under the standard involution.
  - left ideals (`LeftIdeal`, `rightRing`, `translate`, `LocallyPrincipal`).
  - `mirror`/`unmirror`, exchanging left and right multiplication by units.
  - `leftClassSetEquiv : LeftClassSet R ≃ ClassSet R`.
  - This is the proved mirror; Rem. 42.3.3 is not used.
- `PrimeToRepresentative.lean`: `LeftIdeal.exists_integral_primeTo`. Every locally principal left ideal of an order in a definite algebra has a right translate contained in the order and containing an integer prime to `q`. The proof approximates a local generator at `q` modulo `q` and uses Nakayama over `ℤ_q`, then clears denominators away from `q`. This is the arithmetic fact that lets the separable-scope candidates reach every class.
- `LevelOrderClasses.lean`, step 8(c):
  - `exists_levelReferenceCoordinates`. This is `detector_referenceCoordinates` with `hSplit` from `splitProfile_of_cyclicReference`, `bE := S.basis.map j.symm…` and `bT` from `TateModuleFree`. It uses no `hD`.
  - `classSetEquivOfReference : ClassSet S' ≃ ClassSet (levelOrder …)`, right multiplication by `z` on double cosets.
  - `classSetEquivOfReference_self`: the unit class goes to `fromAdelic z`.
  - `leftRing_classSetEquivOfReference`: left rings are conjugate.
  - No equality of orders is claimed.
- Step 8(b) (inverse ideals, the Lemma 42.2.22 form) is not needed and not built.

### The map, reference lemma and order lemma (steps 9–11)

- `HomPlacement S j E` (`VoightCandidates.lean`) is the Lean form of "`Hom(E, E₀)` is an invertible left `O₀`-module" (a representation choice for the reading desk). It is an injective additive map `Hom(E, E₀) → B` that intertwines postcomposition with left multiplication through `j`, and whose image is a locally principal left ideal of `S`. A placement gives the rank-four `ℤ`-basis `HomPlacement.homBasis`.
- `HomPlacementBasic.lean`:
  - any two placements differ by a right unit (`exists_unit`);
  - transport along isomorphisms;
  - `levelIdeal`: the lattice of maps sending `C` into `C₀`, a full left ideal of `levelOrderOfEndOrder S j C₀`;
  - local principality away from `N`.
- `LevelIdealTate.lean` / `LevelIdealPrincipal.lean`, local principality at `p ∣ N` (tex 9136–9142):
  - `tateToLocal`, which sends `T_p α` to the placed `α`;
  - `span_levelHom_cyclic`, the completed level lattice as the chain-preserving Tate maps (from `span_levelHom_eq_tateLevelMaps`);
  - `hfull` from `span_homT_eq_top_of_basis` with the placement basis;
  - `levelIdeal_locallyPrincipal_tate`: a chain isomorphism generates.
- `LevelDeuringMap.lean`:
  - `placedLevelIdeal_locallyPrincipal`;
  - independence of the placement (`placedLevelClass_eq`) and of the representative (`placedLevelClass_iso`);
  - **`levelDeuringClass`**: the placed level ideal, then its mirror, then the reference coordinate.
  - **`levelDeuringClass_reference`**: the reference pair goes to `⟦fromAdelic z⟧` for the chosen `z = enhancedReferenceCoordinate`.
- `EndPlacement.lean`:
  - `endRightHom`: the ring map `End(E) → B`, `ι(α ∘ γ) = ι(α) x_γ`;
  - `endRight_mem_levelRight`;
  - `endRight_injective`. The Tate maps span, so `α ∘ γ = 0` for all `α` forces `T_p γ = 0`, and then `γ` is divisible by every power of `p` in the lattice `End(E)`. A frame of `E` is used only to know that `End(E)` is a lattice.
- `LevelOrderLemma.lean`:
  - `exists_endRight_eq_level` (surjectivity onto the right order of the placed level ideal). `N x` is in the level-one right order, so it is the action of some `γ'` by the level-one order lemma `exists_endRight_eq_of_mem_rightRing`: inclusion plus maximality (ON THE SPOT, Voight's own proof of Lemma 42.2.9 done on the placement, with no `φ_I` and so no reach). The right action `End(E) → B` lands in `O_R(I)`; through the frame `(SE, jE)` of `E` (which also gives the maximality of `End(E)`) it extends to a `ℚ`-algebra automorphism `σ` of `B` (`exists_algEquiv_extend`: `Basis.constr` on the rational basis of `SE`, multiplicative on basis pairs, bijective by dimension); `σ(SE)` is a maximal order inside the order `O_R(I)` (the left order of the mirror), hence equal to it. `VoightCor4237` is not used. At each `p ∣ N` the chain isomorphism shows `p^{v_p N} ∣ T_p γ'`. `exists_eq_nsmul_of_primeTo_homT_dvd` and `exists_nsmul_of_forall_primary` give `γ' = N γ`.
  - `mem_levelHom_of_comp` (recovery of the level from the Hom lattice, through the Tate chains and `mem_of_primary_pow_mem`).
  - **`levelEndEquivRight`**: `levelEnd E ⟨Pt⟩ ≃+* rightRing(placed level ideal)`.
- `LevelDeuringOrder.lean`:
  - `LeftIdeal.mem_rightRing_iff_mem_mirror_leftRing`: in a definite algebra the right order of a left ideal is the left order of its mirror;
  - `conjSubringEquiv`;
  - **`levelDeuringClass_order`**: for every `X` and every representative `J` with `levelDeuringClass [X] = ⟦J⟧`, `Nonempty (levelEnd X.curve X.level ≃+* J.val.leftRing)`;
  - `levelDeuringClass_reference_order`. This is `Aut = R_z^×` at tex 8467–8468 at the level of rings.

### Injectivity (step 12)

`LevelDeuringInjective.lean`:
- `orderSpan_levelLattice`: the level-one ideal is the `O₀`-span of the placed level ideal. This is local: away from `N` the completions agree, and at `p ∣ N` the chain isomorphism lies in the completed level ideal and generates the completed level-one ideal over `O₀`.
- `nonempty_enhancedIso_of_translate`. If `I_N(X) u = I_N(Y)`, then `I(X) u = I(Y)`, and right multiplication by `u⁻¹` is a bijective left `O₀`-module map `Hom(E_Y, E₀) → Hom(E_X, E₀)`. The bijection clause of the Thm 42.3.2 candidate, with its reach premises `rX`, `rY` for the two curves (from `hR : SeparableReach E₀`), writes it and its inverse as `φ*`, `ψ*` with `φ, ψ` étale. The injectivity clause gives `ψ ∘ φ = 1` and `φ ∘ ψ = 1`. The level subgroups correspond by `mem_levelHom_of_comp` and a cardinality count.
- **`levelDeuringClass_injective`**.

### What remains (surjectivity, step 13, and the `Equiv`)

Every class must come from an enhanced curve. This needs Lean work only; no new print is needed. The ingredients are:
- the essential-surjectivity candidate `VoightThm4232EssSurj`, which is stated, on the integral prime-to-`q` representative of the `O₀`-span of a level ideal (local principality of `orderSpan` to prove);
- the construction of a cyclic subgroup of order `N` from the nested pair (the converse of `tateLevelPreimage`). At each `p ∣ N`, the completed level ideal is `R₀,p g` with `g = Ψ(γ_g)` for a Tate isomorphism `γ_g`. The chain `γ_g⁻¹(Y₀)` determines a cyclic subgroup of `E[p^n](k)`, through the reduction `T_p E → E[p^n]` and the bijection `levelPointsToClosure` for algebraically closed `k`, and these assemble by CRT;
- the identification of its level lattice with the given ideal, by local comparison;
- the `Equiv` as the inverse of the bijective map, with the reference and order lemmas restated.

Estimated size: 600–900 lines of Lean. No new statement is needed beyond the candidates already stated.

## Audit table (step 14)

| Hypothesis on the path | Where (binder file:line) | Verdict |
|---|---|---|
| `hT : VoightThm4219` | `HCMV21/EnhancedObjects.lean:148` (`exists_referenceFrame`); `HCMV21/LevelOrderLemma.lean:376` (`exists_endRight_eq_of_mem_rightRing`, frame and maximality of `End(E)`), `:415`, `:537`; `HCMV21/LevelDeuringOrder.lean:63`, `:93`, `:111` | level-one (Thm 42.1.9 candidate). Not in separable scope: it involves no isogeny or ideal. |
| `hV : QuaternionRamificationUniqueness` | same lines as `hT` | level-one (Main Thm 14.1.3 candidate). |
| `S, j, hmax` (frame of `E₀`) | section variables `HCMV21/LevelDeuringMap.lean:211–215`, `HCMV21/LevelDeuringOrder.lean:53–58`, `HCMV21/LevelDeuringInjective.lean:133–139`; supplied by `exists_referenceFrame` (`HCMV21/EnhancedObjects.lean:148`) | level-one (Thm 42.1.9 + 14.1.3). |
| `h₀ : IsSupersingular E₀`, `P₀`, `hP₀` | same section variables | reference pair (Voight's setting 42.3.1 fixes `E₀`). Supplying it is outside part (2). |
| `hInv : VoightThm4232Invertible` | `HCMV21/LevelDeuringMap.lean:181`, `:235`; `HCMV21/LevelDeuringOrder.lean:58`; `HCMV21/LevelDeuringInjective.lean:139` | level-one (Thm 42.3.2 candidate, invertibility clause). Unrestricted as printed; no isogeny involved. |
| `hEt : VoightThm4232Etale` | `HCMV21/LevelDeuringInjective.lean:154` (`nonempty_enhancedIso_of_translate`), `:282` (`levelDeuringClass_injective`); candidate at `HCMV21/VoightCandidates.lean:208` | level-one (Thm 42.3.2 candidate, bijection clause on étale maps, with reach premises). Applied to bijective module maps and to `ψ ∘ φ`, `1`. Separable-scope inputs (five): (1) the reach premise: `SeparableReach E₀` for the ∀-statements, `rX`/`rY` per curve; as a statement it is a specialization of Voight p. 786 (GLUE), and it stays the binder of the part (2) theorems; rating of `SeparableReach`: derivable in Lean from `SilvermanII212PrimeModel` (UNVERIFIED, rating UNCERTAIN) for a reference `A_k` with `A` over `F_q` (`separableReach_of_primeModel`, `HCMV21/PrimeModelReach.lean:343`, with `hInv`, `hT`, `hV`); (2) Voight Prop. 42.2.16 (GLUE, Nehrkorn); (3) Voight Exercise 16.11 (step 8(b), not built); (4) the Silverman III.4.11 reading of Lemma 42.2.7; (5) the step of 42.2.21's separable branch "for separable φ, ker φ is étale and deg φ = #ker φ is prime to q" (reading-desk inference: Silverman III.4.10(c), and `E₀[q](k) = 0` from Voight 42.1.7(ii), proved there only by citing Silverman V.3.1). |
| reach premises `rX`, `rY`, `hR` | `HCMV21/LevelDeuringInjective.lean:158–159` (`rX`, `rY`), `:282` (`hR : SeparableReach E₀`); `SeparableReach` at `HCMV21/VoightCandidates.lean:89` | the source-fixed instance of `SeparableIsogenyExists` (Voight p. 786, GLUE); binder of injectivity. No order declaration takes a reach binder. |
| `hCor : VoightCor4237` | not used: the order lemma no longer uses `VoightCor4237`; candidate stated at `HCMV21/VoightCandidates.lean:294` with its reach premise | level-one candidate (Cor. 42.3.7 / Lemma 42.2.9), unused. Its own separable-scope inputs (docstring): its reach premise and the Silverman III.4.11 reading of Lemma 42.2.7 through 42.2.9. |
| `VoightThm4232EssSurj` | stated at `HCMV21/VoightCandidates.lean:227`; unused | level-one candidate, unused. |
| `SeparableIsogenyExists` | stated at `HCMV21/VoightCandidates.lean:256`; on no path | GLUE (Voight p. 786, Springer printing; deleted in Voight's errata, replaced in v1.0.7u by Cor. 42.2.28, which is itself GLUE). The two-curve Prop is on no path; its source-fixed instance `SeparableReach E₀` (`separableReach_of_separableIsogenyExists`, `:262`) binds the part (2) theorems. |
| `SilvermanII212PrimeModel` | `HCMV21/PrimeModelReach.lean:285`; binder of `separableReach_of_primeModel` (`:343`) and `levelDeuringClass_injective_primeModel` (`:376`) | printed candidate (Silverman AEC Cor. II.2.12, prime-model form), UNVERIFIED until the owner's page check, rating UNCERTAIN (direct instance or GLUE: the reading desk decides). No fall in the GLUE count is claimed. Representations: `primeFrobBC ^ r` for Silverman's `q^r`-power Frobenius (`primeFrobBC_pt`, `:107`, the named identification on `k`-points), `IsSeparableMor`, `IsNonconstant`. Teeth (a) proved (`base_genericPoint_of_isNonconstant`, `:197`); teeth (b) (`primeFrobBC` is not `IsSeparableMor`) open: flagged for the skeptic reader's vacuity check. |
| `separableReach_of_primeModel` and its corollary | `HCMV21/PrimeModelReach.lean:343`, `:376` | Lean, ON THE SPOT (provenance (c)). Rests on `SilvermanII212PrimeModel`, `hInv`, `hT`, `hV` (and `hq : q % 4 = 3`); the corollary `levelDeuringClass_injective_primeModel` adds `hEt` (no new GLUE: `hT`, `hV` are existing candidates). The corollary needs the reference to come from some `A` over `F_q`, strictly stronger than a supersingular `E₀` over `k`; supplying `A`, like supplying `E₀`, is outside part (2), and no nonzero AbVar can be built at this pin (`ZInQKernel/HDecomp/Objects.lean:393–395`). |
| Where the separable-scope inputs enter | — | Prop. 42.2.16, Exercise 16.11, the Silverman III.4.11 reading of Lemma 42.2.7 (with 42.2.22) and the étale-kernel step enter through `hEt`. None enters through the order lemma. |
| Order lemma by inclusion plus maximality | `HCMV21/LevelOrderLemma.lean:308` (`exists_algEquiv_extend`), `:376` (`exists_endRight_eq_of_mem_rightRing`) | Lean, ON THE SPOT (provenance (c); Voight's proof of Lemma 42.2.9 done on the placement, no `φ_I`, no reach). |
| Level ideal locally principal | `levelIdeal_locallyPrincipal_tate`, `levelIdeal_locallyPrincipal_away`, `placedLevelIdeal_locallyPrincipal` | level-N proved |
| Placement independence / iso invariance | `HomPlacement.exists_unit`, `placedLevelClass_eq`, `placedLevelClass_iso` | level-N proved |
| `End(E₀, C₀)` Eichler order identified with `levelOrder` on class sets | `exists_levelReferenceCoordinates`, `classSetEquivOfReference`, `leftRing_classSetEquivOfReference` | level-N proved (no `hD`). |
| Order lemma | `levelEndEquivRight` (`HCMV21/LevelOrderLemma.lean:537`), `levelDeuringClass_order` (`HCMV21/LevelDeuringOrder.lean:93`) | level-N proved from `hInv`, `hT` and `hV` only. |
| Injectivity | `orderSpan_levelLattice`, `mem_levelHom_of_comp`, `levelDeuringClass_injective` (`HCMV21/LevelDeuringInjective.lean:282`) | level-N proved from `hEt` (étale, with its five inputs), `hInv` and `hR : SeparableReach E₀`. |
| Surjectivity / `Equiv` | not built | **open**, this lane (see "What remains"). |
| `JetchevKane.classes` | `PMAdelic/Comparison.lean:88` | GLUE, open: a Lean proof in this lane (the present construction once surjective), then the bridge to the consumer's coarse fibre, owned by the O.7 integral-model lane. |
| `OperatorComparison` (`hecke`, `atkin`, `frobenius`) | `PMAdelic/Comparison.lean:95` | ELLIOT, open: the next run in this lane. |

None of the hD-taking lemmas (`end_basis_of_deuring`, `span_homT_eq_top_of_deuring`, `exists_rationalTate_coordinates_of_deuring`, `exists_referenceEndOrder`, `detector_referenceCoordinates_of_cyclic`, `exists_detectorEndOrder`) is used in part (2). The GLUE bridge of part (0) does not enter part (2).

## Fixup: the reach from a model over `F_q`

New file `ZInQKernel/Contrib/OneProof/RC/HCMV21/PrimeModelReach.lean` (imports `LevelDeuringInjective`, `AbsFrob.Basic`, `AbsFrob.Sanity`).

Route (the reviewer's design note, checked against the prints): take the reference with a model over `F_q`, `E₀ = A_k`. The invertibility clause (with `E` as the reference and `E₀` as the curve) gives a nonzero `α : E₀ → E`. By Silverman Cor. II.2.12, `α` is a power of the `q`-power Frobenius `E₀ → E₀^(q^r)` followed by a separable map, and `E₀^(q^r) = E₀` because `E₀`'s coefficients lie in `F_q`. The separable factor fixes the origin and is multiplicative, so it is a homomorphism, and it is nonconstant because `α` is. This replaces Voight's unproved p. 786 sentence for such a reference. Baker, González-Jiménez, González and Poonen take the same step inside the proof of their Lemma 3.21 (arXiv math/0211394v2; Amer. J. Math. 127 (2005), journal version unread, UNVERIFIED). Silverman's AEC is cited by the manuscript (tex 11144–11145) and used elsewhere (III.7.4 at tex 1572, V.1.1 at tex 1591).

| Declaration | Status |
|---|---|
| `frO`, `frO_naturality`, `frO_unit`, `frO_tensor`, `primeFrob` (`:51`–`:82`) | Lean. The absolute Frobenius of an `F_q`-scheme as a morphism over `Spec F_q` (`fr_naturality`, `fr_Spec_zmod`); `IsMonHom` from naturality on `η`, `μ` and the product projections. |
| `primeFrobBC` (`:85`), `primeFrobBC_left_fst` (`:91`), `primeFrobBC_pt` (`:107`) | Lean. `primeFrobBC = bcHom k A A (primeFrob q A)`; `primeFrobBC_pt`: on a `k`-point `P`, read in `A`, `Frob ∘ P = P ∘ Spec(x ↦ x^q)`, the named identification with Silverman's coordinatewise `q`-power map. |
| `surjective_primeFrobBC`, `surjective_pow_hom`, `surjective_tensorHom` (`:127`–`:149`) | Lean (base change of a surjection, `MorphismProperty.overPullbackMap` / `pullbackMap`). |
| `isNonconstant_of_ne_zero` (`:169`) | Lean (Mathlib's `ext_of_apply_eq` over the algebraically closed `k`). |
| `base_genericPoint_of_isNonconstant` (`:197`) | Lean, teeth (a): a nonconstant map of one-dimensional abelian varieties sends the generic point to the generic point, so `IsSeparableMor` is separability of `k(A)/f^* k(B)`. |
| teeth (b): `primeFrobBC` is not `IsSeparableMor` when `dim = 1` | **open.** Missing: the stalk map of `primeFrobBC` at the generic point (write the absolute Frobenius of `A_k` as `primeFrobBC ∘ (id × Fr_k)` with `id × Fr_k` an isomorphism, so separability over `primeFrobBC^*` is separability of `K/K^q`) and the non-perfectness of the function field `K` of a curve (a uniformizer at a closed point is not a `q`-th power; the DVR stalk needs `SmoothOfRelativeDimension 1` from `Smooth` and `dim = 1`). Estimated 300–500 lines. Smallest faithful statement: `¬ IsSeparableMor (primeFrobBC q k A).hom` for `(A.baseChange k).dim = 1`. Until it exists the candidate is only as strong as `IsSeparableMor` at `r = 0`; flagged for the skeptic reader's vacuity check. |
| `SilvermanII212PrimeModel` (`:285`) | Printed candidate, UNVERIFIED until the owner's page check of Silverman II.2.12 and the reading desk's two-lens pass; rating UNCERTAIN (direct instance of II.2.12 or GLUE, the desk decides: it uses `C₁^(q^r) = C₁` for `F_q` coefficients and the identification of Silverman's `q^r`-power map with `primeFrobBC ^ r`). No fall in the GLUE count is claimed. Specializations and representations in the docstring. |
| `isMonHom_of_frob_comp` (`:304`), `isNonconstant_of_comp` (`:327`) | Lean, the factor lemma: unit by `η ≫ Frob^r = η`; multiplicativity after cancelling the dominant `Frob^r × Frob^r` on the reduced `A_k × A_k` (`ext_of_isDominant_of_isSeparated`; reducedness from `isReduced_of_flat_of_finite_irreducibleComponents`). |
| `separableReach_of_primeModel` (`:343`) | Lean, ON THE SPOT (provenance (c)), sketch in the docstring. From `hS`, `hInv`, `hT`, `hV`, `hq : q % 4 = 3` and `h₀ : IsSupersingular (A.baseChange k)`. Recorded as a rating of `SeparableReach`: "derivable in Lean from `SilvermanII212PrimeModel` (UNVERIFIED, rating UNCERTAIN)", never as LEAF or as discharged. |
| `levelDeuringClass_injective_primeModel` (`:376`) | Lean corollary at `E₀ := A.baseChange k`; adds `hT`, `hV` as binders (existing candidates, no new GLUE). The part (2) theorems keep `SeparableReach E₀` as their binder; which binder a later fold uses is the lead's call under the no-same-count-swap rule. |
| `isSeparableIsogeny_of_isEtaleIsogeny` | open (optional, not attempted). |

Weighed and not used: Waterhouse 1969, §3.2 (kernel ideals `H(I)` as finite subgroup schemes; Thm 3.15). It is stated over a finite field with `End_k` maximal and does not state the reach. Deriving the reach from it needs Nehrkorn (an ideal of norm prime to `q` in the class), the invariance of `A/H(I)` under the class, and the descent from `F̄_q` to a finite field with all endomorphisms defined, ruled an unprinted bridge (GLUE) on 11-23.

## Printed candidates and convention

Voight's convention throughout: left `O₀`-modules, `O₀ = End(E₀)` acting on `Hom(E, E₀)` by postcomposition, and the contravariant functor `φ ↦ φ*`, `φ*(ψ) = ψφ` (42.3.4). Nothing is mirrored in a candidate; the mirror is used only in Lean, to reach the right-ideal `ClassSet`.

All are UNVERIFIED until the reading desk's two-lens pass.

| Candidate | Locator | Scope |
|---|---|---|
| `VoightThm4219` | Thm 42.1.9, p. 784 (proof p. 785) | as printed |
| `QuaternionRamificationUniqueness` | Main Thm 14.1.3, p. 218 | restricted to `Ram B = {q, ∞}` |
| `VoightThm4232Invertible` | Thm 42.3.2, p. 791, invertibility clause (print quoted, typo "defines and" noted) | unrestricted |
| `VoightThm4232Etale` | Thm 42.3.2, bijection clause | étale maps only, with reach premises for `E` and `E′` |
| `VoightThm4232EssSurj` | Thm 42.3.2, essential surjectivity | integral invertible left ideals containing an integer prime to `q` |
| `VoightCor4237` | Cor. 42.3.7, p. 792; ring statement from Lemma 42.2.9, p. 788 | integral ideals containing an integer prime to `q`, with a reach premise `∃ φ₀ : Hom E₀ E, IsSeparableIsogeny φ₀`; stated, unused |
| `SeparableIsogenyExists` | sentence after Lemma 42.1.11, p. 786 (Springer printing; deleted in the errata, replaced by Cor. 42.2.28 in v1.0.7u) | GLUE (unproved in every Voight version); stated, on no path |

The module docstring of `VoightCandidates.lean` (lines 10–16) quotes the sentence of 42.2.4, p. 787, on which the inseparable case rests; the candidate docstrings refer to it.

Strict weakness of the hypotheses taken by part (2) theorems:
- `VoightThm4232Invertible` says nothing about levels, cyclic subgroups, `levelOrder` or class sets. It only places one `Hom` module.
- `VoightThm4232Etale` says nothing beyond `N = 1`: it compares maps of curves with module maps.
- `VoightCor4237` is a level-one ring statement for one placement (unused).
- The reach binder `SeparableReach E₀` says nothing about levels, cyclic subgroups, `levelOrder` or class sets: it asks only for one separable isogeny `E₀ → E` per supersingular `E`.
- None mentions `End(E, C)` or Eichler orders, and none asserts that pairs correspond to classes.

The Thm 42.3.2 candidate implies the `N = 1` case of the target, as the owner ruled for this permitted leaf. For `N > 1` and the class-set form, the level-`N` ideal, its local principality, the identification with `levelOrder`, the order lemma and injectivity are all Lean proofs.

## Count delta

None. The count tracks Theorem 5.3 as `RestrictedConverseGenuine` (`docs/one-proof/OPEN.md:462–469`), and `JetchevKane` is no `docs/one-proof` row.

## Known issues

- **Jetchev–Kane scope.** arXiv v1 §1.1 states `N ≥ 1` with ell prime to `N`. `docs/theorem-application-audit/INVENTORY.md:1510` (row A052) gives `N > 1`. The "citation scope error at tex 8468–8474" in `docs/research/rc-hcm-v21f.md:5` and `:89` rested on that row and is withdrawn: the scope of the cited source covers level one. However, the cited source does not prove the correspondence: §2.5 refers to Ribet's Prop. 3.3, which reports it without proof. INVENTORY.md is not edited.
- **Integrality in the separable-scope candidates.** "Ideal containing an integer prime to `q`" is only meaningful for integral ideals: some rational translate contains `1`. `VoightThm4232EssSurj` and `VoightCor4237` therefore require `I ⊆ O₀` as well, and `exists_integral_primeTo` supplies such representatives.
- **The Cor. 42.3.7 candidate (unused) is stated for a placement.** It is invariant under moving the placement by a right unit (both sides conjugate), so stating it for an admissible placement of the class loses nothing (docstring).
- **Voight errata.** Springer numbering is used throughout. Errata item 125 (display (42.2.18)) is not cited. The printed slips in Ch. 42 are not copied.
- **Voight p. 786 is GLUE in every version.** The sentence after Lemma 42.1.11 ("there exists a separable isogeny E → E′") is in the Springer printing (p. 786). Voight's errata and addenda (the author's PDF of 2026-08-05, Addenda item 17; UNVERIFIED, one reader) delete it; in the online v1.0.7u that the manuscript cites (tex 11241–11245) it is replaced by Cor. 42.2.28 (p. 777), whose proof uses Cor. 42.2.21 (its inseparable branch goes through 42.2.15 to the asserted 42.2.4), Lemma 42.2.7 and Exercise 17.5 (Nehrkorn). Nehrkorn's density argument is not a re-cite: it needs a link between degree and `nrd` at `q`, which is not printed for a general `Hom`.
- **Partial withdrawal of the v21f scope error in other lanes (for the integrator; not edited here).** `docs/research/pm-adelic-join.md:115–121`, `:131`, `docs/research/rc-pm-geometry.md:93–99` and `docs/research/rc-stage-kummer.md:55`, `:66` still assert the v21f "citation scope error at tex 8468–8474", which this run's report withdraws.
- **Stale locator outside this lane (for the integrator).** `RC/GoodRowWire/Row.lean:12` (module docstring) and `:72` cite `RC/PMWire/Assembly.lean:120–122` for `G`; on this branch `G` is at `:122–124`.
- **Silverman II.2.12 locators from memory.** Cor. II.2.12 (§II.2, pp. 19–27; the author's errata corrects a notation in the last line of its proof, p. 27, line 1) and III.4.10(c), III.4.11, V.3.1 are cited from memory, UNVERIFIED until the owner's page check. The candidate paraphrases II.2.12 and does not quote it (no permitted copy, no network).
- **Reserved tokens.** `ι` and `γ` are reserved tokens in this scope, so Lean names use `emb` and `gam`; docstrings keep the printed letters.

## Manuscript check

| Tex | Step | Verdict |
|---|---|---|
| 8462–8463 | `B/ℚ` ramified exactly at ell₀ and ∞ by Main Thm 14.6.1 | OK for existence as cited. The manuscript cites the author's PDF v1.0.7u; the number is the same in the Springer edition. Uniqueness, used for the frame, is Main Thm 14.1.3 (candidate). |
| 8464–8466 | `R` Eichler of level `N`; supersingular pairs are `B^×\B̂^×/R̂^×` | gap filled for the map and injectivity (`levelDeuringClass`, `levelDeuringClass_injective`), from the level-one candidates and the reach binder `hR : SeparableReach E₀`. Surjectivity is open. The explicit `levelOrder` is Eichler (`levelOrder_isEichler`); `End(E₀, C₀)` is identified with it on class sets. |
| 8467–8468 | automorphism groups `R_z^×`, `R_z = B ∩ z R̂ z⁻¹` | gap filled at the level of rings (`levelDeuringClass_order`, `levelDeuringClass_reference_order`), by inclusion plus maximality (Voight's proof of Lemma 42.2.9 on the placement, ON THE SPOT) from `hInv`, `hT` and `hV`; `VoightCor4237` is not used. |
| 8468–8469 | every `N` prime to ell₀, including powers of two | OK: all part (2) results take any `N ≥ 1` prime to `q`, including `N = 1` and powers of two. |
| 8469–8473 | scalar Frobenius over `F_{ell₀²}`; coarse points over that field | unverified (not part of this run; ELLIOT `frobSS`). |
| 8473–8474 | attribution to Jetchev–Kane §§1.1–1.2, 2.5 | unverified. The source's scope is `N ≥ 1` (arXiv v1 §1.1), so the v21f scope error is withdrawn. The source states the description and refers to Ribet Prop. 3.3, which gives no proof. |
| 8480–8492 | Hecke, Atkin–Lehner and Frobenius compatibilities | unverified (ELLIOT; `OperatorComparison`, next run). |
| 9136–9142 | local orbits; the Eichler lattice pair's cyclic quotient at `p^e ∥ N` | unverified (orientation classification not in this run); only the cyclic-chain form at 9140–9142 is used. Tex 9136–9148 classifies local orientations (`2^(ω(N)+1)` of them); the Lean proves local principality of the Hom level ideal at `p ∣ N` through a chain isomorphism of Tate modules (`levelIdeal_locallyPrincipal_tate`), and away from `N` from level one. |
