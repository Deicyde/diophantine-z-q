# Level-one fixes, the JetchevKane split, and the level-N Deuring correspondence in Lean

> **Review correction (2026-11-25): not fold-ready.** The review of this branch at 2630f292 found one error, and it changes what part (2) rests on. Full review: docs/research/review-rc-hcm-v21g.md. Line numbers below are at 2630f292.
> - `levelDeuringClass_injective` and `nonempty_enhancedIso_of_translate` (HCMV21/LevelDeuringInjective.lean:212-215, :276) apply `VoightThm4232Etale` to arbitrary supersingular curves. That candidate (HCMV21/VoightCandidates.lean:90-98) quantifies over every supersingular `E, E′`, although its docstring (:87-89) says it reaches a curve only through an étale isogeny from `E₀`.
> - In separable scope, injectivity therefore rests on `SeparableIsogenyExists` (GLUE: Voight p. 786 asserts it without proof). It also rests on Prop. 42.2.16 (Nehrkorn), Exercise 16.11 and the Silverman III.4.11 reading of Lemma 42.2.7.
> - Three statements in this report are therefore wrong: "used by no theorem" in the summary, "not through `SeparableIsogenyExists`" in the `hEt` row, and "not used" for 42.2.16, 16.11 and 42.2.7.
> - The order lemma has the same gap through `VoightCor4237`, which applies Lemma 42.2.9 to the given `E` and so needs `E ≅ E_I`.
> - Soundness is unaffected: every candidate is a hypothesis, and none is false or stronger than Voight's print.
> - Planned fixup: reach premises on `VoightThm4232Etale` and `VoightCor4237`, and `SeparableIsogenyExists` as an explicit hypothesis of injectivity and of the order lemma. Then derive the reach from printed statements instead of Voight p. 786.
> - Interaction with wip/rc-goodrow-wire: merged with that branch on main 162d4636 (checks27), GoodRowWire/Assembly.lean fails with 9 errors. Part (1) gives `Reference` an operator family `O`, which that file does not pass. Agreed order: the wiring lands first, then this branch's fixup threads `O` through GoodRowWire/Assembly.lean.

**Result: scoped stop after injectivity.** Parts (0) and (1) are complete. Part (2) fixes a supersingular reference pair `(E₀, ⟨P₀⟩)`. For it, part (2) builds in Lean:
- the map `levelDeuringClass` from isomorphism classes of supersingular enhanced elliptic curves of level `N` to `ClassSet (levelOrder q h N hN)`;
- its reference lemma;
- its order lemma (`End(E, C)` is isomorphic to the left ring of every representative of its class);
- its injectivity.

The level-one inputs are the permitted Voight candidates, stated in separable scope. Every step at level `N` is a Lean proof. Surjectivity, and hence the `Equiv`, remains (see "What remains"). No new print was needed and no stop rule fired. The only GLUE Prop of part (2), `SeparableIsogenyExists`, is stated but used by no theorem.

All new declarations depend only on `propext`, `Classical.choice` and `Quot.sound` (`scratch/rc-hcm-v21g/axioms.txt`).

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
- the nine docstring-edited modules: OK;
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
  - `exists_endRight_eq_level` (surjectivity onto the right order of the placed level ideal). `N x` is in the level-one right order. The Cor. 42.3.7 candidate is applied to a placement translated to an integral ideal containing an integer prime to `q` and gives `γ'`. At each `p ∣ N` the chain isomorphism shows `p^{v_p N} ∣ T_p γ'`. `exists_eq_nsmul_of_primeTo_homT_dvd` and `exists_nsmul_of_forall_primary` give `γ' = N γ`.
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
- `nonempty_enhancedIso_of_translate`. If `I_N(X) u = I_N(Y)`, then `I(X) u = I(Y)`, and right multiplication by `u⁻¹` is a bijective left `O₀`-module map `Hom(E_Y, E₀) → Hom(E_X, E₀)`. The bijection clause of the Thm 42.3.2 candidate writes it and its inverse as `φ*`, `ψ*` with `φ, ψ` étale. The injectivity clause gives `ψ ∘ φ = 1` and `φ ∘ ψ = 1`. The level subgroups correspond by `mem_levelHom_of_comp` and a cardinality count.
- **`levelDeuringClass_injective`**.

### What remains (surjectivity, step 13, and the `Equiv`)

Every class must come from an enhanced curve. This needs Lean work only; no new print is needed. The ingredients are:
- the essential-surjectivity candidate `VoightThm4232EssSurj`, which is stated, on the integral prime-to-`q` representative of the `O₀`-span of a level ideal (local principality of `orderSpan` to prove);
- the construction of a cyclic subgroup of order `N` from the nested pair (the converse of `tateLevelPreimage`). At each `p ∣ N`, the completed level ideal is `R₀,p g` with `g = Ψ(γ_g)` for a Tate isomorphism `γ_g`. The chain `γ_g⁻¹(Y₀)` determines a cyclic subgroup of `E[p^n](k)`, through the reduction `T_p E → E[p^n]` and the bijection `levelPointsToClosure` for algebraically closed `k`, and these assemble by CRT;
- the identification of its level lattice with the given ideal, by local comparison;
- the `Equiv` as the inverse of the bijective map, with the reference and order lemmas restated.

Estimated size: 600–900 lines of Lean. No new statement is needed beyond the candidates already stated.

## Audit table (step 14)

| Hypothesis on the path | Where | Verdict |
|---|---|---|
| `hT : VoightThm4219` | `HCMV21/EnhancedObjects.lean` (`exists_referenceFrame`), `HCMV21/LevelOrderLemma.lean` (`levelEndEquivRight`, frame of `E` for injectivity) | level-one (Thm 42.1.9 candidate). Not in separable scope: it involves no isogeny or ideal. |
| `hV : QuaternionRamificationUniqueness` | same | level-one (Main Thm 14.1.3 candidate). |
| `S, j, hmax` (frame of `E₀`) | parameters of every part (2) result; supplied by `exists_referenceFrame` from `hT`, `hV` and `explicit_ramifiedExactlyAtEll0Infty` | level-one (Thm 42.1.9 + 14.1.3). |
| `h₀ : IsSupersingular E₀`, `P₀`, `hP₀` | parameters | reference pair (Voight's setting 42.3.1 fixes `E₀`). Supplying it is outside part (2). |
| `hInv : VoightThm4232Invertible` | `HCMV21/LevelDeuringMap.lean` (`levelLeftClass`), every map statement | level-one (Thm 42.3.2 candidate, invertibility clause). Unrestricted as printed, a clean clause; no isogeny involved. |
| `hCor : VoightCor4237` | `HCMV21/LevelOrderLemma.lean` (`exists_endRight_eq_level`) | level-one (Cor. 42.3.7 / Lemma 42.2.9 candidate). Used only on a placement whose ideal is integral and contains an integer prime to `q` (`exists_integral_primeTo`): **prime to `q`**. Lemma 42.2.9 applies (42.1.4) to `φ_I`; **this use is marked on the spot here**, with `nrd(I)` prime to `q`. |
| `hEt : VoightThm4232Etale` | `HCMV21/LevelDeuringInjective.lean` | level-one (Thm 42.3.2 candidate, bijection clause on étale maps). Applied to bijective module maps, giving étale `φ, ψ`, and to the étale maps `ψ ∘ φ` and `1`: **prime to `q`** (étale). It reaches the curves through placements, not through `SeparableIsogenyExists`. |
| `VoightThm4232EssSurj`, `SeparableIsogenyExists` | stated in `HCMV21/VoightCandidates.lean`; not used by any theorem | level-one candidate / GLUE (Voight p. 786, unproved there; re-cite candidate Nehrkorn), unused. |
| Prop. 42.2.16, Exercise 16.11, Lemma 42.2.7 and 42.2.22 forms | not used | — |
| Level ideal locally principal | `levelIdeal_locallyPrincipal_tate`, `levelIdeal_locallyPrincipal_away`, `placedLevelIdeal_locallyPrincipal` | level-N proved |
| Placement independence / iso invariance | `HomPlacement.exists_unit`, `placedLevelClass_eq`, `placedLevelClass_iso` | level-N proved |
| `End(E₀, C₀)` Eichler order identified with `levelOrder` on class sets | `exists_levelReferenceCoordinates`, `classSetEquivOfReference`, `leftRing_classSetEquivOfReference` | level-N proved (no `hD`). |
| Order lemma | `levelEndEquivRight`, `levelDeuringClass_order` | level-N proved from `hCor` (prime to `q`). |
| Injectivity | `orderSpan_levelLattice`, `mem_levelHom_of_comp`, `levelDeuringClass_injective` | level-N proved from `hEt` (étale). |
| Surjectivity / `Equiv` | — | **open**, this lane (see "What remains"). |
| `JetchevKane.classes` | `PMAdelic/Comparison.lean` | GLUE, open: a Lean proof in this lane (the present construction once surjective), then the bridge to the consumer's coarse fibre, owned by the O.7 integral-model lane. |
| `OperatorComparison` (`hecke`, `atkin`, `frobenius`) | `PMAdelic/Comparison.lean` | ELLIOT, open: the next run in this lane. |

None of the hD-taking lemmas (`end_basis_of_deuring`, `span_homT_eq_top_of_deuring`, `exists_rationalTate_coordinates_of_deuring`, `exists_referenceEndOrder`, `detector_referenceCoordinates_of_cyclic`, `exists_detectorEndOrder`) is used in part (2). The GLUE bridge of part (0) does not enter part (2).

## Printed candidates and convention

Voight's convention throughout: left `O₀`-modules, `O₀ = End(E₀)` acting on `Hom(E, E₀)` by postcomposition, and the contravariant functor `φ ↦ φ*`, `φ*(ψ) = ψφ` (42.3.4). Nothing is mirrored in a candidate; the mirror is used only in Lean, to reach the right-ideal `ClassSet`.

All are UNVERIFIED until the reading desk's two-lens pass.

| Candidate | Locator | Scope |
|---|---|---|
| `VoightThm4219` | Thm 42.1.9, p. 784 (proof p. 785) | as printed |
| `QuaternionRamificationUniqueness` | Main Thm 14.1.3, p. 218 | restricted to `Ram B = {q, ∞}` |
| `VoightThm4232Invertible` | Thm 42.3.2, p. 791, invertibility clause (print quoted, typo "defines and" noted) | unrestricted |
| `VoightThm4232Etale` | Thm 42.3.2, bijection clause | étale maps only |
| `VoightThm4232EssSurj` | Thm 42.3.2, essential surjectivity | integral invertible left ideals containing an integer prime to `q` |
| `VoightCor4237` | Cor. 42.3.7, p. 792; ring statement from Lemma 42.2.9, p. 788 | integral ideals containing an integer prime to `q` |
| `SeparableIsogenyExists` | sentence after Lemma 42.1.11, p. 786 | GLUE (unproved in Voight) |

The candidate docstrings quote the sentence of 42.2.4, p. 787, on which the inseparable case rests.

Strict weakness of the hypotheses taken by part (2) theorems:
- `VoightThm4232Invertible` says nothing about levels, cyclic subgroups, `levelOrder` or class sets. It only places one `Hom` module.
- `VoightThm4232Etale` says nothing beyond `N = 1`: it compares maps of curves with module maps.
- `VoightCor4237` is a level-one ring statement for one placement.
- None mentions `End(E, C)` or Eichler orders, and none asserts that pairs correspond to classes.

The Thm 42.3.2 candidate implies the `N = 1` case of the target, as the owner ruled for this permitted leaf. For `N > 1` and the class-set form, the level-`N` ideal, its local principality, the identification with `levelOrder`, the order lemma and injectivity are all Lean proofs.

## Count delta

None. The count tracks Theorem 5.3 as `RestrictedConverseGenuine` (`docs/one-proof/OPEN.md:462–469`), and `JetchevKane` is no `docs/one-proof` row.

## Known issues

- **Jetchev–Kane scope.** arXiv v1 §1.1 states `N ≥ 1` with ell prime to `N`. `docs/theorem-application-audit/INVENTORY.md:1510` (row A052) gives `N > 1`. The "citation scope error at tex 8468–8474" in `docs/research/rc-hcm-v21f.md:5` and `:89` rested on that row and is withdrawn: the scope of the cited source covers level one. However, the cited source does not prove the correspondence: §2.5 refers to Ribet's Prop. 3.3, which reports it without proof. INVENTORY.md is not edited.
- **Integrality in the separable-scope candidates.** "Ideal containing an integer prime to `q`" is only meaningful for integral ideals: a fractional translate always contains `1`. `VoightThm4232EssSurj` and `VoightCor4237` therefore require `I ⊆ O₀` as well, and `exists_integral_primeTo` supplies such representatives.
- **The Cor. 42.3.7 candidate is stated for a placement.** It is invariant under moving the placement by a right unit (both sides conjugate), so stating it for an admissible placement of the class loses nothing (docstring).
- **Voight errata.** Springer numbering is used throughout. Errata item 125 (display (42.2.18)) is not cited. The printed slips in Ch. 42 are not copied.
- **Reserved tokens.** `ι` and `γ` are reserved tokens in this scope, so Lean names use `emb` and `gam`; docstrings keep the printed letters.

## Manuscript check

| Tex | Step | Verdict |
|---|---|---|
| 8462–8463 | `B/ℚ` ramified exactly at ell₀ and ∞ by Main Thm 14.6.1 | OK for existence as cited. The manuscript cites the author's PDF v1.0.7u; the number is the same in the Springer edition. Uniqueness, used for the frame, is Main Thm 14.1.3 (candidate). |
| 8464–8466 | `R` Eichler of level `N`; supersingular pairs are `B^×\B̂^×/R̂^×` | gap filled for the map and injectivity (`levelDeuringClass`, `levelDeuringClass_injective`), from the level-one candidates. Surjectivity is open. The explicit `levelOrder` is Eichler (`levelOrder_isEichler`); `End(E₀, C₀)` is identified with it on class sets. |
| 8467–8468 | automorphism groups `R_z^×`, `R_z = B ∩ z R̂ z⁻¹` | gap filled at the level of rings (`levelDeuringClass_order`, `levelDeuringClass_reference_order`), from the Cor. 42.3.7 candidate in separable scope. |
| 8468–8469 | every `N` prime to ell₀, including powers of two | OK: all part (2) results take any `N ≥ 1` prime to `q`, including `N = 1` and powers of two. |
| 8469–8473 | scalar Frobenius over `F_{ell₀²}`; coarse points over that field | unverified (not part of this run; ELLIOT `frobSS`). |
| 8473–8474 | attribution to Jetchev–Kane §§1.1–1.2, 2.5 | unverified. The source's scope is `N ≥ 1` (arXiv v1 §1.1), so the v21f scope error is withdrawn. The source states the description and refers to Ribet Prop. 3.3, which gives no proof. |
| 8480–8492 | Hecke, Atkin–Lehner and Frobenius compatibilities | unverified (ELLIOT; `OperatorComparison`, next run). |
| 9136–9142 | local orbits; the Eichler lattice pair's cyclic quotient at `p^e ∥ N` | gap filled for the geometric level ideal: local principality at `p ∣ N` through a chain isomorphism of Tate modules (`levelIdeal_locallyPrincipal_tate`), and away from `N` from level one. |
