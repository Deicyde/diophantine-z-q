# rc-same-place1: the moduli-side coarse fibre X, first part

**None yet.** This run completes no field of `GoodRowWire.SamePlaceData` and discharges no hypothesis of
`GoodRowWire.oddStagedOfSamePlace`.

No error verdict.

Main result: all of items 1–7 are built. Every module compiles with no `sorry` and no axiom declaration.
`#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every new declaration.
The INTERFACE block is unchanged and composes with items 3, 4 and 6 (types read and checked; see Composition).

Pieces supplied, by field of `SamePlaceData`:

* **`X.Point`**: the supersingular locus `ssPoint K ell N`, the pair classes `PairClasses K N` whose curve has
  `E[ell](K) = {0}`, with `X.ss = univ` intended. The reason for the supersingular locus: `frobenius_sq`
  fails on ordinary points, and `J` reaches only the supersingular locus (the lead's ruling R2).
* **`point`**: `SamePlace.point h₅ htame h₂ K x := (pointForm h₅ htame h₂ K).symm ((Pinned.Y0LevelPoints h₅ htame h₂).symm x.val)`.
  It is injective.
* **`point_W`**: supplied here are `pointForm`, the φ lemma `pointForm_comp_map` (item 3(b)), `point` and
  `sigmaQ`/`sigmaQSS`. Still open:
  * generic7's `atkinLevelAlg`, `Wint` lemma and `PointW`;
  * generic8's `atkinLevel_moduli_special`;
  * SP2's `X.W` comparison for every separable seam.

  The point_W assembly then proves `PointW` for this lane's point map and builds the final `sp`.
* **`point_frob`**: supplied here is the Frobenius form `pointForm_residueFrob` (item 3(c)), which is the
  `pointForm` half, together with `frobeniusAlgHom_eq_frobenius`. The `Y0LevelPoints` half is SP2's.
* **`X.frobenius`**: `frobTwistSS ell`, the `ell`-power Frobenius twist `E ↦ E.map (frobenius K ell)` on
  supersingular pair classes. It is the moduli twist, never `J ∘ uniformizer ∘ J⁻¹`.
* **`X.W`**: `sigmaQSS ell hq he hNk h2k`, the moduli σ_Q through a chosen separable seam. It is never
  `J ∘ atkin ∘ J⁻¹`.
* **`frobenius_sq`**: `frobenius_involutive`, derived from `O.frobenius` and `uniformizer_involutive`. It is
  therefore ELLIOT, through `O`.

X is **not constructed**. `frobenius_involutive` is a lemma for any `X` with `X.ss = univ`, any `J` and any `O`.
It does not cover a concrete `X`, since none exists until SP2 assembles one; that assembly needs `X.T`.

## Files (ZInQKernel/Contrib/OneProof/RC/SamePlace/, namespace `ZInQ.Manuscript.RC.SamePlace`)

| File | Items | Commit |
| --- | --- | --- |
| `Supersingular.lean` | 2 | 6a1c4b87d |
| `PointForm.lean` | 3, 4 | a39316b0e |
| `FrobeniusTwist.lean` | 5 | d116d00bd |
| `AtkinLehner.lean` | 6 | 211c8484e |
| `FrobeniusSquare.lean` | 7 | 4810a1201 |

Item 1 (the doc fixes) is commit 20ec445fc.

## Statements

Throughout, `K : Type` is a field with `[DecidableEq K]`. The `LocalIntegers ell`-structure on `K` is
`resAlgebra ell K := (ModelTarget.resRing ell K).toAlgebra`, an abbrev used as a local instance.

### Item 2 (Supersingular.lean)

* `IsSupersingular (ell : ℕ) (E : WeierstrassCurve K) [E.IsElliptic] : Prop := Submodule.torsionBy ℤ E.toAffine.Point (ell : ℤ) = ⊥`.
  This is the standard definition. `ell` is an explicit argument; the predicate is not defined through `ringChar K`.
* `isSupersingular_iff`: `IsSupersingular ell E ↔ ∀ P, (ell : ℤ) • P = 0 → P = 0`.
* `torsionBy_eq_bot_congr (e : G ≃+ H) n`: `torsionBy ℤ G n = ⊥ ↔ torsionBy ℤ H n = ⊥`.
* `isSupersingular_variableChange`: `IsSupersingular ell (v • E) ↔ IsSupersingular ell E`, through
  `Point.addEquivVariableChange`.
* `isSupersingular_congr`: transport along `E = E'`.
* `EnhancedCurve.IsSupersingular` and `PairClasses.IsSupersingular ell : PairClasses K N → Prop`, defined by
  `Quot.lift`. The simp lemma is `isSupersingular_mk`.
* `ssPoint K ell N := {x : PairClasses K N // PairClasses.IsSupersingular ell x}`.

### Items 3–4 (PointForm.lean)

Here `[Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)` and `[Algebra (ZMod ell) K]`.

* `pointForm h₅ htame h₂ K : (residueSource ell K ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj (Pinned.Y0Level h₅ htame h₂)) ≃ (Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] K)`.
  It is the composite of three equivalences:
  1. `(Over.mapPullbackAdj _).homEquiv … |>.symm`;
  2. `overHomEquiv`: `v ↦ ⟨v.left, (Over.w v).trans (residue_structure ell K)⟩`, with inverse `Over.homMk`, both
     inverse laws `rfl`;
  3. `Spec.homEquivAlgHom`.
* `spec_pointForm`: `Spec.map (ofHom (pointForm P)) = P.left ≫ pullback.fst _ _`.
* **φ lemma** `pointForm_comp_map (φ : A →ₐ[LocalIntegers ell] A) (f : Y0Level ⟶ Y0Level) (hf : letI := ModelGeneric5.levelCommRing h₅ htame h₂; f.left = Spec.map (CommRingCat.ofHom (φ : A →+* A))) P : pointForm (P ≫ (Over.pullback _).map f) = (pointForm P).comp φ`.
  The hypothesis is stated under `levelCommRing`, as the brief asks. In a scratch check, `hf` closed by `rfl`
  at `f = Wint h₅ htame h₂ (isExactDivisor_primePow)` and `φ = {atkinLevel with commutes' := atkinLevel_algebraMap}`.
* `frobAlg ell K : K →ₐ[LocalIntegers ell] K` is the ring map `FiniteField.frobeniusAlgHom (ZMod ell) K` of `residueFrob`.
* `frobeniusAlgHom_eq_frobenius [CharP K ell] : (FiniteField.frobeniusAlgHom (ZMod ell) K : K →+* K) = frobenius K ell`,
  and `frobAlg_toRingHom`. SP2's point_frob needs these.
* **Frobenius form** `pointForm_residueFrob : pointForm (residueFrob ell K ≫ P) = (frobAlg ell K).comp (pointForm P)`.
* The following need `[IsAlgClosed K]`:
  * `point h₅ htame h₂ K : ssPoint K ell N → (residueSource ell K ⟶ (Over.pullback …).obj (Pinned.Y0Level h₅ htame h₂))`;
  * `pointForm_point`;
  * `Y0LevelPoints_pointForm_point`;
  * `point_injective`.
* Auxiliary: `algHom_ext_spec`, `spec_homEquivAlgHom`, `spec_ofHom_comp`, `specOf`, `specOf_injective`.

### Item 5 (FrobeniusTwist.lean)

* `mapAlong_changePoints (φ : F →+* L) W V v (h : v • W = V) (h' : v.map φ • W.map φ = V.map φ) P : mapAlong φ (changePoints W V v h P) = changePoints (W.map φ) (V.map φ) (v.map φ) h' (mapAlong φ P)`.
* The following are stated for a bijective `σ : K →+* K` (`hσ : Function.Bijective σ`):
  * `twistPoints σ hσ E : E(K) ≃+ (E.map σ)(K)`, defined as `Point.mapAlong σ`;
  * `twistSubgroup`;
  * `twistEnhanced`;
  * `pairTwist σ hσ : PairClasses K N → PairClasses K N`, well defined through `pairClasses_eq_iff`.
* `isSupersingular_map : IsSupersingular ell (E.map σ) ↔ IsSupersingular ell E`, and `pairTwist_isSupersingular`.
* With `[Fact ell.Prime] [CharP K ell] [PerfectRing K ell]`:
  * `frobTwist ell := pairTwist (frobenius K ell) (bijective_frobenius K ell)`;
  * `frobTwistSS ell : ssPoint K ell N → ssPoint K ell N`.

  At `ResidueAt v`, `PerfectRing` comes from `IsAlgClosed`.

### Item 6 (AtkinLehner.lean)

* (a) `smulSubgroup_cyclic (hN : N ≠ 0) (hQ : Q ∣ N) C (hC : IsAddCyclic C ∧ Nat.card C = N) : IsAddCyclic (smulSubgroup (N / Q) C) ∧ Nat.card (smulSubgroup (N / Q) C) = Q`.
* `SepSeam E H n` is a structure with fields `elliptic`, `ι`, `isIntegral`, `finite : FiniteAlong K ι`,
  `finrank : finrankAlong K ι = n`, `g`, `ker : g.ker = H` and `seam : ModelGeneric6.IsSeam ι isIntegral g`.
  `SepSeam.choose` picks one, from `ModelGeneric6.exists_quotientSeam`.
* (b) `sigmaEnhanced hq he hQe hQ hNk h2k A` is the class
  `Quot.mk _ ⟨_, S.elliptic, ModelGeneric6.atkinImage A.equation hq he hQe (Nat.mul_div_cancel' hQ.dvd).symm hQ.coprime hNk h2k A.subgroup S.g S.ker⟩`,
  where `S = atkinSeam hQ hNk A` is the chosen separable seam at `C_Q = (N/Q) • C`.
  * `sigmaAt … x := sigmaEnhanced … (Quot.out x)`.
  * `sigmaQ hq he hNk h2k := sigmaAt hq he rfl (isExactDivisor_primePow) hNk h2k`, at `Q = q^(v_q N)`.
* (c) The surjectivity results:
  * `separableAlong_of_coprime ell ι hfin (hcop : (finrankAlong K ι).Coprime ell) : SeparableAlong K ι`. It uses the
    vendored `Algebra.IsSeparable.of_coprime_finrank_expChar`, applied under `algebraAlong ι`.
  * `surjective_of_isSeam ι hι g hfin hsep hseam : Function.Surjective g`. It uses the vendored
    `Place.restrictAlong_surjective` and the gate's `pointEquivPlace`.
  * `SepSeam.surjective ell S (hcop : n.Coprime ell)`.
* (d) Preservation of supersingularity:
  * `torsionBy_eq_bot_of_surjective g hg (hker : Nat.card g.ker = Q) (hcop : Q.Coprime ell)`, a group lemma;
  * `sigmaEnhanced_isSupersingular`;
  * `sigmaAt_isSupersingular`;
  * `sigmaQSS ell hq he hNk h2k : ssPoint K ell N → ssPoint K ell N`.

### Item 7 (FrobeniusSquare.lean)

* `neg_one_mem_localUnits R p : (-1) ∈ localUnits R p`.
* `divisionUnit_val : divisionUnit ell h = ⟨0, 0, 1, 0⟩`.
* `divisionUnit_sq : Π * Π = algebraMap ℚ_[ell] _ (-(ell : ℚ_[ell]))`, a coordinate computation with `QuaternionAlgebra.mk_mul_mk`.
* (a) `uniformizer_involutive : Function.Involutive (Adelic.uniformizer ell h N hN)`, and
  `uniformizerOnDoubleCosets_involutive`.
* (b) `frobenius_involutive {X} (hss : X.ss = Set.univ) (J : PMAdelic.JetchevKane ell h N hN hcop X) (O : PMAdelic.OperatorComparison ell h N hN hcop X J) : Function.Involutive X.frobenius`.

Three points about `frobenius_involutive`:

* It inherits O's ELLIOT status.
* A future discharge of O must not assume `frobenius_sq`.
* The moduli route is a direct proof of `frobenius_sq` that would remove its dependence on O. It is recorded
  here and not built: tex 8469–8473, a model over F_{ell²} with scalar Frobenius, so every supersingular pair
  class is F_{ell²}-rational (UNVERIFIED). Discharging `O.frobenius` (tex 8489–8490) itself needs the
  identification of the Frobenius isogeny with the uniformizer ideal.

### Provenance of adapted text

These blocks follow generic7's variant terms: a provenance line sits above each block, and the names are in this namespace.

* `smulSubgroup_cyclic` adapts the order computation of `ModelGeneric6.isAddCyclic_map_atkinSum`
  (RC/ModelGeneric6/Cyclicity.lean:140-159, base 8b140cd2a).
* In `uniformizer_involutive`, the away-from-`ell` branch and the centrality step adapt `Adelic.atkin_involutive`
  (RC/Adelic/Operations.lean:166-178 and :180-189, base 8b140cd2a).

The private `divisionUnit` and `diagonal_scalar_val` are reached with `open private`; no private declaration is edited.

## Composition with the INTERFACE block

I read the types only and did not paste the block anywhere.

* **`point`**: `PointW`'s `point` argument has type `X.Point → (PMQuotient.residueSource ell K ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj (Pinned.Y0Level h₅ htame h₂))`.
  At `X.Point = ssPoint K ell N` this is exactly the type of `point h₅ htame h₂ K`.
* **Shared structure**: the same `Pinned.Y0LevelPoints h₅ htame h₂` and the same `(ModelTarget.resRing ell K).toAlgebra`.
* **φ lemma**: it holds for every `LocalIntegers ell`-algebra endomorphism. I checked that it applies to `Wint` by
  `rfl` against an `AlgHom` with ring map `atkinLevel`; generic7's `atkinLevelAlg` is that `AlgHom`.
* **σ_Q**: its value is the block's class expression, with seam data `IsSeam`, `FiniteAlong` and `finrankAlong = Q`.

A separate scratch check confirmed that `point` and `frobTwistSS` elaborate at `K = PMGeometry.ResidueAt v`.
That needs `open scoped Classical` for `DecidableEq`, as the tree does.

## What remains

| Piece | Owner | Tier | Reduces to |
| --- | --- | --- | --- |
| X assembly (SP2), needs X.T | SP2 | medium (once X.T exists) | assembly of this run's pieces; X.T is the moduli Hecke correspondence (Eichler–Shimura; Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, 1971, §7.3, UNVERIFIED) |
| X.T (the moduli Hecke correspondence on supersingular pair classes) and the HeckePacket agreement | SP2 | large missing theory | the `p+1` cyclic `p`-isogenies, i.e. the Brandt matrix as Hecke operator (Gross, *Heights and the special values of L-series*, CMS Conf. Proc. 7, 1987, Prop. 2.7, UNVERIFIED) |
| hCM-class -> ssPoint bridge (SP2) | SP2 | medium | from `levelDeuringClass` (RC/HCMV21/LevelDeuringMap.lean:241) on `EnhancedClasses` (RC/HCMV21/EnhancedObjects.lean:112) to `ssPoint`; Deuring correspondence (Voight, *Quaternion Algebras*, 2021, Thm. 42.3.2, UNVERIFIED) |
| X.W comparison for every separable seam (uniqueness of separable quotients up to variable change) | SP2 | medium | Silverman, *The Arithmetic of Elliptic Curves*, 1986, Prop. III.4.12 (textbook route only, never a leaf; UNVERIFIED) |
| point_frob (identification of `frobTwist` with generic7's `PairClasses.map` along Frobenius; naturality of `Y0LevelPoints`) | SP2 (with generic7's naturality) | medium | this run's `pointForm_residueFrob` and `frobeniusAlgHom_eq_frobenius` give the pointForm half |
| SamePlaceData assembly; CMDiagram and HeckePacket agreements, with PointW as a hypothesis | SP2 | medium | assembly |
| PointW and the final sp (the point_W assembly) | the point_W assembly | cheap extraction (once the inputs land) | generic8's `atkinLevel_moduli_special`, generic7's `atkinLevelAlg` and `Wint` lemma, SP2's X.W comparison, and this run's `pointForm_comp_map`, `point` and `sigmaQ` |
| A direct proof of frobenius_sq (removing the dependence on O) | unassigned | large missing theory | supersingular curves have a model over F_{ell²} with Frobenius = [±ell] (Waterhouse, *Abelian varieties over finite fields*, Ann. Sci. ENS 1969, Thm. 4.1, UNVERIFIED) |
| O itself (`OperatorComparison`: hecke, atkin, frobenius) | hCM lane | large missing theory | ELLIOT; Jetchev–Kane does not print them (see Known issues) |

## Known issues

* **Stale wording outside this run's edit rights**, listed for the integrator. Each item still names the hCM lane
  as owner of the same-place data, or the old generic5-item-4 input:
  * Lean docstrings: RC/GoodRowWire/SamePlace.lean:12, :28-29; RC/GoodRowWire/Assembly.lean:73;
    RC/GoodRowWire/Row.lean:21-22, :57;
  * docs/research/rc-model-target.md:15-16, :61, :63, :169;
  * .fleet/rc-model-target.md:25-26;
  * docs/research/rc-model-neron.md:69, :82;
  * docs/research/rc-model-generic4.md:51, :53, :55, :69, :70;
  * docs/research/rc-goodrow-wire.md:111 (the relations row; Relations.hecke keeps that owner) and :147-149
    (HeckePacket.source_eq and target_eq, which SP2 now states through X.T).
* **Accepted duplicates, for the fold**:
  * `smulSubgroup_cyclic` duplicates generic7's Cyclicity piece;
  * `pairTwist`/`frobTwist` duplicates generic7's characteristic-free `PairClasses.map` along a ring isomorphism.
    SP2 proves the identification.
* **The choice of separable seam** is fixed by `Classical.choice` in `SepSeam.choose`, and the representative by
  `Quot.out`. Independence of both choices (so that σ_Q is the canonical moduli map) is SP2's X.W comparison and
  is not used or claimed here. In characteristic `ell`, a seam followed by Frobenius is still a seam, so only
  separable seams (degree `Q`) are allowed, and `SepSeam` records the degree.
* **`IsSupersingular` takes `ell` explicitly** and is meant for `K` of characteristic `ell`. It is not
  `ringChar`-based; for such `K` the two agree.
* **`sigmaQ` and `sigmaQSS` take `hNk : (N : K) ≠ 0` and `h2k : (2 : K) ≠ 0` as arguments**, the inputs of
  `atkinImage`. At `ResidueAt v` these follow from `CharP`, `5 ≤ ell` and `¬ ell ∣ N`; SP2's assembly supplies them.
* **Inherited known issues**:
  * The Milne locators at tex 1784–1788 do not state the normalized-newform and Hecke claims.
  * Jetchev–Kane (arXiv v1; journal version unread), cited at tex 8468–8474, cites the class correspondence to
    Ribet 1990 Prop. 3.3 and does not print the Hecke, Atkin–Lehner or Frobenius compatibilities. The class
    correspondence is GLUE, and the three compatibilities are ELLIOT, to be proved in Lean.
  * Ribet 1990 Prop. 3.6 is the citable converse. Prop. 3.3 and Rem. 3.5 defer their proofs to other works and
    are never cited as sources.
  * The level-N correspondence is being built in Lean in the hCM lane.
  * Cornut–Jetchev 2010 §§4.9–4.10 (UNVERIFIED) still needs a checked refereed locator.
* **Print locators**: none is in the docs desk's checked table, so every print locator in this report is UNVERIFIED.

## Manuscript check

| Step | tex | Verdict |
| --- | --- | --- |
| Supersingular pairs as the double cosets `B^×\B̂^×/R̂^×`; the standard supersingularity definition `E[ell] = 0` used for X.Point | 8462–8468 | OK (definition only; the class correspondence is J, GLUE) |
| Each supersingular curve has a model over F_{ell²} with scalar Frobenius; its cyclic subgroups are stable; so the coarse points are F_{ell²}-rational | 8469–8473 | unverified (not formalized; recorded as the direct route to frobenius_sq) |
| Special-fibre points of the good-reduction model at the place (`point`, `pointForm`) | 8476–8479 | gap filled (pointForm, an assembly of Mathlib and tree results, provenance (c)) |
| Hecke compatibility | 8479–8486 | unverified (X.T is SP2's; not built here) |
| Atkin–Lehner `W_{p^e}` on supersingular points (σ_Q as a moduli map; preservation of supersingularity) | 8486–8489 | gap filled (σ_Q through a separable seam; preservation of the supersingular locus proved, provenance (c)) |
| Frobenius acts on the supersingular set (twist; preservation of the locus) | 8489–8490 | gap filled (Frobenius twist on pair classes and supersingularity proved, provenance (c)) |
| Frobenius acts as the right division-uniformizer operation | 8489–8490 | unverified (this is O.frobenius, ELLIOT; used, not proved) |
| Uniformizer eigenvalue +1 (the uniformizer operation is an involution; `Π² = −ell`) | 8490–8492 | OK (uniformizer_involutive proved; frobenius_sq follows from O) |
