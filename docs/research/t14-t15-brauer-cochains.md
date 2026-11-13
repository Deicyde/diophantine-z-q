# T14/T15: Brauer `H²` bundle forms versus the cochain forms consumed by the glue

Issue 37, phase 2. Proof-only, non-release contribution proposal. **Preliminary**: written and
self-checked by an AI agent (model identity not recorded). No independent review, no Astra
acceptance, no registration, no provider for `ZInQ.Targets.H.T14`/`T15`.

## 1. Result in one paragraph

The frozen reference targets T14 (`T14a ∧ T14b`) and T15 are, by `Iff.rfl`, the base-main
bundle leaves `PkgI6.BrauerHasse2`, `PkgI6.BrauerReciprocity2` and `PkgI6.LocalH2Card`, stated
over Mathlib's `continuousCohomology`. The glue on main consumes different, *not definitionally equal* forms: the
cochain leaves `PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC` (continuous `ZMod 2`
inhomogeneous cochains) and the descent leaves `GlueDescent.B2Q.LeafHasse`, `LeafLocalTwo`
(locally constant `ℂˣ` sign cochains, finite places only). This contribution **proves**, with no
hypotheses and only the axioms `propext`, `Classical.choice`, `Quot.sound`:

1. a comparison of Mathlib's `continuousCohomology 2 X` (homogeneous resolution, homology in
   `TopModuleCat`) with continuous — equivalently, for discrete coefficients, locally constant —
   inhomogeneous 2-cocycles modulo coboundaries of continuous 1-cochains, for every locally
   compact topological group and every topological representation with trivial action, natural
   in every continuous homomorphism and coefficient map (localization, inflation);
2. `PkgI6.BrauerHasse2 ↔ PkgI6.BrauerHasse2C`, `PkgI6.BrauerReciprocity2 ↔
   PkgI6.BrauerReciprocity2C`, `PkgI6.LocalH2Card ↔ PkgI6.LocalH2CardC` (all primes including
   `2`, and the real place);
3. the real place of T15 outright, in both forms: `H²(G_ℝ, ℤ/2)` has exactly two elements;
4. `LeafHasse` from T14 and `LeafLocalTwo` from the `p`-adic part of T15 (bundle or cochain form).

**Not proved:** T14a, T14b and the `p`-adic part of T15 themselves (global and local class field
theory). They remain explicit hypotheses of the theorems in item 4; nothing is assumed as an axiom,
`Fact` or instance, and no predicate is weakened.

## 2. Scope, base and owned files

- Base: `main` at `a5937595cde3e3db00975b81e5171cdef92c801a`; branch `work/issue37-phase2-brauer`;
  changes left uncommitted. Lean `4.35.0`, Mathlib `v4.35.0`
  (`56a005855ea17e0b0958f73ec801ae140b0a1679`); no pin, lakefile, manifest, registry, checker,
  policy, root or baseline source changed.
- Owned and changed: only `ZInQKernel/Contrib/BrauerCohomology/*.lean` (six new modules) and this
  note. The modules are not imported by any root; the checker builds tracked `Contrib` modules.
- Manuscript/TeX/PDF release duties do not apply: no record, headline, manuscript or registered
  target changes.

| Module | Role | SHA-256 |
|---|---|---|
| `TopHomology.lean` | elementwise homology in `TopModuleCat` (ported, Apache-2.0, §8) | `892cd0344a2d3a9f95ec1b838ea258ddc88515e46eac21c06a48bde1926c9775` |
| `Comparison.lean` | homogeneous ↔ inhomogeneous cochains, classes, zero criterion | `b87edc397e2159a359dc488d207a254de7487bb7f1b27185b98ecc91df1595ab` |
| `Functoriality.lean` | naturality, `Z²/B² ≃+ H²`, two-element criterion | `29fc181138571d2df57a609473bbe8029378ef0055dea40ac60744274d4da3a2` |
| `Galois.lean` | Galois specialization; bundle ↔ cochain equivalences | `4792235a3b2c2bdac9a0b0ec47694ca64e074d5d6982d22505e29d38b43e4186` |
| `Real.lean` | real place | `b4255706c35a281983c946b6f486d931480f5dc4a65d4812310a2911b91a97c4` |
| `Glue.lean` | sign cochains; `LeafHasse`, `LeafLocalTwo` | `bf45019485ae020551e239ac636656e23794b62961bd7cb6eefe17cd4bec9881` |

## 3. Sources read (frozen)

Base main, compared with `KERNEL_CONTRACT.json` (hashes agree with the lock):

| File | SHA-256 | Used for |
|---|---|---|
| `ZInQKernel/HDecomp/Conductor/I6Base.lean` | `3a2688e5271203cb1d28663fefe3c017426a43dd4c5f4a710f0dabe6de96ce2d` | `Z2`, `loc`, `locP`, `locInf`, bundle and cochain leaves, `resC`, `H2TwoClasses`, `cob_of_same_finite_support` |
| `ZInQKernel/HDecomp/Descent/B2Glue.lean` | `bd7e603f92928ff3f34121d053be9d945b82968200486fb77ea3a22a968cd545` | `IsSignCocycle`, `SignCob`, `dB`, `pull`, `resp`, `LeafHasse`, `LeafLocalTwo` |
| `ZInQKernel/HDecomp/Conductor/Dyadic.lean` | `d52d6ce0e3b7ff34ca30b2a06d382c1c65255aa19510e945d1638b907795072a` | imported by `I6Base` only |
| `ZInQKernel/HDecomp/Descent/Cochain.lean` | `cd63dd6f550c4b777e428166c1f73c137b9c0b25b52fab025e3363adce50aa59` | read; group-theoretic B2–B3 core, no Brauer input |

Frozen reference, PR #41 head `2757349fbd8ca613340b679bbd149f78c2baba6b`, **unregistered**,
statement reference only (hashes agree with its `REFERENCE.json`):
`ZInQKernel/Targets/H/T14.lean` `3980b7fdb48281733728534e5b324b60169ad4d1b94a02f99f6c70a0218ea2bf`,
`ZInQKernel/Targets/H/T15.lean` `5a599f41fd55f15d195f17d5c0c5999726624813c7758fbf830b1497d76b252a`.

Mathlib `v4.35.0`:

| File | SHA-256 |
|---|---|
| `RepresentationTheory/Homological/ContCohomology/Basic.lean` | `36377f09d8a539040e80626b6263de8a1fc715d927086aeb987e24c22135927c` |
| `RepresentationTheory/Homological/ContCohomology/Functoriality.lean` | `6ac09a368cda240cc9d7170113909e0605b7f9a6064d8a27b7bb53681679011d` |
| `Algebra/Category/ModuleCat/Topology/Homology.lean` | `6a43c2bfe421c85025996e3d9e25d0178b5a0b46f529e6a49f83f642a73cdab6` |
| `RepresentationTheory/Continuous/Basic.lean` | `a3138468b8c9e8e4afcc8bbdea4dfafc4d83e5a7657b1b8206afb302c334b955` |
| `RepresentationTheory/Continuous/TopRep.lean` | `d084437a837258cbe59ae3306018f9a35c10cb073b971792b8081c528251d3a2` |
| `FieldTheory/AbsoluteGaloisGroup.lean` | `2c032f24a0be4112eec973ed12a23e2aee25bdfc8e02810e7b5882835a3e7cb0` |
| `FieldTheory/Galois/Profinite.lean` (`CompactSpace Gal(K/k)`, line 329) | `fc73d2ca5d71085e817689303741f1e98e52856b0f52efe34abd480605c11897` |
| `Topology/Instances/ZMod.lean` (`ZMod n` discrete) | `1e90e84426475ff4f6b14c863c0b881c5e4018de49efe7a75a0f600297fefbeb` |

Tau Ceti (`TauCetiProject/TauCeti`), revision `61090fff281d0c6cece0176aa8436ab748b53048`, GitHub
source archive SHA-256 `b092f9e2bfbc977bb676d20f371955aded8c2c4c2a6f96d9b0957e07f4a3bd88`;
`lean-toolchain` `leanprover/lean4:v4.36.0-rc2`; Mathlib pin
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`; Apache-2.0, `LICENSE` SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, no `NOTICE` file. See §7.

## 4. Definitions, coefficients and conventions compared

| Item | Bundle form (T14/T15, `I6Base`) | Cochain form (`…2C`, `I6Base`) | Glue form (`B2Glue`) |
|---|---|---|---|
| Group | `Field.absoluteGaloisGroup K = Gal(K̄/K)`, Krull topology | same | same (`GQ`, `GQp p`) |
| Coefficients | `Z2 K = TopRep.of (ContRepresentation.trivial ℤ G (ZMod 2))`; restricted via `TopRep.res` | `ZMod 2`, functions `G → G → ZMod 2` | `ℂˣ` with `η² = 1` |
| Topology on coefficients | `ZMod 2` with `⊥` (discrete) | same | `IsLocallyConstant` (no topology used) |
| Action | trivial | trivial (implicit) | trivial (implicit) |
| Cochains | homogeneous, invariant `C(G, C(G, C(G, ZMod 2)))` | continuity of `(a, b) ↦ ε a b` on `G × G` | local constancy of `uncurry η` |
| Differential | `d₀ = const`, `dₙ₊₁ F = const F − dₙ ∘ F` | `ε b c − ε (ab) c + ε a (bc) − ε a b` | `η (xy) z · η x y = η y z · η x (yz)` |
| Coboundary | image of degree-1 homogeneous cochains | `f b − f (ab) + f a`, `f` continuous | `γ x γ y / γ (xy)`, `γ` locally constant, `γ² = 1` |
| Localization | `loc F 2 = ContinuousCohomology.map (absoluteGaloisGroup.map (algebraMap ℚ F)) (𝟙 _) 2` | `resC F ε = ε ∘ (map × map)` with the same map | `pull (resp p)`, `resp p` the same map |
| Places | all primes and `ℝ`; reciprocity counts `ℝ` | all primes and `ℝ` | finite primes only |
| Cardinality | `Nat.card (continuousCohomology 2 …) = 2` | `H2TwoClasses`: a nontrivial class exists, two nontrivial classes differ by a coboundary | `LeafLocalTwo`: at most two classes |

Checked identifications (now Lean theorems, §5):

- `d₃` at `(1, a, ab, abc)` is exactly `ε b c − ε (ab) c + ε a (bc) − ε a b` for
  `ε a b = F 1 a (ab)`; the image of a homogeneous 1-cochain `E` at `(1, a, ab)` is exactly
  `f b − f (ab) + f a` with `f = E 1` (`d23_toHC2_eq_zero_iff`, `cls_eq_zero_iff`). No sign,
  order or normalization is changed; cochains are not normalized on either side.
- `ContinuousCohomology.map φ f` acts on nested cochains by `F ↦ f ∘ F ∘ φ`, so on inhomogeneous
  coordinates it is `ε ↦ f ∘ ε ∘ (φ × φ)`; with `f = 𝟙` and `φ = absoluteGaloisGroup.map
  (algebraMap ℚ F)` this is literally `resC F` (`loc_clsQ`). Both sides use the *same* term, so the
  choice of embedding `ℚ̄ → F̄` made by `IsAlgClosed.lift` is the same; no
  independence-of-embedding argument is needed or claimed.
- `μ₂ = {±1} ≅ ℤ/2` canonically over every field of characteristic `≠ 2`; the glue's sign
  cochains are identified with `ZMod 2` cochains by `ofSign` (`signCob_iff_isCoboundary2`). For a
  discrete target, continuity is local constancy (`isInhCocycle2_iff_isLocallyConstant`).
- The comparison needs `LocallyCompactSpace G` (exponential law, `ContinuousMap.uncurry`). For
  `K` of characteristic zero, `IsAlgClosure.isGalois` and Mathlib's `CompactSpace Gal(K/k)` give
  compactness; this covers `ℚ`, `ℚ_[p]` and `ℝ` (`locallyCompactSpace_absoluteGaloisGroup`).

## 5. Lean results

Namespace `ZInQ.Contrib.BrauerCohomology` unless stated. `X : TopRep k G`, `hX : IsTrivialAction X`
(`∀ g v, X.ρ g v = v`).

Comparison (`Comparison.lean`, `Functoriality.lean`):

- `IsInhCocycle2 ε`, `IsInhCoboundary2 ε`: the `PkgI6` predicates verbatim for any coefficient
  module; `isCocycle2_iff`/`isCoboundary2_iff` are `Iff.rfl` for `ZMod 2`.
- `cls hX ε hε : continuousCohomology 2 X`, the class of the homogeneous cocycle
  `(x₀, x₁, x₂) ↦ ε (x₀⁻¹ x₁) (x₁⁻¹ x₂)`.
- `cls_surjective [LocallyCompactSpace G]`, `cls_eq_zero_iff`, `cls_sub`.
- `map_cls hX hY φ f ε hε : (ContinuousCohomology.map φ f 2).hom (cls hX ε hε) =
  cls hY (pull2 φ f ε) _`, for every `φ : H →ₜ* G` and `f : res φ X ⟶ Y` with `Y` trivial;
  `map_id_cls` is the case `f = 𝟙` (restriction or inflation).
- `h2AddEquiv [LocallyCompactSpace G] hX : (Z2inh X ⧸ (B2inh X).addSubgroupOf (Z2inh X)) ≃+
  continuousCohomology 2 X`.
- `natCard_eq_two_iff [LocallyCompactSpace G] hX : Nat.card (continuousCohomology 2 X) = 2 ↔
  H2TwoClassesOf X`.

Galois specialization (`Galois.lean`):

- `brauerHasse2_iff : PkgI6.BrauerHasse2 ↔ PkgI6.BrauerHasse2C`
- `brauerReciprocity2_iff : PkgI6.BrauerReciprocity2 ↔ PkgI6.BrauerReciprocity2C`
- `localH2Card_iff : PkgI6.LocalH2Card ↔ PkgI6.LocalH2CardC`
- `t14_bundle_iff_cochain : (BrauerHasse2 ∧ BrauerReciprocity2) ↔ (BrauerHasse2C ∧
  BrauerReciprocity2C)`
- `natCard_Z2res_eq_two_iff F : Nat.card (continuousCohomology 2 (Z2res F)) = 2 ↔
  H2TwoClasses (Field.absoluteGaloisGroup F)` (any `F` of characteristic zero over `ℚ`)
- `cob_of_same_finite_support_of_bundle`: the cochain Brauer step of B2 from the bundle targets.

Real place (`Real.lean`):

- `h2TwoClasses_real : PkgI6.H2TwoClasses (Field.absoluteGaloisGroup ℝ)`
- `natCard_h2_real : Nat.card (continuousCohomology 2 (TopRep.res (absoluteGaloisGroup.map
  (algebraMap ℚ ℝ)) (Z2 ℚ))) = 2` — the second conjunct of T15.
- `localH2Card_iff_padic`, `localH2CardC_iff_padic`: T15 (either form) is exactly its `p`-adic
  part.

Glue (`Glue.lean`):

- `leafHasse_of_cochain (hH : BrauerHasse2C) (hR : BrauerReciprocity2C) : LeafHasse`
- `leafLocalTwo_of_cochain (hC : ∀ p [Fact p.Prime], H2TwoClasses (absoluteGaloisGroup ℚ_[p])) :
  LeafLocalTwo`
- `leafHasse_of_bundle`, `leafLocalTwo_of_bundle`, and
  `glueLeaves_of_T14_T15 : (BrauerHasse2 ∧ BrauerReciprocity2) → LocalH2Card →
  LeafHasse ∧ LeafLocalTwo` (GLUE-01 of the reference task table).

Cross-check against the frozen reference (scratch file, not part of the change): the two
reference files were compiled byte-for-byte after their import line, together with
`T14 ↔ BrauerHasse2C ∧ BrauerReciprocity2C`, `T14a ↔ BrauerHasse2C`, `T14b ↔ BrauerReciprocity2C`,
`T15 ↔ LocalH2CardC`, `T15 ↔ (its p-adic part)`, the real conjunct of `T15`, and
`T14 → T15 → LeafHasse ∧ LeafLocalTwo`, each proved by the theorems above (§6).

## 6. Verification evidence

- **Compilation.** Each module was compiled separately, in dependency order, one Lean process at
  a time with `LEAN_NUM_THREADS=2` and `--threads=2`, from the repository root:
  `lake env lean -o <olean> -i <ilean> ZInQKernel/Contrib/BrauerCohomology/<Module>.lean`.
  Final run, in order: `TopHomology` 3 s, `Comparison` 11 s, `Functoriality` 7 s, `Galois` 14 s,
  `Real` 6 s, `Glue` 5 s. No errors and no warnings. No root target, `lake build` of the
  libraries, or full project build was run.
- **Axioms (`#print axioms`).** `h2AddEquiv`, `cls_surjective`, `cls_eq_zero_iff`, `map_cls`,
  `natCard_eq_two_iff`, `h2TwoClasses_real`, `leafHasse_of_cochain`, `leafLocalTwo_of_cochain`,
  and the seven frozen-reference cross-check theorems of §5: each depends on exactly
  `[propext, Classical.choice, Quot.sound]`.
- **Scoped kernel replay.** A local copy of `scripts/audit_kernel.lean`, identical through the
  replay and the closure walk over actual bodies, with the headline/export/target section replaced
  by a per-declaration axiom report. Owned modules: the six modules above. External base: their
  imports (Mathlib and the base `HDecomp` modules `I6Base`, `Dyadic`, `B2Glue`). Result:
  **passed**; 199 declarations replayed through the kernel, 0 duplicate bodies, no unsafe or
  partial declarations, axioms used `propext`, `Classical.choice`, `Quot.sound`. All 22 reported
  main declarations (the comparison, naturality, equivalence, real-place and glue theorems of §5)
  use exactly these three. Wall time 56 s, peak resident memory 16.2 GB. This is not the CI gate.
- **Source scan.** No `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`,
  `extern` or `unsafe` in the six modules; each sets `autoImplicit false`. The only `Fact`
  terms are the primality instances `⟨p.2⟩` for `p : Nat.Primes`, as in `I6Base`.
- **Frozen reference.** The cross-check of §5 compiled with the reference files at the hashes in
  §3.
- **Endpoint checks** (scratch file, not part of the change; same compile procedure). The full
  signatures of the endpoint theorems (`#check @…`) contain no binders beyond the stated
  hypotheses: `glueLeaves_of_T14_T15`, `leafHasse_of_bundle`/`_of_cochain`,
  `leafLocalTwo_of_bundle`/`_of_cochain` conclude exactly the unmodified
  `GlueDescent.B2Q.LeafHasse`/`LeafLocalTwo`; `brauerHasse2_iff`, `brauerReciprocity2_iff`,
  `localH2Card_iff` relate exactly the unmodified `PkgI6` definitions. Checked by elaboration
  against the expected types: `GlueDescent.B2Q.resp p` and `Field.absoluteGaloisGroup.map
  (algebraMap ℚ ℚ_[p])` are equal as functions by `rfl`; `PkgI6.IsCocycle2`,
  `PkgI6.IsCoboundary2` and `PkgI6.H2TwoClasses` agree with the comparison's predicates by
  `Iff.rfl` (no cochain normalization on either side); `loc_clsQ` is stated with the base
  `PkgI6.loc` and `PkgI6.resC`. At the real place, `Nat.card (Field.absoluteGaloisGroup ℝ) = 2`,
  `DiscreteTopology (Field.absoluteGaloisGroup ℝ)` and `FiniteDimensional ℝ (AlgebraicClosure ℝ)`
  are closed theorems (axioms as above), so `h2TwoClasses_real` and `natCard_h2_real` carry no
  finiteness or discreteness assumption.
- **Not CI.** The scoped replay and these checks are local evidence only. The required check is
  the unmodified `scripts/check_kernel.py`, to be run by the integrator on a tracked commit.

## 7. What remains, exactly

Remaining mathematical inputs, now each a single explicit hypothesis:

| Input | Exact Lean form | Places |
|---|---|---|
| T14a (ABHN, 2-torsion) | `PkgI6.BrauerHasse2C` (equivalently `BrauerHasse2`) | all primes and `ℝ` |
| T14b (reciprocity, 2-torsion) | `PkgI6.BrauerReciprocity2C` (equivalently `BrauerReciprocity2`) | all primes and `ℝ` |
| T15 at primes | `∀ (p : ℕ) [Fact p.Prime], PkgI6.H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])` | every prime, including `p = 2` |

Exceptional places: the real place is proved (no class field theory: `|G_ℝ| = 2`, Krull topology
discrete). `p = 2` is not special anywhere in the comparison; the local input at `p = 2`
(`Br(ℚ₂)[2] ≅ ℤ/2`) stays inside the uniform `p`-adic hypothesis. `LeafHasse` uses no real input
beyond T14b.

Formal inputs that the classical route to these statements uses and that Mathlib `v4.35.0`
lacks. Each is a precise, conditional gap; none is assumed, added as an axiom or instance, or
replaced by a weaker predicate:

- No long exact sequence for `continuousCohomology` (listed as a TODO in Mathlib's
  `ContCohomology/Basic.lean`), hence no Kummer coboundary `H¹(G_K, K̄ˣ) → … → H²(G_K, μ₂)`.
- Hilbert 90 only for finite Galois groups in `groupCohomology` (`GroupCohomology/Hilbert90.lean`);
  no continuous `H¹(G_K, K̄ˣ) = 0` for the profinite absolute Galois group.
- Mathlib's `BrauerGroup` (`Algebra/BrauerGroup/Defs.lean`) is the set of Brauer-equivalence
  classes of central simple algebras (its group structure is still a TODO there), with no
  identification with `H²(G_K, K̄ˣ)`; there is no local invariant
  `Br(K) ≅ ℚ/ℤ` for nonarchimedean local fields (although `IsNonarchimedeanLocalField ℚ_[p]` is
  available) and no global Brauer sequence.

Tau Ceti status (pinned in §3). The closures below measure *import* closures of the cited Tau
Ceti files: they rule out a small package port within this bounded task. They do not show that a
smaller declaration-level route to the same statements is impossible.

- `TauCeti.ClassFieldTheory.brLocalization_injective : Function.Injective (brLocalization K)` and
  `sumLocalInv_brLocalization_eq_zero` (`Global/Brauer/SumFormula.lean`): over Tau Ceti's
  `Br K := continuousCohomology 2 (unitsRep K)`, places `HeightOneSpectrum (𝓞 K)` with
  `v.adicCompletion K` and `InfinitePlace K` with `w.Completion`. Import closure: 918 Tau Ceti
  modules, 220,702 lines. Bridging to T14 additionally needs: the Kummer map over `ℚ`
  (`h2MuToBr`, defined for every field and injective when `n` is invertible) and its naturality
  under base change; transport of `H²` along `v.adicCompletion ℚ ≃A[ℚ] ℚ_[p]` (present in Mathlib
  `v4.35.0`, `NumberTheory/Padics/HeightOneSpectrum.lean`) and along `w.Completion ≅ ℝ`,
  compatible with the maps `Field.absoluteGaloisGroup.map (algebraMap ℚ F)` used by `PkgI6.loc`
  (different embeddings of algebraic closures differ by conjugation, which acts trivially on
  cohomology; that fact is not in Mathlib either); and `μ₂ ≅ ℤ/2`. A targeted search of the
  snapshot (`adicCompletion`/`ℚ_[p]`/`absoluteGaloisGroup.map` near `brLocalization`) found no
  statement over `PkgI6`'s objects; the search was not exhaustive.
- `h2MuEquivZMod F hn : continuousCohomology 2 (muNRep n F) ≃+ ZMod n` and
  `natCard_cohomFp_two_absoluteGaloisGroup_of_isPrimitiveRoot : Nat.card (cohomFp n
  (Field.absoluteGaloisGroup F) 2) = n` (`ClassFieldTheory/Brauer/RootsOfUnity.lean`), for
  `[IsNonarchimedeanLocalField F]`; `n` need only be invertible in `F`, so `p = 2` is included. With
  `ζ = -1` this is T15 at `p` up to coefficients: Tau Ceti's `trivialFp 2 G` is a `TopRep (ZMod 2)`
  on `ULift (ZMod 2)`, not `TopRep ℤ` on `ZMod 2`. That gap is closable with this contribution's
  `natCard_eq_two_iff` applied to both representations, since it holds for any coefficient ring
  `k` and both reduce to the same cochain statement up to `ULift`. Import closure: 335 modules,
  87,034 lines.
- Tau Ceti's own explicit/canonical comparison (`ContCohomology/CohomologyComparison.lean`,
  general discrete smooth modules) has a 58-module, 18,165-line closure; the trivial-coefficient
  comparison here was written independently, guided by it.
- Pins: Lean `v4.36.0-rc2` and a later Mathlib master, versus our `v4.35.0` pins. A text scan of
  the three closures above (comments stripped) found no `sorry`, `native_decide`,
  `implemented_by`, `extern`, `unsafe def` or `axiom` declaration. Their axioms were **not**
  checked: Tau Ceti was not built.

Coordination: the T30 worker's goal (`LeafSqrtCrit`) and the separate T31 worker (cochain
unramified leaf, pro-cyclic inflation) are not duplicated. `map_cls`/`map_id_cls` are typed
interfaces for any later inflation argument.

## 8. Port record (`TopHomology.lean`)

Source: Tau Ceti `TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean` at the revision
above, SHA-256 `34f6afefabb0fd9016c01277f550bcdadc03f5b7ad7f5d89149023cb3f42e35e`. Kept:
`homologyIsoCoker`, `homologyπ_comp_homologyIsoCoker_hom`, `cokerπ_comp_homologyIsoCoker_inv`,
`homologyπ_surjective`, `homologyπ_eq_zero_iff`, `iCycles_injective`, `cyclesMkOfEq`,
`iCycles_cyclesMkOfEq`, their complex-level forms, `d_iCycles_apply`, `iCycles_toCycles_apply` and
`homologyMap_homologyπ_cyclesMkOfEq`. Moved to the namespace
`ZInQ.Contrib.BrauerCohomology.TopHom` (primed names for complex forms); the Tau Ceti helper
`HomologicalComplex.Hom.comm_apply` replaced by Mathlib's `Hom.comm`; discreteness,
`descHomologyₗ`, exactness parts and both Tau Ceti imports removed. The header keeps the copyright
and license notice and states the changes. The license text is reproduced in the appendix.

## 9. Application records (Protocol_D obligations)

Each record states required versus constructed and where the evidence is. All transitions are
formal; the Lean statements in §5 are the evidence and were kernel-checked (§6).

**A1. Mathlib `H²` versus inhomogeneous classes** (`cls`, `cls_surjective`, `cls_eq_zero_iff`,
`cls_sub`, `h2AddEquiv`).

- Source hypotheses: Mathlib's definitions only, no theorem imported; `G` topological group,
  locally compact for surjectivity; `X` any topological `k`-module with trivial action.
- Constructed objects: invariant nested continuous maps (degrees 1, 2, 3 of
  `homogeneousCochains`), homology via the concrete cokernel of `toCycles` (ported lemmas).
- Domain coverage: all of `continuousCohomology 2 X` (surjectivity), every cocycle; no
  normalization assumed.
- Maps: `ε ↦ ((x₀, x₁, x₂) ↦ ε (x₀⁻¹x₁) (x₁⁻¹x₂))`, inverse `F ↦ ((a, b) ↦ F 1 a (ab))`; inverse
  identities `inh2_homog2`, `homog2_inh2` (invariance).
- Consumed object: Mathlib's `continuousCohomology 2 X` itself (not a copy), its `homologyπ`.
- Conventions: differentials computed from Mathlib's `d` (`d12_apply`, `d23_apply`), equal to
  I6Base's expressions with no sign change.
- Local conditions: not applicable (group-level statement).
- Exceptional cases: local compactness is required only for continuity of `F ↦ F 1 a (ab)`;
  absent it, `cls` and `cls_eq_zero_iff` still hold.
- Downstream: A2–A5.

**A2. Naturality** (`map_cls`, `map_id_cls`, `loc_clsQ`). Required: `loc F 2` on classes equals
`resC F` on cochains. Constructed: `ContinuousCohomology.cochainsMap φ f` in degree 2
(`cochainsMap_toHC2`), then `homologyMap` of a cycle (ported). Same group map term on both sides;
coefficient map `𝟙` is the identity of `ZMod 2` (definitional). Index coverage: every `F` with
`[Algebra ℚ F]`. Exceptional cases: none. Downstream: A3–A5.

**A3. T14a** (`brauerHasse2_iff`). Required: for every class (bundle) / every cocycle (cochain),
local vanishing at `ℝ` and all primes implies vanishing. Index set: `∀ p [Fact p.Prime]` and `ℝ`,
identical on both sides. Transition: A1 surjectivity and zero criterion, A2 localization. Both
directions proved.

**A4. T14b** (`brauerReciprocity2_iff`). Required: the sets `{p | locP p x ≠ 0}` and
`{p | ¬ IsCoboundary2 (resC ℚ_[p] ε)}` coincide for `x = cls ε` (`badPrimes_clsQ`, including the
in-set `Fact` instance), and the real indicator matches (decided by `ite_eq_left`/`ite_eq_right`,
so the classical decidability instances on the two sides need not agree syntactically). Finiteness
and parity transfer by rewriting.

**A5. T15** (`natCard_Z2res_eq_two_iff`, `localH2Card_iff`). Required: `Nat.card = 2` on
`continuousCohomology 2 (res … (Z2 ℚ))` versus `H2TwoClasses (G_F)` with `ZMod 2` cochains on
`G_F`. Constructed: A1 for the restricted representation (trivial action, carrier `ZMod 2`), plus
`natCard_eq_two_iff_of_addGroup`. Coverage: every prime and `ℝ`.

**A6. Real place** (`h2TwoClasses_real`). Required: `H2TwoClasses (absoluteGaloisGroup ℝ)`.
Constructed: `ℝ̄ ≅ ℂ` (`IsAlgClosure.equiv`), `[ℝ̄ : ℝ] = 2`, `|Gal| = 2`
(`IsGalois.card_aut_eq_finrank`), discreteness
(`krullTopology_discreteTopology_of_finiteDimensional`);
for `G = {1, s}`: `ε 1 x = ε x 1 = ε 1 1`, coboundary iff `ε s s = ε 1 1`, witness
`ε a b = [a = s ∧ b = s]`. Exceptional cases: none (any group of order two).

**A7. Glue leaves** (`leafHasse_of_cochain`, `leafLocalTwo_of_cochain`). Required: `LeafHasse`
quantifies over finite primes only and `ℂˣ` sign cochains. Constructed: `signToZMod`; a sign
cocycle gives an `IsCocycle2`, `SignCob ↔ IsCoboundary2`. The real place is supplied by
reciprocity: with no bad prime the parity condition forces `IsCoboundary2 (resC ℝ ε)`, then
BrauerHasse2C applies. `LeafLocalTwo`: `ofSign (η₁ η₂⁻¹) = ofSign η₁ − ofSign η₂` and the second
conjunct of `H2TwoClasses` at `p`. Index coverage: `Nat.Primes` with the glue's `Fact` instance,
which is definitionally the one `PkgI6` receives. Downstream: `GlueDescent.B2Q.b2_of_leaves`
takes these two leaves as its hypotheses `hHasse`, `hTwo` (together with `LeafSqrtCrit` and
`LeafUnramified`, the T30/T31 leaves); it was not modified or re-proved.

## 10. Review status and limitations

- Author: AI agent, model identity not recorded. This is a preliminary author self-check, not an
  independent or Astra review. No coverage decision, no source-first reconstruction by a
  non-author, no acceptance is claimed.
- This frozen packet (six sources and this note) is the initial author submission. Freezing it is
  not an acceptance, and preparing it does not close any registered premise or target.
- A passing compile and kernel replay establish the formal statements in §5 only. They do not
  establish T14 or T15, and no target is registered.
- The scoped replay is a local copy of `scripts/audit_kernel.lean` without the headline, export and
  target sections; it is not the CI gate. No full root build was run.
- The bundle/cochain equivalences rest on Mathlib's `continuousCohomology` definitions at the
  pinned version. A change to those definitions requires re-checking §5.

## Appendix: Apache-2.0 license from the Tau Ceti source revision

```text
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
```
