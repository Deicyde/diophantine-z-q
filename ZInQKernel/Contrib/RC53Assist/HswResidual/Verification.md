# Residual switch nondegeneracy: verification report


## Update after independent review (2026-11-18)

The shipped `Residual.lean` is 35,509 bytes, SHA-256 `8eab349b6864e949e4efc70a35340b622088eccc2ad3830a6ee710aa2a47181b`: the checked source with its trailing `#check` and `#print axioms` lines removed. The digest recorded further below (37,274 bytes, `bdd77c73…`) is that of the instrumented checking edition. `InterfaceCheck.lean`, cited below, is a separate checking file that is not shipped. An independent review recompiled the shipped source, confirmed that `derivSwitch_switchCoordinates_tame_of_Milne` produces the original consumer's unabbreviated result type, and matched `MilneCor23Residual` against Milne, Arithmetic Duality Theorems, 2nd ed., I, Corollary 2.3, p. 28.

Compiled, conditional residual bridge for target (10). The implementation produces the exact `hnd` accepted by `derivSwitch_switchCoordinates_tame` and applies that consumer directly. It does not prove the uninstantiated Milne print or the A23 Kummer–Brauer comparison.

## Mathematical statement of the target

Put `k = F_2`, `L = K_q`, and `M_q = Res_q M`, a finite two-dimensional `k`-space with continuous Galois action. At the tame residual switch the quotient space

`W = H^1(U_rel/U_str) = H^1(L,M_q)`

has tame coordinates `W = k^2 ⊕ k^2`. The local cup product comes from the equivariant coefficient pairing `β_q : M_q × M_q -> T_q`, where `T_q = mu_2 = k(1)`.

The consumer's `hnd` says that the left radical of the residue form is zero: if a relaxed one-cocycle `t` pairs to zero with every relaxed one-cocycle `u`, its quotient class `gClass t ht` is zero. Equivalently, the induced bilinear form on the four-dimensional finite `F_2`-space `W` is nondegenerate.

On cocycles, the cone residue formula has the orientation

`resForm(t,u) = -tr(0, iota(u) cup iota(t))`.

Testing against a cocycle `z` supported at `q` gives the proved identity

`resForm(t, relSingle z) = -localCupTrace([z], [t_q])`.

The minus sign is retained in the formal statement, even though it is trivial in `F_2`. In particular, the right adjoint of the local cup pairing supplies the consumer's left-radical condition. There is no assumed nondegeneracy of the residue form in the new proof.

## Printed source and its precise scope

J. S. Milne, *Arithmetic Duality Theorems*, second edition (2006), Chapter I, Section 2, **Corollary 2.3**, printed page 28, PDF page 36:

https://www.jmilne.org/math/Books/ADTnot.pdf

> Let M be a finitely generated G-module whose torsion subgroup has order prime to char(K). Then cup-product defines isomorphisms

`H^r(G,M^D) -> H^(2-r)(G,M)^*` for `r >= 1`, and an isomorphism of compact groups in degree zero. Here `M^D = Hom(M,(K^s)^*)`. The source also says:

> The groups H^1(G,M) and H^1(G,M^D) are finite.

This edition labels the result Corollary 2.3, not Theorem 2.3. The finite exponent-two degree-one specialization, with a perfect coefficient pairing into a trivial rank-one target and an isomorphism-inducing local trace, is stated as `MilneCor23Residual : Prop`. It is an explicit printed input, not an added kernel assumption or a proof of the printed proposition.

The manuscript's citation is at lines 3442–3444. The transported derivative pairing is at lines 2816–2820 and 4854–4890. The existing `MilneLocalTateDualityKummer` and its characteristic-zero-ground-field version concern Kummer-map adjointness, not a statement of perfectness of the full finite-module degree-one pairing. Their definitions were read; the existing `cupH`, `kummerToBr`, and `invMap` are reused.

Source-reading classification: **AI-READ**. No independent human statement check is claimed. The ground local field is of characteristic zero throughout the Milne input, while the coefficient field is `F_2`. There is no characteristic-zero coefficient conclusion.

## Arithmetic normalization and the A23 input

`KummerBrauerComparisonF2 L` states, for the existing natural map `j = kummerToBr 2`, exactly

`Function.Injective j` and `j.range = Br(L)[2]`.

Thus it specifies the comparison `H^2(L,mu_2) -> Br(L)[2]` without proving it. That comparison remains the A23 input.

The target-module identification `eμ : T_q = mu_2` is transported along the existing continuous restriction isomorphism between algebraic and separable closures. This produces `kummerH2Transport`, not an unspecified cohomology isomorphism.

`LocalTraceMatchesInvariant eμ heμ tr_q` is the explicit normalization condition on every local two-cocycle `c`:

`f2ToQmodZ(tr_q(c)) = inv_L(j(kummerH2Transport([c])))`,

where the proved injective map `f2ToQmodZ : F_2 -> Q/Z` sends `1` to `1/2`.

`inducesIsoH2_of_KummerBrauer` derives `InducesIsoH2 tr_q` from the comparison and this normalization. It uses injectivity to identify the trace kernel with coboundaries, and surjectivity onto `Br(L)[2]` to lift the invariant `1/2`. It does not re-prove the A23 comparison.

The supplied sum-formula backport is present. Its theorem `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_eq_zero` is at line 48 of module `ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula`. It is not needed by this local-only proof and was not newly imported or built.

## How the consumer is supplied

The final theorem `derivSwitch_switchCoordinates_tame_of_Milne` does the following inside its kernel-checked proof:

1. Derives both coefficient adjoints' bijectivity from the transported residual Weil formula using `coefficient_perfect_of_weil`. The two coordinate identifications are allowed to differ, as required for conjugate duality.
2. Derives the restricted local trace's `InducesIsoH2` from `KummerBrauerComparisonF2` and `LocalTraceMatchesInvariant`.
3. Calls `derivSwitch_hnd_of_Milne` to produce exactly the original consumer's quantified `hnd`.
4. Passes that result to `derivSwitch_switchCoordinates_tame`, retaining all its other inputs. The conclusion is its original coordinate change fixing the finite plane and its original `SwitchCoordinates` statement.

The underlying residue/cup comparison is proved for a general relaxed cochain tested against a cocycle supported at `q`. The proof does not assume a residue pairing has already been identified with local duality. `gClass_eq_coordAt` and `gClass_eq_zero_of_localClass` then connect a zero local cohomology class to the exact quotient-coordinate class required by the consumer.

## What remains open

For an actual arithmetic instantiation, the following explicit inputs must be supplied:

- `hMilne : MilneCor23Residual`: the stated finite local duality print. No Lean proof of this universal arithmetic proposition is supplied.
- `hKB : KummerBrauerComparisonF2 K_q`: the reserved A23 comparison. It was not re-proved.
- `eμ`, `heμ`, and `hmatch`: the actual target-module identification with `mu_2`, its equivariance, and equality of the given cone trace with the local Brauer invariant on two-cocycles. The global trace was not constructed or replaced.
- `eT`, `eM₂`, and `hWeil`: the actual coefficient identifications and transported Weil formula. Perfectness follows from that formula by the new proved theorem; it is not a further hypothesis of the final consumer theorem.

The original consumer's remaining inputs are unchanged: the derivative family and `RelAt`, tame coordinates and inertia containment, polarization and equivariance, isotropy data, cone-trace coboundary vanishing, strict degree-two vanishing, local triviality, and the nonzero scalar/involutive-matrix parameters. This contribution does not instantiate those unrelated inputs.

No assertion is made about characteristic-zero coefficient fibres, the full restricted converse, or the full Diophantine theorem. No existing source was edited, no version-control operation or dependency build was run, and no outreach was performed.

## Verification

- Lean 4.35.0, release compiler, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Supplied source base: `a6c70bd54e403ce3ead8ff2b8e40f80445fe58cc`; no independent repository query or base change was performed.
- The required parent build-completion marker was observed before the first single-file compilation.
- The prescribed single-file compiler invocation was used with six threads, processor affinity 160–175, and priority adjustment 10.
- Final `Residual.lean` compilation: exit 0. `InterfaceCheck.lean` also compiled successfully. All imported modules were available.
- All eleven exported theorems were checked individually. Every axiom report contains exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Source restrictions checked: no proof gaps, new axiom declarations, kernel bypasses, custom parsing extensions, forbidden phrases, or private identifiers; heartbeat limit 800000.
- Initial construction checks found implicit type mismatches, a helper specialized to identical coefficient modules applied to distinct modules, and a heartbeat-bounded rewrite. These were repaired. Earlier failed checks are not credited as proofs; the recorded final transcript is the successful check.

`Verification.txt` preserves the raw compiler transcript. The following sections repeat each theorem's verbatim compiler type and its separate axiom report. The standard pretty printer elides proof terms as `⋯`; the explicit source annotations and proof terms remain in `Residual.lean`.

## Input-file digests

- `Residual.lean`: 37274 bytes; SHA-256 `bdd77c732dda3ea6835d2d472e16b514c68a35aa626746b7fa500ceacda0ecf6`.
- `InterfaceCheck.lean`: 1061 bytes; SHA-256 `5e0b428d187f3605c383d2347f04f7c6a5c90132bb59d03007af86cd5b506537`.
- `Verification.txt`: 33120 bytes; SHA-256 `99066e96eb45b789335740003d1d396c3f311769378445d0ef7ef60eacae799c`.

## `traceH2_mk`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.traceH2_mk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {T : Type} [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction G T] [SMulCommClass G (ZMod 2) T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul G T]
  (tr2 : ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G T).X 2) →ₗ[ZMod 2] ZMod 2)
  (htr2 :
    ∀ (c : ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G T).X 1)),
      tr2 ((ModuleCat.Hom.hom ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G T).d 1 2)) c) = 0)
  (z : ↥(TauCeti.ContCohomology.Z2 G T)) :
  (ZInQ.Contrib.RC53Assist.HswResidual.traceH2 tr2 htr2) ((TauCeti.ContCohomology.H2pi G T) z) =
    tr2 (ZInQ.Manuscript.RC.SelmerComplex.mkCochain2 ↑z ⋯)
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.traceH2_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `localCupTrace_cocycles`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.localCupTrace_cocycles {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M N T : Type} [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [AddCommGroup N]
  [Module (ZMod 2) N] [DistribMulAction G N] [SMulCommClass G (ZMod 2) N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul G N] [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction G T] [SMulCommClass G (ZMod 2) T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul G T] (β : M →ₗ[ZMod 2] N →ₗ[ZMod 2] T)
  (hβ : ∀ (g : G) (x : M) (y : N), (β (g • x)) (g • y) = g • (β x) y)
  (tr2 : ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G T).X 2) →ₗ[ZMod 2] ZMod 2)
  (htr2 :
    ∀ (c : ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G T).X 1)),
      tr2 ((ModuleCat.Hom.hom ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G T).d 1 2)) c) = 0)
  (z : ↥(ModuleCat.Hom.hom ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G M).d 1 2)).ker)
  (w : ↥(ModuleCat.Hom.hom ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) G N).d 1 2)).ker) :
  ((ZInQ.Contrib.RC53Assist.HswResidual.localCupTrace β hβ tr2 htr2) (ZInQ.Manuscript.RC.SelmerComplex.kerToH1 z))
      (ZInQ.Manuscript.RC.SelmerComplex.kerToH1 w) =
    tr2 (((ZInQ.Manuscript.RC.SelmerComplex.contCup β ⋯ 1 1 2 ⋯) ↑z) ↑w)
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.localCupTrace_cocycles' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `coefficient_perfect_of_weil`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.coefficient_perfect_of_weil {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] (e1 e2 : V ≃ₗ[ZMod 2] Fin 2 → ZMod 2) (eW : W ≃ₗ[ZMod 2] ZMod 2)
  (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W) (hβ : ∀ (x y : V), eW ((β x) y) = (ZInQ.Manuscript.RC.Uniform.weil (e1 x)) (e2 y)) :
  Function.Bijective ⇑β ∧ Function.Bijective ⇑β.flip
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.coefficient_perfect_of_weil' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `f2ToQmodZ_injective`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.f2ToQmodZ_injective :
  Function.Injective ⇑ZInQ.Contrib.RC53Assist.HswResidual.f2ToQmodZ
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.f2ToQmodZ_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `inducesIsoH2_of_KummerBrauer`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.inducesIsoH2_of_KummerBrauer {L : Type} [Field L] [CharZero L] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
  [DistribMulAction (Field.absoluteGaloisGroup L) T] [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (Field.absoluteGaloisGroup L) T]
  (eμ : T ≃+ TauCeti.KummerCoeff L 2)
  (heμ :
    ∀ (g : TauCeti.AbsoluteGaloisGroup L) (t : T),
      eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv L).symm g • t) = g • eμ t)
  (hKB : ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2 L)
  (tr2 :
    ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 2) →ₗ[ZMod 2] ZMod 2)
  (hmatch : ZInQ.Contrib.RC53Assist.HswResidual.LocalTraceMatchesInvariant eμ heμ tr2) :
  ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH2 tr2
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.inducesIsoH2_of_KummerBrauer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `residualTraceAt_d`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt_d {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
  [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  (X : ZInQ.Manuscript.RC.SelmerComplex.GenuineSwitch K S (ZMod 2) M) (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
  (hβ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (β (g • x)) (g • y) = g • (β x) y)
  (Iso : ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2)
  (htr :
    ∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).d
              2 3 ⋯)
            c) =
        0)
  (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (c :
    ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
            (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T)).X
        1)) :
  (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt X β hβ Iso tr q)
      ((ModuleCat.Hom.hom
          ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
                (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T)).d
            1 2))
        c) =
    0
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt_d' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `gClass_eq_coordAt`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.gClass_eq_coordAt {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S M))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q)
  (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
  (eM :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) M ≃ₗ[ZMod 2]
      Fin 2 → ZMod 2)
  {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
  (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ) (t : ↑(F.Urel.X 1)) (ht : (F.Urel.d 1 2 ⋯) t = 0) :
  ZInQ.Contrib.CloudB3RC53.Hsw.gClass
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).toQuasi
      t ht =
    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.coordAt q φ σ eM) ↑(t q)
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.gClass_eq_coordAt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `gClass_eq_zero_of_localClass`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.gClass_eq_zero_of_localClass {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S M))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q)
  (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
  (eM :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) M ≃ₗ[ZMod 2]
      Fin 2 → ZMod 2)
  {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
  (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ) (t : ↑(F.Urel.X 1)) (ht : (F.Urel.d 1 2 ⋯) t = 0)
  (hz : ZInQ.Manuscript.RC.SelmerComplex.kerToH1 (ZInQ.Contrib.RC53Assist.HswResidual.localCocycle F hR t) = 0) :
  ZInQ.Contrib.CloudB3RC53.Hsw.gClass
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).toQuasi
      t ht =
    0
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.gClass_eq_zero_of_localClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `resForm_eq_localCupTrace`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.resForm_eq_localCupTrace {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
  [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S M))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q)
  (eR : ↑(HomologicalComplex.homology F.Wrel.toCC 1) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
  (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
  (hβ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (β (g • x)) (g • y) = g • (β x) y)
  (Iso :
    ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) β hβ
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔS
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔS
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔR Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2)
  (htr :
    ∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔS
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔR Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔS
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔR Iso).resE).d
              2 3 ⋯)
            c) =
        0)
  (t : ↑(F.Urel.X 1))
  (z :
    ↥(ModuleCat.Hom.hom
          ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
                (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) M)).d
            1 2)).ker) :
  ZInQ.Contrib.CloudB3RC53.Hsw.resForm (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).toQuasi
      (ZInQ.Manuscript.RC.SelmerComplex.piCx (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).US)
      (ZInQ.Manuscript.RC.SelmerComplex.piMap (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).φ)
      (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
        (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔS
        (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR).ΔR Iso)
      tr t (ZInQ.Contrib.CloudB3RC53.Hsw.relSingle F q ⋯ ↑z ⋯) =
    -((ZInQ.Contrib.RC53Assist.HswResidual.localCupTrace
            (ZInQ.Manuscript.RC.SelmerComplex.resPairing (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) β
              (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q))
            ⋯
            (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F eR)
              β hβ Iso tr q)
            ⋯)
          (ZInQ.Manuscript.RC.SelmerComplex.kerToH1 z))
        (ZInQ.Manuscript.RC.SelmerComplex.kerToH1 (ZInQ.Contrib.RC53Assist.HswResidual.localCocycle F hR t))
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.resForm_eq_localCupTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `derivSwitch_hnd_of_Milne`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.derivSwitch_hnd_of_Milne {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
  [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S M))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q)
  (hMilne : ZInQ.Contrib.RC53Assist.HswResidual.MilneCor23Residual) (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
  (eM :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) M ≃ₗ[ZMod 2]
      Fin 2 → ZMod 2)
  {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
  (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ) (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
  (hβ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (β (g • x)) (g • y) = g • (β x) y)
  (Iso :
    ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) β hβ
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                  Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2)
  (htr :
    ∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                    Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                      Iso).resE).d
              2 3 ⋯)
            c) =
        0)
  (eT : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T ≃ₗ[ZMod 2] ZMod 2)
  (htrivT :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q) (m : T),
      (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) g • m = m)
  (hb :
    Function.Bijective
      ⇑(ZInQ.Manuscript.RC.SelmerComplex.resPairing (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) β
          (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)))
  (hb' :
    Function.Bijective
      ⇑(ZInQ.Manuscript.RC.SelmerComplex.resPairing (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) β
            (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)).flip)
  (htrace :
    ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH2
      (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt
        (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc))
        β hβ Iso tr q))
  (t :
    ↑((ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                  (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).toQuasi.D.U.X
        1))
  (ht :
    ((ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).toQuasi.D.U.d
          1 2 ⋯)
        t =
      0) :
  (∀
      (u :
        ↑((ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).toQuasi.D.U.X
            1)),
      ((ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).toQuasi.D.U.d
              1 2 ⋯)
            u =
          0 →
        ZInQ.Contrib.CloudB3RC53.Hsw.resForm
            (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).toQuasi
            (ZInQ.Manuscript.RC.SelmerComplex.piCx
              (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                  (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).US)
            (ZInQ.Manuscript.RC.SelmerComplex.piMap
              (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                  (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).φ)
            (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
              (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                  (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
              (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                  (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
              Iso)
            tr t u =
          0) →
    ZInQ.Contrib.CloudB3RC53.Hsw.gClass
        (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
            (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).toQuasi
        t ht =
      0
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.derivSwitch_hnd_of_Milne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## `derivSwitch_switchCoordinates_tame_of_Milne`

```lean
ZInQ.Contrib.RC53Assist.HswResidual.derivSwitch_switchCoordinates_tame_of_Milne {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
  [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S M))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q)
  (hMilne : ZInQ.Contrib.RC53Assist.HswResidual.MilneCor23Residual) (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
  (eM :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) M ≃ₗ[ZMod 2]
      Fin 2 → ZMod 2)
  {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
  (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ)
  (hIur :
    ∀ (g : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)),
      (ZInQ.Manuscript.RC.SelmerComplex.urRes K ↑q) g = 1 → g ∈ I)
  (β γ : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
  (hβ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (β (g • x)) (g • y) = g • (β x) y)
  (hγ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (γ (g • x)) (g • y) = g • (γ x) y)
  (hpol : ∀ (x y : M), (β x) y = (γ x) y - (γ y) x)
  (Iso :
    ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) β hβ
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                  Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2)
  (htr :
    ∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                    Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                      Iso).resE).d
              2 3 ⋯)
            c) =
        0)
  (hUS2 : ∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (x : ↑((F.str v).cx.X 2)), x = 0) {ε : ZMod 2}
  (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hJ2 : J * J = 1)
  (htriv :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q) (m : M),
      (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) g • m = m)
  (htrivT :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q) (m : T),
      (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) g • m = m)
  (eT : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T ≃ₗ[ZMod 2] ZMod 2)
  (eM₂ :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) M ≃ₗ[ZMod 2]
      Fin 2 → ZMod 2)
  (hWeil :
    ∀ (x y : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) M),
      eT
          (((ZInQ.Manuscript.RC.SelmerComplex.resPairing (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) β
                (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q))
              x)
            y) =
        (ZInQ.Manuscript.RC.Uniform.weil (eM x)) (eM₂ y))
  (hKB :
    ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q))
  (eμ :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T ≃+
      TauCeti.KummerCoeff (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) 2)
  (heμ :
    ∀ (g : TauCeti.AbsoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q))
      (t : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T),
      eμ
          ((TauCeti.absoluteGaloisGroupRestrictEquiv (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)).symm g •
            t) =
        g • eμ t)
  (hmatch :
    ZInQ.Contrib.RC53Assist.HswResidual.LocalTraceMatchesInvariant eμ heμ
      (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt
        (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc))
        β hβ Iso tr q)) :
  let X :=
    ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc);
  ∃ Φ,
    Submodule.map (↑Φ) (ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) =
        ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
      { ΔR := X.ΔR, US := X.US, φ := X.φ, W := X.W, g := X.g, hfg := ⋯, φ_inj := ⋯, g_surj := ⋯, ex := ⋯,
            eR := X.eR ≪≫ₗ Φ }.SwitchCoordinates
        (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso) tr ε (- -1) J
```

`#print axioms`:

```text
'ZInQ.Contrib.RC53Assist.HswResidual.derivSwitch_switchCoordinates_tame_of_Milne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Exact input propositions

```lean
def ZInQ.Contrib.RC53Assist.HswResidual.MilneCor23Residual : Prop :=
∀ (L : Type) [inst : Field L] [CharZero L] [inst_2 : ValuativeRel L] [inst_3 : TopologicalSpace L]
  [IsNonarchimedeanLocalField L] (M N T : Type) [inst_5 : AddCommGroup M] [inst_6 : Module (ZMod 2) M]
  [inst_7 : DistribMulAction (Field.absoluteGaloisGroup L) M] [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) M]
  [inst_9 : TopologicalSpace M] [inst_10 : DiscreteTopology M]
  [inst_11 : ContinuousSMul (Field.absoluteGaloisGroup L) M] [Finite M] [inst_13 : AddCommGroup N]
  [inst_14 : Module (ZMod 2) N] [inst_15 : DistribMulAction (Field.absoluteGaloisGroup L) N]
  [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) N] [inst_17 : TopologicalSpace N] [inst_18 : DiscreteTopology N]
  [inst_19 : ContinuousSMul (Field.absoluteGaloisGroup L) N] [Finite N] [inst_21 : AddCommGroup T]
  [inst_22 : Module (ZMod 2) T] [inst_23 : DistribMulAction (Field.absoluteGaloisGroup L) T]
  [inst_24 : SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T] [inst_25 : TopologicalSpace T]
  [inst_26 : DiscreteTopology T] [inst_27 : ContinuousSMul (Field.absoluteGaloisGroup L) T] (_eT : T ≃ₗ[ZMod 2] ZMod 2),
  (∀ (g : Field.absoluteGaloisGroup L) (t : T), g • t = t) →
    ∀ (β : M →ₗ[ZMod 2] N →ₗ[ZMod 2] T)
      (hβ : ∀ (g : Field.absoluteGaloisGroup L) (x : M) (y : N), (β (g • x)) (g • y) = g • (β x) y),
      Function.Bijective ⇑β →
        Function.Bijective ⇑β.flip →
          ∀
            (tr2 :
              ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 2) →ₗ[ZMod 2]
                ZMod 2)
            (htr2 :
              ∀ (c : ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 1)),
                tr2
                    ((ModuleCat.Hom.hom
                        ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).d 1
                          2))
                      c) =
                  0),
            ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH2 tr2 →
              Finite (TauCeti.ContCohomology.H1 (Field.absoluteGaloisGroup L) M) ∧
                Finite (TauCeti.ContCohomology.H1 (Field.absoluteGaloisGroup L) N) ∧
                  Function.Bijective ⇑(ZInQ.Contrib.RC53Assist.HswResidual.localCupTrace β hβ tr2 htr2) ∧
                    Function.Bijective ⇑(ZInQ.Contrib.RC53Assist.HswResidual.localCupTrace β hβ tr2 htr2).flip
def ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2 : (L : Type) →
  [inst : Field L] → [CharZero L] → Prop :=
fun L [Field L] [CharZero L] =>
  Function.Injective ⇑(ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr 2) ∧
    (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr 2).range = AddSubgroup.torsionBy (TauCeti.ClassFieldTheory.Br L) 2
def ZInQ.Contrib.RC53Assist.HswResidual.LocalTraceMatchesInvariant : {L : Type} →
  [inst : Field L] →
    [inst_1 : ValuativeRel L] →
      [inst_2 : TopologicalSpace L] →
        [IsNonarchimedeanLocalField L] →
          {T : Type} →
            [inst_4 : AddCommGroup T] →
              [inst_5 : Module (ZMod 2) T] →
                [inst_6 : DistribMulAction (Field.absoluteGaloisGroup L) T] →
                  [inst_7 : SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T] →
                    [inst_8 : TopologicalSpace T] →
                      [inst_9 : DiscreteTopology T] →
                        [inst_10 : ContinuousSMul (Field.absoluteGaloisGroup L) T] →
                          (eμ : T ≃+ TauCeti.KummerCoeff L 2) →
                            (∀ (g : TauCeti.AbsoluteGaloisGroup L) (t : T),
                                eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv L).symm g • t) = g • eμ t) →
                              (↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L)
                                          T).X
                                      2) →ₗ[ZMod 2]
                                  ZMod 2) →
                                Prop :=
fun {L} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] {T} [AddCommGroup T]
    [Module (ZMod 2) T] [DistribMulAction (Field.absoluteGaloisGroup L) T]
    [SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
    [ContinuousSMul (Field.absoluteGaloisGroup L) T] eμ heμ tr2 =>
  ∀
    (c :
      ↥(ModuleCat.Hom.hom
            ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).d 2 3)).ker),
    ZInQ.Contrib.RC53Assist.HswResidual.f2ToQmodZ (tr2 ↑c) =
      (TauCeti.ClassFieldTheory.invMap L)
        ((ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr 2)
          ((ZInQ.Contrib.RC53Assist.HswResidual.kummerH2Transport eμ heμ) (ZInQ.Manuscript.RC.SelmerComplex.kerToH2 c)))
```
