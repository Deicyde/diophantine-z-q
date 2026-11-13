# x1-belyi fold notes (leaf-adopt3)

Fragment: `scratch/leaf-adopt3/fold/x1-belyi.lean`, section `X1BelyiSec`, namespace `X1Belyi`.
Source: `scratch/x1-belyi/X1Belyi.lean`, copied verbatim (lines 3-364). The import is dropped, the 4
`#print axioms` lines are dropped, and `set_option linter.unusedSimpArgs false` is scoped to the section.
It depends on no other fragment. Insertion order: x1-belyi, e1-sub, c9-rhof.

## Bundle and glue changes
- `LeafModCurves.X1ModelExists` (glue target; field `x1` of `LeafModCurves.ModCurveLeaves`) is
  **proved from 4 new leaves**: T1, M1, M2, M3.
- `LeafModCurves.BelyiX1` (glue target; E2's Belyi half, G18 row) is **proved from 2 new leaves**: T1, T2.
- The x1-belyi theorems do not use or reduce any existing bundle field. T33 (`t33`), R16 (`r16`) and
  T34 (`t34`) are only passed through, in `modCurveLeaves_of` and `exists_J1_of_leaves`.

## Bridging theorems (exact Leaves.lean types)
- `X1Belyi.belyiX1_of_leaves (hT : X1Belyi.TorsionStructure) (hG : X1Belyi.GoodReductionUnramified) : LeafModCurves.BelyiX1`
- `X1Belyi.x1ModelExists_of_leaves (hT : TorsionStructure) (hC : CurveOfFunctionFieldQ) (hK : X1ConstantField) (hR : X1RationalCusp) : LeafModCurves.X1ModelExists`
- `X1Belyi.x1ModelExists_and_belyiX1 (L : X1Belyi.X1Leaves) : LeafModCurves.X1ModelExists ∧ LeafModCurves.BelyiX1`
- `X1Belyi.modCurveLeaves_of (L : X1Leaves) (hJ : LeafModCurves.JacobianExists ℚ) (h16 : LeafModCurves.R16_EichlerShimuraJ1') (hd : LeafModCurves.DimJ1Genus) : LeafModCurves.ModCurveLeaves`
- New, added by me (one line): `X1Belyi.exists_J1_of_leaves (L : X1Leaves) (hJ : LeafModCurves.JacobianExists ℚ) (N) (hN : 0 < N) : ∃ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J`.
  It gives non-vacuity of `IsJ1` from t33 plus the new leaves.
- Also proved: `X1Belyi.finrank_fieldX1_le` (`[K_N : ℚ(j)] ≤ N²` from T1).
- `#print axioms` dropped: `belyiX1_of_leaves`, `x1ModelExists_of_leaves`, `finrank_fieldX1_le`,
  `x1ModelExists_and_belyiX1`.

## New leaf Props (all `def … : Prop` in namespace `X1Belyi`, statement-identical to the task file)
Bundled as `structure X1Belyi.X1Leaves` (fields `torsion goodRed curve constants cusp`).
Helper defs: `nTors`, `ratHom`, `ConstantFieldIsQ`, `HasRationalPlace`.

| Leaf | One-line meaning | Reference (numbers UNVERIFIED) |
|---|---|---|
| `TorsionStructure` (T1) | For an elliptic `W` over an algebraically closed `K` of char 0 and `N ≥ 1`, `W[N] ≃+ ℤ/N × ℤ/N` (Mathlib's `W.toAffine.Point`) | Silverman, AEC, Cor. III.6.4(b) |
| `GoodReductionUnramified` (T2) | `W/k(T)` (char 0) with good reduction at an irreducible `p ∈ k[T]` ⇒ `k(T)(x(P))` is unramified over `p` for every torsion `P` (every place `w ∋ k[T]` with `p ∈ 𝔪_w` has `𝔪_w = p·w`) | Néron–Ogg–Shafarevich in Serre–Tate, Ann. Math. 88 (1968) Thm 1; AEC VII.4.1; Serre, *Local Fields* I §7 |
| `CurveOfFunctionFieldQ` (M1) | A finite extension `F/ℚ(T)` with constant field `ℚ` is the function field of an integral `X` with `IsCurve X`; `X` has a `ℚ`-point if `F` has a degree-1 place | Stacks, *Algebraic Curves*, "Curves and function fields"; Hartshorne I.6, II.6.7 |
| `X1ConstantField` (M2) | For `P` of exact order `N` on `E_j`, `ℚ` is algebraically closed in `K_N = ℚ(j)(x(P))` (`X₁(N)` is geometrically irreducible) | Igusa, Amer. J. Math. 81 (1959); Shimura 1971 §6.2, Prop. 6.9 |
| `X1RationalCusp` (M3) | For `P` of exact order `N`, `K_N` has a place of degree 1 over `ℚ` (a rational cusp) | Tate curve: Silverman, *Advanced Topics* V.3.1; Ogg 1973; Igusa transitivity |

**Reuse check.** None of the five is an existing Leaves.lean leaf.
- **T1 is not `PkgI2.TorsionStructure`** (field `t5`). `t5` is about `A : Grp (Over (Spec K))` with
  `IsAbelianVariety`, Krull dimension `g`, `n` invertible in `K`, and torsion of
  `Pts A (AlgebraicClosure K)` as `Fin (2g) → ZMod n`. T1 is about the group law of Mathlib's
  Weierstrass points over an algebraically closed field. Mathematically T1 is `t5` at `g = 1`. Deriving
  it would need new glue: a Weierstrass curve is a `Grp`-scheme abelian variety whose `K̄`-points are
  `W.toAffine.Point`. That glue is not in Mathlib or Leaves.lean, and it is much harder than T1.
- **T2 is not `PkgI2.NeronOggShafarevich`** (field `r7a`). `r7a` is stated for `Grp` abelian varieties
  over a DVR, with `HasGoodReduction` and `InertiaTrivialOn`. T2 is a function-field consequence:
  integral coefficients plus a unit discriminant imply unramified places of `k(T)(x(P))`.
- M1, M2, M3 have no counterpart.

## Duplicates deleted / kernel declarations copied
- Nothing deleted: every `X1Belyi.*` name is new.
- Kernel names used, all present in Leaves.lean `LeafModCurvesSec` with the same text: `Qj`, `Ej`,
  `Kbar`, `EjBar`, `xCoord`, `fieldX1`, `IsCurve`, `SpecQ`, `RatPt`, `IsX1Model`, `IsBelyiFunction`,
  `BelyiX1`, `X1ModelExists`, `JacobianExists`, `R16_EichlerShimuraJ1'`, `DimJ1Genus`,
  `ModCurveLeaves`, `exists_J1`. Nothing copied in.

## Expected trouble spots
- `open LeafModCurves` in Leaves.lean also brings that namespace's local copies of `coeff`, `CF`,
  `IsNewform`, … (absent from the kernel). x1-belyi uses none of these tokens; a script check found no
  ambiguity. `coeff` is not used, so `open Polynomial` does not clash.
- The two anonymous instances (`CharZero Kbar`, `EjBar.IsElliptic`) are new in namespace `X1Belyi`.
  Leaves.lean has no `CharZero Kbar` instance.

## g0-split's `X1BelyiOnModel` (scratch/g0-split/part_split.lean L114-129): assessment
**It follows from `LeafModCurves.BelyiX1` alone, plus pure transport glue.** It does not need
`X1ModelExists` or T33. The `IsJ1 N J` hypothesis already supplies:
- the model `X`, `P₀`, `aj` and `IsJacobian X P₀ J aj`;
- `IsX1Model N X`, i.e. `IsCurve X`, `hI : IsIntegral X.left`, `P` with `addOrderOf P = N`, and
  `φ : X.left.functionField ≃+* fieldX1 P`.

`X1ModelExists` plus T33 give `∃ J, IsJ1 N J` (`exists_J1`). That is the non-vacuity of
`X1BelyiOnModel` / `JavanpeykarJ1`, not part of the implication. So with this fragment, `X1BelyiOnModel`
reduces to T1 + T2 (via `belyiX1_of_leaves`) plus the transport below. The transport is about
50-100 lines of glue and is not written in the fragment.

The transport needs three things:
- the ℚ-algebra structure on `ℚ(X)` (`ffAlgebra X`) agrees with the one pulled back along `φ`, since
  ring homs out of `ℚ` are unique (`RingEquiv.toRatAlgEquiv`);
- `IsBelyiFunction` transports along a `k`-algebra isomorphism, using `ValuationSubring.comap` and
  `ValuationSubring.mem_nonunits_iff_or`;
- `[ℚ(X) : ℚ(t)] = [K_N : ℚ(j)]`, because `ℚ(t) = image of ℚ(j)` (`t = j/1728`, `RatFunc.adjoin_X`),
  via `Algebra.finrank_eq_of_equiv_equiv`.

Positivity of `d` follows from `IntermediateField.adjoin.finiteDimensional`.

Lean sketch (not compiled; lemma names partly unverified):
```lean
theorem isBelyiFunction_map {k F F' : Type} [Field k] [Field F] [Field F'] [Algebra k F]
    [Algebra k F'] (ψ : F ≃ₐ[k] F') {t : F} (h : LeafModCurves.IsBelyiFunction k F t) :
    LeafModCurves.IsBelyiFunction k F' (ψ t) := by
  refine ⟨fun ha => h.1 ((isAlgebraic_algHom_iff (ψ : F →ₐ[k] F') ψ.injective).mp ha), ?_⟩
  intro w hk ht q hqm hqi hqX hqX1 hq x hx
  let w' : ValuationSubring F := w.comap (ψ : F →+* F')
  have hnu : ∀ y, y ∈ w'.nonunits ↔ ψ y ∈ w.nonunits := fun y => by
    simp [w', ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
  have haev : ∀ y, ψ (Polynomial.aeval y q) = Polynomial.aeval (ψ y) q :=
    fun y => Polynomial.aeval_algHom_apply (ψ : F →ₐ[k] F') y q
  obtain ⟨y, hy, hxy⟩ := h.2 w' (fun c => by simpa [w', ValuationSubring.mem_comap] using hk c)
    (by simpa [w', ValuationSubring.mem_comap] using ht) q hqm hqi hqX hqX1
    ((hnu _).2 (by rw [haev]; exact hq)) (ψ.symm x) ((hnu _).2 (by simpa using hx))
  refine ⟨ψ y, hy, ?_⟩
  simpa [map_mul, haev] using congrArg ψ hxy

theorem x1BelyiOnModel_of_belyiX1 (hB : LeafModCurves.BelyiX1) : X1BelyiOnModel := by
  rintro N hN J ⟨X, P₀, aj, ⟨hC, hI, P, hP, ⟨φ⟩⟩, hJac⟩
  letI := ffAlgebra X
  obtain ⟨hBel, hdeg⟩ := hB N P hN hP
  let ψ : LeafModCurves.fieldX1 P ≃ₐ[ℚ] X.left.functionField := φ.symm.toRatAlgEquiv
  set t₀ := algebraMap LeafModCurves.Qj (LeafModCurves.fieldX1 P) (RatFunc.X / 1728)
  haveI : FiniteDimensional LeafModCurves.Qj (LeafModCurves.fieldX1 P) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  -- ι : ℚ(j) → ℚ(X); its field range is ℚ(ψ t₀) (⊇: ψ t₀ = ι (j/1728);
  -- ⊆: RatFunc.adjoin_X and ι j = 1728 • ψ t₀)
  let ι := (ψ : _ →+* X.left.functionField).comp (algebraMap LeafModCurves.Qj _)
  have hrange : ι.fieldRange = (IntermediateField.adjoin ℚ {ψ t₀}).toSubfield := sorry
  let i : LeafModCurves.Qj ≃+* IntermediateField.adjoin ℚ {ψ t₀} := sorry -- from ι, injective, hrange
  have hd := Algebra.finrank_eq_of_equiv_equiv i ψ.toRingEquiv (by ext a; rfl)
  exact ⟨X, hC, hI, P₀, aj, hJac, ψ t₀, isBelyiFunction_map ψ hBel, _, hd.symm,
    Module.finrank_pos, hdeg⟩
```
