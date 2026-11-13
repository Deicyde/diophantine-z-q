# rv-gluepieces2: review of six GluePieces2 fields (misc batch)

Reviewer: adversarial statement review, 2026-11-13. Read-only. No Lean was run.
File: `scratch/g0-assemble/G0Assemble.lean` (written "GA" below). `GluePieces2` is at GA L41938-41998.
Evidence tags: VERIFIED (I read or diffed it), STANDARD (published, reference given), SPECULATIVE.
All theorem numbers quoted from memory are UNVERIFIED.

| field | kind | verdict |
|---|---|---|
| `G0FibreSimple.MulIsogeny` (GA L36128) | LEAF | TRUE |
| `G0FibreSimple.RigidityHom` (GA L36193) | LEAF | TRUE |
| `G0FibreSimple.FiniteDescends` (GA L36324) | GLUE | TRUE, proved (identical copy) |
| `G0Split.ThetaPt.ThetaRatiosAlgebraic` (GA L41407) | LEAF candidate | TRUE as mathematics; a composite, not one printed theorem |
| `G0ModField.FibreCoverExists` (GA L39815) | GLUE | UNSURE (likely TRUE); only reduced, not proved |
| `G0ModField.UnramifiedSup` (GA L39770) | GLUE | TRUE, proved (identical copy) |

## 0. Shared definitions (VERIFIED)

- `PkgI3.AbVar K` (GA L2555): `X : Over (Spec K)` with `[GrpObj X]`, `IsProper X.hom`,
  `Smooth X.hom` and `GeometricallyIntegral X.hom`. Commutativity is a theorem (L2569, Stacks
  0BFD). This is a genuine abelian variety (Milne's definition), so it is not a placeholder.
- `Hom A B` (L2580-2600): the subgroup `{f | IsMonHom f}` of the pointwise group `A.X ⟶ B.X`,
  written additively. `End A` (L2615) is a `Ring` with `mul f g = g ≫ f` and `one = 𝟙`.
  `natCast` and `intCast` are not overridden, so the Mathlib defaults apply (`Nat.unaryCast`,
  `Int.castDef`). Then `((n : ℤ) : End A).hom` is the `n`-fold pointwise product of `𝟙` with
  itself (inverted for `n < 0`). That is exactly `[n]`. The `PkgI4.I3` copy (L3821) is a
  different type and does not interfere.
- `IsIsogenyMor f := IsFinite f.left ∧ Surjective f.left` (L2639).
- No project definition shadows `IsFinite`, `Surjective`, `Spec`, `Flat`, `IsMonHom`, `Over` or
  `toUnit` in the namespaces opened at L35864-35867. A grep finds only
  `LeafModCurves.pullback` (L16556), and that namespace is not opened.

## 1. `MulIsogeny`: TRUE (LEAF)

Statement (L36128): `∀ k [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
IsIsogenyMor ((n : End A).hom)`.

- **The cast really is `[n]`** (VERIFIED, §0).
- **Content.** `[n]` is finite, flat and surjective of degree `n^{2g}` over any field when
  `n ≠ 0`. STANDARD: Mumford, *Abelian Varieties*, §4 Application 2 and §6; Milne, *Abelian
  Varieties* (Cornell–Silverman), Thm 8.2. Restricting to characteristic 0 and dropping the
  degree makes the statement weaker than the published one, not stronger.
- **Dimension 0.** `A = Spec k`, so `[n] = 𝟙`, which is finite and surjective. The statement
  holds.
- **Empty `A`.** Excluded by geometric integrality. Even if `A` were empty, the empty map is
  finite and surjective.
- **Universe.** `k : Type`. This is no stronger than the published statement.

Use (L36153-36188): the leaf is applied only to `[s]` with `s ≠ 0` from clearing denominators.
No issue.

## 2. `RigidityHom`: TRUE (LEAF)

Statement (L36193): `∀ k [Field k] (A B : PkgI3.AbVar k) (h : A.X ⟶ B.X),
η[A.X] ≫ h = η[B.X] → IsMonHom h`.

- **Target.** `IsMonHom h` means `η ≫ h = η` (the hypothesis) together with
  `μ ≫ h = (h ⊗ h) ≫ μ`. For a morphism of group objects this is exactly "is a homomorphism"
  (`IsMonHom` of a group object also gives compatibility with inverses). This is the right
  target.
- **Truth over any field** (STANDARD). Milne, *Abelian Varieties*, Thm 1.1 (rigidity) and
  Cor 2.2 (Mumford §4 Cor 1 is over `k̄`). Apply rigidity to
  `α(x, y) = h(x+y) − h(x) − h(y) : A × A → B`. It needs:
  - `A` complete and `A × A` geometrically irreducible, which follows from proper and
    geometrically integral;
  - a `k`-point `0` with `α(A × {0}) = {0}`;
  - `B` separated.

  All of these hold here, so `α` is constant, equal to `0`.
- **No group axioms assumed on `B` beyond `GrpObj`.** None are needed.
- **Dimension 0.** If `A = Spec k`, then `h = η_B` and both sides of the `mul` equation are
  `η_B`, so it holds. If `B = Spec k`, everything is trivial.

Nothing makes the leaf stronger than the published statement. Its use in L36200-36260 is
correct as glue (it compiled).

## 3. `FiniteDescends`: TRUE, proved (GLUE)

Statement (L36324-36328): for fields `K → L` and any `g : X ⟶ Y` in `Over (Spec K)`, if
`((Over.pullback (Spec L → Spec K)).map g).left` is finite then `g.left` is finite.

- **Mathematics** (STANDARD). Finiteness is fpqc-local on the base (EGA IV₂ 2.7.1; Stacks
  02LA). `X_L → Y_L` is the base change of `g` along `Y_L → Y`, which is faithfully flat and
  quasi-compact.
- **Diff** (VERIFIED). The body of `FS1Descend.FiniteDescends` in
  `scratch/fs1-descend/FiniteDescends.lean` L34-38 is character-identical to GA L36324-36328.
  - Both bind `K L : Type` and depend only on Mathlib names.
  - No shadowing in GA (§0).
- **Compiled** (log, VERIFIED as read). `scratch/fs1-descend/log.md` records:
  - `FS1Descend.finiteDescends` compiled with standard axioms;
  - an integration check against g0-fibresimple's own `FiniteDescends`
    (`finiteDescends_proof : FiniteDescends := FS1Descend.finiteDescends`, typechecked).
- **Proof route** (read). `IsFinite = IsProper ⊓ LocallyQuasiFinite`. Properness descends via
  `IsSeparated = diagonal UniversallyClosed`. Local quasi-finiteness descends by the
  fibre-cardinality criterion. This is sound.

**Recommendation.** GA could replace the field with `FS1Descend.finiteDescends`. The proof is
Mathlib-only, so this needs only the `set_option backward.isDefEq.respectTransparency.types
false` noted in the log.

## 4. `ThetaRatiosAlgebraic`: TRUE as mathematics (LEAF candidate, composite)

Statement (L41407). Take `K` a number field, `A : PkgI3.AbVar K`, `σ : K → ℂ`, `Λ ≤ ℂ²`, and
`Φu : ℂ² → A(ℂ)_σ` with `IsUniformization σ Λ Φu`. Then for every `Ω` with `IsSiegel Ω` and
`IsPeriodMatrix Λ Ω` there is `m₀` such that:
- `thetaConst Ω m₀ ≠ 0`, and
- `∀ m, IsAlgebraic ℚ (thetaConst Ω m / thetaConst Ω m₀)`.

**Definitions in scope** (VERIFIED). L41131 opens `ZInQ.LeafPush2 (CPts cptObj IsUniformization
IsSiegel IsPeriodMatrix Char2 thetaConst ...)`. Those are at GA L20641-20702, inside
`namespace ZInQ.LeafPush2` (L18862-21119).

The other `thetaConst`s:
- `PkgI1.thetaConst` (L192, argument order `m Ω`, with the exponent `πi vᵀb` written
  equivalently);
- the copy at L34517.

Neither is opened here. `thetaConst Ω m` only typechecks with the `LeafPush2` argument order.

- `IsUniformization` (L20668). `Φ` is a group homomorphism, `Φ z = 1 ↔ z ∈ Λ`, `Φ` is
  surjective, the preimages `cDom Φ U` are open, and every regular function composed with `Φ`
  is holomorphic on `cDom`. Affine charts embed `U(ℂ)` in `ℂᴺ`, so `Φ` is a holomorphic
  homomorphism `ℂ² → A_σ^an`. Hence `Φ = exp ∘ dΦ₀`.
  - If `dim A > 2`, surjectivity fails (the image has measure zero).
  - If `dim A < 2`, then `Λ ⊇ ker dΦ₀` is uncountable, while `IsPeriodMatrix` needs a
    bijection `Λ ≅ Ωℤ² + ℤ²`, which is countable. So the hypotheses fail.
  - So in every non-vacuous case `dim A = 2`, `Λ` is the period lattice in some linear
    coordinates, and `ℂ²/Λ ≅ A_σ(ℂ)` (SPECULATIVE-light, standard Lie theory).
- `IsSiegel` (L20677): `Ωᵀ = Ω` and `(Im Ω).PosDef`. This is genuine `𝔥₂`, so the theta series
  is absolutely summable and the `tsum` is not junk.
- `IsPeriodMatrix Λ Ω` (L20686): some `ℂ`-linear automorphism `T` of `ℂ²` has `T(Λ) = Ωℤ² + ℤ²`.
  It does **not** tie `Ω` to a polarization chosen on `A`.
  - That is harmless. For `Ω ∈ 𝔥₂`, the torus `X_Ω = ℂ²/(Ωℤ² + ℤ²)` carries the principal
    polarization `H = (Im Ω)⁻¹`, and `(Ωe₁, Ωe₂, e₁, e₂)` is a symplectic basis of type `(1,1)`
    (Birkenhake–Lange §8.1; STANDARD).
  - So the hypothesis says exactly: `A_σ^an` has some principal polarization and `Ω` is its
    normalized period matrix in some symplectic basis.
  - Non-principal polarizations and non-symplectic bases are excluded by the shape
    `Ωℤ² + ℤ²` together with `Ω ∈ 𝔥₂`. If `A` is not principally polarizable, the hypotheses
    are empty.
- `thetaConst` (L20697): `∑_{n∈ℤ²} exp(πi (n+a/2)ᵀΩ(n+a/2) + 2πi (n+a/2)ᵀ b/2)`. This is the
  standard `θ[a;b](0, Ω)` (Mumford, Tata I, II §1).
- **Odd characteristics and division by zero.** The six odd characteristics give `θ = 0`, so
  their ratios are `0`, which is algebraic. That is correct, not a vacuity. Division by zero
  cannot help, because the denominator is required to be nonzero.
- **"Algebraic" means `IsAlgebraic ℚ` in `ℂ`.** That is the right notion (`ℚ̄ ⊂ ℂ`).

**Why it is true** (STANDARD composite; Shimura and Igusa locators UNVERIFIED):
1. `A_σ^an ≅ X_Ω`, so `H` is a polarization of `A_ℂ`. By Appell–Humbert and GAGA it comes from
   an ample line bundle.
2. The polarization is defined over `ℚ̄` because `NS(A_ℚ̄) = NS(A_ℂ)` (homomorphisms
   `A → A^∨` do not change under extension of algebraically closed fields; Lang, *Abelian
   Varieties*; Milne). So `(A_ℚ̄, λ)` is a principally polarized abelian surface over `ℚ̄`.
3. `θ_m/θ_{m₀}` is a Siegel modular function for `Γ₂(4,8)` with algebraic (cyclotomic) Fourier
   coefficients. Its value at a moduli point (with level structure) defined over `ℚ̄` is
   algebraic. Sources: Shimura (Duke 43, 1976, and his papers on algebraicity of Fourier
   coefficients); Faltings–Chai Ch. V (`q`-expansion principle); for genus 2 also Thomae's
   formula (Mumford, Tata II, IIIa §8).
4. A change of symplectic basis acts by `Sp₄(ℤ)`, which permutes the characteristics up to
   8th roots of unity and a common factor. So "every `Ω`" is no stronger than "some `Ω`".
5. Nonvanishing: in genus 2 at most one even `θ_m(0, Ω)` vanishes on `𝔥₂` (Igusa 1962/67), so
   `m₀` exists.

**Not stronger than published.** Each step is a published, standard result. The universal
quantification over `Ω` is covered by steps 1, 2 and 4.

**Caveat for the leaf audit.** It is not one printed theorem. It needs steps 1 and 2 (the
algebraicity and `ℚ̄`-rationality of an analytic principal polarization) in front of
Shimura/Thomae. The docstring and docs/research/g0-thetapoint.md L59-62 already say this. I
found no refutation:
- no characteristic-2 issue, since all fields involved have characteristic 0;
- no vanishing-denominator issue;
- no loose period-matrix quantifier.

## 5. `UnramifiedSup`: TRUE, proved (GLUE)

Statement (L39770-39772): for `E, K` finite Galois in `ℚ̄`, any `p : ℕ`, if `UnramifiedAt E p`
and `UnramifiedAt K p` then `UnramifiedAt (E ⊔ K) p`.

- **Definition in scope.** `G0ModField` opens `GlueDescent.B2Q`, so `UnramifiedAt` is GA L8827:
  every prime `P` of `𝓞 L` with `(p : 𝓞 L) ∈ P` has `ramificationIdx = 1`. This is genuine.
  - The other copy, `GlueB3Unram.UnramifiedAt` (L12522), is not opened, and its body is
    identical anyway.
  - `IF = IntermediateField ℚ (AlgebraicClosure ℚ)` (L39123).
- **Diff** (VERIFIED). `diff` of GA L39770-39772 against `scratch/unram-tate/UnramSup.lean`
  L32-34 reports them identical.
  - `UnramSup.lean` opens the same `GlueDescent.B2Q` from `ZInQKernel/HDecomp/Descent/B2Glue.lean`
    L310, whose body is identical to GA L8827-8829.
  - `IF` and `Qbar` are identical.
  - It is also identical to `scratch/g0-mod-field/ModField.lean` L704-706.
  - `scratch/unram-tate/TateBridge.lean` L1891 proves `unramifiedSup_mf : G0ModField.UnramifiedSup`
    against the ModField copy itself.
- **Compiled** (log, VERIFIED as read). Standard axioms. The proof works through the inertia
  group: `#I = e = 1`, then lift to `G_ℚ`.
- **`p = 0` or `p` composite.** `UnramifiedAt E 0` is false (`⊥` is a prime containing `0`, and
  its ramification index is the junk value `0`). That only makes the hypothesis vacuous. The
  field is proved for all `p` anyway.

**Recommendation.** Replace the field with the proved theorem.

## 6. `FibreCoverExists`: UNSURE (likely TRUE); not proved

Statement (L39815-39818): for all `Y, Φ, π, u, P` with `FibreCtx Y Φ π u P` (R1fp, R2fp,
`u ∉ 𝒞`, and a `ℚ̄`-point `y` over `J(u)` with `Φ y = [P]`), there is a separable `f ∈ ℚ[X]` of
degree `≤ 324` such that:
- its splitting field in `ℚ̄` is unramified at every prime `p ∉ T u`, and
- the splitting field carries a `RationalFibre`.

**Diff** (VERIFIED). A script compared GA against `scratch/fibre-cover/FibreCover.lean` for
`IF`, `T`, `IsModelOver`, `FibreCtx`, `RationalFibre`, `FibreCoverOut` and `FibreCoverExists`:
all are character-identical, in the same namespace with the same opens (except
`GlueDescent.B3Q`, which is absent under its imports and unused by these definitions).

**Status.** fibre-cover only **reduces** it (`fibreCoverExists_of_propTS`, `..._propTSAll`, 14
theorems with standard axioms). The reduction lands on open Props:
- `InnerTwistCount` (glue);
- `PropTS` (Beckmann specialization, the large item);
- `CurvePinned` or `PropTSAll` (glue);
- `UnramifiedConjugates` (textbook);
- T5 (a bundle leaf).

No proof transfers.

**My analysis.**
- **(a) `Φ` is irrelevant** (VERIFIED as read). `fibreCoverOut_iff` makes the output a property
  of `residueImage y` alone. Moreover R1fp naturality and bijectivity force `κ(y)` to be the
  field of definition of the class `[P]`. That is intrinsic to `P`, so relabelings of `Φ` that
  preserve residue fields cannot change it.
- **(b) The weak point is `π`.** R2fp fixes the `ℚ̄`-fibres of `π` only as `Φ`-preimages of
  `W`-orbits. `Φ` (natural on all fields) can permute closed points in a way that preserves
  residue fields and is not induced by a morphism. So nothing in the clauses forces the twist
  class lying over `J(u)` to be the "true" one over `J(u)`. It could instead be a class whose
  true value is a rational `s` with `T(s) ≠ T(u)`.
  - The ramification of `κ(y)` is controlled by the true value `s`. If `π⁻¹(J(u))` could be the
    true fibre over `s`, the field could ramify at primes of `T(s) \ T(u)`, and the Prop would
    be FALSE.
  - Against this: `π` is a genuine morphism over `ℚ`, and residue fields are preserved, so
    `κ(y)` is unramified outside `T(u)` iff the residue fields of `π₀⁻¹(s)` are.
  - docs/research/fibre-cover.md §3.2 argues that `π` is Galois with the same branch data
    `(4, 6, 2)` over `0, ∞, −16/27`, so Beckmann applies to `π` directly (`PropTSAll`). This is
    SPECULATIVE. I could neither confirm nor refute it, in particular whether a `ℚ`-form of the
    cover could have bad reduction at some `p ∉ T(u)` beyond Beckmann's field of moduli.
- **(c)** No Lean-checkable refutation suggests itself: a counterexample would need a second
  admissible `(Y, π)`, which cannot be built in Mathlib.

**Recommendation.** Treat it as open glue with a known pinning dependency, as fibre-cover.md
says, and prefer the qm-pin repair (R1 via a universal family, after which `CurvePinned` is light
glue). Not refuted.

## 7. Optional Lean sanity check (append after GA's content)

This confirms that the `ℤ`-cast in `End A` is `[n]` (here `n = 2`: the pointwise square of `𝟙`).
The expected result is that it compiles. The proof is a guess and was not run.

```lean
open CategoryTheory in
theorem rv_misc_intCast_two {k : Type} [Field k] (A : PkgI3.AbVar k) :
    ((2 : ℤ) : PkgI3.AbVar.End A).hom = 𝟙 A.X * 𝟙 A.X := by
  rw [Int.cast_ofNat, ← _root_.one_add_one_eq_two, PkgI3.AbVar.Hom.hom_add]; rfl
```

## 8. Summary

- Of the six fields, none is FALSE, five are TRUE and one is UNSURE (`FibreCoverExists`).
- `FiniteDescends` and `UnramifiedSup` have compiled proofs of character-identical statements.
  GA should replace those fields with the proved theorems.
- `ThetaRatiosAlgebraic` is true, and its period-matrix quantifier is tight. It remains a
  composite (polarization algebraicity plus Shimura/Thomae/Igusa), so it is a leaf candidate
  for human audit.
