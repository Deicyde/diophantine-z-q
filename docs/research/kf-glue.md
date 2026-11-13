# kf-glue: `EndTransport` proved; `ConjIsogMaps` reduced to Galois descent (`TwistDescent`) and `MulIsogeny`

Task kf-glue, 2026-11-13.
- Lean: `scratch/kf-glue/KfGlue.lean` (7209 lines). `scratch/kf-glue/assemble.sh` builds it from:
  - verbatim copies: `scratch/kernel-field/KernelField.lean`, and `scratch/mul-rigidity/MulRigidity.lean`
    lines 3-182 and 205-604;
  - new parts: `scratch/kf-glue/Points.lean` (120 lines, Mathlib only) and `scratch/kf-glue/New.lean`
    (859 lines).
- Results log: `scratch/kf-glue/log.md`. Compiler output: `scratch/kf-glue/build7.txt`.
- Base: `wip/integrate-w38b` (f90cf864), merged with `origin/wip/kernel-field` and `origin/wip/mul-rigidity`.

## 1. Main result

**VERIFIED (compiled).** `lake env lean scratch/kf-glue/KfGlue.lean` exits 0, with no `sorry`
anywhere. Each of the 21 new `#print axioms` lines gives `[propext, Classical.choice, Quot.sound]`.
`Points.lean` also compiles on its own.

Both statements are kernel-field's, copied verbatim and unchanged (they sit inside the verbatim
copy of `KernelField.lean`).

**`EndTransport` (medium) is a theorem with no hypotheses.**

```
theorem G0ModField.KernelField.endTransport : G0ModField.KernelField.EndTransport
```

It combines two earlier results:
- kernel-field's `endTransport_of (endTransportBC_of_rigidity ·)`;
- mul-rigidity's proof of `RigidityHom` from Mathlib.

**`ConjIsogMaps` (large) is reduced to one glue Prop and one leaf (or two glue Props).**

```
theorem conjIsogMaps_of_descent (hMul : G0FibreSimple.MulIsogeny) (hD : TwistDescent) : ConjIsogMaps
theorem conjIsogMaps_of_kerUnitOpen (hK : MulRigidity.KerUnitOpen) (hD : TwistDescent) : ConjIsogMaps
theorem conjIsogMaps_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) (hD : TwistDescent) : ConjIsogMaps
```

- **`TwistDescent`** is the only new remaining glue. It is Galois descent of twisted isomorphisms
  between conjugate abelian varieties, from `ℚ̄` to the Hom field `L`. It has no moduli content: no
  `Y`, `Φ`, `π` or `j₀`.
- **`MulIsogeny`** is mul-rigidity's textbook leaf: `[n]` is finite and surjective in
  characteristic 0. mul-rigidity reduces it in two ways:
  - to the leaf `KerUnitOpen`, which follows in Lean from the published "`[n]` is étale"
    (`MulEtale`);
  - to two cotangent-space glue statements.

  Its reductions are included verbatim.
- All the moduli content of `ConjIsogMaps` is now proved:
  - A7 (`conj_iso_of_rational`, from R1fp and R2fp);
  - the transport of A7 to the Galois conjugates of the rational fibre;
  - Skolem–Noether;
  - the isogeny `ι(b)` and its quasi-inverse;
  - the discrepancy in `End_L`;
  - the points bookkeeping `m_σ(x) = F_σ ∘ x ∘ Spec σ`.

**Effect on `KernelFieldExists`** (g0-mod-field's piece, statement unchanged):

```
theorem kernelFieldExists_of_kerUnitOpen
    (hHFF : PkgI3.HomFreeFinite)              -- leaf T6 (Mumford §19 Thm 3)
    (hNOS : PkgI2.NeronOggShafarevich.{0})    -- leaf r7a (Serre–Tate 1968 Thm 1)
    (hRay : PkgI2.RaynaudCriterion.{0})       -- leaf r6
    (hTors : PkgI2.TorsionStructure.{0})      -- leaf t5
    (t27 : PkgI3.QMDichotomyYu)               -- leaf T27 (Yu 2013 Thm 1.1)
    (h5 : G0FibreSimple.FibreComTrivial)      -- glue FS5 (g0-fibresimple)
    (hK : MulRigidity.KerUnitOpen)            -- leaf (mul-rigidity; implied by MulEtale)
    (hD : TwistDescent)                       -- glue (this task)
    : G0ModField.KernelFieldExists
```

Compared with kernel-field's `kernelFieldExists_of_rigidity`:
- `RigidityHom` is gone, because it is a theorem;
- `ConjIsogMaps` is replaced by `KerUnitOpen` and `TwistDescent`.

Locators are as in the earlier reports and are UNVERIFIED.

## 2. The reduction chain (all compiled)

| level | statement | proved from | new proved inputs |
|---|---|---|---|
| 0 | `ConjIsogMaps` (verbatim) | level 1 | — |
| 1 | `SemilinearIsogMaps`: σ-semilinear finite surjective scheme endomorphisms `F_σ` of `A_L` (see below) | level 2 | `conjIsogMapsAt_of_semilinear`; `liftQbarPoints`, `finiteFibreQbarPoints` (from Mathlib) |
| 2 | `SemilinearTwistIsos`: σ-semilinear scheme automorphisms `E_σ` twisting `ι` by `α_σ ∈ Aut 𝒪` | level 3 + `MulIsogeny` | `exists_b`, `exists_quasi_inv`, `iota_isogeny`, `semilinearIsogAt_of_twist` (uses `rigidityHom`) |
| 3 | `TwistDescent` (general abelian varieties, no moduli data) | — (**remaining glue**) | `bc_transport`, `conjTwist_of_rational`, `semilinearTwistIsos_of_descent` |

**Level 1: `SemilinearIsogAt L A ι' F`.** For each `σ ∈ G_ℚ`, `F_σ : A → A` is a morphism of
schemes with the following clauses:
- it lies over `Spec τ` for some `τ : L ≃+* L` with `τ = σ⁻¹` on `L`;
- it respects the group law: `μ ≫ F_σ = pullback.map … F_σ F_σ (Spec τ) ≫ μ`;
- `ι'(a) ≫ F_σ = F_σ ≫ ι'(a)`;
- it is finite and surjective;
- `F_k = 𝟙` for `k ∈ G_L`, and `F` is constant on the double cosets of `G_L`;
- `F_τ ≫ F_σ ≫ [e] = F_{στ} ≫ δ`, with `e ≠ 0` and `δ ∈ End_L(A)`.

Given these, `m_σ(x) = Spec σ ≫ x ≫ F_σ` (`semHom`) satisfies every clause of `ConjIsogMapsAt`:
- additivity comes from the group-law clause;
- surjectivity and the finite kernel come from the two point lemmas below.

**The point lemmas (`Points.lean`, proved from Mathlib).**
- `LiftQbarPoints`: a finite surjective morphism is surjective on `ℚ̄`-points.
- `FiniteFibreQbarPoints`: a finite morphism has finite fibres on `ℚ̄`-points.

Proof. `P = pullback F y` is a finite affine scheme `Spec B` over `Spec ℚ̄`.
- A section exists: it comes from a maximal ideal `m` of `B`. The field `B/m` is finite over the
  algebraically closed `ℚ̄`, so `ℚ̄ → B/m` is bijective (`IsAlgClosed.ringHom_bijective_of_isIntegral`).
- There are finitely many sections: they inject into `B →ₐ[ℚ̄] ℚ̄`, which is finite by `Finite.algHom`.

**Level 2: `SemilinearTwistAt L A ι' E α`.** For each `σ`, `E_σ` satisfies:
- `IsIso E_σ`;
- it lies over `Spec τ` with `τ = σ⁻¹|_L`;
- it respects `μ`, and `η` (`η ≫ E_σ = Spec τ ≫ η`);
- `ι'(a) ≫ E_σ = E_σ ≫ ι'(α_σ a)`;
- `E_k = 𝟙` and `α_k = id` on `G_L`;
- `E` and `α` are constant on cosets.

The proof `semilinearIsogAt_of_twist` constructs `F_σ = E_σ ≫ ι(b_σ)`:
- `b_σ ≠ 0` satisfies `b_σ α_σ(a) = a b_σ`. It comes from Skolem–Noether on `𝒪` (`aut_O_inner`)
  and is chosen as a function of `α_σ`, with `b = 1` when `α_σ = id`.
- `ι(b)` is finite and surjective by `MulIsogeny`, because `ι(c) ι(b) = [N] = ι(b) ι(c)` with
  `c = N b⁻¹ ∈ 𝒪` (`exists_quasi_inv`).
- The discrepancy is `δ = ι(b_σ) ι(α_σ b_τ) D ι(c)`, where `D = E_{στ}⁻¹ E_τ E_σ`:
  - `D` lies over `Spec L` and fixes `η`, so it is in `End_L(A)` by `rigidityHom`;
  - `[N]` is central.

**Level 3: `TwistDescent`.** Data: `B/K` with `ι : 𝒪 → End B`, and finite Galois fields
`K ⊆ L ⊆ ℚ̄` such that `G_L` acts trivially on `conjAction K B` (`L` is a Hom field).

- Hypothesis: for any two embeddings `e₁, e₂ : K → ℚ̄`, there is an isomorphism `φ : B_{e₁} ≅ B_{e₂}`
  with `ι_{e₁}(α a) φ = φ ι_{e₂}(a)`. Here `ι_e = bcEnd` is base change to the conjugate
  `B_e = (G4WeilRes.conjData K B).A e`.
- Conclusion: `SemilinearTwistAt` holds on `B_L` for `ι_L = endBC ∘ ι`.

The hypothesis is proved for the rational fibre `PK` (`conjTwist_of_rational`):
- A7's manuscript form `conj_iso_of_rational` gives twisted QM isomorphisms between the base
  changes `Q_e`.
- `bc_transport` identifies `Q_e` with `B_e` as abelian varieties with `𝒪`-action. It uses the
  `IsBaseChangeOf` pullback square and `η`-compatibility, then `rigidityHom`, following the pattern
  of kernel-field's `endTransportBC_of_rigidity`.
- `π(yK) = j₀` holds in `K`, because `Φ` is injective and `val_comp` holds.

## 3. What remains

1. **`TwistDescent`** (glue; SPECULATIVE truth argument from a model check, no human review).
   - Construction. For `σ ∈ G_ℚ` put `Ē_σ = φ ≫ cmp` on `B_{ℚ̄} = B_{K.val}`:
     - `φ : B_{K.val} → B_{σ⁻¹ K.val}` is the twisted isomorphism, chosen on representatives of
       `G_ℚ/G_L`, with `φ = id` on `G_L`;
     - `cmp` is `G4Conj.cmp` over `Spec σ⁻¹`.
   - Properties of `Ē_σ`:
     - it is σ-semilinear and preserves `μ` and `η` (`cmp_mul`, `cmp_one`);
     - it twists `ι`, because `cmp` intertwines base-changed endomorphisms.
   - Descent. `L` is a Hom field, so `φ` is fixed by conjugation through `G_L`, and `Ē_σ` commutes
     with the descent datum of `B_{ℚ̄}/B_L`. It therefore descends to `B_L`.
   - **Finding (VERIFIED by reading Mathlib 4.35 `AlgebraicGeometry/Sites/Fpqc.lean`, L88-130).**
     Mathlib proves that the fpqc topology is subcanonical. It also gives `EffectiveEpi f` for
     quasi-compact, surjective, flat `f`, such as `Spec L' → Spec L` and its base changes.
   - So Galois descent of morphisms needs no new literature leaf. The project route has three steps:
     1. `morphismsDescend` (EGA IV 8.8.2, already proved) descends to a finite `L'`;
     2. take the Galois closure;
     3. use the `EffectiveEpi` of `X_{L'} → X` together with `L' ⊗_L L' ≅ ∏_{Gal(L'/L)} L'`,
        which splits the kernel pair into Galois translates.
   - Not formalized: steps 2 and 3 above, plus the bookkeeping that identifies `B_{K.val}` with
     `(B_L)_{ℚ̄}` and semilinear maps with maps out of `^σB_L`. A grep of Mathlib v4.35 found no
     `L' ⊗_L L' ≅ ∏ L'` for Galois `L'/L`.
   - **`GaloisDescentMor`** (`New.lean`, statement only, typechecked, unused) is the standard
     theorem in the project's language. Hypotheses: `X` quasi-compact and quasi-separated, `Y`
     locally of finite presentation over a number field `L ⊆ ℚ̄`. Claim: a `ℚ̄`-morphism
     `X_ℚ̄ → Y_ℚ̄` fixed by `G4Conj.conj` through `G_L` is the base change of a unique `L`-morphism.
     Sources: SGA 1 VIII; Stacks, fpqc descent; locators UNVERIFIED.
     - Whoever formalizes `TwistDescent` should prove this first.
     - The deduction `GaloisDescentMor ⟹ TwistDescent` is a model check (SPECULATIVE), not
       compiled.
2. **`MulIsogeny`** (mul-rigidity's open item). It reduces to the leaf `KerUnitOpen` (implied by
   `MulEtale`) or to two glue statements on the cotangent space at `0`.
3. **FS5 `FibreComTrivial`** (g0-fibresimple). Unchanged: it is the only NoCM input
   (kernel-field §4).

## 4. Findings

- **No literature leaf is needed for `ConjIsogMaps` beyond `MulIsogeny`.**
  - kernel-field §3 expected two inputs that are not needed:
    - the quasi-inverse (Mumford §8, the leaf `IsogenyQuasiInverse` of g0-reverseisog);
    - a separate Galois-descent leaf.
  - The quasi-inverse is explicit: `ι(N b⁻¹)`. Descent is Mathlib-derivable glue (§3.1).
  - The only isogeny input is that `[N]` is finite and surjective (`MulIsogeny`).
- **Porting note (VERIFIED, compiled).** kernel-field's `KernelField.lean` does not compile on this
  base as is.
  - Cause: `R1fpProps` now has six clauses (pin-apply's `R1famProps`, `R1univProps`), so
    `endTransport_of`'s proof term `hR1.2.2.2` must be `hR1.2.2.2.1`.
  - `assemble.sh` applies exactly this one-token fix to a proof. No statement changes.
- **Non-vacuity.**
  - The levels are linked by implications, so each new Prop implies `ConjIsogMaps`.
  - `ConjIsogMapsAt` is satisfiable (kernel-field's `conjIsogMapsAt_bot`).
  - `SemilinearTwistAt` is satisfied over `L = ℚ` by `E_σ = 𝟙`, `τ = id`, `α = id`, for every
    abelian variety and every `ι'`. This is compiled: `semilinearTwistAt_bot`.
  - `SemilinearIsogAt` is satisfied in the same way by `F_σ = 𝟙` (checked by reading).
- **`TwistDescent` is stated over genuine objects.**
  - It uses `PkgI3.AbVar`, Mathlib pullbacks, `G4WeilRes.conjData`/`conjAction`, `endBC`, and the new
    `bcEnd` (`Over.pullback` on endomorphisms).
  - It is a ∀-statement about all abelian varieties with an `𝒪`-action and a Hom field. Its
    hypothesis is exactly what A7 yields on the conjugates.

## 5. Integration

- `New.lean` needs only what `KernelField.lean` and `MulRigidity.lean` import, plus `Points.lean`
  (Mathlib only).
- In g0-assemble / g0-mod-field, replace `hKer : KernelFieldExists` by
  `kernelFieldExists_of_kerUnitOpen hHFF hNOS hRay hTors t27 h5 hK hD`.
- In g0-assemble's `GluePieces2` (docs/research/g0-assemble.md L76-88):
  - field 13 `kernelFieldExists` (GLUE, QM-PIN) can be replaced by
    `kernelFieldExists_of_descent hHFF hNOS hRay hTors t27 h5 hMul hD`. Its inputs are:
    - bundle leaves T6, r7a, r6, t5, T27;
    - field 4 FS5;
    - field 1 `mulIsogeny`;
    - the new glue `TwistDescent`.
  - The QM-PIN dependence of field 13 then sits entirely in FS5, as kernel-field §4 found.
    `TwistDescent` has no moduli data and is not QM-PIN.
  - Field 2 `rigidityHom` is a theorem (mul-rigidity; restated here).
- When merging into one file, keep a single copy of `RigidityHom`.
  - `assemble.sh` already omits MulRigidity.lean L184-203, which hold `RigidityHom` again and
    `rigidityHom`.
  - That copy of `RigidityHom` is identical to kernel-field's (checked with `diff`).
  - `rigidityHom` is restated in `New.lean` with mul-rigidity's proof.

## 6. Labels

- **VERIFIED (compiled):** every theorem in §1-§2 and its axiom list (`build7.txt`). Also
  `Points.lean` standalone.
- **VERIFIED (read):** Mathlib's `Fpqc.lean` (subcanonical, `EffectiveEpi`);
  `ResidueField.lean` (`SpecToEquivOfField`); the definitions `ConjIsogMapsAt`, `ConjIsogMaps`,
  `EndTransport`, `R1fpProps`, `IsBaseChangeOf`, `conjData`, `conjAction`, `RationalFibre`,
  `PtEquiv`, `ToP1.val_comp`, `conj_iso_of_rational`.
- **SPECULATIVE (model check):** the truth argument for `TwistDescent` (§3.1), and the Mathlib
  route to it.
- **UNVERIFIED locators:** Mumford §4, §8, §19; Serre–Tate 1968; Yu 2013; EGA IV 8.8.2.
