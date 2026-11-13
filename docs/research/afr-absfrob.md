# afr-absfrob: `AbsFrob` and `FExtendGen` (from alg-frob-red)

Task afr-absfrob, 2026-11-13. Lean: `scratch/afr-absfrob/`. Log: `scratch/afr-absfrob/log.md`.

## 1. Result

**`AlgFrobRedRed.AbsFrob`, copied verbatim, is proved from Mathlib alone.** The proof
constructs the absolute Frobenius of a scheme, which Mathlib 4.35 does not have
(`scratch/afr-absfrob/AbsFrobDef.lean`, imports only `Mathlib`; `#print axioms
AlgFrobRedRed.absFrob` = `[propext, Classical.choice, Quot.sound]`, VERIFIED by `lake env lean`).

**`AlgFrobRedRed.FExtendGen`, copied verbatim, is proved from the kernel leaf I2-NMP
(`PkgI2.NeronMappingAbelianScheme`, BLR §1.2):**
`fExtendGen_of_nmp : PkgI2.NeronMappingAbelianScheme.{0} → FExtendGen`. Only the surjectivity half
of I2-NMP is used. Everything else is proved from Mathlib and alg-frob-red's lemmas (`owDVR`,
`tSig`). It compiles, and its `#print axioms` is `[propext, Classical.choice, Quot.sound]`
(VERIFIED).

```
theorem AlgFrobRedRed.algFrobRed_of_nmp (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed
theorem AlgFrobRedRed.tateBridge35_of_nmp (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) : G14Bridge.TateBridge35
```

Together with alg-frob-red's `algFrobRed_of_gen`, `FrobTrace.AlgFrobRed` then rests on
`GoodRedCofinite`, `SmoothGeomConnIntegral` (leaf candidates), I2-Red and I2-NMP (kernel leaves)
only; the two glue Props of alg-frob-red are gone.

No statement was changed. The copies of `AbsFrob` (in `AbsFrobDef.lean`) and of `FExtendGen`,
`FExtendCore` (in `src_AlgFrobRed.lean`, a `cmp`-identical copy of
`scratch/alg-frob-red/AlgFrobRed.lean`) are byte-identical to alg-frob-red's.

## 2. The absolute Frobenius (`AbsFrobDef.lean`, namespace `AbsFrobDef`)

For a prime `p` and a scheme `X` with `(p : Γ(X, ⊤)) = 0`:

| declaration | content |
|---|---|
| `powHom p R h : R →+* R` | `x ↦ x ^ p` for a commutative ring with `(p : R) = 0`; the ring may be trivial (empty open), so no `CharP` instance is assumed (case split: subsingleton, or `CharP R p` by `charP_iff_prime_eq_zero`). |
| `natCast_sections` | `p = 0` in every `Γ(X, U)` (restriction of `p = 0` in `Γ(X, ⊤)`). |
| `frobC p X hX` | the natural transformation `O_X ⟶ (𝟙 X)_* O_X`, `s ↦ s ^ p` on each `Γ(X, U)`. |
| `frobPSh p X hX` | the morphism of presheafed spaces `(𝟙, frobC)`. |
| `frob_stalkMap` | its stalk map is `a ↦ a ^ p` (germ calculus: `exists_germ_eq`, `stalkMap_germ_apply`). |
| `fr p X hX : X ⟶ X` | **the absolute Frobenius**, a morphism of schemes: stalk maps are local because `a ^ p` a unit forces `a` a unit (`isUnit_pow_iff`). |
| `fr_base`, `fr_app` | `Fr.base = 𝟙`, `Fr.app U = (s ↦ s ^ p)` (both `rfl`). |
| `fr_naturality` | `f ≫ Fr_X = Fr_Y ≫ f` for every `f : Y ⟶ X` (`Scheme.Hom.ext`: equal bases, and `f.app` commutes with `p`-th powers). |
| `fr_Spec` | `Fr_{Spec R} = Spec.map (powHom p R h)` (`ext_of_isAffine` and `ΓSpecIso_naturality`). |
| `natCast_Spec`, `natCast_of_hom` | `p = 0` on `Spec R` if `p = 0` in `R`, and on any `X → Spec R`. |

Then (namespace `AlgFrobRedRed`): `frobenius_eq_powHom` and

```
theorem AlgFrobRedRed.absFrob : AbsFrob
```

with `Fr := fr p X.left _`. The over-`Spec k` clause is `fr_naturality` for `X.hom` plus
`fr_Spec k`; the point clause is `fr_naturality` for `g` plus `fr_Spec R`.

## 3. `FExtendGen` from I2-NMP (`part_fext.lean`)

Statement (alg-frob-red, informal): for `L ⊆ ℚ̄` finite Galois, an abelian variety `A/L`, a
scheme endomorphism `F` of `A`, `σ` an arithmetic Frobenius at `v ∣ p`, an abelian scheme `𝒜`
over `O_w = v ∩ L` with `e : 𝒜_L ≅ A`, and an additive `f` on `A(ℚ̄)` with
`f(x) = Spec(σ) ≫ x ≫ F`: there is `F̃ : 𝒜 → 𝒜` over `Spec t` (`t = σ⁻¹|_{O_w}`), fixing the
unit section, with `e⁻¹ ≫ pr₁ ≫ F̃ = F ≫ e⁻¹ ≫ pr₁`.

Proof (each step a Lean lemma or a block of `fExtendGen_of_nmp`):

1. **`F` lies over `Spec τ`, `τ = σ⁻¹|_L`.** From `f 0 = 0`: `Spec σ ≫ x₀ ≫ F = x₀` for the
   zero point `x₀ = Spec ι ≫ η_A`, hence `x₀ ≫ F = Spec ι ≫ Spec τ ≫ η_A`
   (`spec_aut_cancel`). So `F ≫ A → Spec L` and `A → Spec L → Spec τ` agree at the point `x₀`.
   `A` is integral (`GeometricallyIntegral.isIntegral_of_subsingleton`), and
   `hom_spec_eq_of_point` shows that two morphisms from an integral scheme to `Spec L`
   (`L/ℚ` normal) agreeing at one field-valued point are equal. Its algebraic core is
   `ringHom_eq_of_normal`: two ring maps `L → R` (`R` a domain) that agree after some
   `R → Q` are equal, since `ψ₂(ℓ)` is a root of `minpoly ℓ`, which splits in `L`.
2. **The conjugate model** `ℬ = (Over.pullback (Spec t)).mapGrp.obj 𝒜` is an abelian scheme:
   proper, smooth and geometrically connected are stable under base change (Mathlib instances
   for `pullback.snd`).
3. **The generic morphism** `φ : 𝒜_L → ℬ_L` is
   `pullback.lift (pullback.lift (E ≫ F ≫ E⁻¹ ≫ pr₁) (pr₂ ≫ jS)) pr₂`. The pullback condition
   is step 1 together with `jS ≫ Spec t = Spec τ ≫ jS`. I2-NMP (surjectivity, with
   `owDVR` for the DVR instance) gives `G : 𝒜 → ℬ` over `O_w` with `G_L = φ`. Set
   `F̃ = G ≫ pr₁`. It lies over `Spec t` (pullback condition), and
   `pr₁ ≫ F̃ = E ≫ F ≫ E⁻¹ ≫ pr₁`, which gives clause 3.
4. **The unit section.** Both `η ≫ F̃` and `Spec t ≫ η` are maps `Spec O_w → 𝒜` with the same
   composite to `Spec O_w`. Mathlib's `ext_of_isDominant_of_isSeparated` (`𝒜` separated,
   `Spec O_w` reduced, `Spec L → Spec O_w` dominant by `isDominant_Spec_map_of_injective`)
   reduces equality to the generic point. There, `pb_eta_fst` and `IsMonHom.one_hom` for
   `e⁻¹` turn it into `η_A ≫ F = Spec τ ≫ η_A`. This holds by the same lemma applied to
   `A → Spec L` and `Spec ℚ̄ → Spec L`, together with step 1's point identity.

## 4. Leaf / glue status after this task

| Prop | before | now |
|---|---|---|
| `AbsFrob` | glue | **proved** (Mathlib only) |
| `FExtendGen` | glue (from I2-NMP) | **proved from I2-NMP** (`fExtendGen_of_nmp`) |
| `FExtendCore`, `FExtend`, `FrobMorph` | proved from the two above | proved from I2-NMP / outright |

## 5. Checks

- Statements unchanged. `AbsFrob` in `AbsFrobDef.lean` is byte-identical to `part_red.lean`
  (`cmp` of the 11-line block). `FExtendGen`, `FExtendCore`, `AbsFrob` and every other
  alg-frob-red declaration come from `src_AlgFrobRed.lean`, which is `cmp`-identical to
  `scratch/alg-frob-red/AlgFrobRed.lean`. The proofs target those declarations (VERIFIED).
- Hypotheses of `FExtendGen` that the proof does not use: `IsFinite F`, `Surjective F`, and the
  Frobenius clause of `hσ`. Only `σ ∈ D(v)`, which defines `t`, is used. `p` and `LiesOver v p`
  are used only through `owDVR` (I2-NMP needs a DVR). This agrees with alg-frob-red's review,
  which noted that `IsFinite` and `Surjective` are unused.
- `AbsFrob` is not vacuous: `fr` is a genuine morphism of schemes (the identity on points,
  `p`-th power on sections); for `X = Spec R` it is `Spec(r ↦ r^p)` (`fr_Spec`).

## 6. What compiles, what remains

- `scratch/afr-absfrob/AbsFrobDef.lean` imports only `Mathlib`. It contains the absolute
  Frobenius, the verbatim `AbsFrob` and `absFrob`. `lake env lean`: no errors;
  `absFrob` has standard axioms (VERIFIED, log run 2).
- `scratch/afr-absfrob/AfrAbsFrob.lean` is assembled by `build.sh`: `src_AlgFrobRed.lean`, then
  the `AbsFrobDef` body, then `part_fext.lean`. `lake env lean`: exit 0, no `sorry`, every
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` (VERIFIED, log run 7). It needs
  the ZInQKernel oleans that `src_AlgFrobRed.lean` imports. The first run here built them with
  `lake build <those modules>`.
- **Remains** (unchanged from alg-frob-red, not in this task's scope):
  - the leaf candidates `GoodRedCofinite` and `SmoothGeomConnIntegral`;
  - the kernel leaves I2-Red and I2-NMP.
- **Integration notes:**
  - `AbsFrobDef.lean` is self-contained (Mathlib only) and could become a Contrib file as is.
  - In `fExtendGen_of_nmp`, `generalize hσ.1 = hσ1` comes first. Otherwise `rw` fails with
    "motive is not type correct at implicit transparency": the projection `hσ.1` goes through
    the def `PkgI4.IsArithFrob`.
  - For the same reason, `G.left` is retyped as `Gl : 𝒜.X.left ⟶ pullback 𝒜.X.hom (Spec t)`.
  - The proof needs `synthInstance.maxHeartbeats 400000`, as alg-frob-red's does.
