# twist-descent: `TwistDescent` proved (statement verbatim), and kf-glue's `GaloisDescentMor`

Task twist-descent, 2026-11-13. Base: fork main 57a7fa26 + `origin/wip/kf-glue`, later merged with
`origin/main` (b7cdba8e).

## 1. Main result

**VERIFIED (compiled).** `lake env lean scratch/twist-descent/TwistDescent.lean` exits 0 with no
`sorry` and no error (`scratch/twist-descent/build3.txt`, 1m24s wall; rechecked after the last edit of the Contrib file in `build4.txt`: rc=0, all 35 `#print axioms` lines standard). Every new `#print axioms`
line gives `[propext, Classical.choice, Quot.sound]`.

kf-glue's glue Prop `TwistDescent` is proved with its statement unchanged. So is kf-glue's
standard statement `GaloisDescentMor`, which kf-glue stated but did not use:

```
theorem G0ModField.KernelField.twistDescent : G0ModField.KernelField.TwistDescent
theorem G0ModField.KernelField.galoisDescentMor : G0ModField.KernelField.GaloisDescentMor
```

Both definitions are kf-glue's own text (`scratch/kf-glue/New.lean`), unchanged:
- They sit inside a verbatim copy of `scratch/kf-glue/KfGlue.lean`.
- `scratch/twist-descent/verbatim_check.py` (output in `verbatim_check_out.txt`) checks:
  - the `def` blocks of `TwistDescent`, `GaloisDescentMor`, `SemilinearTwistAt` and `bcEnd` equal the
    owner text in `New.lean`, and each is defined exactly once;
  - `New.lean` is verbatim inside `KfGlue.lean`;
  - the whole body of `KfGlue.lean` is verbatim inside `TwistDescent.lean`.

**Corollaries.** These are kf-glue's reductions with `TwistDescent` discharged, all compiled:

```
theorem conjIsogMaps_of_mulIsogeny (hMul : G0FibreSimple.MulIsogeny) : ConjIsogMaps
theorem conjIsogMaps_of_kerUnitOpen' (hK : MulRigidity.KerUnitOpen) : ConjIsogMaps
theorem conjIsogMaps_of_cotangent' (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) : ConjIsogMaps
theorem kernelFieldExists_of_kerUnitOpen' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hK : MulRigidity.KerUnitOpen) : KernelFieldExists
theorem kernelFieldExists_of_mulIsogeny (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny) : KernelFieldExists
```

All are in namespace `G0ModField.KernelField`.
- `ConjIsogMaps` (kernel-field) now depends only on `MulIsogeny`.
- g0-mod-field's `KernelFieldExists` now has these inputs:
  - leaves T6, r7a (NOS), r6 (Raynaud), t5, T27 and `KerUnitOpen`;
  - glue FS5 (`FibreComTrivial`).

**`#print axioms` output** (`build3.txt`):

```
'G0ModField.KernelField.galoisDescentMor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwistDescentGD.exists_open_gal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwistDescentGD.descend' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwistDescentXC.xc_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwistDescentXC.xc_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwistDescentHFD.hfd' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0ModField.KernelField.td_hom_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0ModField.KernelField.td_construct' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0ModField.KernelField.twistDescent' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0ModField.KernelField.conjIsogMaps_of_mulIsogeny' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0ModField.KernelField.conjIsogMaps_of_kerUnitOpen'' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0ModField.KernelField.conjIsogMaps_of_cotangent'' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0ModField.KernelField.kernelFieldExists_of_kerUnitOpen'' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0ModField.KernelField.kernelFieldExists_of_mulIsogeny' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2. Truth of `TwistDescent`

**`TwistDescent` is true as stated, and no correction is needed.** This is VERIFIED by the compiled
proof. kf-glue's speculative argument was correct in substance. The proof follows it with one
change: the descent is done on the linear isomorphism `φ` and not on the semilinear `Ē_σ`.

Fix `σ ∈ G_ℚ` and put `τ = σ⁻¹|_L`, `e₀ = (K ↪ ℚ̄)` and `e₂ = σ⁻¹ ∘ e₀`.
1. **The isomorphism over `ℚ̄`.** The hypothesis gives `α ∈ Aut 𝒪` and an isomorphism of abelian
   varieties `φ : B_{e₀} ≅ B_{e₂}` over `ℚ̄` with `ι_{e₀}(α a) φ = φ ι_{e₂}(a)`.
2. **`φ` is `G_L`-invariant** (`td_hom_inv`). Because `conjAction K B k = 1` for `k ∈ G_L`, we get
   `cmp_k ∘ φ = φ ∘ cmp_k`, where `cmp_k` is the comparison of `G4Conj` over `Spec k`.
3. **Descent of `φ`** (`TwistDescentHFD.hfd`). `φ` is the base change of an `L`-morphism
   `φ_L : B ×_{K} L → B ×_{K,τ∘(K↪L)} L`. Its inverse descends as well, so `φ_L` is an isomorphism.
4. **The semilinear automorphism.** Put `E_σ = φ_L ≫ c_τ`, where `c_τ` is the comparison over
   `Spec τ`; it is an isomorphism with inverse `c_{τ⁻¹}`.
   - `E_σ` lies over `Spec τ`.
   - It preserves `η` and `μ`. The reason is that `φ_L` is a homomorphism by rigidity
     (`G0FibreSimple.rigidityHom`, proved in kf-glue from Mathlib), and `c_τ` respects `η` and `μ`
     (`xc_one`, `xc_mul`).
   - With `α_σ = α⁻¹` we get `ι(a) E_σ = E_σ ι(α_σ a)`.
5. **Coset constancy.** `E_σ` and `α_σ` are chosen as functions of `σ|_L` (`twistDescent`):
   - on the trivial class, `E = 𝟙` and `α = id` (`twistClause_one`);
   - otherwise they come from step 4 for a lift of `σ|_L`. Restriction to `L` is surjective
     (`AlgEquiv.restrictNormalHom_surjective`).

   So `E_k = 𝟙` and `α_k = id` on `G_L`, and both are constant on the cosets
   `σ G_L = G_L σ`.

## 3. The Galois descent (the new mathematics, all compiled)

### `ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean`

This file needs only Mathlib (namespace `TwistDescentGD`). It builds with
`lake build ZInQKernel.Contrib.TwistDescent.GaloisDescent`.

```
theorem exists_open_gal [FiniteDimensional k k'] [IsGalois k k'] {Z : Scheme}
    (u v : Z ⟶ Spec (CommRingCat.of k'))
    (h : u ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      v ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
    (z : Z) : ∃ (U : Z.Opens) (g : k' ≃ₐ[k] k'), z ∈ U ∧
      U.ι ≫ v = U.ι ≫ u ≫ Spec.map (CommRingCat.ofHom (g : k' →+* k'))
theorem descend [FiniteDimensional k k'] [IsGalois k k'] {X X' Y : Scheme}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : X' ⟶ X} {s : X' ⟶ Spec (CommRingCat.of k')}
    (hpb : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (f : X' ⟶ Y)
    (hf : ∀ g : k' ≃ₐ[k] k', ∃ c : X' ⟶ X', c ≫ q = q ∧
      c ≫ s = s ≫ Spec.map (CommRingCat.ofHom (g : k' →+* k')) ∧ c ≫ f = f) :
    ∃ f₀ : X ⟶ Y, q ≫ f₀ = f
theorem epi_of_isPullback_field … (hpb : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap k k')))) : Epi q
```

**`exists_open_gal`.** This is the scheme form of `k' ⊗_k k' ≅ ∏_{Gal} k'`, which kf-glue listed as
missing from Mathlib. The proof avoids the tensor product.
- Take a primitive element `θ`.
- The polynomial `∏_g (X - gθ)` has coefficients in `k`. In Mathlib this is
  `Algebra.IsInvariant.charpoly_mem_lifts`, with `IsGaloisGroup.of_isGalois`.
- Hence `∏_g (v^♯θ - u^♯(gθ)) = 0` in `Γ(Z)`.
- The factors differ by units, so at each point exactly one germ is a non-unit, say the one for `g`.
  On the basic open where the other factors are invertible, `v^♯ = u^♯ ∘ g`.

**`descend`.**
- Mathlib makes `q` an `EffectiveEpi`: flat, surjective, quasi-compact (`Sites/Fpqc.lean`).
- The coequalizing condition for a test pair `a, b` is checked locally with
  `Scheme.hom_ext_of_forall`. On the opens of `exists_open_gal`, `b = a ≫ c_g`.

### `scratch/twist-descent/PartXC.lean` (namespace `TwistDescentXC`)

This generalizes `G4Conj.cmp` to two bases. For `f₂ = s ≫ f₁` with `s : T₂ ⟶ T₁` it defines
`xc X s h : X ×_{f₂} T₂ → X ×_{f₁} T₁` and proves:
- its pullback square (`xc_isPullback`);
- its composition rules (`xc_comp`, `xc_comp_eq`, `xc_self`);
- compatibility with base-changed endomorphisms (`xc_map`), the unit (`xc_one`) and the
  multiplication (`xc_mul`; it reuses `G4Conj.mul_left_fst` and `one_left_fst`).

### `scratch/twist-descent/PartHFD.lean`: `TwistDescentHFD.hfd`

Setting:
- `X` is quasi-compact and quasi-separated over `K ⊆ ℚ̄`, and `Y` is locally of finite presentation;
- `L ⊆ ℚ̄` is a number field, and `eᵢ = (L ↪ ℚ̄) ∘ eᵢL`.

Claim: a `ℚ̄`-morphism `φ : X ×_{K,e₁} ℚ̄ → Y ×_{K,e₂} ℚ̄` that commutes with the translates by `G_L`
satisfies `xc ≫ φ_L = φ ≫ xc` for some `φ_L : X ×_{K,e₁L} L → Y ×_{K,e₂L} L`.

Proof:
1. EGA IV₃ 8.8.2 (`MorphDescend.exists_descend`, already proved in the project) descends `φ` to a
   finite `L₁ ⊇ L`.
2. Let `L'` be the normal closure of `L₁`. Then `L'/L` is finite Galois
   (`IsGalois.tower_top_of_isGalois`).
3. The base change of `φ` to `L'`, followed by `L' → L`, is `Gal(L'/L)`-invariant. This is checked
   after the epimorphism `X_{ℚ̄} → X_{L'}`, by lifting `g ∈ Gal(L'/L)` to `k ∈ G_L`.
4. It therefore descends by `TwistDescentGD.descend`.

### `PartMain.lean` and `PartGDM.lean`

- `PartMain.lean`: `td_hom_inv`, `TwistClause` (the clauses of `SemilinearTwistAt` at one `σ`,
  written in terms of `σ|_L`), `twistClause_one`, `td_construct` and `twistDescent`.
- `PartGDM.lean`: `galoisDescentMor`. It applies `hfd` with `K = L`, `e₁L = e₂L = id`, and uses
  `X ×_{L,id} L ≅ X`. Uniqueness holds because `X_{ℚ̄} → X` is an epimorphism.

## 4. Files and how to check

- **New Contrib file:** `ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean` (Mathlib only).
- **Scratch parts:** `scratch/twist-descent/Part{XC,HFD,Main,GDM,Final}.lean`.
- **Assembly:** `scratch/twist-descent/assemble.sh` writes `scratch/twist-descent/TwistDescent.lean`
  (7959 lines). It consists of:
  - `scratch/kf-glue/KfGlue.lean` verbatim, with one import line added:
    `import ZInQKernel.Contrib.TwistDescent.GaloisDescent`;
  - the five parts.
- **Check:** run `lake build ZInQKernel.Contrib.TwistDescent.GaloisDescent`, then
  `lake env lean scratch/twist-descent/TwistDescent.lean`.
  - Compiler outputs: `build1.txt`–`build3.txt`. `build2.txt` is the run after merging
    `origin/main`.
  - About 1m25s wall, after a one-time `lake build ZInQKernel.Hypotheses.JHeight` (this builds the
    `lean/` helper package).
- **Verbatim:** `python3 scratch/twist-descent/verbatim_check.py`.
- **Dev loop used:** compile `KfGlue.lean` once to a `/tmp` olean (`lake env lean -o`, about 3.5 min),
  then check the parts against it with `LEAN_PATH` (10–25 s per iteration).
- **Vendoring:** no Tau Ceti code was vendored. `diffcheck2.py` reports MOD-UNNOTED 0 and
  NOTE-ONLY 0.

## 5. Integration notes

- In g0-assemble's `GluePieces2`, field 13 `kernelFieldExists` can be replaced in either of two
  ways:
  - `kernelFieldExists_of_mulIsogeny hHFF hNOS hRay hTors t27 h5 hMul`, which uses field 1
    `mulIsogeny`;
  - `kernelFieldExists_of_kerUnitOpen' … hK`.

  The open inputs of that path are then `MulIsogeny` (or `KerUnitOpen`) and FS5.
- `galoisDescentMor` is a general tool. It descends any `G_L`-invariant `ℚ̄`-morphism between base
  changes of `L`-schemes (source qcqs, target lfp) to `L`. `hfd` does the same for twisted
  conjugates. Other tasks that need Galois descent of morphisms (for example
  `HomDescends`-style arguments) can use them.

## 6. Labels

- **VERIFIED (compiled):** every theorem in §1 and §3 and its axiom list (`build3.txt`); the Contrib
  module (`lake build`).
- **VERIFIED (read):** Mathlib's `Sites/Fpqc.lean` (the `EffectiveEpi` instance for qc, surjective,
  flat morphisms), `Gluing.lean` (`Scheme.hom_ext_of_forall`), `RingTheory/Invariant/Basic.lean`
  (`charpoly_mem_lifts`), and `FieldTheory/Galois/IsGaloisGroup.lean` (`of_isGalois`).
- **UNVERIFIED locators:** EGA IV₃ 8.8.2; Stacks 023Q, as tagged in Mathlib.
