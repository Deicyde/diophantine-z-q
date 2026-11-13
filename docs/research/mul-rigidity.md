# mul-rigidity: `RigidityHom` proved from Mathlib; `MulIsogeny` reduced to two glue statements on the cotangent space at the origin (no literature leaf left)

Task mul-rigidity, 2026-11-13. Lean: `scratch/mul-rigidity/` (`Rigidity.lean`, `Mul.lean`, and
`MulRigidity.lean`, which `assemble.sh` builds from both and adds the g0-fibresimple consumers).
Log: `scratch/mul-rigidity/log.md`.

## 1. Result

**`RigidityHom` is a theorem.** It is the textbook leaf added by g0-fibresimple (Mumford §4 Cor. 1,
Milne Cor. 2.2; locators UNVERIFIED). Copied verbatim, it is proved in Lean from Mathlib, with no
hypotheses:

```
theorem G0FibreSimple.rigidityHom : G0FibreSimple.RigidityHom
```

Consequence: g0-fibresimple's glue piece FS2 now holds unconditionally:
`G0FibreSimple.endDivisionOfSchemeIso : EndDivisionOfSchemeIso`. Its proof
`endDivisionOfSchemeIso_of_rigidity` is copied verbatim and applied to `rigidityHom`.

**`MulIsogeny` reduces to two glue statements and needs no literature leaf.**

```
theorem MulRigidity.mulIsogeny_of_cotangent (h1 : KerUnitOpenOfCotangentSurj)
    (h2 : CotangentMulN) : G0FibreSimple.MulIsogeny
```

* `CotangentMulN`: the map `[n]` induces on `m₀/m₀²`, the cotangent space of the local ring
  `𝒪_{A,0}`, is `n • id`. This holds for every `n ∈ ℤ` and in every characteristic; it is the group
  law to first order.
* `KerUnitOpenOfCotangentSurj`: if a homomorphism `f : A → A` has surjective cotangent map at `0`,
  then the unit section of `ker f` is an open immersion. This is commutative algebra of the fibre,
  plus Nakayama.

Both are glue: standard and elementary, but not formalized. They are stated in Lean over Mathlib's
`stalkMap`, `IsLocalRing.CotangentSpace` and `Ideal.mapCotangent` (§3). The step in between is
proved: in characteristic 0, `n • id` is bijective on a vector space over the residue field at
`0`, which has characteristic 0 (`charZero_residueField`).

**Leaf alternative: the single leaf `KerUnitOpen`.** `MulIsogeny` (copied verbatim) says that in
characteristic 0, `[n]` is finite and surjective for `n ≠ 0`. It is also proved from a single
leaf, and the glue pair above passes through this leaf:

```
theorem MulRigidity.mulIsogeny_of_kerUnitOpen (h : KerUnitOpen) : G0FibreSimple.MulIsogeny
theorem MulRigidity.kerUnitOpen_of_mulEtale (h : MulEtale) : KerUnitOpen
```

`KerUnitOpen` says: in characteristic 0 and for `n ≠ 0`, the unit section
`Spec k → A[n] = A ×_{[n], A, e} Spec k` is an open immersion. In other words, the kernel `A[n]` is
unramified over `k` at the origin. `MulEtale` is the published statement "`[n]` is étale when
`char k ∤ n`" (Mumford §4 Application 2 and §6; Milne Thm 8.2; locators UNVERIFIED), restricted to
characteristic 0.

Lean derives `KerUnitOpen` from `MulEtale`, so the new leaf is a consequence of the published
statement and is no stronger than it. Everything else in the reduction is proved from Mathlib:
finiteness, surjectivity, the reduction from `[n]` to its kernel, and the step from unramified
to finite.

**Consumer.** g0-fibresimple's glue piece FS3 is now proved from T6 and `KerUnitOpen`:
`G0FibreSimple.end0Division_of_homFree_kerUnitOpen`. Since `KerUnitOpen` follows from the glue
pair, FS3 also follows from T6 and that pair.

**Verification.** VERIFIED (compiled). `lake env lean scratch/mul-rigidity/MulRigidity.lean`
exits 0 in 12 s with no `sorry`. All nine `#print axioms` lines give
`[propext, Classical.choice, Quot.sound]`. `Rigidity.lean` and `Mul.lean` also compile on their
own, using targeted Mathlib imports. The statements of `RigidityHom` and `MulIsogeny` match the
source exactly (checked with `diff` against `scratch/g0-fibresimple/FibreSimple.lean`). Their
`PkgI3` objects come from `ZInQKernel/HDecomp/Objects.lean`, whose `AbVar`/`Hom`/`End`/
`IsIsogenyMor` text matches the copy in g0-split's `Split.lean` exactly (lines 2516-2612, checked
with `diff`).

## 2. `RigidityHom` (Rigidity.lean)

| theorem | statement | proof |
|---|---|---|
| `rigidity_algClosed` | Take `K` algebraically closed. Let `G` be proper with `G ×_K G` integral, and `Z` separated and locally of finite type, with points `e`, `z`. If `c : G × G → Z` satisfies `c(e, ·) = z` and `c(·, e) = z` (as `T`-points), then `c = z` | Mathlib's proof of Stacks 0BFD (`isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`), with the commutator replaced by `c` and `γ = (fst, c)` landing in `G ⊗ Z`. Ingredients: Zariski's main theorem (`exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage`), Jacobson spaces, and `ext_of_apply_eq` |
| `isMonHom_of_algClosed` | Over `K̄`: for group objects `G`, `B` with `G` proper and `G × G` integral, and `B` separated and locally of finite type, a morphism `h` with `h(e) = e` is a homomorphism | apply `rigidity_algClosed` to `c = (μ ≫ h) · ((h ⊗ h) ≫ μ)⁻¹` |
| `isMonHom_of_geometricallyIntegral` | the same over any field `K`, with `G` geometrically integral | base change along `Spec K̄ → Spec K`. `Over.pullback` is faithful there and monoidal (`Functor.grpObjObj`, `obj.μ_def`, `μ_natural`), so `μ ≫ h = (h ⊗ h) ≫ μ` can be checked after base change |
| `G0FibreSimple.rigidityHom` | `RigidityHom` | instance of the previous row: `AbVar` gives proper, smooth and geometrically integral |

The proof uses only "proper + geometrically integral" on the source and "separated + locally of
finite type" on the target. Smoothness is not used.

## 3. `MulIsogeny` (Mul.lean)

### Leaves

| name | statement | source | status |
|---|---|---|---|
| `KerUnitOpen` (**the remaining leaf**) | char 0, `n ≠ 0`: `(kerUnit A [n]).left` is an open immersion, where `kerUnit = pullback.lift η (𝟙) : 𝟙 ⟶ pullback [n] η` | consequence of "`A[n]` is étale for `char k ∤ n`" (Mumford §4 Application 2 / §6; Milne Thm 8.2; UNVERIFIED). Its content is `d[n] = n` on the tangent space at `0` | leaf; implied by `MulEtale` in Lean (`kerUnitOpen_of_mulEtale`) |
| `MulEtale` | char 0, `n ≠ 0`: `[n].left` is étale | Mumford §4 Application 2 / §6; Milne Thm 8.2, "étale iff `char k ∤ n`" (UNVERIFIED), restricted to char 0 | alternative leaf, ≥ `KerUnitOpen` |
| `MulUnramified` | char 0, `n ≠ 0`: `[n].left` is formally unramified | consequence of `MulEtale` | intermediate (`mulUnramified_of_kerUnitOpen`, `mulUnramified_of_mulEtale`) |

### Glue (all proved)

| name | statement | proof |
|---|---|---|
| `locallyQuasiFinite_of_formallyUnramified` | formally unramified + locally of finite type ⇒ locally quasi-finite (schemes) | made affine-local (`HasRingHomProperty.iff_appLE`) from Mathlib's `Algebra.QuasiFinite` instance (`EssFiniteType` + `FormallyUnramified`) |
| `isProper_left` | a `K`-morphism of abelian varieties is proper | `IsProper.of_comp` |
| `isIsogenyMor_of_lqf_of_isOpenMap` | a locally quasi-finite open endomorphism is finite and surjective | finite: Mathlib ZMT `IsFinite.of_isProper_of_locallyQuasiFinite` (Stacks 02LS). Surjective: the range is clopen and nonempty, and `A` is irreducible |
| `ne_of_specializes_of_lqf` | under a locally quasi-finite map, a strict specialization `x ⤳ y` has `f x ≠ f y` | fibres are discrete (`isDiscrete_preimage_singleton`) |
| `surjective_of_lqf_self` | a locally quasi-finite closed self-map of an irreducible Noetherian scheme is surjective | if `f ξ ≠ ξ` for the generic point `ξ`, then `ξ ⤳ fξ ⤳ f²ξ ⤳ ⋯` are strict, giving a strictly decreasing chain of closed sets `cl{fᵐξ}`, which Noetherianity forbids. So `ξ ∈ range f`, which is closed |
| `quasiFiniteEndSurjective` | `QuasiFiniteEndSurjective`: a locally quasi-finite endomorphism of an abelian variety is surjective | previous row. `A` is Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`, `QuasiCompact.compactSpace_of_compactSpace`) and irreducible (`GeometricallyIrreducible.irreducibleSpace_of_subsingleton`). **No dimension theory is needed**, although this was first stated as a dimension-theory leaf |
| `diagonal_isPullback` | for any homomorphism `f : A → A`, the diagonal `Δ_f` is the base change of the unit section of `ker f` along `(x, y) ↦ x⁻¹y : A ×_f A → ker f` | universal property in `Over (Spec K)`, using the group structure on morphisms |
| `formallyUnramified_of_kerUnit` | unit section of `ker f` an open immersion ⇒ `f.left` formally unramified | `Over.forget` preserves the pullback (connected limits), open immersions are stable under base change, and `PreservesPullback.iso` identifies `Δ_f` with `pullback.diagonal f.left`; then apply Mathlib's instance (open diagonal ⇒ formally unramified) |
| `isOpenImmersion_of_section` | a section of a formally unramified morphism locally of finite type is an open immersion (Stacks 024T) | Mathlib's `isOpenImmersion_diagonal` and `pullback_lift_diagonal_isPullback` |
| `kerUnitOpen_of_mulEtale` | `MulEtale → KerUnitOpen` | the kernel is a base change of `[n]`, so it is étale, and `kerUnit` is a section of it |
| `mulIsogeny_of_mulEtale`, `mulIsogeny_of_mulUnramified'`, `mulIsogeny_of_kerUnitOpen` | the three reductions | composition |

So the chain is: `KerUnitOpen` ⇒ (diagonal) `MulUnramified` ⇒ (with properness) locally
quasi-finite ⇒ finite (ZMT) and surjective (Noetherian generic-point argument) ⇒ `MulIsogeny`.

### `KerUnitOpen` from two glue statements (proved reduction; glue unproved)

| name | statement (Lean) | why true | status |
|---|---|---|---|
| `origin`, `O0`, `stalkEndo`, `cotangentMap` | the origin `η(pt)`; `𝒪_{A,0}`; `f^♯ = stalkCongr ≫ stalkMap`, a local endomorphism of `𝒪_{A,0}` (`f(0) = 0`, `map_origin`); `Ideal.mapCotangent` of `f^♯` on `m₀/m₀²` | definitions | compiled |
| `CotangentMulN` | `cotangentMap A [n] = n • LinearMap.id`, all `n ∈ ℤ`, any field | modulo `m ⊗ m`, `μ^♯φ ≡ φ ⊗ 1 + 1 ⊗ φ` (unit axioms), so the cotangent map of `f * g` is the sum of those of `f` and `g`; induct on `n`. Mumford §4, "`d(n_X) = n`" (UNVERIFIED locator) | **glue, unproved** |
| `KerUnitOpenOfCotangentSurj` | for `f : A.X ⟶ A.X` with `[IsMonHom f]`: `Surjective (cotangentMap A f) → IsOpenImmersion (kerUnit A f).left` | `𝒪_{ker f,0} = 𝒪_{A,0}/f^♯(m₀)𝒪`, so surjectivity gives `m₀ = f^♯(m₀)𝒪 + m₀²`, hence `m₀ = f^♯(m₀)𝒪` (Nakayama), so `𝒪_{ker f,0} = k`. A rational point of a Noetherian scheme whose local ring is a field is an open point `≅ Spec k` | **glue, unproved** |
| `charZero_residueField` | char 0 ⇒ `CharZero (ResidueField 𝒪_{A,0})` | ring hom `k → Γ(Spec k) → Γ(A) → 𝒪_{A,0} → κ` | **proved** |
| `kerUnitOpen_of_cotangent` | `KerUnitOpenOfCotangentSurj → CotangentMulN → KerUnitOpen` | `n • v = (n : κ) • v` with `(n : κ) ≠ 0` | **proved** |
| `mulIsogeny_of_cotangent` | `KerUnitOpenOfCotangentSurj → CotangentMulN → MulIsogeny` | composition | **proved** |

Sanity check (argument): for `n = 0`, the cotangent map is `0` (`[0]^♯` factors through the
residue map, which kills `m₀`). `KerUnitOpenOfCotangentSurj` then says that `ker [0] = A` has an
open unit section iff `m₀/m₀² = 0` iff `dim A = 0`, which is correct. Neither glue statement is
proved: Mathlib v4.35 has no lemmas on stalks of fibre products (`AlgebraicGeometry/Fiber.lean`
has the fibre but no stalk comparison), and no tangent vectors as `k[ε]`-points. Formalizing those
two pieces of commutative algebra would make `MulIsogeny` a theorem.

### The degree

The degree `n^{2g}` is not needed: `MulIsogeny` drops it, and its only consumer, FS3, uses only
"finite and surjective". Mathlib has no notion of the degree of a finite morphism of schemes, so
the degree is not stated.

## 4. Effect on the decomposition

* `RigidityHom` moves from the textbook leaves to the proved glue (`rigidityHom`). FS2 no longer
  needs a hypothesis.
* `MulIsogeny` can be replaced in either of two ways. One is the glue pair
  `KerUnitOpenOfCotangentSurj` + `CotangentMulN`, which leaves no literature leaf. The other is
  the leaf `KerUnitOpen` (or `MulEtale`, which implies it). That leaf sits at a single point, the
  origin of `A[n]`, and Lean shows that the published étaleness statement implies it.
* Integration: `fibreSimple_of_leaves (t) (hMul) (hRig) (p)` can be called with
  `hRig := rigidityHom` and `hMul := mulIsogeny_of_kerUnitOpen h`. My file uses
  `ZInQKernel.HDecomp.Objects`'s `PkgI3`, whose text matches the `PkgI3` copy inside
  `FibreSimple.lean`. When the two are merged into one file, the declarations above go in after
  `FibreSimple.lean`'s `RigidityHom`/`MulIsogeny`; only the names they refer to are needed.
* With `import Mathlib`, the identifier `γ` clashes with a Mathlib notation. `Rigidity.lean`
  therefore uses `gm` (Mathlib's source uses `γ` under targeted imports).
