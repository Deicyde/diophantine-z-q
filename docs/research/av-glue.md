# av-glue: the two glue Props under `SimpleImageIsogeny` (ImageFactorization, SimpleSurjIsogeny)

Task av-glue, 2026-11-14. Branch `wip/av-glue` (from `origin/wip/w54` d5d43efc). Targets (av-b1,
`ZInQKernel/Contrib/AVB1/Poincare.lean`): `ZInQ.Contrib.AVB1.ImageFactorization` and
`ZInQ.Contrib.AVB1.SimpleSurjIsogeny`. Together they give `SimpleImageIsogeny`, one of the two GLUE
fields of the canonical H assembly (leaf-fold5).

## 1. Main result

Both glue Props are **reduced to three published theorems about group schemes over a field, plus
two leaves the canonical assembly already has. All the glue is proved in Lean**: no sorry, axioms
`[propext, Classical.choice, Quot.sound]`, VERIFIED by compilation. Each statement is copied
verbatim and checked `Iff.rfl` against the kernel's.

| target | proved from | Lean |
|---|---|---|
| `ImageFactorization` | **`CartierSmooth`** alone | `AVGlue.imageFactorization_of_cartier` |
| `SimpleSurjIsogeny` | `CartierSmooth`, `GeomConnOfRationalPoint`, `GroupSchemeEquidim`, `PoincareComplement` (existing field), `WeilPairing.IsogenyQuasiInverse` (existing field `isogenyQuasiInverse`, H-54) | `AVGlue.simpleSurjIsogeny_of_published'` |
| `SimpleImageIsogeny` (the assembly's GLUE field) | the same five | `AVGlue.simpleImageIsogeny_of_published'` |
| T8 `PkgI3.PoincareReducibility` | the same five | `AVGlue.poincareReducibility_of_published'` |

The three new LEAF Props are published theorems about group schemes over a field. Each is stated
over Mathlib's own definitions (`GrpObj` in `Over (Spec k)`, `Smooth`, `GeometricallyConnected`,
`irreducibleComponents`, `topologicalKrullDim`). None is stronger than the published statement (§5):

- **`CartierSmooth`** (Cartier's theorem): a group scheme locally of finite type over a field of
  characteristic `0` is smooth.
- **`GeomConnOfRationalPoint`** (Stacks Tag 04KV): a connected scheme of finite type over `k` with
  a `k`-rational point is geometrically connected.
- **`GroupSchemeEquidim`** (Stacks, group schemes over a field; SGA 3 VI_A): every irreducible
  component of a group scheme of finite type over a field has the dimension of the group.

Answer to the task's question: **`EndDivision` does suffice for `SimpleSurjIsogeny`** once a
positive-dimensional abelian subvariety inside the kernel is available. Write `j : C → A` for its
inclusion and `φ = (j, g) : C × Z → A` for the isogeny that Poincaré's complement gives. A
quasi-inverse `ψ` of `φ` then gives the nonzero endomorphism `e = j ∘ pr₁ ∘ ψ`. `EndDivision` makes
`e` surjective, so `j` is surjective, hence an isomorphism (`A` is reduced), so `h = 0`. And `e = 0`
is impossible: then `j ∘ [n] = 0`, and `[n]` is finite, which makes `C` discrete. The kernel, its identity
component and the dimension facts are built here (`Kernel.lean`). A grep of `Objects.lean`,
`Contrib/AVB1`, `Contrib/AVB2`, `Contrib/NeronC` and `Contrib/CurvesG` found no kernel or
identity-component construction (VERIFIED by grep). From the kernel, only g9-abvarbc's
`mulIsogeny` is used.

**For the canonical assembly (leaf-fold5):** the GLUE field `simpleImageIsogeny` can be replaced by
the three LEAF fields `CartierSmooth`, `GeomConnOfRationalPoint` and `GroupSchemeEquidim`.
`PoincareComplement` and `isogenyQuasiInverse` are already fields. Some kernel theorems are used as
proved inputs: the vendored Tau Ceti theorem `Smooth.geometricallyIntegral`, the proved
`ZInQ.Contrib.AbVarBC.mulIsogeny` (g9-abvarbc: `[n]` is finite in characteristic 0) and
`ZInQ.Contrib.AVB1.simpleImageIsogeny_of_pieces`. No statement is changed. None of the targets is
false, vacuous or inert (§6).

### 1.1 The reduction chain (all arrows proved in Lean)

```
CartierSmooth ───────────────────────────────────────────────▶ ImageFactorization
CartierSmooth + GeomConnOfRationalPoint + GroupSchemeEquidim ─▶ KernelIdentityComponent   (Kernel.lean)
KernelIdentityComponent ───────────(shear isomorphism)───────▶ KernelAbSubvariety        (Kernel.lean)
PoincareComplement + WeilPairing.IsogenyQuasiInverse + KernelAbSubvariety ─▶ SimpleSurjIsogeny  (SurjIsog.lean)
   (alternative: scheme-level IsogenyQuasiInverse instead of the K̄-point one)
ImageFactorization + SimpleSurjIsogeny ─(av-b1)─▶ SimpleImageIsogeny ─(+ PoincareComplement, av-b1)─▶ T8
```

### 1.2 Declarations (namespace `AVGlue`, `scratch/av-glue/`)

```lean
-- ImageFact.lean
theorem imageFactorization_iff : ImageFactorization ↔ ZInQ.Contrib.AVB1.ImageFactorization
theorem imageFactorization_of_cartier (hC : CartierSmooth) : ImageFactorization
-- SurjIsog.lean
theorem simpleSurjIsogeny_iff : SimpleSurjIsogeny ↔ ZInQ.Contrib.AVB1.SimpleSurjIsogeny
theorem simpleSurjIsogeny_of_leaves (hP : ZInQ.Contrib.AVB1.PoincareComplement)
    (hQ : IsogenyQuasiInverse) (hK : KernelAbSubvariety) : SimpleSurjIsogeny
theorem simpleSurjIsogeny_of_leaves' (hP : ZInQ.Contrib.AVB1.PoincareComplement)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hK : KernelAbSubvariety) : SimpleSurjIsogeny
theorem hom_ext_of_points {A B : PkgI3.AbVar K} (u v : A.X ⟶ B.X)
    (H : ∀ z : A.Pt (AlgebraicClosure K), z ≫ u = z ≫ v) : u = v
-- Kernel.lean
theorem lqf_of_ker (h : A.X ⟶ B.X) [IsMonHom h] [IsProper h.left]
    (hK : LocallyQuasiFinite (kerOver h).hom) : LocallyQuasiFinite h.left
theorem kernelAbSubvariety_of_identityComponent (hK1 : KernelIdentityComponent) :
    KernelAbSubvariety
theorem kernelIdentityComponent_of_leaves (hC : CartierSmooth') (hG : GeomConnOfRationalPoint)
    (hE : GroupSchemeEquidim) : KernelIdentityComponent
-- Combined.lean (generated by `python3 scratch/av-glue/mk_combined.py`; all of the above)
theorem simpleImageIsogeny_iff : SimpleImageIsogeny ↔ ZInQ.Contrib.AVB1.SimpleImageIsogeny
theorem cartierSmooth_iff : CartierSmooth ↔ CartierSmooth'
theorem simpleImageIsogeny_of_published' (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : WeilPairing.IsogenyQuasiInverse)
    (hG : GeomConnOfRationalPoint) (hE : GroupSchemeEquidim) : SimpleImageIsogeny
theorem simpleSurjIsogeny_of_published'   -- same hypotheses : SimpleSurjIsogeny
theorem poincareReducibility_of_published' -- same hypotheses : PkgI3.PoincareReducibility
theorem simpleImageIsogeny_of_published   -- scheme-level IsogenyQuasiInverse variant
theorem simpleImageIsogeny_of_leaves (hC) (hP) (hQ : IsogenyQuasiInverse) (hK : KernelAbSubvariety)
```

General-purpose glue lemmas, all proved from Mathlib alone:

- Scheme-theoretic images. `ker_toImage`: `f.toImage.ker = ⊥` for quasi-compact `f`.
  `surjective_toImage`: `X → f(X)` is surjective for proper `f`. `ker_le_of_dominant`: if `d` is
  scheme-theoretically dominant and `d ≫ g` factors through a closed immersion `i`, then
  `ker i ≤ ker g`.
- `grpObjOfMono`, `isMonHom_grpObjOfMono`, `isMonHom_of_comp_mono`: a subobject of a group object
  (in any cartesian monoidal category) that is closed under unit, multiplication and inverse is a
  group object.
- `isPullback_whiskerRight/Left`, `dominant_whiskerRight/Left`: in `Over S`, whiskering is a base
  change.
- `isOpen_connectedComponent_of_noetherian`: in a noetherian space, connected components are open.
- `kerOver`, `kerι`, `kerLift`, `kerGrp`: the kernel `A ×_B Spec k` of a homomorphism, as a group
  scheme. `shearIso : (A ×_k ker h) ≅ A ×_B A` over `A`. `lqf_of_ker`: if the kernel is
  quasi-finite, so is `h`.
- `hom_ext_of_points`: two morphisms of abelian varieties that agree on `A(K̄)` are equal.
- `prodAbVar` (g0-product's product, as a `PkgI3.AbVar`), `dim_le_zero_of_comp_one`,
  `hom_eq_one_of_surjective`, `isProper_hom`, `natCast_hom`, `comp_eq_pow_of_isQuasiInverse`.

## 2. `ImageFactorization` from Cartier's theorem (`ImageFact.lean`)

Given `f : A → J`, let `F = f.left`. Take `B = F.image`, Mathlib's scheme-theoretic image
(`Scheme.Hom.image`, the closed subscheme cut out by `ker F`), as a `k`-scheme. Take `i = F.imageι`,
a closed immersion, and `h = F.toImage`.

1. `ker F.toImage = ⊥` (`ker_toImage`: on the affine cover `ι⁻¹U`, by `Hom.ker_apply` and
   `toImage_app_injective`), so `h` is scheme-theoretically dominant.
2. `A ×_k A → B ×_k B` equals `(h ▷ A) ≫ (B ◁ h)`. Each factor is a base change of `h` along a
   flat map (everything over a field is flat). So the map is scheme-theoretically dominant, by
   Mathlib's `IsSchemeTheoreticallyDominant.of_isPullback` (scheme-theoretic images commute with
   flat base change).
3. Group law. `μ_J ∘ (i × i)`, composed with the dominant map `A × A → B × B`, equals `f ∘ μ_A`,
   which factors through `i`. So `ker i ≤ ker(μ_J ∘ (i × i))`, and `IsClosedImmersion.lift` gives
   `μ_B`. The unit is `η_A ≫ h`; the inverse is obtained the same way. `grpObjOfMono` makes `B` a
   group object with `i` and `h` homomorphisms.
4. `B → Spec k` is proper (a closed immersion into the proper `J`) and so locally of finite type.
   It is smooth by **Cartier**.
5. `B` is geometrically connected: for every field `K/k`, `A_K → B_K` is a base change of the
   surjective `h`. Smooth and geometrically connected implies geometrically integral (vendored Tau
   Ceti). So `B` is a `PkgI3.AbVar`.
6. `h` is surjective: it is proper and dominant.

## 3. `SimpleSurjIsogeny` (`SurjIsog.lean`)

`simpleSurjIsogeny_of_leaves'`. The map `h` is proper, so by Mathlib's Zariski main theorem
(`IsFinite.of_isProper_of_locallyQuasiFinite`) it suffices to show that `h` is locally
quasi-finite. Otherwise:

1. `KernelAbSubvariety` gives `j : C ↪ A` with `dim C > 0` and `h ∘ j = 0`.
2. `PoincareComplement` gives `Z` and `g` with `φ = (j, g) : C × Z → A` an isogeny.
3. The quasi-inverse leaf gives `ψ` and `n ≥ 1` with `ψφ = [n]` on `(C × Z)(K̄)`.
   `hom_ext_of_points` makes this an identity of morphisms.
4. Put `e = j ∘ pr₁ ∘ ψ ∈ End A`.
   - If `e = 0`, then `j ∘ [n]_C = [n]_A ∘ j = 0`. `[n]_A` is finite (proved `mulIsogeny`), so
     `j(C)` lies in a finite, discrete fibre and `dim C ≤ 0`, a contradiction.
   - If `e ≠ 0`, `EndDivision` makes `e` surjective, so the closed immersion `j` is surjective onto
     the reduced `A`. Hence `j` is an isomorphism and `h = 0`, a contradiction.

The variant `simpleSurjIsogeny_of_leaves` instead takes the scheme-level quasi-inverse (the text of
`HSyn.G0RevIsog.IsogenyQuasiInverse`). That form gives `[n]_A = φψ` finite directly.

## 4. The kernel (`Kernel.lean`)

- **Shear.** Let `ker h = A ×_B Spec k` (`kerOver`). The map `(a, x) ↦ (a, a + x)` is an
  isomorphism `A ×_k ker h ≅ A ×_B A` over the first projection (`shearIso`, built in `Over`
  with the group law of `A`). If `ker h → Spec k` is locally quasi-finite, so is
  `A ×_B A → A`. Every fibre of `h` is the image of a fibre of that map
  (`Scheme.Pullback.exists_preimage_pullback`), so `h` is locally quasi-finite (`lqf_of_ker`).
  This gives `KernelAbSubvariety ⇐ KernelIdentityComponent`.
- **Identity component.**
  - `ker h` is a group scheme (`kerGrp`, via `grpObjOfMono`), a closed subscheme of `A` (the unit
    section of the separated `B` is a closed immersion), proper and noetherian. It is smooth by
    Cartier.
  - The connected component `U0` of the unit is open (`isOpen_connectedComponent_of_noetherian`)
    and closed.
  - `(ker h)⁰ := U0` is a group: products and inverses land in `U0` because they are images of
    connected spaces containing `e`. `(ker h)⁰ ×_k (ker h)⁰` is connected by
    `GeomConnOfRationalPoint` and Mathlib.
  - `(ker h)⁰` is proper, smooth (open in `ker h`), geometrically connected (04KV) and
    geometrically integral (Tau Ceti), so it is an abelian variety. Its inclusion into `A` is a
    closed immersion killed by `h`.
  - Dimension: if `ker h` is not locally quasi-finite, then `dim ker h > 0` (Mathlib
    `IsLocallyArtinian.of_topologicalKrullDim_le_zero`). The irreducible component through `e`
    lies in `U0` and has dimension `dim ker h` by `GroupSchemeEquidim`.

## 5. Leaf statements and sources

```lean
def CartierSmooth : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    LocallyOfFiniteType G.hom → Smooth G.hom
def GeomConnOfRationalPoint : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (s : Spec (CommRingCat.of k) ⟶ X), s ≫ f = 𝟙 _ → LocallyOfFiniteType f → QuasiCompact f →
    ConnectedSpace X → GeometricallyConnected f
def GroupSchemeEquidim : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    LocallyOfFiniteType G.hom → QuasiCompact G.hom →
    ∀ Z ∈ irreducibleComponents G.left, topologicalKrullDim Z = topologicalKrullDim G.left
```

- `CartierSmooth`: P. Cartier, *Groupes algébriques et groupes formels* (Colloque Bruxelles 1962);
  F. Oort, Invent. Math. 2 (1966) 79–80; Mumford, *Abelian varieties* §11 Thm 1; Milne,
  *Algebraic Groups* (2017) Thm 3.23; Stacks Tag 047N. This is the published statement. A `GrpObj`
  in `Over (Spec k)`, with Mathlib's cartesian monoidal structure (fibre products over `k`), is a
  group scheme over `k`.
- `GeomConnOfRationalPoint`: Stacks, Varieties, Lemma 33.7.14 (Tag 04KV). Stacks states it for any
  scheme over `k` with a point `x` such that `k` is algebraically closed in `κ(x)`. The Prop adds
  "of finite type" and asks for a rational point, so it is a consequence, never stronger.
- `GroupSchemeEquidim`: Stacks, Groupoid schemes, section "Properties of group schemes over a
  field" ("`G` is equidimensional and `dim G = dim_g G`"); SGA 3, Exp. VI_A, 2.4. The Prop is
  restricted to finite type, so never stronger. Dimensions are Krull dimensions of the underlying
  spaces, each component with its subspace topology.
- `PoincareComplement` (av-b1, unchanged) and `WeilPairing.IsogenyQuasiInverse` (weil-pairing,
  verbatim text: `scratch/av-b2/olean/TailB.lean` l. 5484, 5570, 5771, 5864) are existing fields.
- Intermediate Props, now proved from the leaves above: `KernelAbSubvariety` (if `h` is not
  locally quasi-finite, there is a positive-dimensional abelian subvariety killed by `h`) and
  `KernelIdentityComponent` (the same, with the hypothesis on `ker h`). The scheme-level
  `IsogenyQuasiInverse` (text of `HSyn.G0RevIsog.IsogenyQuasiInverse`) is an alternative input.

All locators are UNVERIFIED (from memory; no network). The statements themselves are STANDARD.

## 6. Statement audit (no change proposed)

- `ImageFactorization`: true as stated (§2 proves it from Cartier). For `f = 𝟙` it holds with
  `B = A`.
- `SimpleSurjIsogeny`: true as stated. The hypothesis `Surjective h.hom.left` is not used: any
  nonzero homomorphism out of `A` with `EndDivision A` is finite. This is harmless.
- `SimpleImageIsogeny`: true; it is the two Props together (av-b1).
- The Props are not vacuous, but no nonzero abelian variety can be built in Mathlib 4.35
  (`PkgI3.AbVar.zero`'s docstring). As for every abelian-variety field of the assembly, the
  content is in the instantiation.

## 7. Checks

- `lake build ZInQKernel.Contrib.AVB1.Poincare` and `lake build ZInQKernel.Contrib.AbVarBC.Main`
  (oleans used by the scratch files; the Tau Ceti module was already built).
- `lake env lean` on each of `scratch/av-glue/ImageFact.lean`, `SurjIsog.lean`, `Kernel.lean` and
  `Combined.lean`: exit 0, no sorry. `#print axioms` of every theorem in §1.2 gives
  `[propext, Classical.choice, Quot.sound]` (VERIFIED). Each file takes about 10–40 s.
- `Combined.lean` is generated: `python3 scratch/av-glue/mk_combined.py` concatenates the three
  files and drops the duplicated blocks marked `-- BEGIN DUP` / `-- END DUP`.
- Results log: `scratch/av-glue/log.md`.
