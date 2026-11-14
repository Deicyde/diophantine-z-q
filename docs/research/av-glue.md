# av-glue: the two glue Props under `SimpleImageIsogeny` (ImageFactorization, SimpleSurjIsogeny)

Task av-glue, 2026-11-14. Branch `wip/av-glue` (from `origin/wip/w54` d5d43efc). Targets (av-b1,
`ZInQKernel/Contrib/AVB1/Poincare.lean`): `ZInQ.Contrib.AVB1.ImageFactorization` and
`ZInQ.Contrib.AVB1.SimpleSurjIsogeny`, which give `SimpleImageIsogeny`, one of the two GLUE fields of
the canonical H assembly (leaf-fold5).

## 1. Main result

Both glue Props are **reduced to published theorems, with all glue proved in Lean** (no sorry,
axioms `[propext, Classical.choice, Quot.sound]`, VERIFIED by compilation; statements copied
verbatim and checked `Iff.rfl` against the kernel's):

- **`ImageFactorization` ⇐ `CartierSmooth`** (one LEAF: Cartier's theorem, a group scheme locally
  of finite type over a field of characteristic `0` is smooth). Everything else is proved from
  Mathlib (scheme-theoretic image, scheme-theoretically dominant maps and their flat base change,
  Zariski-local lifting through closed immersions) and the vendored Tau Ceti theorem
  "smooth + geometrically connected ⇒ geometrically integral" (already in `ZInQKernel/Contrib/TauCeti`).
- **`SimpleSurjIsogeny` ⇐ `PoincareComplement` ∧ `IsogenyQuasiInverse` ∧ `KernelAbSubvariety`**.
  `PoincareComplement` is av-b1's LEAF (already a field of the canonical assembly);
  `IsogenyQuasiInverse` is the existing scheme-level LEAF text of `HSyn.G0RevIsog.IsogenyQuasiInverse`
  (g0-revisog); `KernelAbSubvariety` is new: if `h : A → B` is not locally quasi-finite, then
  `(ker h)⁰_red` is a positive-dimensional abelian subvariety killed by `h` (LEAF, a consequence of
  Milne 1986 §8 / Mumford §§4, 8, 11; §3).
  This answers the task's question: **`EndDivision` does suffice** once a positive-dimensional
  abelian subvariety in the kernel is available — Poincaré's complement plus a quasi-inverse give a
  nonzero endomorphism `e = j ∘ pr₁ ∘ ψ`; `EndDivision` makes `e` surjective, so the closed immersion
  `j` is surjective, hence an isomorphism (`A` is reduced), so `h = 0`; and `e = 0` is impossible
  because then `j ∘ [n] = 0` with `[n] = φ ∘ ψ` finite, which makes `C` discrete, contradicting
  `dim C > 0`. Finiteness of `h` then comes from Mathlib's Zariski main theorem
  (`IsFinite.of_isProper_of_locallyQuasiFinite`).
- Hence **`SimpleImageIsogeny` ⇐ `CartierSmooth` ∧ `PoincareComplement` ∧ `IsogenyQuasiInverse` ∧
  `KernelAbSubvariety`**, and **T8 (`PkgI3.PoincareReducibility`) ⇐ the same four**
  (`scratch/av-glue/Combined.lean`).

For the canonical assembly (leaf-fold5): the GLUE field `simpleImageIsogeny` can be replaced by the
three new LEAF Props `CartierSmooth`, `IsogenyQuasiInverse`, `KernelAbSubvariety` (the fourth input,
`PoincareComplement`, is already a field). No statement is changed; none of the targets is false,
vacuous or inert (§4).

### 1.1 Declarations proved (namespace `AVGlue`)

```lean
-- scratch/av-glue/ImageFact.lean
theorem AVGlue.imageFactorization_iff : ImageFactorization ↔ ZInQ.Contrib.AVB1.ImageFactorization
theorem AVGlue.imageFactorization_of_cartier (hC : CartierSmooth) : ImageFactorization
-- scratch/av-glue/SurjIsog.lean
theorem AVGlue.simpleSurjIsogeny_iff : SimpleSurjIsogeny ↔ ZInQ.Contrib.AVB1.SimpleSurjIsogeny
theorem AVGlue.simpleSurjIsogeny_of_leaves (hP : ZInQ.Contrib.AVB1.PoincareComplement)
    (hQ : IsogenyQuasiInverse) (hK : KernelAbSubvariety) : SimpleSurjIsogeny
-- scratch/av-glue/Combined.lean (generated: python3 scratch/av-glue/mk_combined.py)
theorem AVGlue.simpleImageIsogeny_iff : SimpleImageIsogeny ↔ ZInQ.Contrib.AVB1.SimpleImageIsogeny
theorem AVGlue.simpleImageIsogeny_of_leaves (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : IsogenyQuasiInverse)
    (hK : KernelAbSubvariety) : SimpleImageIsogeny
theorem AVGlue.poincareReducibility_of_leaves (hC : CartierSmooth)
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : IsogenyQuasiInverse)
    (hK : KernelAbSubvariety) : PkgI3.PoincareReducibility
```

Glue lemmas of general use (all proved, Mathlib only):

- `AVGlue.ker_toImage : f.toImage.ker = ⊥` for quasi-compact `f` (so `X → f(X)` is
  scheme-theoretically dominant); `AVGlue.surjective_toImage` for proper `f`;
  `AVGlue.ker_le_of_dominant` (if `d` is scheme-theoretically dominant and `d ≫ g` factors through
  a closed immersion `i`, then `ker i ≤ ker g`, so `g` lifts through `i`).
- `AVGlue.grpObjOfMono`, `AVGlue.isMonHom_grpObjOfMono`: a subobject `i : Y ↪ G` of a group
  object in a cartesian monoidal category, closed under multiplication, unit and inverse, is a
  group object with `i` a homomorphism; `AVGlue.isMonHom_of_comp_mono`.
- `AVGlue.isPullback_whiskerRight`, `isPullback_whiskerLeft`, `dominant_whiskerRight`,
  `dominant_whiskerLeft`: in `Over S` (schemes), `g ▷ R` and `R ◁ g` are base changes of `g`, so
  scheme-theoretic dominance passes to them when `R → S` is flat.
- `AVGlue.prodAbVar` (g0-product's product, as a `PkgI3.AbVar`), `AVGlue.dim_le_zero_of_comp_one`,
  `AVGlue.hom_eq_one_of_surjective`, `AVGlue.isProper_hom`.

## 2. `ImageFactorization` from Cartier's theorem

Given `f : A → J`, let `F = f.left`. The abelian variety `B` is Mathlib's scheme-theoretic image
`F.image` (`Scheme.Hom.image`, the closed subscheme cut out by `ker F`) as a `k`-scheme, with
`i = F.imageι` (a closed immersion) and `h = F.toImage`.

1. `ker F.toImage = ⊥` (`ker_toImage`: on the affine cover `ι⁻¹U`, `Hom.ker_apply` and
   `toImage_app_injective`), so `F.toImage` is scheme-theoretically dominant.
2. `A ×_k A → B ×_k B` is scheme-theoretically dominant: it is `(h ▷ A) ≫ (B ◁ h)`, each a base
   change of `h` along a flat map (everything over a field is flat), and Mathlib's
   `IsSchemeTheoreticallyDominant.of_isPullback` (Stacks: scheme-theoretic images commute with flat
   base change). The same for `h` itself.
3. Group law: `μ_J ∘ (i × i)` composed with the dominant `A × A → B × B` equals `f ∘ μ_A`, which
   factors through `i`; so `ker i ≤ ker(μ_J ∘ (i × i))` (`ker_le_of_dominant`) and
   `IsClosedImmersion.lift` gives `μ_B`. Unit `η_A ≫ h`; inverse likewise. `grpObjOfMono` makes
   `B` a group object with `i`, then `h`, homomorphisms.
4. `B → Spec k` is proper (closed immersion into proper `J`), locally of finite type, hence smooth
   by **Cartier** (the only leaf).
5. `B` is geometrically connected: for any field `K/k`, `A_K → B_K` is a base change of the
   surjective `h`, so `B_K` is the image of the connected `A_K` (`geometricallyConnected_img`).
   Smooth + geometrically connected ⇒ geometrically integral (vendored Tau Ceti
   `Smooth.geometricallyIntegral`). So `B` is a `PkgI3.AbVar`.
6. `h` is surjective: it is proper (`h ≫ i = F` proper, `i` separated) and dominant
   (`surjective_toImage`).

Leaf statement:

```lean
def CartierSmooth : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    LocallyOfFiniteType G.hom → Smooth G.hom
```

LEAF, the published statement (no hypothesis dropped): P. Cartier, *Groupes algébriques et groupes
formels* (Colloque Bruxelles 1962); F. Oort, *Algebraic group schemes in characteristic zero are
reduced*, Invent. Math. 2 (1966); Mumford, *Abelian varieties*, §11, Thm 1; Milne, *Algebraic
Groups* (2017), Thm 3.23; Stacks Project, Groupoids, "Cartier's theorem" (Tag 047N). All locators
UNVERIFIED (no network). A `GrpObj` in `Over (Spec k)` with Mathlib's cartesian monoidal
structure (fibre products over `k`) is exactly a group scheme over `k`: a genuine definition.

## 3. `SimpleSurjIsogeny` from three leaves

```lean
def IsIsogeny {K : Type} [Field K] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) : Prop :=
  IsMonHom φ ∧ IsFinite φ.left ∧ Surjective φ.left
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X),
    IsIsogeny φ →
    ∃ (ψ : B.X ⟶ A.X) (n : ℕ), 0 < n ∧ IsIsogeny ψ ∧
      φ ≫ ψ = (𝟙 A.X) ^ n ∧ ψ ≫ φ = (𝟙 B.X) ^ n
def KernelAbSubvariety : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : PkgI3.AbVar k)
    (h : PkgI3.AbVar.Hom A B), ¬ LocallyQuasiFinite h.hom.left →
    ∃ (C : PkgI3.AbVar k) (j : PkgI3.AbVar.Hom C A),
      IsClosedImmersion j.hom.left ∧ 0 < C.dim ∧ j.hom ≫ h.hom = 1
```

- `IsogenyQuasiInverse` (LEAF): the text of `HSyn.G0RevIsog.IsogenyQuasiInverse`
  (`scratch/av-b2/olean/TailA.lean` l. 1660) with its `ZInQ.DefFaltings.AbVar` (a structure with
  the same five fields in that assembly; in the kernel `ZInQ.DefFaltings` opens `PkgI3 (AbVar)`)
  written `PkgI3.AbVar`, and `IsIsogeny` the text of `ZInQ.DefFaltings.IsIsogeny`
  (`ZInQKernel/HDecomp/Faltings/Leaves.lean`). Mumford §7 Rem. after Thm 4 / §8; Milne 1986 §8,
  notes (2008) I Prop. 7.1 (UNVERIFIED). Note: `WeilPairing.IsogenyQuasiInverse` (weil-pairing) is
  the weaker form on `K̄`-points and does not suffice here (the proof composes scheme maps).
- `KernelAbSubvariety` (LEAF, consequence of published statements): take `C = (ker h)⁰_red`. Inputs
  (UNVERIFIED locators): the reduced identity component of a closed subgroup scheme of an abelian
  variety is an abelian subvariety (Milne 1986 §8; Mumford §8; reduced ⇒ smooth by Cartier, char 0);
  `h` is quasi-finite iff `ker h` is finite (fibres over `k̄`-points are translates of `ker h`).
  Never stronger: `C` is existential, and `0 < dim C` is the published positivity of
  `dim ker h` when `h` is not quasi-finite.
- `PoincareComplement` (LEAF, av-b1, unchanged).

Proof (`simpleSurjIsogeny_of_leaves`): `h` is proper; by the Zariski main theorem in Mathlib it
suffices that `h` is locally quasi-finite. Otherwise `KernelAbSubvariety` gives `j : C ↪ A`,
`dim C > 0`, `h ∘ j = 0`; Poincaré gives `Z`, `g` with `φ = (j, g) : C × Z → A` an isogeny
(`C × Z` is `prodAbVar`); the quasi-inverse gives `ψ`, `n` with `φψ = [n]_A`, `ψφ = [n]_{C×Z}`.
Put `e = j ∘ pr₁ ∘ ψ ∈ End A`. If `e = 0`: `0 = e ∘ φ = j ∘ pr₁ ∘ [n]`, restricted to `C × 0`
gives `j ∘ [n]_C = [n]_A ∘ j = 0`; `[n]_A = φ ∘ ψ` is finite, so `j(C)` lies in a finite discrete
fibre, `C` is discrete, `dim C ≤ 0` (`dim_le_zero_of_comp_one`). If `e ≠ 0`: `EndDivision A` makes
`e` surjective, so `j` is surjective, a surjective closed immersion onto the reduced `A`, an
isomorphism (`isIso_of_isClosedImmersion_of_surjective`), and `h = 0` (`hom_eq_one_of_surjective`).

## 4. Statement audit (no change proposed)

- `ImageFactorization`: true as stated (§2 proves it from Cartier). Not vacuous: for `A = J`,
  `f = 𝟙` it holds with `B = A`; it is used at E1 through `SimpleImageIsogeny`.
- `SimpleSurjIsogeny`: true as stated (§3). Its hypothesis `Surjective h.hom.left` is not used by
  the proof (any nonzero homomorphism out of `A` with `EndDivision A` is finite); harmless.
- `KernelAbSubvariety` is true: `(ker h)⁰_red` works. The hypothesis `¬ LocallyQuasiFinite` is the
  Mathlib form of "`h` not quasi-finite".
- `CartierSmooth` is the published theorem, over Mathlib's genuine definitions.

## 5. Checks

- `lake build ZInQKernel.Contrib.AVB1.Poincare` (needed for the `Iff.rfl` checks and the leaf
  `PoincareComplement`; the TauCeti module was already built).
- `lake env lean scratch/av-glue/SurjIsog.lean`, `scratch/av-glue/ImageFact.lean`,
  `scratch/av-glue/Combined.lean`: exit 0, no sorry; `#print axioms` of
  `imageFactorization_of_cartier`, `simpleSurjIsogeny_of_leaves`, `simpleImageIsogeny_of_leaves`,
  `poincareReducibility_of_leaves`: `[propext, Classical.choice, Quot.sound]` (VERIFIED).
- Results log: `scratch/av-glue/log.md`.
