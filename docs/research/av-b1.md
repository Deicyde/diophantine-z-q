# av-b1: leaf-fold3's group B fields t6, t7, t8 (textbook abelian varieties)

Task av-b1, 2026-11-13. Branch `wip/av-b1` (from fork main 8ec80711, plus `origin/wip/leaf-fold3`
f7951690). Fields (leaf-fold3 §2.2, `HDec.HSyn.OpenTextbookLeaves3`):
`t6 : PkgI3.HomFreeFinite` (T6), `t7 : PkgI3.CharPolyIndepOfEll` (T7),
`t8 : PkgI3.PoincareReducibility` (T8).

## 1. Main result

All three fields are **reduced** to strictly smaller named Props, with all the glue proved (no
sorry, axioms `[propext, Classical.choice, Quot.sound]`, VERIFIED by compilation):

- **T6** ⇐ `HomFreeFiniteAlgClosed`: the same statement over algebraically closed fields only,
  which is Mumford, *Abelian varieties* §19 Thm 3 in Mumford's own setting (the book assumes `k`
  algebraically closed throughout).
- **T7** ⇐ `CharPolyIndepOfEllAlgClosed`: the same statement over algebraically closed fields
  only, a consequence of Mumford §19 Thm 4 (it drops `deg P = 2g` and `P(n) = deg(n − φ)`).
- **T8** ⇐ `PoincareComplement` ∧ `ImageFactorization` ∧ `SimpleSurjIsogeny`. The first is
  Poincaré's theorem in its published complement form (Milne 1986 Prop. 12.1; Mumford §19 Thm 1),
  weakened. The other two are textbook facts on images and kernels of homomorphisms (GLUE-level
  composites, §3.3).

The fields are not proved outright: each reduced Prop is still a theorem of the textbook theory
of abelian varieties, and Mathlib 4.35 cannot even build a nonzero abelian variety (see
`PkgI3.AbVar.zero`'s docstring).

### 1.1 Declarations proved

Kernel files (new, `ZInQKernel/Contrib/AVB1/`, over the kernel's `_root_.PkgI3` object layer
`ZInQKernel/HDecomp/Objects.lean`). Each builds with `lake build ZInQKernel.Contrib.AVB1.<File>`.

```lean
-- AlgClosed.lean
theorem ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed
    (h : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : PkgI3.HomFreeFinite
theorem ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed
    (h : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed) : PkgI3.CharPolyIndepOfEll
-- Poincare.lean
theorem ZInQ.Contrib.AVB1.poincareReducibility_of_pieces
    (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hI : ZInQ.Contrib.AVB1.ImageFactorization)
    (hS : ZInQ.Contrib.AVB1.SimpleSurjIsogeny) : PkgI3.PoincareReducibility
-- BaseChange.lean (glue, Mathlib-level)
noncomputable def ZInQ.Contrib.AVB1.bcHom (L) (A B : PkgI3.AbVar K) :
    A.Hom B →+ (A.baseChange L).Hom (B.baseChange L)
theorem ZInQ.Contrib.AVB1.bcHom_injective (A B : PkgI3.AbVar K) :
    Function.Injective (bcHom L A B)
theorem ZInQ.Contrib.AVB1.tateBC_homT (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (ℓ : ℕ) [Fact ℓ.Prime] (f : A.Hom B) (x : A.T ℓ) :
    tateBC B κ ℓ (PkgI3.AbVar.homT f x) = PkgI3.AbVar.homT (bcHom L A B f) (tateBC A κ ℓ x)
theorem ZInQ.Contrib.AVB1.tateBC_bijective_closure (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Bijective (tateBC A (κbar K) ℓ)
```

`#print axioms` (scratch/av-b1/Axioms1.lean, `lake env lean`, VERIFIED):

```
'ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AVB1.bcHom_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AVB1.tateBC_bijective_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AVB1.poincareReducibility_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Single-file check over leaf-fold3's objects (scratch/av-b1/mk_check.py builds
`scratch/av-b1/AVB1Check.lean` = `scratch/leaf-fold3/Leaves3.lean` + the three AVB1 files with
`_root_.PkgI3 → _root_.HDec.PkgI3` + `scratch/av-b1/check_tail.lean`). It proves leaf-fold3's
fields themselves (the constants `HDec.PkgI3.*` that `HDec.HSyn.OpenTextbookLeaves3` uses):

```lean
theorem HDec.AVB1Check.t6_of_algClosed (h : HomFreeFiniteAlgClosed) : PkgI3.HomFreeFinite
theorem HDec.AVB1Check.t7_of_algClosed (h : CharPolyIndepOfEllAlgClosed) : PkgI3.CharPolyIndepOfEll
theorem HDec.AVB1Check.t8_of_pieces (hP : PoincareComplement) (hI : ImageFactorization)
    (hS : SimpleSurjIsogeny) : PkgI3.PoincareReducibility
theorem HDec.AVB1Check.t6_t7_t8_of_avb1 (h6 : HomFreeFiniteAlgClosed)
    (h7 : CharPolyIndepOfEllAlgClosed) (hP : PoincareComplement) (hI : ImageFactorization)
    (hS : SimpleSurjIsogeny) :
    PkgI3.HomFreeFinite ∧ PkgI3.CharPolyIndepOfEll ∧ PkgI3.PoincareReducibility
example (t : HSyn.OpenTextbookLeaves3) :
    PkgI3.HomFreeFinite ∧ PkgI3.CharPolyIndepOfEll ∧ PkgI3.PoincareReducibility := ⟨t.t6, t.t7, t.t8⟩
```

Outcome of the flat run: §5.

## 2. The glue (BaseChange.lean, AlgClosed.lean, Poincare.lean)

For `A, B : PkgI3.AbVar k` and `K̄ = AlgebraicClosure k`:

1. `bcHom`: `Over.pullback (Spec K̄ → Spec k)` on morphisms is a homomorphism
   (`Functor.map.instIsMonHom`), additive (`Functor.map_mul`, `Functor.map_one`).
2. `bcHom_injective`: the projection `A_{K̄} → A` is flat and surjective, hence an epimorphism of
   schemes (`Flat.epi_of_flat_of_surjective`); `f_{K̄}` determines `f`.
3. `tateBC_homT`: g9-abvarbc's `tateBC : T_ℓ(A) → T_ℓ(A_{K̄})` is natural in homomorphisms
   (adjunction naturality `homEquiv_naturality_right_symm`).
4. `tateBC_bijective_closure`: with `κ = algebraMap K̄ \overline{K̄}`, which is bijective because
   `K̄` is algebraically closed (`IsAlgClosed.algebraMap_bijective_of_isIntegral`), every point of
   `A_{K̄}(\overline{K̄})` comes from `A(K̄)`, so g9-abvarbc's `TorsionDescends` holds and `tateBC`
   is bijective, for every `ℓ` and every characteristic.
5. T6: `Hom_k(A,B) ↪ Hom_{K̄}` gives finiteness (`Module.Finite.of_injective`), torsion-freeness,
   hence freeness (`Module.free_of_finite_type_torsion_free'`), and the rank bound
   (`finrank_le_finrank_of_injective`, `dim A_{K̄} = dim A` by g9-abvarbc's `dim_baseChange`).
   Injectivity on Tate modules: `ℤ_ℓ` is flat over `ℤ`, so `ℤ_ℓ ⊗ Hom_k ↪ ℤ_ℓ ⊗ Hom_{K̄}`, and
   `tateHomZl_bc` with the bijective `tateBC` carries a kernel element over `k` to one over `K̄`.
6. T7: `V_ℓ(A) ≅ V_ℓ(A_{K̄})` (base change of the bijective `tateBC`) intertwines `V(φ)` and
   `V(φ_{K̄})`; transport the basis (`Basis.map`); the matrices agree, so the characteristic
   polynomials do. `P` is the one given for `φ_{K̄}`.
7. T8: if `f = i ∘ h`, then `(f, g) = (i, g) ∘ (h × 1_Z)` (`MonObj.comp_mul`, `whiskerRight_fst`,
   `whiskerRight_snd`); `h × 1_Z` is finite and surjective when `h` is
   (`MorphismProperty.pullbackMap`, base change); composites of finite surjective morphisms are
   finite surjective. `h ≠ 0` because `f ≠ 0` (`1 ≫ i = 1` for a homomorphism `i`).

## 3. The new Props: statements, sources, faithfulness

All are `def … : Prop` in `ZInQKernel/Contrib/AVB1/`; their docstrings give the same sources.

### 3.1 `HomFreeFiniteAlgClosed` (LEAF: published theorem)

```lean
def HomFreeFiniteAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : _root_.PkgI3.AbVar k),
    Module.Free ℤ (_root_.PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (_root_.PkgI3.AbVar.Hom A B) ∧
      ((Module.finrank ℤ (_root_.PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
        Function.Injective (_root_.PkgI3.AbVar.tateHomZl ℓ A B)
```

Source: D. Mumford, *Abelian varieties* (1970), §19, Theorem 3 (UNVERIFIED locator; STANDARD):
`Hom(X, Y)` is a free ℤ-module of finite rank `≤ 4 dim X dim Y`, and for `ℓ ≠ char k`,
`ℤ_ℓ ⊗ Hom(X, Y) → Hom_{ℤ_ℓ}(T_ℓX, T_ℓY)` is injective. Relation: **the published statement**,
word for word, over Mumford's algebraically closed field. Faithfulness (VERIFIED by reading the
Lean): `T_ℓ` is the limit of `A(k̄)[ℓⁿ]` (for `k` algebraically closed `AlgebraicClosure k ≅ k`);
the target of `tateHomZl` is the `ℤ_ℓ`-linear maps; `dim` is the Krull dimension of `|A|`, i.e.
`g`; `(ℓ : k) ≠ 0` is `ℓ ≠ char k`. It is strictly smaller than T6 (T6 restricted to
`IsAlgClosed k`).

### 3.2 `CharPolyIndepOfEllAlgClosed` (LEAF: consequence of a published theorem)

```lean
def CharPolyIndepOfEllAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : _root_.PkgI3.AbVar k)
    (φ : _root_.PkgI3.AbVar.End A), ∃ P : ℤ[X], P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((_root_.PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])
```

Source: Mumford (1970), §19, Theorem 4 (UNVERIFIED locator; STANDARD): `P_φ(n) = deg(n_X − φ)` is
a polynomial with integer coefficients, monic of degree `2g`, and it is the characteristic
polynomial of `T_ℓ(φ)` for every `ℓ ≠ char k`. Relation: **consequence** (drops the degree and the
identity with `deg(n − φ)`); never stronger: any finite basis of `V_ℓ` computes the characteristic
polynomial of `T_ℓ(φ) ⊗ ℚ_ℓ`, and if `V_ℓ` had no finite basis the clause would be vacuous.
Strictly smaller than T7 (T7 restricted to `IsAlgClosed k`).

### 3.3 T8's three pieces

```lean
def PoincareComplement : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (J B : _root_.PkgI3.AbVar k)
    (i : _root_.PkgI3.AbVar.Hom B J), IsClosedImmersion i.hom.left →
    ∃ (Z : _root_.PkgI3.AbVar k) (g : _root_.PkgI3.AbVar.Hom Z J),
      _root_.PkgI3.AbVar.IsIsogenyMor (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom)

def ImageFactorization : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : _root_.PkgI3.AbVar k)
    (f : _root_.PkgI3.AbVar.Hom A J),
    ∃ (B : _root_.PkgI3.AbVar k) (h : _root_.PkgI3.AbVar.Hom A B)
      (i : _root_.PkgI3.AbVar.Hom B J),
      Surjective h.hom.left ∧ IsClosedImmersion i.hom.left ∧ f.hom = h.hom ≫ i.hom

def SimpleSurjIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k), _root_.PkgI3.EndDivision A →
    ∀ h : _root_.PkgI3.AbVar.Hom A B, h ≠ 0 → Surjective h.hom.left →
      _root_.PkgI3.AbVar.IsIsogenyMor h.hom
```

- `PoincareComplement` (LEAF, published theorem, weakened). J. S. Milne, *Abelian varieties*, in
  Cornell–Silverman (eds.), *Arithmetic Geometry* (1986), Prop. 12.1 (UNVERIFIED locator, from
  memory and pkg-I3 §2): for an abelian subvariety `A₁ ⊆ A` there is an abelian subvariety `A₂`
  with `A₁ × A₂ → A` an isogeny; any field. Mumford §19 Thm 1 (UNVERIFIED locator): over `k̄`,
  `A₁ ∩ A₂` finite and `A₁ + A₂ = A`, which is the same (dimension count). The Prop adds
  `CharZero k` and drops "`g` is a closed immersion": weaker than the published statement.
  "Abelian subvariety" is read as a homomorphism from an abelian variety that is a closed
  immersion.
- `ImageFactorization` (GLUE-level composite of textbook facts; true, SPECULATIVE only in that no
  single locator states it in this form). `f(A)` is closed (`A` proper), irreducible, reduced and
  a subgroup; in characteristic `0` a reduced group scheme of finite type is smooth (Cartier;
  Mumford §11, UNVERIFIED); `f(A)` is geometrically integral since `f(A)_{k̄} = f_{k̄}(A_{k̄})`; so
  `f(A)` is an abelian variety, `A → f(A)` surjective, `f(A) ↪ J` a closed immersion.
- `SimpleSurjIsogeny` (GLUE-level composite; true). `(ker h)⁰_red` is an abelian subvariety `C` of
  `A`; `C ≠ A` since `h ≠ 0`; if `C ≠ 0`, Poincaré gives `C × D → A` an isogeny with `D ≠ A`, and
  with a quasi-inverse isogeny (group B leaf `WeilPairing.IsogenyQuasiInverse`; Mumford §19,
  Thm 1 Cor. 1, UNVERIFIED) a nonzero endomorphism of `A` with image in `C`, not surjective,
  contradicting `EndDivision A`; so `ker h` is finite, and a surjective homomorphism with finite
  kernel is finite (Milne 1986 Prop. 7.1 / Mumford §6, UNVERIFIED).

Why "strictly smaller": `PoincareComplement` is the published theorem the docs cite for T8
(h-decomposition.md row T8: "Milne Prop. 12.1"), not T8's derived form; the two glue Props
isolate the image/kernel steps that pkg-I3 §3 lists as "+ images of homomorphisms, §§4-8". None
of the three implies T8 alone. They are not proved: `ImageFactorization` needs scheme-theoretic
images of group schemes and Cartier's theorem, `SimpleSurjIsogeny` needs kernels and the finiteness
of quasi-finite proper maps, and neither exists for the kernel's `AbVar` in Mathlib 4.35.

## 4. Statement audit of t6, t7, t8 (no change proposed)

- T6 `PkgI3.HomFreeFinite` is over any field `k`. Over a non-closed `k` it follows from the
  closed case (proved here), so it is never stronger than Mumford's theorem. Milne 1986 Thm 12.5
  (UNVERIFIED) states it over any field directly.
- T7 `PkgI3.CharPolyIndepOfEll`: likewise (proved here); `T_ℓ` uses `AlgebraicClosure k`, and in
  characteristic `p ≠ ℓ` that has the same `ℓ`-power torsion as `k^sep`, as pkg-I3 notes.
- T8 `PkgI3.PoincareReducibility`: true as stated (argument in §3.3). Not stronger than the
  published theory. Its hypothesis `EndDivision A` (every nonzero endomorphism finite and
  surjective) holds vacuously for `A = 0`, and then `Hom(0, J) = 0`, so the conclusion is vacuous.
- Text identity (VERIFIED, `python3 scratch/av-b1/verbatim_check.py`: ALL IDENTICAL): the 26
  declarations the three fields depend on (`Tate.T`, its module structure and `map`, `AbVar`,
  `dim`, `Hom`, `End`, `End0`, `IsIsogenyMor`, `Pt`, `ptMap`, `T`, `V`, `homT`, `tateHom`,
  `tateHomZl`, `baseChange`, `EndDivision`, `HomFreeFinite`, `CharPolyIndepOfEll`,
  `PoincareReducibility`, …) have the same text in the kernel's `HDecomp/Objects.lean` (what the
  AVB1 files prove), the owner file `scratch/pkg-I3/I3.lean`, and leaf-fold3's `Leaves3.lean`.

## 5. Checks

- `lake build ZInQKernel.Contrib.AVB1.BaseChange`, `.AlgClosed`, `.Poincare`: success.
- `scratch/av-b1/Axioms1.lean`: the five `#print axioms` above.
- Flat single file `scratch/av-b1/AVB1Check.lean` (111 374 lines; md5 in
  `scratch/av-b1/check.md5`; regenerate with `python3 scratch/av-b1/mk_check.py`): see
  `scratch/av-b1/log.md` for the exit code, time and `#print axioms` output.

## 6. For the next fold

Replacing t6, t7, t8 in `OpenTextbookLeaves3` by `HomFreeFiniteAlgClosed`,
`CharPolyIndepOfEllAlgClosed`, `PoincareComplement`, `ImageFactorization`, `SimpleSurjIsogeny`
(`HDec.AVB1Check.t6_t7_t8_of_avb1`) turns 3 fields into 5. The gain is faithfulness (T6 and T7
become Mumford's statements verbatim; T8's published core is separated from glue), not the count.
