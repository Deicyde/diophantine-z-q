import ZInQKernel.OneProof.H.TailZ12
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Adeles.FiniteBaseChange
import ZInQKernel.Contrib.TYZGenus.ShimuraModFn

/-!
# shimura-cft: Shimura's Main Theorem I with its reciprocity law (Deligne's adelic form, Tau Ceti's
# Artin map), and the fields `shimuraFamily` / `shimuraFamilyAb` from it

Part A (verbatim copies, scratch files cannot import each other):
* A1: `scratch/r1univ-rigid/R1UnivLeaves.lean` (origin/wip/route-a-fold), lines 10-564: the core
  `LeafQM.AV.R1UnivRigid` (`R1fpPropsAb`, `MumfordRigidityCore`, `r1fpProps_iff_ab_core`);
* A2: `scratch/c-to-printed/Shimura.lean` (origin/wip/c-to-printed), without its `import` line:
  `ShimuraSplit.IsHolFamily`, `holP1_of_isHolFamily`, `IsShimuraHolFamily`, `ShimuraHolFamily`,
  `InGamma3`, `ShimuraMainThmIY3`, `shimuraFamily_of_mainThmI`;
* A3: `HDec.QMSplit.Moduli.ShimuraFamilyAb` from `R1UnivLeaves.lean` (the field of route-a-fold's
  `OpenResearchLeaves11`).

Part B (new): definitions, the leaf `ShimuraCFT.ShimuraMainThmIDeligneY3Ab`, the fields from it, checks.
Part C: the reciprocity clause applies to every `σ ∈ Aut(ℂ/κ(K))` (copies from t5-glue + `exists_artinCondC`).
Part D: its hypotheses can be met (`recip_hyp_nonempty`). Report: `docs/research/shimura-cft.md`.
-/

set_option linter.all false

/-!
# r1univ-rigid: closing the `R1univProps` gap with Mumford's rigidity

`LeafQM.AV.R1univProps` (ZInQKernel/HDecomp/QM/Leaves.lean) classifies families `QMFamily S`
(proper smooth families with endomorphisms `ι(a)` and sections `η(a)`, *no group law*), while the
published fine-moduli theorems classify abelian schemes. This file

1. states Mumford's rigidity/abelian-scheme theorem as one leaf `MumfordRigidity` over Mathlib's
   schemes and the kernel's `PkgI3.AbVar`;
2. defines `QMAbScheme S` (an abelian scheme over `S` with `𝒪`-action and level-3 structure, i.e.
   the objects of the published moduli problem) and states the abelian-scheme versions
   `R1univAbProps`, `R1famAbProps`, `R1fpPropsAb` of the kernel's clauses;
3. proves `R1univProps Y Φ` from `MumfordRigidity` and `R1univAbProps Y Φ`
   (`r1univProps_of_ab`), and `R1fpProps Y Φ ↔ R1fpPropsAb Y Φ` under `MumfordRigidity`
   (`r1fpProps_iff_ab`).

No `sorry`, no `axiom`. See `docs/research/r1univ-rigid.md`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace R1UnivRigid

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ## §1 Fibres of a family that are abelian varieties -/

/-- **`A` is the fibre of `F → S` at the field point `s : Spec K → S`, with identity `e(s)`**:
`g : A → F` makes `A → Spec K` the pullback of `F → S` along `s`, and carries the identity
`K`-point of `A` to the section `e` (the shape of `IsBaseChangeOfPair` and of
`IsFibreOf` at `a = 0`). -/
def IsAbVarFibre {S : Scheme.{0}} (F : Over S) (e : S ⟶ F.left) {K : Type} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K) (g : A.X.left ⟶ F.left) : Prop :=
  IsPullback g A.X.hom F.hom s ∧ (1 : A.Pt K).left ≫ g = s ≫ e

/-- **`g` is a group homomorphism onto the fibre** (for a group object `F` of `Over S`): the
multiplication of `A` followed by `g` is `g × g` followed by the multiplication of `F`; `φ` is the
map `A ×_K A → F ×_S F` induced by `g` (unique, the target being a pullback). -/
def IsGrpFibre {S : Scheme.{0}} (F : Over S) [GrpObj F] {K : Type} [Field K] (A : AbVar K)
    (g : A.X.left ⟶ F.left) : Prop :=
  ∃ φ : (A.X ⊗ A.X).left ⟶ (F ⊗ F).left,
    φ ≫ (fst F F).left = (fst A.X A.X).left ≫ g ∧ φ ≫ (snd F F).left = (snd A.X A.X).left ≫ g ∧
    μ[A.X].left ≫ g = φ ≫ μ[F].left

/-! ## §2 The rigidity leaf -/

/-- **LEAF (Mumford's rigidity; abelian-scheme structure on a smooth proper family with a section).**
Let `S` be a locally noetherian scheme, `F → S` proper, smooth, with geometrically connected fibres,
and `e : S → F` a section, such that every field fibre `F_s` (`s : Spec K → S`) is an abelian variety
with identity `e(s)`. Then `F` carries a group-object structure over `S` (an abelian scheme) with
identity `e` such that
* (a) every `S`-endomorphism `f` of `F` with `f ∘ e = e` is a homomorphism;
* (b) every identification `g : A ≅ F_s` of an abelian variety with a fibre, carrying the identity of
  `A` to `e(s)`, is a group homomorphism.

Sources (theorem numbers from memory, UNVERIFIED): Mumford, *Geometric Invariant Theory*, Ch. 6, §1:
Def. 6.1 (abelian scheme: smooth proper group scheme with geometrically connected fibres), Prop. 6.1
(rigidity lemma), Cor. 6.4 (an `S`-morphism of abelian schemes carrying identity to identity is a
homomorphism), Cor. 6.5 (abelian schemes are commutative), Cor. 6.6 (the group structure is determined
by the identity section), Thm. 6.14 (`S` connected and locally noetherian, `F → S` smooth proper with a
section `e`, one fibre an abelian variety with identity `e(s)`: then `F` is an abelian scheme with
identity `e`; due to Grothendieck, via the rigidity of deformations, §6.3).

*Form*: a consequence of these printed statements. Existence: Thm 6.14 on each connected component of
`S` (open, since `S` is locally noetherian), the group laws glued over the disjoint union. (a) is
Cor. 6.4 for `X = Y = F`. (b): the base change `F_s` is an abelian scheme over `Spec K` with identity
`e(s)`, i.e. an abelian variety, and `g : A ≅ F_s` carries identity to identity, so it is a
homomorphism by Cor. 6.4 over `Spec K` (equivalently Mumford, *Abelian varieties*, §4 Cor. 1, which the
kernel proves: `G0FibreSimple.rigidityHom`). The hypotheses are stronger than printed (every fibre, at
every field, is an abelian variety, and `S` need not be connected), so the leaf is not stronger than its
sources. -/
def MumfordRigidity : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom →
    Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e ∧
      (∀ f : F ⟶ F, e ≫ f.left = e → IsMonHom f) ∧
      (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
        (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g → IsGrpFibre F A g)

/-! ## §3 Abelian schemes with `𝒪`-action and level-3 structure: the published moduli problem -/

/-- **An abelian surface scheme over `S` with QM by `𝒪` and a level-3 structure** (the objects of
the published moduli problem; Shimura 1967, Deligne 1971 in its PEL form, Buzzard 1997 §1 in the
unpolarized form): a `QMFamily` (proper, smooth of relative dimension 2, `ι(a)`, `η(a)`) that is an
abelian scheme (`GrpObj` over `S`, geometrically connected fibres; Mumford GIT Def. 6.1, as the
kernel's `IsAbelianScheme`) with identity `η(0)`, such that `ι : 𝒪 → End_S(A)` is a unital ring
homomorphism into the homomorphisms (`ι(ab) = ι(a) ∘ ι(b)`, `ι(a+b) = ι(a)·ι(b)` in the group
`Hom_S(A, A)`), and `η : 𝒪 → A(S)` is an `𝒪`-linear group homomorphism whose kernel on every field
fibre is exactly `3𝒪`.

The level clauses are the relative form of the kernel's `Level3`: `eta_three` says `η` kills `3𝒪`
globally, so it is a map `(𝒪/3𝒪)_S → A[3]`; `eta_ker` says it is injective on every field fibre. In
characteristic 0 such a map is an isomorphism, both sides being finite étale of degree 81
(`#A_s[3] = 3⁴`, the kernel's `TorsionStructure`), and conversely (STANDARD; the same argument as
`Structures.lean` §2 over a field). Without `eta_three` the class would be too large over a
non-reduced `S` (independent review: `S = Spec ℚ[ε]`, `η = η₀ + ε·δ`). Injectivity of `ι` is not required: for `S ≠ ∅`
a unital ring map `𝒪 → End_S(A)` is injective (its kernel is a two-sided ideal with torsion-free
quotient, `B` is simple), and for `S = ∅` there is nothing to classify. The polarization of the PEL
form is not part of the datum (Lemma P / rv-qm-polar: for the fixed `μ` it exists and is unique;
see the report §4 for its relative form). -/
structure QMAbScheme (S : Scheme.{0}) extends QMFamily S where
  [grp : GrpObj F]
  geomConn : GeometricallyConnected F.hom
  one_eq : η[F].left = eta 0
  iota_hom : ∀ a : O, IsMonHom (Over.homMk (iota a) (iota_over a) : F ⟶ F)
  iota_one : iota 1 = 𝟙 _
  iota_mul : ∀ a b : O, iota (a * b) = iota b ≫ iota a
  iota_add : ∀ a b : O, (Over.homMk (iota (a + b)) (iota_over _) : F ⟶ F) =
    Over.homMk (iota a) (iota_over a) * Over.homMk (iota b) (iota_over b)
  eta_add : ∀ a b : O, (Over.homMk (U := 𝟙_ (Over S)) (eta (a + b)) (eta_sec _) : 𝟙_ (Over S) ⟶ F) =
    Over.homMk (U := 𝟙_ (Over S)) (eta a) (eta_sec a) *
      Over.homMk (U := 𝟙_ (Over S)) (eta b) (eta_sec b)
  eta_linear : ∀ a b : O, eta (a * b) = eta b ≫ iota a
  eta_three : ∀ b : O, eta (3 * b) = eta 0
  eta_ker : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (a : O),
    s ≫ eta a = s ≫ eta 0 ↔ ∃ b : O, a = 3 * b

/-- **R1univ, abelian-scheme clause** (the existence half of the universal property of the published
fine moduli scheme, on abelian-scheme families over proper smooth curves `S/ℚ` whose field fibres are
objects): `R1univProps` restricted to the families that are abelian schemes with `𝒪`-action and
level-3 structure. -/
def R1univAbProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜' : QMAbScheme S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜'.toQMFamily s.left P) →
      ∃ g : S ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S) (P : QML3 K),
        IsFibreOf 𝒜'.toQMFamily s.left P → Φ K (s ≫ g) = M3.mk P

/-- **R1fam, abelian-scheme clause**: `Φ` is induced by an abelian scheme over `Y` with `𝒪`-action
and level-3 structure (the universal object of the published moduli problem). -/
def R1famAbProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ 𝒜 : QMAbScheme Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
    Φ K y = M3.mk P → IsFibreOf 𝒜.toQMFamily y.left P

/-- **R1fp, abelian-scheme clause list**: the kernel's `R1fpProps` with `R1famProps` and
`R1univProps` replaced by their abelian-scheme versions (the form in which the published fine-moduli
theorems are stated). -/
def R1fpPropsAb (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famAbProps Y Φ ∧ R1univAbProps Y Φ

/-! ## §4 The easy directions -/

theorem r1univAbProps_of_r1univProps {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1univProps Y Φ) : R1univAbProps Y Φ :=
  fun S hp hs 𝒜' hfib => h S hp hs 𝒜'.toQMFamily hfib

theorem r1famProps_of_r1famAbProps {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1famAbProps Y Φ) : R1famProps Y Φ := by
  obtain ⟨𝒜, h𝒜⟩ := h
  exact ⟨𝒜.toQMFamily, h𝒜⟩


/-! ## §5 Glue lemmas (proved) -/

/-- A smooth scheme over a field is reduced (copied verbatim from `scratch/curve-split/CurveBij.lean`,
`isReduced_of_smooth`, with `SpecK k` written out). -/
theorem isReduced_of_smooth {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
    have hVU : V ≤ f ⁻¹ᵁ ⊤ := by simp
    have hsm := f.smooth_appLE hU hV hVU
    let _ : Field Γ(Spec (CommRingCat.of k), ⊤) :=
      (ZInQ.Contrib.Dim.isField_sections_spec k ⊤ Set.univ_nonempty).toField
    let _ : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := (f.appLE ⊤ V hVU).hom.toAlgebra
    have : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := hsm
    have : _root_.IsReduced Γ(X, V) :=
      ZInQ.SmoothFibre.isReduced_of_smooth_of_field Γ(Spec (CommRingCat.of k), ⊤) _
    let x' : V := ⟨x, hxV⟩
    have hloc := hV.isLocalization_stalk x'
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
    exact isReduced_localizationPreserves (hV.primeIdealOf x').asIdeal.primeCompl
      (X.presheaf.stalk x') ‹_›
  exact isReduced_of_isReduced_stalk X

/-- Two morphisms from a reduced scheme to a scheme separated over `W`, equal over `W`, are equal
if they agree on all field points (Mathlib's `ext_of_fromSpecResidueField_eq` at residue fields). -/
theorem hom_ext_pts {X Z W : Scheme.{0}} [IsReduced X] (i : Z ⟶ W) [IsSeparated i] (u v : X ⟶ Z)
    (hu : u ≫ i = v ≫ i)
    (h : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ X), t ≫ u = t ≫ v) : u = v :=
  ext_of_fromSpecResidueField_eq u v i Set.univ dense_univ
    (fun x _ => h _ (X.fromSpecResidueField x)) hu

/-- A field point `t : Spec K → S` of a `ℚ`-scheme is a point of `fieldPt K` for the induced
`ℚ`-algebra structure on `K`; so the fibre hypothesis of `R1univProps` (stated for `ℚ`-algebras)
gives fibres at all field points. -/
theorem fibre_of_fieldPt {S : Over (Spec (CommRingCat.of ℚ))} (𝒜 : QMFamily S.left)
    (hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 s.left P)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S.left) : ∃ P : QML3 K, IsFibreOf 𝒜 t P := by
  let : Algebra ℚ K := (Spec.preimage (t ≫ S.hom)).hom.toAlgebra
  have ht : t ≫ S.hom = (fieldPt K).hom := (Spec.map_preimage (t ≫ S.hom)).symm
  exact hfib K (Over.homMk t ht)

/-- The fibres of a family whose field fibres are objects are connected: `F → S` is geometrically
connected (the fibre at `Spec K → S` is `P.A`, geometrically integral over `K`). -/
theorem geomConn_of_fibres {S : Scheme.{0}} (𝒜 : QMFamily S)
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P) : GeometricallyConnected 𝒜.F.hom := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  obtain ⟨P, g, hpb, -, -⟩ := hfib K y
  have e : P.A.X.left ≅ Z := IsPullback.isoIsPullback _ _ hpb h
  have : IrreducibleSpace P.A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton P.A.X.hom
  exact (Scheme.homeoOfIso e).surjective.connectedSpace (Scheme.homeoOfIso e).continuous

/-- The identity point of the fibre goes to `η(0)`. -/
theorem one_left_comp {S : Scheme.{0}} {𝒜 : QMFamily S} {K : Type} [Field K]
    {t : Spec (CommRingCat.of K) ⟶ S} {P : QML3 K} {g : P.A.X.left ⟶ 𝒜.F.left}
    (he : ∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = t ≫ 𝒜.eta a) :
    (1 : P.A.Pt K).left ≫ g = t ≫ 𝒜.eta 0 := by
  have h0 := he 0
  rw [map_zero] at h0
  exact h0

/-- Morphisms `F → F` over `S` are determined on the fibres, when `F` is reduced. -/
theorem F_ext {S : Scheme.{0}} (𝒜 : QMFamily S) [IsReduced 𝒜.F.left]
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P)
    (u v : 𝒜.F.left ⟶ 𝒜.F.left) (hu : u ≫ 𝒜.F.hom = v ≫ 𝒜.F.hom)
    (h : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K)
      (g : P.A.X.left ⟶ 𝒜.F.left), IsPullback g P.A.X.hom 𝒜.F.hom t →
      (∀ a : O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a) →
      (∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = t ≫ 𝒜.eta a) → g ≫ u = g ≫ v) :
    u = v := by
  have := 𝒜.proper
  refine hom_ext_pts 𝒜.F.hom u v hu (fun K _ x => ?_)
  obtain ⟨P, g, hpb, hι, he⟩ := hfib K (x ≫ 𝒜.F.hom)
  have hx := hpb.lift_fst x (𝟙 _) (by simp)
  rw [← hx, Category.assoc, Category.assoc, h K _ P g hpb hι he]

/-- Sections of `F → S` are determined on the fibres, when `S` is reduced. -/
theorem sec_ext {S : Scheme.{0}} [IsReduced S] (𝒜 : QMFamily S)
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P)
    (u v : S ⟶ 𝒜.F.left) (hu : u ≫ 𝒜.F.hom = v ≫ 𝒜.F.hom)
    (h : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K)
      (g : P.A.X.left ⟶ 𝒜.F.left), IsPullback g P.A.X.hom 𝒜.F.hom t →
      (∀ a : O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a) →
      (∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = t ≫ 𝒜.eta a) → t ≫ u = t ≫ v) :
    u = v := by
  have := 𝒜.proper
  refine hom_ext_pts 𝒜.F.hom u v hu (fun K _ t => ?_)
  obtain ⟨P, g, hpb, hι, he⟩ := hfib K t
  exact h K t P g hpb hι he


/-- `lift` into the fibre product commutes with the fibre identification `g` (bookkeeping for the
group laws). -/
theorem lift_comp_φ {S : Scheme.{0}} {F : Over S} {K : Type} [Field K] {A : AbVar K}
    {g : A.X.left ⟶ F.left} {X : Over (Spec (CommRingCat.of K))} {Z : Over S}
    (f₁ f₂ : X ⟶ A.X) (h₁ h₂ : Z ⟶ F) (u : X.left ⟶ Z.left)
    (φ : (A.X ⊗ A.X).left ⟶ (F ⊗ F).left)
    (hφ₁ : φ ≫ (fst F F).left = (fst A.X A.X).left ≫ g)
    (hφ₂ : φ ≫ (snd F F).left = (snd A.X A.X).left ≫ g)
    (e₁ : f₁.left ≫ g = u ≫ h₁.left) (e₂ : f₂.left ≫ g = u ≫ h₂.left) :
    (lift f₁ f₂).left ≫ φ = u ≫ (lift h₁ h₂).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change (lift f₁ f₂).left ≫ φ ≫ (fst F F).left = u ≫ (lift h₁ h₂).left ≫ (fst F F).left
    rw [hφ₁, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst, e₁]
  · simp only [Category.assoc]
    change (lift f₁ f₂).left ≫ φ ≫ (snd F F).left = u ≫ (lift h₁ h₂).left ≫ (snd F F).left
    rw [hφ₂, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd, e₂]

/-! ## §6 A family with object fibres is an abelian scheme with `𝒪`-action (from the rigidity leaf) -/

/-- **Main construction.** Over a reduced locally noetherian `S`, a `QMFamily` with reduced total
space all of whose field fibres are objects (`QML3`) underlies a `QMAbScheme`. The group law and
(a), (b) come from `MumfordRigidity`; the ring-homomorphism and level identities are checked on
field points (`hom_ext_pts`). -/
theorem exists_qmAbScheme (hR : MumfordRigidity) {S : Scheme.{0}} [IsReduced S]
    [IsLocallyNoetherian S] (𝒜 : QMFamily S) [IsReduced 𝒜.F.left]
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P) :
    ∃ 𝒜' : QMAbScheme S, 𝒜'.toQMFamily = 𝒜 := by
  have := 𝒜.proper
  have := 𝒜.smooth
  have hsm : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  have hgc := geomConn_of_fibres 𝒜 hfib
  obtain ⟨G, hη, ha, hb⟩ := hR S 𝒜.F (𝒜.eta 0) inferInstance 𝒜.proper hsm hgc (𝒜.eta_sec 0)
    (fun K _ s => by
      obtain ⟨P, g, hpb, -, he⟩ := hfib K s
      exact ⟨P.A, g, hpb, one_left_comp he⟩)
  -- `η(0)` is fixed by every `ι(a)`
  have hιe : ∀ a : O, 𝒜.eta 0 ≫ 𝒜.iota a = 𝒜.eta 0 := fun a => by
    refine sec_ext 𝒜 hfib _ _ (by rw [Category.assoc, 𝒜.iota_over])
      (fun K _ t P g hpb hι he => ?_)
    have h0 : t ≫ 𝒜.eta 0 = (1 : P.A.Pt K).left ≫ g := (one_left_comp he).symm
    rw [← Category.assoc t, h0]
    erw [Category.assoc, ← hι a, ← Over.comp_left_assoc, MonObj.one_comp]
  have hone : 𝒜.iota 1 = 𝟙 _ := F_ext 𝒜 hfib _ _ (by rw [𝒜.iota_over, Category.id_comp])
    (fun K _ t P g hpb hι he => by
      rw [← hι 1, map_one, Category.comp_id]
      show (𝟙 P.A.X : P.A.X ⟶ P.A.X).left ≫ g = g
      simp)
  have hmul : ∀ a b : O, 𝒜.iota (a * b) = 𝒜.iota b ≫ 𝒜.iota a := fun a b =>
    F_ext 𝒜 hfib _ _ (by rw [𝒜.iota_over, Category.assoc, 𝒜.iota_over, 𝒜.iota_over])
      (fun K _ t P g hpb hι he => by
        rw [← Category.assoc g (𝒜.iota b), ← hι b, Category.assoc, ← hι a, ← hι (a * b), map_mul]
        show ((P.q.iota b).hom ≫ (P.q.iota a).hom).left ≫ g = _
        rw [Over.comp_left, Category.assoc])
  have hadd : ∀ a b : O, (Over.homMk (𝒜.iota (a + b)) (𝒜.iota_over _) : 𝒜.F ⟶ 𝒜.F) =
      Over.homMk (𝒜.iota a) (𝒜.iota_over a) * Over.homMk (𝒜.iota b) (𝒜.iota_over b) :=
    fun a b => by
      apply Over.OverMorphism.ext
      refine F_ext 𝒜 hfib _ _ (by rw [Over.w, Over.w])
        (fun K _ t P g hpb hι he => ?_)
      obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := hb K t P.A g ⟨hpb, one_left_comp he⟩
      change g ≫ 𝒜.iota (a + b) = _
      rw [← hι (a + b), map_add, AbVar.Hom.hom_add,
        CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, Over.comp_left, Over.comp_left,
        Category.assoc, hφμ,
        reassoc_of% (lift_comp_φ _ _ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F)
          (Over.homMk (𝒜.iota b) (𝒜.iota_over b)) g φ hφ₁ hφ₂ (hι a) (hι b))]
  have headd : ∀ a b : O,
      (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta (a + b)) (𝒜.eta_sec _) : 𝟙_ (Over S) ⟶ 𝒜.F) =
      Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a) *
        Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta b) (𝒜.eta_sec b) := fun a b => by
    apply Over.OverMorphism.ext
    refine sec_ext 𝒜 hfib _ _ (by rw [Over.w, Over.w])
      (fun K _ t P g hpb hι he => ?_)
    obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := hb K t P.A g ⟨hpb, one_left_comp he⟩
    change t ≫ 𝒜.eta (a + b) = _
    rw [← he (a + b), map_add, toMul_add,
      CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, Over.comp_left, Over.comp_left,
      Category.assoc, hφμ,
      reassoc_of% (lift_comp_φ _ _ (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a))
        (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta b) (𝒜.eta_sec b)) t φ hφ₁ hφ₂ (he a) (he b))]
    rfl
  have helin : ∀ a b : O, 𝒜.eta (a * b) = 𝒜.eta b ≫ 𝒜.iota a := fun a b => by
    refine sec_ext 𝒜 hfib _ _
      (by rw [𝒜.eta_sec, Category.assoc, 𝒜.iota_over, 𝒜.eta_sec])
      (fun K _ t P g hpb hι he => ?_)
    have hl : Additive.toMul (P.e.eta (a * b)) =
        Additive.toMul (P.e.eta b) ≫ (P.q.iota a).hom := by
      rw [P.e.linear]; rfl
    rw [← he (a * b), hl, Over.comp_left, Category.assoc, hι a, reassoc_of% (he b)]
    rfl
  have hthree : ∀ b : O, 𝒜.eta (3 * b) = 𝒜.eta 0 := fun b =>
    sec_ext 𝒜 hfib _ _ (by rw [𝒜.eta_sec, 𝒜.eta_sec]) (fun K _ t P g hpb hι he => by
      rw [← he (3 * b), ← he 0, (P.e.eq_iff (3 * b) 0).2 ⟨b, by simp⟩])
  have hker : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (a : O),
      s ≫ 𝒜.eta a = s ≫ 𝒜.eta 0 ↔ ∃ b : O, a = 3 * b := by
    intro K _ s a
    obtain ⟨P, g, hpb, hι, he⟩ := hfib K s
    rw [← he a, ← he 0]
    constructor
    · intro h
      have h' : Additive.toMul (P.e.eta a) = Additive.toMul (P.e.eta 0) := by
        apply Over.OverMorphism.ext
        apply hpb.hom_ext h
        rw [Over.w, Over.w]
      obtain ⟨c, hc⟩ := (P.e.eq_iff a 0).1 (Additive.toMul.injective h')
      exact ⟨c, by simpa using hc⟩
    · rintro ⟨b, rfl⟩
      rw [(P.e.eq_iff (3 * b) 0).2 ⟨b, by simp⟩]
  refine ⟨{ 𝒜 with
    grp := G
    geomConn := hgc
    one_eq := hη
    iota_hom := fun a => ha _ (hιe a)
    iota_one := hone
    iota_mul := hmul
    iota_add := hadd
    eta_add := headd
    eta_linear := helin
    eta_three := hthree
    eta_ker := hker }, rfl⟩

/-! ## §7 `R1univProps` from rigidity and the abelian-scheme clause; the clause lists agree -/

/-- Instances for a proper smooth curve `S/ℚ` and a family over it. -/
theorem reduced_of_smooth_curve {S : Over (Spec (CommRingCat.of ℚ))}
    (hs : SmoothOfRelativeDimension 1 S.hom) (𝒜 : QMFamily S.left) :
    IsReduced S.left ∧ IsLocallyNoetherian S.left ∧ IsReduced 𝒜.F.left := by
  have : Smooth S.hom := SmoothOfRelativeDimension.smooth 1 _
  have := 𝒜.smooth
  have : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  exact ⟨isReduced_of_smooth S.hom, LocallyOfFiniteType.isLocallyNoetherian S.hom,
    isReduced_of_smooth (𝒜.F.hom ≫ S.hom)⟩

/-- **(3) `R1univProps` from Mumford's rigidity and the abelian-scheme clause.** -/
theorem r1univProps_of_ab (hR : MumfordRigidity) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h : R1univAbProps Y Φ) : R1univProps Y Φ := by
  intro S hp hs 𝒜' hfib
  obtain ⟨h1, h2, h3⟩ := reduced_of_smooth_curve hs 𝒜'
  obtain ⟨𝒜, h𝒜⟩ := exists_qmAbScheme hR 𝒜' (fun K _ t => fibre_of_fieldPt 𝒜' hfib t)
  subst h𝒜
  exact h S hp hs 𝒜 hfib

/-- The family of `R1famProps` is an abelian scheme with `𝒪`-action (rigidity). -/
theorem r1famAbProps_of_r1famProps (hR : MumfordRigidity) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (hs : SmoothOfRelativeDimension 1 Y.hom) (h : R1famProps Y Φ) :
    R1famAbProps Y Φ := by
  obtain ⟨𝒜, h𝒜⟩ := h
  obtain ⟨h1, h2, h3⟩ := reduced_of_smooth_curve hs 𝒜
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y), ∃ P : QML3 K,
      IsFibreOf 𝒜 s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K s)
    exact ⟨P, h𝒜 K s P hP.symm⟩
  obtain ⟨𝒜', rfl⟩ := exists_qmAbScheme hR 𝒜 (fun K _ t => fibre_of_fieldPt 𝒜 hfib t)
  exact ⟨𝒜', h𝒜⟩

/-- **The two clause lists agree under rigidity**: `R1fpProps Y Φ ↔ R1fpPropsAb Y Φ`. -/
theorem r1fpProps_iff_ab (hR : MumfordRigidity) (Y : Over (Spec (CommRingCat.of ℚ)))
    (Φ : PtEquiv Y) : R1fpProps Y Φ ↔ R1fpPropsAb Y Φ :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, r1famAbProps_of_r1famProps hR h2 h5,
      r1univAbProps_of_r1univProps h6⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, r1famProps_of_r1famAbProps h5,
      r1univProps_of_ab hR h6⟩⟩


/-- **`R1fpProps = R1fpPropsAb` under rigidity** (as predicates on `(Y, Φ)`): every Prop stated on
`R1fpProps`, in any position, is equivalent to the same text with `R1fpPropsAb`. -/
theorem r1fpProps_eq_ab' (hR : MumfordRigidity) :
    (R1fpProps : (Y : Over (Spec (CommRingCat.of ℚ))) → PtEquiv Y → Prop) = R1fpPropsAb :=
  funext fun Y => funext fun Φ => propext (r1fpProps_iff_ab hR Y Φ)

/-- **Abelian-scheme form of `LeafQM.AV.R1fp`** (leaf R1fp of leaf-qm-fp): its text with `R1fpProps`
replaced by `R1fpPropsAb`. -/
def R1fpAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAb Y Φ

/-- **Abelian-scheme form of `LeafQM.AV.R1R2fp`**: its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def R1R2fpAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpPropsAb Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
      CMExists X Ψ ∧ R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

theorem r1fp_iff_ab (hR : MumfordRigidity) : R1fp ↔ R1fpAb := by
  unfold R1fp R1fpAb
  rw [r1fpProps_eq_ab' hR]

theorem r1R2fp_iff_ab (hR : MumfordRigidity) : R1R2fp ↔ R1R2fpAb := by
  unfold R1R2fp R1R2fpAb
  rw [r1fpProps_eq_ab' hR]


/-! ## §8 Clause (b) of the leaf from its printed core and the kernel's field rigidity -/

/-- **LEAF (Mumford's rigidity, printed core)**: `MumfordRigidity` without clause (b), i.e. *GIT*
Thm. 6.14 (the abelian-scheme structure with identity `e`, on each connected component) and Cor. 6.4
over `S` (clause (a)). Numbers UNVERIFIED, see `MumfordRigidity`. -/
def MumfordRigidityCore : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom →
    Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e ∧ (∀ f : F ⟶ F, e ≫ f.left = e → IsMonHom f)

open scoped CategoryTheory.Obj in
/-- **Clause (b), proved**: for a group object `F` of `Over S`, proper and smooth, every
identification `g : A ≅ F_s` of an abelian variety with a fibre carrying identity to identity is a group
homomorphism. The base change `F_s = (Over.pullback s).obj F` is an abelian variety (its group law is
Mathlib's `Functor.grpObjObj`), `A ≅ F_s` over `K` (`IsPullback.isoPullback`) preserves identities, so
it is a homomorphism by the kernel's `G0FibreSimple.rigidityHom` (Mumford, *Abelian varieties*, §4
Cor. 1, proved from Mathlib). -/
theorem isGrpFibre_of_rigidity {S : Scheme.{0}} (F : Over S) [GrpObj F] [IsProper F.hom]
    [Smooth F.hom] {K : Type} [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
    (g : A.X.left ⟶ F.left) (h : IsAbVarFibre F η[F].left s A g) : IsGrpFibre F A g := by
  obtain ⟨hpb, h1⟩ := h
  let Fs : Over (Spec (CommRingCat.of K)) := (Over.pullback s).obj F
  have : IsProper Fs.hom := by dsimp [Fs]; infer_instance
  have : Smooth Fs.hom := by dsimp [Fs]; infer_instance
  let eA : A.X ≅ Fs := Over.isoMk hpb.isoPullback (by simp [Fs])
  have : GeometricallyIntegral Fs.hom := by
    have e : eA.inv.left ≫ A.X.hom = Fs.hom := Over.w eA.inv
    have : MorphismProperty.RespectsIso (C := Scheme) @GeometricallyIntegral := by
      rw [GeometricallyIntegral.eq_geometrically]; infer_instance
    rw [← e]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral eA.inv.left
      A.X.hom).2 inferInstance
  let AF : AbVar K := ⟨Fs⟩
  have hg : eA.hom.left ≫ pullback.fst F.hom s = g := hpb.isoPullback_hom_fst
  have h1' : η[A.X].left ≫ g = s ≫ η[F].left := by
    rw [← h1]
    change _ = ((toUnit (AbVar.ptObj (K := K) K)) ≫ η[A.X]).left ≫ g
    rw [Over.comp_left, Over.toUnit_left]
    simp [AbVar.ptObj, Algebra.algebraMap_self]
  have hη : η[A.X] ≫ eA.hom = η[AF.X] := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [Over.comp_left, Category.assoc, hg, h1']
      change s ≫ η[F].left = (Functor.LaxMonoidal.ε (Over.pullback s) ≫
        (Over.pullback s).map η[F]).left ≫ pullback.fst F.hom s
      have hs : inv (pullback.snd (𝟙 S) s) ≫ pullback.fst (𝟙 S) s = s := by
        rw [IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
        Over.ε_pullback_left]
      rw [← Category.assoc]
      erw [hs]
    · exact (Over.w (η[A.X] ≫ eA.hom)).trans (Over.w η[AF.X]).symm
  have hmon : IsMonHom eA.hom := G0FibreSimple.rigidityHom K A AF eA.hom hη
  refine ⟨(eA.hom ⊗ₘ eA.hom).left ≫ (Functor.LaxMonoidal.μ (Over.pullback s) F F).left ≫
    pullback.fst _ _, ?_, ?_, ?_⟩
  · change _ ≫ pullback.fst F.hom F.hom = _
    rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst, ← Category.assoc]
    change ((eA.hom ⊗ₘ eA.hom).left ≫ (fst Fs Fs).left) ≫ pullback.fst F.hom s = _
    rw [← Over.comp_left, tensorHom_fst, Over.comp_left, Category.assoc, hg]
  · change _ ≫ pullback.snd F.hom F.hom = _
    rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd, ← Category.assoc]
    change ((eA.hom ⊗ₘ eA.hom).left ≫ (snd Fs Fs).left) ≫ pullback.fst F.hom s = _
    rw [← Over.comp_left, tensorHom_snd, Over.comp_left, Category.assoc, hg]
  · have hm : μ[A.X] ≫ eA.hom = (eA.hom ⊗ₘ eA.hom) ≫ μ[AF.X] := IsMonHom.mul_hom eA.hom
    rw [← hg, ← Over.comp_left_assoc, hm]
    change ((eA.hom ⊗ₘ eA.hom) ≫ Functor.LaxMonoidal.μ (Over.pullback s) F F ≫
      (Over.pullback s).map μ[F]).left ≫ pullback.fst F.hom s = _
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]

/-- **`MumfordRigidity` from its printed core** (clause (b) by `isGrpFibre_of_rigidity`). -/
theorem mumfordRigidity_of_core (hC : MumfordRigidityCore) : MumfordRigidity := by
  intro S F e hN hP hS hG he hfib
  obtain ⟨G, hη, ha⟩ := hC S F e hN hP hS hG he hfib
  refine ⟨G, hη, ha, fun K _ s A g hg => ?_⟩
  rw [← hη] at hg
  exact isGrpFibre_of_rigidity F s A g hg

/-- **(3) with the printed core of the leaf**: `R1univProps` from *GIT* Thm. 6.14 + Cor. 6.4
(`MumfordRigidityCore`) and the abelian-scheme clause. -/
theorem r1univProps_of_core_ab (hC : MumfordRigidityCore) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h : R1univAbProps Y Φ) : R1univProps Y Φ :=
  r1univProps_of_ab (mumfordRigidity_of_core hC) h

/-- The clause lists agree under the printed core of the leaf. -/
theorem r1fpProps_iff_ab_core (hC : MumfordRigidityCore) (Y : Over (Spec (CommRingCat.of ℚ)))
    (Φ : PtEquiv Y) : R1fpProps Y Φ ↔ R1fpPropsAb Y Φ :=
  r1fpProps_iff_ab (mumfordRigidity_of_core hC) Y Φ

end R1UnivRigid

end AV

end LeafQM

/-! # Part A2: verbatim copy of scratch/c-to-printed/Shimura.lean (without its import line) -/


/-!
# shimura-split, Part 4: `ShimuraFamily` (row shimuraFamily) from Shimura's holomorphic family

The row `HDec.QMSplit.Moduli.ShimuraFamily` asks, on one fine witness `(Y, Φ)`, for every algebraic
`π : Y → P¹` a family `τ ↦ y_τ ∈ Y(ℂ)` with the moduli clause (the object at `y_τ` is `ℂ²/ι(𝒪)(τ,1)ᵀ`) and
`τ ↦ π(y_τ)` continuous and holomorphic into `P¹(ℂ)`. qm-split flagged it as Shimura's Main Theorem I
**plus** a GAGA-level step (an algebraic map composed with a holomorphic family is holomorphic).

Here Shimura's statement is a leaf in its own form: **one** family `τ ↦ y_τ` (independent of `π`) with the
moduli clause which is *holomorphic*, where "holomorphic map `ℍ → Y(ℂ)`" is the standard notion written
with the regular functions of `Y`: preimages of Zariski opens are open, and every regular function on a
Zariski open pulls back to a holomorphic function (`IsHolFamily`). The step to every `π : Y → P¹` is proved
in Lean (`ShimuraSplit.holP1_of_isHolFamily`): it only uses the two charts of `π`.
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits Filter Topology
open LeafQM.AV

variable {X : Scheme.{0}}

/-- The point of `X` under a `ℂ`-point. -/
abbrev ptC (y : Spec (CommRingCat.of ℂ) ⟶ X) : X := (Scheme.SpecToEquivOfField ℂ X y).1

open Classical in
/-- The value `f(y) ∈ ℂ` of a regular function `f ∈ Γ(X, U)` at a `ℂ`-point `y` whose point lies in `U`
(the image of `f(x) ∈ κ(x)` under the embedding `κ(x) → ℂ` of `y`), and `0` otherwise. -/
def regVal (U : X.Opens) (f : Γ(X, U)) (y : Spec (CommRingCat.of ℂ) ⟶ X) : ℂ :=
  if h : ptC y ∈ U then (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation U _ h f) else 0

/-- **A holomorphic map `ℍ → X(ℂ)`**, written with the regular functions of `X`: the preimage of every
Zariski open is open, and every regular function on a Zariski open `U` pulls back to a function holomorphic
(analytic) on the preimage of `U`. For a variety this is the usual notion (an affine open embeds in `ℂ^n`
by finitely many regular functions, and the analytic topology is the one induced from `ℂ^n`). -/
def IsHolFamily (φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)) : Prop :=
  (∀ U : X.Opens, IsOpen {τ | ptC (φ τ) ∈ U}) ∧
  ∀ (U : X.Opens) (f : Γ(X, U)) (τ : UpperHalfPlane), ptC (φ τ) ∈ U →
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, regVal U f (φ ⟨z, hz⟩) = g z

/-! ## The two charts of `π` -/

theorem val_of_mem (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X) (h : ptC y ∈ π.U) :
    π.val y = ((regVal π.U π.f y : ℂ) : OnePoint ℂ) := by
  unfold ToP1.val regVal
  rw [dif_pos h, dif_pos h]

theorem eval_res {U U' : X.Opens} (i : U' ⟶ U) (x : X) (hx : x ∈ U') (f : Γ(X, U)) :
    X.evaluation U' x hx (X.presheaf.map i.op f) = X.evaluation U x (i.le hx) f := by
  simp only [Scheme.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

theorem val_of_memV (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X) (hV : ptC y ∈ π.V) :
    π.val y = if regVal π.V π.g y = 0 then OnePoint.infty
      else (((regVal π.V π.g y)⁻¹ : ℂ) : OnePoint ℂ) := by
  have hreg : regVal π.V π.g y =
      (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation π.V (ptC y) hV π.g) := by
    unfold regVal; rw [dif_pos hV]
  rw [hreg]
  by_cases hg : X.evaluation π.V (ptC y) hV π.g = 0
  · have hxU : ptC y ∉ π.U := by
      intro hU
      have := (Scheme.evaluation_eq_zero_iff_notMem_basicOpen X (ptC y) hV π.g).1 hg
      rw [π.basicOpen_g] at this
      exact this ⟨hU, hV⟩
    rw [hg, map_zero, if_pos rfl]
    unfold ToP1.val
    rw [dif_neg hxU]
  · have hmem : ptC y ∈ X.basicOpen π.g :=
      (Scheme.evaluation_ne_zero_iff_mem_basicOpen X (ptC y) hV π.g).1 hg
    rw [π.basicOpen_g] at hmem
    have hU : ptC y ∈ π.U := hmem.1
    have hι0 : (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation π.V (ptC y) hV π.g) ≠ 0 := by
      intro h0
      exact hg ((Scheme.SpecToEquivOfField ℂ X y).2.hom.injective (h0.trans (map_zero _).symm))
    rw [if_neg hι0]
    unfold ToP1.val
    rw [dif_pos hU]
    congr 1
    have hinv := congrArg (X.evaluation (π.U ⊓ π.V) (ptC y) hmem) π.inv
    rw [map_mul, map_one, eval_res, eval_res] at hinv
    have h2 := congrArg (Scheme.SpecToEquivOfField ℂ X y).2 hinv
    rw [map_mul, map_one] at h2
    exact eq_inv_of_mul_eq_one_left h2

/-! ## Topology on `ℍ` versus `ℂ` -/

theorem eventually_of_complex {P : UpperHalfPlane → Prop} {τ : UpperHalfPlane}
    (h : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, P ⟨z, hz⟩) : ∀ᶠ σ in 𝓝 τ, P σ :=
  ((UpperHalfPlane.continuous_coe.tendsto τ).eventually h).mono fun σ hσ => hσ σ.im_pos

theorem complex_of_eventually {P : UpperHalfPlane → Prop} {τ : UpperHalfPlane}
    (h : ∀ᶠ σ in 𝓝 τ, P σ) : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, P ⟨z, hz⟩ := by
  rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ, Filter.eventually_map]
  exact h.mono fun σ hσ hz => hσ

/-- `w ↦ 1/w` as a map `ℂ → P¹(ℂ)` (`0 ↦ ∞`) is continuous at `0`. -/
theorem tendsto_invP1 :
    Tendsto (fun w : ℂ => if w = 0 then (OnePoint.infty : OnePoint ℂ) else ((w⁻¹ : ℂ) : OnePoint ℂ))
      (𝓝 0) (𝓝 OnePoint.infty) := by
  rw [← nhdsNE_sup_pure (0 : ℂ)]
  refine Tendsto.sup ?_ ?_
  · have h1 : Tendsto (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 OnePoint.infty) := by
      have hc := OnePoint.tendsto_coe_infty (X := ℂ)
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at hc
      exact hc.comp tendsto_inv₀_nhdsNE_zero
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (if_neg hw).symm
  · rw [tendsto_pure_left]
    intro s hs
    rw [if_pos rfl]
    exact mem_of_mem_nhds hs

/-! ## The GAGA-level step: every `π : X → P¹` composed with a holomorphic family -/

/-- **For a holomorphic family `φ` and every `π : X → P¹` (by charts), `τ ↦ π(φ τ)` is continuous and
holomorphic into `P¹(ℂ)` at every point.** -/
theorem holP1_of_isHolFamily (π : ToP1 X) {φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)}
    (hφ : IsHolFamily φ) :
    Continuous (fun τ => π.val (φ τ)) ∧
      ∀ τ, HDec.HSyn.G0Split.FibreQM.IsHolP1At (fun τ => π.val (φ τ)) τ := by
  obtain ⟨hopen, hhol⟩ := hφ
  -- the local description at each `τ`
  have key : ∀ τ : UpperHalfPlane,
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, π.val (φ ⟨z, hz⟩) = ((g z : ℂ) : OnePoint ℂ)) ∨
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ = 0 ∧
        ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im,
          π.val (φ ⟨z, hz⟩) = if g z = 0 then OnePoint.infty else (((g z)⁻¹ : ℂ) : OnePoint ℂ)) := by
    intro τ
    by_cases hU : ptC (φ τ) ∈ π.U
    · left
      obtain ⟨g, hg, hev⟩ := hhol π.U π.f τ hU
      have hU' := complex_of_eventually (P := fun σ => ptC (φ σ) ∈ π.U)
        ((hopen π.U).mem_nhds hU)
      refine ⟨g, hg, ?_⟩
      filter_upwards [hev, hU'] with z h1 h2 hz
      rw [val_of_mem π _ (h2 hz), h1 hz]
    · right
      have hV : ptC (φ τ) ∈ π.V := by
        have : ptC (φ τ) ∈ π.U ⊔ π.V := by rw [π.cover]; trivial
        rcases (TopologicalSpace.Opens.mem_sup).1 this with h | h
        · exact absurd h hU
        · exact h
      obtain ⟨g, hg, hev⟩ := hhol π.V π.g τ hV
      have hV' := complex_of_eventually (P := fun σ => ptC (φ σ) ∈ π.V)
        ((hopen π.V).mem_nhds hV)
      refine ⟨g, hg, ?_, ?_⟩
      · have h0 := hev.self_of_nhds τ.im_pos
        rw [← h0]
        have hτ : (⟨(τ : ℂ), τ.im_pos⟩ : UpperHalfPlane) = τ := rfl
        rw [hτ]
        unfold regVal
        rw [dif_pos hV]
        have hnot : ptC (φ τ) ∉ X.basicOpen π.g := by
          rw [π.basicOpen_g]; exact fun h => hU h.1
        rw [(Scheme.evaluation_eq_zero_iff_notMem_basicOpen X _ hV π.g).2 hnot, map_zero]
      · filter_upwards [hev, hV'] with z h1 h2 hz
        rw [val_of_memV π _ (h2 hz), h1 hz]
  refine ⟨continuous_iff_continuousAt.2 fun τ => ?_, fun τ => key τ⟩
  rcases key τ with ⟨g, hg, hev⟩ | ⟨g, hg, hg0, hev⟩
  · have hc : ContinuousAt (fun σ : UpperHalfPlane => ((g σ : ℂ) : OnePoint ℂ)) τ :=
      OnePoint.continuous_coe.continuousAt.comp
        (hg.continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt)
    exact hc.congr (eventually_of_complex (P := fun σ => ((g σ : ℂ) : OnePoint ℂ) = π.val (φ σ))
      (hev.mono fun z hz hz' => (hz hz').symm))
  · have hc : ContinuousAt (fun σ : UpperHalfPlane =>
        if g σ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g σ)⁻¹ : ℂ) : OnePoint ℂ)) τ := by
      have ht := hg.continuousAt.comp (UpperHalfPlane.continuous_coe.continuousAt (x := τ))
      unfold ContinuousAt at ht ⊢
      have hgτ : (g ∘ (fun σ : UpperHalfPlane => (σ : ℂ))) τ = 0 := hg0
      rw [hgτ] at ht
      have hval : (if g τ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g τ)⁻¹ : ℂ) : OnePoint ℂ)) =
          OnePoint.infty := by rw [if_pos hg0]
      dsimp only
      rw [hval]
      exact tendsto_invP1.comp ht
    exact hc.congr (eventually_of_complex
      (P := fun σ => (if g σ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g σ)⁻¹ : ℂ) : OnePoint ℂ)) =
        π.val (φ σ))
      (hev.mono fun z hz hz' => (hz hz').symm))

end ShimuraSplit

namespace HDec

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace FibreQM

open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex

/-- **Shimura's holomorphic family on a witness** (the moduli clause of `IsR1bFamily`, copied verbatim, and
holomorphy of `τ ↦ y_τ` in the sense of `ShimuraSplit.IsHolFamily`; no map to `P¹` involved). -/
def IsShimuraHolFamily (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu) ∧
  ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (yτ τ).left)

/-- **The GAGA-level step, proved**: a holomorphic family with the moduli clause is an `R1bFamily` family for
every `π : Y → P¹`. -/
theorem isR1bFamily_of_hol {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)} (h : IsShimuraHolFamily Y Φ yτ) (π : ToP1 Y.left) :
    IsR1bFamily Y Φ π yτ :=
  ⟨h.1, ShimuraSplit.holP1_of_isHolFamily π h.2⟩

end FibreQM

end G0Split

end HSyn

end HDec

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF (Shimura's complex uniformization of the canonical model, Main Theorem I).**

*Published statement* (Shimura, Ann. of Math. 85 (1967), Main Theorem I; Deligne, Sém. Bourbaki 389 (1971),
§4.15; locators UNVERIFIED, no network): the canonical model `V` of `Γ\ℍ` carries a holomorphic map
`φ : ℍ → V(ℂ)` whose value at `τ` is the moduli point of `ℂ²/ι(𝒪)(τ, 1)ᵀ` (with its `ι` and level
structure).

*Lean form*: some fine witness `(Y, Φ)` (the canonical model `Y₃`) has `τ ↦ y_τ ∈ Y(ℂ)` with the object at
`y_τ` equal (by an `ι`-compatible analytic uniformization with kernel `Λ_τ = ι(𝒪)(τ,1)ᵀ`) to `ℂ²/Λ_τ`, and
`τ ↦ y_τ` holomorphic (`ShimuraSplit.IsHolFamily`: preimages of Zariski opens are open and regular
functions pull back to holomorphic functions, the standard notion for maps into the complex points of a
variety).

*Form*: a **consequence** of Main Thm I (one holomorphic `φ`, as here), not its printed form: Shimura's
`V` for the level-3 group is one geometric component, defined over `ℚ(ζ₃)`, while `Y₃` over `ℚ` has two; the
moduli clause on `Y₃` comes through Deligne's adelic reformulation (§4) with R1 and Lemma QP (independent
review, shimura-split §3.4). The row's "for every `π : Y → P¹`" is derived (`isR1bFamily_of_hol`), so the
flagged GAGA-level composition step is no longer part of the leaf. -/
def ShimuraHolFamily : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ

/-- **Row `shimuraFamily` from Shimura's holomorphic family.** -/
theorem shimuraFamily_of_hol (h : ShimuraHolFamily) : ShimuraFamily := by
  obtain ⟨Y, Φ, h1, yτ, hy⟩ := h
  exact ⟨Y, Φ, h1, fun π => ⟨yτ, HSyn.G0Split.FibreQM.isR1bFamily_of_hol hy π⟩⟩

end HDec.QMSplit.Moduli

#print axioms ShimuraSplit.holP1_of_isHolFamily
#print axioms HDec.QMSplit.Moduli.shimuraFamily_of_hol

example : HDec.QMSplit.Moduli.ShimuraHolFamily → HDec.QMSplit.Moduli.ShimuraFamily :=
  HDec.QMSplit.Moduli.shimuraFamily_of_hol

/-! # c-to-printed, Part H: `shimuraFamily`

Everything above is a verbatim copy of `scratch/shimura-split/ShimuraFam.lean` (shimura-split; it still
compiles against the e38375b3 kernel). Below: the fullest form of Shimura's Main Theorem I that can be stated
over the kernel's and Mathlib's definitions, and the field from it. -/

namespace CToPrinted.Shimura

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- Verbatim copy of the field statement `HDec.QMSplit.Moduli.ShimuraFamily`
(`ZInQKernel/OneProof/H/TailU.lean`). -/
def ShimuraFamily : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1fpProps Y Φ ∧
    ∀ π : ToP1 Y.left, HDec.HSyn.G0Split.FibreQM.R1bFamily Y Φ π

example : ShimuraFamily = HDec.QMSplit.Moduli.ShimuraFamily := rfl

/-- `x ∈ Γ(3) = {x ∈ 𝒪 : nrd x = 1, x ≡ 1 mod 3𝒪}`, the group `Γ_S = B^×_+ ∩ K₃` of the level-3 structure
(`nrd x = x x̄`; units of `𝒪` have `nrd = ±1`, and the positive ones act on `ℍ`). -/
def InGamma3 (x : LeafQM.B) : Prop :=
  LeafQM.InO x ∧ x * star x = 1 ∧ ∃ y : LeafQM.B, LeafQM.InO y ∧ x = 1 + 3 * y

/-- **LEAF `ShimuraMainThmIY3`** (Shimura, Ann. of Math. 85 (1967), Main Theorem I, without its
reciprocity law; with the moduli interpretation of `φ_S` (Shimura 1967 §§2-3 and Ann. of Math. 78 (1963);
Deligne, Sém. Bourbaki 389 (1971), §4); locators recalled, UNVERIFIED).

*Printed* (as recalled): for `S = K₃`, the canonical model `(V_S, φ_S)` over `k_S` (for `K₃`, `ℚ(ζ₃)`):
`V_S` a smooth projective curve, `φ_S : ℍ → V_S(ℂ)` holomorphic, inducing a biholomorphic
`Γ_S\ℍ ≅ V_S(ℂ)`, and Shimura's reciprocity law at the CM points. In the moduli construction, `φ_S(τ)` is the
moduli point of `(ℂ²/Λ_τ, ι, η_τ)`, `Λ_τ = ι(𝒪)(τ,1)ᵀ`, `η_τ(a) = ι(a)(τ,1)ᵀ/3`.

*Lean form*: on a fine witness `(Y, Φ)` (`R1fpProps`; `V_S` is one geometric component of `Y₃`), a map
`τ ↦ y_τ ∈ Y(ℂ)` with the moduli clause and holomorphic (`IsShimuraHolFamily`, shimura-split), whose fibres
are exactly the `Γ(3)`-orbits (injectivity of `Γ_S\ℍ → V_S(ℂ)`; invariance: `Λ_{γτ} = Λ_τ/(cτ+d)` and
`η_{γτ} = η_τ` up to that scalar iff `γ ≡ 1 mod 3𝒪`). Dropped (not statable over Mathlib 4.35): the
reciprocity law, which needs the Artin map `[s, K] : 𝔸_K^× → Gal(K^ab/K)` of an imaginary quadratic `K`
(Mathlib has no global class field theory), and the surjectivity onto `V_S(ℂ)`, which needs the canonical
model `V_S` over `k_S` as a separate object together with Deligne's comparison `Y₃ ⊗ ℚ(ζ₃) = V_S ⊔ V_S^σ`. -/
def ShimuraMainThmIY3 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1fpProps Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ ∧
      ∀ τ τ' : UpperHalfPlane, (yτ τ = yτ τ' ↔ ∃ x : LeafQM.B, InGamma3 x ∧
        ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = BPAnalytic.QM.iota x ∧ g • τ = τ')

/-- shimura-split's leaf from the fuller form (drop the orbit clause). -/
theorem shimuraHolFamily_of_mainThmI (h : ShimuraMainThmIY3) : HDec.QMSplit.Moduli.ShimuraHolFamily := by
  obtain ⟨Y, Φ, h1, yτ, hy, -⟩ := h
  exact ⟨Y, Φ, h1, yτ, hy⟩

/-- **The field `shimuraFamily` from `ShimuraMainThmIY3`** (compiled; the composition with every
`π : Y → P¹` is shimura-split's `holP1_of_isHolFamily`). -/
theorem shimuraFamily_of_mainThmI (h : ShimuraMainThmIY3) : HDec.QMSplit.Moduli.ShimuraFamily :=
  HDec.QMSplit.Moduli.shimuraFamily_of_hol (shimuraHolFamily_of_mainThmI h)

end CToPrinted.Shimura

#print axioms CToPrinted.Shimura.shimuraFamily_of_mainThmI

/-! # Part A3: verbatim from scratch/r1univ-rigid/R1UnivLeaves.lean -/


namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ShimuraFamily`** (row shimuraFamily H-139): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ShimuraFamilyAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∀ π : ToP1 Y.left, HSyn.G0Split.FibreQM.R1bFamily Y Φ π

end HDec.QMSplit.Moduli

/-! # Part B (new): Shimura's Main Theorem I with its reciprocity law, in Deligne's adelic form

All objects below are Mathlib's (finite adeles, ideles, quaternion algebras, schemes) or Tau Ceti's
(`ideleClassArtinMap`, `finiteAdeleBaseChangeAlgEquiv`), vendored in `ZInQKernel/Contrib/TauCeti/`. -/

noncomputable section

namespace ShimuraCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open scoped TensorProduct FiniteAdeleExtension

/-! ## B1. `𝔸_f`, `B ⊗ 𝔸_f`, `𝒪̂` and the level group `K₃`

`𝔸_f = FiniteAdeleRing (𝓞 ℚ) ℚ`: Mathlib's finite adeles of the number field `ℚ` (the base of Tau
Ceti's base change `𝔸_{ℚ,f} ⊗_ℚ K ≅ 𝔸_{K,f}`). The kernel's `ShimuraGlue.Af = FiniteAdeleRing ℤ ℚ` is
the same ring with `ℤ` in place of `𝓞 ℚ`; the definitions of `𝒪̂` and `K₃` below are the kernel's
(`ShimuraGlue.Ohat`, `ShimuraGlue.K3`) with that one change. -/

/-- The finite adeles `𝔸_f` of `ℚ`. -/
abbrev AQ : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

/-- `B ⊗_ℚ 𝔸_f` for `B = (2, −3 | ℚ)`. -/
abbrev BAQ : Type := ShimuraGlue.BR AQ

/-- `ℤ̂ ⊆ 𝔸_f`: the adeles integral at every finite place. -/
def ZhatQ : Set AQ := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ}

/-- `𝒪̂ = 𝒪 ⊗ ℤ̂ ⊆ B ⊗ 𝔸_f`: the `ℤ̂`-span of the basis `1, i, (1+j)/2, (i+k)/2` of the kernel's `𝒪`
(`ShimuraGlue.ofQ`). -/
def OhatQ : Set BAQ := {x | ∃ n : Fin 4 → AQ, (∀ i, n i ∈ ZhatQ) ∧ x = ShimuraGlue.ofQ n}

/-- **`K₃ = {k ∈ 𝒪̂^× : k ≡ 1 mod 3𝒪̂}`**, the level of `Y₃` (as in the kernel's `ShimuraGlue.K3`). -/
def K3Q : Set BAQˣ :=
  {k | (k : BAQ) ∈ OhatQ ∧ ((k⁻¹ : BAQˣ) : BAQ) ∈ OhatQ ∧ ∃ y ∈ OhatQ, (k : BAQ) = 1 + 3 * y}

/-- The embedding `B → B ⊗ 𝔸_f`, coordinatewise. -/
def bEmb : LeafQM.B →ₐ[ℚ] BAQ where
  toFun x := ⟨algebraMap ℚ AQ x.re, algebraMap ℚ AQ x.imI, algebraMap ℚ AQ x.imJ,
    algebraMap ℚ AQ x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, map_add, map_sub, map_mul, map_neg,
      map_ofNat, map_zero] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  commutes' r := by
    show (⟨_, _, _, _⟩ : BAQ) = ⟨algebraMap ℚ AQ r, 0, 0, 0⟩
    apply QuaternionAlgebra.ext <;> simp

/-! ## B2. The embedding `q̂ : 𝔸_{K,f} → B ⊗ 𝔸_f` of an embedding `q : K → B` -/

variable {K : Type} [Field K] [NumberField K]

/-- `𝔸_f ⊗_ℚ K → B ⊗ 𝔸_f`, `a ⊗ k ↦ a · q(k)`. -/
def qT (q : K →ₐ[ℚ] LeafQM.B) : AQ ⊗[ℚ] K →ₐ[AQ] BAQ :=
  Algebra.TensorProduct.lift (Algebra.ofId AQ BAQ) (bEmb.comp q)
    (fun a k => by
      show algebraMap AQ BAQ a * _ = _ * algebraMap AQ BAQ a
      exact Algebra.commutes a _)

/-- **`q̂ : 𝔸_{K,f} → B ⊗ 𝔸_f`**, the extension of `q` to finite adeles, through Tau Ceti's base
change `𝔸_{ℚ,f} ⊗_ℚ K ≅ 𝔸_{K,f}`. -/
def qHat (q : K →ₐ[ℚ] LeafQM.B) : FiniteAdeleRing (𝓞 K) K →+* BAQ :=
  (qT q).toRingHom.comp
    (TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv ℚ K).symm.toRingEquiv.toRingHom

/-- `s ↦ q̂(s_f)`, ideles of `K` to `(B ⊗ 𝔸_f)^×`. -/
def qHatU (q : K →ₐ[ℚ] LeafQM.B) : IdeleGroup (𝓞 K) K →* BAQˣ :=
  (Units.map (qHat q).toMonoidHom).comp (IdeleGroup.toFiniteIdele (𝓞 K) K)

/-! ## B3. The Artin symbol on `Aut(ℂ)`, the Galois action on `ℂ`-points, CM points -/

/-- **`σ = [s, K]` on `K^ab`** for `K ⊂ ℂ` through `κ`: for every finite abelian extension `L/K` and
every `K`-embedding `j : L → ℂ`, `σ ∘ j = j ∘ art_K(s)`, with `art_K = ideleClassArtinMap K L` Tau
Ceti's global Artin map `C_K → Gal(L/K)` (uniformizers ↦ arithmetic Frobenius). -/
def ArtinCondC (κ : K →+* ℂ) (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (j : L →+* ℂ),
    j.comp (algebraMap K L) = κ → ∀ x : L,
      σ (j x) = j (TauCeti.ClassFieldTheory.ideleClassArtinMap K L (QuotientGroup.mk s) x)

/-- The action of `σ ∈ Aut(ℂ)` on `ℂ`-points of a `ℚ`-scheme: `y ↦ y ∘ Spec σ` (on coordinates,
`σ` applied to the values of regular functions). -/
def galPt {Y : Over (Spec (CommRingCat.of ℚ))} (σ : ℂ ≃+* ℂ) (y : fieldPt ℂ ⟶ Y) : fieldPt ℂ ⟶ Y :=
  fieldMap (σ : ℂ →+* ℂ).toRatAlgHom ≫ y

/-- **`z ∈ ℍ` is the CM point of `q : K → B` with reflex embedding `κ`**: `q(K^×)` fixes `z` and acts
on `(z, 1)ᵀ` through `κ`: `ι(q(a))·(z, 1)ᵀ = κ(a)·(z, 1)ᵀ` (`ι = BPAnalytic.QM.iota : B → M₂(ℝ)`). -/
def IsCMPoint (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ) (z : UpperHalfPlane) : Prop :=
  ∀ a : K, Matrix.mulVec ((BPAnalytic.QM.iota (q a)).map (algebraMap ℝ ℂ)) ![(z : ℂ), 1] =
    κ a • ![(z : ℂ), 1]

/-- `B^×_+ ∋ γ` acting on `ℍ` and on `G(𝔸_f)`: the relation `(τ', g') = (γτ, γ g k)` with
`γ ∈ B`, `nrd γ > 0`, `k ∈ K₃` (`γ` acts on `ℍ` through `ι(γ) ∈ GL₂(ℝ)⁺`). -/
def DCRel (τ : UpperHalfPlane) (g : BAQˣ) (τ' : UpperHalfPlane) (g' : BAQˣ) : Prop :=
  ∃ γ : LeafQM.B, 0 < ShimuraGlue.nrdQ ℚ γ ∧
    (∃ M : GL (Fin 2) ℝ, (M : Matrix (Fin 2) (Fin 2) ℝ) = BPAnalytic.QM.iota γ ∧ M • τ = τ') ∧
    ∃ k ∈ K3Q, (g' : BAQ) = bEmb γ * (g : BAQ) * (k : BAQ)

end ShimuraCFT

/-! ## B4. The leaf: Shimura's Main Theorem I (canonical model of `Γ(3)\ℍ`, reciprocity included) in
Deligne's adelic form, on the moduli scheme `Y₃` -/

noncomputable section

namespace ShimuraCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain

/-- **The canonical-model clauses of Shimura's Main Theorem I for `Sh_{K₃}(B^×, ℍ^±)` on a
`ℚ`-scheme `Y` with moduli bijections `Φ`** (Deligne's adelic form), with a map
`Ψ : ℍ × (B ⊗ 𝔸_f)^× → Y(ℂ)`:

1. *(uniformization)* `Ψ` induces a bijection `B^×_+ \ (ℍ × (B ⊗ 𝔸_f)^×) / K₃ ≃ Y(ℂ)`: it is onto,
   and `Ψ(τ, g) = Ψ(τ', g')` iff `(τ', g') = (γτ, γ g k)` with `γ ∈ B^×`, `nrd γ > 0`, `k ∈ K₃`;
2. *(complex structure)* `τ ↦ Ψ(τ, g)` is holomorphic for every `g` (`ShimuraSplit.IsHolFamily`);
3. *(moduli interpretation, at `g = 1`)* the object at `Ψ(τ, 1)` is `ℂ²/ι(𝒪)(τ, 1)ᵀ` with its `ι`
   (and `τ ↦ Ψ(τ, 1)` holomorphic): `IsShimuraHolFamily Y Φ (Ψ · 1)` (shimura-split's clause, verbatim);
4. *(Shimura's reciprocity law at CM points)* for every imaginary quadratic `K`, `κ : K → ℂ`,
   `q : K → B` with CM point `z ∈ ℍ` (`IsCMPoint`, reflex embedding `κ`, or its conjugate when
   `δ = false`), every idele `s` of `K` and every `σ ∈ Aut(ℂ)` with `σ = [s, K]` on `K^ab`
   (`ArtinCondC`, Tau Ceti's Artin map): `σ(Ψ(z, g)) = Ψ(z, q̂(s_f)^ε g)` for all `g`.
   The signs `ε = ±1`, `δ` are existential: they absorb the conventions (Deligne 1971 versus 1979
   normalization of the reciprocity map, `z` versus `z̄` in `h_z`, left versus right Galois action
   on points), which change the printed law only by `s ↦ s⁻¹` or `s ↦ s̄`. -/
def ShimuraDeligneBody (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y),
    (∀ y : fieldPt ℂ ⟶ Y, ∃ τ g, Ψ τ g = y) ∧
    (∀ τ g τ' g', Ψ τ g = Ψ τ' g' ↔ DCRel τ g τ' g') ∧
    (∀ g, ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ τ g).left)) ∧
    HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ (fun τ => Ψ τ 1) ∧
    ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ z g) = Ψ z (qHatU q s ^ (ε : ℤ) * g)

/-- **LEAF `ShimuraMainThmIDeligneY3Ab`** (Shimura's Main Theorem I for `Γ(3)`, printed form with its
reciprocity law, in Deligne's adelic reformulation, on the fine moduli scheme `Y₃` of QM abelian
surfaces with level-3 structure; abelian-scheme form of the moduli clause).

*Published statements* (locators recalled, UNVERIFIED; no network):
* G. Shimura, *Construction of class fields and zeta functions of algebraic curves*, Ann. of Math. 85
  (1967), 58-159, Main Theorem I (existence of the canonical system `(V_S, φ_S)` over `k_S`, with the
  reciprocity law at CM points) and §§2-3 (for `F = ℚ`, `V_S` from the moduli of QM abelian surfaces,
  `φ_S(τ)` the moduli point of `ℂ²/ι(𝒪)(τ,1)ᵀ`);
* P. Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§3-4: Shimura's systems of models over
  the `k_S` are the same as one canonical model `M_K` of `G(ℚ)\(X × G(𝔸_f))/K` over the reflex field
  `E = ℚ`, characterized by `σ[h, g] = [h, r(s) g]` at special points (`σ = art_E(s)`), and for
  quaternion algebras over `ℚ` this model is the moduli scheme (§4); also Milne, *Introduction to
  Shimura varieties* (2005), §§12-14.

*Lean form*: some `(Y, Φ)` with `R1fpPropsAb` (the fine moduli scheme `Y₃` over `ℚ`; r1univ-rigid's
abelian-scheme clause list) satisfies `ShimuraDeligneBody`. `Y₃ = Sh_{K₃}(B^×, ℍ^±)` over `ℚ`: its
two geometric components (`π₀ = ℚ^×_{>0}\𝔸_f^×/nrd K₃ = (ℤ/3)^×`, clause 1) are Shimura's `V_S` and
`V_S^σ` over `k_S = ℚ(ζ₃)` via clauses 1 and 4 and Deligne's comparison between Shimura's systems of models
and the adelic canonical model over the reflex field `ℚ`; the leaf is Deligne's form over `ℚ`, so no
model over `ℚ(ζ₃)` has to be named.

*Form*: a consequence of the print, not stronger: the reciprocity law is stated at every CM point and
every idele, with the conventions made existential (`ε`, `δ`); `ℍ` with `B^×_+` replaces
`ℍ^± = ℂ \ ℝ` with `B^×` (an element of negative norm swaps the half planes); the biholomorphism of
clause 1 is weakened to "bijective, holomorphic in `τ`"; the moduli clause is kept at `g = 1` only;
the field-of-moduli clause (`k_S(φ_S(z))` is a class field) is dropped (it follows from 1 and 4). -/
def ShimuraMainThmIDeligneY3Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ ShimuraDeligneBody Y Φ

/-- The same leaf with the kernel's clause list `R1fpProps` (families without group law); equivalent
to `ShimuraMainThmIDeligneY3Ab` under Mumford's rigidity (`mainThmI_iff_ab`). -/
def ShimuraMainThmIDeligneY3 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ShimuraDeligneBody Y Φ

/-! ## B5. The fields from the leaf -/

/-- The family `τ ↦ Ψ(τ, 1)` is shimura-split's holomorphic family. -/
theorem isShimuraHolFamily_of_body {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : ShimuraDeligneBody Y Φ) :
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ := by
  obtain ⟨Ψ, -, -, -, hmod, -⟩ := h
  exact ⟨fun τ => Ψ τ 1, hmod⟩

/-- **`shimuraFamilyAb` (route-a-fold's field) from the printed leaf.** -/
theorem shimuraFamilyAb_of_mainThmI (h : ShimuraMainThmIDeligneY3Ab) :
    HDec.QMSplit.Moduli.ShimuraFamilyAb := by
  obtain ⟨Y, Φ, h1, hb⟩ := h
  obtain ⟨yτ, hy⟩ := isShimuraHolFamily_of_body hb
  exact ⟨Y, Φ, h1, fun π => ⟨yτ, HDec.HSyn.G0Split.FibreQM.isR1bFamily_of_hol hy π⟩⟩

/-- **`shimuraFamily` (the kernel's field) from the leaf in `R1fpProps` form.** -/
theorem shimuraFamily_of_mainThmI (h : ShimuraMainThmIDeligneY3) :
    HDec.QMSplit.Moduli.ShimuraFamily := by
  obtain ⟨Y, Φ, h1, hb⟩ := h
  obtain ⟨yτ, hy⟩ := isShimuraHolFamily_of_body hb
  exact HDec.QMSplit.Moduli.shimuraFamily_of_hol ⟨Y, Φ, h1, yτ, hy⟩

/-- The two forms of the leaf agree under Mumford's rigidity (`MumfordRigidityCore`, r1univ-rigid). -/
theorem mainThmI_iff_ab (hC : LeafQM.AV.R1UnivRigid.MumfordRigidityCore) :
    ShimuraMainThmIDeligneY3 ↔ ShimuraMainThmIDeligneY3Ab := by
  constructor
  · rintro ⟨Y, Φ, h1, hb⟩
    exact ⟨Y, Φ, (LeafQM.AV.R1UnivRigid.r1fpProps_iff_ab_core hC Y Φ).1 h1, hb⟩
  · rintro ⟨Y, Φ, h1, hb⟩
    exact ⟨Y, Φ, (LeafQM.AV.R1UnivRigid.r1fpProps_iff_ab_core hC Y Φ).2 h1, hb⟩

/-- **`shimuraFamily` from the printed (abelian-scheme) leaf and Mumford's rigidity.** -/
theorem shimuraFamily_of_mainThmIAb (hC : LeafQM.AV.R1UnivRigid.MumfordRigidityCore)
    (h : ShimuraMainThmIDeligneY3Ab) : HDec.QMSplit.Moduli.ShimuraFamily :=
  shimuraFamily_of_mainThmI ((mainThmI_iff_ab hC).2 h)

end ShimuraCFT

#print axioms ShimuraCFT.ShimuraMainThmIDeligneY3Ab
#print axioms ShimuraCFT.shimuraFamilyAb_of_mainThmI
#print axioms ShimuraCFT.shimuraFamily_of_mainThmI
#print axioms ShimuraCFT.shimuraFamily_of_mainThmIAb

/-! ## B6. Checks on the definitions, and c-to-printed's `ShimuraMainThmIY3` from the leaf

`q̂` extends `q` (`qHat_algebraMap`); `K₃ ∩ B^×_+ = Γ(3)` (`dcRel_one_iff`), so the leaf implies the
earlier "fullest statable" form `CToPrinted.Shimura.ShimuraMainThmIY3` (`mainThmIY3_of_mainThmI`). -/

noncomputable section

namespace ShimuraCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open scoped TensorProduct FiniteAdeleExtension

variable {K : Type} [Field K] [NumberField K]

/-- `q̂` extends `q`: `q̂(k) = q(k)` for `k ∈ K ⊂ 𝔸_{K,f}`. -/
theorem qHat_algebraMap (q : K →ₐ[ℚ] LeafQM.B) (k : K) :
    qHat q (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) = bEmb (q k) := by
  simp [qHat, qT, TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv_symm_algebraMap]

/-- `ℤ̂` as a subring. -/
def ZhatS : Subring AQ where
  carrier := ZhatQ
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

/-- A rational number lies in `ℤ̂` iff it is an integer. -/
theorem rat_mem_zhat_iff (r : ℚ) : algebraMap ℚ AQ r ∈ ZhatQ ↔ ∃ m : ℤ, r = m := by
  constructor
  · intro h
    obtain ⟨o, ho⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) (K := ℚ) r
      (fun v => by
        have hv := h v
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact hv)
    exact ⟨Rat.ringOfIntegersEquiv o, by rw [Rat.ringOfIntegersEquiv_apply_coe, ho]⟩
  · rintro ⟨m, rfl⟩
    have : algebraMap ℚ AQ (m : ℚ) = ((m : ℤ) : AQ) := map_intCast _ _
    rw [this]
    exact intCast_mem ZhatS m


/-- Coordinates in the basis `1, i, (1+j)/2, (i+k)/2` (inverse of `ShimuraGlue.ofQ`). -/
def cQ {R : Type*} [CommRing R] (x : ShimuraGlue.BR R) : Fin 4 → R :=
  ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK]

theorem cQ_ofQ {R : Type*} [CommRing R] [Algebra ℚ R] (n : Fin 4 → R) :
    cQ (ShimuraGlue.ofQ n) = n := by
  have hh := ShimuraGlue.two_mul_half R
  funext i
  fin_cases i <;> simp [cQ, ShimuraGlue.ofQ]
  · linear_combination (n 2) * hh
  · linear_combination (n 3) * hh

theorem cQ_bEmb (x : LeafQM.B) : cQ (bEmb x) = fun i => algebraMap ℚ AQ (cQ x i) := by
  funext i
  fin_cases i <;> simp [cQ, bEmb, map_sub, map_mul, map_ofNat]

theorem cQ_ofInt (m : Fin 4 → ℤ) : cQ (LeafQM.ofInt m) = fun i => (m i : ℚ) := by
  funext i
  fin_cases i <;> simp [cQ, LeafQM.ofInt] <;> ring

theorem eq_ofInt_of_cQ (x : LeafQM.B) (m : Fin 4 → ℤ) (h : ∀ i, cQ x i = m i) :
    x = LeafQM.ofInt m := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [cQ] at h0 h1 h2 h3
  ext <;> simp [LeafQM.ofInt] <;> linarith

theorem inO_of_bEmb_mem {x : LeafQM.B} (h : bEmb x ∈ OhatQ) : InO x := by
  obtain ⟨n, hn, he⟩ := h
  have hc : ∀ i, algebraMap ℚ AQ (cQ x i) ∈ ZhatQ := fun i => by
    have := congrFun (congrArg cQ he) i
    rw [cQ_bEmb, cQ_ofQ] at this
    have h' : algebraMap ℚ AQ (cQ x i) = n i := this
    rw [h']; exact hn i
  choose m hm using fun i => (rat_mem_zhat_iff _).1 (hc i)
  exact ⟨m, eq_ofInt_of_cQ x m hm⟩

theorem bEmb_mem_of_inO {x : LeafQM.B} (h : InO x) : bEmb x ∈ OhatQ := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨fun i => algebraMap ℚ AQ (m i), fun i => (rat_mem_zhat_iff _).2 ⟨m i, rfl⟩, ?_⟩
  have h1 := ShimuraGlue.ofQ_coords (bEmb (LeafQM.ofInt m))
  have h2 : (![(bEmb (LeafQM.ofInt m)).re - (bEmb (LeafQM.ofInt m)).imJ,
      (bEmb (LeafQM.ofInt m)).imI - (bEmb (LeafQM.ofInt m)).imK,
      2 * (bEmb (LeafQM.ofInt m)).imJ, 2 * (bEmb (LeafQM.ofInt m)).imK] : Fin 4 → AQ) =
      fun i => algebraMap ℚ AQ (m i) := by
    have := cQ_bEmb (LeafQM.ofInt m)
    rw [cQ_ofInt] at this
    exact this
  rw [h2] at h1
  exact h1

theorem star_ofInt (m : Fin 4 → ℤ) :
    star (LeafQM.ofInt m) = LeafQM.ofInt ![m 0 + m 2, -m 1, -m 2, -m 3] := by
  ext <;> simp [LeafQM.ofInt] <;> ring

theorem inO_star {x : LeafQM.B} (h : InO x) : InO (star x) := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨_, star_ofInt m⟩

theorem nrd_bEmb (x : LeafQM.B) :
    ShimuraGlue.nrdQ AQ (bEmb x) = algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ x) := by
  simp only [ShimuraGlue.nrdQ_apply]
  simp [bEmb, map_sub, map_add, map_mul, map_pow, map_ofNat]

theorem nrd_mem_of_mem {y : BAQ} (h : y ∈ OhatQ) : ShimuraGlue.nrdQ AQ y ∈ ZhatQ := by
  obtain ⟨n, hn, rfl⟩ := h
  rw [ShimuraGlue.nrdQ_ofQ]
  have : ShimuraGlue.N4 (fun i => ZhatS.subtype ⟨n i, hn i⟩) =
      ZhatS.subtype (ShimuraGlue.N4 (fun i => (⟨n i, hn i⟩ : ZhatS))) := (ShimuraGlue.map_N4 _ _).symm
  rw [show (fun i => ZhatS.subtype ⟨n i, hn i⟩) = n from rfl] at this
  rw [this]
  exact (ShimuraGlue.N4 (fun i => (⟨n i, hn i⟩ : ZhatS))).2

theorem nrd_coe_eq {x : LeafQM.B} :
    ((ShimuraGlue.nrdQ ℚ x : ℚ) : LeafQM.B) = x * star x := ShimuraGlue.nrdQ_eq_mul_star x

theorem star_mul_eq {x : LeafQM.B} : star x * x = x * star x := by
  exact (star_comm_self' x)


theorem nrdQ_eq_one {x : LeafQM.B} (h : x * star x = 1) : ShimuraGlue.nrdQ ℚ x = 1 := by
  have h1 : ((ShimuraGlue.nrdQ ℚ x : ℚ) : LeafQM.B) = ((1 : ℚ) : LeafQM.B) := by
    rw [nrd_coe_eq, h]; rfl
  exact QuaternionAlgebra.coe_injective h1

/-- A positive rational `r` with `r, r⁻¹` both in `ℤ̂` is `1`. -/
theorem eq_one_of_mem {r : ℚ} (hpos : 0 < r) (h1 : algebraMap ℚ AQ r ∈ ZhatQ)
    (h2 : algebraMap ℚ AQ r⁻¹ ∈ ZhatQ) : r = 1 := by
  obtain ⟨m, hm⟩ := (rat_mem_zhat_iff _).1 h1
  obtain ⟨m', hm'⟩ := (rat_mem_zhat_iff _).1 h2
  have hr0 : r ≠ 0 := hpos.ne'
  have hmm : (m : ℚ) * m' = 1 := by rw [← hm, ← hm', mul_inv_cancel₀ hr0]
  have hmm' : m * m' = 1 := by exact_mod_cast hmm
  have hmpos : (0 : ℚ) < m := hm ▸ hpos
  have hmpos' : 0 < m := by exact_mod_cast hmpos
  have : m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm' with h | h
    · exact h
    · omega
  rw [hm, this]; simp

/-- **`K₃ ∩ B^×_+ = Γ(3)`**: the relation `DCRel` at `g = g' = 1` is the action of
`Γ(3) = {x ∈ 𝒪 : x x̄ = 1, x ≡ 1 mod 3𝒪}` (c-to-printed's `InGamma3`). -/
theorem dcRel_one_iff (τ τ' : UpperHalfPlane) :
    DCRel τ 1 τ' 1 ↔ ∃ x : LeafQM.B, CToPrinted.Shimura.InGamma3 x ∧
      ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = BPAnalytic.QM.iota x ∧ g • τ = τ' := by
  constructor
  · rintro ⟨γ, hpos, hM, k, ⟨hk1, hk2, y, hy, hky⟩, hg⟩
    refine ⟨γ, ?_, hM⟩
    -- `q(γ) = k⁻¹`
    have hgk : bEmb γ * (k : BAQ) = 1 := by simpa using hg.symm
    have hγk : bEmb γ = ((k⁻¹ : BAQˣ) : BAQ) := by
      calc bEmb γ = bEmb γ * (k : BAQ) * ((k⁻¹ : BAQˣ) : BAQ) := by simp [mul_assoc]
        _ = _ := by rw [hgk, one_mul]
    have hγO : bEmb γ ∈ OhatQ := hγk ▸ hk2
    have hO : InO γ := inO_of_bEmb_mem hγO
    -- `nrd γ = 1`
    set r := ShimuraGlue.nrdQ ℚ γ with hr
    have hn1 : algebraMap ℚ AQ r ∈ ZhatQ := nrd_bEmb γ ▸ nrd_mem_of_mem hγO
    have hnk : ShimuraGlue.nrdQ AQ (k : BAQ) ∈ ZhatQ := nrd_mem_of_mem hk1
    have hprod : algebraMap ℚ AQ r * ShimuraGlue.nrdQ AQ (k : BAQ) = 1 := by
      rw [← nrd_bEmb, ← map_mul, hgk, map_one]
    have hkinv : ShimuraGlue.nrdQ AQ (k : BAQ) = algebraMap ℚ AQ r⁻¹ := by
      have hr0 : r ≠ 0 := hpos.ne'
      calc ShimuraGlue.nrdQ AQ (k : BAQ)
          = algebraMap ℚ AQ r⁻¹ * (algebraMap ℚ AQ r * ShimuraGlue.nrdQ AQ (k : BAQ)) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hr0, map_one, one_mul]
        _ = _ := by rw [hprod, mul_one]
    have hr1 : r = 1 := eq_one_of_mem hpos hn1 (hkinv ▸ hnk)
    have hγs : γ * star γ = 1 := by
      rw [← nrd_coe_eq, ← hr, hr1]; rfl
    have hsγ : star γ * γ = 1 := by rw [star_mul_eq, hγs]
    -- `k = q(γ̄)`, so `γ̄ ≡ 1 mod 3`
    have hkst : (k : BAQ) = bEmb (star γ) := by
      calc (k : BAQ) = bEmb (star γ * γ) * (k : BAQ) := by rw [hsγ, map_one, one_mul]
        _ = bEmb (star γ) * (bEmb γ * (k : BAQ)) := by rw [map_mul, mul_assoc]
        _ = _ := by rw [hgk, mul_one]
    set y₁ : LeafQM.B := (1 / 3 : ℚ) • (star γ - 1) with hy₁
    have hy₁e : bEmb y₁ = y := by
      rw [hy₁, map_smul, map_sub, map_one, ← hkst, hky]
      rw [Algebra.smul_def, add_sub_cancel_left, ← mul_assoc]
      have : (algebraMap ℚ BAQ (1 / 3)) * (3 : BAQ) = 1 := by
        rw [← map_ofNat (algebraMap ℚ BAQ) 3, ← map_mul]; norm_num
      rw [this, one_mul]
    have hy₁O : InO y₁ := inO_of_bEmb_mem (hy₁e ▸ hy)
    have hsγ1 : star γ = 1 + 3 * y₁ := by
      rw [hy₁, Algebra.smul_def, ← mul_assoc]
      have : (3 : LeafQM.B) * algebraMap ℚ LeafQM.B (1 / 3) = 1 := by
        rw [← map_ofNat (algebraMap ℚ LeafQM.B) 3, ← map_mul]; norm_num
      rw [this, one_mul]; abel
    refine ⟨hO, hγs, star y₁, inO_star hy₁O, ?_⟩
    have := congrArg star hsγ1
    rw [star_star, star_add, star_one, star_mul, star_ofNat] at this
    rw [this]
    congr 1
    exact (Commute.ofNat_right _ 3).eq
  · rintro ⟨x, ⟨hxO, hxn, y, hyO, hxy⟩, hM⟩
    have hsx : star x * x = 1 := by rw [star_mul_eq, hxn]
    have hn : ShimuraGlue.nrdQ ℚ x = 1 := nrdQ_eq_one hxn
    let k : BAQˣ :=
      { val := bEmb (star x)
        inv := bEmb x
        val_inv := by rw [← map_mul, hsx, map_one]
        inv_val := by rw [← map_mul, hxn, map_one] }
    refine ⟨x, by rw [hn]; norm_num, hM, k, ⟨bEmb_mem_of_inO (inO_star hxO), bEmb_mem_of_inO hxO,
      bEmb (star y), bEmb_mem_of_inO (inO_star hyO), ?_⟩, ?_⟩
    · show bEmb (star x) = 1 + 3 * bEmb (star y)
      rw [hxy, star_add, star_one, star_mul, star_ofNat, map_add, map_one, map_mul, map_ofNat,
        (Commute.ofNat_right _ 3).eq]
    · show (1 : BAQ) = bEmb x * 1 * bEmb (star x)
      rw [mul_one, ← map_mul, hxn, map_one]

/-- **c-to-printed's `ShimuraMainThmIY3` from the printed leaf** (the new leaf is at least as strong:
its fibre clause at `g = 1` is the `Γ(3)`-orbit clause, by `dcRel_one_iff`). -/
theorem mainThmIY3_of_mainThmI (h : ShimuraMainThmIDeligneY3) :
    CToPrinted.Shimura.ShimuraMainThmIY3 := by
  obtain ⟨Y, Φ, h1, Ψ, -, hfib, -, hmod, -⟩ := h
  exact ⟨Y, Φ, h1, fun τ => Ψ τ 1, hmod, fun τ τ' => (hfib τ 1 τ' 1).trans (dcRel_one_iff τ τ')⟩

end ShimuraCFT

#print axioms ShimuraCFT.qHat_algebraMap
#print axioms ShimuraCFT.dcRel_one_iff
#print axioms ShimuraCFT.mainThmIY3_of_mainThmI

/-! # Part C: the reciprocity clause applies to every `σ ∈ Aut(ℂ/κ(K))`

C1 (verbatim copies from origin/wip/t5-glue, `scratch/t5-glue/`): `mem_range_of_isAlgebraic`
(`Field.lean`), `AbsArtinSurjective` (`parts/Artin.lean`) and the section `AbsArtin` of
`parts/AbsArtin.lean` (surjectivity of Tau Ceti's absolute Artin map for number fields without real
places, proved). C2 (new): every `σ ∈ Aut(ℂ)` fixing `κ(K)` is `[s, K]` on `K^ab` for some idele `s`
(`exists_artinCondC`), so clause 4 of `ShimuraDeligneBody` determines `σ(Ψ(z, g))` for all such `σ`. -/

noncomputable section

namespace T5Glue

open MvPolynomial

/-- An element algebraic over an algebraically closed subfield lies in it. -/
theorem mem_range_of_isAlgebraic {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {z : K} (hz : IsAlgebraic k z) : z ∈ Set.range (algebraMap k K) := by
  have hi : IsIntegral k z := hz.isIntegral
  exact minpoly.mem_range_of_degree_eq_one k z
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))

end T5Glue


noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain

/-- **GLUE ABS-ARTIN-SURJ (class field theory, over Tau Ceti's own objects).** The absolute Artin
map `C_K → G_K^ab` of Tau Ceti's global class formation is surjective: every element of the
absolute Galois group is, modulo the closure of the commutator subgroup, the absolute Artin symbol
of an idele class. (Tau Ceti proves dense image, `ClassFormation.denseRange_absoluteArtinMap`;
surjectivity for number fields follows from the compactness of `C_K` modulo its connected component
(finite class number, compactness of `Ô^×`, Artin symbols trivial on the archimedean component):
Neukirch, *Algebraic number theory*, VI.5; Artin–Tate, Ch. IX; UNVERIFIED numbers.) -/
def AbsArtinSurjective (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ g : TauCeti.AbsoluteGaloisGroup K, ∃ c : IdeleClassGroup (𝓞 K) K,
    Additive.ofMul (g : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (Additive.ofMul c))

section AbsArtin

variable (K : Type) [Field K] [NumberField K]

set_option synthInstance.maxHeartbeats 400000 in
instance zeroDim_Gab :
    ZeroDimensionalSpace (TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) :=
  inferInstance

/-- The absolute Artin map `C_K →* G_K^ab` (multiplicative form). -/
def absArt : IdeleClassGroup (𝓞 K) K →* TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K) :=
  MonoidHom.toAdditive.symm
    ((globalClassFormation K).absoluteArtinMap.comp (globalGroundEquiv K).toAddMonoidHom)

theorem ofMul_absArt (c : IdeleClassGroup (𝓞 K) K) :
    Additive.ofMul (absArt K c) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (Additive.ofMul c)) :=
  rfl

theorem continuous_absArt : Continuous (absArt K) := by
  refine continuous_of_continuousAt_one (absArt K) ?_
  rw [ContinuousAt, map_one]
  intro N hN
  obtain ⟨U0, hU0N, hU0o, h1⟩ := mem_nhds_iff.1 hN
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU0o h1
  obtain ⟨V, hV⟩ := (globalClassFormation K).exists_absoluteArtinMap_mem_iff H.toOpenSubgroup
  have hpre : ∀ c, c ∈ globalNormSubgroup K V → absArt K c ∈ (H : Set _) := by
    intro c hc
    rw [mem_globalNormSubgroup_iff, ← hV] at hc
    exact hc
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((isOpen_globalNormSubgroup K V).mem_nhds (one_mem _)) ?_
  intro c hc
  exact hU0N (hH (hpre c hc))

theorem denseRange_absArt : DenseRange (absArt K) := by
  have h1 : DenseRange (fun a => Additive.toMul ((globalClassFormation K).absoluteArtinMap a)) :=
    DenseRange.comp (Additive.toMul.surjective.denseRange) (globalClassFormation K).denseRange_absoluteArtinMap
      continuous_toMul
  have h2 : Function.Surjective fun c : IdeleClassGroup (𝓞 K) K =>
      globalGroundEquiv K (Additive.ofMul c) :=
    (globalGroundEquiv K).surjective.comp Additive.ofMul.surjective
  have : (absArt K : IdeleClassGroup (𝓞 K) K → _) =
      (fun a => Additive.toMul ((globalClassFormation K).absoluteArtinMap a)) ∘
        (fun c : IdeleClassGroup (𝓞 K) K => globalGroundEquiv K (Additive.ofMul c)) := rfl
  rw [DenseRange, this, h2.range_comp]
  exact h1

/-- **Idele classes with trivial finite part are killed** (no real places). -/
theorem absArt_eq_one_of_coord (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) (x : IdeleGroup (𝓞 K) K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.ideleFiniteCoord x = 1) :
    absArt K (x : IdeleClassGroup (𝓞 K) K) = 1 := by
  apply Additive.ofMul.injective
  rw [ofMul_absArt, ofMul_one, (globalClassFormation K).absoluteArtinMap_eq_zero_iff]
  intro V
  have hmem : (x : IdeleClassGroup (𝓞 K) K) ∈ globalNormSubgroup K V := by
    rw [globalNormSubgroup_eq_range_classField]
    apply isAdmissibleModulus_abelianConductor K (classField K V)
    rw [mem_raySubgroup_iff]
    refine ⟨x, ?_, rfl⟩
    rw [mem_ideleCongruenceSubgroup_iff]
    refine ⟨fun v _ => by simp [hx v], fun v _ => by simp [hx v], fun w _ => absurd w.2 (hK w.1)⟩
  exact hmem

/-- Units of the integral finite adeles, `Ô^×`. -/
def intUnits : Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
  {w | (w : FiniteAdeleRing (𝓞 K) K) ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K ∧
    ((w⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) ∈
      FiniteAdeleRing.integralAdeles (𝓞 K) K}

theorem isCompact_intUnits : IsCompact (intUnits K) := by
  have hc := FiniteAdeleRing.isCompact_integralAdeles (R := 𝓞 K) (K := K)
  have hc2 : IsCompact ((FiniteAdeleRing.integralAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) ×ˢ
      (MulOpposite.op '' (FiniteAdeleRing.integralAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))) :=
    hc.prod (hc.image MulOpposite.continuous_op)
  have := Units.isClosedEmbedding_embedProduct.isCompact_preimage hc2
  convert this using 1
  ext w
  simp [intUnits, Units.embedProduct]

/-- `Ô^× → 𝕀_K`, `w ↦ (1, w)`. -/
def finEmb : (FiniteAdeleRing (𝓞 K) K)ˣ →* IdeleGroup (𝓞 K) K :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
    FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K)

theorem continuous_finEmb : Continuous (finEmb K) :=
  Units.continuous_map (show Continuous fun w : FiniteAdeleRing (𝓞 K) K =>
    ((1 : InfiniteAdeleRing K), w) from continuous_const.prodMk continuous_id)

/-- The compact set `T = ⋃_q q̄·[Ô^×]` (finitely many ray-class representatives `q̄`). -/
def bigT : Set (IdeleClassGroup (𝓞 K) K) :=
  ⋃ q : IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K),
    (fun w => q.out * ((finEmb K w : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K)) '' intUnits K

theorem isCompact_bigT : IsCompact (bigT K) := by
  have : Finite (IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K)) :=
    Subgroup.finite_quotient_of_finiteIndex
  refine isCompact_iUnion fun q => (isCompact_intUnits K).image ?_
  have hmk : Continuous (QuotientGroup.mk : IdeleGroup (𝓞 K) K → IdeleClassGroup (𝓞 K) K) :=
    QuotientGroup.continuous_mk
  exact continuous_const.mul (hmk.comp (continuous_finEmb K))

theorem range_absArt_eq (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) :
    Set.range (absArt K) = absArt K '' bigT K := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨c, rfl⟩
  set q : IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K) := QuotientGroup.mk c
  obtain ⟨⟨h, hh⟩, hq⟩ := QuotientGroup.mk_out_eq_mul (raySubgroup (Modulus.one K)) c
  -- `c = q̄ · h⁻¹` with `h⁻¹` a ray class
  have hc : c = q.out * h⁻¹ := by rw [hq, mul_inv_cancel_right]
  obtain ⟨x, hx, hxc⟩ := mem_raySubgroup_iff.1 (inv_mem hh)
  rw [mem_ideleCongruenceSubgroup_iff] at hx
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
    intro v
    refine hx.1 v ?_
    intro hdvd
    have : (Modulus.one K).finitePart = ⊤ := rfl
    rw [this, Ideal.dvd_iff_le, top_le_iff] at hdvd
    exact v.isPrime.ne_top hdvd
  set xf := IdeleGroup.toFiniteIdele (𝓞 K) K x
  have hcoord : ∀ v : HeightOneSpectrum (𝓞 K),
      ((xf : FiniteAdeleRing (𝓞 K) K) v) = (v.ideleFiniteCoord x : v.adicCompletion K) := fun v => rfl
  have hcoordi : ∀ v : HeightOneSpectrum (𝓞 K),
      ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v =
        ((v.ideleFiniteCoord x)⁻¹ : (v.adicCompletion K)ˣ) := fun v => rfl
  have hxf : xf ∈ intUnits K := by
    refine ⟨fun v => ?_, fun v => ?_⟩
    · rw [hcoord, HeightOneSpectrum.mem_adicCompletionIntegers, hv1 v]
    · rw [hcoordi, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀,
        hv1 v, inv_one]
  set y := (finEmb K xf)⁻¹ * x
  have hy : ∀ v : HeightOneSpectrum (𝓞 K), v.ideleFiniteCoord y = 1 := by
    intro v
    apply Units.ext
    show ((finEmb K xf)⁻¹ * x : IdeleGroup (𝓞 K) K).val.2 v = 1
    rw [Units.val_mul, Prod.snd_mul]
    show ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v * (x.val.2 v) = 1
    have e1 : ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) * xf = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v *
        (xf : FiniteAdeleRing (𝓞 K) K) v = 1 := by
      rw [← FiniteAdeleRing.mul_apply, e1, FiniteAdeleRing.one_apply]
    exact e2
  have hxy : x = finEmb K xf * y := by rw [mul_inv_cancel_left]
  refine ⟨q.out * ((finEmb K xf : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K),
    Set.mem_iUnion.2 ⟨q, xf, hxf, rfl⟩, ?_⟩
  rw [hc, ← hxc, QuotientGroup.mk'_apply, hxy, QuotientGroup.mk_mul, map_mul, map_mul, map_mul,
    absArt_eq_one_of_coord K hK y hy, mul_one]

/-- **`AbsArtinSurjective K` for number fields without real places.** -/
theorem absArtinSurjective_of_noReal (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) :
    AbsArtinSurjective K := by
  have hclosed : IsClosed (Set.range (absArt K)) := by
    rw [range_absArt_eq K hK]
    exact ((isCompact_bigT K).image (continuous_absArt K)).isClosed
  intro g
  have hg : (g : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) ∈ Set.range (absArt K) := by
    rw [← hclosed.closure_eq]
    exact denseRange_absArt K _
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, by rw [← ofMul_absArt, hc]⟩

end AbsArtin


/-- `ℚ(√−m)` has no real places. -/
theorem not_isReal_QNeg (m : ℕ) [NeZero m] (w : InfinitePlace (QNeg m)) : ¬ w.IsReal := by
  intro hw
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hw
  set φ := w.embedding
  have h1 : φ QuadraticAlgebra.omega ^ 2 = -(m : ℂ) := by
    rw [← map_pow, omega_sq', map_neg, map_natCast]
  have h2 : (starRingEnd ℂ) (φ QuadraticAlgebra.omega) = φ QuadraticAlgebra.omega := by
    have := congrArg (fun ψ : QNeg m →+* ℂ => ψ QuadraticAlgebra.omega) hw
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  have him : (φ QuadraticAlgebra.omega).im = 0 := Complex.conj_eq_iff_im.1 h2
  have hre := congrArg Complex.re h1
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  simp only [sq, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  nlinarith [sq_nonneg (φ QuadraticAlgebra.omega).re]

end T5Glue

namespace ShimuraCFT

open NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

/-- `σ ∈ Aut(ℂ)` fixing `κ(K)` acts on `e(Kˢ)` through some `τ ∈ Gal(Kˢ/K)`, for a `K`-embedding
`e : Kˢ → ℂ` (generalizes t5-glue's `exists_tau_of_sigma`). -/
theorem exists_tau (κ : K →+* ℂ) (e : SeparableClosure K →+* ℂ)
    (he : e.comp (algebraMap K (SeparableClosure K)) = κ) (σ : ℂ ≃+* ℂ)
    (hσ : ∀ k : K, σ (κ k) = κ k) :
    ∃ τ : TauCeti.AbsoluteGaloisGroup K, ∀ x, σ (e x) = e (τ x) := by
  set Ks := SeparableClosure K
  have hεinj : Function.Injective e := e.injective
  letI : Algebra Ks ℂ := e.toAlgebra
  have halgK : Algebra.IsAlgebraic ℚ Ks := Algebra.IsAlgebraic.trans ℚ K Ks
  have hrange : ∀ z : ℂ, IsAlgebraic ℚ z → ∃ y : Ks, e y = z := by
    intro z hz
    have hz' : IsAlgebraic Ks z := hz.extendScalars (algebraMap ℚ Ks).injective
    obtain ⟨y, hy⟩ := T5Glue.mem_range_of_isAlgebraic hz'
    exact ⟨y, hy⟩
  have halg : ∀ (φ : ℂ ≃+* ℂ) (x : Ks), IsAlgebraic ℚ (φ (e x)) := by
    intro φ x
    have h1 : IsAlgebraic ℚ (e x) := (halgK.isAlgebraic x).algHom (e.toRatAlgHom)
    exact h1.algHom ((φ : ℂ →+* ℂ).toRatAlgHom)
  choose τf hτf using fun x => hrange (σ (e x)) (halg σ x)
  choose τi hτi using fun x => hrange (σ.symm (e x)) (halg σ.symm x)
  have hK : ∀ k : K, e (algebraMap K Ks k) = κ k := fun k => by rw [← he]; rfl
  let τh : Ks →ₐ[K] Ks :=
    { toFun := τf
      map_one' := hεinj (by simp [hτf])
      map_mul' := fun x y => hεinj (by rw [hτf, map_mul, map_mul, map_mul, hτf, hτf])
      map_zero' := hεinj (by simp [hτf])
      map_add' := fun x y => hεinj (by rw [hτf, map_add, map_add, map_add, hτf, hτf])
      commutes' := fun k => hεinj (by
        show e (τf (algebraMap K Ks k)) = e (algebraMap K Ks k)
        rw [hτf, hK, hσ]) }
  have hbij : Function.Bijective τh := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨τi y, ?_⟩⟩
    · have h := congrArg e hxy
      change e (τf x) = e (τf y) at h
      rw [hτf, hτf] at h
      exact hεinj (σ.injective h)
    · apply hεinj
      change e (τf (τi y)) = e y
      rw [hτf, hτi, RingEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofBijective τh hbij, fun x => ?_⟩
  show σ (e x) = e (τf x)
  rw [hτf]

/-- A `K`-embedding `j : L → ℂ` of a finite extension factors through `e : Kˢ → ℂ`. -/
theorem exists_iota (κ : K →+* ℂ) (e : SeparableClosure K →+* ℂ)
    (he : e.comp (algebraMap K (SeparableClosure K)) = κ)
    (L : Type) [Field L] [NumberField L] [Algebra K L] (j : L →+* ℂ)
    (hj : j.comp (algebraMap K L) = κ) :
    ∃ ι : L →ₐ[K] SeparableClosure K, ∀ x, e (ι x) = j x := by
  set Ks := SeparableClosure K
  have hεinj : Function.Injective e := e.injective
  letI : Algebra Ks ℂ := e.toAlgebra
  have hrange : ∀ z : ℂ, IsAlgebraic ℚ z → ∃ y : Ks, e y = z := by
    intro z hz
    have hz' : IsAlgebraic Ks z := hz.extendScalars (algebraMap ℚ Ks).injective
    obtain ⟨y, hy⟩ := T5Glue.mem_range_of_isAlgebraic hz'
    exact ⟨y, hy⟩
  have halg : ∀ x : L, IsAlgebraic ℚ (j x) := fun x =>
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).algHom (j.toRatAlgHom)
  choose ιf hιf using fun x => hrange (j x) (halg x)
  have hK : ∀ k : K, e (algebraMap K Ks k) = κ k := fun k => by rw [← he]; rfl
  have hK' : ∀ k : K, j (algebraMap K L k) = κ k := fun k => by rw [← hj]; rfl
  refine ⟨{ toFun := ιf
            map_one' := hεinj (by simp [hιf])
            map_mul' := fun x y => hεinj (by rw [hιf, map_mul, map_mul, hιf, hιf])
            map_zero' := hεinj (by simp [hιf])
            map_add' := fun x y => hεinj (by rw [hιf, map_add, map_add, hιf, hιf])
            commutes' := fun k => hεinj (by
              show e (ιf (algebraMap K L k)) = e (algebraMap K Ks k)
              rw [hιf, hK, hK']) }, fun x => hιf x⟩

open scoped IsMulCommutative in
/-- **Every `σ ∈ Aut(ℂ)` fixing `κ(K)` is `[s, K]` on `K^ab`** (`ArtinCondC`), when Tau Ceti's absolute
Artin map of `K` is surjective. -/
theorem exists_artinCondC_of_abs (hA : T5Glue.AbsArtinSurjective K) (κ : K →+* ℂ) (σ : ℂ ≃+* ℂ)
    (hσ : ∀ k : K, σ (κ k) = κ k) : ∃ s : IdeleGroup (𝓞 K) K, ArtinCondC κ σ s := by
  letI : Algebra K ℂ := κ.toAlgebra
  let e : SeparableClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have he : (e : SeparableClosure K →+* ℂ).comp (algebraMap K (SeparableClosure K)) = κ := by
    ext k; exact e.commutes k
  obtain ⟨τ, hτ⟩ := exists_tau κ (e : SeparableClosure K →+* ℂ) he σ hσ
  obtain ⟨c, hc⟩ := hA τ
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨s, ?_⟩
  intro L _ _ _ _ j hj x
  obtain ⟨ι, hι⟩ := exists_iota κ (e : SeparableClosure K →+* ℂ) he L j hj
  have h1 := of_ideleClassArtinMap K L ι (QuotientGroup.mk s)
  have h0 := globalArtinMap_eq_of_mk_eq_absoluteArtinMap K L ι τ hc
  have h3 : Abelianization.of (ideleClassArtinMap K L (QuotientGroup.mk s)) =
      Abelianization.of (ι.restrictNormalHom τ) := by
    rw [h1, h0, toMul_ofMul]
  have h2 : ideleClassArtinMap K L (QuotientGroup.mk s) = ι.restrictNormalHom τ :=
    (Abelianization.equivOfComm (H := Gal(L/K))).injective h3
  rw [h2, ← hι, ← hι, AlgHom.restrictNormalHom_commutes]
  exact hτ (ι x)

/-- **Every `σ ∈ Aut(ℂ)` fixing `κ(K)` is `[s, K]` on `K^ab`** for `K` totally complex (in particular
imaginary quadratic), from t5-glue's proved surjectivity of the absolute Artin map. -/
theorem exists_artinCondC [IsTotallyComplex K] (κ : K →+* ℂ) (σ : ℂ ≃+* ℂ)
    (hσ : ∀ k : K, σ (κ k) = κ k) : ∃ s : IdeleGroup (𝓞 K) K, ArtinCondC κ σ s :=
  exists_artinCondC_of_abs (T5Glue.absArtinSurjective_of_noReal K fun w hw =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)) hw) κ σ hσ

end ShimuraCFT

#print axioms ShimuraCFT.exists_artinCondC

/-! # Part D: the hypotheses of the reciprocity clause can be met (for either value of `δ`)

`K = ℚ(√−3)` (the kernel's `QNeg 3`), `q : √−3 ↦ j` (`j² = −3` in `B = (2, −3)`), `κ : √−3 ↦ i√3`, and
`z = i√3`, the fixed point of `ι(j) = [[0, −3], [1, 0]]`. -/

noncomputable section

namespace ShimuraCFT

open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura Complex NumberField

/-- `j ∈ B` as a root of `X² + 3`. -/
def jRoot : {u : LeafQM.B // u * u = (-((3 : ℕ) : ℚ)) • (1 : LeafQM.B) + (0 : ℚ) • u} :=
  ⟨⟨0, 0, 1, 0⟩, by ext <;> simp⟩

/-- `q : ℚ(√−3) → B`, `√−3 ↦ j`. -/
def q3 : QNeg 3 →ₐ[ℚ] LeafQM.B := QuadraticAlgebra.lift jRoot

theorem q3_apply (a : QNeg 3) : q3 a = ⟨a.re, 0, a.im, 0⟩ := by
  ext <;> simp [q3, jRoot, Rat.smul_def]

/-- `z₃ = i√3 ∈ ℍ`. -/
def z3 : UpperHalfPlane := ⟨I * Real.sqrt 3, by simp⟩

theorem sq_I_sqrt3 : (I * (Real.sqrt 3 : ℂ)) * (I * Real.sqrt 3) = -3 := by
  have := sqrt_mul_self_C 3
  push_cast at this
  rw [show I * (Real.sqrt 3 : ℂ) * (I * Real.sqrt 3) = (I * I) * (Real.sqrt 3 * Real.sqrt 3) by ring,
    I_mul_I, this]; ring

/-- **`z₃` is the CM point of `q₃` with reflex embedding `κ = kappaAlg 3`.** -/
theorem isCMPoint_q3 : IsCMPoint q3 ((kappaAlg 3 : QNeg 3 →ₐ[ℚ] ℂ) : QNeg 3 →+* ℂ) z3 := by
  intro a
  have h := sq_I_sqrt3
  rw [q3_apply]
  ext i
  fin_cases i
  · simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, z3, kappaAlg_apply, kappa]
    linear_combination (-(↑a.im : ℂ)) * h
  · simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, z3, kappaAlg_apply, kappa]
    linear_combination (0 : ℂ) * h

instance : IsTotallyComplex (QNeg 3) :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 (T5Glue.not_isReal_QNeg 3 w)⟩

/-- **The reciprocity clause is not vacuous**: for either value of `δ` there is an imaginary
quadratic `K`, `κ`, `q` and a CM point `z` meeting its hypothesis, and every `σ ∈ Aut(ℂ)` fixing
`κ(K)` is `[s, K]` on `K^ab` for some idele `s`. -/
theorem recip_hyp_nonempty (δ : Bool) :
    ∃ (κ : QNeg 3 →+* ℂ) (q : QNeg 3 →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
      Module.finrank ℚ (QNeg 3) = 2 ∧
      IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z ∧
      ∀ σ : ℂ ≃+* ℂ, (∀ k, σ (κ k) = κ k) → ∃ s : IdeleGroup (𝓞 (QNeg 3)) (QNeg 3),
        ArtinCondC κ σ s := by
  refine ⟨if δ then (kappaAlg 3 : QNeg 3 →+* ℂ) else (starRingEnd ℂ).comp (kappaAlg 3 : QNeg 3 →+* ℂ),
    q3, z3, QuadraticAlgebra.finrank_eq_two _ _, ?_, fun σ hσ => exists_artinCondC _ σ hσ⟩
  cases δ
  · simp only [Bool.false_eq_true, if_false]
    have : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp (kappaAlg 3 : QNeg 3 →+* ℂ)) =
        (kappaAlg 3 : QNeg 3 →+* ℂ) := by ext x; simp
    rw [this]; exact isCMPoint_q3
  · simpa using isCMPoint_q3

end ShimuraCFT

#print axioms ShimuraCFT.recip_hyp_nonempty
