import ZInQKernel.Contrib.OneProof.H.TailZ15
import ZInQKernel.Contrib.HDecomp.QM.Leaves
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.FrobChain.Rigidity

/-! # OneProof H, route-a-fold: Mumford's rigidity and the abelian-scheme moduli clauses

r1univ-rigid's `R1UnivRigid.lean` (docs/research/r1univ-rigid.md), verbatim below its imports: the leaf
`LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (Mumford, GIT Thm 6.14 with Cor. 6.4 over a base; numbers UNVERIFIED),
the published fine-moduli objects `QMAbScheme S` (an abelian scheme with `𝒪 → End_S` and level 3) and clauses
`R1univAbProps`, `R1famAbProps`, `R1fpPropsAb`, and the proofs `mumfordRigidity_of_core`, `r1univProps_of_core_ab`,
`r1fpProps_iff_ab_core`. Everything is in the kernel-side namespace `LeafQM.AV.R1UnivRigid` (no `HDec` copy) and
uses the kernel's `LeafQM.AV.R1univProps`, `R1famProps`, `R1fpProps` (ZInQKernel/Contrib/HDecomp/QM/Leaves.lean). The fold
itself (route A for `R1univProps`) is `TailZ17`. -/

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
