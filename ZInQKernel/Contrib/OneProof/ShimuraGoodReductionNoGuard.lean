import ZInQKernel.OneProof.H.TailW
import ZInQKernel.OneProof.H.TailZ16
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import ZInQKernel.Contrib.AbVarBC.Main

/-!
# sgr-split: `ShimuraGoodReductionNoGuard` from the printed integral model of the Shimura curve

`HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` (field `shimuraGoodReductionNoGuard` of the added bundle,
`ZInQKernel/OneProof/H/TailW.lean`) asserts, for every prime `p > 324`, a proper smooth curve `𝒴/ℤ_(p)` with a
`QMFamily` `𝒜 → 𝒴` whose field fibres are the objects `QML3`, bijective on `ℚ̄`-points onto their classes, with
the Hecke automorphisms for `Aut 𝒪` and `𝒪^×`. curve-split (docs/research/curve-split.md §3.6) found the printed
source (representability of the integral moduli problem) not statable for want of abelian schemes over a base.
The kernel now has them: r1univ-rigid's `LeafQM.AV.R1UnivRigid.QMAbScheme S` (an abelian scheme over `S` with
`𝒪 → End_S` and level 3). Over it the printed theorem is stated here as `ShimuraIntegralModelRep`, and

* `shimuraGoodReductionNoGuard_of_rep : ShimuraIntegralModelRep → QMAbFieldFibre → QML3AsQMAb →
  FibreClassUnique → ShimuraGoodReductionNoGuard` (the clause-by-clause glue: Yoneda for the Hecke clauses,
  uniqueness for injectivity, existence for surjectivity);
* `fibreClassUnique : FibreClassUnique` (proved: the pullback isomorphism of two fibres is a homomorphism by
  the kernel's `G0FibreSimple.rigidityHom`);
* `qml3AsQMAb_of : AbVarSurfaceRelDim → QML3AsQMAb` (proved: an object over a field is a `QMAbScheme` over
  `Spec K` with the same data) and `abVarSurfaceRelDim : AbVarSurfaceRelDim` (proved from the kernel's smooth
  dimension theory: an abelian surface is smooth of relative dimension 2);
* `qmAbFieldFibre : QMAbFieldFibre` (proved: the fibre of a `QMAbScheme` at a field point of characteristic 0,
  with its `𝒪`-action and level points, is an object `QML3`), from `smoothGeomConnIntegral` (a smooth
  geometrically connected scheme over a field is geometrically integral) and `abVarEndTorsionFree` (`End` of an
  abelian variety is torsion-free in characteristic 0), both proved from the kernel;
* `shimuraGoodReductionNoGuard_of_printed : ShimuraIntegralModelRep → ShimuraGoodReductionNoGuard`, the
  discharge.

The only new hypothesis is the printed leaf `ShimuraIntegralModelRep` (Kottwitz/Buzzard/Morita). Report:
docs/research/sgr-split.md.
-/

noncomputable section

namespace SGRSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid HDec.VertWitness HDec.CurveSplitGR

/-- **`𝒜'` is the pullback of `𝒜` along `g`, with its `𝒪`-action and level sections**: a morphism
`h : 𝒜' → 𝒜` making `𝒜' → S` the base change of `𝒜 → T` along `g`, carrying `ι'(a)` to `ι(a)` and
`η'(a)` to `η(a)`; i.e. an isomorphism `𝒜' ≅ g^*𝒜` of the data (the relative form of the kernel's
`IsFibreOf`). For `QMAbScheme`s such an isomorphism carries the identity `η'(0)` to `η(0)`, so it is an
isomorphism of abelian schemes (Mumford, *GIT*, Cor. 6.4; number UNVERIFIED): this is the isomorphism relation
of the moduli problem. -/
def QMFamFibre {S T : Scheme.{0}} (𝒜 : QMFamily T) (g : S ⟶ T) (𝒜' : QMFamily S) : Prop :=
  ∃ h : 𝒜'.F.left ⟶ 𝒜.F.left, IsPullback h 𝒜'.F.hom 𝒜.F.hom g ∧
    (∀ a : O, 𝒜'.iota a ≫ h = h ≫ 𝒜.iota a) ∧ (∀ a : O, 𝒜'.eta a ≫ h = g ≫ 𝒜.eta a)

/-- The assertion of `ShimuraIntegralModelRep` at one prime `p`: a proper smooth curve `𝒴/ℤ_(p)` with a
`QMAbScheme` `𝒜` over it that represents the moduli problem on locally noetherian `ℤ_(p)`-schemes. -/
def ShimuraIntegralModelRepAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMAbScheme 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of (Zloc p)))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbScheme S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

/-- **LEAF (printed form; pending reading): the integral model of the level-3 Shimura curve of
discriminant 6.** For each prime `p > 324` the moduli problem `S ↦ {(A, ι, η)}/≅` on locally noetherian
`ℤ_(p)`-schemes `S` (in universe 0) is representable by a proper smooth curve `𝒴/ℤ_(p)`: there is a universal
`𝒜 : QMAbScheme 𝒴` such that every object `𝒜'` over `S` is the pullback of `𝒜` along exactly one
`ℤ_(p)`-morphism `S → 𝒴`. Here `(A, ι, η)` is the kernel's `QMAbScheme S`: `A/S` an abelian scheme of relative
dimension 2 (proper, smooth, geometrically connected, a group object of `Over S`), `ι : 𝒪 → End_S(A)` a unital
ring homomorphism for the maximal order `𝒪` of `B = (2, −3)` (discriminant 6), and `η : 𝒪 → A(S)` an
`𝒪`-linear map killing `3𝒪` and injective mod `3𝒪` on every field fibre.

*Printed sources* (all locators UNVERIFIED; no network; docs/research/locators.md row R1 for Kottwitz):
- R. Kottwitz, *Points on some Shimura varieties over finite fields*, J. AMS 5 (1992), 373–444, §5: the PEL
  moduli problem with neat `K^p` and hyperspecial `K_p` is representable by a smooth quasi-projective scheme over
  `𝒪_E ⊗ ℤ_(p)`, proper when `B` is a division algebra. Here `E = ℚ`, `K_p = 𝒪_p^× ≅ GL₂(ℤ_p)` for `p ∤ 6`,
  `K^p = K₃ × ∏_{ℓ ≠ 3, p} 𝒪_ℓ^×` (full level 3, neat), which covers the level at `3 ∣ D` since `3 ≠ p`.
- K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), 591–612, §1–§4: the
  polarization-free moduli problem of abelian surfaces with `𝒪`-action and level structure, representable by
  a smooth proper curve over `ℤ[1/(D·level)]`.
- Y. Morita, *Reduction modulo 𝔓 of Shimura curves*, Hokkaido Math. J. 10 (1981), 209–238: good reduction of
  the Shimura curve and its universal QM abelian surfaces at `p ∤ D·level`.
- H. Carayol, *Sur la mauvaise réduction des courbes de Shimura*, Compositio Math. 59 (1986), 151–230 (its
  main construction is for totally real `F ≠ ℚ`; secondary).

*Form.* The printed functor has, in Kottwitz's PEL form, a polarization and rational level structures; it is
identified with this one by (i) the relative Lemma P (for the fixed Rosati type the principal polarization of
`(A, ι)` exists and is unique; Boutot–Carayol, Astérisque 196–197 (1991), III §1, UNVERIFIED), (ii) the standard
comparison of `K^p`-orbits of rational level structures with integral ones, (iii) `η` with `eta_three` and
`eta_ker` is the same as an `𝒪`-linear isomorphism `(𝒪/3𝒪)_S ≅ A[3]` because `3` is invertible on `S` (a
fibrewise injective map of finite étale group schemes of the same degree 81 is an isomorphism), (iv) Kottwitz's
determinant condition is automatic for `𝒪 ⊗ ℤ_p ≅ M₂(ℤ_p)`, (v) `QMFamFibre` is the isomorphism relation
(see its docstring). Only `p > 324` is asserted (the printed range is `p ∤ 6`), only locally noetherian `S` in
universe 0. Flagged pending reading: whether Buzzard's or Morita's printed level structures include a prime
dividing `D` (Kottwitz's do), and the comparison (i)–(ii) for the PEL form. -/
def ShimuraIntegralModelRep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraIntegralModelRepAt p

/-- **GLUE G1: the fibre of a QM abelian scheme at a field point is an object.** For a `QMAbScheme` `𝒜` over
any `S` and a point `y : Spec K → S` with `K ⊇ ℚ`, some `P : QML3 K` is the fibre of `𝒜` at `y`. Proved
(`qmAbFieldFibre`): the base change `A_y` with Mathlib's `Functor.grpObjObj` group law is an abelian variety of
dimension 2, `ι` and `η` push forward along the monoidal functor `Over.pullback y`, and `ι` stays injective
because `End(A_y)` is torsion-free. -/
def QMAbFieldFibre : Prop :=
  ∀ (S : Scheme.{0}) (𝒜 : QMAbScheme S) (K : Type) [Field K] [Algebra ℚ K]
    (y : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K, IsFibreOf 𝒜.toQMFamily y P

/-- **GLUE G2: an object over a field is a `QMAbScheme` over `Spec K` with the same data** (so `IsFibreOf`
at `y` is `QMFamFibre` along `y`). Proved from `AbVarSurfaceRelDim` (`qml3AsQMAb_of`). -/
def QML3AsQMAb : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (P : QML3 K), ∃ 𝒜' : QMAbScheme (Spec (CommRingCat.of K)),
    ∀ (T : Scheme.{0}) (𝒜 : QMFamily T) (y : Spec (CommRingCat.of K) ⟶ T),
      IsFibreOf 𝒜 y P ↔ QMFamFibre 𝒜 y 𝒜'.toQMFamily

/-- **GLUE G3: fibres are unique up to isomorphism**: two objects that are fibres of the same family at the
same field point are isomorphic. Proved (`fibreClassUnique`). -/
def FibreClassUnique : Prop :=
  ∀ (S : Scheme.{0}) (𝒜 : QMFamily S) (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ S)
    (P P' : QML3 K), IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P'

/-! ## Lemmas -/

/-- Morphisms `Spec R → Spec ℤ_(p)` are unique. -/
theorem spec_to_Zloc_ext (p : ℕ) [Fact p.Prime] {R : CommRingCat.{0}}
    (f g : Spec R ⟶ Spec (CommRingCat.of (Zloc p))) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (pIdeal p).primeCompl (RingHom.ext_int _ _)

/-- The ring map `ℤ_(p) → K` to a field of characteristic `0`. -/
def zlocTo (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] : Zloc p →+* K :=
  IsLocalization.lift (M := (pIdeal p).primeCompl) (g := Int.castRingHom K) (fun x => by
    have hx : (x : ℤ) ≠ 0 := fun h => x.2 (by rw [h]; exact Ideal.zero_mem _)
    exact isUnit_iff_ne_zero.2 (by simpa using hx))

/-- Fibres are invariant under isomorphism of objects. -/
theorem isFibreOf_of_iso {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    {y : Spec (CommRingCat.of K) ⟶ S} {P P' : QML3 K} (f : P.Iso P') (h : IsFibreOf 𝒜 y P') :
    IsFibreOf 𝒜 y P := by
  obtain ⟨k, hpb, hι, he⟩ := h
  have hiso : IsIso f.φ.hom.left := ⟨f.ψ.hom.left, by rw [← Over.comp_left, f.left]; rfl,
    by rw [← Over.comp_left, f.right]; rfl⟩
  have sq : IsPullback f.φ.hom.left P.A.X.hom P'.A.X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨f.φ.hom.left ≫ k, by simpa using sq.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
  · have := congrArg CommaMorphism.left (f.equivariant a)
    simp only [Over.comp_left] at this
    simp only [Category.assoc]
    rw [reassoc_of% this, hι]
  · have hl := congrArg Additive.toMul (f.level a)
    simp only [toMul_ofMul] at hl
    rw [← he a, ← hl, Over.comp_left, Category.assoc]


/-! ## Hecke relabelings of a QM abelian scheme -/

/-- `ι ↦ ι ∘ α`, `η ↦ η ∘ α` on a `QMAbScheme`. -/
def twistAb {S : Scheme.{0}} (𝒜 : QMAbScheme S) (α : O ≃+* O) : QMAbScheme S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota (α a)
  iota_over a := 𝒜.iota_over (α a)
  eta a := 𝒜.eta (α a)
  eta_sec a := 𝒜.eta_sec (α a)
  grp := 𝒜.grp
  geomConn := 𝒜.geomConn
  one_eq := by rw [map_zero]; exact 𝒜.one_eq
  iota_hom a := 𝒜.iota_hom (α a)
  iota_one := by simp only [map_one]; exact 𝒜.iota_one
  iota_mul a b := by simp only [map_mul]; exact 𝒜.iota_mul _ _
  iota_add a b := by
    have h := 𝒜.iota_add (α a) (α b)
    rw [← map_add] at h
    exact h
  eta_add a b := by
    have h := 𝒜.eta_add (α a) (α b)
    rw [← map_add] at h
    exact h
  eta_linear a b := by simp only [map_mul]; exact 𝒜.eta_linear _ _
  eta_three b := by
    simp only [map_mul, map_ofNat, map_zero]
    exact 𝒜.eta_three _
  eta_ker K _ s a := by
    simp only [map_zero]
    rw [𝒜.eta_ker K s (α a)]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨α.symm c, by
        apply α.injective
        rw [hc, map_mul, RingEquiv.apply_symm_apply, map_ofNat]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨α c, by rw [map_mul, map_ofNat]⟩

/-- `η ↦ η(· u)` on a `QMAbScheme`. -/
def rightMulAb {S : Scheme.{0}} (𝒜 : QMAbScheme S) (u : Oˣ) : QMAbScheme S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota := 𝒜.iota
  iota_over := 𝒜.iota_over
  eta a := 𝒜.eta (a * u)
  eta_sec a := 𝒜.eta_sec (a * u)
  grp := 𝒜.grp
  geomConn := 𝒜.geomConn
  one_eq := by rw [zero_mul]; exact 𝒜.one_eq
  iota_hom := 𝒜.iota_hom
  iota_one := 𝒜.iota_one
  iota_mul := 𝒜.iota_mul
  iota_add := 𝒜.iota_add
  eta_add a b := by
    have h := 𝒜.eta_add (a * u) (b * u)
    rw [← add_mul] at h
    exact h
  eta_linear a b := by rw [_root_.mul_assoc]; exact 𝒜.eta_linear _ _
  eta_three b := by rw [_root_.mul_assoc, zero_mul]; exact 𝒜.eta_three _
  eta_ker K _ s a := by
    rw [zero_mul, 𝒜.eta_ker K s (a * u)]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c * ↑u⁻¹, by
        rw [← _root_.mul_assoc, ← hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * u, by rw [_root_.mul_assoc]⟩

/-- Identity pullback. -/
theorem qmFamFibre_id {S : Scheme.{0}} (𝒜 : QMFamily S) : QMFamFibre 𝒜 (𝟙 S) 𝒜 :=
  ⟨𝟙 _, IsPullback.of_horiz_isIso ⟨by simp⟩, fun a => by simp, fun a => by simp⟩

/-- Composition of relabeled pullbacks. -/
theorem qmFamFibre_comp {S : Scheme.{0}} (𝒜 : QMAbScheme S) (i j i' j' : O → O)
    (g g' : S ⟶ S) (h h' : 𝒜.F.left ⟶ 𝒜.F.left)
    (hpb : IsPullback h 𝒜.F.hom 𝒜.F.hom g) (hpb' : IsPullback h' 𝒜.F.hom 𝒜.F.hom g')
    (hi : ∀ a, 𝒜.iota (i a) ≫ h = h ≫ 𝒜.iota a) (he : ∀ a, 𝒜.eta (j a) ≫ h = g ≫ 𝒜.eta a)
    (hi' : ∀ a, 𝒜.iota (i' a) ≫ h' = h' ≫ 𝒜.iota a) (he' : ∀ a, 𝒜.eta (j' a) ≫ h' = g' ≫ 𝒜.eta a)
    (hii : ∀ a, i (i' a) = a) (hjj : ∀ a, j (j' a) = a) :
    QMFamFibre 𝒜.toQMFamily (g ≫ g') 𝒜.toQMFamily := by
  refine ⟨h ≫ h', hpb.paste_horiz hpb', fun a => ?_, fun a => ?_⟩
  · have := hi (i' a)
    rw [hii] at this
    rw [reassoc_of% this, hi', Category.assoc]
  · have := he (j' a)
    rw [hjj] at this
    rw [reassoc_of% this, he', Category.assoc]


instance zloc_noetherian (p : ℕ) [Fact p.Prime] : IsNoetherianRing (Zloc p) :=
  IsLocalization.isNoetherianRing (pIdeal p).primeCompl _ inferInstance

theorem isLocallyNoetherian_of_smooth (p : ℕ) [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (hsm : SmoothOfRelativeDimension 1 𝒴.hom) :
    IsLocallyNoetherian 𝒴.left := by
  have : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 _
  exact LocallyOfFiniteType.isLocallyNoetherian 𝒴.hom

theorem paste_iota {X Y Z : Scheme.{0}} (e : X ⟶ X) (k : X ⟶ Y) (h : Y ⟶ Z) (ι : Y ⟶ Y)
    (ι' : Z ⟶ Z) (h1 : e ≫ k = k ≫ ι) (h2 : ι ≫ h = h ≫ ι') : e ≫ k ≫ h = (k ≫ h) ≫ ι' := by
  rw [reassoc_of% h1, h2, Category.assoc]

theorem paste_eta {X S Y Z W : Scheme.{0}} (e : X ⟶ Y) (k : Y ⟶ Z) (h : Z ⟶ W) (y : X ⟶ S)
    (η : S ⟶ Z) (g : S ⟶ S') (η' : S' ⟶ W) (h1 : e ≫ k = y ≫ η) (h2 : η ≫ h = g ≫ η') :
    e ≫ k ≫ h = (y ≫ g) ≫ η' := by
  rw [reassoc_of% h1, h2, Category.assoc]

/-! ## The reduction -/

/-- **`ShimuraGoodReductionNoGuard` from the printed representability and three pieces of glue**. -/
theorem shimuraGoodReductionNoGuard_of_rep (hRep : ShimuraIntegralModelRep)
    (g1 : QMAbFieldFibre) (g2 : QML3AsQMAb) (g3 : FibreClassUnique) :
    ShimuraGoodReductionNoGuard := by
  intro p _ hp
  obtain ⟨𝒴, 𝒜, hpr, hsm, hU⟩ := hRep p hp
  have hN := isLocallyNoetherian_of_smooth p 𝒴 hsm
  -- the Hecke automorphism attached to a relabeling with an inverse relabeling
  have hecke : ∀ (𝒜₁ 𝒜₂ : QMAbScheme 𝒴.left) (i j i' j' : O → O),
      𝒜₁.F = 𝒜.F → 𝒜₂.F = 𝒜.F → True := fun _ _ _ _ _ _ _ _ => trivial
  clear hecke
  refine ⟨𝒴, 𝒜.toQMFamily, hpr, hsm, fun K _ _ y => g1 _ 𝒜 K y, ?_, ?_, ?_, ?_⟩
  · -- injectivity on `ℚ̄`-points
    intro y y' P P' hP hP' hPP'
    obtain ⟨𝒜P, h𝒜P⟩ := g2 Qbar P
    obtain ⟨f⟩ := Quotient.exact hPP'
    have hP'' : IsFibreOf 𝒜.toQMFamily y' P := isFibreOf_of_iso _ f hP'
    have hyy : y' ≫ 𝒴.hom = y ≫ 𝒴.hom := spec_to_Zloc_ext p _ _
    obtain ⟨g, -, hg⟩ := hU (Over.mk (y ≫ 𝒴.hom)) (by dsimp; infer_instance) 𝒜P
    have e1 := hg (Over.homMk y rfl) ((h𝒜P _ _ y).mp hP)
    have e2 := hg (Over.homMk y' hyy) ((h𝒜P _ _ y').mp hP'')
    have := congrArg CommaMorphism.left (e1.trans e2.symm)
    simpa using this
  · -- surjectivity on `ℚ̄`-points
    intro P
    obtain ⟨𝒜P, h𝒜P⟩ := g2 Qbar P
    obtain ⟨g, hg, -⟩ := hU (Over.mk (Spec.map (CommRingCat.ofHom (zlocTo p Qbar))))
      (by dsimp; infer_instance) 𝒜P
    exact ⟨g.left, (h𝒜P _ _ g.left).mpr hg⟩
  · -- `Aut(𝒪)`
    intro α
    obtain ⟨g, ⟨h, hpb, hi, he⟩, -⟩ := hU 𝒴 hN (twistAb 𝒜 α)
    obtain ⟨g', ⟨h', hpb', hi', he'⟩, -⟩ := hU 𝒴 hN (twistAb 𝒜 α.symm)
    obtain ⟨g0, -, h0⟩ := hU 𝒴 hN 𝒜
    have hid : QMFamFibre 𝒜.toQMFamily (CommaMorphism.left (𝟙 𝒴)) 𝒜.toQMFamily :=
      qmFamFibre_id _
    have c1 : g ≫ g' = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a => α a) (fun a => α a) (fun a => α.symm a) (fun a => α.symm a)
        g.left g'.left h h' hpb hpb' hi he hi' he' (fun a => by simp) (fun a => by simp)
    have c2 : g' ≫ g = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a => α.symm a) (fun a => α.symm a) (fun a => α a) (fun a => α a)
        g'.left g.left h' h hpb' hpb hi' he' hi he (fun a => by simp) (fun a => by simp)
    refine ⟨⟨g, g', c1, c2⟩, fun y P P' hP hP' => ?_⟩
    rw [M3.twist_mk]
    refine g3 _ _ _ _ _ _ hP' ?_
    obtain ⟨k, hkpb, hki, hke⟩ := hP
    refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
    · exact paste_iota _ _ _ _ _ (hki (α a)) (hi a)
    · exact paste_eta _ _ _ _ _ _ _ (hke (α a)) (he a)
  · -- `𝒪^×`
    intro u
    obtain ⟨g, ⟨h, hpb, hi, he⟩, -⟩ := hU 𝒴 hN (rightMulAb 𝒜 u)
    obtain ⟨g', ⟨h', hpb', hi', he'⟩, -⟩ := hU 𝒴 hN (rightMulAb 𝒜 u⁻¹)
    obtain ⟨g0, -, h0⟩ := hU 𝒴 hN 𝒜
    have hid : QMFamFibre 𝒜.toQMFamily (CommaMorphism.left (𝟙 𝒴)) 𝒜.toQMFamily :=
      qmFamFibre_id _
    have c1 : g ≫ g' = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a : O => a) (fun a : O => a * (u : O)) (fun a : O => a)
        (fun a : O => a * ((u⁻¹ : Oˣ) : O)) g.left g'.left h h' hpb hpb' hi he hi' he' (fun a => rfl)
        (fun a => by rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one])
    have c2 : g' ≫ g = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a : O => a) (fun a : O => a * ((u⁻¹ : Oˣ) : O)) (fun a : O => a)
        (fun a : O => a * (u : O)) g'.left g.left h' h hpb' hpb hi' he' hi he (fun a => rfl)
        (fun a => by rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one])
    refine ⟨⟨g, g', c1, c2⟩, fun y P P' hP hP' => ?_⟩
    change M3.mk P' = M3.mk (P.rightMul u)
    refine g3 _ _ _ _ _ _ hP' ?_
    obtain ⟨k, hkpb, hki, hke⟩ := hP
    refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
    · exact paste_iota _ _ _ _ _ (hki a) (hi a)
    · exact paste_eta _ _ _ _ _ _ _ (hke (a * u)) (he a)


/-! ## G3 proved: fibres are unique up to isomorphism -/

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3 in
/-- The identity of a fibre goes to `η(0)` (as in r1univ-rigid's `isGrpFibre_of_rigidity`). -/
theorem eta_left_comp {S : Scheme.{0}} {𝒜 : QMFamily S} {K : Type} [Field K]
    {t : Spec (CommRingCat.of K) ⟶ S} {P : QML3 K} {g : P.A.X.left ⟶ 𝒜.F.left}
    (he : ∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = t ≫ 𝒜.eta a) :
    η[P.A.X].left ≫ g = t ≫ 𝒜.eta 0 := by
  rw [← one_left_comp he]
  change _ = ((toUnit (AbVar.ptObj (K := K) K)) ≫ η[P.A.X]).left ≫ g
  rw [Over.comp_left, Over.toUnit_left]
  simp [AbVar.ptObj, Algebra.algebraMap_self]

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3 in
/-- **G3 holds** (proved: the pullback isomorphism of two fibres is `𝒪`-equivariant, respects the
level sections, and is a homomorphism by the kernel's `G0FibreSimple.rigidityHom`). -/
theorem fibreClassUnique : FibreClassUnique := by
  intro S 𝒜 K _ y P P' ⟨k, hpb, hι, he⟩ ⟨k', hpb', hι', he'⟩
  let e : P.A.X.left ⟶ P'.A.X.left := hpb'.lift k P.A.X.hom hpb.w
  let e' : P'.A.X.left ⟶ P.A.X.left := hpb.lift k' P'.A.X.hom hpb'.w
  have ek : e ≫ k' = k := hpb'.lift_fst _ _ _
  have eh : e ≫ P'.A.X.hom = P.A.X.hom := hpb'.lift_snd _ _ _
  have ek' : e' ≫ k = k' := hpb.lift_fst _ _ _
  have eh' : e' ≫ P.A.X.hom = P'.A.X.hom := hpb.lift_snd _ _ _
  have ee : e ≫ e' = 𝟙 _ := hpb.hom_ext (by rw [Category.assoc, ek', ek, Category.id_comp])
    (by rw [Category.assoc, eh', eh, Category.id_comp])
  have ee' : e' ≫ e = 𝟙 _ := hpb'.hom_ext (by rw [Category.assoc, ek, ek', Category.id_comp])
    (by rw [Category.assoc, eh, eh', Category.id_comp])
  let φ0 : P.A.X ⟶ P'.A.X := Over.homMk e eh
  let ψ0 : P'.A.X ⟶ P.A.X := Over.homMk e' eh'
  have h0 := eta_left_comp he
  have h0' := eta_left_comp he'
  have hη : η[P.A.X] ≫ φ0 = η[P'.A.X] := by
    apply Over.OverMorphism.ext
    apply hpb'.hom_ext
    · rw [Over.comp_left, Category.assoc]
      change η[P.A.X].left ≫ e ≫ k' = _
      rw [ek, h0, h0']
    · exact (Over.w (η[P.A.X] ≫ φ0)).trans (Over.w η[P'.A.X]).symm
  have hη' : η[P'.A.X] ≫ ψ0 = η[P.A.X] := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [Over.comp_left, Category.assoc]
      change η[P'.A.X].left ≫ e' ≫ k = _
      rw [ek', h0, h0']
    · exact (Over.w (η[P'.A.X] ≫ ψ0)).trans (Over.w η[P.A.X]).symm
  have := G0FibreSimple.rigidityHom K P.A P'.A φ0 hη
  have := G0FibreSimple.rigidityHom K P'.A P.A ψ0 hη'
  refine Quotient.sound ⟨⟨AbVar.Hom.mk' φ0, AbVar.Hom.mk' ψ0, ?_, ?_, fun a => ?_, fun a => ?_⟩⟩
  · apply Over.OverMorphism.ext
    simp only [AbVar.Hom.hom_mk', Over.comp_left, Over.id_left]
    exact ee
  · apply Over.OverMorphism.ext
    simp only [AbVar.Hom.hom_mk', Over.comp_left, Over.id_left]
    exact ee'
  · apply Over.OverMorphism.ext
    simp only [AbVar.Hom.hom_mk', Over.comp_left]
    apply hpb'.hom_ext
    · change (P.q.iota a).hom.left ≫ e ≫ k' = e ≫ (P'.q.iota a).hom.left ≫ k'
      rw [ek, hι, hι', reassoc_of% ek]
    · change (P.q.iota a).hom.left ≫ e ≫ P'.A.X.hom = e ≫ (P'.q.iota a).hom.left ≫ P'.A.X.hom
      rw [eh, Over.w, Over.w, eh]
  · apply congrArg Additive.ofMul ?_ |>.trans (ofMul_toMul _)
    apply Over.OverMorphism.ext
    simp only [AbVar.Hom.hom_mk', Over.comp_left]
    apply hpb'.hom_ext
    · change (Additive.toMul (P.e.eta a)).left ≫ e ≫ k' = (Additive.toMul (P'.e.eta a)).left ≫ k'
      rw [ek, he, he']
    · change (Additive.toMul (P.e.eta a)).left ≫ e ≫ P'.A.X.hom =
        (Additive.toMul (P'.e.eta a)).left ≫ P'.A.X.hom
      rw [eh, Over.w, Over.w]


/-! ## G2 from the dimension glue -/

/-- **An abelian surface is smooth of relative dimension 2**: for an abelian variety `A/K` (the kernel's
`PkgI3.AbVar`) whose underlying space has Krull dimension 2, the structure morphism is smooth of relative
dimension 2. (`QML3` records `A.dim = 2`; `QMAbScheme` asks for `SmoothOfRelativeDimension 2`.) Proved below
(`abVarSurfaceRelDim`). -/
def AbVarSurfaceRelDim : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), A.dim = 2 → SmoothOfRelativeDimension 2 A.X.hom

/-- **`AbVarSurfaceRelDim` holds** (proved from the kernel's smooth dimension theory,
`ZInQKernel/Contrib/Dim/SmoothStalk.lean`): take a standard smooth chart at `x` (Mathlib's
`Smooth.exists_isStandardSmooth`) of relative dimension `d`, and a closed point `z` of the chart (`A` is
Jacobson); then `d = dim 𝒪_{A,z} = dim A = 2` (`ringKrullDim_stalk_of_chart`,
`topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth`, `A` irreducible). -/
theorem abVarSurfaceRelDim : AbVarSurfaceRelDim := by
  intro K _ A hA
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.X.hom
  have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth A.X.hom x
  let _ := (A.X.hom.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(A.X.left, V) := h
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h'.out
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨z, hzV, hzc⟩ := nonempty_inter_closedPoints (Z := (V : Set A.X.left)) ⟨x, hxV⟩
    V.isOpen.isLocallyClosed
  have h1 := (ZInQ.Contrib.Dim.ringKrullDim_stalk_of_chart A.X.hom hV e P.dimension hP z hzV hzc).1
  have h2 := (ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth A.X.hom z hzc).1
  have hd : P.dimension = 2 := by
    have : ((P.dimension : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by
      rw [← h1, ← h2]; exact hA
    exact_mod_cast this
  exact ⟨U, hU, V, hV, hxV, e, hd ▸ hP⟩

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3 in
theorem ptObj_hom_self (K : Type) [Field K] : (AbVar.ptObj (K := K) K).hom = 𝟙 _ := by
  simp [AbVar.ptObj, Algebra.algebraMap_self]

/-- A morphism `Spec K' → Spec K` of spectra of fields is an epimorphism. -/
theorem epi_spec_field {K K' : Type} [Field K] [Field K']
    (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K)) : Epi s := by
  let _ : Algebra K K' := (Spec.preimage s).hom.toAlgebra
  have hs : s = Spec.map (CommRingCat.ofHom (algebraMap K K')) := (Spec.map_preimage s).symm
  rw [hs]
  exact Flat.epi_of_flat_of_surjective _

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3 in
/-- **G2 from G2a** (proved). -/
theorem qml3AsQMAb_of (hD : AbVarSurfaceRelDim) : QML3AsQMAb := by
  intro K _ _ P
  have hsec : ∀ x : P.A.Pt K, x.left ≫ P.A.X.hom = 𝟙 _ := fun x => by
    rw [Over.w x, ptObj_hom_self]
  let c : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ AbVar.ptObj (K := K) K :=
    Over.homMk (𝟙 _) (by rw [ptObj_hom_self]; rfl)
  have hc : ∀ x : P.A.Pt K, (Over.homMk (U := 𝟙_ (Over (Spec (CommRingCat.of K)))) x.left (hsec x) :
      𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A.X) = c ≫ x := fun x => by
    apply Over.OverMorphism.ext
    exact (Category.id_comp _).symm
  have hio : ∀ f : P.A.X ⟶ P.A.X, (Over.homMk f.left (Over.w f) : P.A.X ⟶ P.A.X) = f := fun f => by
    apply Over.OverMorphism.ext; simp
  let 𝒜' : QMAbScheme (Spec (CommRingCat.of K)) :=
    { F := P.A.X
      proper := inferInstance
      smooth := hD K P.A P.surface
      iota := fun a => (P.q.iota a).hom.left
      iota_over := fun a => Over.w _
      eta := fun a => (Additive.toMul (P.e.eta a)).left
      eta_sec := fun a => hsec _
      grp := P.A.grp
      geomConn := ⟨fun K' _ y Z fst snd h => by
        have : IrreducibleSpace Z :=
          GeometricallyIrreducible.geometrically_irreducibleSpace (f := P.A.X.hom) y fst snd h
        infer_instance⟩
      one_eq := by
        rw [map_zero, toMul_zero]
        change _ = ((toUnit (AbVar.ptObj (K := K) K)) ≫ η[P.A.X]).left
        rw [Over.comp_left, Over.toUnit_left, ptObj_hom_self]; exact (Category.id_comp _).symm
      iota_hom := fun a => by
        rw [hio]; infer_instance
      iota_one := by
        change (P.q.iota 1).hom.left = 𝟙 _
        rw [map_one]; rfl
      iota_mul := fun a b => by
        change (P.q.iota (a * b)).hom.left = (P.q.iota b).hom.left ≫ (P.q.iota a).hom.left
        rw [map_mul]; rfl
      iota_add := fun a b => by
        rw [hio, hio, hio, map_add]; rfl
      eta_add := fun a b => by
        rw [hc, hc, hc, map_add, toMul_add, MonObj.comp_mul]
      eta_linear := fun a b => by
        change (Additive.toMul (P.e.eta (a * b))).left =
          (Additive.toMul (P.e.eta b)).left ≫ (P.q.iota a).hom.left
        rw [P.e.linear]; rfl
      eta_three := fun b => by
        change (Additive.toMul (P.e.eta (3 * b))).left = (Additive.toMul (P.e.eta 0)).left
        rw [(P.e.ker _).mpr ⟨b, rfl⟩, (P.e.ker 0).mpr ⟨0, by simp⟩]
      eta_ker := fun K' _ s a => by
        rw [← P.e.ker a, show P.e.eta 0 = 0 from map_zero _]
        constructor
        · intro h
          have := epi_spec_field s
          have h2 := cancel_epi s |>.mp h
          have h3 : Additive.toMul (P.e.eta a) = Additive.toMul (0 : Additive (P.A.Pt K)) :=
            Over.OverMorphism.ext h2
          exact Additive.toMul.injective h3
        · intro h; rw [h] }
  exact ⟨𝒜', fun T 𝒜 y => Iff.rfl⟩

/-! ## G1, proved -/

section G1

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3
open scoped CategoryTheory.Obj

/-- **A smooth, geometrically connected scheme over a field is geometrically integral** (Stacks Project,
Varieties and Properties; EGA IV₂ 4.5–4.6, 6.7–6.8; locators UNVERIFIED). Proved below
(`smoothGeomConnIntegral`) from the kernel's vendored `Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`
(stalks of a smooth scheme over a field are domains), Tau Ceti's
`irreducibleSpace_of_connected_of_isDomain_stalk` and r1univ-rigid's `isReduced_of_smooth`. -/
def SmoothGeomConnIntegral : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), Smooth f →
    GeometricallyConnected f → GeometricallyIntegral f

/-- **`End(A)` is torsion-free in characteristic 0**: for an abelian variety `A/K`, `char K = 0`, `n • f = 0`
with `n > 0` forces `f = 0` (Mumford, *Abelian varieties*, §19 Thm. 3; locators UNVERIFIED). Proved below
(`abVarEndTorsionFree`) from the kernel's `ZInQ.Contrib.AbVarBC.mulIsogeny` (`[n]` is finite and surjective in
characteristic 0, proved from Mathlib): `[n] ≫ f = [n] ≫ 1` and `[n]` is dominant onto the reduced `A`. -/
def AbVarEndTorsionFree : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : AbVar K) (n : ℕ) (f : AbVar.End A), 0 < n → n • f = 0 → f = 0

/-- Stalks of a smooth scheme over a field are domains. -/
theorem isDomain_stalk_of_smooth {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (x : X) : IsDomain (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := by simp
  have hsm := f.smooth_appLE hU hV hVU
  let _ : Field Γ(Spec (CommRingCat.of k), ⊤) :=
    (ZInQ.Contrib.Dim.isField_sections_spec k ⊤ Set.univ_nonempty).toField
  let _ : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := (f.appLE ⊤ V hVU).hom.toAlgebra
  have : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := hsm
  let x' : V := ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk x'
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  exact (ZInQ.Contrib.CloudW03NeronSurj.FLT.Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) (hV.primeIdealOf x').asIdeal (X.presheaf.stalk x)).1

/-- **`SmoothGeomConnIntegral` holds** (compiled). -/
theorem smoothGeomConnIntegral : SmoothGeomConnIntegral := by
  intro K _ X f hs hc
  refine ⟨fun L _ y Z fst snd h => ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback h hs
  have : ConnectedSpace Z := hc.geometrically_connectedSpace y fst snd h
  have : IsReduced Z := LeafQM.AV.R1UnivRigid.isReduced_of_smooth snd
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
  have : IrreducibleSpace Z :=
    TauCeti.AlgebraicGeometry.irreducibleSpace_of_connected_of_isDomain_stalk Z
      (fun x => isDomain_stalk_of_smooth snd x)
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

/-- **`AbVarEndTorsionFree` holds** (compiled). -/
theorem abVarEndTorsionFree : AbVarEndTorsionFree := by
  intro K _ _ A n f hn h
  obtain ⟨-, hsurj⟩ := ZInQ.Contrib.AbVarBC.mulIsogeny K A (n : ℤ) (by exact_mod_cast hn.ne')
  have h1 : f * ((n : ℤ) : AbVar.End A) = 0 := by
    rw [← Int.cast_comm, ← zsmul_eq_mul, natCast_zsmul, h]
  have h2 : ((n : ℤ) : AbVar.End A).hom ≫ f.hom =
      ((n : ℤ) : AbVar.End A).hom ≫ (1 : A.X ⟶ A.X) := by
    rw [MonObj.comp_one]
    exact congrArg AbVar.Hom.hom h1
  apply AbVar.Hom.ext'
  rw [AbVar.Hom.hom_zero]
  apply Over.OverMorphism.ext
  have : IsReduced A.X.left := LeafQM.AV.R1UnivRigid.isReduced_of_smooth A.X.hom
  have : IsDominant ((n : ℤ) : AbVar.End A).hom.left := inferInstance
  exact ext_of_isDominant_of_isSeparated A.X.hom (by rw [Over.w, Over.w])
    ((n : ℤ) : AbVar.End A).hom.left (by rw [← Over.comp_left, h2, Over.comp_left])

section
variable {S : Scheme.{0}} (𝒜 : QMAbScheme S) {K : Type} [Field K] (y : Spec (CommRingCat.of K) ⟶ S)

/-- The sections `η(a)` as maps from the unit. -/
def sec (a : O) : 𝟙_ (Over S) ⟶ 𝒜.F := Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a)

/-- `ι(a)` as an `Over` endomorphism. -/
def fa (a : O) : 𝒜.F ⟶ 𝒜.F := Over.homMk (𝒜.iota a) (𝒜.iota_over a)

/-- The comparison `Spec K → y^*𝟙`. -/
def cpt : AbVar.ptObj (K := K) K ⟶ (Over.pullback y).obj (𝟙_ (Over S)) :=
  Over.homMk (pullback.lift y (AbVar.ptObj (K := K) K).hom (by
    rw [ptObj_hom_self]; simp only [Over.tensorUnit_hom]
    exact (Category.id_comp y).symm)) (pullback.lift_snd _ _ _)

theorem cpt_fst : (cpt y).left ≫ pullback.fst (𝟙_ (Over S)).hom y = y := pullback.lift_fst _ _ _

theorem map_left_fst {X Z : Over S} (u : X ⟶ Z) :
    ((Over.pullback y).map u).left ≫ pullback.fst Z.hom y = pullback.fst X.hom y ≫ u.left := by
  simp [Over.pullback_map_left]

end

theorem int_eq_zero_of_forall_dvd (z : ℤ) (h : ∀ k : ℕ, (3 : ℤ) ^ k ∣ z) : z = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h z.natAbs)
  rw [Int.natAbs_pow]
  exact Nat.lt_pow_self (by norm_num)

theorem pow_three_mul_ofInt (k : ℕ) (m : Fin 4 → ℤ) :
    (3 : B) ^ k * ofInt m = ofInt (fun i => 3 ^ k * m i) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', _root_.mul_assoc, ih, three_mul_ofInt]
    congr 1; funext i; ring

theorem O_eq_zero_of_forall_dvd (c : O) (h : ∀ k : ℕ, ∃ d : O, c = 3 ^ k * d) : c = 0 := by
  obtain ⟨n, hn⟩ := c.2
  have hn0 : n = 0 := by
    funext i
    apply int_eq_zero_of_forall_dvd
    intro k
    obtain ⟨d, hd⟩ := h k
    obtain ⟨m, hm⟩ := d.2
    have : ofInt n = ofInt (fun i => 3 ^ k * m i) := by
      rw [← hn, ← pow_three_mul_ofInt, ← hm, hd]
      push_cast; rfl
    exact ⟨m i, congrFun (ofInt_injective this) i⟩
  apply Subtype.ext
  rw [hn, hn0]
  exact ofInt_zero


/-- The fibre of a QM abelian scheme at a field point, as an abelian variety (given `SmoothGeomConnIntegral`). -/
def fibreAbVar (hI : SmoothGeomConnIntegral) {S : Scheme.{0}} (𝒜 : QMAbScheme S) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) : AbVar K :=
  letI := 𝒜.grp
  have := 𝒜.proper
  have := 𝒜.smooth
  have := 𝒜.geomConn
  have : IsProper ((Over.pullback y).obj 𝒜.F).hom := by dsimp; infer_instance
  have : SmoothOfRelativeDimension 2 ((Over.pullback y).obj 𝒜.F).hom := by dsimp; infer_instance
  have : Smooth ((Over.pullback y).obj 𝒜.F).hom := SmoothOfRelativeDimension.smooth 2 _
  have : GeometricallyConnected ((Over.pullback y).obj 𝒜.F).hom := by dsimp; infer_instance
  have : GeometricallyIntegral ((Over.pullback y).obj 𝒜.F).hom :=
    hI K _ _ inferInstance inferInstance
  ⟨(Over.pullback y).obj 𝒜.F⟩

/-- **G1 from `SmoothGeomConnIntegral` and `AbVarEndTorsionFree`** (compiled): the base change `A_y = (Over.pullback y).obj A` with the
group law of Mathlib's `Functor.grpObjObj` is an abelian variety (`fibreAbVar`, geometric integrality from
`SmoothGeomConnIntegral`) of dimension 2 (the kernel's `SmoothStalk.lean`); `ι` and `η` push forward along the
monoidal functor `Over.pullback y` (`Functor.map_mul`, `Functor.map_one`); `ι` is injective because
`ι(d) = 0 ⇒ d ∈ 3𝒪` (the level structure) and `End` is torsion-free (`AbVarEndTorsionFree`), so the kernel lies
in `⋂ 3^k 𝒪 = 0`; the fibre square is Mathlib's pullback. -/
theorem qmAbFieldFibre_of (hI : SmoothGeomConnIntegral) (hT : AbVarEndTorsionFree) :
    QMAbFieldFibre := by
  intro S 𝒜 K _ _ y
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI := 𝒜.grp
  have := 𝒜.proper
  have := 𝒜.smooth
  have := 𝒜.geomConn
  let Fs : Over (Spec (CommRingCat.of K)) := (Over.pullback y).obj 𝒜.F
  have hsm2 : SmoothOfRelativeDimension 2 Fs.hom := by dsimp [Fs]; infer_instance
  have : Smooth Fs.hom := SmoothOfRelativeDimension.smooth 2 _
  set AF : AbVar K := fibreAbVar hI 𝒜 y with hAF
  -- the level points
  let pt : O → AF.Pt K := fun a => cpt y ≫ (Over.pullback y).map (sec 𝒜 a)
  have hpt : ∀ a, (pt a).left ≫ pullback.fst 𝒜.F.hom y = y ≫ 𝒜.eta a := fun a => by
    change ((cpt y).left ≫ ((Over.pullback y).map (sec 𝒜 a)).left) ≫ _ = _
    rw [Category.assoc, map_left_fst, ← Category.assoc, cpt_fst]
    rfl
  have hpt_eq : ∀ a b, pt a = pt b ↔ y ≫ 𝒜.eta a = y ≫ 𝒜.eta b := fun a b => by
    constructor
    · intro h; rw [← hpt, ← hpt, h]
    · intro h
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · exact (hpt a).trans (h.trans (hpt b).symm)
      · exact (Over.w (pt a)).trans (Over.w (pt b)).symm
  -- dimension
  have hdim : AF.dim = 2 := by
    have : GeometricallyIntegral Fs.hom := (fibreAbVar hI 𝒜 y).geomInt
    have : IrreducibleSpace Fs.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton Fs.hom
    have : JacobsonSpace Fs.left := LocallyOfFiniteType.jacobsonSpace Fs.hom
    obtain ⟨z, -, hzc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set Fs.left))
      ⟨(pt 0).left.base (IsLocalRing.closedPoint K), trivial⟩ isClosed_univ.isLocallyClosed
    have h1 := (ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension Fs.hom 2 z hzc).1
    have h2 := (ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth Fs.hom z hzc).1
    change topologicalKrullDim Fs.left = 2
    rw [h2, h1]; rfl
  -- `ι` on the fibre
  have hmon : ∀ a, IsMonHom ((Over.pullback y).map (fa 𝒜 a)) := fun a => by
    have : IsMonHom (fa 𝒜 a) := 𝒜.iota_hom a
    infer_instance
  let jf : O → AbVar.End AF := fun a => @AbVar.Hom.mk' K _ AF AF ((Over.pullback y).map (fa 𝒜 a)) (hmon a)
  have hjf : ∀ a, (jf a).hom = (Over.pullback y).map (fa 𝒜 a) := fun a => rfl
  have hfa1 : fa 𝒜 1 = 𝟙 _ := Over.OverMorphism.ext 𝒜.iota_one
  have hfamul : ∀ a b, fa 𝒜 (a * b) = fa 𝒜 b ≫ fa 𝒜 a := fun a b =>
    Over.OverMorphism.ext (𝒜.iota_mul a b)
  have hfaadd : ∀ a b, fa 𝒜 (a + b) = fa 𝒜 a * fa 𝒜 b := fun a b => 𝒜.iota_add a b
  have hfa0 : fa 𝒜 0 = 1 := by
    have h := hfaadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  let jq : O →+* AbVar.End AF :=
    { toFun := jf
      map_one' := AbVar.Hom.ext' (by rw [hjf, hfa1]; exact CategoryTheory.Functor.map_id _ _)
      map_mul' := fun a b => AbVar.Hom.ext' (by
        rw [hjf, hfamul]; exact CategoryTheory.Functor.map_comp _ _ _)
      map_zero' := AbVar.Hom.ext' (by
        rw [hjf, hfa0]; exact CategoryTheory.Functor.map_one _)
      map_add' := fun a b => AbVar.Hom.ext' (by
        rw [hjf, hfaadd]; exact CategoryTheory.Functor.map_mul _ _ _) }
  have hsec_lin : ∀ a b, sec 𝒜 (a * b) = sec 𝒜 b ≫ fa 𝒜 a := fun a b =>
    Over.OverMorphism.ext (𝒜.eta_linear a b)
  have hpt_lin : ∀ a b, pt (a * b) = pt b ≫ (jq a).hom := fun a b => by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 (a * b)) = (cpt y ≫ (Over.pullback y).map (sec 𝒜 b)) ≫
      (Over.pullback y).map (fa 𝒜 a)
    rw [hsec_lin, CategoryTheory.Functor.map_comp, Category.assoc]
  -- `jq(d) = 0 ⇒ d ∈ 3𝒪`
  have hker1 : ∀ d : O, jq d = 0 → ∃ e : O, d = 3 * e := fun d hd => by
    rw [← 𝒜.eta_ker K y d, ← hpt_eq]
    have h1 := hpt_lin d 1
    rw [_root_.mul_one, hd, AbVar.Hom.hom_zero, MonObj.comp_one] at h1
    have h0 := hpt_lin 0 1
    rw [_root_.mul_one, map_zero, AbVar.Hom.hom_zero, MonObj.comp_one] at h0
    rw [h1, h0]
  have hinj : Function.Injective jq := by
    have hz : ∀ c, jq c = 0 → c = 0 := fun c hc => by
      apply O_eq_zero_of_forall_dvd
      intro k
      induction k with
      | zero => exact ⟨c, by simp⟩
      | succ k ih =>
        obtain ⟨d, hd⟩ := ih
        have hd0 : jq d = 0 := by
          apply hT K AF (3 ^ k) (jq d) (by positivity)
          rw [nsmul_eq_mul, ← map_natCast jq, ← map_mul]
          push_cast
          rw [← hd, hc]
        obtain ⟨e, he⟩ := hker1 d hd0
        exact ⟨e, by rw [hd, he, pow_succ, _root_.mul_assoc]⟩
    intro a b hab
    have := hz (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp this
  let q : QMStr AF := ⟨jq, hinj⟩
  -- the level structure
  have hsec0 : sec 𝒜 0 = 1 := by
    apply Over.OverMorphism.ext
    change 𝒜.eta 0 = (toUnit (𝟙_ (Over S)) ≫ η[𝒜.F]).left
    rw [toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp, 𝒜.one_eq]
  have hpt0 : pt 0 = 1 := by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 0) = 1
    rw [hsec0, CategoryTheory.Functor.map_one, MonObj.comp_one]
  have hptadd : ∀ a b, pt (a + b) = pt a * pt b := fun a b => by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 (a + b)) = _
    rw [show sec 𝒜 (a + b) = sec 𝒜 a * sec 𝒜 b from 𝒜.eta_add a b,
      CategoryTheory.Functor.map_mul, MonObj.comp_mul]
    rfl
  let e0 : O →+ Additive (AF.Pt K) :=
    { toFun := fun a => Additive.ofMul (pt a)
      map_zero' := by rw [hpt0]; rfl
      map_add' := fun a b => by rw [hptadd]; rfl }
  let e : Level3 q :=
    { eta := e0
      linear := fun a b => by
        change Additive.ofMul (pt (a * b)) = Additive.ofMul (pt b ≫ (jq a).hom)
        rw [hpt_lin]
      ker := fun a => by
        change Additive.ofMul (pt a) = Additive.ofMul (1 : AF.Pt K) ↔ _
        rw [EmbeddingLike.apply_eq_iff_eq, ← hpt0, hpt_eq, 𝒜.eta_ker] }
  refine ⟨⟨AF, hdim, q, e⟩, pullback.fst 𝒜.F.hom y, IsPullback.of_hasPullback _ _, fun a => ?_,
    fun a => hpt a⟩
  exact map_left_fst y (fa 𝒜 a)

end G1

/-! ## The discharge -/

/-- **G1 holds** (compiled). -/
theorem qmAbFieldFibre : QMAbFieldFibre :=
  qmAbFieldFibre_of smoothGeomConnIntegral abVarEndTorsionFree

/-- **`ShimuraGoodReductionNoGuard` from the printed integral model alone** (compiled; standard axioms). -/
theorem shimuraGoodReductionNoGuard_of_printed (hRep : ShimuraIntegralModelRep) :
    ShimuraGoodReductionNoGuard :=
  shimuraGoodReductionNoGuard_of_rep hRep qmAbFieldFibre (qml3AsQMAb_of abVarSurfaceRelDim)
    fibreClassUnique

end SGRSplit
