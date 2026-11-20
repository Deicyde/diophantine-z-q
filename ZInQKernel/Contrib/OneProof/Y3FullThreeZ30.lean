import ZInQKernel.Contrib.OneProof.Y3RepresentableQ

/-! # y3-route-a: the Y₃ fine-moduli leaf as the manuscript's own conclusion (diophantine_zq.tex L473-477)

Task y3-route-a (2026-11-17). Report: `docs/research/y3-route-a.md`; log: `scratch/y3-route-a/log.md`.

The research leaf `Y3Fix.Y3FineModuliAbP` cited Buzzard (Duke 1997) and Boutot–Carayol directly for full
`𝒪`-linear level 3 at discriminant 6, which Buzzard's hypotheses exclude (level prime to the discriminant; y3-audit).
The manuscript does not cite a print at level 3: it builds `Y₃` from Buzzard at `V₁(5)` and a free quotient
(L443-477). This file states the manuscript's conclusion as the leaf, `Y3FullThreeRepZ30`, over `ℤ[1/30]`, and proves
from it:

* `y3RepresentableQ_of_z30 : Y3FullThreeRepZ30 → Y3Audit.Y3RepresentableQ` (the generic fibre represents the problem
  on locally noetherian `ℚ`-schemes; base change of `QMAbScheme` along any morphism, `abBC`, copied from y3-audit's
  unfinished `scratch/y3-audit/GenFib.lean`, where it is route-independent);
* `y3FineModuliAbP_of_z30 : Y3FullThreeRepZ30 → Y3Fix.Y3FineModuliAbP` (with y3-audit's `y3FineModuliAbP_of_rep'`);
* `shimuraMainThmIDeligneY3AbU_of_z30` (the research field, with y3-fix's canonical-model leaf).

No `sorry`.
-/

set_option linter.all false

noncomputable section

namespace Y3RouteA

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open Y3Fix SGRSplit HDec.VertWitness HDec.ModelGlue Y3Audit
open scoped CategoryTheory.Obj

/-! ## Generic pullback lemmas (all objects abstract, to avoid defeq-only object mismatches) -/

theorem map_left_fst' {S T : Scheme.{0}} (j : T ⟶ S) {X Z : Over S} (u : X ⟶ Z) :
    ((Over.pullback j).map u).left ≫ pullback.fst Z.hom j = pullback.fst X.hom j ≫ u.left := by
  simp [Over.pullback_map_left]

theorem lift_compat_iota {A P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {j : Y ⟶ Z}
    (hP : IsPullback fst snd f j) (k : A ⟶ P) (i' : A ⟶ A) (iP : P ⟶ P) (iX : X ⟶ X) (h₀ : A ⟶ X)
    (sA : A ⟶ Y) (hk1 : k ≫ fst = h₀) (hk2 : k ≫ snd = sA) (hι : i' ≫ h₀ = h₀ ≫ iX)
    (hiP : iP ≫ fst = fst ≫ iX) (hi's : i' ≫ sA = sA) (hiPs : iP ≫ snd = snd) : i' ≫ k = k ≫ iP := by
  apply hP.hom_ext
  · rw [Category.assoc, hk1, hι, Category.assoc, hiP, ← Category.assoc, hk1]
  · rw [Category.assoc, hk2, hi's, Category.assoc, hiPs, hk2]

theorem lift_compat_eta {A P X Y Z U : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {j : Y ⟶ Z}
    (hP : IsPullback fst snd f j) (k : A ⟶ P) (e' : U ⟶ A) (g : U ⟶ Y) (eP : Y ⟶ P) (eX : Z ⟶ X)
    (h₀ : A ⟶ X) (sA : A ⟶ U) (hk1 : k ≫ fst = h₀) (hk2 : k ≫ snd = sA ≫ g) (hη : e' ≫ h₀ = (g ≫ j) ≫ eX)
    (heP : eP ≫ fst = j ≫ eX) (he's : e' ≫ sA = 𝟙 U) (hePs : eP ≫ snd = 𝟙 Y) : e' ≫ k = g ≫ eP := by
  apply hP.hom_ext
  · rw [Category.assoc, hk1, hη, Category.assoc, Category.assoc, heP]
  · rw [Category.assoc, hk2, ← Category.assoc, he's, Category.id_comp, Category.assoc, hePs,
      Category.comp_id]

theorem sec_eq_iff {P X Y Z W : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {j : Y ⟶ Z}
    (hP : IsPullback fst snd f j) (s : W ⟶ Y) (ea eb : Y ⟶ P) (xa xb : Z ⟶ X)
    (ha : ea ≫ fst = j ≫ xa) (hb : eb ≫ fst = j ≫ xb) (hsa : ea ≫ snd = 𝟙 Y) (hsb : eb ≫ snd = 𝟙 Y) :
    s ≫ ea = s ≫ eb ↔ (s ≫ j) ≫ xa = (s ≫ j) ≫ xb := by
  constructor
  · intro h
    have := congrArg (· ≫ fst) h
    simp only [Category.assoc] at this
    rw [ha, hb] at this
    simpa only [Category.assoc] using this
  · intro h
    apply hP.hom_ext
    · rw [Category.assoc, Category.assoc, ha, hb, ← Category.assoc, ← Category.assoc, h]
    · rw [Category.assoc, Category.assoc, hsa, hsb]

section BC

variable {S T : Scheme.{0}} (𝒜 : QMAbScheme S) (j : T ⟶ S)

/-- The unit section of the pulled-back unit. -/
abbrev epsBC : 𝟙_ (Over T) ⟶ (Over.pullback j).obj (𝟙_ (Over S)) :=
  Functor.LaxMonoidal.ε (Over.pullback j)

theorem epsBC_fst : (epsBC j).left ≫ pullback.fst (𝟙_ (Over S)).hom j = j := by
  have h1 : (epsBC j).left ≫ pullback.snd (𝟙_ (Over S)).hom j = 𝟙 T := Over.w (epsBC j)
  have h2 : pullback.fst (𝟙_ (Over S)).hom j = pullback.snd (𝟙_ (Over S)).hom j ≫ j := by
    have := pullback.condition (f := (𝟙_ (Over S)).hom) (g := j)
    exact (Category.comp_id _).symm.trans this
  rw [h2, ← Category.assoc, h1]
  exact Category.id_comp j

theorem fa_one : fa 𝒜 1 = 𝟙 _ := Over.OverMorphism.ext 𝒜.iota_one

theorem fa_mul (a b : O) : fa 𝒜 (a * b) = fa 𝒜 b ≫ fa 𝒜 a := Over.OverMorphism.ext (𝒜.iota_mul a b)

theorem sec_mul (a b : O) : sec 𝒜 (a * b) = sec 𝒜 b ≫ fa 𝒜 a :=
  Over.OverMorphism.ext (𝒜.eta_linear a b)

theorem sec_three (b : O) : sec 𝒜 (3 * b) = sec 𝒜 0 := Over.OverMorphism.ext (𝒜.eta_three b)

/-- The section `η'(a) = ε ≫ j^*η(a)` of the base change. -/
abbrev secBC (a : O) : 𝟙_ (Over T) ⟶ (Over.pullback j).obj 𝒜.F :=
  epsBC j ≫ (Over.pullback j).map (sec 𝒜 a)

theorem secBC_fst (a : O) :
    (secBC 𝒜 j a).left ≫ pullback.fst 𝒜.F.hom j = j ≫ 𝒜.eta a := by
  change (epsBC j).left ≫ ((Over.pullback j).map (sec 𝒜 a)).left ≫ pullback.fst 𝒜.F.hom j = _
  rw [map_left_fst', ← Category.assoc, epsBC_fst]
  rfl

theorem secBC_snd (a : O) : (secBC 𝒜 j a).left ≫ pullback.snd 𝒜.F.hom j = 𝟙 T :=
  Over.w (secBC 𝒜 j a)

theorem iotaBC_fst (a : O) :
    ((Over.pullback j).map (fa 𝒜 a)).left ≫ pullback.fst 𝒜.F.hom j =
      pullback.fst 𝒜.F.hom j ≫ 𝒜.iota a :=
  map_left_fst' j (fa 𝒜 a)

/-- **The base change of a `QMAbScheme`** along `j : T ⟶ S`. -/
def abBC : QMAbScheme T :=
  letI := 𝒜.grp
  have := 𝒜.proper
  have := 𝒜.smooth
  have := 𝒜.geomConn
  { F := (Over.pullback j).obj 𝒜.F
    proper := by dsimp; infer_instance
    smooth := by dsimp; infer_instance
    iota := fun a => ((Over.pullback j).map (fa 𝒜 a)).left
    iota_over := fun a => Over.w ((Over.pullback j).map (fa 𝒜 a))
    eta := fun a => (secBC 𝒜 j a).left
    eta_sec := fun a => Over.w (secBC 𝒜 j a)
    grp := inferInstance
    geomConn := by dsimp; infer_instance
    one_eq := by
      have hsec0 : sec 𝒜 0 = η[𝒜.F] := by
        apply Over.OverMorphism.ext
        change 𝒜.eta 0 = (η[𝒜.F]).left
        rw [𝒜.one_eq]
      change _ = (epsBC j ≫ (Over.pullback j).map (sec 𝒜 0)).left
      rw [hsec0]
      rfl
    iota_hom := fun a => by
      have : IsMonHom (fa 𝒜 a) := 𝒜.iota_hom a
      have e : (Over.homMk ((Over.pullback j).map (fa 𝒜 a)).left (Over.w _) :
          (Over.pullback j).obj 𝒜.F ⟶ (Over.pullback j).obj 𝒜.F) = (Over.pullback j).map (fa 𝒜 a) :=
        Over.OverMorphism.ext rfl
      rw [e]
      infer_instance
    iota_one := by
      change ((Over.pullback j).map (fa 𝒜 1)).left = _
      rw [fa_one, CategoryTheory.Functor.map_id]
      rfl
    iota_mul := fun a b => by
      change ((Over.pullback j).map (fa 𝒜 (a * b))).left = _
      rw [fa_mul, CategoryTheory.Functor.map_comp]
      rfl
    iota_add := fun a b => by
      have e : ∀ c : O, (Over.homMk ((Over.pullback j).map (fa 𝒜 c)).left (Over.w _) :
          (Over.pullback j).obj 𝒜.F ⟶ (Over.pullback j).obj 𝒜.F) = (Over.pullback j).map (fa 𝒜 c) :=
        fun c => Over.OverMorphism.ext rfl
      rw [e, e, e]
      have h : fa 𝒜 (a + b) = fa 𝒜 a * fa 𝒜 b := 𝒜.iota_add a b
      rw [h, CategoryTheory.Functor.map_mul]
    eta_add := fun a b => by
      have e : ∀ c : O, (Over.homMk (U := 𝟙_ (Over T)) (secBC 𝒜 j c).left (Over.w _) :
          𝟙_ (Over T) ⟶ (Over.pullback j).obj 𝒜.F) = secBC 𝒜 j c :=
        fun c => Over.OverMorphism.ext rfl
      rw [e, e, e]
      have h : sec 𝒜 (a + b) = sec 𝒜 a * sec 𝒜 b := 𝒜.eta_add a b
      simp only [secBC]
      rw [h, CategoryTheory.Functor.map_mul, MonObj.comp_mul]
    eta_linear := fun a b => by
      change (epsBC j ≫ (Over.pullback j).map (sec 𝒜 (a * b))).left = _
      rw [sec_mul, CategoryTheory.Functor.map_comp, ← Category.assoc]
      rfl
    eta_three := fun b => by
      change (epsBC j ≫ (Over.pullback j).map (sec 𝒜 (3 * b))).left = _
      rw [sec_three]
    eta_ker := fun K _ s a => by
      rw [← 𝒜.eta_ker K (s ≫ j) a]
      exact sec_eq_iff (IsPullback.of_hasPullback 𝒜.F.hom j) s _ _ (𝒜.eta a) (𝒜.eta 0)
        (secBC_fst 𝒜 j a) (secBC_fst 𝒜 j 0) (secBC_snd 𝒜 j a) (secBC_snd 𝒜 j 0) }

theorem abBC_F : (abBC 𝒜 j).F = (Over.pullback j).obj 𝒜.F := rfl

theorem abBC_eta_fst (a : O) : (abBC 𝒜 j).eta a ≫ pullback.fst 𝒜.F.hom j = j ≫ 𝒜.eta a :=
  secBC_fst 𝒜 j a

theorem abBC_iota_fst (a : O) :
    (abBC 𝒜 j).iota a ≫ pullback.fst 𝒜.F.hom j = pullback.fst 𝒜.F.hom j ≫ 𝒜.iota a :=
  iotaBC_fst 𝒜 j a

/-- The pullback square of the base change, with its `ι` and `η`. -/
theorem qmFamFibre_abBC : QMFamFibre 𝒜.toQMFamily j (abBC 𝒜 j).toQMFamily :=
  ⟨pullback.fst 𝒜.F.hom j, IsPullback.of_hasPullback _ _, fun a => abBC_iota_fst 𝒜 j a,
    fun a => abBC_eta_fst 𝒜 j a⟩

/-- Pasting of `QMFamFibre`. -/
theorem qmFamFibre_trans {U : Scheme.{0}} {𝒜₁ : QMFamily S} {𝒜₂ : QMFamily T} {𝒜₃ : QMFamily U}
    {j : T ⟶ S} {g : U ⟶ T} (h₂ : QMFamFibre 𝒜₁ j 𝒜₂) (h₃ : QMFamFibre 𝒜₂ g 𝒜₃) :
    QMFamFibre 𝒜₁ (g ≫ j) 𝒜₃ := by
  obtain ⟨h, hpb, hi, he⟩ := h₂
  obtain ⟨k, hkpb, hki, hke⟩ := h₃
  refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
  · exact paste_iota _ _ _ _ _ (hki a) (hi a)
  · exact paste_eta _ _ _ _ _ _ _ (hke a) (he a)

/-- Conversely, a pullback of `𝒜` along `g ≫ j` is a pullback of `j^*𝒜` along `g`. -/
theorem qmFamFibre_abBC_of {U : Scheme.{0}} {𝒜' : QMFamily U} {g : U ⟶ T}
    (h : QMFamFibre 𝒜.toQMFamily (g ≫ j) 𝒜') : QMFamFibre (abBC 𝒜 j).toQMFamily g 𝒜' := by
  obtain ⟨h₀, hpb, hι, hη⟩ := h
  have w : h₀ ≫ 𝒜.F.hom = (𝒜'.F.hom ≫ g) ≫ j := by rw [hpb.w, Category.assoc]
  let k : 𝒜'.F.left ⟶ (pullback 𝒜.F.hom j) := pullback.lift h₀ (𝒜'.F.hom ≫ g) w
  have hk1 : k ≫ pullback.fst 𝒜.F.hom j = h₀ := pullback.lift_fst _ _ _
  have hk2 : k ≫ pullback.snd 𝒜.F.hom j = 𝒜'.F.hom ≫ g := pullback.lift_snd _ _ _
  refine ⟨k, ?_, fun a => ?_, fun a => ?_⟩
  · have hR : IsPullback (pullback.fst 𝒜.F.hom j) (pullback.snd 𝒜.F.hom j) 𝒜.F.hom j :=
      IsPullback.of_hasPullback _ _
    have hs : IsPullback (k ≫ pullback.fst 𝒜.F.hom j) 𝒜'.F.hom 𝒜.F.hom (g ≫ j) := by
      rw [hk1]; exact hpb
    exact IsPullback.of_right hs hk2 hR
  · exact lift_compat_iota (IsPullback.of_hasPullback 𝒜.F.hom j) k (𝒜'.iota a) ((abBC 𝒜 j).iota a)
      (𝒜.iota a) h₀ (𝒜'.F.hom ≫ g) hk1 hk2 (hι a) (abBC_iota_fst 𝒜 j a)
      (by rw [← Category.assoc, 𝒜'.iota_over]) ((abBC 𝒜 j).iota_over a)
  · exact lift_compat_eta (IsPullback.of_hasPullback 𝒜.F.hom j) k (𝒜'.eta a) g ((abBC 𝒜 j).eta a)
      (𝒜.eta a) h₀ 𝒜'.F.hom hk1 hk2 (hη a) (abBC_eta_fst 𝒜 j a) (𝒜'.eta_sec a) ((abBC 𝒜 j).eta_sec a)

end BC

/-! ## The base ring `ℤ[1/30]` -/

/-- `ℤ[1/30]`, the base of the manuscript's integral model (L444-445). -/
abbrev Z30 : Type := Localization.Away (30 : ℤ)

theorem isUnit_thirty_rat : IsUnit ((Int.castRingHom ℚ) (30 : ℤ)) := by
  rw [isUnit_iff_ne_zero]; norm_num

/-- `ℤ[1/30] → ℚ`. -/
def z30ToRat : Z30 →+* ℚ := IsLocalization.Away.lift (30 : ℤ) isUnit_thirty_rat

/-- `Spec ℚ → Spec ℤ[1/30]`. -/
abbrev specRatToZ30 : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of Z30) :=
  Spec.map (CommRingCat.ofHom z30ToRat)

/-! ## The leaf -/

/-- **LEAF (consequence; the manuscript's own claim, diophantine_zq.tex L473-477): the full-three moduli problem of
abelian surfaces with QM by `𝒪` is representable over `ℤ[1/30]` by a proper smooth curve.**

*Statement.* There are a `ℤ[1/30]`-scheme `𝒴`, proper and smooth of relative dimension 1, and a universal object
`𝒜 : QMAbSchemeP 𝒴` such that for every locally noetherian `ℤ[1/30]`-scheme `S` (universe 0) and every
`𝒜' : QMAbSchemeP S` there is exactly one `ℤ[1/30]`-morphism `g : S → 𝒴` with `𝒜'` the pullback of `𝒜` along
`g`, together with the `𝒪`-action and the level sections (`QMFamFibre`). Here a `QMAbSchemeP S` is an abelian
scheme `A/S` of relative dimension 2 (proper, smooth, geometrically connected group object of `Over S`), a unital
ring map `ι : 𝒪 → End_S(A)` for the maximal order `𝒪` of `B = (2, −3 | ℚ)` (discriminant 6), and an `𝒪`-linear
`η : 𝒪 → A(S)` killing `3𝒪` that is, at every geometric point `s`, a bijection `𝒪/3𝒪 ≅ A_s[3]` (`LevelPrint`).
Such an `η` is the same as a section of the manuscript's sheaf `Isom_𝒪(𝒪/3𝒪, A[3])` (L451-453): `η(1)` determines
it by `η(a) = ι(a) η(1)`, and over `ℤ[1/30]` the group `A[3]` is finite étale, so an isomorphism is one on
geometric fibres. Its generic fibre over `ℚ` is `Y₃` (L476): `y3RepresentableQ_of_z30` proves that it satisfies
`Y3Audit.Y3RepresentableQ`, hence (`y3FineModuliAbP_of_z30`) it is a witness of `Y3Fix.Y3FineModuliAbP`.

*The manuscript's derivation* (L443-477; not a print at level 3):
1. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), Thm 2.1 and Cor. 2.3, applied at
   `V₁(5)` over `ℤ[1/30]` (L443-446): determinant image full, level maximal at the division primes 2 and 3, and
   `5 ≥ 4` prime to 6, so inside Buzzard's hypotheses.
2. A full five-marking refining the `V₁(5)`-marking gives the full-five moduli scheme as a finite étale cover
   (L447-449).
3. The finite étale sheaf `Isom_𝒪(𝒪/3𝒪, A[3])` over it (L449-453), nonempty on every geometric fibre because the
   Tate lattice is free of rank one over `𝒪₃` (`B₃` a division algebra; every `𝒪₃`-stable lattice principal,
   L453-462). The result `X₃₅` is smooth projective with full markings at 3 and 5 (L464-465).
4. `G₅ = (𝒪/5𝒪)^×` acts freely, changing only the five-marking (L465-472): a stabilizer gives a polarized
   automorphism preserving the full three-marking, hence a finite-order element of `1 + 3M₄(ℤ₃)`, which is
   torsion-free (first nonzero 3-adic term of a prime-order element); so the automorphism is the identity, and the
   full five-marking forces the group element to be the identity.
5. The quotient `X₃₅/G₅` is smooth projective, `X₃₅ → X₃₅/G₅` is finite étale, and the universal abelian scheme with
   its canonical principal polarization, `𝒪`-action and three-marking descends; the quotient represents exactly the
   full-three moduli problem, and its generic fibre is `Y₃` (L472-477).

*Polarization.* The manuscript's moduli problem carries the canonical principal polarization (L467, L474-475);
`QMAbSchemeP` has none. The polarization-free functor is isomorphic to the polarized one through the canonical
polarization: every `(A, ι)` over `S` carries a unique principal polarization of the manuscript's canonical type,
compatible with every isomorphism (relative Lemma P). **ON THE SPOT**: this equivalence is in neither the
manuscript nor a print read for this task, and it is not proved in the tree (Lemma P is proved over fields and on
lattices only, `RvQMPolar`, `lemmaP_H1`); nothing here builds on it beyond reading the leaf.

*Form.* Weaker than the manuscript's statement in three ways: proper instead of projective; the universal property
only on locally noetherian bases in universe 0; the polarization-free functor (equivalent as above). It is the
manuscript's statement, not a print: kind consequence, flagged ELLIOT. -/
def Y3FullThreeRepZ30 : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of Z30))) (𝒜 : QMAbSchemeP 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of Z30))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbSchemeP S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

/-! ## The generic fibre -/

/-- The generic fibre `𝒴 ×_{ℤ[1/30]} Spec ℚ` as a `ℚ`-scheme. -/
def genFib30 (𝒴 : Over (Spec (CommRingCat.of Z30))) : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk (pullback.snd 𝒴.hom specRatToZ30)

theorem genFib30_isProper (𝒴 : Over (Spec (CommRingCat.of Z30))) (h : IsProper 𝒴.hom) :
    IsProper (genFib30 𝒴).hom := by
  show IsProper (pullback.snd 𝒴.hom specRatToZ30)
  infer_instance

theorem genFib30_smooth (𝒴 : Over (Spec (CommRingCat.of Z30)))
    (h : SmoothOfRelativeDimension 1 𝒴.hom) : SmoothOfRelativeDimension 1 (genFib30 𝒴).hom := by
  show SmoothOfRelativeDimension 1 (pullback.snd 𝒴.hom specRatToZ30)
  infer_instance

/-- **The generic fibre of the manuscript's model represents the problem over `ℚ`** (given `TorsionStructure`, to
pass back to the printed level form over `ℚ`). -/
theorem y3RepresentableQ_of_z30_of (hT : ObjBridge.TorsionStructure) (h : Y3FullThreeRepZ30) :
    Y3RepresentableQ := by
  obtain ⟨𝒴, 𝒜, hp, hs, hU⟩ := h
  let Y : Over (Spec (CommRingCat.of ℚ)) := genFib30 𝒴
  let j : Y.left ⟶ 𝒴.left := pullback.fst 𝒴.hom specRatToZ30
  have hc : j ≫ 𝒴.hom = Y.hom ≫ specRatToZ30 := pullback.condition
  let 𝒜Q : QMAbSchemeP Y.left := ofKer hT (S := Y) (abBC (toKer 𝒜) j)
  refine ⟨Y, 𝒜Q, genFib30_isProper 𝒴 hp, genFib30_smooth 𝒴 hs, fun S hN 𝒜' => ?_⟩
  -- `S` as a `ℤ[1/30]`-scheme
  let Sp : Over (Spec (CommRingCat.of Z30)) := Over.mk (S.hom ≫ specRatToZ30)
  have hNp : IsLocallyNoetherian Sp.left := hN
  obtain ⟨g', hg', hgu⟩ := hU Sp hNp 𝒜'
  have w : g'.left ≫ 𝒴.hom = S.hom ≫ specRatToZ30 := Over.w g'
  let g : S ⟶ Y := Over.homMk (pullback.lift g'.left S.hom w) (pullback.lift_snd _ _ _)
  have hgj : g.left ≫ j = g'.left := pullback.lift_fst _ _ _
  refine ⟨g, ?_, fun g₂ hg₂ => ?_⟩
  · change QMFamFibre (abBC (toKer 𝒜) j).toQMFamily g.left 𝒜'.toQMFamily
    apply qmFamFibre_abBC_of
    have hg'' := hg'
    rw [← hgj] at hg''
    exact hg''
  · have h₂ : QMFamFibre 𝒜.toQMFamily (g₂.left ≫ j) 𝒜'.toQMFamily :=
      qmFamFibre_trans (qmFamFibre_abBC (toKer 𝒜) j) hg₂
    have w₂ : (g₂.left ≫ j) ≫ 𝒴.hom = Sp.hom := by
      change (g₂.left ≫ j) ≫ 𝒴.hom = S.hom ≫ specRatToZ30
      rw [Category.assoc, hc, ← Category.assoc, Over.w g₂]
    have e := hgu (Over.homMk (g₂.left ≫ j) w₂) h₂
    have e' : g₂.left ≫ j = g'.left := congrArg CommaMorphism.left e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change g₂.left ≫ j = g.left ≫ j
      rw [e', hgj]
    · exact (Over.w g₂).trans (Over.w g).symm

/-- `Y3RepresentableQ` from the manuscript's leaf alone (`TorsionStructure` from the proved
`mumfordTorsionAlgClosed`). -/
theorem y3RepresentableQ_of_z30 (h : Y3FullThreeRepZ30) : Y3RepresentableQ :=
  y3RepresentableQ_of_z30_of
    (AvSplit.torsionStructure_of_mumford ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof) h

/-- **The chain's leaf `Y3Fix.Y3FineModuliAbP` from the manuscript's leaf.** -/
theorem y3FineModuliAbP_of_z30 (h : Y3FullThreeRepZ30) : Y3FineModuliAbP :=
  y3FineModuliAbP_of_rep' (y3RepresentableQ_of_z30 h)

/-- The research field `ShimuraMainThmIDeligneY3AbU` from the manuscript's leaf and y3-fix's canonical-model leaf. -/
theorem shimuraMainThmIDeligneY3AbU_of_z30 (h : Y3FullThreeRepZ30) (h2 : DeligneCanonicalModelY3EveryH) :
    RayClassCFT.ShimuraMainThmIDeligneY3AbU :=
  shimuraMainThmIDeligneY3AbU_of_rep' (y3RepresentableQ_of_z30 h) h2

end Y3RouteA
