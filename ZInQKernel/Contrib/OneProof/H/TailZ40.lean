import ZInQKernel.Contrib.OneProof.H.TailZ22
import ZInQKernel.Contrib.OneProof.MumfordRigidity

/-! # OneProof H, rigid-prune: what the chain needs from Mumford's rigidity is *GIT* Thm 6.14 on QM families

route-a-fold (`TailZ16`, `TailZ17`) and x6-fold (`TailZ22`) convert the bundle's moduli leaves from their printed
abelian-scheme form (`R1fpPropsAb`) to the kernel's `R1fpProps` (families `QMFamily` without group law) by
`L_iff_ab (mumfordRigidity_of_core r.mumfordRigidityCore)`. Both directions of `R1fpProps ↔ R1fpPropsAb` apply
rigidity only to one kind of family: a `QMFamily` over a proper smooth curve `S/ℚ` all of whose field fibres are
objects (`exists_qmAbScheme`, in `r1univProps_of_ab` and `r1famAbProps_of_r1famProps`). This module

* states that instance as a Prop, `QMFamilyGroupLaw`;
* proves it from gt-rigidity's `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` alone (Mumford, *GIT* Thm 6.14: the
  group law with identity `e`; numbers UNVERIFIED), i.e. **without clause (a)** (*GIT* Cor. 6.4 over `S`): the one
  use of (a), "`ι(a)` is a homomorphism", is checked on field points of the reduced `F ×_S F`, where it is the
  field-level statement (`isMonHom_of_fibres`; clause (b) is r1univ-rigid's proved `isGrpFibre_of_rigidity`);
* proves `R1fpProps ↔ R1fpPropsAb` and the nine `L ↔ LAb` used on the chain under `QMFamilyGroupLaw`
  (`*_iff_ab_gl`), so the chain's conversions (`TailZ23`) no longer go through `mumfordRigidity_of_core`.

Why `QMFamilyGroupLaw` cannot be dropped (docs/research/rigid-prune.md §1): the field
`OpenGlue7.quotientP1Coordinate` has `R1fpProps Y Φ` as a hypothesis, and `ModelGlue.exists_genFib_to_Y` applies
`R1univProps` to the generic fibre of the Shimura model's family, which the field `shimuraGoodReductionNoGuard`
gives only as a `QMFamily`. Both need `R1univProps` of a witness on families not known to be abelian schemes. -/

noncomputable section

namespace LeafQM

namespace AV

namespace R1UnivRigid

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ## §1 The Prop -/

/-- **Mumford's Thm 6.14 on QM families** (the instance of rigidity the chain uses): a `QMFamily` over a proper
smooth curve `S/ℚ` all of whose field fibres are objects (`QML3`) underlies an abelian scheme with `𝒪`-action and
level 3 (`QMAbScheme`). A consequence of `MumfordGroupLaw` (`qmFamilyGroupLaw_of_groupLaw`), hence of
`MumfordRigidityCore` (`qmFamilyGroupLaw_of_core`). -/
def QMFamilyGroupLaw : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜 : QMFamily S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K, IsFibreOf 𝒜 s.left P) →
      ∃ 𝒜' : QMAbScheme S.left, 𝒜'.toQMFamily = 𝒜

/-! ## §2 `ι(a)` is a homomorphism, on field points (replaces clause (a)) -/

/-- **`ι(a)` is a homomorphism** when `F ×_S F` is reduced, `F` is a group object with identity `η(0)` and
`ι(a)` fixes `η(0)`: `μ ≫ ι(a)` and `(ι(a) ⊗ ι(a)) ≫ μ` agree on every field point `x` of `F ×_S F`, since `x`
factors through `A ×_K A` for the fibre `A` at the image of `x` (`lift_comp_φ`), the fibre map is a group
homomorphism (clause (b), `isGrpFibre_of_rigidity`), and `ι_A(a)` is a homomorphism of abelian varieties. -/
theorem isMonHom_of_fibres {S : Scheme.{0}} (𝒜 : QMFamily S) [GrpObj 𝒜.F] [IsProper 𝒜.F.hom]
    [Smooth 𝒜.F.hom] [IsReduced (𝒜.F ⊗ 𝒜.F).left] (hη : η[𝒜.F].left = 𝒜.eta 0)
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K, IsFibreOf 𝒜 t P)
    (a : O) (hιe : 𝒜.eta 0 ≫ 𝒜.iota a = 𝒜.eta 0) :
    IsMonHom (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F) := by
  set fi : 𝒜.F ⟶ 𝒜.F := Over.homMk (𝒜.iota a) (𝒜.iota_over a) with hfidef
  constructor
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, hη]
    exact hιe
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    refine hom_ext_pts 𝒜.F.hom _ _ (by simp only [Category.assoc, Over.w]) (fun K _ x => ?_)
    obtain ⟨P, g, hpb, hι, he⟩ := hfib K (x ≫ (𝒜.F ⊗ 𝒜.F).hom)
    obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := isGrpFibre_of_rigidity 𝒜.F (x ≫ (𝒜.F ⊗ 𝒜.F).hom) P.A g
      ⟨hpb, by rw [hη]; exact one_left_comp he⟩
    have w₁ : (x ≫ (fst 𝒜.F 𝒜.F).left) ≫ 𝒜.F.hom = 𝟙 _ ≫ (x ≫ (𝒜.F ⊗ 𝒜.F).hom) := by
      rw [Category.id_comp, Category.assoc, Over.w]
    have w₂ : (x ≫ (snd 𝒜.F 𝒜.F).left) ≫ 𝒜.F.hom = 𝟙 _ ≫ (x ≫ (𝒜.F ⊗ 𝒜.F).hom) := by
      rw [Category.id_comp, Category.assoc, Over.w]
    let c₁ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ P.A.X :=
      Over.homMk (hpb.lift _ _ w₁) (by simp)
    let c₂ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ P.A.X :=
      Over.homMk (hpb.lift _ _ w₂) (by simp)
    have hx : (lift c₁ c₂).left ≫ φ = x := by
      rw [lift_comp_φ c₁ c₂ (fst 𝒜.F 𝒜.F) (snd 𝒜.F 𝒜.F) x φ hφ₁ hφ₂ (hpb.lift_fst _ _ _)
        (hpb.lift_fst _ _ _), lift_fst_snd, Over.id_left, Category.comp_id]
    have hι' : g ≫ fi.left = (P.q.iota a).hom.left ≫ g := (hι a).symm
    have hcomm : ((P.q.iota a).hom ⊗ₘ (P.q.iota a).hom).left ≫ φ = φ ≫ (fi ⊗ₘ fi).left := by
      rw [← lift_fst_comp_snd_comp, ← lift_fst_comp_snd_comp]
      refine lift_comp_φ _ _ _ _ φ φ hφ₁ hφ₂ ?_ ?_
      · rw [Over.comp_left, Over.comp_left, Category.assoc, ← hι', ← Category.assoc, ← hφ₁,
          Category.assoc]
      · rw [Over.comp_left, Over.comp_left, Category.assoc, ← hι', ← Category.assoc, ← hφ₂,
          Category.assoc]
    have hm : μ[P.A.X].left ≫ (P.q.iota a).hom.left =
        ((P.q.iota a).hom ⊗ₘ (P.q.iota a).hom).left ≫ μ[P.A.X].left := by
      rw [← Over.comp_left, IsMonHom.mul_hom, Over.comp_left]
    rw [← hx]
    simp only [Category.assoc]
    rw [← reassoc_of% hφμ, hι', reassoc_of% hm, hφμ, reassoc_of% hcomm]

/-! ## §3 The construction from the group law alone -/

/-- **`exists_qmAbScheme` from `MumfordGroupLaw`** (r1univ-rigid's proof, with clause (b) from
`isGrpFibre_of_rigidity` and `ι(a)` a homomorphism from `isMonHom_of_fibres` in place of clause (a)). -/
theorem exists_qmAbScheme_gl (hG : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) {S : Scheme.{0}}
    [IsReduced S] [IsLocallyNoetherian S] (𝒜 : QMFamily S) [IsReduced 𝒜.F.left]
    [IsReduced (𝒜.F ⊗ 𝒜.F).left]
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P) :
    ∃ 𝒜' : QMAbScheme S, 𝒜'.toQMFamily = 𝒜 := by
  have := 𝒜.proper
  have := 𝒜.smooth
  have hsm : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  have hgc := geomConn_of_fibres 𝒜 hfib
  obtain ⟨G, hη⟩ := hG S 𝒜.F (𝒜.eta 0) inferInstance 𝒜.proper hsm hgc (𝒜.eta_sec 0)
    (fun K _ s => by
      obtain ⟨P, g, hpb, -, he⟩ := hfib K s
      exact ⟨P.A, g, hpb, one_left_comp he⟩)
  have hb : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
      (g : A.X.left ⟶ 𝒜.F.left), IsAbVarFibre 𝒜.F (𝒜.eta 0) s A g → IsGrpFibre 𝒜.F A g :=
    fun K _ s A g h => isGrpFibre_of_rigidity 𝒜.F s A g (by rw [hη]; exact h)
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
    iota_hom := fun a => isMonHom_of_fibres 𝒜 hη hfib a (hιe a)
    iota_one := hone
    iota_mul := hmul
    iota_add := hadd
    eta_add := headd
    eta_linear := helin
    eta_three := hthree
    eta_ker := hker }, rfl⟩

/-- **`QMFamilyGroupLaw` from Mumford's Thm 6.14 alone** (`MumfordGroupLaw`; no Cor. 6.4 over the base). Over a
smooth curve `S/ℚ`, `S`, `F` and `F ×_S F` are smooth over `ℚ`, hence reduced, and `S` is locally noetherian. -/
theorem qmFamilyGroupLaw_of_groupLaw (hG : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) :
    QMFamilyGroupLaw := by
  intro S _ hs 𝒜 hfib
  obtain ⟨h1, h2, h3⟩ := reduced_of_smooth_curve hs 𝒜
  have : Smooth S.hom := SmoothOfRelativeDimension.smooth 1 _
  have := 𝒜.smooth
  have : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (𝒜.F ⊗ 𝒜.F).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : IsReduced (𝒜.F ⊗ 𝒜.F).left := isReduced_of_smooth ((𝒜.F ⊗ 𝒜.F).hom ≫ S.hom)
  exact exists_qmAbScheme_gl hG 𝒜 (fun K _ t => fibre_of_fieldPt 𝒜 hfib t)

/-- **`QMFamilyGroupLaw` from the research field `mumfordRigidityCore`** (through gt-rigidity's
`mumfordGroupLaw_of_core`, which drops clause (a)). -/
theorem qmFamilyGroupLaw_of_core (hC : MumfordRigidityCore) : QMFamilyGroupLaw :=
  qmFamilyGroupLaw_of_groupLaw (ZInQ.Contrib.MumfordRigidity.mumfordGroupLaw_of_core hC)

/-! ## §4 The clause lists agree under `QMFamilyGroupLaw` -/

/-- `R1univProps` from its abelian-scheme clause, under `QMFamilyGroupLaw` (r1univ-rigid's `r1univProps_of_ab`). -/
theorem r1univProps_of_ab_gl (hG : QMFamilyGroupLaw) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h : R1univAbProps Y Φ) : R1univProps Y Φ := by
  intro S hp hs 𝒜' hfib
  obtain ⟨𝒜, h𝒜⟩ := hG S hp hs 𝒜' hfib
  subst h𝒜
  exact h S hp hs 𝒜 hfib

/-- The family of `R1famProps` is an abelian scheme with `𝒪`-action, under `QMFamilyGroupLaw`
(r1univ-rigid's `r1famAbProps_of_r1famProps`). -/
theorem r1famAbProps_of_r1famProps_gl (hG : QMFamilyGroupLaw) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (hp : IsProper Y.hom) (hs : SmoothOfRelativeDimension 1 Y.hom)
    (h : R1famProps Y Φ) : R1famAbProps Y Φ := by
  obtain ⟨𝒜, h𝒜⟩ := h
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y), ∃ P : QML3 K,
      IsFibreOf 𝒜 s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K s)
    exact ⟨P, h𝒜 K s P hP.symm⟩
  obtain ⟨𝒜', rfl⟩ := hG Y hp hs 𝒜 hfib
  exact ⟨𝒜', h𝒜⟩

/-- **`R1fpProps ↔ R1fpPropsAb` under `QMFamilyGroupLaw`.** -/
theorem r1fpProps_iff_ab_gl (hG : QMFamilyGroupLaw) (Y : Over (Spec (CommRingCat.of ℚ)))
    (Φ : PtEquiv Y) : R1fpProps Y Φ ↔ R1fpPropsAb Y Φ :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, r1famAbProps_of_r1famProps_gl hG h1 h2 h5,
      r1univAbProps_of_r1univProps h6⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, r1famProps_of_r1famAbProps h5,
      r1univProps_of_ab_gl hG h6⟩⟩

/-- `R1fpProps = R1fpPropsAb` as predicates, under `QMFamilyGroupLaw`. -/
theorem r1fpProps_eq_ab_gl (hG : QMFamilyGroupLaw) :
    (R1fpProps : (Y : Over (Spec (CommRingCat.of ℚ))) → PtEquiv Y → Prop) = R1fpPropsAb :=
  funext fun Y => funext fun Φ => propext (r1fpProps_iff_ab_gl hG Y Φ)

/-! ## §5 The nine leaves of the chain, under `QMFamilyGroupLaw`

The proofs of route-a-fold's and x6-fold's `L_iff_ab` (`TailZ17`, `TailZ22`) with `r1fpProps_eq_ab_gl`. -/

theorem gonzalezRotgerCountX6_iff_ab_gl (hG : QMFamilyGroupLaw) :
    ShimuraSplit.GonzalezRotgerCountX6 ↔ ShimuraSplit.GonzalezRotgerCountX6Ab := by
  unfold ShimuraSplit.GonzalezRotgerCountX6 ShimuraSplit.GonzalezRotgerCountX6Ab
  rw [r1fpProps_eq_ab_gl hG]

theorem deligneComponentsY3Printed_iff_ab_gl (hG : QMFamilyGroupLaw) :
    ShimuraGlue.DeligneComponentsY3Printed ↔ ShimuraGlue.DeligneComponentsY3PrintedAb := by
  unfold ShimuraGlue.DeligneComponentsY3Printed ShimuraGlue.DeligneComponentsY3PrintedAb
  rw [r1fpProps_eq_ab_gl hG]

theorem r1R2fpRep_iff_ab_gl (hG : QMFamilyGroupLaw) :
    HDec.LeafAdopt.R1R2fpRep ↔ HDec.LeafAdopt.R1R2fpRepAb := by
  unfold HDec.LeafAdopt.R1R2fpRep HDec.LeafAdopt.R1R2fpRepAb
  rw [r1fpProps_eq_ab_gl hG]

theorem shimuraFamily_iff_ab_gl (hG : QMFamilyGroupLaw) :
    HDec.QMSplit.Moduli.ShimuraFamily ↔ HDec.QMSplit.Moduli.ShimuraFamilyAb := by
  unfold HDec.QMSplit.Moduli.ShimuraFamily HDec.QMSplit.Moduli.ShimuraFamilyAb
  rw [r1fpProps_eq_ab_gl hG]

theorem deligneComponentsX6Printed_iff_ab_gl (hG : QMFamilyGroupLaw) :
    ShimuraGlue.DeligneComponentsX6Printed ↔ ShimuraGlue.DeligneComponentsX6PrintedAb := by
  unfold ShimuraGlue.DeligneComponentsX6Printed ShimuraGlue.DeligneComponentsX6PrintedAb
  rw [r1fpProps_eq_ab_gl hG]

theorem rayClassCM_iff_ab_gl (hG : QMFamilyGroupLaw) :
    ShimuraGlue.Ray.RayClassCM ↔ ShimuraGlue.Ray.RayClassCMAb := by
  unfold ShimuraGlue.Ray.RayClassCM ShimuraGlue.Ray.RayClassCMAb
  rw [r1fpProps_eq_ab_gl hG]

theorem gonzalezRotgerX6_iff_ab_gl (hG : QMFamilyGroupLaw) :
    HDec.QMSplit.Moduli.GonzalezRotgerX6 ↔ HDec.QMSplit.Moduli.GonzalezRotgerX6Ab := by
  unfold HDec.QMSplit.Moduli.GonzalezRotgerX6 HDec.QMSplit.Moduli.GonzalezRotgerX6Ab
  rw [r1fpProps_eq_ab_gl hG]

theorem elkiesEquationsX6_iff_ab_gl (hG : QMFamilyGroupLaw) :
    HDec.QMSplit.Moduli.ElkiesEquationsX6 ↔ HDec.QMSplit.Moduli.ElkiesEquationsX6Ab := by
  unfold HDec.QMSplit.Moduli.ElkiesEquationsX6 HDec.QMSplit.Moduli.ElkiesEquationsX6Ab
  rw [r1fpProps_eq_ab_gl hG]

theorem babaGranathRational_iff_ab_gl (hG : QMFamilyGroupLaw) :
    HDec.QMSplit.Moduli.BabaGranathRational ↔ HDec.QMSplit.Moduli.BabaGranathRationalAb := by
  unfold HDec.QMSplit.Moduli.BabaGranathRational HDec.QMSplit.Moduli.BabaGranathRationalAb
  rw [r1fpProps_eq_ab_gl hG]

end R1UnivRigid

end AV

end LeafQM

#print axioms LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw
#print axioms LeafQM.AV.R1UnivRigid.babaGranathRational_iff_ab_gl
