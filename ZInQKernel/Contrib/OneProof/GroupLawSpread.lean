import ZInQKernel.Contrib.OneProof.GroupLawGlue
import ZInQKernel.Contrib.OneProof.GroupLawStage
import ZInQKernel.Contrib.OneProof.GroupLawLocDiagram
import ZInQKernel.Contrib.SpreadOut.Spread

/-!
# group-law, II: a group law over a local ring of the base spreads out to an open neighbourhood

Let `V = Spec A` be an affine open of `S` and `𝔭 ⊂ A` a prime. `Spec A_𝔭 = lim_{f ∉ 𝔭} Spec A[1/f]` (gt-blr's
`GapBLR.specConeIsLimit`). A group law on the base change `F ×_S Spec A_𝔭` whose identity is the base change of `e`
descends to some `F ×_S Spec A[1/f]` (spread-out's `exists_grp_stage`, EGA IV₃ 8.8.2 (i) for the structure maps and
the axioms, from Mathlib), and after shrinking once more its identity is the base change of `e` (`exists_map_eq`).
This is a local group law (`LocalLaw`) whose open contains the point `𝔭` (`localLaw_of_stalk`).

Only Mathlib and the fork's proved spreading lemmas (`ZInQKernel/Contrib/SpreadOut`, `GapBLR`) are used.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Opposite

namespace ZInQ.Contrib.GroupLaw

open ZInQ.Contrib.SpreadOut

/-! ## §2 Spreading a local group law -/

section Spread

open ZInQ.Contrib.GroupLaw.Loc

variable {S : Scheme.{0}} {F : Over S} {e : S ⟶ F.left} {V : S.Opens} (hV : IsAffineOpen V)
  (𝔭 : Ideal Γ(S, V)) [𝔭.IsPrime]

/-- `Spec Γ(S, V)_𝔭 → S`. -/
abbrev locMap : Spec (CommRingCat.of (Localization.AtPrime 𝔭)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) (Localization.AtPrime 𝔭))) ≫ hV.fromSpec

/-- `ε` of a base-change functor followed by the first projection is the base map. -/
theorem eps_fst {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.fst (𝟙_ (Over Y)).hom f = f := by
  rw [Over.ε_pullback_left]
  have h : pullback.fst (𝟙 Y) f = pullback.snd (𝟙 Y) f ≫ f := by
    rw [← pullback.condition, Category.comp_id]
  change inv (pullback.snd (𝟙 Y) f) ≫ pullback.fst (𝟙 Y) f = f
  rw [h, IsIso.inv_hom_id_assoc]

theorem eps_fst' {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.fst (𝟙 Y) f = f :=
  eps_fst f

theorem fst_unit {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pullback.fst (𝟙_ (Over Y)).hom f = pullback.snd (𝟙_ (Over Y)).hom f ≫ f := by
  change pullback.fst (𝟙 Y) f = pullback.snd (𝟙 Y) f ≫ f
  rw [← pullback.condition, Category.comp_id]

variable [IsProper F.hom] [Smooth F.hom]

/-- **Spreading out, generic form.** For a cofiltered system `D` with limit `c`, maps `jj a : D a → S` compatible
with `D` and with `J : lim D → S`, a group law on `F ×_S lim D` whose identity is the base change of `e` comes from a
group law on the base change of `F` to some stage, with identity the base change of `e`. -/
theorem exists_stage_law {I : Type} [Category.{0} I] [IsCofiltered I] (D : I ⥤ Scheme.{0})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c)
    (he : e ≫ F.hom = 𝟙 S) (jj : ∀ a, D.obj a ⟶ S) (hDι : ∀ {a b : I} (f : a ⟶ b), D.map f ≫ jj b = jj a)
    (J : c.pt ⟶ S) (hπι : ∀ a, c.π.app a ≫ jj a = J) (a₀ : I)
    (G : GrpObj ((Over.pullback J).obj F))
    (hG : η[(Over.pullback J).obj F].left ≫ pullback.fst F.hom J = J ≫ e) :
    ∃ (k : I) (P : Over (D.obj k)) (q : P.left ⟶ F.left) (_ : IsPullback q P.hom F.hom (jj k))
      (_ : GrpObj P), η[P].left ≫ q = jj k ≫ e := by
  let N := (Over.pullback J).obj F
  let s₀ : Stage D c N :=
    { k := a₀
      M := (Over.pullback (jj a₀)).obj F
      qc := by dsimp; infer_instance
      qs := by dsimp; infer_instance
      lfp := by dsimp; infer_instance
      proper := by dsimp; infer_instance
      smooth := by dsimp; infer_instance
      e := (pbNat (c.π.app a₀) (jj a₀) J (hπι _)).app F }
  let Q : Stage D c N → Prop := fun t => ∃ q : t.M.left ⟶ F.left,
    IsPullback q t.M.hom F.hom (jj t.k) ∧
      t.e.hom.left ≫ pullback.fst F.hom J = pullback.fst t.M.hom (c.π.app t.k) ≫ q
  have hQ : ∀ (t : Stage D c N) {k' : I} (b : k' ⟶ t.k), Q t → Q (t.next b) := by
    rintro t k' b ⟨q, hq, hcomp⟩
    refine ⟨pullback.fst t.M.hom (D.map b) ≫ q, ?_, ?_⟩
    · have := (IsPullback.of_hasPullback t.M.hom (D.map b)).paste_horiz hq
      rw [hDι b] at this
      exact this
    · change ((stθ D c b).app t.M ≪≫ t.e).hom.left ≫ pullback.fst F.hom J = _
      rw [Iso.trans_hom, Over.comp_left, Category.assoc, hcomp]
      change (pbNatLeft (c.π.app k') (D.map b) (c.π.app t.k) (c.w b) t.M).hom ≫ _ = _
      rw [pbNatLeft_hom_fst_assoc]
      rfl
  have hQ0 : Q s₀ := by
    refine ⟨pullback.fst F.hom (jj a₀), IsPullback.of_hasPullback _ _, ?_⟩
    change (pbNatLeft _ _ _ (hπι _) F).hom ≫ _ = _
    rw [pbNatLeft_hom_fst]
    rfl
  obtain ⟨t, ⟨q, hq, hcomp⟩, Gt, hmon⟩ := exists_grp_stage_Q D hc Q hQ s₀ hQ0
  -- the base change of `e` at the stage
  let eT : 𝟙_ (Over (D.obj t.k)) ⟶ t.M :=
    Over.homMk (hq.lift (jj t.k ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]))
      (by simp)
  have heTq : eT.left ≫ q = jj t.k ≫ e := hq.lift_fst _ _ _
  have heTh : eT.left ≫ t.M.hom = 𝟙 _ := hq.lift_snd _ _ _
  -- the identity of the stage group law agrees with `eT` over the limit
  have key : c.π.app t.k ≫ η[t.M].left = c.π.app t.k ≫ eT.left := by
    apply hq.hom_ext
    · have e2 : c.π.app t.k ≫ eT.left ≫ q = J ≫ e := by rw [heTq, ← Category.assoc, hπι]
      rw [Category.assoc, Category.assoc, e2, ← hG]
      letI : GrpObj ((Over.pullback (c.π.app t.k)).obj t.M) := Functor.grpObjObj
      have h1 : η[(Over.pullback (c.π.app t.k)).obj t.M] ≫ t.e.hom = η[N] := IsMonHom.one_hom t.e.hom
      rw [← h1, Functor.obj.η_def]
      simp only [Over.comp_left, Category.assoc, hcomp, Over.pullback_map_left, pullback.lift_fst_assoc]
      simp only [← Category.assoc, eps_fst]
    · rw [Category.assoc, Category.assoc, heTh, Over.w η[t.M]]
      rfl
  have hmap : (Over.pullback (c.π.app t.k)).map η[t.M] = (Over.pullback (c.π.app t.k)).map eT := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      rw [fst_unit, Category.assoc, Category.assoc, key]
    · simp only [Over.pullback_map_left, pullback.lift_snd]
  haveI : QuasiCompact (𝟙_ (Over (D.obj t.k))).hom := show QuasiCompact (𝟙 _) from inferInstance
  obtain ⟨k', b, hb⟩ := exists_map_eq D c hc η[t.M] eT hmap
  let P := (Over.pullback (D.map b)).obj t.M
  letI GP : GrpObj P := Functor.grpObjObj
  have hPq : IsPullback (pullback.fst t.M.hom (D.map b) ≫ q) P.hom F.hom (jj k') := by
    have := (IsPullback.of_hasPullback t.M.hom (D.map b)).paste_horiz hq
    rw [hDι b] at this
    exact this
  have hPη : η[P].left ≫ pullback.fst t.M.hom (D.map b) ≫ q = jj k' ≫ e := by
    rw [Functor.obj.η_def, hb]
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst_assoc, heTq]
    simp only [← Category.assoc, eps_fst, hDι]
  exact ⟨k', P, _, hPq, GP, hPη⟩

/-- **Spreading out.** A group law on `F ×_S Spec Γ(S, V)_𝔭` with identity the base change of `e` comes from a
local group law whose open contains the point `𝔭`. -/
theorem localLaw_of_stalk (he : e ≫ F.hom = 𝟙 S)
    (G : GrpObj ((Over.pullback (locMap hV 𝔭)).obj F))
    (hG : η[(Over.pullback (locMap hV 𝔭)).obj F].left ≫ pullback.fst F.hom (locMap hV 𝔭) =
      locMap hV 𝔭 ≫ e) :
    ∃ L : LocalLaw F e, hV.fromSpec (⟨𝔭, inferInstance⟩ : PrimeSpectrum Γ(S, V)) ∈ Set.range L.j := by
  let R𝔭 := Localization.AtPrime 𝔭
  let jj : ∀ a : (Idx 𝔭)ᵒᵖ, (specDiag 𝔭).obj a ⟶ S := fun a => ej a ≫ hV.fromSpec
  have hπι : ∀ a, (specCone 𝔭 R𝔭).π.app a ≫ jj a = locMap hV 𝔭 := fun a => by
    rw [← Category.assoc]
    exact congrArg (· ≫ hV.fromSpec) (π_ej R𝔭 a)
  have hDι : ∀ {a b : (Idx 𝔭)ᵒᵖ} (f : a ⟶ b), (specDiag 𝔭).map f ≫ jj b = jj a := fun f => by
    rw [← Category.assoc]
    exact congrArg (· ≫ hV.fromSpec) (map_ej 𝔭 f)
  let i₀ : Idx 𝔭 := ⟨1, fun h => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 h)⟩
  obtain ⟨k, P, q, hq, GP, hη⟩ := exists_stage_law (specDiag 𝔭) (specConeIsLimit 𝔭 R𝔭) he jj hDι
    (locMap hV 𝔭) hπι (Opposite.op i₀) G hG
  refine ⟨⟨_, jj k, P, q, hq, GP, hη⟩, ?_⟩
  refine ⟨(specCone 𝔭 R𝔭).π.app k (IsLocalRing.closedPoint R𝔭), ?_⟩
  change ((specCone 𝔭 R𝔭).π.app k ≫ jj k) (IsLocalRing.closedPoint R𝔭) = _
  rw [hπι]
  change hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) R𝔭))
    (IsLocalRing.closedPoint R𝔭)) = _
  congr 1
  exact PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal

end Spread

end ZInQ.Contrib.GroupLaw
