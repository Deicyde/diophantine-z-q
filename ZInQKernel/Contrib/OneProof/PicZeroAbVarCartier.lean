import ZInQKernel.Contrib.OneProof.PicZeroAbVar
import ZInQKernel.Contrib.OneProof.CartierSmooth

/-!
# `PicZeroSmooth` from Cartier's theorem in characteristic `0` (pic-smooth)

`PicDict.PicZeroSmooth` (the identity component of `Pic_{A/K}` is smooth) quantifies over **every** field `K`.
Cartier's theorem (`AVGlue.CartierSmooth`, proved by `ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof`)
gives it for every field of characteristic `0`, from `PicDict.PicLocFinType` alone: the Picard scheme is a
commutative group scheme locally of finite type over `K` (`picardFunctorCommGrpObj`), hence smooth, and every open
subscheme of a smooth `K`-scheme is smooth.

In characteristic `p > 0` Cartier's theorem does not apply (non-reduced group schemes such as `μ_p` exist), and
the statement is a genuine theorem about abelian varieties (Mumford §13: `dim Pic⁰ = h¹(𝒪_A) = g`). That case is
the new Prop `PicSmooth.PicZeroSmoothPosChar` (pending reading, GLUE).

Main results:
* `PicSmooth.picZeroSmooth_of_cartier : CartierSmooth → PicLocFinType → PicZeroSmoothPosChar → PicZeroSmooth`;
* `PicSmooth.picZeroAbVar_of_printed2 : PicLocFinType → IdentityComponentLFT → PicZeroSmoothPosChar →
  KleimanPicZeroProper → PicZeroAbVar` (Cartier's theorem supplied by `cartierSmooth_proof`);
* `PicSmooth.picZeroAbVarAt_charZero`: `PicZeroAbVar` at every field of characteristic `0` from the three LEAF
  statements `PicLocFinType`, `IdentityComponentLFT`, `KleimanPicZeroProper` alone.
-/

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PicSmooth

open T09Pic PkgI3 PkgI3.AbVar PicDict PicFix

/-! ## Statements at one field -/

/-- `PicDict.PicZeroSmooth` at the one field `K`. -/
def PicZeroSmoothAt (K : Type) [Field K] : Prop :=
  ∀ (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (V : P.left.Opens),
    letI := picardFunctorCommGrpObj A.X.hom rep
    (V : Set P.left) = identityComponent P → Smooth (V.ι ≫ P.hom)

/-- `PicDict.PicZeroProper` at the one field `K`. -/
def PicZeroProperAt (K : Type) [Field K] : Prop :=
  ∀ (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (V : P.left.Opens),
    letI := picardFunctorCommGrpObj A.X.hom rep
    (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)

/-- `T09Pic.PicZeroAbVar` at the one field `K`. -/
def PicZeroAbVarAt (K : Type) [Field K] : Prop :=
  ∀ (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P),
    ∃ (B : AbVar K) (j : B.X ⟶ P), IsPicZero rep B j

theorem picZeroSmooth_iff : PicZeroSmooth ↔ ∀ (K : Type) [Field K], PicZeroSmoothAt K := Iff.rfl

theorem picZeroAbVar_iff : PicZeroAbVar ↔ ∀ (K : Type) [Field K], PicZeroAbVarAt K := Iff.rfl

/-- **`PicZeroAbVar` at one field `K`** from the two global leaves `PicLocFinType` and `IdentityComponentLFT` and
smoothness and properness of `Pic⁰` at `K`. The proof of `PicDict.picZeroAbVar_of_leaves` (pic-dict) verbatim,
with `K` fixed. -/
theorem picZeroAbVarAt_of (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (K : Type) [Field K]
    (h3a : PicZeroSmoothAt K) (h3b : PicZeroProperAt K) : PicZeroAbVarAt K := by
  intro A P rep
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨V, hV, hmulV, hinvV, hirr⟩ := h2 K P (h1 K A P rep)
  let j := subι V
  have hmem : ∀ x : P.left, x ∈ identityComponent P → x ∈ V := fun x hx => by
    rw [← SetLike.mem_coe, hV]; exact hx
  have hιV : ∀ y, V.ι y ∈ V := fun y => by
    rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι V]; exact ⟨y, rfl⟩
  -- multiplication
  let pj : subX V ⊗ subX V ⟶ P ⊗ P := CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst (subX V) (subX V) ≫ j) (CartesianMonoidalCategory.snd (subX V) (subX V) ≫ j)
  have hm : ∀ t, (pj ≫ μ[P]).left t ∈ V := fun t => by
    rw [Over.comp_left]
    apply hmulV
    · change (pj ≫ CartesianMonoidalCategory.fst P P).left t ∈ V
      rw [CartesianMonoidalCategory.lift_fst, Over.comp_left, Scheme.Hom.comp_apply]
      exact hιV _
    · change (pj ≫ CartesianMonoidalCategory.snd P P).left t ∈ V
      rw [CartesianMonoidalCategory.lift_snd, Over.comp_left, Scheme.Hom.comp_apply]
      exact hιV _
  let mulY := liftV V (pj ≫ μ[P]) hm
  have hmul : mulY ≫ j = CartesianMonoidalCategory.fst (subX V) (subX V) ≫ j *
      CartesianMonoidalCategory.snd (subX V) (subX V) ≫ j := by
    rw [liftV_comp, CategoryTheory.Hom.mul_def]
  -- unit
  have ho : ∀ t, (η[P]).left t ∈ V := fun t => hmem _ ⟨t, mem_connectedComponent⟩
  let oneY := liftV V η[P] ho
  have hone : oneY ≫ j = η[P] := liftV_comp V _ _
  -- inverse
  have hi : ∀ t, (j ≫ (𝟙 P)⁻¹).left t ∈ V := fun t => by
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hinvV _ (hιV t)
  let invY := liftV V (j ≫ (𝟙 P)⁻¹) hi
  have hinv : invY ≫ j = j⁻¹ := by
    rw [liftV_comp, GrpObj.comp_inv, Category.comp_id]
  letI : GrpObj (subX V) := AVGlue.grpObjOfMono j mulY hmul oneY hone invY hinv
  have hjmon : IsMonHom j := AVGlue.isMonHom_grpObjOfMono j mulY hmul oneY hone invY hinv
  haveI : IsProper (subX V).hom := h3b A P rep V hV
  haveI : Smooth (subX V).hom := h3a A P rep V hV
  haveI : GeometricallyReduced (subX V).hom := geometricallyReduced_of_smooth _
  haveI : GeometricallyIrreducible (subX V).hom := hirr
  haveI : GeometricallyIntegral (subX V).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  refine ⟨AbVar.mk (subX V), j, ?_, ?_, hjmon⟩
  · exact inferInstanceAs (IsOpenImmersion V.ι)
  · change Set.range V.ι = _
    rw [Scheme.Opens.range_ι, hV]

/-! ## Characteristic `0`: Cartier's theorem -/

/-- **The Picard scheme is smooth in characteristic `0`.** It is a group scheme over `K`
(`picardFunctorCommGrpObj`), locally of finite type (`PicLocFinType`), so Cartier's theorem applies. -/
theorem picard_smooth_of_cartier (hC : AVGlue.CartierSmooth) (h1 : PicLocFinType) (K : Type) [Field K]
    [CharZero K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) : Smooth P.hom := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  exact hC K P (h1 K A P rep)

/-- **`Pic⁰` is smooth in characteristic `0`**: an open subscheme of the smooth Picard scheme. The hypothesis
that `V` is the identity component is not needed. -/
theorem picZeroSmoothAt_charZero (hC : AVGlue.CartierSmooth) (h1 : PicLocFinType) (K : Type) [Field K]
    [CharZero K] : PicZeroSmoothAt K := by
  intro A P rep V _
  haveI := picard_smooth_of_cartier hC h1 K A P rep
  infer_instance

/-- `PicZeroProperAt` from Kleiman 9.5.4 in its printed form (pic-fix's `picZeroProper_of_kleiman`). -/
theorem picZeroProperAt_of_kleiman (h : KleimanPicZeroProper) (K : Type) [Field K] : PicZeroProperAt K :=
  fun A P rep V hV => picZeroProper_of_kleiman h K A P rep V hV

/-- **`PicZeroAbVar` at every field of characteristic `0` from three LEAF statements** (Kleiman 9.4.8 / BLR 8.2
Thm 3, SGA 3 VI_A 2.4, Kleiman 9.5.4) and Cartier's theorem. -/
theorem picZeroAbVarAt_charZero_of_cartier (hC : AVGlue.CartierSmooth) (h1 : PicLocFinType)
    (h2 : IdentityComponentLFT) (h3b : KleimanPicZeroProper) (K : Type) [Field K] [CharZero K] :
    PicZeroAbVarAt K :=
  picZeroAbVarAt_of h1 h2 K (picZeroSmoothAt_charZero hC h1 K) (picZeroProperAt_of_kleiman h3b K)

/-- **`PicZeroAbVar` at every field of characteristic `0` from the three LEAF statements alone** (Cartier's
theorem is `cartierSmooth_proof`). -/
theorem picZeroAbVarAt_charZero (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3b : KleimanPicZeroProper)
    (K : Type) [Field K] [CharZero K] : PicZeroAbVarAt K :=
  picZeroAbVarAt_charZero_of_cartier ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof h1 h2 h3b K

/-! ## Positive characteristic: the remaining statement -/

/-- **GLUE, pending reading (Z3a in characteristic `p > 0`: `Pic⁰_{A/K}` is smooth).** `PicDict.PicZeroSmooth`
restricted to fields of characteristic `p > 0`, a consequence of it (never stronger). Cartier's theorem does not
apply. Sources: Mumford, *Abelian varieties*, §13 (over `k̄`: `Â = Pic⁰`, `dim Â = h¹(𝒪_A) = g`, `Â` smooth),
with the identification of Mumford's `Â` with the identity component of the fppf `Pic_{A/K}` and descent from
`K̄` (Kleiman 9.5.1); one print over an arbitrary field (BLR 8.4, FGA Explained 9.5, Milne 1986 §10) still to be
read. Locators UNVERIFIED. -/
def PicZeroSmoothPosChar : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p], PicZeroSmoothAt K

/-- **`PicZeroSmooth` from Cartier's theorem, `PicLocFinType` and the positive-characteristic case.** -/
theorem picZeroSmooth_of_cartier (hC : AVGlue.CartierSmooth) (h1 : PicLocFinType)
    (hp : PicZeroSmoothPosChar) : PicZeroSmooth := by
  rw [picZeroSmooth_iff]
  intro K _
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hpr | h0
  · haveI : Fact (ringChar K).Prime := ⟨hpr⟩
    exact hp K (ringChar K)
  · haveI : CharP K 0 := h0 ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    exact picZeroSmoothAt_charZero hC h1 K

/-- **Main result (`PicZeroAbVar`)** from Kleiman 9.4.8 (`PicLocFinType`), SGA 3 VI_A 2.4
(`IdentityComponentLFT`), Kleiman 9.5.4 in its printed form, Cartier's theorem (a hypothesis here) and
`PicZeroSmoothPosChar` (pending reading). -/
theorem picZeroAbVar_of_cartier (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (hC : AVGlue.CartierSmooth)
    (hp : PicZeroSmoothPosChar) (h3b : KleimanPicZeroProper) : PicZeroAbVar :=
  picZeroAbVar_of_printed h1 h2 (picZeroSmooth_of_cartier hC h1 hp) h3b

/-- **Main result (`PicZeroAbVar`)**, Cartier's theorem supplied by `cartierSmooth_proof`: from the three LEAF
statements and `PicZeroSmoothPosChar` (pending reading). -/
theorem picZeroAbVar_of_printed2 (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
    (hp : PicZeroSmoothPosChar) (h3b : KleimanPicZeroProper) : PicZeroAbVar :=
  picZeroAbVar_of_cartier h1 h2 ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof hp h3b

end PicSmooth
