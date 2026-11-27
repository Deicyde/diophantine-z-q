import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ProperSmooth
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# The torsion leaf from Milne, Prop. 20.7 (draft)

The leaf `TorsionRep 5` is reduced to the printed statement `MilneProp207 5`: multiplication by
`5` on a false elliptic curve over a `Z[1/30]`-scheme is finite and etale.

The `n`-torsion is the fibre `W` of `ι(n)` over the zero section, with `j : W ⟶ A` the first
projection of the pullback.

1. `j` is a closed immersion: it is the base change of the zero section, and a section of the
   separated structure map is a closed immersion (Stacks, tag 01KT).
2. `j ≫ π` is the second projection `W ⟶ S`, the base change of `ι(n)` along the zero section,
   hence finite and etale.
3. A point `P` factors through `j` exactly when `P ≫ ι(n)` is the zero point over `P ≫ π`, that
   is, when `P` is killed by `n` (by `comp_iotaHom_natCast`).
-/

attribute [local instance] FEC.grp

/-- Leaf (Milne, Prop. 20.7). For a false elliptic curve `A` over a `Z[1/30]`-scheme `S`, the
endomorphism `ι(n)` of `A` is finite and etale. The leaf is used at `n = 3` and `n = 5`.

`ι(n)` is multiplication by `n` on `A`: by `iotaHom_natCast`, `Over.homMk (ι n) _ = (𝟙 A.F) ^ n`
in the hom-monoid of `A.F`, which is the `n`-th power map `n_A`.

Source: J. S. Milne, *Abelian Varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic
Geometry*, Springer (1986), Section 20, Prop. 20.7 (p. 44 of the author's retyped edition; the
page in the 1986 printing is not verified). Its text, with subscripts and exponents transcribed:
"Let A be an abelian scheme of relative dimension g over S, and let n_A be multiplication by n
on A. Then n_A is flat, surjective, and finite, and its kernel A_n is a finite flat group scheme
over S of order n^{2g}. Moreover n_A (and therefore its kernel) is étale if and only if n is not
divisible by any of the characteristics of the residue fields of S."

Here `A` is an abelian scheme of relative dimension 2 over `S`: a proper smooth group scheme
with connected geometric fibres (ibid., Section 20, p. 42). On a `Z[1/30]`-scheme no residue
characteristic divides 3 or 5, so the etale part applies at both values used. -/
def MilneProp207 (n : ℕ) : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left),
    AlgebraicGeometry.IsFinite (A.iota (n : O)) ∧ AlgebraicGeometry.Etale (A.iota (n : O))

section Torsion

variable {S : Scheme.{0}} (A : FEC S)

/-- The zero section of `A`: the underlying map of the unit `𝟙_ (Over S) ⟶ A.F`. -/
def torsZeroL : S ⟶ A.F.left :=
  (MonObj.one : 𝟙_ (Over S) ⟶ A.F).left

theorem torsZeroL_sec : torsZeroL A ≫ A.F.hom = 𝟙 S :=
  Over.w (MonObj.one : 𝟙_ (Over S) ⟶ A.F)

theorem torsToUnit_left (U : Over S) : (toUnit U).left = U.hom := by
  first
    | rfl
    | exact Over.toUnit_left U
    | simpa using Over.w (toUnit U)

/-- The zero section is a monomorphism: it has the retraction `A.F.hom`. -/
theorem torsZeroL_mono : Mono (torsZeroL A) := by
  constructor
  intro Z a b hab
  have h := congrArg (fun k => k ≫ A.F.hom) hab
  simpa only [Category.assoc, torsZeroL_sec, Category.comp_id] using h

/-- The zero section is a closed immersion: it is a section of the separated morphism
`A.F.hom` (Stacks, tag 01KT). -/
theorem torsZeroL_isClosedImmersion : IsClosedImmersion (torsZeroL A) := by
  haveI hsep : AlgebraicGeometry.IsSeparated A.F.hom := by
    haveI := A.proper
    infer_instance
  haveI hc : IsClosedImmersion (torsZeroL A ≫ A.F.hom) := by
    rw [torsZeroL_sec A]
    infer_instance
  first
    | exact IsClosedImmersion.of_comp (torsZeroL A) A.F.hom
    | (haveI hp : IsProper (torsZeroL A ≫ A.F.hom) :=
          ((IsClosedImmersion.iff_isProper_and_mono (torsZeroL A ≫ A.F.hom)).1 hc).1
       exact (IsClosedImmersion.iff_isProper_and_mono (torsZeroL A)).2
         ⟨IsProper.of_comp (torsZeroL A) A.F.hom, torsZeroL_mono A⟩)

/-- On the fibre of `ι(n)` over the zero section, `j ≫ π` is the second projection. -/
theorem torsFst_hom (n : ℕ) :
    pullback.fst (A.iota (n : O)) (torsZeroL A) ≫ A.F.hom =
      pullback.snd (A.iota (n : O)) (torsZeroL A) := by
  calc pullback.fst (A.iota (n : O)) (torsZeroL A) ≫ A.F.hom
      = pullback.fst (A.iota (n : O)) (torsZeroL A) ≫ A.iota (n : O) ≫ A.F.hom := by
        rw [A.iota_over]
    _ = (pullback.snd (A.iota (n : O)) (torsZeroL A) ≫ torsZeroL A) ≫ A.F.hom := by
        rw [← Category.assoc, pullback.condition]
    _ = pullback.snd (A.iota (n : O)) (torsZeroL A) := by
        rw [Category.assoc, torsZeroL_sec, Category.comp_id]

/-- `j` is a closed immersion: the base change of the zero section along `ι(n)`. -/
theorem torsFst_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (pullback.fst (A.iota (n : O)) (torsZeroL A)) := by
  have hz : IsClosedImmersion (torsZeroL A) := torsZeroL_isClosedImmersion A
  first
    | exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (IsPullback.of_hasPullback (A.iota (n : O)) (torsZeroL A)).flip hz
    | exact MorphismProperty.pullback_fst (P := @IsClosedImmersion)
        (A.iota (n : O)) (torsZeroL A) hz
    | (haveI := hz; infer_instance)

/-- `j ≫ π` is finite: the base change of `ι(n)` along the zero section. -/
theorem torsFst_hom_isFinite (n : ℕ) (hfin : AlgebraicGeometry.IsFinite (A.iota (n : O))) :
    AlgebraicGeometry.IsFinite (pullback.fst (A.iota (n : O)) (torsZeroL A) ≫ A.F.hom) := by
  rw [torsFst_hom A n]
  first
    | exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsFinite)
        (IsPullback.of_hasPullback (A.iota (n : O)) (torsZeroL A)) hfin
    | exact MorphismProperty.pullback_snd (P := @AlgebraicGeometry.IsFinite)
        (A.iota (n : O)) (torsZeroL A) hfin
    | (haveI := hfin; infer_instance)

/-- `j ≫ π` is etale: the base change of `ι(n)` along the zero section. -/
theorem torsFst_hom_etale (n : ℕ) (het : AlgebraicGeometry.Etale (A.iota (n : O))) :
    AlgebraicGeometry.Etale (pullback.fst (A.iota (n : O)) (torsZeroL A) ≫ A.F.hom) := by
  rw [torsFst_hom A n]
  first
    | exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
        (IsPullback.of_hasPullback (A.iota (n : O)) (torsZeroL A)) het
    | exact MorphismProperty.pullback_snd (P := @AlgebraicGeometry.Etale)
        (A.iota (n : O)) (torsZeroL A) het
    | (haveI := het; infer_instance)

/-- A point `P` is killed by `n` exactly when `P ≫ ι(n)` is the zero point over `P ≫ π`. -/
theorem torsPow_eq_one_iff {T : Scheme.{0}} (P : T ⟶ A.F.left) (n : ℕ) :
    (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ n = 1 ↔
      P ≫ A.iota (n : O) = (P ≫ A.F.hom) ≫ torsZeroL A := by
  have hc := comp_iotaHom_natCast A
    (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) n
  have e1 : ((Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ≫
      (Over.homMk (A.iota (n : O)) (A.iota_over _) : A.F ⟶ A.F)).left =
        P ≫ A.iota (n : O) := rfl
  have e2 : (1 : Over.mk (P ≫ A.F.hom) ⟶ A.F).left =
      (toUnit (Over.mk (P ≫ A.F.hom))).left ≫ torsZeroL A := rfl
  have e3 : (toUnit (Over.mk (P ≫ A.F.hom))).left = P ≫ A.F.hom :=
    torsToUnit_left (Over.mk (P ≫ A.F.hom))
  have e4 : (1 : Over.mk (P ≫ A.F.hom) ⟶ A.F).left = (P ≫ A.F.hom) ≫ torsZeroL A :=
    e2.trans (congrArg (fun t => t ≫ torsZeroL A) e3)
  constructor
  · intro h
    exact e1.symm.trans
      ((congrArg (fun f : Over.mk (P ≫ A.F.hom) ⟶ A.F => f.left) (hc.trans h)).trans e4)
  · intro h
    exact hc.symm.trans (Over.OverMorphism.ext (e1.trans (h.trans e4.symm)))

/-- The fibre of `ι(n)` over the zero section represents the `n`-torsion. -/
theorem torsChar (n : ℕ) (T : Scheme.{0}) (P : T ⟶ A.F.left) :
    (∃ f : T ⟶ pullback (A.iota (n : O)) (torsZeroL A),
        f ≫ pullback.fst (A.iota (n : O)) (torsZeroL A) = P) ↔
      (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ n = 1 := by
  refine Iff.trans ?_ (torsPow_eq_one_iff A P n).symm
  constructor
  · rintro ⟨f, rfl⟩
    calc (f ≫ pullback.fst (A.iota (n : O)) (torsZeroL A)) ≫ A.iota (n : O)
        = f ≫ (pullback.snd (A.iota (n : O)) (torsZeroL A) ≫ torsZeroL A) := by
          rw [Category.assoc, pullback.condition]
      _ = ((f ≫ pullback.fst (A.iota (n : O)) (torsZeroL A)) ≫ A.F.hom) ≫ torsZeroL A := by
          rw [Category.assoc f (pullback.fst (A.iota (n : O)) (torsZeroL A)) A.F.hom,
            torsFst_hom A n, Category.assoc]
  · intro hP
    exact ⟨pullback.lift P (P ≫ A.F.hom) hP, pullback.lift_fst _ _ _⟩

end Torsion

/-- The torsion leaf at `n` from Milne, Prop. 20.7 at `n`. -/
theorem torsionRep_of_milne (n : ℕ) (h : MilneProp207 n) : TorsionRep n :=
  fun S A =>
    ⟨pullback (A.iota (n : O)) (torsZeroL A), pullback.fst (A.iota (n : O)) (torsZeroL A),
      torsFst_isClosedImmersion A n, torsFst_hom_isFinite A n (h S A).1,
      torsFst_hom_etale A n (h S A).2, fun T P => torsChar A n T P⟩

/-- `TorsionRep 5` from Milne, Prop. 20.7 at `n = 5`, which is invertible on `Z[1/30]`. -/
theorem torsionRep5_of_milne (h : MilneProp207 5) : TorsionRep 5 :=
  torsionRep_of_milne 5 h

end Y3Buzzard
