import ZInQKernel.Contrib.OneProof.SZThm33.TateLevelSurjectivity
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsAbelianImage

/-! A group homomorphism whose image contains all prime-power torsion in an
abelian variety over an algebraically closed field is dominant. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Topology
open ZInQ.HeightSplit ZInQ.SemiAbDescend ZInQ.FaltingsRestate
open ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open scoped IsMulCommutative

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

namespace SZRaynaud

/-- A finite-dimensional irreducible space admits no closed embedding of
equal dimension with proper image. -/
theorem surjective_of_isClosedEmbedding_of_krullDim_ge
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IrreducibleSpace Y]
    {f : X → Y} (hf : IsClosedEmbedding f) (d : ℕ)
    (hX : (d : WithBot ℕ∞) ≤ topologicalKrullDim X)
    (hY : topologicalKrullDim Y = (d : WithBot ℕ∞)) :
    Function.Surjective f := by
  by_contra h
  obtain ⟨y, hy⟩ := not_forall.mp h
  obtain ⟨s, hs⟩ := Order.le_krullDim_iff.mp hX
  let m := IrreducibleCloseds.map f hf.continuous
  let t := s.map m (IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing)
  let U : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have hsub : (t.last : Set Y) ⊆ Set.range f := by
    rw [show t.last = m s.last from LTSeries.last_map ..]
    change closure (f '' (s.last : Set X)) ⊆ Set.range f
    exact closure_minimal (Set.image_subset_range _ _) hf.isClosed_range
  have hlt : t.last < U := by
    refine lt_of_le_of_ne (Set.subset_univ _) ?_
    intro he
    apply hy
    exact hsub (show y ∈ (t.last : Set Y) by rw [he]; exact Set.mem_univ y)
  let l := t.snoc U hlt
  have hl : l.length = d + 1 := by simp [l, t, hs]
  have hle : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Y :=
    Order.le_krullDim_iff.mpr ⟨l, hl⟩
  rw [hY, Nat.cast_le] at hle
  omega

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- An injective point homomorphism containing each level of a tower lifts
the tower uniquely, so containment of all prime-power torsion gives
surjectivity on integral Tate modules. -/
theorem surjective_tate_map_of_injective_of_torsion_range
    {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) (hf : Function.Injective f)
    (h : ∀ (n : ℕ) (z : N), ℓ ^ n • z = 0 → z ∈ f.range) :
    Function.Surjective (PkgI3.Tate.map (ℓ := ℓ) f) := by
  classical
  intro t
  choose y hy using fun n : ℕ => h n (t.1 n) (pow_smul_tate t n)
  have hz : y 0 = 0 := hf ((hy 0).trans (t.2.1.trans (map_zero f).symm))
  have hstep (n : ℕ) : ℓ • y (n + 1) = y n := by
    apply hf
    rw [map_nsmul, hy, hy]
    exact t.2.2 n
  refine ⟨⟨y, hz, hstep⟩, Subtype.ext ?_⟩
  funext n
  exact hy n

/-- A finite quotient of point groups disappears on taking the Tate module. -/
theorem surjective_tate_map_of_finite_quotient
    {M N : Type} [CommGroup M] [CommGroup N]
    (f : M →* N) (hf : Function.Injective f) [Finite (N ⧸ f.range)] :
    Function.Surjective (PkgI3.Tate.map (ℓ := ℓ) f.toAdditive) := by
  classical
  let q := QuotientGroup.mk' f.range
  intro t
  have hq := tate_eq_zero_of_finite (PkgI3.Tate.map (ℓ := ℓ) q.toAdditive t)
  have hx (n : ℕ) : Additive.toMul (t.1 n) ∈ f.range := by
    apply (QuotientGroup.eq_one_iff (N := f.range) _).mp
    exact congrArg (fun t : PkgI3.Tate.T ℓ (Additive (N ⧸ f.range)) =>
      Additive.toMul (t.1 n)) hq
  choose y hy using hx
  have hz : y 0 = 1 := by
    apply hf
    rw [hy, map_one]
    exact t.2.1
  have hstep (n : ℕ) : y (n + 1) ^ ℓ = y n := by
    apply hf
    rw [map_pow, hy, hy]
    exact t.2.2 n
  refine ⟨⟨fun n => Additive.ofMul (y n), hz, hstep⟩, Subtype.ext ?_⟩
  funext n
  exact congrArg Additive.ofMul (hy n)

variable {k : Type} [Field k] [IsAlgClosed k]

private def algPtUnitIso : algPt k k ≅ (𝟙_ (Over (Spec (CommRingCat.of k)))) :=
  Over.isoMk (Iso.refl _) (by simp [algPt])

omit [IsAlgClosed k] in
private theorem isCommMonObj_of_mono_group
    {X Y : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (i : X ⟶ Y) [IsMonHom i] [Mono i] :
    IsCommMonObj X := by
  apply (isCommMonObj_iff_isMulCommutative X).mpr
  intro T
  refine ⟨⟨fun x y => (cancel_mono i).mp ?_⟩⟩
  rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

omit [IsAlgClosed k] in
private theorem pointMap_injective {X Y : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj Y]
    (P : (Over (Spec (CommRingCat.of k)))) (i : X ⟶ Y) [Mono i] [IsMonHom i] :
    Function.Injective (mapGroupPoint (P := P) i) :=
  fun _ _ h => (cancel_mono i).mp h

set_option backward.isDefEq.respectTransparency false in
/-- A closed subgroup of an abelian variety containing all of its prime-power
torsion is surjective on the underlying space. -/
theorem surjective_closedGroup_of_primary_torsion
    (B : PkgI3.AbVar k) (b : ℕ) (hb : B.dim = (b : WithBot ℕ∞))
    (hℓ : (ℓ : k) ≠ 0) (G : (Over (Spec (CommRingCat.of k)))) [GrpObj G]
    (i : G ⟶ B.X) [IsClosedImmersion i.left] [IsMonHom i]
    (ht : ∀ (n : ℕ) (x : algPt k k ⟶ B.X), x ^ ℓ ^ n = 1 →
      x ∈ (mapGroupPoint (P := algPt k k) i).range) :
    Function.Surjective i.left := by
  haveI : Mono i := Over.mono_of_mono_left i
  haveI : IsCommMonObj G := isCommMonObj_of_mono_group i
  haveI : IsProper G.hom := by rw [← Over.w i]; infer_instance
  letI : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  let L := relativeGroupLawOfGrpObj k G.hom
  obtain ⟨X, j₀, L₀, n, hj, _, hsm, hgi, _, _, hdim, hmul, _, reps, hRepFin, hRep⟩ :=
    L.exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField k
  let G₀ : (Over (Spec (CommRingCat.of k))) := Over.mk (j₀ ≫ G.hom)
  let j : G₀ ⟶ G := Over.homMk j₀ rfl
  letI : GrpObj G₀ := L₀.grpObjOverMk
  haveI : IsClosedImmersion j.left := hj
  haveI : IsClosedImmersion j₀ := hj
  haveI : Mono j := Over.mono_of_mono_left j
  haveI : IsMonHom j := isMonHom_of_relativeGroupLaw_mul G G₀ L₀ j hmul
  haveI : IsCommMonObj G₀ := isCommMonObj_of_mono_group j
  haveI : SmoothOfRelativeDimension n G₀.hom := hsm
  haveI : Smooth G₀.hom := SmoothOfRelativeDimension.smooth (n := n) G₀.hom
  haveI : IsProper G₀.hom := show IsProper (j₀ ≫ G.hom) by infer_instance
  haveI : GeometricallyIrreducible G₀.hom := hgi
  haveI : GeometricallyReduced G₀.hom := by
    refine ⟨fun K _ y Z fst snd h => ?_⟩
    haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
    exact ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.isReduced_of_smooth_of_field snd
  haveI : GeometricallyIntegral G₀.hom := by
    rw [GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible]
    exact ⟨inferInstance, inferInstance⟩
  let A : PkgI3.AbVar k :=
    { X := G₀, grp := inferInstance, proper := inferInstance, smooth := inferInstance,
      geomInt := inferInstance }
  -- The finite component representatives still act on the field-valued point group.
  let P := algPt k k
  let repsToUnit : reps → ((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G) := fun x =>
    (overHomEquivSchemeHomOver (𝟙_ (Over (Spec (CommRingCat.of k)))) G.hom).symm x.1
  let v : reps × ((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G₀) → ((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G) := fun a => repsToUnit a.1 * (a.2 ≫ j)
  haveI : Finite reps := hRepFin
  have hv : Function.Surjective v := by
    intro z
    let e := overHomEquivSchemeHomOver (𝟙_ (Over (Spec (CommRingCat.of k)))) G.hom
    let e₀ := overHomEquivSchemeHomOver (𝟙_ (Over (Spec (CommRingCat.of k)))) G₀.hom
    obtain ⟨s, hs, a, ha⟩ := hRep (e z)
    refine ⟨(⟨s, hs⟩, e₀.symm a), ?_⟩
    apply e.injective
    change e (repsToUnit ⟨s, hs⟩ * (e₀.symm a ≫ j)) = e z
    rw [ha]
    apply Subtype.ext
    rfl
  let repsToPt (s : reps) : P ⟶ G := algPtUnitIso.hom ≫ repsToUnit s
  have hvP (z : P ⟶ G) : ∃ (s : reps) (t : P ⟶ G₀), repsToPt s * (t ≫ j) = z := by
    obtain ⟨⟨s, a⟩, ha⟩ := hv (algPtUnitIso.inv ≫ z)
    refine ⟨s, algPtUnitIso.hom ≫ a, ?_⟩
    have eq := congrArg (algPtUnitIso.hom ≫ ·) ha
    rw [Iso.hom_inv_id_assoc] at eq
    change algPtUnitIso.hom ≫ (repsToUnit s * (a ≫ j)) = z at eq
    rw [MonObj.comp_mul, ← Category.assoc] at eq
    exact eq
  let jPts := mapGroupPoint (P := P) j
  let iPts := mapGroupPoint (P := P) i
  let C := jPts.range
  let q := QuotientGroup.mk' C
  haveI : Finite ((P ⟶ G) ⧸ C) := by
    apply Finite.of_surjective (fun s : reps => q (repsToPt s))
    intro a
    obtain ⟨z, rfl⟩ := Quotient.exists_rep a
    obtain ⟨s, t, hst⟩ := hvP z
    refine ⟨s, ?_⟩
    change q (repsToPt s) = q z
    rw [← hst]
    change q (repsToPt s) = q (repsToPt s * jPts t)
    have hqt : q (jPts t) = 1 := (QuotientGroup.eq_one_iff (N := C) _).mpr ⟨t, rfl⟩
    rw [map_mul, hqt, _root_.mul_one]
  have hjT := surjective_tate_map_of_finite_quotient (ℓ := ℓ) jPts (pointMap_injective P j)
  have hiT := surjective_tate_map_of_injective_of_torsion_range (ℓ := ℓ) iPts.toAdditive
    (pointMap_injective P i) (fun m x hx => ht m (Additive.toMul x) hx)
  let f := (PkgI3.Tate.map (ℓ := ℓ) iPts.toAdditive).comp
    (PkgI3.Tate.map (ℓ := ℓ) jPts.toAdditive)
  have hf : Function.Surjective f := hiT.comp hjT
  obtain ⟨eA⟩ := T5Torsion.TateFree.tate_linearEquiv _
    (card_torsion_abelian_algClosed (ℓ := ℓ) A n · hdim hℓ)
  obtain ⟨eB⟩ := T5Torsion.TateFree.tate_linearEquiv _
    (card_torsion_abelian_algClosed (ℓ := ℓ) B b · hb hℓ)
  let F := eB.toLinearMap.comp (f.comp eA.symm.toLinearMap)
  have hF : Function.Surjective F := eB.surjective.comp (hf.comp eA.symm.surjective)
  have hdimle := LinearMap.finrank_le_finrank_of_surjective hF
  have hbn : b ≤ n := by
    simp only [Module.finrank_fin_fun] at hdimle
    omega
  haveI : IrreducibleSpace B.X.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton B.X.hom
  let g := j.left ≫ i.left
  haveI : IsClosedImmersion g := inferInstanceAs (IsClosedImmersion (j.left ≫ i.left))
  have hsur := surjective_of_isClosedEmbedding_of_krullDim_ge g.isClosedEmbedding b
    (hdim ▸ Nat.cast_le.mpr hbn) hb
  intro z
  obtain ⟨x, hx⟩ := hsur z
  exact ⟨j.left x, hx⟩

end SZRaynaud

#print axioms SZRaynaud.surjective_of_isClosedEmbedding_of_krullDim_ge
#print axioms SZRaynaud.surjective_tate_map_of_injective_of_torsion_range
#print axioms SZRaynaud.surjective_tate_map_of_finite_quotient
#print axioms SZRaynaud.surjective_closedGroup_of_primary_torsion
