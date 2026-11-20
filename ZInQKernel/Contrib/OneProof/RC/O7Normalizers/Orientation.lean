import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Local
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Transport

/-! Transport the local labels through the chosen adelic representatives. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Normalizers

open Adelic Eichler ThetaJoin O7Actual O7Orbits LocalWeights

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D : ℤ}
variable (s : StageAt O N M hN m) (H : SupportBridge s D)

abbrev generator (P : ActualPoint s (D := D)) (q : Prime) :
    (ActualOrder s).completion q.val := ⟨atRep P.z q P.y, P.integral q⟩

theorem generator_rel {P Q : ActualPoint s (D := D)}
    (W : (pointRel _ _).r P Q) (q : Prime) :
    ∃ u : ((ActualOrder s).completion q.val)ˣ,
      generator s Q q = unitConjRing u⁻¹ (generator s P q) := by
  obtain ⟨r, hr⟩ := pointRel_atRep W q
  exact ⟨completedUnit q r, Subtype.ext hr⟩

theorem label_rel {P Q : ActualPoint s (D := D)} (W : (pointRel _ _).r P Q) (q : Prime)
    {A : Type*} [CommRing A] (f : (ActualOrder s).completion q.val →+* A) :
    f (generator s Q q) = f (generator s P q) := by
  obtain ⟨u, hu⟩ := generator_rel s W q
  rw [hu, unitConjRing_apply, map_mul, map_mul, mul_right_comm,
    ← map_mul, inv_inv, Units.inv_mul, map_one, one_mul]

abbrev splitLabel (i : Fin N.primeFactors.card) :=
  (level (levelPrime N i).val (N.factorization (levelPrime N i).val)).comp
    (splitOrderChart s (levelPrime N i) (levelPrime_ne_detecting s i)).toRingHom

abbrev divisionLabel :=
  letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  (LocalDivision.red (p := s.ell)).comp (divisionOrderChart s).toRingHom

def pointOrientation (P : ActualPoint s (D := D)) : Orientations N.primeFactors.card :=
  Fin.lastCases
    (let r := divisionLabel s (2 * generator s P (detectingPrime s.ell) - 1)
     residueBit r (-r))
    (fun j => let r := splitLabel s j (generator s P (levelPrime N j))
              residueBit r (1-r))

theorem pointOrientation_rel {P Q : ActualPoint s (D := D)} (W : (pointRel _ _).r P Q) :
    pointOrientation s Q = pointOrientation s P := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [pointOrientation, Fin.lastCases_last, map_sub, map_mul, map_ofNat, map_one]
    rw [label_rel s W (detectingPrime s.ell) (divisionLabel s)]
  · simp only [pointOrientation, Fin.lastCases_castSucc]
    rw [label_rel s W _ (splitLabel s j)]

theorem pointOrientation_actual (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    pointOrientation s (pointOfSupport s H z x) =
      orientation s H ⟨z, Quotient.mk _ x⟩ := rfl

theorem levelPrime_injective (N : ℕ) : Function.Injective (levelPrime N) := by
  intro i j h
  apply (N.primeFactors.orderIsoOfFin rfl).injective
  exact Subtype.ext (congrArg (fun p : Prime => p.val) h)

abbrev splitAdele (i : Fin N.primeFactors.card) : FiniteUnits (ActualOrder s) :=
  single _ (levelPrime N i) (splitUnit (N := N) s.mod_four _ (levelPrime_ne_detecting s i))

abbrev divisionAdele : FiniteUnits (ActualOrder s) :=
  single _ (detectingPrime s.ell) (divisionUnit s.mod_four)

theorem splitAdele_order (i : Fin N.primeFactors.card) : PreservesOrder (splitAdele s i) :=
  preservesOrder_single _ _ (splitUnit_mem s.mod_four hN _ (levelPrime_ne_detecting s i))

theorem divisionAdele_order : PreservesOrder (divisionAdele s) :=
  preservesOrder_single _ _ (divisionUnit_mem s.mod_four hN)

theorem generator_away (q : Prime) {p : Prime}
    (v : (Bp p.val (-1) (-(s.ell : ℚ)))ˣ)
    (hk : PreservesOrder (single (ActualOrder s) p v)) (hq : q ≠ p)
    (P : ActualPoint s (D := D)) :
    generator s (stepPoint _ hk P) q = generator s P q := by
  apply Subtype.ext
  change atRep (P.z * single _ p v) q P.y = atRep P.z q P.y
  rw [atRep_right, single_away hq]
  simp

theorem splitAdele_chart (i : Fin N.primeFactors.card) (P : ActualPoint s (D := D)) :
    let q := levelPrime N i
    let f := splitOrderChart s q (levelPrime_ne_detecting s i)
    f (generator s (stepPoint _ (splitAdele_order s i) P) q) =
      splitSwap q (N.factorization q.val) (f (generator s P q)) := by
  let q := levelPrime N i
  let hq := levelPrime_ne_detecting s i
  let f := splitOrderChart s q hq
  let F := splitChart s.ell s.mod_four q hq
  change f _ = splitSwap q _ (f _)
  apply Subtype.ext
  apply Matrix.map_injective (show Function.Injective (algebraMap ℤ_[q.val] ℚ_[q.val]) from Subtype.val_injective)
  change matrixCast q.val (f _).val = matrixCast q.val (splitSwap q _ (f _)).val
  rw [splitOrderChart_compatible, splitSwap_cast, splitOrderChart_compatible]
  change F (atRep (P.z * splitAdele s i) q P.y) = _
  rw [atRep_right, single_same]
  change F (rightConj _ _) = _
  have hmap := map_rightConj F.toRingHom
    (splitUnit (N := N) s.mod_four q hq) (atRep P.z q P.y)
  change F (rightConj _ _) = _ at hmap
  rw [hmap]
  have hu := splitUnit_chart (N := N) s.mod_four q hq
  change Units.map F.toRingHom.toMonoidHom _ = _ at hu
  rw [hu]
  rfl

private theorem orderChart_cast {p : ℕ} [Fact p.Prime] (h : p % 4 = 3)
    {S : Subalgebra ℤ_[p] (DivisionJoin.LocalB p)}
    (hS : S = DivisionJoin.completedOrder p h) (y : S) :
    (((Subalgebra.equivOfEq _ _ hS).toRingEquiv.trans
      (DivisionJoin.orderEquiv p h).toRingEquiv) y).val =
        DivisionJoin.ambientEquiv p y.val :=
  (DivisionJoin.order_compatible p h (Subalgebra.equivOfEq _ _ hS y)).symm

theorem divisionOrderChart_compatible (y : (ActualOrder s).completion s.ell) :
    (divisionOrderChart s y).val = DivisionJoin.ambientEquiv s.ell y.val := by
  let p : Adelic.Prime := ⟨s.ell, Fact.out⟩
  have h : (ActualOrder s).completion s.ell = DivisionJoin.completedOrder s.ell s.mod_four := by
    change (ActualOrder s).completion p.val = _
    rw [Adelic.levelOrder_completion, Adelic.levelLocal, dite_eq_right (not_not.mpr rfl)]
  exact orderChart_cast s.mod_four h y

theorem divisionAdele_chart (P : ActualPoint s (D := D)) :
    letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
    let q := detectingPrime s.ell
    divisionOrderChart s (generator s (stepPoint _ (divisionAdele_order s) P) q) =
      LocalDivision.uniformizerOrder (divisionOrderChart s (generator s P q)) := by
  letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  let q := detectingPrime s.ell
  apply Subtype.ext
  rw [divisionOrderChart_compatible, LocalDivision.uniformizer_conj, divisionOrderChart_compatible]
  change DivisionJoin.ambientEquiv s.ell (atRep (P.z * divisionAdele s) q P.y) = _
  rw [atRep_right, single_same]
  change DivisionJoin.ambientEquiv s.ell (rightConj _ _) = _
  let F := DivisionJoin.ambientEquiv s.ell
  have hmap := map_rightConj F.toRingHom (divisionUnit s.mod_four) (atRep P.z q P.y)
  change F (rightConj _ _) = _ at hmap
  rw [hmap]
  have hu := divisionUnit_chart s.mod_four
  change Units.map F.toRingHom.toMonoidHom _ = _ at hu
  rw [hu]
  rfl

theorem splitLabel_distinct (i : Fin N.primeFactors.card)
    (hd : disc s D ≠ 0) (h8 : disc s D % 8 = 1)
    (hs : Nonvanishing.SplitsIn (disc s D) (levelPrime N i).val)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    let r := splitLabel s i (generator s (pointOfSupport s H z x) (levelPrime N i))
    r ≠ 1-r := by
  let q := levelPrime N i
  let e := N.factorization q.val
  let c := (1 - disc s D) / 4
  have hc : disc s D = 1 - 4 * c := by dsimp [c]; omega
  obtain ⟨a, ha, hu⟩ := split_branch_of_splitsIn hc hs
  obtain ⟨ht, hd'⟩ := split_generator_trace_det s H hc hd q (levelPrime_ne_detecting s i) z x
  let X := splitOrderChart s q (levelPrime_ne_detecting s i) (localGenerator s H z x q)
  let f := PadicInt.toZModPow (p := q.val) e
  have he : 0 < e := levelPrime_exp hN i
  have hsep : f a ≠ 1 - f a := by
    obtain ⟨A, B, _, _, _, _, hA, hB, hn⟩ := split_level_labels he a hu
    simpa only [hA, hB, map_sub, map_one] using hn
  change level q.val e X ≠ 1 - level q.val e X
  rcases split_level_residue_cases he X ht hu (hd'.symm ▸ ha) with hr | hr
  · simpa only [hr] using hsep
  · rw [hr, map_sub, map_one, sub_sub_cancel]
    exact hsep.symm

theorem divisionRoot_trace (P : ActualPoint s (D := D)) :
    letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
    LocalDivision.tr (divisionOrderChart s (2 * generator s P (detectingPrime s.ell) - 1)).val = 0 := by
  letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  rw [divisionOrderChart_compatible, DivisionJoin.ambient_trace]
  let q := detectingPrime s.ell
  change DivisionJoin.reducedTrace s.ell (2 * atRep P.z q P.y - 1) = 0
  rw [← atRep_root P.z q P.y, DivisionJoin.reducedTrace, atRep_re, P.trace_zero, Rat.cast_zero, mul_zero]

theorem divisionLabel_distinct (hd : ((disc s D : ℤ) : ZMod s.ell) ≠ 0)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    let r := divisionLabel s (2 * generator s (pointOfSupport s H z x) (detectingPrime s.ell) - 1)
    r ≠ -r := by
  letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  let X := divisionGenerator s H z x
  let f := LocalDivision.red (p := s.ell)
  have hh := division_red_ne_zero_of_sq hd (divisionGenerator_square s H z x)
  obtain ⟨hn, _⟩ := division_labels X hh
  have hf : f (-X) = -(f X) := (LocalDivision.red (p := s.ell)).map_neg X
  change f X ≠ -(f X)
  rw [← hf]
  exact hn.symm

theorem residueBit_flip {A : Type*} [Finite A] {x y : A} (h : x ≠ y) :
    residueBit y x = !residueBit x y := by
  have hh := residueBit_swap_ne h
  cases hx : residueBit x y <;> cases hy : residueBit y x <;> simp_all

/-- The split operation changes just the corresponding level bit. -/
theorem split_orientation (i : Fin N.primeFactors.card)
    (hd : disc s D ≠ 0) (h8 : disc s D % 8 = 1)
    (hs : Nonvanishing.SplitsIn (disc s D) (levelPrime N i).val)
    (P : OrbitSet s.visibility (index s D)) :
    orientation s H (orbitMove s H _ (splitAdele_order s i) P) =
      O7Actual.flip i.castSucc (orientation s H P) := by
  obtain ⟨z, x⟩ := P
  induction x using Quotient.inductionOn with
  | _ x =>
    generalize hy : orbitMove s H _ (splitAdele_order s i) ⟨z, Quotient.mk _ x⟩ = Q
    obtain ⟨w, y⟩ := Q
    induction y using Quotient.inductionOn with
    | _ y =>
      change ClassSet (ActualOrder s) at z w
      rw [← pointOrientation_actual s H w y, ← pointOrientation_actual s H z x,
        pointOrientation_rel s (orbitMove_rel s H _ _ z x w y hy)]
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [O7Actual.flip, Function.update_of_ne (Fin.castSucc_ne_last i).symm]
        simp only [pointOrientation, Fin.lastCases_last]
        have haw : detectingPrime s.ell ≠ levelPrime N i := by
          intro he
          exact levelPrime_ne_detecting s i (congrArg (fun p : Prime => p.val) he.symm)
        rw [generator_away s (detectingPrime s.ell) _ _ haw _]
      · by_cases hj : j = i
        · subst j
          simp only [pointOrientation, Fin.lastCases_castSucc, O7Actual.flip, Function.update_self]
          let q := levelPrime N i
          let e := N.factorization q.val
          let f := splitOrderChart s q (levelPrime_ne_detecting s i)
          let P := pointOfSupport s H z x
          have he : f (generator s (stepPoint _ (splitAdele_order s i) P) q) =
              splitSwap q e (f (generator s P q)) := splitAdele_chart s i P
          change residueBit (level q.val e (f (generator s (stepPoint _ (splitAdele_order s i) P) q)))
            (1 - level q.val e (f (generator s (stepPoint _ (splitAdele_order s i) P) q))) = !_
          have ht : (f (generator s P q)).val.trace = 1 :=
            (split_generator_trace_det s H (c := (1 - disc s D) / 4)
              (by omega) hd q (levelPrime_ne_detecting s i) z x).1
          rw [he, splitSwap_level q e (f (generator s P q)) ht, sub_sub_cancel]
          exact residueBit_flip (splitLabel_distinct s H i hd h8 hs z x)
        · have hji : j.castSucc ≠ i.castSucc := fun he => hj (Fin.castSucc_inj.mp he)
          rw [O7Actual.flip, Function.update_of_ne hji]
          simp only [pointOrientation, Fin.lastCases_castSucc]
          have haw : levelPrime N j ≠ levelPrime N i :=
            fun he => hj (levelPrime_injective N he)
          rw [generator_away s (levelPrime N j) _ _ haw _]

private theorem affine_map {A B : Type*} [Ring A] [Ring B] (f : A →+* B) (x : A) :
    f (2 * x - 1) = 2 * f x - 1 := by rw [map_sub, map_mul, map_ofNat, map_one]

/-- The division operation changes just the detecting bit. -/
theorem division_orientation (hd : ((disc s D : ℤ) : ZMod s.ell) ≠ 0)
    (P : OrbitSet s.visibility (index s D)) :
    orientation s H (orbitMove s H _ (divisionAdele_order s) P) =
      O7Actual.flip (Fin.last _) (orientation s H P) := by
  letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  obtain ⟨z, x⟩ := P
  induction x using Quotient.inductionOn with
  | _ x =>
    generalize hy : orbitMove s H _ (divisionAdele_order s) ⟨z, Quotient.mk _ x⟩ = Q
    obtain ⟨w, y⟩ := Q
    induction y using Quotient.inductionOn with
    | _ y =>
      change ClassSet (ActualOrder s) at z w
      rw [← pointOrientation_actual s H w y, ← pointOrientation_actual s H z x,
        pointOrientation_rel s (orbitMove_rel s H _ _ z x w y hy)]
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [pointOrientation, Fin.lastCases_last, O7Actual.flip, Function.update_self]
        change residueBit (LocalDivision.red (divisionOrderChart s _))
          (-LocalDivision.red (divisionOrderChart s _)) = !_
        have he : divisionOrderChart s (2 * generator s
            (stepPoint _ (divisionAdele_order s) (pointOfSupport s H z x)) (detectingPrime s.ell) - 1) =
            LocalDivision.uniformizerOrder
              (divisionOrderChart s (2 * generator s (pointOfSupport s H z x) (detectingPrime s.ell) - 1)) := by
          let f := (divisionOrderChart s).toRingHom
          let g := (LocalDivision.uniformizerOrder (p := s.ell)).toRingHom
          let P := pointOfSupport s H z x
          let q := detectingPrime s.ell
          have hg : f (generator s (stepPoint _ (divisionAdele_order s) P) q) =
              g (f (generator s P q)) := divisionAdele_chart s P
          change f (2 * generator s (stepPoint _ (divisionAdele_order s) P) q - 1) =
            g (f (2 * generator s P q - 1))
          exact (affine_map f _).trans
            ((congrArg (fun y : LocalDivision.order s.ell => 2 * y - 1) hg).trans
              ((affine_map g (f (generator s P q))).symm.trans
                (congrArg g (affine_map f (generator s P q)).symm)))
        rw [he, division_red_neg _ (divisionRoot_trace s _), neg_neg]
        exact residueBit_flip (divisionLabel_distinct s H hd z x)
      · rw [O7Actual.flip, Function.update_of_ne (Fin.castSucc_ne_last j)]
        simp only [pointOrientation, Fin.lastCases_castSucc]
        have haw : levelPrime N j ≠ detectingPrime s.ell := by
          intro he
          exact levelPrime_ne_detecting s j (congrArg (fun p : Prime => p.val) he)
        rw [generator_away s (levelPrime N j) _ _ haw _]

end ZInQ.Manuscript.RC.O7Normalizers
