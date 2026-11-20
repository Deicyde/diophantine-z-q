import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Orientation
import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Norm

/-! Separate the local Schwartz and norm multipliers before descending the
product to the actual supported orbits. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Normalizers

open Adelic Eichler ThetaJoin O7Actual O7Orbits Visibility LocalWeights

section Product

variable {O : Type} [CommRing O] {a b : ℚ} {R : Order a b} {n : ℚ}
variable (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (χ : FiniteUnits R →* Oˣ)

def pointWeight (P : AdelicPoint R n) : O :=
  (χ P.z : O) * weightAt A w P.z (root P.y)

theorem pointWeight_rel (C : NormCovariance A w χ) {P Q : AdelicPoint R n}
    (W : (pointRel _ _).r P Q) :
    pointWeight A w χ Q = pointWeight A w χ P := by
  obtain ⟨u, r, hz, hy⟩ := W
  unfold pointWeight
  rw [hz, hy, root_conj]
  exact weightedAt_change A w C.eps C.local_conj χ C.diagonal C.units P.z u r _

theorem stepPoint_schwartz (q : Prime) (v : (Bp q.val a b)ˣ) (hq : q ∈ A.places)
    (hk : PreservesOrder (single R q v)) (P : AdelicPoint R n) (s : O)
    (hs : w q (rightConj v (atRep P.z q (root P.y))) = s * w q (atRep P.z q (root P.y))) :
    weightAt A w (stepPoint _ hk P).z (root (stepPoint _ hk P).y) =
      s * weightAt A w P.z (root P.y) := by
  classical
  let Q := stepPoint _ hk P
  have hi (T : AdelicPoint R n) (p : Prime) : atRep T.z p (root T.y) ∈ R.completion p.val := by
    rw [atRep_root]
    exact (R.completion p.val).sub_mem ((R.completion p.val).mul_mem
      ((R.completion p.val).natCast_mem 2) (T.integral p)) ((R.completion p.val).one_mem)
  rw [weightAt_of_local A w Q.z _ (hi Q), weightAt_of_local A w P.z _ (hi P)]
  let f (p : Prime) := w p (atRep Q.z p (root Q.y))
  let g (p : Prime) := w p (atRep P.z p (root P.y))
  have hq' : f q = s * g q := by
    change w q (atRep (P.z * single R q v) q (root P.y)) = _
    rw [atRep_right, single_same]
    exact hs
  have he : (∏ p ∈ A.places.erase q, f p) = ∏ p ∈ A.places.erase q, g p := by
    apply Finset.prod_congr rfl
    intro p hp
    change w p (atRep (P.z * single R q v) p (root P.y)) = _
    rw [atRep_right, single_away (Finset.mem_erase.mp hp).1]
    simp [g]
  change (∏ p ∈ A.places, f p) = s * ∏ p ∈ A.places, g p
  rw [← Finset.mul_prod_erase A.places f hq, ← Finset.mul_prod_erase A.places g hq, hq', he, mul_assoc]

theorem stepPoint_weight (q : Prime) (v : (Bp q.val a b)ˣ) (hq : q ∈ A.places)
    (hk : PreservesOrder (single R q v)) (P : AdelicPoint R n) (s : O)
    (hs : w q (rightConj v (atRep P.z q (root P.y))) = s * w q (atRep P.z q (root P.y))) :
    pointWeight A w χ (stepPoint _ hk P) =
      ((χ (single R q v) : O) * s) * pointWeight A w χ P := by
  have h := stepPoint_schwartz A w q v hq hk P s hs
  change (χ (P.z * single R q v) : O) * _ = _
  rw [h, map_mul, Units.val_mul]
  unfold pointWeight
  ring

end Product

section Local

variable {O : Type} [CommRing O] {N M m₀ : ℕ} {hN : 0 < N} {m D : ℤ}
variable (s : StageAt O N M hN m) (C : LevelRoots O N)

theorem splitFactor_on_point (i : Fin N.primeFactors.card) (hi : (levelPrime N i).val ∣ N)
    (P : ActualPoint s (D := D))
    (ht : (splitOrderChart s (levelPrime N i) (levelPrime_ne_detecting s i)
      (generator s P (levelPrime N i))).val.trace = 1) :
    let q := levelPrime N i
    let X := splitOrderChart s q (levelPrime_ne_detecting s i) (generator s P q)
    localFactor s.mod_four C m₀ q (atRep P.z q (root P.y)) =
      levelWeight ((C.alpha q hi).comp
        (Units.map (PadicInt.toZModPow (if q.val = 2 then 2 else 1) : ℤ_[q.val] →+* _).toMonoidHom)) X := by
  let q := levelPrime N i
  let hq := levelPrime_ne_detecting s i
  let X := splitOrderChart s q hq (generator s P q)
  let x := atRep P.z q (root P.y)
  have hx : x.re = 0 := by rw [atRep_re, P.trace_zero, Rat.cast_zero]
  let α := C.alpha q hi
  change localFactor s.mod_four C m₀ q x =
    levelWeight (α.comp (Units.map (PadicInt.toZModPow _).toMonoidHom)) X
  have ho : q.val ≠ s.ell := hq
  have hn : q.val ∣ N := hi
  rw [localFactor, dite_eq_right ho, splitFactor, dite_eq_left hx, dite_eq_left hn]
  have hxt : (splitChart s.ell s.mod_four q hq x).trace = 0 := by
    rw [(split_invariants _ _ _ _).1, hx, mul_zero]
  have he : (⟨splitChart s.ell s.mod_four q hq x, hxt⟩ : TraceZero ℚ_[q.val]) =
      affineZero q.val ⟨X, ht⟩ := by
    apply Subtype.ext
    change splitChart s.ell s.mod_four q hq (atRep P.z q (root P.y)) =
      (2 : ℚ_[q.val]) • integralMat q.val X.val - 1
    rw [atRep_root, map_sub, map_mul, map_ofNat, map_one]
    have hX := splitOrderChart_compatible s q hq (generator s P q)
    change integralMat q.val X.val = splitChart s.ell s.mod_four q hq (atRep P.z q P.y) at hX
    rw [← hX, two_mul, two_smul]
  change levelSchwartz q.val (e := N.factorization q.val) α
    ⟨splitChart s.ell s.mod_four q hq x, hxt⟩ = _
  rw [he]
  let f := affineZero q.val (e := N.factorization q.val)
  let θ := α.comp (Units.map (PadicInt.toZModPow _).toMonoidHom)
  exact (extendWeight_spec f (fun y => levelWeight θ y.val)
    (affineZero_openEmbedding _ _).injective).1 ⟨X, ht⟩

theorem split_schwartz (i : Fin N.primeFactors.card) (hi : (levelPrime N i).val ∣ N)
    (P : ActualPoint s (D := D))
    (ht : (splitOrderChart s (levelPrime N i) (levelPrime_ne_detecting s i)
      (generator s P (levelPrime N i))).val.trace = 1) :
    let q := levelPrime N i
    let u := splitUnit (N := N) s.mod_four q (levelPrime_ne_detecting s i)
    let x := atRep P.z q (root P.y)
    localFactor s.mod_four C m₀ q (rightConj u x) =
      (C.alpha q hi (-1) : O) * localFactor s.mod_four C m₀ q x := by
  let q := levelPrime N i
  let Q := stepPoint _ (splitAdele_order s i) P
  have ht' : (splitOrderChart s q (levelPrime_ne_detecting s i) (generator s Q q)).val.trace = 1 := by
    rw [splitAdele_chart]
    exact (splitSwap_trace q _ _).trans ht
  have he : atRep Q.z q (root Q.y) =
      rightConj (splitUnit (N := N) s.mod_four q (levelPrime_ne_detecting s i))
        (atRep P.z q (root P.y)) := by
    change atRep (P.z * splitAdele s i) q (root P.y) = _
    rw [atRep_right, single_same]
    rfl
  change localFactor s.mod_four C m₀ q (rightConj (splitUnit (N := N) s.mod_four q
      (levelPrime_ne_detecting s i)) (atRep P.z q (root P.y))) =
    (C.alpha q hi (-1) : O) * localFactor s.mod_four C m₀ q (atRep P.z q (root P.y))
  rw [← he, splitFactor_on_point s C i hi Q ht', splitFactor_on_point s C i hi P ht]
  let X := splitOrderChart s q (levelPrime_ne_detecting s i) (generator s P q)
  let Y := splitOrderChart s q (levelPrime_ne_detecting s i) (generator s Q q)
  let φ := Units.map (PadicInt.toZModPow (p := q.val) (if q.val = 2 then 2 else 1)).toMonoidHom
  let θ := (C.alpha q hi).comp φ
  have hchart : Y = splitSwap q (N.factorization q.val) X := splitAdele_chart s i P
  change levelWeight θ Y = (C.alpha q hi (-1) : O) * levelWeight θ X
  have hh := splitSwap_weight q _ (levelPrime_exp hN i) θ X ht
  have hneg : φ (-1) = -1 := by
    apply Units.ext
    change (PadicInt.toZModPow _ : ℤ_[q.val] →+* _) (-1) = -1
    rw [map_neg, map_one]
  rw [hchart, hh]
  change (C.alpha q hi (φ (-1)) : O) * _ = _
  rw [hneg]
  rfl

theorem division_schwartz (x : Bp s.ell (-1) (-(s.ell : ℚ))) (hx : x.re = 0) :
    (divisionFactor s.mod_four (rightConj (divisionUnit s.mod_four) x) : O) =
      -divisionFactor s.mod_four x := by
  letI : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  let f := DivisionJoin.ambientEquiv s.ell
  let u := divisionUnit s.mod_four
  have hf : f (rightConj u x) = rightConj LocalDivision.uniformizer (f x) := by
    have hmap := map_rightConj f.toRingHom u x
    change f (rightConj u x) = _ at hmap
    rw [hmap]
    have he := divisionUnit_chart s.mod_four
    change Units.map f.toRingHom.toMonoidHom _ = _ at he
    rw [he]
    rfl
  have ht : LocalDivision.tr (f x) = 0 := by
    rw [DivisionJoin.ambient_trace, DivisionJoin.reducedTrace, hx, mul_zero]
  have htr' : LocalDivision.tr (f (rightConj u x)) = 0 := by
    rw [hf]
    exact ((LocalDivision.localModel s.ell).tr_conj _ _).trans ht
  have h' : (rightConj u x).re = 0 := by
    have hh := htr'
    rw [DivisionJoin.ambient_trace, DivisionJoin.reducedTrace] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  change divisionFactor s.mod_four (rightConj u x) = -divisionFactor s.mod_four x
  simp only [divisionFactor, dite_eq_left h', dite_eq_left hx]
  have he : (⟨f (rightConj u x), htr'⟩ : (LocalDivision.coordinates s.ell).RationalZero) =
      (LocalDivision.coordinates s.ell).conjZero (LocalDivision.localModel s.ell)
        LocalDivision.uniformizer ⟨f x, ht⟩ := Subtype.ext hf
  change (LocalDivision.coordinates s.ell).divisionSchwartz ⟨f (rightConj u x), htr'⟩ =
    -((LocalDivision.coordinates s.ell).divisionSchwartz ⟨f x, ht⟩ : O)
  rw [he, LocalDivision.divisionSchwartz_uniformizer]

theorem division_local_schwartz (P : ActualPoint s (D := D)) :
    let q := detectingPrime s.ell
    let x := atRep P.z q (root P.y)
    localFactor s.mod_four C m₀ q (rightConj (divisionUnit s.mod_four) x) =
      (-1 : O) * localFactor s.mod_four C m₀ q x := by
  simp only [localFactor, detectingPrime, neg_one_mul]
  apply division_schwartz s
  rw [atRep_re, P.trace_zero, Rat.cast_zero]

end Local

end ZInQ.Manuscript.RC.O7Normalizers
