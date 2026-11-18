import ZInQKernel.Contrib.OneProof.RC.DivisionJoin.Ambient
import ZInQKernel.Contrib.OneProof.RC.Eichler.Explicit
import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Order

/-!
# The explicit order at the detecting prime

Since two is a unit, the global generators with halves and the standard
integral quaternion basis generate the same local order. The comparison
and the transfer of maximality are on-the-spot (c), for tex 8462–8464.
-/

namespace ZInQ.Manuscript.RC.DivisionJoin

open Eichler LocalDivision QuaternionAlgebra

variable (p : ℕ) [Fact p.Prime] (h : p % 4 = 3)

/-- The completion of the specified global order at its detecting prime. -/
noncomputable abbrev completedOrder := (explicitOrderAt p h).completion p

/-- The global basis `1, i, (1+j)/2, (i+k)/2`, in standard coordinates. -/
private def fromCoordinates {b : ℚ} (z : Fin 4 → ℤ) : B (-1) b :=
  ⟨z 0 + (z 2 : ℚ) / 2, z 1 + (z 3 : ℚ) / 2, (z 2 : ℚ) / 2, (z 3 : ℚ) / 2⟩

private theorem mem_explicitOrder_cast (m : ℤ) {b : ℚ} (hb : 1 - 4 * (m : ℚ) = b)
    (x : B (-1) b) :
    x ∈ (Eq.mpr (congrArg (Order (-1)) hb.symm) (explicitOrder m)).ring ↔
      ∃ z : Fin 4 → ℤ, fromCoordinates z = x := by
  subst b
  let e := Module.Basis.ofEquivFun (explicitCoords m)
  change x ∈ Submodule.span ℤ (Set.range e) ↔ _
  rw [e.mem_span_iff_repr_mem ℤ x]
  change (∀ i, explicitCoords m x i ∈ Set.range (algebraMap ℤ ℚ)) ↔ _
  have hc (z : Fin 4 → ℤ) : explicitCoords m (fromCoordinates z) = fun i => (z i : ℚ) := by
    change explicitCoords m ((explicitCoords m).symm fun i => (z i : ℚ)) = _
    exact (explicitCoords m).apply_symm_apply _
  constructor
  · intro hx
    choose z hz using hx
    exact ⟨z, (explicitCoords m).injective ((hc z).trans (funext hz))⟩
  · rintro ⟨z, rfl⟩ i
    rw [hc]
    exact ⟨z i, rfl⟩

omit [Fact p.Prime] in
private theorem mem_explicitOrderAt (x : B (-1) (-(p : ℚ))) :
    x ∈ (explicitOrderAt p h).ring ↔ ∃ z : Fin 4 → ℤ, fromCoordinates z = x := by
  let m : ℤ := (p / 4 : ℕ) + 1
  have hp : (p : ℤ) = 4 * m - 1 := by dsimp [m]; omega
  have hp' : (p : ℚ) = 4 * (m : ℚ) - 1 := by exact_mod_cast hp
  have hb : 1 - 4 * (m : ℚ) = -(p : ℚ) := by linarith
  exact mem_explicitOrder_cast m hb x

include h in
private theorem integral_half : ∃ t : ℤ_[p], (t : ℚ_[p]) = 1 / 2 := by
  have ho : Odd p := ⟨p / 2, by omega⟩
  have hu : IsUnit (2 : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr ho.coprime_two_right)
  obtain ⟨u, hu⟩ := hu
  refine ⟨↑u⁻¹, (eq_div_iff (by norm_num)).mpr ?_⟩
  have hmul : (↑u⁻¹ : ℤ_[p]) * 2 = 1 := by rw [← hu, Units.inv_mul]
  exact congrArg PadicInt.Coe.ringHom hmul

private theorem mapped_coordinates (z : Fin 4 → ℤ) :
    ambientIntegralEquiv p (toLocal p (fromCoordinates z)) =
      (⟨z 0 + (z 2 : ℚ_[p]) / 2, z 1 + (z 3 : ℚ_[p]) / 2,
        (z 2 : ℚ_[p]) / 2, (z 3 : ℚ_[p]) / 2⟩ : D p) := by
  change (⟨((z 0 + (z 2 : ℚ) / 2 : ℚ) : ℚ_[p]), ((z 1 + (z 3 : ℚ) / 2 : ℚ) : ℚ_[p]),
    (((z 2 : ℚ) / 2 : ℚ) : ℚ_[p]), (((z 3 : ℚ) / 2 : ℚ) : ℚ_[p])⟩ : D p) = _
  apply QuaternionAlgebra.ext <;> push_cast <;> rfl

private theorem quaternion_sum {K : Type*} [CommRing K] {a b c : K}
    (x : QuaternionAlgebra K a b c) :
    x.re • (1 : QuaternionAlgebra K a b c) + x.imI • (⟨0, 1, 0, 0⟩ : QuaternionAlgebra K a b c) +
      x.imJ • (⟨0, 0, 1, 0⟩ : QuaternionAlgebra K a b c) +
      x.imK • (⟨0, 0, 0, 1⟩ : QuaternionAlgebra K a b c) = x := by
  ext <;> simp

/-- The image of the completed explicit order is the standard integral quaternion order. -/
theorem completion_map :
    (completedOrder p h).map (ambientIntegralEquiv p).toAlgHom = order p := by
  let S := (completedOrder p h).map (ambientIntegralEquiv p).toAlgHom
  change S = order p
  apply le_antisymm
  · change (completedOrder p h).map (ambientIntegralEquiv p).toAlgHom ≤ order p
    rw [Subalgebra.map_le]
    change Algebra.adjoin ℤ_[p] _ ≤ (order p).comap (ambientIntegralEquiv p).toAlgHom
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_explicitOrderAt p h x).mp hx
    obtain ⟨t, ht⟩ := integral_half p h
    change (ambientIntegralEquiv p) (toLocal p (fromCoordinates z)) ∈ order p
    let y : IntegralD p := ⟨(z 0 : ℤ_[p]) + (z 2 : ℤ_[p]) * t,
      (z 1 : ℤ_[p]) + (z 3 : ℤ_[p]) * t, (z 2 : ℤ_[p]) * t, (z 3 : ℤ_[p]) * t⟩
    refine ⟨y, ?_⟩
    change (⟨(y.re : ℚ_[p]), (y.imI : ℚ_[p]), (y.imJ : ℚ_[p]), (y.imK : ℚ_[p])⟩ : D p) = _
    rw [mapped_coordinates]
    apply QuaternionAlgebra.ext <;> simp [y, ht, div_eq_mul_inv]
  · have hg (z : Fin 4 → ℤ) :
        ambientIntegralEquiv p (toLocal p (fromCoordinates z)) ∈ S :=
      ⟨_, Algebra.subset_adjoin ⟨_, (mem_explicitOrderAt p h _).mpr ⟨z, rfl⟩, rfl⟩, rfl⟩
    have hi : (⟨0, 1, 0, 0⟩ : D p) ∈ S := by
      convert hg ![0, 1, 0, 0] using 1
      apply QuaternionAlgebra.ext <;> norm_num [mapped_coordinates]
    have hj : (⟨0, 0, 1, 0⟩ : D p) ∈ S := by
      have hj' := S.sub_mem (S.add_mem (hg ![0, 0, 1, 0]) (hg ![0, 0, 1, 0])) S.one_mem
      convert hj' using 1
      apply QuaternionAlgebra.ext <;> norm_num [mapped_coordinates]
    have hk : (⟨0, 0, 0, 1⟩ : D p) ∈ S := by
      have hk' := S.sub_mem (S.add_mem (hg ![0, 0, 0, 1]) (hg ![0, 0, 0, 1])) hi
      convert hk' using 1
      apply QuaternionAlgebra.ext <;> norm_num [mapped_coordinates]
    rintro _ ⟨x, rfl⟩
    change includeIntegral x ∈ S
    have hx := congrArg includeIntegral (quaternion_sum x)
    simp only [map_add, map_smul, map_one] at hx
    rw [← hx]
    exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem S.one_mem _) (S.smul_mem hi _))
      (S.smul_mem hj _)) (S.smul_mem hk _)

/-- Restriction of the ambient equivalence to the integral orders. -/
noncomputable def orderEquiv : completedOrder p h ≃ₐ[ℤ_[p]] order p :=
  ((ambientIntegralEquiv p).subalgebraMap (completedOrder p h)).trans
    (Subalgebra.equivOfEq _ _ (completion_map p h))

theorem order_compatible (x : completedOrder p h) :
    ambientEquiv p x.val = (orderEquiv p h x).val := rfl

private theorem completion_mem_iff (x : LocalB p) :
    x ∈ completedOrder p h ↔ ambientEquiv p x ∈ order p := by
  rw [← completion_map p h]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ =>
    (ambientEquiv p).injective hyx ▸ hy⟩

/-- The completion spans the whole local algebra over `ℚ_[p]`. -/
theorem completion_span :
    Submodule.span ℚ_[p] (completedOrder p h : Set (LocalB p)) = ⊤ := by
  let S := Submodule.span ℚ_[p] (completedOrder p h : Set (LocalB p))
  have hm (x : IntegralD p) :
      (ambientEquiv p).symm (includeIntegral x) ∈ S := by
    apply Submodule.subset_span
    rw [SetLike.mem_coe, completion_mem_iff, AlgEquiv.apply_symm_apply]
    exact ⟨x, rfl⟩
  apply eq_top_iff.mpr
  intro x _
  change x ∈ S
  rw [← quaternion_sum x]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ (hm 1))
    (S.smul_mem _ (hm ⟨0, 1, 0, 0⟩))) (S.smul_mem _ (hm ⟨0, 0, 1, 0⟩)))
    (S.smul_mem _ (hm ⟨0, 0, 0, 1⟩))

/-- The explicit completion is a full finite order and is maximal among full finite orders. -/
theorem completion_maximal : IsMaximalLocalOrder p (completedOrder p h) := by
  let _ : Fact (p % 4 = 3) := ⟨h⟩
  have : Module.Finite ℤ_[p] (order p) := finite_order
  refine ⟨Module.Finite.of_surjective (orderEquiv p h).symm.toLinearMap
    (orderEquiv p h).symm.surjective, completion_span p h, ?_⟩
  intro T hT _ hAT x hx
  let e := ambientIntegralEquiv p
  have hTf : Module.Finite ℤ_[p] (T.map e.toAlgHom) :=
    Module.Finite.of_surjective (e.subalgebraMap T).toLinearMap (e.subalgebraMap T).surjective
  have hle : order p ≤ T.map e.toAlgHom :=
    (completion_map p h) ▸ Subalgebra.map_mono hAT
  have heq := maximal_order (T.map e.toAlgHom) hTf hle
  exact (completion_mem_iff p h x).mpr (heq ▸ (show e x ∈ T.map e.toAlgHom from ⟨x, hx, rfl⟩))

omit [Fact p.Prime] in
/-- The exact `IsEichler.ramified_maximal` clause for the explicit order. -/
theorem ramified_maximal (q : ℕ) [Fact q.Prime] (hq : q = p) :
    IsMaximalLocalOrder q ((explicitOrderAt p h).completion q) := by
  subst q
  exact completion_maximal p h

#print axioms mem_explicitOrder_cast
#print axioms mem_explicitOrderAt
#print axioms integral_half
#print axioms mapped_coordinates
#print axioms quaternion_sum
#print axioms completion_map
#print axioms orderEquiv
#print axioms order_compatible
#print axioms completion_mem_iff
#print axioms completion_span
#print axioms completion_maximal
#print axioms ramified_maximal

end ZInQ.Manuscript.RC.DivisionJoin
