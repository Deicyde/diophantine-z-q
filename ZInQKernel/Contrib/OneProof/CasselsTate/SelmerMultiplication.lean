import ZInQKernel.Contrib.OneProof.SelmerFam

/-! The transition map `Sel_(mn) → Sel_m` on the genuine elliptic curve
Selmer groups. Its image in `Sha[m]` consists exactly of the classes
divisible by `n` in Sha. -/

noncomputable section

open TauCeti TauCeti.ContCohomology

set_option linter.style.haveILetI false

namespace WeierstrassCurve

variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- Multiplication by `n` maps the `mn`-torsion Galois module to the
`m`-torsion Galois module. -/
def torsionCoeffMultiplication (m n : ℕ) :
    E.TorsionCoeff (m * n) →+[AbsoluteGaloisGroup K] E.TorsionCoeff m where
  toFun x := ⟨n • (x : E.PointCoeff), AddSubgroup.torsionBy.nsmul_iff.mpr <| by
    rw [← mul_nsmul, Nat.mul_comm]
    exact AddSubgroup.torsionBy.nsmul_iff.mp x.2⟩
  map_zero' := Subtype.ext (nsmul_zero _)
  map_add' x y := Subtype.ext (nsmul_add _ _ _)
  map_smul' σ x := Subtype.ext (smul_comm n σ (x : E.PointCoeff))

private def pointCoeffMultiplication (n : ℕ) :
    E.PointCoeff →+[AbsoluteGaloisGroup K] E.PointCoeff where
  toFun x := n • x
  map_zero' := nsmul_zero _
  map_add' _ _ := nsmul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

theorem torsionCoeffIncl_comp_multiplication (m n : ℕ) :
    (E.torsionCoeffIncl m).comp (E.torsionCoeffMultiplication m n) =
      (E.pointCoeffMultiplication n).comp (E.torsionCoeffIncl (m * n)) := by
  ext x
  rfl

/-- The induced transition on `H¹(E[m])` is multiplication by `n` after
inclusion into `H¹(E)`. -/
theorem explicitCoeff1_multiplication_incl (m n : ℕ)
    (x : H1 (AbsoluteGaloisGroup K) (E.TorsionCoeff (m * n))) :
    explicitCoeff1 _ _ (E.torsionCoeffIncl m) continuous_of_discreteTopology
        (explicitCoeff1 _ _ (E.torsionCoeffMultiplication m n) continuous_of_discreteTopology x) =
      n • explicitCoeff1 _ _ (E.torsionCoeffIncl (m * n)) continuous_of_discreteTopology x := by
  let φ (f : E.TorsionCoeff (m * n) →+[AbsoluteGaloisGroup K] E.PointCoeff) :=
    explicitCoeff1 _ _ f continuous_of_discreteTopology x
  calc
    _ = φ ((E.torsionCoeffIncl m).comp (E.torsionCoeffMultiplication m n)) := by
      exact DFunLike.congr_fun (explicitCoeff1_comp _ _ _ _
        continuous_of_discreteTopology continuous_of_discreteTopology).symm x
    _ = φ ((E.pointCoeffMultiplication n).comp (E.torsionCoeffIncl (m * n))) :=
      congrArg φ (E.torsionCoeffIncl_comp_multiplication m n)
    _ = explicitCoeff1 _ _ (E.pointCoeffMultiplication n) continuous_of_discreteTopology
        (explicitCoeff1 _ _ (E.torsionCoeffIncl (m * n)) continuous_of_discreteTopology x) := by
      exact DFunLike.congr_fun (explicitCoeff1_comp _ _ _ _
        continuous_of_discreteTopology continuous_of_discreteTopology) x
    _ = _ := explicitCoeff1_eq_nsmul _ _ _ _ (fun _ => rfl) _

variable {ι : Type*} {L : ι → Type*}
  [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-- The coefficient transition maps the `mn`-Selmer group to the
`m`-Selmer group for the same local conditions. -/
def selmerMultiplication (m n : ℕ) :
    E.selmerGroup τ (m * n) →+ E.selmerGroup τ m :=
  let f := explicitCoeff1 _ _ (E.torsionCoeffMultiplication m n) continuous_of_discreteTopology
  { toFun := fun x => ⟨f x, (E.mem_selmerGroup_iff τ m).mpr (by
      rw [explicitCoeff1_multiplication_incl]
      exact nsmul_mem ((E.mem_selmerGroup_iff τ (m * n)).mp x.2) n)⟩
    map_zero' := Subtype.ext (map_zero f)
    map_add' _ _ := Subtype.ext (map_add f _ _) }

theorem coe_selmerShaMap_multiplication (m n : ℕ) (x : E.selmerGroup τ (m * n)) :
    (E.selmerShaMap τ m (E.selmerMultiplication τ m n x) : E.shafarevichTateGroup τ) =
      n • (E.selmerShaMap τ (m * n) x : E.shafarevichTateGroup τ) := by
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, coe_selmerShaMap, coe_selmerShaMap]
  exact E.explicitCoeff1_multiplication_incl m n x

/-- The image of `Sel_(mn) → Sel_m → Sha[m]` consists of the classes
of `Sha[m]` that have an `n`-th part in the same Sha group. -/
theorem mem_range_selmerShaMap_multiplication_iff [E.IsElliptic]
    (m n : ℕ) (hmn : IsUnit ((m * n : ℕ) : K))
    (x : AddSubgroup.torsionBy (E.shafarevichTateGroup τ) m) :
    x ∈ ((E.selmerShaMap τ m).comp (E.selmerMultiplication τ m n)).range ↔
      ∃ y : E.shafarevichTateGroup τ, n • y = (x : E.shafarevichTateGroup τ) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨E.selmerShaMap τ (m * n) z, (E.coe_selmerShaMap_multiplication τ m n z).symm⟩
  · rintro ⟨y, hy⟩
    have hmy : (m * n) • y = 0 := by
      rw [Nat.mul_comm, mul_nsmul, hy]
      exact AddSubgroup.torsionBy.nsmul_iff.mp x.2
    obtain ⟨z, hz⟩ := E.selmerShaMap_surjective τ hmn
      ⟨y, AddSubgroup.torsionBy.nsmul_iff.mpr hmy⟩
    refine ⟨z, Subtype.ext ?_⟩
    change (E.selmerShaMap τ m (E.selmerMultiplication τ m n z) : E.shafarevichTateGroup τ) = x
    rw [E.coe_selmerShaMap_multiplication τ m n z, hz]
    exact hy

section Kummer

variable [DecidableEq K] [E.IsElliptic]

/-- The transition takes the `mn`-Kummer class of a point to its `m`-Kummer class. -/
theorem explicitCoeff1_multiplication_kummerMap (m n : ℕ) (hm : IsUnit (m : K))
    (hmn : IsUnit ((m * n : ℕ) : K)) (P : E.toAffine.Point) :
    explicitCoeff1 _ _ (E.torsionCoeffMultiplication m n) continuous_of_discreteTopology
        (E.kummerMap (m * n) hmn P) = E.kummerMap m hm P := by
  obtain ⟨Q, hQ⟩ := (E.kummerShortExact (m * n) hmn).proj_surjective (E.basePointCoeff P)
  rw [kummerShortExact_proj, nsmulAddMonoidHom_apply] at hQ
  have hQ' : m • (n • Q) = E.basePointCoeff P := by rwa [← mul_nsmul, Nat.mul_comm]
  rw [kummerMap_eq_H1pi hmn hQ, kummerMap_eq_H1pi hm hQ']
  change explicitCoeff1 _ _ (E.torsionCoeffMultiplication m n) continuous_of_discreteTopology
      (⟨kummerCocycle hQ, kummerCocycle_mem_Z1 hQ⟩ : Z1 _ _ ) =
    (⟨kummerCocycle hQ', kummerCocycle_mem_Z1 hQ'⟩ : Z1 _ _ )
  rw [explicitCoeff1_mk]
  congr 1
  exact Subtype.ext (funext fun σ => Subtype.ext (by
    change n • (σ • Q - Q) = σ • (n • Q) - n • Q
    rw [nsmul_sub, smul_comm]))

/-- Every rational-point Kummer class lifts along the finite Selmer transition. -/
theorem ker_selmerShaMap_le_range_multiplication (m n : ℕ) (hm : IsUnit (m : K))
    (hmn : IsUnit ((m * n : ℕ) : K)) :
    (E.selmerShaMap τ m).ker ≤ (E.selmerMultiplication τ m n).range := by
  intro x hx
  obtain ⟨a, rfl⟩ := (E.exact_kummerSelmerMap_selmerShaMap τ hm x).mp hx
  induction a using QuotientAddGroup.induction_on with
  | _ P =>
    refine ⟨E.kummerSelmerMap τ hmn (QuotientAddGroup.mk P), Subtype.ext ?_⟩
    change explicitCoeff1 _ _ (E.torsionCoeffMultiplication m n) continuous_of_discreteTopology
        (E.kummerSelmerMap τ hmn (QuotientAddGroup.mk P) : H1 _ _) = _
    rw [coe_kummerSelmerMap, coe_kummerSelmerMap, kummerClassMap_mk, kummerClassMap_mk]
    exact E.explicitCoeff1_multiplication_kummerMap m n hm hmn P

end Kummer

end WeierstrassCurve

#print axioms WeierstrassCurve.mem_range_selmerShaMap_multiplication_iff
#print axioms WeierstrassCurve.ker_selmerShaMap_le_range_multiplication
