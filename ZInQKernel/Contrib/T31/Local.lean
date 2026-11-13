import ZInQKernel.Contrib.T31.Good
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Maximal
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Criterion
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.AlgebraicExtension.IntermediateField

/-!
# T31, local part: a number field unramified at `p` embeds into `K^{ur}`

Let `K` be a nonarchimedean local field, `Ω/K` an algebraic extension with a valuative relation
extending that of `K`, `L` a number field Galois over `ℚ` and `ι : L → Ω` a ring homomorphism.
Let `p` be a natural number with `v_K(p) < 1`, such that every prime of `𝓞 L` containing `p`
has ramification index `1`. Then `ι(L)` lies in the maximal unramified extension `K^{ur}` of `K`
in `Ω` (Tau Ceti's `TauCeti.maximalUnramifiedExtension`).

The prime `w = {x ∈ 𝓞 L | v(ι x) < 1}` has ramification index `1`; for `b` as in
`T31.exists_base`, `(minpoly ℤ b)'(b)` is a `w`-unit, so `K(ι b)/K` is unramified by Tau Ceti's
criterion `TauCeti.isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative`.
-/

namespace T31

open NumberField Polynomial ValuativeRel TauCeti IntermediateField

theorem ringHom_aeval_int {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A)
    (Q : ℤ[X]) : f (aeval x Q) = aeval (f x) Q := by
  simpa using (Polynomial.aeval_algHom_apply (f.toIntAlgHom) x Q).symm

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [ValuativeRel Ω]
  [ValuativeExtension K Ω]
variable {L : Type*} [Field L] [NumberField L]

include K

/-- Integral elements of `Ω` have valuation at most `1`. -/
theorem val_le_one_of_isIntegral {y : Ω} (hy : IsIntegral ℤ y) : valuation Ω y ≤ 1 :=
  ((Valuation.integer.integers (valuation K)).isIntegral_iff_valuation_le_one y).1
    (hy.tower_top (A := 𝒪[K]))

omit [NumberField L] in
theorem val_le_one_ringOfIntegers (j : 𝓞 L →+* Ω) (x : 𝓞 L) : valuation Ω (j x) ≤ 1 :=
  val_le_one_of_isIntegral K ((Algebra.IsIntegral.isIntegral (R := ℤ) x).map j.toIntAlgHom)

/-- The prime `w = {x ∈ 𝓞 L | v(j x) < 1}`. -/
noncomputable def wIdeal (j : 𝓞 L →+* Ω) : Ideal (𝓞 L) where
  carrier := {x | valuation Ω (j x) < 1}
  add_mem' {a b} ha hb := by
    change valuation Ω (j (a + b)) < 1
    rw [map_add]
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by change valuation Ω (j 0) < 1; simp
  smul_mem' c x hx := by
    change valuation Ω (j (c * x)) < 1
    change valuation Ω (j x) < 1 at hx
    rw [map_mul, map_mul]
    calc valuation Ω (j c) * valuation Ω (j x) ≤ 1 * valuation Ω (j x) :=
          mul_le_mul_left (val_le_one_ringOfIntegers K j c) _
      _ < 1 := by rwa [one_mul]

theorem mem_wIdeal (j : 𝓞 L →+* Ω) (x : 𝓞 L) : x ∈ wIdeal K j ↔ valuation Ω (j x) < 1 :=
  Iff.rfl

theorem wIdeal_isPrime (j : 𝓞 L →+* Ω) : (wIdeal K j).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have : (1 : 𝓞 L) ∈ wIdeal K j := h ▸ Submodule.mem_top
    rw [mem_wIdeal, map_one, map_one] at this
    exact lt_irrefl _ this
  · rw [mem_wIdeal, map_mul, map_mul] at hab
    rw [mem_wIdeal, mem_wIdeal]
    by_contra h
    push Not at h
    have ha : valuation Ω (j a) = 1 := le_antisymm (val_le_one_ringOfIntegers K j a) h.1
    have hb : valuation Ω (j b) = 1 := le_antisymm (val_le_one_ringOfIntegers K j b) h.2
    rw [ha, hb, one_mul] at hab
    exact lt_irrefl _ hab

theorem natCast_mem_wIdeal (j : 𝓞 L →+* Ω) {p : ℕ} (hp : valuation K (p : K) < 1) :
    (p : 𝓞 L) ∈ wIdeal K j := by
  rw [mem_wIdeal]
  have : j (p : 𝓞 L) = algebraMap K Ω (p : K) := by simp
  rw [this, Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation Ω)]
  exact hp

/-- If `(minpoly ℤ b)'(b)` is a `w`-unit, then `j b ∈ K^{ur}`. -/
theorem mem_maximalUnramifiedExtension_of_unit (j : 𝓞 L →+* Ω) (b : 𝓞 L)
    (hd : aeval b (derivative (minpoly ℤ b)) ∉ wIdeal K j) :
    j b ∈ maximalUnramifiedExtension K Ω := by
  set x : Ω := j b with hx
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let F := K⟮x⟯
  have : FiniteDimensional K F := adjoin.finiteDimensional hxint
  let _ := finiteIntermediateFieldValuativeRel K Ω F
  let _ := finiteIntermediateFieldTopology K Ω F
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω F
  have := finiteIntermediateField_valuativeExtension K Ω F
  have : ValuativeExtension F Ω := F.valuativeExtension
  have hb1 : valuation F (AdjoinSimple.gen K x) ≤ 1 := by
    rw [← Valuation.HasExtension.val_map_le_one_iff (valuation F) (valuation Ω),
      AdjoinSimple.algebraMap_gen]
    exact val_le_one_ringOfIntegers K j b
  let b' : 𝒪[F] := ⟨AdjoinSimple.gen K x, hb1⟩
  let φ : 𝒪[F] →+* Ω := (algebraMap F Ω).comp (𝒪[F]).subtype
  have hφinj : Function.Injective φ :=
    (algebraMap F Ω).injective.comp Subtype.val_injective
  have hφb : φ b' = j b := AdjoinSimple.algebraMap_gen K x
  have hkey : ∀ Q : ℤ[X], φ (aeval b' (Q.map (algebraMap ℤ 𝒪[K]))) = j (aeval b Q) := by
    intro Q
    rw [aeval_map_algebraMap, ringHom_aeval_int, ringHom_aeval_int, hφb]
  have hadj : IntermediateField.adjoin K {algebraMap 𝒪[F] F b'} = ⊤ := by
    apply IntermediateField.lift_injective
    rw [lift_top]
    exact lift_adjoin_simple (K := F) (α := algebraMap 𝒪[F] F b')
  set P : 𝒪[K][X] := (minpoly ℤ b).map (algebraMap ℤ 𝒪[K]) with hP
  have hp : aeval b' P = 0 := by
    apply hφinj
    rw [hP, hkey, minpoly.aeval, map_zero, map_zero]
  have hu : IsUnit (aeval b' (derivative P)) := by
    rw [(Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
    rw [← Valuation.HasExtension.val_map_eq_one_iff (valuation F) (valuation Ω)]
    have h1 : algebraMap F Ω (algebraMap 𝒪[F] F (aeval b' (derivative P))) =
        j (aeval b (derivative (minpoly ℤ b))) := by
      rw [hP, derivative_map, ← hkey]; rfl
    rw [h1]
    rw [mem_wIdeal, not_lt] at hd
    exact le_antisymm (val_le_one_ringOfIntegers K j _) hd
  have hF : IsUnramified K F := isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative hadj hp hu
  exact F.le_maximalUnramifiedExtension (mem_adjoin_simple_self K x)

end T31
