import ZInQKernel.HDecomp.ModCurves.Leaves
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # javanpeykar-dict: algebra of the constant field extension

Task javanpeykar-dict (2026-11-16). Pure field theory used to prove `JavanpeykarDict.BelyiBaseChange`:
* `productMap_bijective_of_fraction`: `Frac(A) ⊗_K L ≅ Frac(A ⊗_K L)` for `L/K` algebraic;
* `belyi_unram`, `finrank_adjoin_eq`, `transcendental_ι`: the Belyi property and the degree survive the
  constant field extension `F ⊗_K L ≅ FL`, given the leaf `ConstantFieldExtensionUnramified`
  (Stichtenoth, Thm 3.6.3(a));
* `isBelyiFunction_baseChange`: the combination.

No `sorry`, no `axiom`. -/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace JavanpeykarDict


open scoped TensorProduct

section FracTensor

variable {K A KA L B M : Type} [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Field KA]
  [Algebra A KA] [IsFractionRing A KA] [Algebra K KA] [IsScalarTower K A KA]
  [Field L] [Algebra K L] [CommRing B] [Algebra K B] [Field M] [Algebra B M] [IsFractionRing B M]
  [Algebra K M] [IsScalarTower K B M]

/-- **The fraction field commutes with an algebraic base change (glue, proved).** If
`β : A ⊗_K L ≅ B` and `KA = Frac A`, `M = Frac B`, then `KA ⊗_K L ≅ M` through `ι` and `s` compatible
with `β`. -/
theorem productMap_bijective_of_fraction (β : A ⊗[K] L →ₐ[K] B) (hβ : Function.Bijective β)
    (ι : KA →ₐ[K] M) (s : L →ₐ[K] M) [Algebra.IsAlgebraic K L]
    (hι : ∀ a : A, ι (algebraMap A KA a) = algebraMap B M (β (a ⊗ₜ[K] 1)))
    (hs : ∀ l : L, s l = algebraMap B M (β (1 ⊗ₜ[K] l))) :
    Function.Bijective (Algebra.TensorProduct.productMap ι s) := by
  set Ψ := Algebra.TensorProduct.productMap ι s
  set incl : A ⊗[K] L →ₐ[K] KA ⊗[K] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A KA) (AlgHom.id K L)
  have hcomp : ∀ w, Ψ (incl w) = algebraMap B M (β w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      simp only [incl, Ψ, Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom',
        AlgHom.id_apply, Algebra.TensorProduct.productMap_apply_tmul, hι, hs, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp [hx, hy]
  have hden : ∀ w : KA ⊗[K] L, ∃ a ∈ nonZeroDivisors A, ∃ w' : A ⊗[K] L,
      (algebraMap A KA a ⊗ₜ[K] (1 : L)) * w = incl w' := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨1, one_mem _, 0, by simp⟩
    | tmul x l =>
      obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors A) x
      refine ⟨b, b.2, a ⊗ₜ[K] l, ?_⟩
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, incl,
        Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', AlgHom.id_apply]
      rw [mul_comm, h]
    | add x y hx hy =>
      obtain ⟨a₁, ha₁, w₁, h₁⟩ := hx
      obtain ⟨a₂, ha₂, w₂, h₂⟩ := hy
      refine ⟨a₁ * a₂, mul_mem ha₁ ha₂, (a₂ ⊗ₜ[K] 1) * w₁ + (a₁ ⊗ₜ[K] 1) * w₂, ?_⟩
      have e1 : (algebraMap A KA (a₁ * a₂) ⊗ₜ[K] (1 : L)) =
          (algebraMap A KA a₂ ⊗ₜ[K] (1 : L)) * (algebraMap A KA a₁ ⊗ₜ[K] (1 : L)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_mul, mul_comm]
      have e2 : (algebraMap A KA (a₁ * a₂) ⊗ₜ[K] (1 : L)) =
          (algebraMap A KA a₁ ⊗ₜ[K] (1 : L)) * (algebraMap A KA a₂ ⊗ₜ[K] (1 : L)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_mul]
      rw [mul_add, map_add, map_mul incl, map_mul incl]
      congr 1
      · rw [e1, mul_assoc, h₁]; rfl
      · rw [e2, mul_assoc, h₂]; rfl
  have hunit : ∀ a ∈ nonZeroDivisors A,
      (algebraMap A KA a)⁻¹ ⊗ₜ[K] (1 : L) * (algebraMap A KA a ⊗ₜ[K] (1 : L)) = 1 := by
    intro a ha
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      inv_mul_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha)]
    rfl
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨a, ha, w', h⟩ := hden w
    have h1 : algebraMap B M (β w') = 0 := by
      rw [← hcomp, ← h, map_mul, hw, mul_zero]
    have h2 : w' = 0 := by
      have := (IsFractionRing.injective B M) (h1.trans (map_zero _).symm)
      exact hβ.1 (this.trans (map_zero β).symm)
    rw [h2, map_zero] at h
    calc w = ((algebraMap A KA a)⁻¹ ⊗ₜ[K] (1 : L) * (algebraMap A KA a ⊗ₜ[K] (1 : L))) * w := by
          rw [hunit a ha, one_mul]
      _ = 0 := by rw [mul_assoc, h, mul_zero]
  haveI : IsDomain (KA ⊗[K] L) := hinj.isDomain Ψ.toRingHom
  have hfield : IsField (KA ⊗[K] L) :=
    Algebra.TensorProduct.isField_of_isAlgebraic K KA L (.inr inferInstance)
  refine ⟨hinj, fun m => ?_⟩
  obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := B) m
  obtain ⟨w₁, rfl⟩ := hβ.2 b₁
  obtain ⟨w₂, rfl⟩ := hβ.2 b₂
  by_cases h0 : incl w₂ = 0
  · refine ⟨0, ?_⟩
    rw [map_zero, ← hcomp w₂, h0, map_zero, div_zero]
  obtain ⟨u, hu⟩ := hfield.mul_inv_cancel h0
  refine ⟨incl w₁ * u, ?_⟩
  have hΨu : Ψ (incl w₂) * Ψ u = 1 := by rw [← map_mul, hu, map_one]
  rw [map_mul, hcomp, ← hcomp w₂, eq_div_iff (left_ne_zero_of_mul_eq_one hΨu), mul_assoc,
    mul_comm (Ψ u), hΨu, mul_one]


end FracTensor

open Polynomial



section Unram

variable {K F L FL : Type} [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
  [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL]

theorem mem_nonunits_comap {w : ValuationSubring FL} {f : F →+* FL} {x : F} :
    x ∈ (w.comap f).nonunits ↔ f x ∈ w.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem mul_mem_nonunits {w : ValuationSubring FL} {x y : FL} (hx : x ∈ w.nonunits) (hy : y ∈ w) :
    x * y ∈ w.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hx

theorem aeval_mem {w : ValuationSubring FL} (hw : ∀ c : L, algebraMap L FL c ∈ w) {z : FL}
    (hz : z ∈ w) (r : L[X]) : aeval z r ∈ w := by
  induction r using Polynomial.induction_on with
  | C a => simpa using hw a
  | add p q hp hq => simpa using add_mem hp hq
  | monomial n a _ =>
    simpa [pow_succ, mul_assoc] using mul_mem (mul_mem (hw a) (pow_mem hz n)) hz

/-- **The Belyi ramification condition survives a constant field extension (glue, proved).** Given
the `e = 1` property of the places of `F_L / F` over every place of `F/K` with a principal maximal
ideal (`hS`), a `K`-rational Belyi function `t` of `F` (`hB`, the second clause of `IsBelyiFunction`)
gives the same clause for `ι t` over `L`, `L` algebraically closed and algebraic over `K`. -/
theorem belyi_unram (ι : F →ₐ[K] FL) [IsAlgClosed L] [Algebra.IsAlgebraic K L] (t : F)
    (hB : ∀ w : ValuationSubring F, (∀ c : K, algebraMap K F c ∈ w) → t ∈ w →
      ∀ q : Polynomial K, q.Monic → Irreducible q → q ≠ Polynomial.X → q ≠ Polynomial.X - 1 →
        Polynomial.aeval t q ∈ w.nonunits →
        ∀ x ∈ w.nonunits, ∃ y ∈ w, x = Polynomial.aeval t q * y)
    (hS : ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ∀ π : F,
      π ∈ (w.comap (ι : F →+* FL)).nonunits →
      (∀ x ∈ (w.comap (ι : F →+* FL)).nonunits, ∃ y ∈ w.comap (ι : F →+* FL), x = π * y) →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = ι π * y) :
    ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ι t ∈ w →
      ∀ q : Polynomial L, q.Monic → Irreducible q → q ≠ Polynomial.X → q ≠ Polynomial.X - 1 →
        Polynomial.aeval (ι t) q ∈ w.nonunits →
        ∀ x ∈ w.nonunits, ∃ y ∈ w, x = Polynomial.aeval (ι t) q * y := by
  intro w hw ht q hqm hqi hqX hqX1 hq x hx
  -- `q = X - C a`
  have hdeg : q.natDegree = 1 :=
    natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible L hqi)
  set a : L := -q.coeff 0 with ha_def
  have hqa : q = X - C a := by
    rw [hqm.eq_X_add_C hdeg, ha_def, map_neg, sub_neg_eq_add]
  have ha0 : a ≠ 0 := by
    rintro h; apply hqX; rw [hqa, h, map_zero, sub_zero]
  have ha1 : a ≠ 1 := by
    rintro h; apply hqX1; rw [hqa, h, map_one]
  -- the minimal polynomial of `a` over `K`
  have hint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set p := minpoly K a with hp_def
  have hpm : p.Monic := minpoly.monic hint
  have hpi : Irreducible p := minpoly.irreducible hint
  have hpX : p ≠ X := by
    intro h; apply ha0
    have := minpoly.aeval K a
    rw [← hp_def, h, aeval_X] at this
    exact this
  have hpX1 : p ≠ X - 1 := by
    intro h; apply ha1
    have := minpoly.aeval K a
    rw [← hp_def, h, map_sub, aeval_X, map_one, sub_eq_zero] at this
    exact this
  -- `p = (X - a) r` over `L`
  set r := (p.map (algebraMap K L)) /ₘ (X - C a) with hr_def
  have hroot : (p.map (algebraMap K L)).IsRoot a := by
    rw [IsRoot.def, eval_map, ← aeval_def]
    exact minpoly.aeval K a
  have hfac : (X - C a) * r = p.map (algebraMap K L) := mul_divByMonic_eq_iff_isRoot.mpr hroot
  set u := aeval (ι t) r with hu_def
  have hu : u ∈ w := aeval_mem hw ht r
  have hkey : ι (aeval t p) = (ι t - algebraMap L FL a) * u := by
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_map_algebraMap L, ← hfac, map_mul,
      map_sub, aeval_X, aeval_C]
  have hqt : aeval (ι t) q = ι t - algebraMap L FL a := by
    rw [hqa, map_sub, aeval_X, aeval_C]
  rw [hqt] at hq ⊢
  -- `p(t)` is a nonunit at `w₀ = w ∩ F`, so a uniformizer there
  have hpt : aeval t p ∈ (w.comap (ι : F →+* FL)).nonunits := by
    rw [mem_nonunits_comap]
    change ι (aeval t p) ∈ w.nonunits
    rw [hkey]
    exact mul_mem_nonunits hq hu
  have hconst : ∀ c : K, algebraMap K F c ∈ w.comap (ι : F →+* FL) := by
    intro c
    rw [ValuationSubring.mem_comap]
    change ι (algebraMap K F c) ∈ w
    rw [ι.commutes, IsScalarTower.algebraMap_apply K L FL]
    exact hw _
  have ht0 : t ∈ w.comap (ι : F →+* FL) := ValuationSubring.mem_comap.mpr ht
  have hgen := hB (w.comap (ι : F →+* FL)) hconst ht0 p hpm hpi hpX hpX1 hpt
  obtain ⟨y, hy, rfl⟩ := hS w hw (aeval t p) hpt hgen x hx
  refine ⟨u * y, mul_mem hu hy, ?_⟩
  rw [hkey, mul_assoc]

end Unram

section Degree

variable {K F L FL : Type} [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
  [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL]

open IntermediateField

/-- `L` inside `FL`, as an intermediate field over `K`. -/
abbrev Lr (K L FL : Type) [Field K] [Field L] [Field FL] [Algebra K L] [Algebra L FL] [Algebra K FL]
    [IsScalarTower K L FL] : IntermediateField K FL :=
  (IsScalarTower.toAlgHom K L FL).fieldRange

theorem adjoin_toSubfield_eq (x : FL) :
    (adjoin L {x}).toSubfield = (adjoin (Lr K L FL) {x}).toSubfield := by
  rw [adjoin_toSubfield, adjoin_toSubfield]
  congr 2
  ext y
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨⟨algebraMap L FL l, ⟨l, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨z, ⟨l, rfl⟩⟩, rfl⟩
    exact ⟨l, rfl⟩

theorem ι_mem_adjoin (ι : F →ₐ[K] FL) (t : F) (c : K⟮t⟯) :
    ι (c : F) ∈ IntermediateField.adjoin L {ι t} := by
  have h1 : ι (c : F) ∈ (K⟮t⟯).map ι := ⟨c, c.2, rfl⟩
  rw [adjoin_map, Set.image_singleton] at h1
  have h2 : K⟮ι t⟯ ≤ (IntermediateField.adjoin L {ι t}).restrictScalars K :=
    adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (subset_adjoin L {ι t} rfl))
  exact h2 h1

/-- Every element of `L⟮ι t⟯` is `∑ⱼ ι(eⱼ) ℓⱼ` with `eⱼ ∈ K⟮t⟯`, for a `K`-basis `ℓ` of `L` (`L/K`
algebraic). -/
theorem mem_adjoin_repr (ι : F →ₐ[K] FL) [Algebra.IsAlgebraic K L] (t : F) {κ : Type}
    (ℓ : Module.Basis κ K L) (y : FL) (hy : y ∈ IntermediateField.adjoin L {ι t}) :
    ∃ e : κ →₀ K⟮t⟯, y = e.sum fun j c => ι (c : F) * algebraMap L FL (ℓ j) := by
  have hy1 : y ∈ (adjoin (Lr K L FL) {ι t}).restrictScalars K := by
    change y ∈ (adjoin (Lr K L FL) {ι t}).toSubfield
    rw [← adjoin_toSubfield_eq]
    exact hy
  rw [restrictScalars_adjoin_eq_sup] at hy1
  haveI : Algebra.IsAlgebraic K (Lr K L FL) :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L FL)).isAlgebraic
  have hy2 : y ∈ (Lr K L FL).toSubalgebra ⊔ (K⟮ι t⟯).toSubalgebra := by
    rw [← sup_toSubalgebra_of_isAlgebraic_left]
    exact hy1
  have hy3 : y ∈ Subalgebra.toSubmodule (Lr K L FL).toSubalgebra *
      Subalgebra.toSubmodule (K⟮ι t⟯).toSubalgebra := by
    rw [Subalgebra.mul_toSubmodule]
    exact hy2
  refine Submodule.mul_induction_on hy3 (fun m hm n hn => ?_) (fun a b ha hb => ?_)
  · obtain ⟨l, rfl⟩ := hm
    have hn' : n ∈ (K⟮t⟯).map ι := by
      rw [adjoin_map, Set.image_singleton]; exact hn
    obtain ⟨c, hc, rfl⟩ := hn'
    refine ⟨(ℓ.repr l).mapRange (fun a => a • (⟨c, hc⟩ : K⟮t⟯)) (zero_smul _ _), ?_⟩
    rw [Finsupp.sum_mapRange_index (by intro j; simp)]
    conv_lhs => rw [← ℓ.linearCombination_repr l]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    change (IsScalarTower.toAlgHom K L FL) (ℓ.repr l x • ℓ x) * ι c =
      ι (ℓ.repr l x • c) * algebraMap L FL (ℓ x)
    rw [map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, IsScalarTower.coe_toAlgHom']
    ring
  · obtain ⟨e₁, rfl⟩ := ha
    obtain ⟨e₂, rfl⟩ := hb
    refine ⟨e₁ + e₂, ?_⟩
    rw [Finsupp.sum_add_index' (by intro j; simp) (by intro j c₁ c₂; simp [add_mul])]

/-- The tensor product `F ⊗_K L` is a field when it maps bijectively onto the field `FL`. -/
theorem isField_tensor (ι : F →ₐ[K] FL)
    (hbij : Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL))) :
    IsField (TensorProduct K F L) :=
  MulEquiv.isField (Field.toIsField FL) (RingEquiv.ofBijective _ hbij).toMulEquiv

/-- **Degree under the constant field extension (glue, proved).** If `F ⊗_K L ≅ FL` through `ι` and
`L/K` is algebraic, a `K⟮t⟯`-basis of `F` maps to an `L⟮ι t⟯`-basis of `FL`, so
`[FL : L⟮ι t⟯] = [F : K⟮t⟯]`. -/
theorem finrank_adjoin_eq (ι : F →ₐ[K] FL) [Algebra.IsAlgebraic K L]
    (hbij : Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)))
    (t : F) [FiniteDimensional K⟮t⟯ F] :
    Module.finrank (IntermediateField.adjoin L {ι t}) FL = Module.finrank K⟮t⟯ F := by
  classical
  set L' := IntermediateField.adjoin L {ι t}
  set n := Module.finrank K⟮t⟯ F
  let b := Module.finBasis K⟮t⟯ F
  let v : Fin n → FL := fun i => ι (b i)
  let ℓ := Module.Basis.ofVectorSpace K L
  have H := IntermediateField.LinearDisjoint.of_isField' (isField_tensor ι hbij) ι
    (IsScalarTower.toAlgHom K L FL)
  let ℓ' : Module.Basis.ofVectorSpaceIndex K L → (Lr K L FL) :=
    fun j => ⟨algebraMap L FL (ℓ j), ⟨ℓ j, rfl⟩⟩
  have hℓ' : LinearIndependent K ℓ' := by
    have := ℓ.linearIndependent.map' (IsScalarTower.toAlgHom K L FL).toLinearMap
      (LinearMap.ker_eq_bot.mpr (IsScalarTower.toAlgHom K L FL).injective)
    refine LinearIndependent.of_comp (Lr K L FL).val.toLinearMap ?_
    exact this
  have hind := H.linearIndependent_right hℓ'
  -- linear independence of `v` over `L'`
  have hli : LinearIndependent L' v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose e he using fun i => mem_adjoin_repr ι t ℓ (g i : FL) (g i).2
    set S := Finset.univ.biUnion fun i => (e i).support
    have hsum : ∀ i, (g i : FL) = ∑ j ∈ S, ι ((e i j : K⟮t⟯) : F) * algebraMap L FL (ℓ j) := by
      intro i
      rw [he i]
      exact Finsupp.sum_of_support_subset _ (fun j hj => Finset.mem_biUnion.mpr ⟨i, by simp, hj⟩)
        _ (fun j _ => by simp)
    have hg' : ∑ j ∈ S, ι (∑ i, (e i j : K⟮t⟯) • b i) * algebraMap L FL (ℓ j) = 0 := by
      rw [← hg]
      have h1 : ∀ i, g i • v i = (g i : FL) * ι (b i) := fun i => rfl
      simp only [h1, hsum, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [show ∀ (c : K⟮t⟯) (x : F), c • x = (c : F) * x from fun c x => rfl, map_mul]
      ring
    have hzero : ∀ j ∈ S, ∑ i, (e i j : K⟮t⟯) • b i = 0 := by
      intro j hj
      have := linearIndependent_iff'.mp hind S
        (fun j => ⟨ι (∑ i, (e i j : K⟮t⟯) • b i), ⟨_, rfl⟩⟩) (by
          rw [← hg']
          refine Finset.sum_congr rfl fun j _ => ?_
          rfl) j hj
      have h2 : ι (∑ i, (e i j : K⟮t⟯) • b i) = 0 := congrArg Subtype.val this
      exact ι.injective (h2.trans (map_zero ι).symm)
    have hcoef : ∀ j ∈ S, e i j = 0 := fun j hj =>
      Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => e i j) (hzero j hj) i
    apply Subtype.ext
    rw [hsum i]
    simp only [ZeroMemClass.coe_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hcoef j hj]
    simp
  -- spanning
  have hsp : ⊤ ≤ Submodule.span L' (Set.range v) := by
    rintro z -
    obtain ⟨w, rfl⟩ := hbij.2 z
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f l =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, ← b.sum_repr f, map_sum, Finset.sum_mul]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hmem : ι ((b.repr f i : K⟮t⟯) : F) * algebraMap L FL l ∈ L' :=
        mul_mem (ι_mem_adjoin ι t _) (IntermediateField.algebraMap_mem L' l)
      have : ι (b.repr f i • b i) * (IsScalarTower.toAlgHom K L FL) l =
          (⟨_, hmem⟩ : L') • v i := by
        rw [show ∀ (c : K⟮t⟯) (x : F), c • x = (c : F) * x from fun c x => rfl, map_mul,
          IsScalarTower.coe_toAlgHom']
        change _ = (ι ((b.repr f i : F)) * algebraMap L FL l) * ι (b i)
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]

theorem transcendental_ι (ι : F →ₐ[K] FL) [Algebra.IsAlgebraic K L] (t : F)
    (ht : Transcendental K t) : Transcendental L (ι t) :=
  Transcendental.extendScalars L (fun h => ht ((isAlgebraic_algHom_iff ι ι.injective).mp h))

end Degree

/-- **Leaf: a constant field extension of an algebraic function field is unramified** (H. Stichtenoth,
*Algebraic Function Fields and Codes*, 2nd ed., GTM 254 (2009), Thm 3.6.3(a); number UNVERIFIED, not
read). Printed: for an algebraic function field `F/K` (`K` perfect) and an algebraic constant field
extension `F' = FK'`, `F'/F` is unramified: `e(P'|P) = 1` for every place `P'` of `F'` over a place `P`
of `F`. Stated with `F' = FL ≅ F ⊗_K L` (`ι`, `L/K` algebraic; `F/K` of transcendence degree `1` and
finitely generated: `F/K(t)` finite for a transcendental `t`), places as valuation subrings, and
`e = 1` in the form: a generator `π` of the maximal ideal at `P = P' ∩ F` generates the maximal ideal at
`P'` (`v_{P'}(π) = e · v_P(π) = 1`). For the trivial valuation ring both sides say `0 = 0`. -/
def ConstantFieldExtensionUnramified : Prop :=
  ∀ (K F L FL : Type) [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL] [CharZero K] [Algebra.IsAlgebraic K L]
    (ι : F →ₐ[K] FL),
    (∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K {t}) F) →
    Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)) →
    ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ∀ π : F,
      π ∈ (w.comap (ι : F →+* FL)).nonunits →
      (∀ x ∈ (w.comap (ι : F →+* FL)).nonunits, ∃ y ∈ w.comap (ι : F →+* FL), x = π * y) →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = ι π * y

/-- **A Belyi function stays a Belyi function under the constant field extension (glue, proved
from the leaf).** -/
theorem isBelyiFunction_baseChange (hS : ConstantFieldExtensionUnramified)
    {K F L FL : Type} [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL] [CharZero K] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L] (ι : F →ₐ[K] FL)
    (hbij : Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)))
    (t : F) (hB : LeafModCurves.IsBelyiFunction K F t) (d : ℕ)
    (hd : Module.finrank (IntermediateField.adjoin K {t}) F = d) (hd0 : 0 < d) :
    LeafModCurves.IsBelyiFunction L FL (ι t) ∧
      Module.finrank (IntermediateField.adjoin L {ι t}) FL = d := by
  haveI : FiniteDimensional (IntermediateField.adjoin K {t}) F :=
    Module.finite_of_finrank_pos (hd ▸ hd0)
  refine ⟨⟨transcendental_ι ι t hB.1, belyi_unram ι t hB.2 ?_⟩, ?_⟩
  · exact hS K F L FL ι ⟨t, hB.1, inferInstance⟩ hbij
  · rw [finrank_adjoin_eq ι hbij t, hd]

end JavanpeykarDict
