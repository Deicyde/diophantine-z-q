import ZInQKernel.Contrib.RC53Assist.DivisionPoints.Support
import ZInQKernel.Contrib.CloudB3E2Norm.RingClassKS

/-!
# Division points of points over an unramified extension lie in `K_{S₀}`

Manuscript `diophantine_zq.tex`, tex 3080–3084 and 3293–3295 (the Kummer classes of the Heegner
points in the cohomology of `G_{K,S}`): the `2^i`-division points of the Heegner points, which are
defined over the ring class fields `H_f`, have coordinates in `K_{S₀}`.

`RC53Assist/DivisionPoints/Support.lean` proves this for points of `E(K)` (Silverman,
*The Arithmetic of Elliptic Curves*, Proposition VIII.1.5(b)). Here the argument is redone for a
point `P` with coordinates in a finite normal extension `F ⊆ K̄` of `K` that is unramified outside
`S₀` (for `F = H_f`, `S₀` containing the primes dividing the conductor):

* `fixes_of_inertia` (PROVED): an inertia element of a finite Galois `L ⊇ F` at a prime above
  `v ∉ S₀` fixes `F` pointwise. Its restriction to `F` lies in the inertia group of `F` at the
  prime below, whose order is the ramification index (`Ideal.card_inertia_eq_ramificationIdx`), one
  because `F` is unramified at `v`.
* `conjPoints`, `divPoints`, `divCoords`, `divFieldF` (definitions): the conjugates of `P`, their
  `m`-division points, their coordinates, and `L = F(divCoords)`; `finite_divPoints`,
  `finiteDimensional_divFieldF`, `normal_divFieldF` (PROVED).
* **`isUnramifiedOutside_divFieldF`** (PROVED): `L/K` is unramified outside `S₀`. This is the
  argument of `Support.isUnramifiedOutside_divisionField` (an inertia element `σ` does not change the
  reduction of a point of `E(L)`; for a division point `R` of a conjugate `P'`, `σ R − R` is killed by
  `m` and reduces to the origin, so `σ R = R`), with `σ P' = P'` from `fixes_of_inertia`.
* `divFieldF_le_unramifiedOutside`, `le_unramifiedOutside_of_field` (PROVED): `L ⊆ K_{S₀}`, `F ⊆ K_{S₀}`.
* **`exists_supportPoint_of_field`** (PROVED): every `m`-division point over `K̄` of `P` is defined
  over `K_{S₀}`, when `S₀` contains the places dividing `m` and `E` has good reduction outside `S₀`;
  **`exists_nsmul_eq_of_field`** (PROVED): some `Q ∈ E(K_{S₀})` has `m Q = P`.
* **`exists_supportPoint_ringClassField`** (PROVED): the case `F = H_O`, Tau Ceti's ring class field
  of an order `O` (read in `K̄`), when `S₀` contains the primes dividing the conductor of `O`; the
  hypotheses on `F` are discharged by `RingClassKS.isUnramifiedOutside_toAlgClosure` and Tau Ceti's
  `isUnramifiedAt_ringClassField`. The good-reduction and `m`-hypotheses are those of
  `Support.lean` (discharged there for curves of the text, e.g. `hasGoodReductionAt_curveEll`).

Kinds: definitions and PROVED. No printed statement is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.DivisionPointsF

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside IsUnramifiedOutside)
open ZInQ.Manuscript.RC.CoefModules (KS)
open ZInQ.Manuscript.RC.DivisionPoints

/-! ### Inertia fixes an unramified subextension -/

section Fixes

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {S0 : Set (HeightOneSpectrum (𝓞 K))}

/-- The inclusion of rings of integers `𝒪_F → 𝒪_L` for `F ≤ L`. Kind: definition. -/
def intIncl {F L : IntermediateField K (AlgebraicClosure K)} (hFL : F ≤ L) :
    integralClosure (𝓞 K) F →+* integralClosure (𝓞 K) L where
  toFun x := ⟨IntermediateField.inclusion hFL x, by
    have hx : IsIntegral (𝓞 K) (x : F) := x.2
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p, hp, ?_⟩
    have h := congrArg (IntermediateField.inclusion hFL) hpx
    rw [map_zero, Polynomial.eval₂_eq_sum_range, map_sum] at h
    rw [Polynomial.eval₂_eq_sum_range]
    simpa using h⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem algebraMap_intIncl {F L : IntermediateField K (AlgebraicClosure K)} (hFL : F ≤ L)
    (x : integralClosure (𝓞 K) F) :
    algebraMap (integralClosure (𝓞 K) L) L (intIncl hFL x) =
      IntermediateField.inclusion hFL (algebraMap (integralClosure (𝓞 K) F) F x) := rfl

theorem intIncl_algebraMap {F L : IntermediateField K (AlgebraicClosure K)} (hFL : F ≤ L)
    (a : 𝓞 K) :
    intIncl hFL (algebraMap (𝓞 K) (integralClosure (𝓞 K) F) a) =
      algebraMap (𝓞 K) (integralClosure (𝓞 K) L) a := rfl

/-- **Inertia fixes an unramified normal subextension** (PROVED): if `F ≤ L` are finite normal
subextensions of `K̄/K`, `F` is unramified outside `S₀`, `Q` is a prime of `𝒪_L` above `v ∉ S₀`,
and `σ ∈ Gal(L/K)` acts trivially modulo `Q` on `𝒪_L`, then `σ` fixes `F` pointwise. -/
theorem fixes_of_inertia {F L : IntermediateField K (AlgebraicClosure K)} (hFL : F ≤ L)
    [FiniteDimensional K F] [Normal K F] [FiniteDimensional K L] [Normal K L]
    (hF : IsUnramifiedOutside K S0 F) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S0)
    (Q : Ideal (integralClosure (𝓞 K) L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ a : integralClosure (𝓞 K) L, ∃ b, algebraMap _ L b = σ (algebraMap _ L a) ∧
      b - a ∈ Q)
    (x : F) : σ (IntermediateField.inclusion hFL x) = IntermediateField.inclusion hFL x := by
  let : Algebra F L := (IntermediateField.inclusion hFL).toAlgebra
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsGalois K F := {}
  have : Module.Finite (𝓞 K) (integralClosure (𝓞 K) F) :=
    IsIntegralClosure.finite (𝓞 K) K F _
  have : IsDedekindDomain (integralClosure (𝓞 K) F) :=
    IsIntegralClosure.isDedekindDomain (𝓞 K) K F _
  have : IsFractionRing (integralClosure (𝓞 K) F) F :=
    IsIntegralClosure.isFractionRing_of_finite_extension (𝓞 K) K F _
  let := IsIntegralClosure.MulSemiringAction (𝓞 K) K F (integralClosure (𝓞 K) F)
  have : IsGaloisGroup (F ≃ₐ[K] F) (𝓞 K) (integralClosure (𝓞 K) F) :=
    IsGaloisGroup.of_isFractionRing _ _ _ K F
  let σF : F ≃ₐ[K] F := σ.restrictNormal F
  have hσF : ∀ y : F, IntermediateField.inclusion hFL (σF y) =
      σ (IntermediateField.inclusion hFL y) := fun y => AlgEquiv.restrictNormal_commutes σ F y
  let QF : Ideal (integralClosure (𝓞 K) F) := Q.comap (intIncl hFL)
  have : QF.IsPrime := Ideal.comap_isPrime _ _
  have : QF.LiesOver v.asIdeal := by
    constructor
    rw [Ideal.over_def Q v.asIdeal, Ideal.under, Ideal.under, Ideal.comap_comap]
    rfl
  have hinj : Function.Injective (algebraMap (integralClosure (𝓞 K) L) L) :=
    Subtype.val_injective
  have hmem : σF ∈ QF.inertia (F ≃ₐ[K] F) := by
    rw [Ideal.mem_inertia]
    intro a
    obtain ⟨b, hb, hba⟩ := hσ (intIncl hFL a)
    have hj : intIncl hFL (σF • a) = b := by
      apply hinj
      rw [hb, algebraMap_intIncl, algebraMap_intIncl]
      change IntermediateField.inclusion hFL (algebraMap _ F ((galRestrict (𝓞 K) K F _ σF) a)) = _
      rw [algebraMap_galRestrict_apply, hσF]
    change intIncl hFL (σF • a - a) ∈ Q
    rw [(intIncl hFL).map_sub, hj]
    exact hba
  have hcard : Nat.card (QF.inertia (F ≃ₐ[K] F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdx (𝓞 K) (F ≃ₐ[K] F) QF]
    exact hF v hv QF inferInstance inferInstance
  have h1 : σF = 1 := by
    have hsub := (Nat.card_eq_one_iff_unique.1 hcard).1
    exact congrArg Subtype.val (hsub.elim ⟨σF, hmem⟩ ⟨1, one_mem _⟩)
  rw [← hσF, h1]
  rfl

end Fixes

/-! ### The division field of a point over `F` -/

section Field

open scoped Classical

variable {K : Type} [Field K] [NumberField K] (W : WeierstrassCurve K)
  (F : IntermediateField K (AlgebraicClosure K)) (P₀ : (W.baseChange F).toAffine.Point)

/-- The point `P ∈ E(K̄)` of `P₀ ∈ E(F)`. Kind: definition. -/
def basePt : (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  Affine.Point.map (W' := W) F.val P₀

/-- The `m`-division points of the conjugates of `P` over `K̄`. Kind: definition. -/
def divPoints (m : ℕ) : Set (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  {R | ∃ σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K,
    m • R = Affine.Point.map (W' := W) σ (basePt W F P₀)}

/-- Their coordinates. Kind: definition. -/
def divCoords (m : ℕ) : Set (AlgebraicClosure K) :=
  Affine.Point.xCoord '' divPoints W F P₀ m ∪ Affine.Point.yCoord '' divPoints W F P₀ m

/-- **The field `L = F(divCoords)`**. Kind: definition. -/
def divFieldF (m : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  F ⊔ IntermediateField.adjoin K (divCoords W F P₀ m)

theorem le_divFieldF (m : ℕ) : F ≤ divFieldF W F P₀ m := le_sup_left

variable [W.IsElliptic]

/-- The solutions of `m R = X` over `K̄` form a finite set (a coset of the `m`-torsion).
Kind: PROVED. -/
theorem finite_nsmul_eq {m : ℕ} (hm : m ≠ 0) (X : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    {R : (W.baseChange (AlgebraicClosure K)).toAffine.Point | m • R = X}.Finite := by
  have hm' : (m : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.2 hm
  obtain ⟨Q₀, hQ₀⟩ := (W.baseChange (AlgebraicClosure K)).toAffine.nsmul_surjective hm' X
  have hQ₀' : m • Q₀ = X := hQ₀
  have : Finite (AddSubgroup.torsionBy
      (W.baseChange (AlgebraicClosure K)).toAffine.Point (m : ℤ)) :=
    (W.baseChange (AlgebraicClosure K)).finite_torsionBy (by exact_mod_cast hm)
  refine (Set.finite_range fun t : AddSubgroup.torsionBy
    (W.baseChange (AlgebraicClosure K)).toAffine.Point (m : ℤ) => Q₀ + (t : _)).subset ?_
  intro Q hQ
  have hQ' : m • Q = X := hQ
  refine ⟨⟨Q - Q₀, (Submodule.mem_torsionBy_iff (R := ℤ) _ _).2 ?_⟩, ?_⟩
  · rw [smul_sub, natCast_zsmul, natCast_zsmul, hQ', hQ₀', sub_self]
  · show Q₀ + (Q - Q₀) = Q
    abel

omit [NumberField K] [W.IsElliptic] in
/-- The conjugates `σ P` are the points `τ P₀` for `τ : F → K̄`. Kind: PROVED. -/
theorem map_basePt (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    Affine.Point.map (W' := W) σ (basePt W F P₀) =
      Affine.Point.map (W' := W) (σ.comp F.val) P₀ := by
  rw [basePt, Affine.Point.map_map]

/-- There are finitely many division points of the conjugates. Kind: PROVED. -/
theorem finite_divPoints [FiniteDimensional K F] {m : ℕ} (hm : m ≠ 0) :
    (divPoints W F P₀ m).Finite := by
  refine (Set.finite_iUnion fun τ : F →ₐ[K] AlgebraicClosure K =>
    finite_nsmul_eq W hm (Affine.Point.map (W' := W) τ P₀)).subset ?_
  rintro R ⟨σ, hσ⟩
  exact Set.mem_iUnion.2 ⟨σ.comp F.val, by rw [Set.mem_ofPred_eq, hσ, map_basePt]⟩

theorem finite_divCoords [FiniteDimensional K F] {m : ℕ} (hm : m ≠ 0) :
    (divCoords W F P₀ m).Finite :=
  ((finite_divPoints W F P₀ hm).image _).union ((finite_divPoints W F P₀ hm).image _)

/-- `L` is finite over `K`. Kind: PROVED. -/
theorem finiteDimensional_divFieldF [FiniteDimensional K F] {m : ℕ} (hm : m ≠ 0) :
    FiniteDimensional K (divFieldF W F P₀ m) := by
  have := (finite_divCoords W F P₀ hm).to_subtype
  have : FiniteDimensional K (IntermediateField.adjoin K (divCoords W F P₀ m)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

omit [W.IsElliptic] in
/-- The division points of the conjugates are permuted by `Aut(K̄/K)`. Kind: PROVED. -/
theorem map_mem_divPoints (τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) {m : ℕ}
    {R : (W.baseChange (AlgebraicClosure K)).toAffine.Point} (hR : R ∈ divPoints W F P₀ m) :
    Affine.Point.map (W' := W) τ R ∈ divPoints W F P₀ m := by
  obtain ⟨σ, hσ⟩ := hR
  refine ⟨τ.comp σ, ?_⟩
  rw [← map_nsmul, hσ, Affine.Point.map_map]

omit [W.IsElliptic] in
/-- `L` is normal over `K`. Kind: PROVED. -/
theorem normal_divFieldF [Normal K F] (m : ℕ) : Normal K (divFieldF W F P₀ m) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  rw [divFieldF, IntermediateField.map_sup]
  refine sup_le_sup (IntermediateField.normal_iff_forall_map_le'.1 inferInstance σ) ?_
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨c, hc, rfl⟩
  apply IntermediateField.subset_adjoin
  have hσ := fun {R} (hR : R ∈ divPoints W F P₀ m) =>
    map_mem_divPoints W F P₀ (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) hR
  rcases hc with ⟨R, hR, rfl⟩ | ⟨R, hR, rfl⟩
  · exact Or.inl ⟨_, hσ hR, Affine.Point.xCoord_map _ _⟩
  · exact Or.inr ⟨_, hσ hR, Affine.Point.yCoord_map _ _⟩

end Field

/-! ### `L` is unramified outside `S₀` -/

section Unramified

open scoped Classical

variable {K : Type} [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]
  (F : IntermediateField K (AlgebraicClosure K)) (P₀ : (W.baseChange F).toAffine.Point)

/-- **`L = F(divCoords)` is unramified outside `S₀`** (PROVED; Silverman VIII.1.5(b) over `F`):
when `F/K` is finite normal and unramified outside `S₀`, `S₀` contains the places dividing `m`
and `W` has good reduction outside `S₀`. -/
theorem isUnramifiedOutside_divFieldF [FiniteDimensional K F] [Normal K F]
    {S0 : Set (HeightOneSpectrum (𝓞 K))} (hF : IsUnramifiedOutside K S0 F) {m : ℕ} (hm : m ≠ 0)
    (hmS : ∀ v : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ v.asIdeal → v ∈ S0)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S0 → HasGoodReductionAt W v) :
    IsUnramifiedOutside K S0 (divFieldF W F P₀ m) := by
  set L := divFieldF W F P₀ m with hLdef
  have hFL : F ≤ L := le_divFieldF W F P₀ m
  intro v hv Q hQ hQv
  have : FiniteDimensional K L := finiteDimensional_divFieldF W F P₀ hm
  have : Normal K L := normal_divFieldF W F P₀ m
  have : IsGalois K L := {}
  have : Module.Finite (𝓞 K) (integralClosure (𝓞 K) L) :=
    IsIntegralClosure.finite (𝓞 K) K L _
  have : IsDedekindDomain (integralClosure (𝓞 K) L) :=
    IsIntegralClosure.isDedekindDomain (𝓞 K) K L _
  have : IsFractionRing (integralClosure (𝓞 K) L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension (𝓞 K) K L _
  let := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (integralClosure (𝓞 K) L)
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (integralClosure (𝓞 K) L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ K L
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let u : HeightOneSpectrum (integralClosure (𝓞 K) L) := ⟨Q, hQ, hQne⟩
  have huv : ∀ a : 𝓞 K, algebraMap (𝓞 K) _ a ∈ u.asIdeal ↔ a ∈ v.asIdeal := by
    intro a
    rw [Ideal.over_def Q v.asIdeal]
    rfl
  rw [← Ideal.card_inertia_eq_ramificationIdx (𝓞 K) (L ≃ₐ[K] L) Q]
  suffices hbot : Q.inertia (L ≃ₐ[K] L) = ⊥ by
    rw [hbot]
    exact Subgroup.card_bot
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have hcong : ∀ ρ ∈ Q.inertia (L ≃ₐ[K] L),
      ∀ a : integralClosure (𝓞 K) L,
        ∃ b, algebraMap _ L b = ρ (algebraMap _ _ a) ∧ b - a ∈ u.asIdeal :=
    fun ρ hρ a => ⟨ρ • a, algebraMap_galRestrict_apply (𝓞 K) ρ a, Ideal.mem_inertia.1 hρ a⟩
  have hFfix := fixes_of_inertia hFL hF hv Q σ (hcong σ hσ)
  obtain ⟨τ, hτ, rfl⟩ :=
    exists_mem_inertiaSubgroup u σ (hcong σ hσ) (hcong σ⁻¹ (inv_mem hσ))
  obtain ⟨C, h₁, h₂, h₃, h₄, h₆, hΔ⟩ := hgood v hv
  have hmu : (m : integralClosure (𝓞 K) L) ∉ u.asIdeal := by
    rw [← map_natCast (algebraMap (𝓞 K) (integralClosure (𝓞 K) L)), huv]
    exact fun h => hv (hmS v h)
  have hτF : ∀ ρ : F →ₐ[K] F,
      ((τ : L ≃ₐ[K] L).toAlgHom.comp ((IntermediateField.inclusion hFL).comp ρ)) =
        (IntermediateField.inclusion hFL).comp ρ := by
    intro ρ
    ext x
    exact congrArg Subtype.val (hFfix (ρ x))
  have hfix : ∀ R ∈ divPoints W F P₀ m,
      ∃ R' : (W.baseChange L).toAffine.Point,
        Affine.Point.map (W' := W) L.val R' = R ∧
          Affine.Point.map (W' := W) (τ : L ≃ₐ[K] L).toAlgHom R' = R' := by
    intro R hR
    obtain ⟨σ', hσ'⟩ := hR
    have hx : Affine.Point.xCoord R ∈ Set.range L.val :=
      ⟨⟨_, le_sup_right (a := F) (IntermediateField.subset_adjoin K _
        (Or.inl ⟨R, ⟨σ', hσ'⟩, rfl⟩))⟩, rfl⟩
    have hy : Affine.Point.yCoord R ∈ Set.range L.val :=
      ⟨⟨_, le_sup_right (a := F) (IntermediateField.subset_adjoin K _
        (Or.inr ⟨R, ⟨σ', hσ'⟩, rfl⟩))⟩, rfl⟩
    obtain ⟨R', hR'⟩ := (Affine.Point.exists_map_eq_iff R L.val).2 ⟨hx, hy⟩
    refine ⟨R', hR', ?_⟩
    let ρ : F →ₐ[K] F := σ'.restrictNormal F
    have hρ : L.val.comp ((IntermediateField.inclusion hFL).comp ρ) = σ'.comp F.val := by
      ext x
      exact AlgHom.restrictNormal_commutes σ' F x
    have hPL : m • R' = Affine.Point.map (W' := W) ((IntermediateField.inclusion hFL).comp ρ) P₀ := by
      apply Affine.Point.map_injective (W' := W) L.val
      rw [map_nsmul, hR', hσ', map_basePt, Affine.Point.map_map, hρ]
    refine map_eq_self_of_variableChange u W C (valuation_algebraMap_le_one v u huv h₁)
      (valuation_algebraMap_le_one v u huv h₂) (valuation_algebraMap_le_one v u huv h₃)
      (valuation_algebraMap_le_one v u huv h₄) (valuation_algebraMap_le_one v u huv h₆)
      (valuation_algebraMap_eq_one v u huv hΔ) hmu hτ ?_
    rw [hPL, Affine.Point.map_map, hτF]
  have hgen : ∀ c ∈ (F : Set (AlgebraicClosure K)) ∪ divCoords W F P₀ m, c ∈ L := by
    rintro c (hc | hc)
    · exact le_sup_left (b := IntermediateField.adjoin K (divCoords W F P₀ m)) hc
    · exact le_sup_right (a := F) (IntermediateField.subset_adjoin K _ hc)
  have htop : IntermediateField.adjoin K
      {c : L | (c : AlgebraicClosure K) ∈ (F : Set (AlgebraicClosure K)) ∪
        divCoords W F P₀ m} = ⊤ := by
    apply IntermediateField.lift_injective L
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have hset : (fun c : L => (c : AlgebraicClosure K)) ''
        {c : L | (c : AlgebraicClosure K) ∈ (F : Set (AlgebraicClosure K)) ∪
          divCoords W F P₀ m} = (F : Set (AlgebraicClosure K)) ∪ divCoords W F P₀ m := by
      ext c
      constructor
      · rintro ⟨c', hc', rfl⟩
        exact hc'
      · intro hc
        exact ⟨⟨c, hgen c hc⟩, hc, rfl⟩
    rw [hset, IntermediateField.adjoin_union, IntermediateField.adjoin_self, hLdef]
    rfl
  apply TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop
  rintro c (hcF | ⟨R, hR, hcR⟩ | ⟨R, hR, hcR⟩)
  · have hc : c = IntermediateField.inclusion hFL ⟨c, hcF⟩ := Subtype.ext rfl
    rw [hc]
    exact hFfix _
  · obtain ⟨R', hR', hfixR⟩ := hfix R hR
    have hc : c = Affine.Point.xCoord R' := by
      apply Subtype.ext
      rw [← hcR, ← hR', Affine.Point.xCoord_map]
      rfl
    rw [hc]
    exact ((Affine.Point.map_eq_self_iff _ R').1 hfixR).1
  · obtain ⟨R', hR', hfixR⟩ := hfix R hR
    have hc : c = Affine.Point.yCoord R' := by
      apply Subtype.ext
      rw [← hcR, ← hR', Affine.Point.yCoord_map]
      rfl
    rw [hc]
    exact ((Affine.Point.map_eq_self_iff _ R').1 hfixR).2

end Unramified

/-! ### Division points in `K_{S₀}` -/

section Support

open scoped Classical

variable {K : Type} [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]
  (F : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K F] [Normal K F]
  (P₀ : (W.baseChange F).toAffine.Point) {S0 : Set (HeightOneSpectrum (𝓞 K))}
  (hF : IsUnramifiedOutside K S0 F) {m : ℕ} (hm : m ≠ 0)
  (hmS : ∀ v : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ v.asIdeal → v ∈ S0)
  (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S0 → HasGoodReductionAt W v)

include hF hm hmS hgood

/-- **`L = F(divCoords)` lies in `K_{S₀}`** (PROVED). -/
theorem divFieldF_le_unramifiedOutside : divFieldF W F P₀ m ≤ unramifiedOutside K S0 :=
  le_iSup₂_of_le (f := fun (L : IntermediateField K (AlgebraicClosure K))
      (_ : FiniteDimensional K L ∧ Normal K L ∧ IsUnramifiedOutside K S0 L) => L)
    (divFieldF W F P₀ m) ⟨finiteDimensional_divFieldF W F P₀ hm, normal_divFieldF W F P₀ m,
      isUnramifiedOutside_divFieldF W F P₀ hF hm hmS hgood⟩ le_rfl

omit hm hmS hgood in
/-- **`F` lies in `K_{S₀}`** (PROVED). -/
theorem le_unramifiedOutside_of_field : F ≤ unramifiedOutside K S0 :=
  le_iSup₂_of_le (f := fun (L : IntermediateField K (AlgebraicClosure K))
      (_ : FiniteDimensional K L ∧ Normal K L ∧ IsUnramifiedOutside K S0 L) => L)
    F ⟨inferInstance, inferInstance, hF⟩ le_rfl

omit [W.IsElliptic] [FiniteDimensional K F] [Normal K F] hF hm hmS hgood in
theorem map_algHomId (X : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    Affine.Point.map (W' := W) (AlgHom.id K (AlgebraicClosure K)) X = X := by
  rcases X with _ | ⟨x, y, hxy⟩
  · rfl
  · rfl

/-- **Every `m`-division point over `K̄` of a point of `E(F)` is defined over `K_{S₀}`**
(PROVED; Silverman VIII.1.5(b) over `F`). -/
theorem exists_supportPoint_of_field (R : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (hR : m • R = basePt W F P₀) :
    ∃ Q : (W.baseChange (KS K S0)).toAffine.Point,
      Affine.Point.map (W' := W) (unramifiedOutside K S0).val Q = R := by
  have hle := divFieldF_le_unramifiedOutside W F P₀ hF hm hmS hgood
  have hRm : R ∈ divPoints W F P₀ m := ⟨AlgHom.id K _, by rw [hR, map_algHomId]⟩
  have hx : Affine.Point.xCoord R ∈ Set.range (unramifiedOutside K S0).val :=
    ⟨⟨_, hle (le_sup_right (a := F) (IntermediateField.subset_adjoin K _
      (Or.inl ⟨R, hRm, rfl⟩)))⟩, rfl⟩
  have hy : Affine.Point.yCoord R ∈ Set.range (unramifiedOutside K S0).val :=
    ⟨⟨_, hle (le_sup_right (a := F) (IntermediateField.subset_adjoin K _
      (Or.inr ⟨R, hRm, rfl⟩)))⟩, rfl⟩
  exact (Affine.Point.exists_map_eq_iff R (unramifiedOutside K S0).val).2 ⟨hx, hy⟩

/-- **Division points of points of `E(F)` exist in `E(K_{S₀})`** (PROVED): for `P₀ ∈ E(F)` there
is `Q ∈ E(K_{S₀})` with `m Q = P₀` (read in `E(K_{S₀})` through `F ⊆ K_{S₀}`). -/
theorem exists_nsmul_eq_of_field :
    ∃ Q : (W.baseChange (KS K S0)).toAffine.Point,
      m • Q = Affine.Point.map (W' := W)
        (IntermediateField.inclusion (le_unramifiedOutside_of_field F hF)) P₀ := by
  have hm' : (m : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.2 hm
  obtain ⟨R, hR⟩ :=
    (W.baseChange (AlgebraicClosure K)).toAffine.nsmul_surjective hm' (basePt W F P₀)
  obtain ⟨Q, hQ⟩ := exists_supportPoint_of_field W F P₀ hF hm hmS hgood R hR
  refine ⟨Q, Affine.Point.map_injective (W' := W) (unramifiedOutside K S0).val ?_⟩
  rw [map_nsmul, hQ, Affine.Point.map_map]
  exact hR

end Support

/-! ### The ring class fields -/

section RingClass

open scoped Classical
open ZInQ.Contrib.CloudB3E2.NormCochain (toAlgClosure isUnramifiedOutside_toAlgClosure)
open TauCeti.GlobalNumberFields

variable {K : Type} [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]
  (O : NumberFieldOrder K) {S0 : Set (HeightOneSpectrum (𝓞 K))}

/-- **Division points of points over a ring class field lie in `E(K_{S₀})`** (PROVED; tex
3080–3084, 3293–3295): if `S₀` contains the primes dividing the conductor of `O` and the places
dividing `m`, and `W` has good reduction outside `S₀`, every `m`-division point over `K̄` of a
point of `E(H_O)` (`H_O` Tau Ceti's ring class field, read in `K̄`) is defined over `K_{S₀}`. -/
theorem exists_supportPoint_ringClassField
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ O.conductor → v ∈ S0) {m : ℕ} (hm : m ≠ 0)
    (hmS : ∀ v : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ v.asIdeal → v ∈ S0)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S0 → HasGoodReductionAt W v)
    (P₀ : (W.baseChange (toAlgClosure (TauCeti.ClassFieldTheory.ringClassField O))).toAffine.Point)
    (R : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (hR : m • R = basePt W (toAlgClosure (TauCeti.ClassFieldTheory.ringClassField O)) P₀) :
    ∃ Q : (W.baseChange (KS K S0)).toAffine.Point,
      Affine.Point.map (W' := W) (unramifiedOutside K S0).val Q = R := by
  have hU : IsUnramifiedOutside K S0 (toAlgClosure (TauCeti.ClassFieldTheory.ringClassField O)) :=
    isUnramifiedOutside_toAlgClosure S0 (TauCeti.ClassFieldTheory.ringClassField O)
      fun v hv Q _ _ =>
        TauCeti.ClassFieldTheory.isUnramifiedAt_ringClassField O (fun hd => hv (hS v hd)) Q
  have hN : Normal K (toAlgClosure (TauCeti.ClassFieldTheory.ringClassField O)) :=
    Normal.of_algEquiv (IntermediateField.equivMap (TauCeti.ClassFieldTheory.ringClassField O)
      (separableClosure K (AlgebraicClosure K)).val)
  exact exists_supportPoint_of_field W _ P₀ hU hm hmS hgood R hR

end RingClass

end ZInQ.Contrib.CloudB3E2.DivisionPointsF
