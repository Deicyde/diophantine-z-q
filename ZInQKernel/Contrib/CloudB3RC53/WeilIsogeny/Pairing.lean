import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.Divisor
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber

/-!
# The Weil pairing under a separable isogeny

For a separable isogeny `φ : W₁ → W₂` of elliptic curves over a separably closed field `F` and `N`
invertible in `F`, with `S, T ∈ W₁[N]`,

    e_N(φ S, φ T) = e_N(S, T)^{deg φ}        (`weilPairing_torsionMap`; a consequence
of Silverman III.8.2, `e_N(S, φ̂ T) = e_N(φ S, T)`, proved here without the dual isogeny).

Proof (no dual isogeny). Let `g₂` have divisor `[N]^* (φ T) − [N]^* (O)` on `W₂`, so that
`e_N(φ S, φ T) = τ_{φ S} g₂ / g₂`. Pull back along `φ`: since `φ^* ∘ τ_{φ S}^* = τ_S^* ∘ φ^*`
(`fieldPullback_comp_translation`), `e_N(φ S, φ T) = τ_S G / G` for `G = φ^* g₂`, the Kummer
character of `[N]` at `G` (`Gᴺ = φ^* g₂ᴺ` is a pullback along `[N]` because `φ` commutes with
`[N]`). The divisor of `G` is `[N]^* (∑_{R ∈ ker φ} ((T + R) − (R)))` (`pb_weilPairingDivisor`),
which is also the divisor of `g₁^{deg φ} · [N]^* H`, for `g₁` the Weil function of `T` on `W₁` and
`H` a function with divisor `∑_{R ∈ ker φ} ((T + R) − (T) − (R) + (O))`
(`exists_principal_eq_ofPoint_add_sub`), using `|ker φ| = deg φ`. The Kummer character depends only
on the divisor, is multiplicative, and is trivial on pullbacks along `[N]`; so
`τ_S G / G = (τ_S g₁ / g₁)^{deg φ} = e_N(S, T)^{deg φ}`.

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny AlgebraicGeometry

namespace ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] {W₁ W₂ : WeierstrassCurve F}
  [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
  (N : ℕ) [NeZero N] (hN : (N : F) ≠ 0)

omit [DecidableEq F] [IsSepClosed F] [W₁.IsElliptic] [W₂.IsElliptic] [NeZero N] in
include hN in
private theorem intCast_ne_zero' : ((N : ℤ) : F) ≠ 0 := by rwa [Int.cast_natCast]

/-- `φ` maps `W₁[N]` to `W₂[N]`. -/
def torsionMap (S : Submodule.torsionBy ℤ W₁.toAffine.Point (N : ℤ)) :
    Submodule.torsionBy ℤ W₂.toAffine.Point (N : ℤ) :=
  ⟨(Hom.ofIsogeny φ).pointMap S, by
    have := W₂.toAffine.isIntegrallyClosed_coordinateRing
    rw [Submodule.mem_torsionBy_iff, Hom.pointMap_ofIsogeny_eq_toPointHom, ← map_zsmul,
      (Submodule.mem_torsionBy_iff _ _).mp S.2, map_zero]⟩

omit [IsSepClosed F] in
theorem kummerCharacter_congr {W W' : WeierstrassCurve.Affine F} [W.IsElliptic]
    (ψ : Isogeny W W') {g g' : W.FunctionFieldˣ} (e : g = g')
    (hg : (g : W.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange)
    (hg' : (g' : W.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange) :
    ψ.kummerCharacter N g hg = ψ.kummerCharacter N g' hg' := by
  subst e; rfl

omit [IsSepClosed F] in
theorem kummerCharacter_pow {W W' : WeierstrassCurve.Affine F} [W.IsElliptic]
    (ψ : Isogeny W W') {g : W.FunctionFieldˣ}
    (hg : (g : W.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange) (d : ℕ)
    (hgd : ((g ^ d : W.FunctionFieldˣ) : W.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange) :
    ψ.kummerCharacter N (g ^ d) hgd = ψ.kummerCharacter N g hg ^ d := by
  induction d with
  | zero =>
    have h1 : ((1 : W.FunctionFieldˣ) : W.FunctionField) ∈ ψ.fieldPullback.fieldRange := one_mem _
    rw [kummerCharacter_congr N ψ (pow_zero g) hgd (pow_mem h1 N), pow_zero]
    exact kummerCharacter_eq_one_of_mem_fieldRange h1
  | succ d ih =>
    have hd : ((g ^ d : W.FunctionFieldˣ) : W.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange := by
      rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]; exact pow_mem hg d
    rw [kummerCharacter_congr N ψ (pow_succ g d) hgd
      (by rw [Units.val_mul, mul_pow]; exact mul_mem hd hg), kummerCharacter_mul hd hg, ih hd,
      pow_succ]

omit [W₁.IsElliptic] [W₂.IsElliptic] [IsSepClosed F] [DecidableEq F] in
/-- A product of functions has the sum of their divisors. -/
theorem principal_prod {W : WeierstrassCurve.Affine F} {ι : Type*} (s : Finset ι)
    (f : ι → W.FunctionFieldˣ) :
    Divisor.principal W.isFunctionField (∏ i ∈ s, f i) =
      ∑ i ∈ s, Divisor.principal W.isFunctionField (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, Divisor.principal_mul, ih]

omit [W₁.IsElliptic] [W₂.IsElliptic] [IsSepClosed F] [DecidableEq F] in
theorem principal_pow {W : WeierstrassCurve.Affine F} (g : W.FunctionFieldˣ) (d : ℕ) :
    Divisor.principal W.isFunctionField (g ^ d) = d • Divisor.principal W.isFunctionField g := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ, Divisor.principal_mul, ih, succ_nsmul]

/-- **`|ker φ| = deg φ`**, for the kernel as the finite set of points sent to `O`. PROVED. -/
theorem card_kerFinset :
    (Hom.finite_setOf_pointMap_eq (Hom.ofIsogeny_ne_zero φ) 0).toFinset.card = φ.degree := by
  have := W₁.toAffine.isIntegrallyClosed_coordinateRing
  have := W₂.toAffine.isIntegrallyClosed_coordinateRing
  have := W₂.toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed
  rw [← Set.ncard_eq_toFinset_card _ (Hom.finite_setOf_pointMap_eq (Hom.ofIsogeny_ne_zero φ) 0),
    ← φ.ncard_fiber_toPointHom_eq_degree 0]
  congr 1
  ext R
  simp only [Set.mem_ofPred_eq, Hom.pointMap_ofIsogeny_eq_toPointHom]

include hN in
/-- **The Weil pairing under a separable isogeny: `e_N(φ S, φ T) = e_N(S, T)^{deg φ}`**
(a consequence of Silverman III.8.2, written additively in `Additive (rootsOfUnity N F)`). PROVED.
-/
theorem weilPairing_torsionMap (S T : Submodule.torsionBy ℤ W₁.toAffine.Point (N : ℤ)) :
    weilPairing W₂ N hN (torsionMap φ N S) (torsionMap φ N T) =
      φ.degree • weilPairing W₁ N hN S T := by
  classical
  have := W₁.toAffine.isIntegrallyClosed_coordinateRing
  have := W₁.toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed
  have hc := intCast_ne_zero' N hN
  have h₁ := psiFunctionField_ne_zero W₁.toAffine hc
  have h₂ := psiFunctionField_ne_zero W₂.toAffine hc
  have hT₁ : (N : ℤ) • (T : W₁.toAffine.Point) = 0 := (Submodule.mem_torsionBy_iff _ _).mp T.2
  have hT₂ : (N : ℤ) • ((torsionMap φ N T : Submodule.torsionBy ℤ W₂.toAffine.Point (N : ℤ)) :
      W₂.toAffine.Point) = 0 := (Submodule.mem_torsionBy_iff _ _).mp (torsionMap φ N T).2
  obtain ⟨g₂, hg₂⟩ := exists_principal_eq_weilPairingDivisor W₂ hc hT₂
  obtain ⟨g₁, hg₁⟩ := exists_principal_eq_weilPairingDivisor W₁ hc hT₁
  set K := (Hom.finite_setOf_pointMap_eq (Hom.ofIsogeny_ne_zero φ) 0).toFinset
  set ψ := mulByIntIsogeny W₁.toAffine (psiFunctionField_ne_zero W₁.toAffine hc)
  -- the correcting function `H`
  have hex := fun R : W₁.toAffine.Point =>
    W₁.toAffine.exists_principal_eq_ofPoint_add_sub (T : W₁.toAffine.Point) R
  set H : W₁.toAffine.FunctionFieldˣ := ∏ R ∈ K, (hex R).choose
  have hH : Divisor.principal W₁.toAffine.isFunctionField H =
      ∑ R ∈ K, (WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 -
        WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace T).1 -
        (WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace R).1 -
          WeilDivisor.ofPoint (Place.infinity W₁.toAffine))) := by
    rw [principal_prod]
    exact Finset.sum_congr rfl fun R _ => (hex R).choose_spec
  -- the pulled-back Weil function `G` and the comparison function `g'`
  set G : W₁.toAffine.FunctionFieldˣ :=
    Units.map (φ.fieldPullback : W₂.toAffine.FunctionField →* W₁.toAffine.FunctionField) g₂
  set g' : W₁.toAffine.FunctionFieldˣ := g₁ ^ φ.degree *
    Units.map (ψ.fieldPullback : W₁.toAffine.FunctionField →* W₁.toAffine.FunctionField) H
  have hpbP : ∀ {A B : WeierstrassCurve.Affine F} (χ : Isogeny A B) (z : B.FunctionFieldˣ),
      pb χ (Divisor.principal B.isFunctionField z) = Divisor.principal A.isFunctionField
        (Units.map (χ.fieldPullback : B.FunctionField →* A.FunctionField) z) :=
    fun χ z => @Isogeny.divisorPullback_principal F _ _ _ χ χ.fieldPullback.toRingHom.toAlgebra
      (fun _ => rfl) z
  have hdivG : Divisor.principal W₁.toAffine.isFunctionField G =
      pb ψ (∑ R ∈ K, (WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 -
        WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace R).1)) := by
    rw [← hpbP, hg₂]
    exact pb_weilPairingDivisor φ (psiFunctionField_ne_zero W₁.toAffine hc) _ T
  have hdivg' : Divisor.principal W₁.toAffine.isFunctionField g' =
      pb ψ (∑ R ∈ K, (WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 -
        WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace R).1)) := by
    have hW : weilPairingDivisor W₁ (psiFunctionField_ne_zero W₁.toAffine hc) T =
        pb ψ (WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace T).1 -
          WeilDivisor.ofPoint (Place.infinity W₁.toAffine)) := by
      rw [weilPairingDivisor_def, map_sub]; rfl
    rw [Divisor.principal_mul, principal_pow, hg₁, ← hpbP, hH, hW, ← map_nsmul, ← map_add,
      ← card_kerFinset φ, Finset.card_eq_sum_ones, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine congrArg (pb ψ) (Finset.sum_congr rfl fun R _ => ?_)
    rw [one_smul]
    abel
  -- Kummer characters of `[N]` on `W₁`
  have hg₁N : (g₁ : W₁.toAffine.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange := by
    have := zpow_mem_fieldRange_mulByIntIsogeny W₁ (psiFunctionField_ne_zero W₁.toAffine hc) hT₁ hg₁
    rwa [zpow_natCast] at this
  have hGN : (G : W₁.toAffine.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange := by
    have h2 := zpow_mem_fieldRange_mulByIntIsogeny W₂ (psiFunctionField_ne_zero W₂.toAffine hc)
      hT₂ hg₂
    rw [zpow_natCast] at h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨φ.fieldPullback k, ?_⟩
    change ψ.fieldPullback (φ.fieldPullback k) = (φ.fieldPullback (g₂ : _)) ^ N
    rw [fieldPullback_mulByInt_comm φ (psiFunctionField_ne_zero W₁.toAffine hc)
      (psiFunctionField_ne_zero W₂.toAffine hc) k, ← map_pow]
    exact congrArg φ.fieldPullback hk
  have hHm : ((Units.map (ψ.fieldPullback : W₁.toAffine.FunctionField →* W₁.toAffine.FunctionField)
      H : W₁.toAffine.FunctionFieldˣ) : W₁.toAffine.FunctionField) ∈ ψ.fieldPullback.fieldRange :=
    ⟨H, rfl⟩
  have hg₁d : ((g₁ ^ φ.degree : W₁.toAffine.FunctionFieldˣ) : W₁.toAffine.FunctionField) ^ N ∈
      ψ.fieldPullback.fieldRange := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]; exact pow_mem hg₁N _
  have hg'N : (g' : W₁.toAffine.FunctionField) ^ N ∈ ψ.fieldPullback.fieldRange := by
    rw [Units.val_mul, mul_pow]; exact mul_mem hg₁d (pow_mem hHm N)
  have hκ : ψ.kummerCharacter N G hGN = ψ.kummerCharacter N g₁ hg₁N ^ φ.degree := by
    rw [kummerCharacter_eq_of_principal_eq hGN (hdivG.trans hdivg'.symm),
      kummerCharacter_congr N ψ rfl _ hg'N, kummerCharacter_mul hg₁d (pow_mem hHm N),
      kummerCharacter_eq_one_of_mem_fieldRange hHm, mul_one, kummerCharacter_pow N ψ hg₁N]
  -- evaluation at `S`
  have hS : (N : ℤ) • (S : W₁.toAffine.Point) = 0 := (Submodule.mem_torsionBy_iff _ _).mp S.2
  let S' : Multiplicative ψ.ker := Multiplicative.ofAdd ⟨Point.equivBaseChangeSelf W₁.toAffine S,
    (mem_ker_mulByIntIsogeny_iff _ _).mpr (by rw [← map_zsmul, hS, map_zero])⟩
  have key1 : algebraMap F W₁.toAffine.FunctionField (ψ.kummerCharacter N G hGN S' : Fˣ) =
      translation W₁.toAffine (Point.equivBaseChangeSelf W₁.toAffine S)
        (G : W₁.toAffine.FunctionField) / G := algebraMap_kummerCharacter hGN S'
  have key2 : algebraMap F W₁.toAffine.FunctionField (ψ.kummerCharacter N g₁ hg₁N S' : Fˣ) =
      algebraMap F W₁.toAffine.FunctionField ((weilPairing W₁ N hN S T).toMul : Fˣ) :=
    (algebraMap_kummerCharacter hg₁N S').trans (algebraMap_weilPairing W₁ N hN hg₁).symm
  have key3 : translation W₁.toAffine (Point.equivBaseChangeSelf W₁.toAffine S)
      (G : W₁.toAffine.FunctionField) / G = algebraMap F W₁.toAffine.FunctionField
        ((weilPairing W₂ N hN (torsionMap φ N S) (torsionMap φ N T)).toMul : Fˣ) := by
    have ht : φ.fieldPullback (translation W₂.toAffine (Point.equivBaseChangeSelf W₂.toAffine
        ((Hom.ofIsogeny φ).pointMap S)) (g₂ : W₂.toAffine.FunctionField)) =
        translation W₁.toAffine (Point.equivBaseChangeSelf W₁.toAffine S)
          (φ.fieldPullback (g₂ : W₂.toAffine.FunctionField)) :=
      congrArg (fun χ => χ (g₂ : W₂.toAffine.FunctionField))
        (fieldPullback_comp_translation φ (S : W₁.toAffine.Point))
    change translation W₁.toAffine (Point.equivBaseChangeSelf W₁.toAffine S)
      (φ.fieldPullback g₂) / φ.fieldPullback g₂ = _
    have hw2 : algebraMap F W₂.toAffine.FunctionField
        ((weilPairing W₂ N hN (torsionMap φ N S) (torsionMap φ N T)).toMul : Fˣ) =
        translation W₂.toAffine (Point.equivBaseChangeSelf W₂.toAffine
          ((Hom.ofIsogeny φ).pointMap S)) (g₂ : W₂.toAffine.FunctionField) / g₂ :=
      algebraMap_weilPairing W₂ N hN (S := torsionMap φ N S) hg₂
    rw [← ht, ← map_div₀, ← hw2, AlgHom.commutes]
  have hfin : algebraMap F W₁.toAffine.FunctionField
      ((weilPairing W₂ N hN (torsionMap φ N S) (torsionMap φ N T)).toMul : Fˣ) =
      algebraMap F W₁.toAffine.FunctionField
        ((((weilPairing W₁ N hN S T).toMul : Fˣ) : F) ^ φ.degree) := by
    rw [← key3, ← key1, hκ, MonoidHom.pow_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val,
      map_pow, key2, ← map_pow]
  have hinj := (algebraMap F W₁.toAffine.FunctionField).injective hfin
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  ext
  simpa using hinj

/-- **Node `WeilPairingIsogeny`** (a consequence of Silverman III.8.2, for separable isogenies; the
first step of the route from the Weil pairing to Hasse's bound, not a manuscript line): for a
separable isogeny `φ : E₁ → E₂` over a separably closed field and `N` invertible there,
`e_N(φ S, φ T) = e_N(S, T)^{deg φ}` on `E₁[N]`. PROVED (`weilPairingIsogeny_proof`). -/
def WeilPairingIsogeny : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [IsSepClosed F] (W₁ W₂ : WeierstrassCurve F)
    [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (N : ℕ) [NeZero N] (hN : (N : F) ≠ 0) (S T : Submodule.torsionBy ℤ W₁.toAffine.Point (N : ℤ)),
    weilPairing W₂ N hN (torsionMap φ N S) (torsionMap φ N T) = φ.degree • weilPairing W₁ N hN S T

theorem weilPairingIsogeny_proof : WeilPairingIsogeny :=
  fun _ _ _ _ _ _ _ _ φ _ N _ hN S T => weilPairing_torsionMap φ N hN S T

end ZInQ.Contrib.CloudB3RC53.WeilIsogeny
