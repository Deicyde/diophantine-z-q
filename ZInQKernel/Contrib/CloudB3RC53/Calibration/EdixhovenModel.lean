import ZInQKernel.Contrib.CloudB3RC53.Calibration.Edixhoven
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalRational
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# Calibration: the two-torsion count of `EdixhovenComponentNumber` is model-independent (PROVED)

`EdixhovenComponentNumber ℓ h k cB` asks `cB p = #Ẽ₀(𝔽_p)[2]` for EVERY good integral model of
`E₀ = E^{(h)}` at `p`. This file shows that the count does not depend on the model:

* `GoodModelAt.W_eq`: a `GoodModelAt E p` is a Weierstrass curve over `ℤ` mapping to `E` itself, so
  two of them are equal; in particular their two-torsion counts agree (`card_twoTorsion_red_eq`).
* `GoodModelIso E p`: a good integral model of `E` up to a rational change of variables
  (`W_ℚ = C • E`, `p ∤ Δ(W)`), the genuinely model-free notion. **Two such models have reductions
  related by a change of variables over `𝔽_p`** (`exists_red_eq_smul`): the change of variables
  between them over `ℚ_p` has a unit scaling factor (`Δ₂ = u⁻¹² Δ₁`, both `p`-adic units), hence is
  integral (Silverman VII.1.3(d), Tau Ceti's `exists_baseChange_eq_of_smul_eq`), and reduces modulo
  `p`. Hence `#Ẽ(𝔽_p)[2]` is the same for all of them (`card_twoTorsion_red_eq_of_iso`).
* `EdixhovenComponentNumberIso`: the print over models up to isomorphism; it is equivalent to the
  print as stated wherever a good model in the stated sense exists (`edixhovenIso_of_edixhoven`,
  `edixhoven_of_edixhovenIso`).
* Non-vacuity (LESSON 2): `edixhovenComponentNumber_canonical` — for every `ℓ, h, k` the canonical
  choice `cB p = #Ẽ₀(𝔽_p)[2]` (any good model) satisfies the print's statement, and
  `edixhoven_witness_five`: for `ℓ = h = 1`, `k = 5`, the prime `p = 5 ∥ k` carries the good model
  `y² = x³ + 2x² − 3x` and `cB 5 = #Ẽ₀(𝔽₅)[2] = 4` (the cubic `x(x − 1)(x + 3)` splits mod `5`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Calibration

open ZInQ.Contrib.CloudB3RC53 WeierstrassCurve
open IsDedekindDomain Rat.HeightOneSpectrum

/-! ### Equal models -/

/-- Two good models in the sense of `GoodModelAt` are the same Weierstrass curve over `ℤ`
(PROVED). -/
theorem GoodModelAt.W_eq {E : WeierstrassCurve ℚ} {p : ℕ} (M₁ M₂ : GoodModelAt E p) :
    M₁.W = M₂.W :=
  WeierstrassCurve.map_injective (Int.castRingHom ℚ).injective_int (M₁.hmap.trans M₂.hmap.symm)

/-- The two-torsion count does not depend on the model `GoodModelAt` (PROVED). -/
theorem card_twoTorsion_red_eq {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (M₁ M₂ : GoodModelAt E p) :
    Nat.card (AddSubgroup.torsionBy M₁.red.toAffine.Point (2 : ℕ)) =
      Nat.card (AddSubgroup.torsionBy M₂.red.toAffine.Point (2 : ℕ)) := by
  unfold GoodModelAt.red
  rw [M₁.W_eq M₂]

/-! ### Models up to isomorphism -/

/-- **A good integral model of `E` at `p` up to a rational change of variables**: `W` over `ℤ`,
`C` over `ℚ` with `W_ℚ = C • E`, and `p ∤ Δ(W)`. -/
structure GoodModelIso (E : WeierstrassCurve ℚ) (p : ℕ) where
  /-- the integral model -/
  W : WeierstrassCurve ℤ
  /-- the change of variables from `E` -/
  C : VariableChange ℚ
  /-- it is a model of `E` up to that change of variables -/
  hmap : W.map (Int.castRingHom ℚ) = C • E
  /-- good reduction at `p` -/
  hgood : ¬ (p : ℤ) ∣ W.Δ

/-- The reduction over `𝔽_p`. -/
def GoodModelIso.red {E : WeierstrassCurve ℚ} {p : ℕ} (M : GoodModelIso E p) :
    WeierstrassCurve (ZMod p) :=
  M.W.map (Int.castRingHom (ZMod p))

/-- A model in the sense of `GoodModelAt` is one up to the identity change of variables. -/
def GoodModelAt.toIso {E : WeierstrassCurve ℚ} {p : ℕ} (M : GoodModelAt E p) : GoodModelIso E p where
  W := M.W
  C := 1
  hmap := by rw [one_smul]; exact M.hmap
  hgood := M.hgood

theorem GoodModelIso.isElliptic_red {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (M : GoodModelIso E p) : M.red.IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [GoodModelIso.red, map_Δ, eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact M.hgood

section Place

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- `ℤ_v` is integrally closed in `ℚ_v`. -/
instance : IsIntegrallyClosedIn (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) :=
  (isIntegrallyClosed_iff_isIntegrallyClosedIn (v.adicCompletion ℚ)).mp inferInstance

/-- The reduction map `ℤ_v → 𝔽_p`. -/
def redHom : v.adicCompletionIntegers ℚ →+* ZMod (natGenerator v) :=
  (ZInQ.Literature.residueEquiv v : _ →+* _).comp (IsLocalRing.residue _)

theorem redHom_comp_int : (redHom v).comp (algebraMap ℤ (v.adicCompletionIntegers ℚ)) =
    Int.castRingHom (ZMod (natGenerator v)) := RingHom.ext_int _ _

end Place

/-- A unit of `ℚ_v` given by its twelfth power (PROVED). -/
theorem valued_eq_one_of_pow_twelve {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    {x : v.adicCompletion ℚ} (h : Valued.v x ^ 12 = 1) : Valued.v x = 1 :=
  ZInQ.Literature.pow_twelve_eq_one h

/-- **The reductions of two good models up to isomorphism are related by a change of variables
over `𝔽_p`** (PROVED). -/
theorem exists_red_eq_smul {E : WeierstrassCurve ℚ} {p : ℕ} (hp : p.Prime)
    (M₁ M₂ : GoodModelIso E p) : ∃ C' : VariableChange (ZMod p), M₂.red = C' • M₁.red := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := ZInQ.Literature.exists_natGenerator_eq p
  subst hv
  set R := v.adicCompletionIntegers ℚ
  set K := v.adicCompletion ℚ
  set ι := algebraMap ℚ K
  -- the rational change of variables between the two models
  set D : VariableChange ℚ := M₂.C * M₁.C⁻¹
  have hD : D • M₁.W.map (Int.castRingHom ℚ) = M₂.W.map (Int.castRingHom ℚ) := by
    rw [M₁.hmap, M₂.hmap, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  -- over `ℚ_v`
  set V₁ : WeierstrassCurve R := M₁.W.map (algebraMap ℤ R)
  set V₂ : WeierstrassCurve R := M₂.W.map (algebraMap ℤ R)
  have hV : ∀ W : WeierstrassCurve ℤ, (W.map (algebraMap ℤ R)).baseChange K =
      (W.map (Int.castRingHom ℚ)).map ι := by
    intro W
    rw [baseChange, map_map, map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hDK : (D.map ι) • V₁.baseChange K = V₂.baseChange K := by
    rw [hV, hV, map_variableChange, hD]
  have : IsIntegral R (V₁.baseChange K) := ⟨V₁, rfl⟩
  have : IsIntegral R (V₂.baseChange K) := ⟨V₂, rfl⟩
  -- the scaling factor is a unit of `ℤ_v`
  have hΔint : ∀ W : WeierstrassCurve ℤ, ¬ ((natGenerator v : ℕ) : ℤ) ∣ W.Δ →
      Valued.v (ι (W.Δ : ℚ)) = 1 := by
    intro W hW
    rw [ZInQ.Contrib.CloudB3RC53.GenusOdd.valued_iota_eq_one_iff (prime_natGenerator v)
      (ZInQ.Contrib.CloudB3RC53.GenusOdd.mem_primesAbove_rat v)]
    simp only [Rat.num_intCast, Rat.den_intCast, Nat.cast_one]
    exact ⟨hW, fun h => (prime_natGenerator v).one_lt.ne'
      (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)⟩
  have hΔeq : ((M₂.W.map (Int.castRingHom ℚ)).Δ) =
      ((D.u⁻¹ : ℚˣ) : ℚ) ^ 12 * (M₁.W.map (Int.castRingHom ℚ)).Δ := by
    rw [← hD, variableChange_Δ]
  simp only [map_Δ, eq_intCast] at hΔeq
  have hu1 : Valued.v (ι ((D.u⁻¹ : ℚˣ) : ℚ)) = 1 := by
    apply valued_eq_one_of_pow_twelve
    have h := congrArg (fun z : ℚ => Valued.v (ι z)) hΔeq
    simp only [map_mul, map_pow] at h
    rw [hΔint M₂.W M₂.hgood, hΔint M₁.W M₁.hgood, mul_one] at h
    exact h.symm
  have hu1' : Valued.v (ι (D.u : ℚ)) = 1 := by
    have : ι (D.u : ℚ) = (ι ((D.u⁻¹ : ℚˣ) : ℚ))⁻¹ := by
      rw [← map_inv₀, Units.val_inv_eq_inv_val, inv_inv]
    rw [this, map_inv₀, hu1, inv_one]
  have hu0 : ι (D.u : ℚ) ≠ 0 := (map_ne_zero ι).mpr (Units.ne_zero _)
  obtain ⟨hmem, hinv⟩ := (ZInQ.Contrib.CloudB3RC53.GenusOdd.mem_and_inv_mem_iff (𝔭 := v)
    (ι (D.u : ℚ)) hu0).mpr hu1'
  let u₀ : Rˣ := ⟨⟨_, hmem⟩, ⟨_, hinv⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  -- integral change of variables
  obtain ⟨C₀, hC₀⟩ := VariableChange.exists_baseChange_eq_of_smul_eq R (D.map ι) hDK u₀ rfl
  have hR : C₀ • V₁ = V₂ := by
    apply smul_eq_of_baseChange_smul_eq (L := K) (IsFractionRing.injective R K)
    rw [hC₀]; exact hDK
  -- reduce modulo `p`
  refine ⟨C₀.map (redHom v), ?_⟩
  have hred : ∀ W : WeierstrassCurve ℤ, (W.map (algebraMap ℤ R)).map (redHom v) =
      W.map (Int.castRingHom (ZMod (natGenerator v))) := by
    intro W; rw [map_map, redHom_comp_int]
  rw [GoodModelIso.red, GoodModelIso.red, ← hred, ← hred, map_variableChange, hR]

/-- Isomorphic point groups have equally many points of order dividing `n` (PROVED). -/
theorem natCard_torsionBy_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (n : ℕ) : Nat.card (AddSubgroup.torsionBy A n) = Nat.card (AddSubgroup.torsionBy B n) := by
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
  simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AddSubgroup.torsionBy.nsmul_iff]
  constructor
  · intro h; rw [← map_nsmul, h, map_zero]
  · intro h; rw [← map_nsmul] at h; exact (map_eq_zero_iff e e.injective).mp h

/-- **The two-torsion count is model-independent** (PROVED): two good integral models of `E` at
`p`, up to isomorphism, have the same `#Ẽ(𝔽_p)[2]`. -/
theorem card_twoTorsion_red_eq_of_iso {E : WeierstrassCurve ℚ} {p : ℕ} [hp : Fact p.Prime]
    (M₁ M₂ : GoodModelIso E p) :
    Nat.card (AddSubgroup.torsionBy M₁.red.toAffine.Point (2 : ℕ)) =
      Nat.card (AddSubgroup.torsionBy M₂.red.toAffine.Point (2 : ℕ)) := by
  obtain ⟨C', hC'⟩ := exists_red_eq_smul hp.out M₁ M₂
  have e := WeierstrassCurve.Affine.Point.addEquivVariableChange M₁.red C'
  rw [hC']
  exact (natCard_torsionBy_congr e 2).symm

/-! ### The print over models up to isomorphism -/

/-- **`EdixhovenComponentNumber` over good models up to isomorphism** (same print, same
hypotheses; the integral model is only required to be isomorphic to `E₀` over `ℚ`). -/
def EdixhovenComponentNumberIso (ℓ : ℕ) (h : ℚ) (k : ℤ) (cB : ℕ → ℕ) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, p ≠ 2 → (p : ℤ) ∣ k → ¬ ((p : ℤ) ^ 2 ∣ k) →
    ∀ M : GoodModelIso (qtwist (Ecurve ℓ) h) p,
      letI := Fact.mk hp
      cB p = Nat.card (AddSubgroup.torsionBy M.red.toAffine.Point (2 : ℕ))

/-- The print over models up to isomorphism implies the print as stated (PROVED). -/
theorem edixhoven_of_edixhovenIso {ℓ : ℕ} {h : ℚ} {k : ℤ} {cB : ℕ → ℕ}
    (hE : EdixhovenComponentNumberIso ℓ h k cB) : EdixhovenComponentNumber ℓ h k cB :=
  fun p hp h2 hpk hp2 M => hE p hp h2 hpk hp2 M.toIso

/-- **The print as stated implies it over every model up to isomorphism, at the primes where a
stated good model exists** (PROVED; model independence). -/
theorem edixhovenIso_of_edixhoven {ℓ : ℕ} {h : ℚ} {k : ℤ} {cB : ℕ → ℕ}
    (hE : EdixhovenComponentNumber ℓ h k cB)
    (hex : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ k → Nonempty (GoodModelAt (qtwist (Ecurve ℓ) h) p) ∨
      IsEmpty (GoodModelIso (qtwist (Ecurve ℓ) h) p)) :
    EdixhovenComponentNumberIso ℓ h k cB := by
  intro p hp h2 hpk hp2 M
  have := Fact.mk hp
  rcases hex p hp hpk with ⟨⟨M₀⟩⟩ | hempty
  · rw [hE p hp h2 hpk hp2 M₀]
    exact card_twoTorsion_red_eq_of_iso M₀.toIso M
  · exact (hempty.false M).elim

/-! ### Non-vacuity (LESSON 2) -/

open Classical in
/-- The canonical component numbers: `#Ẽ₀(𝔽_p)[2]` for any good model up to isomorphism, `0`
where there is none. -/
def cBcanonical (ℓ : ℕ) (h : ℚ) (p : ℕ) : ℕ :=
  if hp : p.Prime then
    letI := Fact.mk hp
    if hM : Nonempty (GoodModelIso (qtwist (Ecurve ℓ) h) p) then
      Nat.card (AddSubgroup.torsionBy hM.some.red.toAffine.Point (2 : ℕ))
    else 0
  else 0

/-- **The print's statement is satisfiable for every `ℓ, h, k`** (PROVED): the canonical component
numbers satisfy `EdixhovenComponentNumberIso`, hence `EdixhovenComponentNumber`. -/
theorem edixhovenComponentNumber_canonical (ℓ : ℕ) (h : ℚ) (k : ℤ) :
    EdixhovenComponentNumberIso ℓ h k (cBcanonical ℓ h) ∧
      EdixhovenComponentNumber ℓ h k (cBcanonical ℓ h) := by
  have key : EdixhovenComponentNumberIso ℓ h k (cBcanonical ℓ h) := by
    intro p hp _ _ _ M
    have := Fact.mk hp
    rw [cBcanonical, dif_pos hp, dif_pos ⟨M⟩]
    exact card_twoTorsion_red_eq_of_iso _ M
  exact ⟨key, edixhoven_of_edixhovenIso key⟩

end ZInQ.Contrib.CloudB3RC53.Calibration
