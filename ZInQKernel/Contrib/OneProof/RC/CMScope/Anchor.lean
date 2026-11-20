import ZInQKernel.Contrib.OneProof.RC.CMScope.Orientation
import ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.AtScale

/-! The fixed-scale anchor at tex 2839–2844 and 2915–2917.
The input chase and base change are on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField WeierstrassCurve
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
  ZInQ.Contrib.CloudB3E2.NormCochain
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
  ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Wiring

namespace ZInQ.Manuscript.RC.CMScope

open HeegnerAnchor (conductorForm conductorOrder_discr)

/-- An embedding of an algebraic field into `ℂ` factors through the given
embedding of `ℚ̄`: every minimal polynomial splits in the latter's image. -/
theorem factor_embedding {H : Type} [Field H] [Algebra ℚ H] [Algebra.IsAlgebraic ℚ H]
    (ι : Qbar →ₐ[ℚ] ℂ) (j : H →ₐ[ℚ] ℂ) :
    ∃ e : H →ₐ[ℚ] Qbar, ι.comp e = j := by
  have hs (a : H) : ((minpoly ℚ a).map (algebraMap ℚ ι.fieldRange)).Splits :=
    Polynomial.Splits.of_algHom (IsAlgClosed.splits _) ι.rangeRestrict
  let F := IntermediateField.algHomEquivAlgHomOfSplits ℂ ι.fieldRange hs
  let b := F.symm j
  refine ⟨ι.equivFieldRange.symm.toAlgHom.comp b, ?_⟩
  apply AlgHom.ext
  intro a
  change ((ι.equivFieldRange (ι.equivFieldRange.symm (b a)) : ι.fieldRange) : ℂ) = j a
  rw [AlgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (F.apply_symm_apply j) a

theorem fieldPoint_map_map {X : Scheme.{0}} {p : X ⟶ Spec (.of ℚ)}
    {F G L : Type} [Field F] [Field G] [Field L] [Algebra ℚ F] [Algebra ℚ G] [Algebra ℚ L]
    (e : F →ₐ[ℚ] G) (j : G →ₐ[ℚ] L) (x : FieldPoint p F) :
    (x.map e).map j = x.map (j.comp e) := by
  apply Subtype.ext
  simp only [FieldPoint.map, ← Category.assoc, ← Spec.map_comp]
  rfl

open Classical in
/-- Transport the single descended point through the specified algebraic
closure and evaluate the fixed map (the pointwise step of the old proof). -/
theorem anchorValue {E : WeierstrassCurve ℚ} [E.IsElliptic] [NeZero (newformLevel E)]
    {X : X0Model (newformLevel E)} (p : CSTParam E)
    (π : X.X ⟶ Proj E.toProjective.grading) (hπQ : π ≫ projectiveOverQ E = X.overQ)
    (hπ : ∀ τ : UpperHalfPlane,
      projectiveValue ((X.complexPoint τ).comp π hπQ).val = phiAn E p.f p.Lat p.κ τ)
    (ι : Qbar →ₐ[ℚ] ℂ) {L : Type} [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (j : L →ₐ[ℚ] ℂ) (x : FieldPoint X.overQ L)
    {τ : UpperHalfPlane} (hx : x.map j = X.complexPoint τ) :
    ∃ (e : L →ₐ[ℚ] Qbar) (x : FieldPoint X.overQ e.fieldRange),
      x.map (ι.comp e.fieldRange.val) = X.complexPoint τ ∧
      Affine.Point.map (W' := E) ι
        (Affine.Point.map (W' := E) e.fieldRange.val (projectiveValue (x.comp π hπQ).val)) =
          phiAn E p.f p.Lat p.κ τ := by
  obtain ⟨e, he⟩ := factor_embedding ι j
  let j' := ι.comp e.fieldRange.val
  let e' := e.equivFieldRange.toAlgHom
  let x' := x.map e'
  have hx' : x'.map j' = X.complexPoint (τ) := by
    change (x.map e').map j' = _
    rw [fieldPoint_map_map]
    have he' : j'.comp e' = j := he
    rwa [he']
  refine ⟨e, x', hx', ?_⟩
  rw [Affine.Point.map_map]
  calc
    _ = projectiveValue (Spec.map (CommRingCat.ofHom j'.toRingHom) ≫ (x'.comp π hπQ).val) :=
      projectiveValue_map j' _
    _ = projectiveValue ((x'.map j').comp π hπQ).val := by
      simp only [FieldPoint.comp, FieldPoint.map, Category.assoc]
    _ = _ := by rw [hx']; exact hπ _

/-- Splitting at two rules out both exceptional discriminants. At level
two the discriminant is odd and is a square modulo eight (c). -/
theorem discr_ne_of_split_two {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hs : SplitsIn K 2) :
    discr K ≠ -4 ∧ discr K ≠ -3 := by
  have hs' (q : ℕ) (hq : q.Prime) (hd : q ∣ 2 * 2) : SplitsIn K q := by
    have hq2 : q ∣ 2 := (hq.dvd_mul.mp hd).elim id id
    rwa [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2]
  obtain ⟨hcop, B, C, hf⟩ := HeegnerAnchor.conductorForm (d := 1) hK (N := 2)
    (by decide) hs' (by simp)
  have hcop' : IsCoprime (discr K) (2 : ℤ) := by simpa using hcop
  have he : B ^ 2 - 8 * C = discr K := by simpa using hf.2.2.1
  have hmod : Int.ModEq 8 (B ^ 2) (discr K) :=
    Int.modEq_of_dvd ⟨-C, by linarith⟩
  have hsmall : B % 8 < 8 := Int.emod_lt_of_pos B (by decide)
  have hnonneg : 0 ≤ B % 8 := Int.emod_nonneg B (by decide)
  have hsq : (B % 8) ^ 2 % 8 = discr K % 8 :=
    (((Int.mod_modEq B 8).pow 2).trans hmod).eq
  constructor
  · intro h
    rw [h] at hcop'
    exact (by decide : Int.gcd (-4) 2 ≠ 1) (Int.isCoprime_iff_gcd_eq_one.mp hcop')
  · intro h
    rw [h] at hsq
    interval_cases hB : B % 8 <;> norm_num [hB] at hsq

/-- Scale a specified conductor-one form, keeping its orientation as
the conductor varies (c). -/
theorem scale_form {N c : ℕ} {D B C : ℤ}
    (hNc : N.Coprime c) (hf : IsHeegnerForm N D N B C) :
    IsHeegnerForm N (D * (c : ℤ) ^ 2) N ((c : ℤ) * B) ((c : ℤ) ^ 2 * C) := by
  obtain ⟨hA, hdiv, hdisc, hprim⟩ := hf
  refine ⟨hA, hdiv, ?_, ?_⟩
  · rw [← hdisc]
    ring
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hg : (p : ℤ) ∣ (Int.gcd (Int.gcd (N : ℤ) ((c : ℤ) * B)) ((c : ℤ) ^ 2 * C) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpg
  have hgab := hg.trans (Int.gcd_dvd_left _ _)
  have hpN : (p : ℤ) ∣ (N : ℤ) := hgab.trans (Int.gcd_dvd_left _ _)
  have hpc : ¬ (p : ℤ) ∣ (c : ℤ) := by
    intro h
    have h1 := Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hpN) (Int.natCast_dvd_natCast.mp h)
    rw [hNc.gcd_eq_one] at h1
    exact hp.not_dvd_one h1
  have hpp := Nat.prime_iff_prime_int.mp hp
  have hpB : (p : ℤ) ∣ B :=
    (hpp.dvd_mul.mp (hgab.trans (Int.gcd_dvd_right _ _))).resolve_left hpc
  have hpC : (p : ℤ) ∣ C := by
    rcases hpp.dvd_mul.mp (hg.trans (Int.gcd_dvd_right _ _)) with h | h
    · exact (hpc (hpp.dvd_of_dvd_pow h)).elim
    · exact h
  have h1 := Int.dvd_gcd (Int.natCast_dvd_natCast.mpr (Int.dvd_gcd hpN hpB)) hpC
  rw [hprim] at h1
  exact hp.not_dvd_one h1

open Classical in
/-- The source chart and elliptic image for one order of discriminant `Δ`.
Keeping the chart abstract here avoids unfolding its construction when
elaborating the comparison on the actual modular curve. -/
private def ConductorComparison {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] {K : Type} [Field K] [NumberField K]
    (p : CSTParam E) (ι : Qbar →ₐ[ℚ] ℂ) (X : X0Model (newformLevel E))
    (π : X.X ⟶ Proj E.toProjective.grading) (hπQ : π ≫ projectiveOverQ E = X.overQ)
    (O : NumberFieldOrder K) (Δ : ℤ) : Prop :=
  ∃ (B C : ℤ) (e : ringClassField O →ₐ[ℚ] Qbar) (x : FieldPoint X.overQ e.fieldRange),
    IsHeegnerForm (newformLevel E) Δ (newformLevel E : ℤ) B C ∧
    x.map (ι.comp e.fieldRange.val) = X.complexPoint (cmPoint (newformLevel E : ℤ) B Δ) ∧
    Affine.Point.map (W' := E) ι
      (Affine.Point.map (W' := E) e.fieldRange.val (projectiveValue (x.comp π hπQ).val)) =
        phiAn E p.f p.Lat p.κ (cmPoint (newformLevel E : ℤ) B Δ)

set_option maxHeartbeats 800000 in
open Classical in
/-- One rational morphism works for every admissible conductor on the
constructed modular curve. The original conductor domain lies in the
manuscript's domain (tex 2841–2844) when the level is even. The level
is the curve conductor in tex 1780–1782. -/
theorem cmPointsAtScale {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] [NeZero (newformLevel (Ecurve ℓ))]
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (p : CSTParam (Ecurve ℓ)) (ι : Qbar →ₐ[ℚ] ℂ)
    (hK : Module.finrank ℚ K = 2)
    (hsplit : ∀ q : ℕ, q.Prime → q ∣ 2 * newformLevel (Ecurve ℓ) → SplitsIn K q)
    (h2N : 2 ∣ newformLevel (Ecurve ℓ))
    (hr : ∃ c : ℚ, (c : ℂ) = p.κ)
    (hCM : CMFieldOfDefinitionScoped (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    let X := X0Branch.model (newformLevel (Ecurve ℓ))
    ∃ (π : X.X ⟶ Proj (Ecurve ℓ).toProjective.grading)
      (hπQ : π ≫ projectiveOverQ (Ecurve ℓ) = X.overQ),
      IsDominant π ∧ ∀ (d : ℕ) (hd : 0 < d),
        Nat.Coprime d (newformLevel (Ecurve ℓ) * (discr K).natAbs) →
        ConductorComparison p ι X π hπQ
          (@conductorOrder K _ _ d ⟨hd.ne'⟩) (discr K * (d : ℤ) ^ 2) := by
  obtain ⟨h4, h3⟩ := discr_ne_of_split_two hK (hsplit 2 Nat.prime_two (dvd_mul_right 2 _))
  obtain ⟨π, hπQ, hdom, hπ⟩ :=
    ParamJoin.algebraicParametrizationAtScale (ℓ := ℓ) p.f p.hf p.hLat p.hκ hr
  obtain ⟨-, β, C₁, hf₁⟩ := conductorForm (N := newformLevel (Ecurve ℓ)) (d := 1)
    hK (NeZero.pos _) hsplit (by simp)
  have hf₀ : IsHeegnerForm (newformLevel (Ecurve ℓ)) (discr K)
      (newformLevel (Ecurve ℓ) : ℤ) β C₁ := by simpa using hf₁
  have hβ : Int.ModEq (4 * (newformLevel (Ecurve ℓ) : ℤ)) (β ^ 2) (discr K) :=
    Int.modEq_of_dvd ⟨-C₁, by rw [← hf₀.2.2.1]; ring⟩
  refine ⟨π, hπQ, hdom, fun d hd hcop => ?_⟩
  let _ : NeZero d := ⟨hd.ne'⟩
  obtain ⟨hcop', -⟩ :=
    conductorForm (N := newformLevel (Ecurve ℓ)) hK (NeZero.pos _) hsplit hcop
  have hΔ : discr K * (d : ℤ) ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (discr_neg_of_totallyComplex hK) (pow_pos (by exact_mod_cast hd) 2)
  have hcop2 : Nat.Coprime d (2 * newformLevel (Ecurve ℓ) * (discr K).natAbs) := by
    rw [mul_assoc]
    exact (hcop.coprime_dvd_right (dvd_mul_of_dvd_left h2N _)).mul_right hcop
  have hdN := hcop.coprime_dvd_right (dvd_mul_right (newformLevel (Ecurve ℓ)) (discr K).natAbs)
  have hform := scale_form hdN.symm hf₀
  obtain ⟨j, z, hz⟩ := hCM K hK inferInstance hsplit h4 h3 β hβ d hcop2 _ _ _ _
    (conductorOrder_discr hK d) hΔ hcop' hform Int.ModEq.rfl
  obtain ⟨e, x, hx, hy⟩ := anchorValue p π hπQ hπ ι j z hz
  exact ⟨_, _, e, x, hform, hx, hy⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- The CM evaluation supplies the fields and points of the anchor.
The caller can fill the two Galois slots of `HeegnerPointData` without
changing this assertion about the points. -/
theorem genuineHeegnerAnchor {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] [NeZero (newformLevel (Ecurve ℓ))]
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (p : CSTParam (Ecurve ℓ)) (ι : Qbar →ₐ[ℚ] ℂ)
    (hK : Module.finrank ℚ K = 2)
    (hsplit : ∀ q : ℕ, q.Prime → q ∣ 2 * newformLevel (Ecurve ℓ) → SplitsIn K q)
    (h2N : 2 ∣ newformLevel (Ecurve ℓ))
    (hr : ∃ c : ℚ, (c : ℂ) = p.κ)
    (hCM : CMFieldOfDefinitionScoped (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    ∃ (H : ℕ → IntermediateField ℚ Qbar) (y : ℕ → ((Ecurve ℓ).baseChange Qbar).toAffine.Point),
      ∀ (relGal : ℕ → ℕ → Finset GalQ) (frob : ℕ → ℕ → GalQ),
        GenuineHeegnerAnchor (Ecurve ℓ) K p ι
          ⟨discr K, newformLevel (Ecurve ℓ), H, y, relGal, frob⟩ := by
  obtain ⟨π, hπQ, -, hpts⟩ := cmPointsAtScale p ι hK hsplit h2N hr hCM
  have hy (d : ℕ) (hd : 0 < d)
      (hcop : Nat.Coprime d (newformLevel (Ecurve ℓ) * (discr K).natAbs)) :
      ∃ (Hd : IntermediateField ℚ Qbar) (Y : ((Ecurve ℓ).baseChange Hd).toAffine.Point),
        ∃ A B C : ℤ, IsHeegnerForm (newformLevel (Ecurve ℓ)) (discr K * (d : ℤ) ^ 2) A B C ∧
          Affine.Point.map (W' := Ecurve ℓ) ι (Affine.Point.map (W' := Ecurve ℓ) Hd.val Y) =
            phiAn (Ecurve ℓ) p.f p.Lat p.κ (cmPoint A B (discr K * (d : ℤ) ^ 2)) := by
    have h := hpts d hd hcop
    unfold ConductorComparison at h
    obtain ⟨B, C, e, x, hform, -, hvalue⟩ := h
    exact ⟨e.fieldRange, projectiveValue (x.comp π hπQ).val, _, B, C, hform, hvalue⟩
  let H (d : ℕ) : IntermediateField ℚ Qbar :=
    if h : 0 < d ∧ Nat.Coprime d (newformLevel (Ecurve ℓ) * (discr K).natAbs)
      then (hy d h.1 h.2).choose else ⊥
  let y (d : ℕ) : ((Ecurve ℓ).baseChange Qbar).toAffine.Point :=
    if h : 0 < d ∧ Nat.Coprime d (newformLevel (Ecurve ℓ) * (discr K).natAbs)
      then Affine.Point.map (W' := Ecurve ℓ) (hy d h.1 h.2).choose.val
        (hy d h.1 h.2).choose_spec.choose else 0
  refine ⟨H, y, ?_⟩
  intro relGal frob
  refine ⟨rfl, rfl, fun d hd hcop => ?_⟩
  dsimp only
  have hH : H d = (hy d hd hcop).choose := dite_eq_left (And.intro hd hcop)
  have hy' : y d = Affine.Point.map (W' := Ecurve ℓ) (hy d hd hcop).choose.val
      (hy d hd hcop).choose_spec.choose := dite_eq_left (And.intro hd hcop)
  constructor
  · let HasPoint (F : IntermediateField ℚ Qbar) : Prop :=
      ∃ Y' : ((Ecurve ℓ).baseChange F).toAffine.Point,
        Affine.Point.map (W' := Ecurve ℓ) F.val Y' = y d
    change HasPoint (H d)
    exact (congrArg HasPoint hH).mpr ⟨(hy d hd hcop).choose_spec.choose, hy'.symm⟩
  · rw [hy']
    exact (hy d hd hcop).choose_spec.choose_spec

end ZInQ.Manuscript.RC.CMScope
