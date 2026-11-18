import ZInQKernel.Contrib.OneProof.SelmerKummer
import ZInQKernel.Contrib.OneProof.SelmerSplit
import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.EtaleTwoDescent

/-!
# `Sel₂(E/ℚ)` is the explicit `2`-Selmer group; Lemma 5.4 and `CR_M` for the curves `E_ℓ`

* `selmerGroup_emb_eq_inf`, `selmerTwoMulEquivSelmerGroup₂`, `card_selmerAt_one_eq`: for an elliptic
  curve `E/ℚ` in the form `y² = f(x)`, the cohomological `2`-Selmer group `selmerAt E 1` (conditions at
  every finite place and at `ℝ`) is isomorphic, by the cohomological descent map, to the explicit
  `2`-Selmer group of the étale algebra `ℚ[X]/(f)` (Tau Ceti main's
  `WeierstrassCurve.selmerGroupTwoMulEquivSelmerGroup₂`, Silverman X.1.4 and X.4).
* `card_selmerAt_curve_eq_ncard_selM`: for `E_ℓ`, `#Sel₂(E_ℓ/ℚ) = #SelM ℓ`, the manuscript's explicit
  system of pairs of squarefree integers (`ZInQKernel/Contrib/OneProof/SelmerSplit.lean`).
* `lemma54At_selmerCorankOne`: Lemma 5.4 at the curves `E_ℓ` with the genuine corank condition, from
  the Cassels–Tate square property.
* `locM_of_restrictedConverse`: the manuscript's lines 1107–1110 in the descent lane's form: Theorem 5.3
  over the genuine Selmer condition, with Lemma 5.4, Mordell–Weil and the printed inputs Cassels–Tate
  and Kolyvagin, makes every class of `SelM ℓ` the Kummer class of a rational point.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology IsDedekindDomain

variable (E : WeierstrassCurve ℚ)

/-- **The Selmer conditions at the finite places**: `E.selmerGroup embFin m`, with the completions'
own field and `ℚ`-algebra structures (`HeightOneSpectrum.adicCompletion.instField`,
`HeightOneSpectrum.instAlgebraAdicCompletion`) — the ones of Tau Ceti's comparison of Selmer groups;
instance search would otherwise pick `DivisionRing.toRatAlgebra`, equal but not definitionally. -/
abbrev selmerFin (m : ℕ) : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff m)) :=
  @WeierstrassCurve.selmerGroup ℚ _ E (HeightOneSpectrum ℤ) (fun v => v.adicCompletion ℚ)
    (fun v => HeightOneSpectrum.adicCompletion.instField ℚ v)
    (fun v => HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ v) embFin m

/-- **The Selmer condition at the infinite place.** -/
abbrev selmerInf (m : ℕ) : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff m)) :=
  E.selmerGroup embInf m

/-- **`Sel₂(E/ℚ)` is the meet of the Selmer conditions at the finite places and at `ℝ`.** -/
theorem selmerGroup_emb_eq_inf (m : ℕ) :
    E.selmerGroup emb m = selmerFin E m ⊓ selmerInf E m := by
  ext c
  rw [AddSubgroup.mem_inf, WeierstrassCurve.mem_selmerGroup_iff,
    WeierstrassCurve.mem_selmerGroup_iff, WeierstrassCurve.mem_selmerGroup_iff,
    WeierstrassCurve.mem_shafarevichTateGroup_iff, WeierstrassCurve.mem_shafarevichTateGroup_iff,
    WeierstrassCurve.mem_shafarevichTateGroup_iff]
  exact ⟨fun h => ⟨fun a => h (Sum.inl a), fun b => h (Sum.inr b)⟩, fun h i =>
    match i with
    | .inl a => h.1 a
    | .inr b => h.2 b⟩

/-- **`Sel₂(E/ℚ)` is the explicit `2`-Selmer group** of the étale algebra `ℚ[X]/(f)` (Tau Ceti main's
`WeierstrassCurve.selmerGroupTwoMulEquivSelmerGroup₂`, Silverman X.1.4 and X.4), for a curve in
the normal form `y² = f(x)`: the cohomological descent map is an isomorphism onto the square
classes with square norm that satisfy the local `x - T` condition at every finite place and at `ℝ`. -/
noncomputable def selmerTwoMulEquivSelmerGroup₂ [E.IsElliptic] [E.toAffine.IsCharNeTwoNF] :
    (selmerFin E 2 ⊓ selmerInf E 2).toSubgroup ≃* E.toAffine.selmerGroup₂ ℤ (fun _ : Unit => ℝ) :=
  E.selmerGroupTwoMulEquivSelmerGroup₂ (by norm_num) ℤ (fun _ : Unit => ℝ) embFin embInf

/-- **`#Sel₂(E/ℚ)` is the order of the explicit `2`-Selmer group.** -/
theorem card_selmerAt_one_eq [E.IsElliptic] [E.toAffine.IsCharNeTwoNF] :
    Nat.card (selmerAt E 1) = Nat.card (E.toAffine.selmerGroup₂ ℤ (fun _ : Unit => ℝ)) := by
  rw [← Nat.card_congr (selmerTwoMulEquivSelmerGroup₂ E).toEquiv]
  have h : Nat.card (selmerAt E 1) = Nat.card (E.selmerGroup emb 2) := rfl
  rw [h, selmerGroup_emb_eq_inf E 2]
  exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun _ => Iff.rfl))

/-! ### `Sel₂(E_ℓ/ℚ)` is the manuscript's explicit Selmer system `SelM ℓ` -/

open SelmerSplit in
/-- **`#Sel₂(E_ℓ/ℚ) = #SelM ℓ`**: the cohomological `2`-Selmer group of `E_ℓ` and the explicit system
of pairs of squarefree integers satisfying the local x-form conditions over `ℝ` and every `ℚ_p`
have the same order. -/
theorem card_selmerAt_curve_eq_ncard_selM {ℓ : ℕ} [NeZero ℓ] :
    Nat.card (selmerAt (ZInQ.Manuscript.curve (ℓ : ℚ)) 1) = (SelM ℓ).ncard := by
  rw [card_selmerAt_one_eq, ncard_selM]

/-- **Lemma 5.4 (`lem:corank`) at the curves `E_ℓ`, over the genuine Selmer groups**: for positive
squarefree `ℓ ≡ 11 (mod 12)`, dimension three of the explicit `2`-Selmer system
(`#SelM ℓ = 8`) gives `corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1`, given the Cassels–Tate square property of
these curves (Mordell–Weil is proved, `mordellWeilQ`). -/
theorem lemma54At_selmerCorankOne
    (hCT : ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
      CasselsTateSquare (ZInQ.Manuscript.curve ℓ)) :
    ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → (SelmerSplit.SelM ℓ).ncard = 8 →
      SelmerCorankOne (ZInQ.Manuscript.curve ℓ) := by
  intro ℓ hℓ hsf hmod h8
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  haveI := isElliptic_curve hℓ0
  exact selmerCorankOne_of_card_selmerAt_one' _ (hCT ℓ hℓ hsf hmod) (fullTwoTorsion_curve hℓ0)
    (by rw [card_selmerAt_curve_eq_ncard_selM, h8])

open SelmerSplit in
/-- **A surjective Kummer map makes every class of `SelM ℓ` the class of a rational point**: if
`E_ℓ(ℚ)/2E_ℓ(ℚ) → Sel₂(E_ℓ/ℚ)` is onto, every `(a, b) ∈ SelM ℓ` satisfies the x-form condition over
`ℚ` itself (`LocM ℚ ℓ a b`). -/
theorem locM_of_mem_selM_of_surjective {ℓ : ℕ} [NeZero ℓ]
    (hsurj : Function.Surjective
      ((ZInQ.Manuscript.curve (ℓ : ℚ)).kummerSelmerMap emb (isUnit_two_pow 1)))
    {ab : ℤ × ℤ} (hab : ab ∈ SelM ℓ) : LocM ℚ ℓ ab.1 ab.2 := by
  classical
  have h := isCurveM_curve (ℓ : ℚ)
  have hℓ0 : (ℓ : ℚ) ≠ 0 := natCast_ne_zero'
  have h2 : IsUnit ((2 : ℕ) : ℚ) := by norm_num
  have ha : (ab.1 : ℚ) ≠ 0 := by exact_mod_cast hab.1.ne_zero
  have hb : (ab.2 : ℚ) ≠ 0 := by exact_mod_cast hab.2.1.ne_zero
  -- the explicit class of `(a, b)` and its cohomology class
  set m := selMEquiv (ℓ := ℓ) ⟨ab, hab⟩ with hm_def
  have hm : ∀ i, coord h i (m : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.M) =
      ![sq _ ha, sq _ hb, sq _ (mul_ne_zero ha hb)] i := fun i => coord_cls _ _ ha hb i
  set c := (selmerTwoMulEquivSelmerGroup₂ (ZInQ.Manuscript.curve (ℓ : ℚ))).symm m with hc_def
  have hc : TauCeti.TwoDescent.cohomologicalMap (ZInQ.Manuscript.curve (ℓ : ℚ)) h2
      (c : Multiplicative (H1 (AbsoluteGaloisGroup ℚ) ((ZInQ.Manuscript.curve (ℓ : ℚ)).TorsionCoeff 2)))
      = m :=
    WeierstrassCurve.cohomologicalMap_selmerGroupTwoMulEquivSelmerGroup₂_symm_apply _ h2 ℤ _ _ _ m
  have hcS : Multiplicative.toAdd (c : Multiplicative (H1 (AbsoluteGaloisGroup ℚ)
      ((ZInQ.Manuscript.curve (ℓ : ℚ)).TorsionCoeff 2))) ∈
      (ZInQ.Manuscript.curve (ℓ : ℚ)).selmerGroup emb 2 := by
    rw [selmerGroup_emb_eq_inf]
    exact c.2
  -- it is a Kummer class
  obtain ⟨x, hx⟩ := hsurj ⟨_, hcS⟩
  obtain ⟨P, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hk : (ZInQ.Manuscript.curve (ℓ : ℚ)).kummerMap 2 h2 P =
      Multiplicative.toAdd (c : Multiplicative (H1 (AbsoluteGaloisGroup ℚ)
        ((ZInQ.Manuscript.curve (ℓ : ℚ)).TorsionCoeff 2))) := by
    have := congrArg Subtype.val hx
    rw [WeierstrassCurve.coe_kummerSelmerMap, WeierstrassCurve.kummerClassMap_mk] at this
    exact this
  have hμ : (ZInQ.Manuscript.curve (ℓ : ℚ)).toAffine.μ₀ P = m := by
    rw [← TauCeti.TwoDescent.cohomologicalMap_kummerMap _ h2 P, hk]
    exact hc
  exact (exists_coord_μ_iff_locM h hℓ0 _ _ ha hb).mp
    ⟨P, fun i => by rw [WeierstrassCurve.Affine.μ_apply, hμ, hm]⟩

open SelmerSplit in
/-- **The manuscript's lines 1107–1110 in the descent lane's form (`CR_M`, for every class)**: for
positive squarefree `ℓ ≡ 11 (mod 12)` with `#SelM ℓ = 8`, Theorem 5.3 over the genuine Selmer
condition, Lemma 5.4, Mordell–Weil (proved) and the printed inputs Cassels–Tate and Kolyvagin make
every class `(a, b)` of the explicit Selmer system `SelM ℓ` the Kummer class of a rational point,
`LocM ℚ ℓ a b`; in particular `(β, 1) ∈ SelM ℓ` gives `LocM ℚ ℓ β 1`. -/
theorem locM_of_restrictedConverse (hRC : RestrictedConverseGenuine)
    (hK : ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
      KolyvaginRankOne (ZInQ.Manuscript.curve ℓ))
    (hCT : ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
      CasselsTateSquare (ZInQ.Manuscript.curve ℓ)) :
    ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → (SelM ℓ).ncard = 8 →
      ∀ ab ∈ SelM ℓ, LocM ℚ ℓ ab.1 ab.2 := by
  intro ℓ hℓ hsf hmod h8 ab hab
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  haveI := isElliptic_curve hℓ0
  refine locM_of_mem_selM_of_surjective ?_ hab
  exact kummerSelmerMap_surjective_of_restrictedConverse' hℓ hsf hmod hRC (hK ℓ hℓ hsf hmod)
    (hCT ℓ hℓ hsf hmod) (by rw [card_selmerAt_curve_eq_ncard_selM, h8])

end ZInQ.Manuscript.SelmerTwoPower
