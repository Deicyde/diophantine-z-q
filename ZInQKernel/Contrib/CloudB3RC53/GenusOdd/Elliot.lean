import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Points
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Twist

/-!
# GenusOdd: Elliot's index-at-most-two comparison (tex L2433–2435), PROVED

"Each rational free line has index at most two in its native rank-one lattice: conjugation fixes
the free class, and the norm makes twice the class rational." (tex L2433–2435; again at tex
L9427–9428 for (O.8).)

Formally: for `x` in the native lattice `M = E(H_c)^χ` and complex conjugation `ρ`,
`2x = (x + ε ρx) + (x − ε ρx)`; the first summand is fixed by the twisted action of the whole
`Gal(H_c/ℚ)` attached to `√d_R` ("the norm makes twice the class rational": it comes from the rational
line `E^{(d_R)}(ℚ)`), the second by the one attached to `√d_T`, so it comes from `E^{(d_T)}(ℚ)`, which
is torsion ("conjugation fixes the free class": the other eigencomponent has rank zero). Hence
`2M ⊆ ψ(E^{(d_R)}(ℚ)) + torsion` (`two_nsmul_mem_twist_add_torsion`). The Galois descent itself and
the existence of `√d_R, √d_T ∈ H_c` are the GLUE `TwistDescent`, `GenusTheory` of `Glue.lean`.

* `eigen_decomp`: the abstract group-theoretic computation (PROVED).
* `two_nsmul_mem_twist_add_torsion`: the statement for `E(H_c)` (PROVED from `TwistDescent`).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-- **The eigen-decomposition `2x = u + w`** (PROVED). `G` acts on `A`; `ε₁, ε₂` are `±1`-valued
characters agreeing on a subgroup `N` normalized by `ρ`, with `ρ² ∈ N` and `ε₁(ρ) = −ε₂(ρ)`. If
`x` is an `ε₁`-eigenvector of `N`, then `u = x + ε₁(ρ) ρx` and `w = x + ε₂(ρ) ρx` are `ε₁`- and
`ε₂`-eigenvectors of `N` and of `ρ`, and `u + w = 2x`. -/
theorem eigen_decomp {G : Type*} [Group G] {A : Type*} [AddCommGroup A] (act : G → A →+ A)
    (act_mul : ∀ g h x, act (g * h) x = act g (act h x)) (ε₁ ε₂ : G → ℤ)
    (hε₁ : ∀ g h, ε₁ (g * h) = ε₁ g * ε₁ h)
    (hsq₁ : ∀ g, ε₁ g * ε₁ g = 1) (hsq₂ : ∀ g, ε₂ g * ε₂ g = 1)
    (N : Subgroup G) (hN : ∀ g ∈ N, ε₁ g = ε₂ g) (ρ : G) (hρ : ε₁ ρ = -ε₂ ρ)
    (hnorm : ∀ g ∈ N, ρ⁻¹ * g * ρ ∈ N) (hρ2 : ρ * ρ ∈ N) (x : A)
    (hx : ∀ g ∈ N, act g x = ε₁ g • x) :
    (∀ g ∈ N, act g (x + ε₁ ρ • act ρ x) = ε₁ g • (x + ε₁ ρ • act ρ x)) ∧
    act ρ (x + ε₁ ρ • act ρ x) = ε₁ ρ • (x + ε₁ ρ • act ρ x) ∧
    (∀ g ∈ N, act g (x + ε₂ ρ • act ρ x) = ε₂ g • (x + ε₂ ρ • act ρ x)) ∧
    act ρ (x + ε₂ ρ • act ρ x) = ε₂ ρ • (x + ε₂ ρ • act ρ x) ∧
    (x + ε₁ ρ • act ρ x) + (x + ε₂ ρ • act ρ x) = (2 : ℕ) • x := by
  -- `g ρ x = ε(g) ρ x` for `g ∈ N`
  have hconj : ∀ g ∈ N, act g (act ρ x) = ε₁ g • act ρ x := by
    intro g hg
    have h1 : g = ρ * (ρ⁻¹ * g * ρ) * ρ⁻¹ := by group
    have h2 : act g (act ρ x) = act ρ (act (ρ⁻¹ * g * ρ) x) := by
      rw [← act_mul, ← act_mul]
      congr 1
      group
    rw [h2, hx _ (hnorm g hg), map_zsmul]
    congr 1
    rw [hε₁, hε₁, mul_comm (ε₁ ρ⁻¹), mul_assoc, ← hε₁, inv_mul_cancel]
    have h1' : ε₁ 1 = 1 := by
      have := hε₁ 1 1
      have h11 := hsq₁ 1
      rw [mul_one] at this
      nlinarith [this, h11]
    rw [h1', mul_one]
  have hρρ : act ρ (act ρ x) = x := by
    rw [← act_mul, hx _ hρ2, hε₁, hsq₁, one_smul]
  refine ⟨fun g hg => ?_, ?_, fun g hg => ?_, ?_, ?_⟩
  · rw [map_add, map_zsmul, hx g hg, hconj g hg, smul_add, smul_comm (ε₁ g) (ε₁ ρ)]
  · rw [map_add, map_zsmul, hρρ, smul_add, smul_smul, hsq₁, one_smul, add_comm]
  · rw [map_add, map_zsmul, hx g hg, hconj g hg, hN g hg, smul_add, smul_comm (ε₂ g) (ε₂ ρ)]
  · rw [map_add, map_zsmul, hρρ, smul_add, smul_smul, hsq₂, one_smul, add_comm]
  · rw [hρ, neg_smul, two_nsmul]; abel

/-! ### The concrete statement in `E(H_c)` -/

section Concrete

variable {H : Type*} [Field H] [Algebra ℚ H]

open Classical in
/-- The sign `ε_s(g) ∈ {±1}` of `g` on `s` (`g s = ±s`). -/
def sgnAt (s : H) (g : H ≃ₐ[ℚ] H) : ℤ := if g s = s then 1 else -1

theorem sgnAt_sq (s : H) (g : H ≃ₐ[ℚ] H) : sgnAt s g * sgnAt s g = 1 := by
  unfold sgnAt; split_ifs <;> norm_num

theorem apply_eq_or_neg {d : ℚ} {s : H} (hsd : s ^ 2 = algebraMap ℚ H d) (g : H ≃ₐ[ℚ] H) :
    g s = s ∨ g s = -s := by
  have : (g s) ^ 2 = s ^ 2 := by rw [← map_pow, hsd, AlgEquiv.commutes]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

theorem apply_eq_sgnAt {d : ℚ} {s : H} (hsd : s ^ 2 = algebraMap ℚ H d) (g : H ≃ₐ[ℚ] H) :
    g s = (sgnAt s g : H) * s := by
  unfold sgnAt
  split_ifs with h
  · simp [h]
  · rw [(apply_eq_or_neg hsd g).resolve_left h]; simp

theorem sgnAt_mul [CharZero H] {d : ℚ} {s : H} (hs : s ≠ 0) (hsd : s ^ 2 = algebraMap ℚ H d)
    (g h : H ≃ₐ[ℚ] H) : sgnAt s (g * h) = sgnAt s g * sgnAt s h := by
  have key : (g * h) s = ((sgnAt s g * sgnAt s h : ℤ) : H) * s := by
    rw [AlgEquiv.mul_apply, apply_eq_sgnAt hsd h, map_mul, map_intCast, apply_eq_sgnAt hsd g]
    push_cast; ring
  have key' := apply_eq_sgnAt hsd (g * h)
  rw [key] at key'
  have := mul_right_cancel₀ hs key'
  exact_mod_cast this.symm

end Concrete

section RingClass

variable {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]

/-- A `ℚ`-automorphism of `H_c` trivial on `K` is `K`-linear. -/
def toKEquiv [Normal ℚ K] (g : (ringClassField (conductorOrder K c)) ≃ₐ[ℚ] (ringClassField (conductorOrder K c))) (hg : g ∈ (AlgEquiv.restrictNormalHom K (K₁ := (ringClassField (conductorOrder K c)))).ker) :
    (ringClassField (conductorOrder K c)) ≃ₐ[K] (ringClassField (conductorOrder K c)) :=
  AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun k => by
    have h1 := AlgEquiv.restrictNormal_commutes g K k
    have h2 : g.restrictNormal K = 1 := hg
    rw [h2, AlgEquiv.one_apply] at h1
    exact h1.symm

theorem toKEquiv_apply [Normal ℚ K] (g : (ringClassField (conductorOrder K c)) ≃ₐ[ℚ] (ringClassField (conductorOrder K c))) (hg) (z : (ringClassField (conductorOrder K c))) : toKEquiv g hg z = g z := rfl

theorem restrictScalars_mem_ker [Normal ℚ K] (σ : (ringClassField (conductorOrder K c)) ≃ₐ[K] (ringClassField (conductorOrder K c))) :
    σ.restrictScalars ℚ ∈ (AlgEquiv.restrictNormalHom K (K₁ := (ringClassField (conductorOrder K c)))).ker := by
  rw [MonoidHom.mem_ker]
  ext k
  apply (algebraMap K (ringClassField (conductorOrder K c))).injective
  rw [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, AlgEquiv.restrictNormal_commutes]
  simp

variable (E : WeierstrassCurve ℚ) [DecidableEq (ringClassField (conductorOrder K c))]

theorem map_mul_algEquiv (g h : (ringClassField (conductorOrder K c)) ≃ₐ[ℚ] (ringClassField (conductorOrder K c))) (x : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (g * h).toAlgHom x =
      WeierstrassCurve.Affine.Point.map (W' := E.toAffine) g.toAlgHom
        (WeierstrassCurve.Affine.Point.map (W' := E.toAffine) h.toAlgHom x) := by
  rw [WeierstrassCurve.Affine.Point.map_map]
  rfl

/-- **Elliot's index-at-most-two comparison** (tex L2433–2435; PROVED from the GLUE
`TwistDescent`). Let `√d_R, √d_T ∈ H_c` be acted on by `Gal(H_c/K)` through `χ`, and complex
conjugation `ρ` fix one and negate the other. If `E^{(d_T)}(ℚ)` is torsion, then twice every point of
the native lattice `E(H_c)^χ` is, modulo torsion, the image of a point of the rational line
`E^{(d_R)}(ℚ)`. -/
theorem two_nsmul_mem_twist_add_torsion (hdesc : TwistDescent) [E.IsElliptic] (h₁ : E.a₁ = 0)
    (h₃ : E.a₃ = 0) (hK2 : Module.finrank ℚ K = 2) [IsGalois ℚ (ringClassField (conductorOrder K c))]
    {χ : Pic (conductorOrder K c) →* ℂˣ}
    {dR dT : ℚ} {sR sT : (ringClassField (conductorOrder K c))} (hsR : sR ≠ 0) (hsRd : sR ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) dR) (hsT : sT ≠ 0)
    (hsTd : sT ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) dT)
    (hσ : ∀ σ : (ringClassField (conductorOrder K c)) ≃ₐ[K] (ringClassField (conductorOrder K c)),
      σ sR = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : (ringClassField (conductorOrder K c))) * sR ∧
      σ sT = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : (ringClassField (conductorOrder K c))) * sT)
    (ρ : (ringClassField (conductorOrder K c)) ≃ₐ[ℚ] (ringClassField (conductorOrder K c))) (hρ : (ρ sR = sR ∧ ρ sT = -sT) ∨ (ρ sR = -sR ∧ ρ sT = sT))
    (htorT : ∀ P : (qtwist E dT).toAffine.Point, IsOfFinAddOrder P) :
    ∀ x ∈ eigenLattice E χ, ∃ r : (qtwist E dR).toAffine.Point,
      IsOfFinAddOrder ((2 : ℕ) • x - twistEmb E dR sR (twistVC_smul E h₁ h₃ hsR hsRd) r) := by
  intro x hx
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  set φ := AlgEquiv.restrictNormalHom (F := ℚ) K (K₁ := (ringClassField (conductorOrder K c)))
  set N := φ.ker
  set act : ((ringClassField (conductorOrder K c)) ≃ₐ[ℚ] (ringClassField (conductorOrder K c))) → (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point →+ (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point :=
    fun g => WeierstrassCurve.Affine.Point.map (W' := E.toAffine) g.toAlgHom with hact
  have hsRne : sR ≠ -sR := fun h => hsR (by
    have : (2 : (ringClassField (conductorOrder K c))) * sR = 0 := by linear_combination h
    simpa using this)
  have hsTne : sT ≠ -sT := fun h => hsT (by
    have : (2 : (ringClassField (conductorOrder K c))) * sT = 0 := by linear_combination h
    simpa using this)
  -- the two signs agree on `N` with the character `χ`
  have hsgnN : ∀ (g) (hg : g ∈ N), sgnAt sR g = chiSign χ
      ((ringClassArtinEquiv (conductorOrder K c)).symm (toKEquiv g hg)) ∧
      sgnAt sT g = chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm (toKEquiv g hg)) := by
    intro g hg
    obtain ⟨h1, h2⟩ := hσ (toKEquiv g hg)
    rw [toKEquiv_apply, apply_eq_sgnAt hsRd] at h1
    rw [toKEquiv_apply, apply_eq_sgnAt hsTd] at h2
    exact ⟨by exact_mod_cast mul_right_cancel₀ hsR h1, by exact_mod_cast mul_right_cancel₀ hsT h2⟩
  have hNeq : ∀ g ∈ N, sgnAt sR g = sgnAt sT g := fun g hg => by
    rw [(hsgnN g hg).1, (hsgnN g hg).2]
  have hρsgn : sgnAt sR ρ = -sgnAt sT ρ := by
    unfold sgnAt
    rcases hρ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, if_neg (by rw [h2]; exact hsTne.symm)]; (try norm_num)
    · rw [if_neg (by rw [h1]; exact hsRne.symm), if_pos h2]
  have hnorm : ∀ g ∈ N, ρ⁻¹ * g * ρ ∈ N := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [map_mul, map_mul, hg, mul_one, map_inv, inv_mul_cancel]
  have hρ2 : ρ * ρ ∈ N := by
    rw [MonoidHom.mem_ker, map_mul]
    have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK2]
    have := pow_card_eq_one' (G := K ≃ₐ[ℚ] K) (x := φ ρ)
    rw [hcard, pow_two] at this
    exact this
  have hxN : ∀ g ∈ N, act g x = sgnAt sR g • x := by
    intro g hg
    have hfg : (toKEquiv g hg).toAlgHom.restrictScalars ℚ = g.toAlgHom := AlgHom.ext fun z => rfl
    have := hx (toKEquiv g hg)
    rw [galPt, hfg, ← (hsgnN g hg).1] at this
    exact this
  obtain ⟨huN, huρ, hwN, hwρ, hsum⟩ := eigen_decomp act (map_mul_algEquiv E) (sgnAt sR) (sgnAt sT)
    (sgnAt_mul hsR hsRd) (sgnAt_sq sR) (sgnAt_sq sT) N hNeq ρ hρsgn hnorm hρ2 x hxN
  -- `ρ` is not `K`-linear
  have hnotK : ¬ ∃ σ : (ringClassField (conductorOrder K c)) ≃ₐ[K] (ringClassField (conductorOrder K c)), ∀ z, σ z = ρ z := by
    rintro ⟨σ, hσρ⟩
    obtain ⟨h1, h2⟩ := hσ σ
    rw [hσρ] at h1 h2
    rcases hρ with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h3] at h1; rw [h4] at h2
      have e1 : ((chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) : (ringClassField (conductorOrder K c))) = 1 :=
        (mul_right_cancel₀ hsR (h1.symm.trans (one_mul sR).symm))
      rw [e1, one_mul] at h2
      exact hsTne h2.symm
    · rw [h3] at h1; rw [h4] at h2
      have e2 : ((chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) : (ringClassField (conductorOrder K c))) = 1 :=
        (mul_right_cancel₀ hsT (h2.symm.trans (one_mul sT).symm))
      rw [e2, one_mul] at h1
      exact hsRne h1.symm
  -- descent of `u` and `w`
  have hdescent : ∀ (d : ℚ) (s : (ringClassField (conductorOrder K c))) (hs : s ≠ 0) (hsd : s ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) d)
      (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point),
      (∀ g ∈ N, act g y = sgnAt s g • y) → act ρ y = sgnAt s ρ • y →
      ∃ P : (qtwist E d).toAffine.Point, twistEmb E d s (twistVC_smul E h₁ h₃ hs hsd) P = y := by
    intro d s hs hsd y hyN hyρ
    refine hdesc E h₁ h₃ K hK2 (ringClassField (conductorOrder K c)) d s hs hsd ρ hnotK y (fun σ => ?_) ?_
    · have := hyN _ (restrictScalars_mem_ker σ)
      have hfg : (σ.restrictScalars ℚ).toAlgHom = σ.toAlgHom.restrictScalars ℚ :=
        AlgHom.ext fun z => rfl
      simp only [hact, hfg] at this
      rw [this]
      unfold sgnAt
      by_cases h : σ s = s
      · rw [if_pos (by exact h), if_pos h, one_smul]
      · rw [if_neg (by exact h), if_neg h, neg_smul, one_smul]
    · simp only [hact] at hyρ
      rw [hyρ]
      unfold sgnAt
      split_ifs <;> simp
  obtain ⟨P, hP⟩ := hdescent dR sR hsR hsRd _ huN huρ
  obtain ⟨Q, hQ⟩ := hdescent dT sT hsT hsTd _ hwN hwρ
  refine ⟨P, ?_⟩
  rw [hP, ← hsum, add_sub_cancel_left, ← hQ]
  exact isOfFinAddOrder_map _ (htorT Q)

end RingClass

end ZInQ.Contrib.CloudB3RC53.GenusOdd
