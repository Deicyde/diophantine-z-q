import ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor

/-!
# The remaining dictionary fields (ii)–(iv) from the packaging of the Heegner point data

Manuscript `diophantine_zq.tex`, tex 2914–2936. The interface `HeegnerPointData E`
(`RC/PrintsArith/Heegner.lean`) describes its fields as: `H d ⊆ ℚ̄` the ring class field of
conductor `d`; `relGal d ℓ` elements of `G_ℚ` restricting to the elements of
`Gal(H_{dℓ}/H_d)`; `frob d q` an element of `G_ℚ` restricting to the Frobenius `σ_q` at a prime
above the split `q` in `Gal(H_d/K)`.
The existential norm premise uses the anchor to impose these descriptions on the datum.
`FullAnchor` adds them to `GenuineHeegnerAnchor` along a fixed isomorphism
`κ : ℚ̄ ≃ K̄` of algebraic closures (`exists_kappa`).

* `field`: `x ∈ D.H n ↔ κ x ∈ H_{O_n}` (Tau Ceti's ring class field of `O_n = ℤ + n𝒪_K`, read in
  `K̄`), for the admissible conductors;
* `relGal_fix`, `relGal_inj`, `relGal_surj`: `relGal d q` fixes `D.H d` and restricts bijectively
  onto the restrictions to `D.H (dq)` of the elements of `G_ℚ` fixing `D.H d` (= `Gal(H_{dq}/H_d)`);
* `frob`: `frob d q` acts on `κ(D.H d) = H_{O_d}` as the Artin element of a prime `𝔮 ∣ q`.

From these the field-level dictionary of `H20Dictionary` is **proved**:

* `natCast_mem_conductor`, `ringClass_le_KS` (PROVED): `n ∈ cond(O_n)`, hence `H_{O_n} ⊆ K_{S₀}`
  when `S₀` contains the places dividing `n`; **`field_ii`** (PROVED): (ii) `κ(D.H n) ⊆ K_{S₀}`.
* `inflMap_apply_of_resAbs` (PROVED): `G_{K,S} → G_{K,S₀}` acts on `K_{S₀}` through any lift to
  `Gal(K̄/K)`.
* **`field_iii`** (PROVED): for `HP = G_{H_d}`, `HR = G_{H_{dq}}` (as subgroups of `G_{K,S}`,
  through `κ`), a transversal `t` of `HP / (HP ∩ HR)` and the `relGal` clauses, a bijection
  `e : HP/U ≃ relGal d q` with `κ ∘ (e τ) = t_τ ∘ κ` on `D.H (dq)`.
* **`field_iv`**, `field_iv_stab` (PROVED): for every `σ ∈ G_{K,S}` acting on `H_{O_d}` as the Artin
  element of `𝔮` (for the text: a Frobenius at `𝔮`; with lane E1's local Frobenius lift once it is
  on the integration branch), `κ ∘ frob = σ ∘ κ` on `D.H d`, and `D.H d` is stable under `frob⁻¹`.
* **`hnorm_of_full_anchor`** (PROVED): the input `hnorm` of `h1_shapiro` for the realized genuine
  Heegner points from the anchored norm relations, given the transfer data `HP = G_{H_d}`,
  `HR = G_{H_{dq}}` and a `σ` with the Artin restriction.

No monotonicity `H_d ⊆ H_{dq}` of ring class fields is needed. Here `S₀` is the support of the
ambient points; for the relaxed points take it to be the larger support `S₁` of `H20AmbientS`
(containing the primes dividing `dq`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside resAbs resAbs_apply_coe
  resAbs_surjective resUnr_comp)
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve
open scoped WeierstrassCurve

set_option linter.unusedSectionVars false

/-! ### The isomorphism of algebraic closures -/

/-- **`ℚ̄ ≃ K̄`** over `ℚ` (both are algebraic closures of `ℚ`). Kind: PROVED. -/
theorem exists_kappa (K : Type) [Field K] [NumberField K] :
    Nonempty (Qbar ≃ₐ[ℚ] AlgebraicClosure K) := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)
  have : IsAlgClosure ℚ (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  exact ⟨IsAlgClosure.equiv ℚ _ _⟩

/-! ### Ring class fields of `ℤ + n𝒪_K` lie in `K_{S₀}` -/

section Conductor

variable {K : Type} [Field K] [NumberField K]

/-- `n` lies in the conductor of `ℤ + n𝒪_K`. Kind: PROVED. -/
theorem natCast_mem_conductor (n : ℕ) [NeZero n] : (n : 𝓞 K) ∈ (conductorOrder K n).conductor := by
  intro y
  exact ⟨0, y, by push_cast; ring⟩

/-- **The ring class field of `ℤ + n𝒪_K` lies in `K_{S₀}`** when `S₀` contains the places dividing
`n` (PROVED; `RingClassKS.ringClassField_le_KS`). -/
theorem ringClass_le_KS (n : ℕ) [NeZero n] (S₀ : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    toAlgClosure (ringClassField (conductorOrder K n)) ≤ unramifiedOutside K S₀ :=
  ringClassField_le_KS (conductorOrder K n) S₀ fun v hv =>
    hS v ((Ideal.le_of_dvd hv) (natCast_mem_conductor n))

end Conductor

/-! ### The full anchor -/

section Anchor

variable (E : WeierstrassCurve ℚ) (K : Type) [Field K] [NumberField K]

/-- The inclusion `Kˢ → K̄`. Kind: definition. -/
abbrev sepIncl (z : SeparableClosure K) : AlgebraicClosure K := (z : AlgebraicClosure K)

open Classical in
/-- **The full genuine-point anchor** (tex 2914–2936; the descriptions of the fields of
`HeegnerPointData`): the genuine-point anchor, and along `κ : ℚ̄ ≃ K̄`: `D.H n` is the ring class
field of `ℤ + n𝒪_K`; `relGal d q` restricts bijectively onto `Gal(H_{dq}/H_d)`; `frob d q` acts on
`H_d` as the Artin element of a prime above `q`. Kind: definition. -/
structure FullAnchor (p : CSTParam E) (ι : Qbar →ₐ[ℚ] ℂ) (κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K)
    (D : HeegnerPointData E) : Prop where
  /-- the points are the images of the CM points -/
  anchor : GenuineHeegnerAnchor E K p ι D
  /-- `D.H n` is the ring class field of conductor `n` -/
  field : ∀ (n : ℕ) [NeZero n], Nat.Coprime n (D.N * D.DK.natAbs) →
    ∀ x : Qbar, x ∈ D.H n ↔ κ x ∈ toAlgClosure (ringClassField (conductorOrder K n))
  /-- the lifts fix `H_d` -/
  relGal_fix : ∀ d q : ℕ, D.Admissible d q → ∀ g ∈ D.relGal d q, ∀ x ∈ D.H d, g x = x
  /-- distinct lifts restrict to distinct elements of `Gal(H_{dq}/H_d)` -/
  relGal_inj : ∀ d q : ℕ, D.Admissible d q → ∀ g ∈ D.relGal d q, ∀ g' ∈ D.relGal d q,
    (∀ x ∈ D.H (d * q), g x = g' x) → g = g'
  /-- every element of `Gal(H_{dq}/H_d)` is the restriction of a lift -/
  relGal_surj : ∀ d q : ℕ, D.Admissible d q → ∀ g : GalQ, (∀ x ∈ D.H d, g x = x) →
    ∃ g' ∈ D.relGal d q, ∀ x ∈ D.H (d * q), g' x = g x
  /-- `frob d q` acts on `H_d` as the Artin element of a prime above `q` -/
  frob : ∀ (d q : ℕ) [NeZero d], D.Admissible d q → jacobiSym D.DK q = 1 →
    ∃ (𝔮 : HeightOneSpectrum (𝓞 K)) (_ : (q : 𝓞 K) ∈ 𝔮.asIdeal)
      (h : 𝔮.asIdeal ∈ integralIdealsPrimeTo (conductorOrder K d).conductorModulus),
      ∀ z : ringClassField (conductorOrder K d),
        κ (D.frob d q (κ.symm (sepIncl K z))) =
          sepIncl K (ringClassArtinEquiv (conductorOrder K d)
            ((conductorOrder K d).picClass ⟨𝔮.asIdeal, h⟩) z)

end Anchor

/-! ### (ii) -/

section FieldII

variable {E : WeierstrassCurve ℚ} {K : Type} [Field K] [NumberField K] {p : CSTParam E}
  {ι : Qbar →ₐ[ℚ] ℂ} {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} {D : HeegnerPointData E}

/-- **(ii) `κ(D.H n) ⊆ K_{S₀}`** (PROVED from the full anchor). -/
theorem field_ii (hA : FullAnchor E K p ι κ D) (n : ℕ) [NeZero n]
    (hcop : Nat.Coprime n (D.N * D.DK.natAbs)) (S₀ : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) :
    ∀ x ∈ D.H n, κ x ∈ unramifiedOutside K S₀ :=
  fun x hx => ringClass_le_KS n S₀ hS ((hA.field n hcop x).1 hx)

end FieldII

/-! ### The restriction `G_{K,S} → G_{K,S₀}` on elements -/

section Infl

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S)

/-- **`G_{K,S} → G_{K,S₀}` acts on `K_{S₀}` through any lift to `Gal(K̄/K)`** (PROVED). -/
theorem inflMap_apply_of_resAbs (g : GKS K S) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : resAbs K S σ = g) (y : unramifiedOutside K S₀) :
    ((galS K S₀ (inflMap K hS g) y : unramifiedOutside K S₀) : AlgebraicClosure K) =
      σ (y : AlgebraicClosure K) := by
  have h1 : inflMap K hS g = resAbs K S₀ σ := by
    rw [← hσ]
    exact resUnr_comp K hS σ
  rw [show galS K S₀ (inflMap K hS g) = resAbs K S₀ σ from h1, resAbs_apply_coe]

/-- A chosen lift of `g ∈ G_{K,S}` to `Gal(K̄/K)`. Kind: definition. -/
def liftAbs (g : GKS K S) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  Classical.choose (resAbs_surjective K S g)

theorem resAbs_liftAbs (g : GKS K S) : resAbs K S (liftAbs g) = g :=
  Classical.choose_spec (resAbs_surjective K S g)

end Infl

/-! ### (iii) -/

section FieldIII

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K) (L₁ L₂ : IntermediateField ℚ Qbar)
  (h₁ : ∀ x ∈ L₁, κ x ∈ unramifiedOutside K S₀) (h₂ : ∀ x ∈ L₂, κ x ∈ unramifiedOutside K S₀)
  (HP HR : Subgroup (GKS K S))
  (hHP : ∀ g : GKS K S, g ∈ HP ↔ ∀ x (hx : x ∈ L₁),
    ((galS K S₀ (inflMap K hS g) ⟨κ x, h₁ x hx⟩ : unramifiedOutside K S₀) : AlgebraicClosure K) =
      κ x)
  (hHR : ∀ g : GKS K S, g ∈ HR ↔ ∀ x (hx : x ∈ L₂),
    ((galS K S₀ (inflMap K hS g) ⟨κ x, h₂ x hx⟩ : unramifiedOutside K S₀) : AlgebraicClosure K) =
      κ x)
  (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR)
  (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ)
  (hKL : ∀ a : K, κ.symm (algebraMap K (AlgebraicClosure K) a) ∈ L₁)
  (R : Finset GalQ)
  (hfix : ∀ g ∈ R, ∀ x ∈ L₁, g x = x)
  (hinj : ∀ g ∈ R, ∀ g' ∈ R, (∀ x ∈ L₂, g x = g' x) → g = g')
  (hsurj : ∀ g : GalQ, (∀ x ∈ L₁, g x = x) → ∃ g' ∈ R, ∀ x ∈ L₂, g' x = g x)

/-- The transport `κ⁻¹ ∘ σ ∘ κ ∈ G_ℚ` of `σ ∈ Gal(K̄/K)`. Kind: definition. -/
def transportQ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : GalQ :=
  (κ.trans (σ.restrictScalars ℚ)).trans κ.symm

theorem transportQ_apply (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Qbar) :
    κ (transportQ κ σ x) = σ (κ x) := by
  simp [transportQ]

/-- The transport `κ ∘ g ∘ κ⁻¹ ∈ Gal(K̄/K)` of `g ∈ G_ℚ` fixing the image of `K`.
Kind: definition. -/
def transportK (g : GalQ) (hK : ∀ a : K, κ (g (κ.symm (algebraMap K _ a))) = algebraMap K _ a) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  { (κ.symm.trans g).trans κ with
    commutes' := hK }

theorem transportK_apply (g : GalQ) (hK) (y : AlgebraicClosure K) :
    transportK κ g hK y = κ (g (κ.symm y)) := rfl

include hHP in
/-- Elements of `HP` fix `L₁` through their lifts. Kind: PROVED. -/
theorem lift_fix (g : HP) (x : Qbar) (hx : x ∈ L₁) : liftAbs (g : GKS K S) (κ x) = κ x := by
  rw [← inflMap_apply_of_resAbs hS (g : GKS K S) _ (resAbs_liftAbs _) ⟨κ x, h₁ x hx⟩]
  exact (hHP g).1 g.2 x hx

/-- **The lifts of the transversal, in `G_ℚ`**. Kind: definition. -/
def tQ (τ : HP ⧸ U) : GalQ := transportQ κ (liftAbs ((t τ : HP) : GKS K S))

include hHP hsurj in
/-- Each lift of the transversal is matched by an element of `R` on `L₂`. Kind: PROVED. -/
theorem exists_match (τ : HP ⧸ U) :
    ∃ g' ∈ R, ∀ x ∈ L₂, g' x = tQ κ HP U t τ x :=
  hsurj _ fun x hx => κ.injective (by
    rw [tQ, transportQ_apply]
    exact lift_fix hS κ L₁ h₁ HP hHP (t τ) x hx)

/-- **The bijection `e : HP/U → R`**. Kind: definition. -/
def eFun (hmatch : ∀ τ, ∃ g' ∈ R, ∀ x ∈ L₂, g' x = tQ κ HP U t τ x) (τ : HP ⧸ U) : R :=
  ⟨Classical.choose (hmatch τ), (Classical.choose_spec (hmatch τ)).1⟩

theorem eFun_spec (hmatch : ∀ τ, ∃ g' ∈ R, ∀ x ∈ L₂, g' x = tQ κ HP U t τ x) (τ : HP ⧸ U)
    (x : Qbar) (hx : x ∈ L₂) :
    (eFun κ L₂ HP U t R hmatch τ : GalQ) x = tQ κ HP U t τ x :=
  (Classical.choose_spec (hmatch τ)).2 x hx

include hHR hU ht in
/-- Two elements of `HP` agreeing on `L₂` (through their lifts) lie in the same `U`-coset.
Kind: PROVED. -/
theorem coset_eq_of_agree (g g' : HP)
    (hag : ∀ x ∈ L₂, liftAbs (g : GKS K S) (κ x) = liftAbs (g' : GKS K S) (κ x)) :
    (QuotientGroup.mk g : HP ⧸ U) = QuotientGroup.mk g' := by
  rw [QuotientGroup.eq, hU]
  rw [hHR]
  intro x hx
  set y : unramifiedOutside K S₀ := ⟨κ x, h₂ x hx⟩
  have hg := inflMap_apply_of_resAbs hS (g : GKS K S) _ (resAbs_liftAbs _) y
  have hg' := inflMap_apply_of_resAbs hS (g' : GKS K S) _ (resAbs_liftAbs _) y
  have hcomb : galS K S₀ (inflMap K hS (g : GKS K S)) y =
      galS K S₀ (inflMap K hS (g' : GKS K S)) y := Subtype.ext (by rw [hg, hg']; exact hag x hx)
  change ((galS K S₀ (inflMap K hS ((g : GKS K S)⁻¹ * (g' : GKS K S))) y :
    unramifiedOutside K S₀) : AlgebraicClosure K) = κ x
  rw [map_mul, map_inv]
  change ((galS K S₀ (inflMap K hS (g : GKS K S))).symm
    (galS K S₀ (inflMap K hS (g' : GKS K S)) y) : AlgebraicClosure K) = κ x
  rw [← hcomb, AlgEquiv.symm_apply_apply]

include hHR hU in
/-- Two elements of `HP` in the same `U`-coset agree on `L₂` (through any lifts). Kind: PROVED. -/
theorem agree_of_coset_eq (g g' : HP) (h : (QuotientGroup.mk g : HP ⧸ U) = QuotientGroup.mk g')
    (σ σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : resAbs K S σ = (g : GKS K S))
    (hσ' : resAbs K S σ' = (g' : GKS K S)) (x : Qbar) (hx : x ∈ L₂) : σ (κ x) = σ' (κ x) := by
  rw [QuotientGroup.eq, hU, hHR] at h
  set y : unramifiedOutside K S₀ := ⟨κ x, h₂ x hx⟩
  have hx' := h x hx
  change ((galS K S₀ (inflMap K hS ((g : GKS K S)⁻¹ * (g' : GKS K S))) y :
    unramifiedOutside K S₀) : AlgebraicClosure K) = κ x at hx'
  rw [map_mul, map_inv] at hx'
  change ((galS K S₀ (inflMap K hS (g : GKS K S))).symm
    (galS K S₀ (inflMap K hS (g' : GKS K S)) y) : AlgebraicClosure K) = κ x at hx'
  have hy : galS K S₀ (inflMap K hS (g' : GKS K S)) y =
      galS K S₀ (inflMap K hS (g : GKS K S)) y := by
    have := congrArg (galS K S₀ (inflMap K hS (g : GKS K S)))
      (Subtype.ext hx' : (galS K S₀ (inflMap K hS (g : GKS K S))).symm
        (galS K S₀ (inflMap K hS (g' : GKS K S)) y) = y)
    rwa [AlgEquiv.apply_symm_apply] at this
  rw [← inflMap_apply_of_resAbs hS (g : GKS K S) σ hσ y,
    ← inflMap_apply_of_resAbs hS (g' : GKS K S) σ' hσ' y, hy]

include hHP hHR hU ht hfix hinj hKL in
/-- **`e` is a bijection** (PROVED). -/
theorem eFun_bijective (hmatch : ∀ τ, ∃ g' ∈ R, ∀ x ∈ L₂, g' x = tQ κ HP U t τ x) :
    Function.Bijective (eFun κ L₂ HP U t R hmatch) := by
  constructor
  · intro τ τ' hττ
    rw [← ht τ, ← ht τ']
    apply coset_eq_of_agree hS κ L₂ h₂ HP HR hHR U hU t ht
    intro x hx
    have h1 := eFun_spec κ L₂ HP U t R hmatch τ x hx
    have h2 := eFun_spec κ L₂ HP U t R hmatch τ' x hx
    rw [hττ] at h1
    have := h1.symm.trans h2
    have h3 := congrArg κ this
    rwa [tQ, tQ, transportQ_apply, transportQ_apply] at h3
  · intro ⟨g, hg⟩
    have hK : ∀ a : K, κ (g (κ.symm (algebraMap K _ a))) = algebraMap K _ a := by
      intro a
      rw [hfix g hg _ (hKL a), AlgEquiv.apply_symm_apply]
    set σ := transportK κ g hK
    let g₀ : GKS K S := resAbs K S σ
    have hmem : g₀ ∈ HP := by
      refine (hHP g₀).2 fun x hx => ?_
      rw [inflMap_apply_of_resAbs hS _ σ rfl, transportK_apply, AlgEquiv.symm_apply_apply,
        hfix g hg x hx]
    set τ : HP ⧸ U := QuotientGroup.mk (⟨g₀, hmem⟩ : HP)
    refine ⟨τ, Subtype.ext (hinj _ (eFun κ L₂ HP U t R hmatch τ).2 g hg fun x hx => ?_)⟩
    rw [eFun_spec κ L₂ HP U t R hmatch τ x hx]
    apply κ.injective
    rw [tQ, transportQ_apply]
    have hag := agree_of_coset_eq hS κ L₂ h₂ HP HR hHR U hU (t τ) ⟨g₀, hmem⟩ (ht τ)
      (liftAbs ((t τ : HP) : GKS K S)) σ (resAbs_liftAbs _) rfl x hx
    rw [hag, transportK_apply, AlgEquiv.symm_apply_apply]

include hHP hHR hU ht hfix hinj hsurj hKL in
/-- **(iii) on fields**: a bijection `e : HP/U ≃ R` with `κ ∘ (e τ) = t_τ ∘ κ` on `L₂` (PROVED). -/
theorem exists_e :
    ∃ e : HP ⧸ U ≃ R, ∀ τ (x) (hx : x ∈ L₂), κ ((e τ : GalQ) x) =
      (galS K S₀ (inflMap K hS ((t τ : HP) : GKS K S)) ⟨κ x, h₂ x hx⟩ : AlgebraicClosure K) := by
  have hmatch := exists_match hS κ L₁ L₂ h₁ HP hHP U t R hsurj
  refine ⟨Equiv.ofBijective _ (eFun_bijective hS κ L₁ L₂ h₁ h₂ HP HR hHP hHR U hU t ht hKL R hfix
    hinj hmatch), fun τ x hx => ?_⟩
  change κ ((eFun κ L₂ HP U t R hmatch τ : GalQ) x) = _
  rw [eFun_spec κ L₂ HP U t R hmatch τ x hx, tQ, transportQ_apply,
    inflMap_apply_of_resAbs hS _ _ (resAbs_liftAbs _)]

end FieldIII

/-! ### (iii) for the Heegner point data -/

section DataIII

variable {E : WeierstrassCurve ℚ} {K : Type} [Field K] [NumberField K] {p : CSTParam E}
  {ι : Qbar →ₐ[ℚ] ℂ} {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} {D : HeegnerPointData E}
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)

/-- `K ⊆ κ(D.H n)` (the ring class field contains `K`). Kind: PROVED. -/
theorem base_mem_field (hA : FullAnchor E K p ι κ D) (n : ℕ) [NeZero n]
    (hcop : Nat.Coprime n (D.N * D.DK.natAbs)) (a : K) :
    κ.symm (algebraMap K (AlgebraicClosure K) a) ∈ D.H n := by
  rw [hA.field n hcop, AlgEquiv.apply_symm_apply]
  exact IntermediateField.algebraMap_mem _ a

/-- **(iii) `relGal d q` ↔ the transversal** (PROVED from the full anchor): for the transfer data
`HP = G_{H_d}`, `HR = G_{H_{dq}}` (fixing `κ(D.H d)`, `κ(D.H (dq))` inside `K_{S₀}`), a bijection
`e : HP/U ≃ relGal d q` with `κ ∘ (e τ) = t_τ ∘ κ` on `D.H (dq)`. -/
theorem field_iii (hA : FullAnchor E K p ι κ D) {d q : ℕ} [NeZero d] (hadm : D.Admissible d q)
    (hκP : ∀ x ∈ D.H d, κ x ∈ unramifiedOutside K S₀)
    (hκR : ∀ x ∈ D.H (d * q), κ x ∈ unramifiedOutside K S₀)
    (HP HR : Subgroup (GKS K S))
    (hHP : ∀ g : GKS K S, g ∈ HP ↔ ∀ x (hx : x ∈ D.H d),
      ((galS K S₀ (inflMap K hS g) ⟨κ x, hκP x hx⟩ : unramifiedOutside K S₀) :
        AlgebraicClosure K) = κ x)
    (hHR : ∀ g : GKS K S, g ∈ HR ↔ ∀ x (hx : x ∈ D.H (d * q)),
      ((galS K S₀ (inflMap K hS g) ⟨κ x, hκR x hx⟩ : unramifiedOutside K S₀) :
        AlgebraicClosure K) = κ x)
    (U : Subgroup HP) (hU : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR)
    (t : HP ⧸ U → HP) (ht : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ) :
    ∃ e : HP ⧸ U ≃ D.relGal d q, ∀ τ (x) (hx : x ∈ D.H (d * q)), κ ((e τ).1 x) =
      (galS K S₀ (inflMap K hS ((t τ : HP) : GKS K S)) ⟨κ x, hκR x hx⟩ : AlgebraicClosure K) :=
  exists_e hS κ (D.H d) (D.H (d * q)) hκP hκR HP HR hHP hHR U hU t ht
    (base_mem_field hA d (Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) hadm.2.1))
    (D.relGal d q) (hA.relGal_fix d q hadm) (hA.relGal_inj d q hadm) (hA.relGal_surj d q hadm)

end DataIII

/-! ### (iv) -/

section DataIV

variable {E : WeierstrassCurve ℚ} {K : Type} [Field K] [NumberField K] {p : CSTParam E}
  {ι : Qbar →ₐ[ℚ] ℂ} {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} {D : HeegnerPointData E}
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)

/-- `Kˢ`-points of the ring class field lie in `K_{S₀}`. Kind: PROVED. -/
theorem sepIncl_mem (d : ℕ) [NeZero d]
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (z : ringClassField (conductorOrder K d)) : sepIncl K z ∈ unramifiedOutside K S₀ :=
  ringClass_le_KS d S₀ hSd ⟨z, z.2, rfl⟩

/-- **(iv) `frob d q` ↔ `σ`** (PROVED from the full anchor): there is a prime `𝔮 ∣ q` such that
every `σ ∈ G_{K,S}` acting on the ring class field `H_{O_d}` as the Artin element of `𝔮` (for the
text: a Frobenius at `𝔮`) satisfies `κ ∘ frob = σ ∘ κ` on `D.H d`. -/
theorem field_iv (hA : FullAnchor E K p ι κ D) {d q : ℕ} [NeZero d] (hadm : D.Admissible d q)
    (hsplit : jacobiSym D.DK q = 1)
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hκP : ∀ x ∈ D.H d, κ x ∈ unramifiedOutside K S₀) :
    ∃ (𝔮 : HeightOneSpectrum (𝓞 K)) (_ : (q : 𝓞 K) ∈ 𝔮.asIdeal)
      (h : 𝔮.asIdeal ∈ integralIdealsPrimeTo (conductorOrder K d).conductorModulus),
      ∀ σ : GKS K S, (∀ z : ringClassField (conductorOrder K d),
          ((galS K S₀ (inflMap K hS σ) ⟨sepIncl K z, sepIncl_mem d hSd z⟩ :
            unramifiedOutside K S₀) : AlgebraicClosure K) =
          sepIncl K (ringClassArtinEquiv (conductorOrder K d)
            ((conductorOrder K d).picClass ⟨𝔮.asIdeal, h⟩) z)) →
        ∀ x (hx : x ∈ D.H d), κ (D.frob d q x) =
          (galS K S₀ (inflMap K hS σ) ⟨κ x, hκP x hx⟩ : AlgebraicClosure K) := by
  have hcop : Nat.Coprime d (D.N * D.DK.natAbs) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) hadm.2.1
  obtain ⟨𝔮, hq, h, hfr⟩ := hA.frob d q hadm hsplit
  refine ⟨𝔮, hq, h, fun σ hσ x hx => ?_⟩
  obtain ⟨z, hz, hzx⟩ := (hA.field d hcop x).1 hx
  have hzx' : κ x = sepIncl K (⟨z, hz⟩ : ringClassField (conductorOrder K d)) := hzx.symm
  have h1 := hfr (⟨z, hz⟩ : ringClassField (conductorOrder K d))
  rw [← hzx', AlgEquiv.symm_apply_apply] at h1
  rw [h1, ← hσ (⟨z, hz⟩ : ringClassField (conductorOrder K d))]
  congr 2
  exact Subtype.ext hzx'.symm

/-- **`D.H d` is stable under `frob⁻¹`** (PROVED from the full anchor: `frob` acts on `κ(D.H d)` as
an automorphism). -/
theorem field_iv_stab (hA : FullAnchor E K p ι κ D) {d q : ℕ} [NeZero d] (hadm : D.Admissible d q)
    (hsplit : jacobiSym D.DK q = 1) : ∀ x ∈ D.H d, (D.frob d q)⁻¹ x ∈ D.H d := by
  have hcop : Nat.Coprime d (D.N * D.DK.natAbs) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) hadm.2.1
  obtain ⟨𝔮, hq, h, hfr⟩ := hA.frob d q hadm hsplit
  intro x hx
  obtain ⟨z, hz, hzx⟩ := (hA.field d hcop x).1 hx
  set ψ := ringClassArtinEquiv (conductorOrder K d) ((conductorOrder K d).picClass ⟨𝔮.asIdeal, h⟩)
  set z' := ψ.symm (⟨z, hz⟩ : ringClassField (conductorOrder K d))
  have h1 := hfr z'
  rw [show ψ z' = (⟨z, hz⟩ : ringClassField (conductorOrder K d)) from ψ.apply_symm_apply _] at h1
  have hx' : x = κ.symm (sepIncl K (⟨z, hz⟩ : ringClassField (conductorOrder K d))) := by
    have e : sepIncl K (⟨z, hz⟩ : ringClassField (conductorOrder K d)) = κ x := hzx
    rw [e, κ.symm_apply_apply]
  have h2 : D.frob d q (κ.symm (sepIncl K z')) = x := by
    apply κ.injective
    rw [h1, hx', AlgEquiv.apply_symm_apply]
  have h3 : (D.frob d q)⁻¹ x = κ.symm (sepIncl K z') := by
    rw [← h2]
    exact AlgEquiv.symm_apply_apply _ _
  rw [h3, hA.field d hcop, AlgEquiv.apply_symm_apply]
  exact ⟨z', z'.2, rfl⟩

end DataIV

/-! ### `hnorm` from the anchored norm relations -/

section Norm

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) [(E.baseChange K).IsElliptic]
  {Δ : Type} [CommGroup Δ] [Finite Δ]

/-- **`hnorm` for the realized genuine Heegner points** (PROVED from the anchored norm relations).
For the datum `D` and an admissible `(d, q)` with `q` split, take the transfer data
`HP = G_{H_d}`, `HR = G_{H_{dq}}` and a transversal `t` of `HP/(HP ∩ HR)`. There is a prime
`𝔮 ∣ q` such that for every `σ` acting on `H_{O_d}` as the Artin element of `𝔮`, the realized points
`y_R = 1 ⊗ P_{dq}`, `y_P = 1 ⊗ P_d` satisfy the input `hnorm` of `h1_shapiro`. The memberships
`hκP`, `hκR` are supplied by `field_ii`. -/
theorem hnorm_of_full_anchor {p : CSTParam E} {ι : Qbar →ₐ[ℚ] ℂ}
    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K}
    (hnorm : ∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K p ι κ D) :
    ∃ D : HeegnerPointData E, FullAnchor E K p ι κ D ∧ D.NormRelations ∧
      ∀ {d q : ℕ} [NeZero d] (_ : D.Admissible d q) (_ : jacobiSym D.DK q = 1)
        (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
        (hκP : ∀ x ∈ D.H d, κ x ∈ unramifiedOutside K S₀)
        (hκR : ∀ x ∈ D.H (d * q), κ x ∈ unramifiedOutside K S₀)
        (HP HR : Subgroup (GKS K S))
        (_ : ∀ g : GKS K S, g ∈ HP ↔ ∀ x (hx : x ∈ D.H d),
          ((galS K S₀ (inflMap K hS g) ⟨κ x, hκP x hx⟩ : unramifiedOutside K S₀) :
            AlgebraicClosure K) = κ x)
        (_ : ∀ g : GKS K S, g ∈ HR ↔ ∀ x (hx : x ∈ D.H (d * q)),
          ((galS K S₀ (inflMap K hS g) ⟨κ x, hκR x hx⟩ : unramifiedOutside K S₀) :
            AlgebraicClosure K) = κ x)
        (U : Subgroup HP) (_ : ∀ h : HP, h ∈ U ↔ (h : GKS K S) ∈ HR) [Fintype (HP ⧸ U)]
        (t : HP ⧸ U → HP) (_ : ∀ τ : HP ⧸ U, (QuotientGroup.mk (t τ) : HP ⧸ U) = τ),
        ∃ (𝔮 : HeightOneSpectrum (𝓞 K)) (_ : (q : 𝓞 K) ∈ 𝔮.asIdeal)
          (h : 𝔮.asIdeal ∈ integralIdealsPrimeTo (conductorOrder K d).conductorModulus),
          ∀ σ : GKS K S, (∀ z : ringClassField (conductorOrder K d),
              ((galS K S₀ (inflMap K hS σ) ⟨sepIncl K z, sepIncl_mem d hSd z⟩ :
                unramifiedOutside K S₀) : AlgebraicClosure K) =
              sepIncl K (ringClassArtinEquiv (conductorOrder K d)
                ((conductorOrder K d).picClass ⟨𝔮.asIdeal, h⟩) z)) →
            ∃ (hyR : ∃ Y' : (E.baseChange (D.H (d * q))).toAffine.Point,
                Affine.Point.map (W' := E) (D.H (d * q)).val Y' = D.y (d * q))
              (hyP : ∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
                Affine.Point.map (W' := E) (D.H d).val Y' = D.y d),
              ∑ τ : HP ⧸ U, ambRhoU hS (E.baseChange K) Δ (t τ : GKS K S)
                  (yPt E hS (Δ := Δ)
                    (realize E S₀ κ.toAlgHom (D.H (d * q)) hκR (D.y (d * q)) hyR)) =
                (E.LFunction q : ℤ) •
                    yPt E hS (Δ := Δ) (realize E S₀ κ.toAlgHom (D.H d) hκP (D.y d) hyP) -
                  ambRhoU hS (E.baseChange K) Δ σ
                    (yPt E hS (Δ := Δ) (realize E S₀ κ.toAlgHom (D.H d) hκP (D.y d) hyP)) -
                  ambRhoU hS (E.baseChange K) Δ σ⁻¹
                    (yPt E hS (Δ := Δ) (realize E S₀ κ.toAlgHom (D.H d) hκP (D.y d) hyP)) := by
  obtain ⟨D, hD, hA⟩ := hnorm
  refine ⟨D, hA, hD, fun {d q} _ hadm hsplit hSd hκP hκR HP HR hHP hHR U hU _ t ht => ?_⟩
  obtain ⟨hd, hdcop, hq, hqd⟩ := hadm
  have hcopP : Nat.Coprime d (D.N * D.DK.natAbs) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) hdcop
  have hdq : 0 < d * q := Nat.mul_pos hd hq.pos
  have hcopR : Nat.Coprime (d * q) (D.N * D.DK.natAbs) := by
    refine Nat.Coprime.mul_left hcopP ?_
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqd (h.trans ⟨6 * d, by ring⟩)
  have hyR := anchor_coords hA.anchor hdq hcopR
  have hyP := anchor_coords hA.anchor hd hcopP
  obtain ⟨e, he⟩ := field_iii hS hA ⟨hd, hdcop, hq, hqd⟩ hκP hκR HP HR hHP hHR U hU t ht
  obtain ⟨𝔮, hq', h, hiv⟩ := field_iv hS hA ⟨hd, hdcop, hq, hqd⟩ hsplit hSd hκP
  refine ⟨𝔮, hq', h, fun σ hσ => ⟨hyR, hyP, ?_⟩⟩
  exact hnorm_of_fields E hS HP U t D hD ⟨hd, hdcop, hq, hqd⟩ hsplit σ κ.toAlgHom hyR hyP hκR hκP
    e he (hiv σ hσ) (field_iv_stab hA ⟨hd, hdcop, hq, hqd⟩ hsplit)

end Norm

end ZInQ.Contrib.CloudB3E2.NormCochain
