import ZInQKernel.Contrib.CloudB3E1TameKummer.TameKummerPlace
import ZInQKernel.Contrib.OneProof.RC.Local.TameQuasiIsoLow

/-!
# The tame comparison under a change of coefficient ring, and two-torsion coefficients

Manuscript `diophantine_zq.tex`, tex 3470–3487 (the tame local free model (4.4) and the
unramified condition), for the coefficient stages of tex 4385–4451.

`tameCochainMap` compares the continuous cochains `C^•_cont(G, M)` of an `R`-module `M` with the
tame free model (4.4) over the same commutative ring `R`. Lane E1 proved that it is a
quasi-isomorphism at a finite place `w ∤ 2` for inflated coefficients over a FIELD
(`TameKummerPlace.quasiIso_inflation_of_milne`, from the PRINT `MilneADT_I_2_8`). The stage
modules of tex 4385–4451 are modules over the stage rings. This file removes the field hypothesis
for coefficients killed by `2`.

* Elementwise form (PROVED). `elementwise_of_quasiIsoAt_toCC` is the converse of
  `quasiIsoAt_toCC_of_elementwise`: a quasi-isomorphism in degree `n` satisfies the two
  elementwise conditions there. Hence (`quasiIso_toCC_iff_of_addEquiv`) whether a relation-indexed
  chain map is a quasi-isomorphism only depends on the underlying additive groups: degreewise
  additive bijections commuting with the differentials and with the components transport it,
  also between complexes over two different rings.
* Change of rings (PROVED). For one coefficient group `M` with two module structures over
  `R₁` and `R₂` (both commuting with `G`), the continuous cochains over `R₁` and over `R₂` are the
  same continuous functions `Gⁿ → M` (`contCochainRingEquiv`, `natContRingEquiv`), and the
  inhomogeneous differential does not depend on the ring (`contCochainRingEquiv_d`, the signs
  `(−1)^j` act through either ring in the same way); the two tame models have the same terms
  `M`, `M × M`, `M` and the same differentials (`modelRingEquiv`, `modelRingEquiv_d`); the two
  comparison maps agree (`tameCochainMap_ringEquiv`). Hence
  `quasiIso_tameCochainMap_iff_ringChange`: the comparison is a quasi-isomorphism over `R₁` iff
  it is one over `R₂`.
* Two-torsion coefficients over any ring (PROVED from the PRINT `MilneADT_I_2_8`).
  `quasiIso_inflation_two_torsion`: for a commutative ring `A` and inflated `A`-coefficients
  killed by `2`, the comparison over `A` is a quasi-isomorphism at `w ∤ 2`. The coefficients are
  `ZMod 2`-modules (`AddCommGroup.zmodModule`), the representation of `Gal(K_w^ur/K_w)` is one
  over the field `ZMod 2` with the same action, lane E1 applies over `ZMod 2`, and the change of
  rings returns to `A`.

Kinds: definitions and PROVED (the last from the PRINT `MilneADT_I_2_8`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith

/-! ### Quasi-isomorphisms of relation-indexed complexes, elementwise, in both directions -/

section Elementwise

variable {R : Type} [CommRing R] {A B : GCx R}

/-- **A quasi-isomorphism in degree `n` satisfies the elementwise conditions** (the converse of
`quasiIsoAt_toCC_of_elementwise`; tex 3470–3487): every cycle whose image is a boundary is a
boundary, and every cycle of the target is the image of a cycle up to a boundary. Kind:
PROVED. -/
theorem elementwise_of_quasiIsoAt_toCC (f : GHom A B) (m n p : ℤ) (hmn : m + 1 = n)
    (hnp : n + 1 = p) (h : QuasiIsoAt (GHom.toCC f) n) :
    (∀ z : A.X n, A.d n p hnp z = 0 → ∀ y : B.X m, B.d m n hmn y = f.f n n rfl z →
      ∃ x : A.X m, A.d m n hmn x = z) ∧
    (∀ w : B.X n, B.d n p hnp w = 0 → ∃ z : A.X n, A.d n p hnp z = 0 ∧
      ∃ y : B.X m, f.f n n rfl z - w = B.d m n hmn y) := by
  rw [quasiIsoAt_iff' _ m n p ((ComplexShape.up ℤ).prev_eq' hmn)
    ((ComplexShape.up ℤ).next_eq' hnp), quasiIso_iff_bijective_homologyMapLin] at h
  refine ⟨fun z hz y hy => ?_, fun w hw => ?_⟩
  · have hz' : ((A.toCC).d n p).hom z = 0 := (GCx.toCC_d_hom A n p hnp z).trans hz
    let zc : LinearMap.ker ((A.toCC).d n p).hom := ⟨z, hz'⟩
    have h0 : homologyMapLin ((HomologicalComplex.shortComplexFunctor' (ModuleCat R)
        (ComplexShape.up ℤ) m n p).map (GHom.toCC f)) (Submodule.Quotient.mk zc) = 0 := by
      change (Submodule.Quotient.mk (cyclesMapLin ((HomologicalComplex.shortComplexFunctor'
        (ModuleCat R) (ComplexShape.up ℤ) m n p).map (GHom.toCC f)) zc) :
          LinearMap.ker ((B.toCC).d n p).hom ⧸ LinearMap.range
            ((B.toCC).sc' m n p).moduleCatToCycles) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨y, Subtype.ext ?_⟩
      exact (GCx.toCC_d_hom B m n hmn y).trans hy
    have h1 := h.1 (h0.trans (map_zero _).symm)
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, (GCx.toCC_d_hom A m n hmn x).symm.trans (congrArg Subtype.val hx)⟩
  · have hw' : ((B.toCC).d n p).hom w = 0 := (GCx.toCC_d_hom B n p hnp w).trans hw
    obtain ⟨c, hc⟩ := h.2 (Submodule.Quotient.mk ⟨w, hw'⟩)
    induction c using Submodule.Quotient.induction_on with
    | H zc =>
      have hc' : (Submodule.Quotient.mk (cyclesMapLin ((HomologicalComplex.shortComplexFunctor'
          (ModuleCat R) (ComplexShape.up ℤ) m n p).map (GHom.toCC f)) zc) :
            LinearMap.ker ((B.toCC).d n p).hom ⧸ LinearMap.range
              ((B.toCC).sc' m n p).moduleCatToCycles) = Submodule.Quotient.mk ⟨w, hw'⟩ := hc
      rw [Submodule.Quotient.eq] at hc'
      obtain ⟨y, hy⟩ := hc'
      refine ⟨zc.1, (GCx.toCC_d_hom A n p hnp zc.1).symm.trans zc.2, y, ?_⟩
      exact (congrArg Subtype.val hy).symm.trans (GCx.toCC_d_hom B m n hmn y)

end Elementwise

/-! ### Transport of quasi-isomorphisms along additive bijections -/

section Transport

variable {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {A₁ B₁ : GCx R₁} {A₂ B₂ : GCx R₂}

/-- **Transport of a quasi-isomorphism** (tex 3470–3487): if degreewise additive bijections
`A₁ ≃ A₂`, `B₁ ≃ B₂` (of complexes over possibly different rings) commute with the differentials
and with the components of `f₁`, `f₂`, and `f₁` is a quasi-isomorphism, so is `f₂`. Kind:
PROVED. -/
theorem quasiIso_toCC_of_addEquiv (f₁ : GHom A₁ B₁) (f₂ : GHom A₂ B₂)
    (eA : ∀ n, A₁.X n ≃+ A₂.X n) (eB : ∀ n, B₁.X n ≃+ B₂.X n)
    (hA : ∀ i j (h : i + 1 = j) x, eA j (A₁.d i j h x) = A₂.d i j h (eA i x))
    (hB : ∀ i j (h : i + 1 = j) y, eB j (B₁.d i j h y) = B₂.d i j h (eB i y))
    (hf : ∀ n x, eB n (f₁.f n n rfl x) = f₂.f n n rfl (eA n x))
    (h : QuasiIso (GHom.toCC f₁)) : QuasiIso (GHom.toCC f₂) := by
  rw [quasiIso_iff] at h ⊢
  intro n
  obtain ⟨hinj, hsurj⟩ :=
    elementwise_of_quasiIsoAt_toCC f₁ (n - 1) n (n + 1) (by omega) rfl (h n)
  apply quasiIsoAt_toCC_of_elementwise f₂ (n - 1) n (n + 1) (by omega) rfl
  · intro z hz y hy
    obtain ⟨x, hx⟩ := hinj ((eA n).symm z) ((eA (n + 1)).injective (by
      rw [hA, AddEquiv.apply_symm_apply, hz, map_zero])) ((eB (n - 1)).symm y)
      ((eB n).injective (by rw [hB, hf, AddEquiv.apply_symm_apply,
        AddEquiv.apply_symm_apply, hy]))
    exact ⟨eA (n - 1) x, by rw [← hA, hx, AddEquiv.apply_symm_apply]⟩
  · intro w hw
    obtain ⟨z, hz, y, hy⟩ := hsurj ((eB n).symm w) ((eB (n + 1)).injective (by
      rw [hB, AddEquiv.apply_symm_apply, hw, map_zero]))
    refine ⟨eA n z, by rw [← hA, hz, map_zero], eB (n - 1) y, ?_⟩
    rw [← hB, ← hy, map_sub, hf, AddEquiv.apply_symm_apply]

/-- **Quasi-isomorphisms only see the underlying additive groups** (tex 3470–3487): under the
hypotheses of `quasiIso_toCC_of_addEquiv`, `f₁` is a quasi-isomorphism iff `f₂` is. Kind:
PROVED. -/
theorem quasiIso_toCC_iff_of_addEquiv (f₁ : GHom A₁ B₁) (f₂ : GHom A₂ B₂)
    (eA : ∀ n, A₁.X n ≃+ A₂.X n) (eB : ∀ n, B₁.X n ≃+ B₂.X n)
    (hA : ∀ i j (h : i + 1 = j) x, eA j (A₁.d i j h x) = A₂.d i j h (eA i x))
    (hB : ∀ i j (h : i + 1 = j) y, eB j (B₁.d i j h y) = B₂.d i j h (eB i y))
    (hf : ∀ n x, eB n (f₁.f n n rfl x) = f₂.f n n rfl (eA n x)) :
    QuasiIso (GHom.toCC f₁) ↔ QuasiIso (GHom.toCC f₂) :=
  ⟨quasiIso_toCC_of_addEquiv f₁ f₂ eA eB hA hB hf,
    quasiIso_toCC_of_addEquiv f₂ f₁ (fun n => (eA n).symm) (fun n => (eB n).symm)
      (fun i j h x => (eA j).injective (by
        rw [AddEquiv.apply_symm_apply, hA, AddEquiv.apply_symm_apply]))
      (fun i j h y => (eB j).injective (by
        rw [AddEquiv.apply_symm_apply, hB, AddEquiv.apply_symm_apply]))
      (fun n x => (eB n).injective (by
        rw [AddEquiv.apply_symm_apply, hf, AddEquiv.apply_symm_apply]))⟩

end Transport

/-! ### The continuous cochains over two rings -/

section Sign

variable {R₁ R₂ : Type} [Ring R₁] [Ring R₂] {M : Type} [AddCommGroup M] [Module R₁ M]
  [Module R₂ M]

/-- The signs `(−1)^n` of the inhomogeneous differential act on `M` in the same way through any
two rings (tex 3470–3487). Kind: PROVED. -/
theorem neg_one_pow_smul_ringChange (n : ℕ) (m : M) :
    (-1 : R₁) ^ n • m = (-1 : R₂) ^ n • m := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_smul, one_smul]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_smul, neg_smul, one_smul, one_smul]

end Sign

section RingChange

variable {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M : Type} [AddCommGroup M] [Module R₁ M] [Module R₂ M]
  [DistribMulAction G M] [SMulCommClass G R₁ M] [SMulCommClass G R₂ M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul R₁ M] [ContinuousConstSMul R₂ M] [ContinuousSMul G M]

variable (R₁ R₂ G M) in
/-- The continuous `n`-cochains over `R₁` and over `R₂` are the same continuous functions
`Gⁿ → M`: the identity on functions, an additive bijection (tex 3470–3487). Kind:
definition. -/
def contCochainRingEquiv (n : ℕ) : (contCochains R₁ G M).X n ≃+ (contCochains R₂ G M).X n where
  toFun c := ⟨asFun R₁ G M ((contSubCx R₁ G M).el c : contCochain R₁ G M n),
    mem_contCochain.mpr (mem_contCochain.mp ((contSubCx R₁ G M).el c).2)⟩
  invFun c := ⟨asFun R₂ G M ((contSubCx R₂ G M).el c : contCochain R₂ G M n),
    mem_contCochain.mpr (mem_contCochain.mp ((contSubCx R₂ G M).el c).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The identification of continuous cochains over two rings commutes with the inhomogeneous
differential, whose formula does not involve the ring (tex 3470–3487). Kind: PROVED. -/
theorem contCochainRingEquiv_d (n : ℕ) (c : (contCochains R₁ G M).X n) :
    contCochainRingEquiv R₁ R₂ G M (n + 1) (((contCochains R₁ G M).d n (n + 1)).hom c) =
      ((contCochains R₂ G M).d n (n + 1)).hom (contCochainRingEquiv R₁ R₂ G M n c) := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := R₁) (G := G) (M := M) n c g
  have h2 := contCochains_d_apply (k := R₂) (G := G) (M := M) n
    (contCochainRingEquiv R₁ R₂ G M n c) g
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  exact Finset.sum_congr rfl fun j _ => neg_one_pow_smul_ringChange _ _

variable (R₁ R₂ G M) in
/-- The identification of the continuous cochain complexes over two rings, extended by zero to
all integer degrees (tex 3470–3487). Kind: definition. -/
def natContRingEquiv : ∀ n : ℤ,
    (natCx (contCochains R₁ G M)).X n ≃+ (natCx (contCochains R₂ G M)).X n
  | Int.ofNat n => contCochainRingEquiv R₁ R₂ G M n
  | Int.negSucc _ => AddEquiv.refl PUnit

/-- The identification of the continuous cochain complexes over two rings commutes with the
differentials in every degree (tex 3470–3487). Kind: PROVED. -/
theorem natContRingEquiv_d (i j : ℤ) (h : i + 1 = j) (x : (natCx (contCochains R₁ G M)).X i) :
    natContRingEquiv R₁ R₂ G M j ((natCx (contCochains R₁ G M)).d i j h x) =
      (natCx (contCochains R₂ G M)).d i j h (natContRingEquiv R₁ R₂ G M i x) := by
  subst h
  rcases i with n | n
  · exact contCochainRingEquiv_d n x
  · have e1 : (natCx (contCochains R₁ G M)).d (Int.negSucc n) (Int.negSucc n + 1) rfl = 0 :=
      rfl
    have e2 : (natCx (contCochains R₂ G M)).d (Int.negSucc n) (Int.negSucc n + 1) rfl = 0 :=
      rfl
    rw [e1, e2, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

end RingChange

/-! ### The tame models over two rings -/

section ModelEquiv

variable {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {M : Type} [AddCommGroup M] [Module R₁ M]
  [Module R₂ M]

variable (R₁ R₂ M) in
/-- The terms `M`, `M × M`, `M` of the tame models over `R₁` and over `R₂` are the same groups:
the identity in every degree (tex 3470–3487). Kind: definition. -/
def modelRingEquiv : ∀ n : ℤ, cx3X (A := R₁) M (M × M) M n ≃+ cx3X (A := R₂) M (M × M) M n
  | .ofNat 0 => AddEquiv.refl M
  | .ofNat 1 => AddEquiv.refl (M × M)
  | .ofNat 2 => AddEquiv.refl M
  | .ofNat (_ + 3) => AddEquiv.refl PUnit
  | .negSucc _ => AddEquiv.refl PUnit

/-- The tame models (4.4) over `R₁` and over `R₂` have the same differentials when `Φ` and `g`
are the same maps of `M` (tex 3470–3487). Kind: PROVED. -/
theorem modelRingEquiv_d (Φ₁ g₁ : M →ₗ[R₁] M) (Φ₂ g₂ : M →ₗ[R₂] M) (q : ℕ) (hq : Odd q)
    (hc₁ : Φ₁ ∘ₗ g₁ = g₁ ∘ₗ Φ₁) (hg₁ : g₁ ∘ₗ g₁ = LinearMap.id)
    (hc₂ : Φ₂ ∘ₗ g₂ = g₂ ∘ₗ Φ₂) (hg₂ : g₂ ∘ₗ g₂ = LinearMap.id)
    (hΦ : ∀ m, Φ₁ m = Φ₂ m) (hg : ∀ m, g₁ m = g₂ m) (i j : ℤ) (h : i + 1 = j)
    (y : (tameFreeModel Φ₁ g₁ q hq hc₁ hg₁).X i) :
    modelRingEquiv R₁ R₂ M j ((tameFreeModel Φ₁ g₁ q hq hc₁ hg₁).d i j h y) =
      (tameFreeModel Φ₂ g₂ q hq hc₂ hg₂).d i j h (modelRingEquiv R₁ R₂ M i y) := by
  by_cases h0 : i = 0
  · subst h0
    obtain rfl : j = 1 := by omega
    revert y
    rintro (y : M)
    change ((Φ₁ - LinearMap.id : M →ₗ[R₁] M) y, (g₁ - LinearMap.id : M →ₗ[R₁] M) y) =
      ((Φ₂ - LinearMap.id : M →ₗ[R₂] M) y, (g₂ - LinearMap.id : M →ₗ[R₂] M) y)
    rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, hΦ,
      hg, LinearMap.id_apply, LinearMap.id_apply]
  · by_cases h1 : i = 1
    · subst h1
      obtain rfl : j = 2 := by omega
      obtain ⟨v, u⟩ := y
      change -(g₁ - LinearMap.id : M →ₗ[R₁] M) v + (Φ₁ - tameNorm q g₁) u =
        -(g₂ - LinearMap.id : M →ₗ[R₂] M) v + (Φ₂ - tameNorm q g₂) u
      simp only [tameNorm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hΦ, hg]
    · have z1 : (tameFreeModel Φ₁ g₁ q hq hc₁ hg₁).d i j h = 0 := cx3D_eq_zero _ _ i j h h0 h1
      have z2 : (tameFreeModel Φ₂ g₂ q hq hc₂ hg₂).d i j h = 0 := cx3D_eq_zero _ _ i j h h0 h1
      exact (congrArg (modelRingEquiv R₁ R₂ M j) (LinearMap.congr_fun z1 y)).trans
        ((map_zero _).trans (LinearMap.congr_fun z2 _).symm)

end ModelEquiv

/-! ### The tame comparison over two rings -/

section ComparisonRingChange

variable {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M : Type} [AddCommGroup M] [Module R₁ M] [Module R₂ M]
  [DistribMulAction G M] [SMulCommClass G R₁ M] [SMulCommClass G R₂ M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul R₁ M] [ContinuousConstSMul R₂ M] [ContinuousSMul G M]

/-- The comparison maps over `R₁` and over `R₂` agree under the identifications of the cochains
and of the models: `evalZero`, `tameOne = (c(φ), c(σ))` and `tameE` only use the values of the
cochains and the maps `Φ = (φ • ·)`, `g = (σ • ·)` (tex 3470–3487). Kind: PROVED. -/
theorem tameCochainMap_ringEquiv (Φ₁ g₁ : M →ₗ[R₁] M) (Φ₂ g₂ : M →ₗ[R₂] M) (φ σ : G)
    (q : ℕ) (hq : Odd q) (hΦ₁ : ∀ m, Φ₁ m = φ • m) (hgσ₁ : ∀ m, g₁ m = σ • m)
    (hg₁ : g₁ ∘ₗ g₁ = LinearMap.id) (hc₁ : Φ₁ ∘ₗ g₁ = g₁ ∘ₗ Φ₁) (hΦ₂ : ∀ m, Φ₂ m = φ • m)
    (hgσ₂ : ∀ m, g₂ m = σ • m) (hg₂ : g₂ ∘ₗ g₂ = LinearMap.id) (hc₂ : Φ₂ ∘ₗ g₂ = g₂ ∘ₗ Φ₂)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (n : ℤ) (x : (natCx (contCochains R₁ G M)).X n) :
    modelRingEquiv R₁ R₂ M n
        ((tameCochainMap Φ₁ g₁ φ σ q hq hΦ₁ hgσ₁ hg₁ hc₁ hrel).f n n rfl x) =
      (tameCochainMap Φ₂ g₂ φ σ q hq hΦ₂ hgσ₂ hg₂ hc₂ hrel).f n n rfl
        (natContRingEquiv R₁ R₂ G M n x) := by
  rcases n with (_ | _ | _ | n) | n
  · rfl
  · rfl
  · revert x
    rintro (x : (contCochains R₁ G M).X 2)
    change tameE Φ₁ g₁ φ σ q x = tameE Φ₂ g₂ φ σ q (contCochainRingEquiv R₁ R₂ G M 2 x)
    rw [tameE_apply, tameE_apply]
    simp only [hΦ₁, hΦ₂, hgσ₁, hgσ₂]
    rfl
  · rfl
  · rfl

/-- **Change of rings for the tame comparison** (tex 3470–3487; tex 4385–4451 for the stage
rings). Let `M` carry two module structures, over `R₁` and over `R₂`, both commuting with `G`, and
let `Φᵢ = (φ • ·)`, `gᵢ = (σ • ·)` over `Rᵢ`. Then the comparison `tameCochainMap` over `R₁` is a
quasi-isomorphism iff the comparison over `R₂` is one. In particular this holds for inflated
coefficients, `Φ = DistribSMul.toLinearMap R M φ` and `g = id`. Kind: PROVED. -/
theorem quasiIso_tameCochainMap_iff_ringChange (Φ₁ g₁ : M →ₗ[R₁] M) (Φ₂ g₂ : M →ₗ[R₂] M)
    (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ₁ : ∀ m, Φ₁ m = φ • m) (hgσ₁ : ∀ m, g₁ m = σ • m)
    (hg₁ : g₁ ∘ₗ g₁ = LinearMap.id) (hc₁ : Φ₁ ∘ₗ g₁ = g₁ ∘ₗ Φ₁) (hΦ₂ : ∀ m, Φ₂ m = φ • m)
    (hgσ₂ : ∀ m, g₂ m = σ • m) (hg₂ : g₂ ∘ₗ g₂ = LinearMap.id) (hc₂ : Φ₂ ∘ₗ g₂ = g₂ ∘ₗ Φ₂)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    QuasiIso (GHom.toCC (tameCochainMap Φ₁ g₁ φ σ q hq hΦ₁ hgσ₁ hg₁ hc₁ hrel)) ↔
      QuasiIso (GHom.toCC (tameCochainMap Φ₂ g₂ φ σ q hq hΦ₂ hgσ₂ hg₂ hc₂ hrel)) :=
  quasiIso_toCC_iff_of_addEquiv _ _ (natContRingEquiv R₁ R₂ G M) (modelRingEquiv R₁ R₂ M)
    natContRingEquiv_d
    (modelRingEquiv_d Φ₁ g₁ Φ₂ g₂ q hq hc₁ hg₁ hc₂ hg₂ (fun m => (hΦ₁ m).trans (hΦ₂ m).symm)
      (fun m => (hgσ₁ m).trans (hgσ₂ m).symm))
    (tameCochainMap_ringEquiv Φ₁ g₁ Φ₂ g₂ φ σ q hq hΦ₁ hgσ₁ hg₁ hc₁ hΦ₂ hgσ₂ hg₂ hc₂ hrel)

end ComparisonRingChange

/-! ### Two-torsion coefficients over any ring at a place -/

section TwoTorsion

open NumberField IsDedekindDomain TauCeti ValuativeRel
open ZInQ.Manuscript.RC.Limits (MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (resUr)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **The tame comparison at `w ∤ 2` for inflated two-torsion coefficients over any ring**
(tex 3470–3487; tex 4385–4451 for the stage rings). Let `A` be a commutative ring, `X` a finite
discrete `A`-representation of `Gal(K_w^ur/K_w)`, and `f : X → M` an `A`-linear bijection onto a
`G_{K_w}`-module with `f (resUr g • x) = g • f x`, with `M` killed by `2`. For an Iwasawa triple
`(φ, σ, P)` at `w`, the comparison `tameCochainMap` over `A` (with `Φ = (φ • ·)`, `g = id`) is a
quasi-isomorphism, given the PRINT `MilneADT_I_2_8` only. Proof: `M` and `X` are `ZMod 2`-modules,
`X` is a representation over the field `ZMod 2` with the same action, lane E1
(`TameKummerPlace.quasiIso_inflation_of_milne`) applies over `ZMod 2`, and
`quasiIso_tameCochainMap_iff_ringChange` returns to `A`. Kind: PROVED (from the PRINT). -/
theorem quasiIso_inflation_two_torsion (h28 : MilneADT_I_2_8) (h2 : (2 : 𝓞 K) ∉ w.asIdeal)
    (A : Type) [CommRing A] [TopologicalSpace A] (M : Type) [AddCommGroup M] [Module A M]
    [DistribMulAction (Gloc K w) M] [SMulCommClass (Gloc K w) A M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (Gloc K w) M] [Finite M]
    (X : TopRep.{0} A (GUr K w)) [ContinuousSMul (GUr K w) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[A] M)
    (hf : ∀ (g : Gloc K w) (x : X.V), f (resUr K w g • x) = g • f x)
    (hbij : Function.Bijective f) (h2M : ∀ m : M, (2 : ℕ) • m = 0) {φ σ : Gloc K w}
    {P : Subgroup (Gloc K w)} (hI : IsIwasawaTriple K w φ σ P) :
    QuasiIso (GHom.toCC (tameCochainMap (DistribSMul.toLinearMap A M φ) LinearMap.id φ σ
      (Nat.card 𝓀[w.adicCompletion K]) (odd_natCard_residueField h2) (fun _ => rfl)
      (fun m => (smul_eq_self_of_mem_inertia_of_inflation f hf hbij.2 hI.mem_inertia m).symm)
      (LinearMap.id_comp _) ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm)
      hI.rel)) := by
  let _ : Module (ZMod 2) M := AddCommGroup.zmodModule h2M
  have h2X : ∀ x : X.V, (2 : ℕ) • x = 0 := fun x =>
    hbij.1 (by rw [map_nsmul, h2M, map_zero])
  let _ : Module (ZMod 2) X.V := AddCommGroup.zmodModule h2X
  have : SMulCommClass (Gloc K w) (ZMod 2) M :=
    ⟨fun g c m => ZMod.map_smul (DistribSMul.toAddMonoidHom M g) c m⟩
  have : ContinuousSMul (ZMod 2) X.V := ⟨continuous_of_discreteTopology⟩
  let ρ' : ContRepresentation (ZMod 2) (GUr K w) X.V := ContRepresentation.ofMonoidHom
    { toFun := fun γ =>
        { toLinearMap :=
            AddMonoidHom.toZModLinearMap 2 (X.ρ.toMonoidHom γ).toLinearMap.toAddMonoidHom
          cont := (X.ρ.toMonoidHom γ).cont }
      map_one' := by
        ext x
        exact congrArg (fun T : X.V →L[A] X.V => T x) (map_one X.ρ.toMonoidHom)
      map_mul' := fun a b => by
        ext x
        exact congrArg (fun T : X.V →L[A] X.V => T x) (map_mul X.ρ.toMonoidHom a b) }
  let X' : TopRep.{0} (ZMod 2) (GUr K w) := TopRep.of ρ'
  have : ContinuousSMul (GUr K w) X'.V := ‹ContinuousSMul (GUr K w) X.V›
  have : DiscreteTopology X'.V := ‹DiscreteTopology X.V›
  have : Finite X'.V := ‹Finite X.V›
  let f' : X'.V →ₗ[ZMod 2] M := AddMonoidHom.toZModLinearMap 2 f.toAddMonoidHom
  have hf' : ∀ (g : Gloc K w) (x : X'.V), f' (resUr K w g • x) = g • f' x := hf
  have hQ := TameKummerPlace.quasiIso_inflation_of_milne h28 h2 (ZMod 2) M X' f' hf' hbij.2 hI
    ⟨1, fun m => by rw [pow_one]; exact h2M m⟩
  exact (quasiIso_tameCochainMap_iff_ringChange (R₁ := ZMod 2) (R₂ := A)
    (DistribSMul.toLinearMap (ZMod 2) M φ) LinearMap.id (DistribSMul.toLinearMap A M φ)
    LinearMap.id φ σ _ _ _ _ _ _ _ _ _ _ _).mp hQ

end TwoTorsion

end ZInQ.Manuscript.RC.Local
