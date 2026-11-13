import Mathlib
import ZInQKernel.HDecomp.B3Unram.B3b
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.Objects

/-!
# g4-weilres, part 1: Galois-theoretic unramifiedness gives ideal-theoretic unramifiedness

The converse of glue-b3-unram's `GlueB3Unram.inertia_le_of_unramifiedAt`. For a finite Galois
`L ⊆ ℚ̄` and a prime `p`: if every inertia group `I_w ≤ G_ℚ` over `p` fixes `L` pointwise, then
every prime of `𝓞 L` above `p` has ramification index `1` (glue-descent's `UnramifiedAt L p`, the
form consumed by `GlueDescent.B3Q.b3_degree_le_QM`).

Proof: Mathlib's profinite transitivity and its surjectivity of the stabilizer of a prime of the
algebraic integers onto the residue automorphisms (`Ideal.Quotient.stabilizerHom_surjective_of_profinite`),
over the fixed ring of `G_L`, lift an element of the finite inertia group `I(P | p) ≤ Gal(L/ℚ)` to
an element of some `I_w`; the hypothesis kills it, and `|I(P | p)| = e(P | p)` (Mathlib).
The pattern is glue-b3b's `exists_inertia_neg`, with `α` replaced by all of `L`.

No leaf is used.
-/

namespace G4WeilRes

open GlueB3Unram GlueDescent.B2Q NumberField
open scoped Pointwise

/-! ## Places over `p` exist -/

/-- There is a valuation subring of `ℚ̄` over every prime `p`. -/
theorem exists_liesOver (p : ℕ) (hp : p.Prime) : ∃ w : ValuationSubring Qbar, LiesOver w p := by
  let A : Subring Qbar := ⊥
  let pA : A := ⟨(p : Qbar), by simpa using (⊥ : Subring Qbar).natCast_mem p⟩
  let I : Ideal A := Ideal.span {pA}
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := by rw [h]; trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp a.2
    have h2 : ((n * p : ℤ) : Qbar) = ((1 : ℤ) : Qbar) := by
      have := congrArg Subtype.val ha
      simp only [Subring.coe_mul, OneMemClass.coe_one] at this
      push_cast
      rw [hn]; exact this
    have h3 : n * (p : ℤ) = 1 := Int.cast_injective h2
    have h4 : (p : ℤ) ∣ 1 := ⟨n, by rw [← h3]; ring⟩
    have := Int.eq_one_of_dvd_one (by positivity) h4
    exact hp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨B, ?_⟩
  have hmem : (p : Qbar) ∈ B.nonunits := hB ⟨pA, Ideal.subset_span rfl, rfl⟩
  exact (ValuationSubring.mem_nonunits_iff B).mp hmem

/-! ## A Galois automorphism maps a normal subfield into itself -/

theorem map_mem_of_normal (L : IntermediateField ℚ Qbar) [Normal ℚ L] (σ : Gal) {y : Qbar}
    (hy : y ∈ L) : σ y ∈ L := by
  have h := AlgEquiv.restrictNormal_commutes σ L ⟨y, hy⟩
  rw [← show algebraMap L Qbar ⟨y, hy⟩ = y from rfl, ← h]
  exact (AlgEquiv.restrictNormal σ L ⟨y, hy⟩).2

/-! ## Lifting a residually trivial automorphism of `L` into an inertia group -/

/-- `σ` acts trivially modulo `w` on the algebraic integers of `L`. -/
def ResTrivOn (L : IntermediateField ℚ Qbar) (w : ValuationSubring Qbar) (σ : Gal) : Prop :=
  ∀ y : Qbar, IsIntegral ℤ y → y ∈ L → w.valuation (σ y - y) < 1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The inertia lift.** Let `L ⊆ ℚ̄` be finite Galois, `w` a place over `p` and `σ ∈ G_ℚ`
acting trivially modulo `w` on the algebraic integers of `L`. Then some `s ∈ I_w` agrees with
`σ` on `L`. -/
theorem exists_inertia_restrict (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (p : ℕ) (hp : p.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w p)
    (σ : Gal) (hσ : ResTrivOn L w σ) :
    ∃ s : Gal, s ∈ inertiaGQ w ∧ ∀ y ∈ L, s y = σ y := by
  classical
  let H : Subgroup Gal := L.fixingSubgroup
  have hH : ∀ g : Gal, g ∈ H ↔ ∀ y ∈ L, g y = y := fun g =>
    IntermediateField.mem_fixingSubgroup_iff L g
  have hHopen : IsOpen (H : Set Gal) := IntermediateField.fixingSubgroup_isOpen L
  have hHclosed : IsClosed (H : Set Gal) := Subgroup.isClosed_of_isOpen H hHopen
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let A := FixedPoints.subalgebra ℤ B H
  let Q := centerIdeal w
  haveI : SMulCommClass H A B := ⟨fun h a b => by
    rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_mul', a.2 h]⟩
  -- elements of `A` lie in `L`
  have hAL : ∀ a : A, ((a : B) : Qbar) ∈ L := by
    intro a
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro g hg
    have := a.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hAint : ∀ a : A, IsIntegral ℤ ((a : B) : Qbar) := fun a =>
    (mem_integralClosure_iff ℤ Qbar).mp (a : B).2
  -- the valuation input on `A`
  have hAval : ∀ (a : A) (τ : Gal), ResTrivOn L w τ →
      w.valuation (((a : B) : Qbar) - τ ((a : B) : Qbar)) < 1 := by
    intro a τ hτ
    rw [Valuation.map_sub_swap]
    exact hτ _ (hAint a) (hAL a)
  -- `σ⁻¹` is also residually trivial on `L`
  have hσi : ResTrivOn L w σ⁻¹ := by
    intro y hy hyL
    have hy' : IsIntegral ℤ ((σ⁻¹ : Gal) y) := hy.map ((σ⁻¹ : Gal) : Qbar →+* Qbar).toIntAlgHom
    have h := hσ _ hy' (map_mem_of_normal L σ⁻¹ hyL)
    have hss : σ ((σ⁻¹ : Gal) y) = y := by
      show (σ * σ⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    rw [hss, Valuation.map_sub_swap] at h
    exact h
  -- step 1: `σ • Q` and `Q` lie over the same prime of `A`
  have hunder : (σ • Q).under A = Q.under A := by
    ext a
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal, mem_centerIdeal]
    have h := hAval a σ⁻¹ hσi
    show w.valuation ((σ⁻¹ : Gal) ((a : B) : Qbar)) < 1 ↔ w.valuation ((a : B) : Qbar) < 1
    constructor
    · intro h1
      have : ((a : B) : Qbar) = (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) +
          (σ⁻¹ : Gal) ((a : B) : Qbar) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
    · intro h1
      have : (σ⁻¹ : Gal) ((a : B) : Qbar) = ((a : B) : Qbar) -
          (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h)
  -- step 2: transitivity over `A` gives `τ` stabilizing `Q` and agreeing with `σ` on `L`
  haveI hσQ : (σ • Q).IsPrime := by
    show (σ • centerIdeal w).IsPrime
    rw [← centerIdeal_smul]; infer_instance
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := H)
    (σ • Q) Q hunder
  let τ : Gal := (g : Gal) * σ
  have hτQ : τ • Q = Q := by
    show ((g : Gal) * σ) • Q = Q
    rw [mul_smul]; exact hg.symm
  have hτL : ∀ y ∈ L, τ y = σ y := by
    intro y hy
    show (g : Gal) (σ y) = σ y
    exact (hH g).mp g.2 _ (map_mem_of_normal L σ hy)
  have hτ : ResTrivOn L w τ := by
    intro y hy hyL
    rw [hτL y hyL]; exact hσ y hy hyL
  -- step 3: `τ` induces an `A/P`-automorphism of `B/Q`
  let f : B ≃+* B := MulSemiringAction.toRingEquiv Gal B τ
  have hQf : Q = Q.map f := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨τ⁻¹ • b, ?_, by simp [f]⟩
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hτQ]; exact hb
    · rintro ⟨x, hx, rfl⟩
      rw [← hτQ]
      exact Ideal.smul_mem_pointwise_smul_iff.mpr hx
  let e : (B ⧸ Q) ≃+* (B ⧸ Q) := Ideal.quotientEquiv Q Q f hQf
  have he : ∀ b : B, e (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (τ • b) := fun b => rfl
  let φ : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := e) (by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, he, Ideal.Quotient.eq, mem_centerIdeal]
    have h := hAval a τ hτ
    rw [Valuation.map_sub_swap] at h
    exact h)
  -- step 4: Mathlib's surjectivity gives `h' ∈ H` acting on `B/Q` as `τ`
  obtain ⟨h', hh'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under A) Q φ
  have hact : ∀ b : B, Ideal.Quotient.mk Q (((h' : H) : Gal) • b) =
      Ideal.Quotient.mk Q (τ • b) := by
    intro b
    have := congrArg (fun ψ => ψ (Ideal.Quotient.mk Q b)) hh'
    exact this
  let k : Gal := ((h' : H) : Gal)
  have hkQ : k • Q = Q := h'.2
  have hkL : ∀ y ∈ L, k y = y := (hH k).mp (h' : H).2
  let s : Gal := k⁻¹ * τ
  refine ⟨s, ?_, ?_⟩
  · apply mem_inertia_of_center hp hw s
    · show (k⁻¹ * τ) • Q = Q
      rw [mul_smul, hτQ, inv_smul_eq_iff, hkQ]
    · intro b
      have h1 := hact (s • b)
      have h2 : ((h' : H) : Gal) • (s • b) = τ • b := by
        show k • ((k⁻¹ * τ) • b) = τ • b
        rw [mul_smul, smul_inv_smul]
      rw [h2, Ideal.Quotient.eq] at h1
      have h3 : b - s • b ∈ Q := by
        have h4 : τ • (b - s • b) ∈ τ • Q := by rw [hτQ, smul_sub]; exact h1
        rwa [Ideal.smul_mem_pointwise_smul_iff] at h4
      have := Q.neg_mem h3
      rwa [neg_sub] at this
  · intro y hy
    show k⁻¹ (τ y) = σ y
    rw [hτL y hy]
    have hk' : k⁻¹ ∈ H := H.inv_mem (h' : H).2
    exact (hH _).mp hk' _ (map_mem_of_normal L σ hy)

/-! ## The bridge -/

/-- `P.under ℤ = (p)` for a prime of `𝓞 L` containing the prime `p`. -/
theorem under_eq_span {L : IntermediateField ℚ Qbar} [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hpP : ((p : ℤ) : 𝓞 L) ∈ P) :
    P.under ℤ = Ideal.span {(p : ℤ)} := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : (p : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using hpP
  have hle : Ideal.span {(p : ℤ)} ≤ P.under ℤ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  exact ((Int.ideal_span_isMaximal_of_prime p).eq_of_le
    (Ideal.comap_isPrime (algebraMap ℤ (𝓞 L)) P).ne_top hle).symm

/-- **Bridge (glue, proved).** If every inertia group of `G_ℚ` over `p` fixes the finite Galois
field `L ⊆ ℚ̄`, then `L` is unramified at `p` in glue-descent's ideal-theoretic sense. -/
theorem unramifiedAt_of_inertia_le (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (p : ℕ) (hp : p.Prime)
    (h : ∀ w : ValuationSubring Qbar, LiesOver w p → inertiaGQ w ≤ L.fixingSubgroup) :
    UnramifiedAt L p := by
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  intro P hP hpP
  obtain ⟨w, hw⟩ := exists_liesOver p hp
  let P₀ : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal w).comap (embW L w)
  haveI hP₀prime : P₀.IsPrime := Ideal.comap_isPrime _ _
  have hpP₀ : ((p : ℤ) : 𝓞 L) ∈ P₀ := by
    show embW L w ((p : ℤ) : 𝓞 L) ∈ IsLocalRing.maximalIdeal w
    rw [ValuationSubring.valuation_lt_one_iff]
    have : ((embW L w ((p : ℤ) : 𝓞 L) : w) : Qbar) = (p : Qbar) := by
      simp [embW, emb]
    rw [this]; exact hw
  let G := L ≃ₐ[ℚ] L
  have hunder : P.under ℤ = P₀.under ℤ := by
    rw [under_eq_span p hp P hpP, under_eq_span p hp P₀ hpP₀]
  -- the inertia group of `P₀` in `Gal(L/ℚ)` is trivial
  have htriv : ∀ g ∈ P₀.inertia G, g = 1 := by
    intro g hg
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (E := Qbar) (K₁ := L) g
    have hσL : ∀ x : L, algebraMap L Qbar (g x) = σ (algebraMap L Qbar x) := by
      intro x
      rw [← hσ]; exact AlgEquiv.restrictNormal_commutes σ L x
    have hres : ResTrivOn L w σ := by
      intro y hy hyL
      let x : 𝓞 L := ⟨⟨y, hyL⟩, by
        rw [mem_integralClosure_iff]
        exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L Qbar)
          (algebraMap L Qbar).injective).mp hy⟩
      have hx := (Ideal.mem_inertia.mp hg) x
      change embW L w (g • x - x) ∈ IsLocalRing.maximalIdeal w at hx
      rw [ValuationSubring.valuation_lt_one_iff] at hx
      have he1 : ((embW L w (g • x - x) : w) : Qbar) = emb L (g • x) - emb L x := by
        show emb L (g • x - x) = _
        rw [map_sub]
      have he2 : emb L (g • x) = σ y := by
        simp only [emb, RingHom.comp_apply]
        rw [show σ y = σ (algebraMap L Qbar ⟨y, hyL⟩) from rfl, ← hσL]
        rfl
      have he : ((embW L w (g • x - x) : w) : Qbar) = σ y - y := by
        rw [he1, he2]; rfl
      rw [he] at hx; exact hx
    obtain ⟨s, hs, hsL⟩ := exists_inertia_restrict L p hp w hw σ hres
    have hsfix := (IntermediateField.mem_fixingSubgroup_iff L s).mp (h w hw hs)
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L Qbar).injective
    rw [hσL x]
    show σ (x : Qbar) = (x : Qbar)
    rw [← hsL _ x.2, hsfix _ x.2]
  have hcard : Nat.card (P₀.inertia G) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  have e₀ : P₀.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P₀.under ℤ) P₀ G,
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P₀.under ℤ) P₀, hcard]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G, hunder,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P₀.under ℤ) P₀ G, e₀]

/-- The Galois form of "unramified outside `T`" gives glue-descent's form at every `p ∉ T`. -/
theorem unramifiedAt_of_galUnramifiedOutside (L : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (T : Finset ℕ) (h : GalUnramifiedOutside L T) :
    ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p :=
  fun p hpT => unramifiedAt_of_inertia_le L p p.2 (fun w hw => h p p.2 hpT w hw)

/-- And conversely (glue-b3-unram's bridge): the two forms agree on finite Galois fields. -/
theorem galUnramifiedOutside_iff (L : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (T : Finset ℕ) :
    GalUnramifiedOutside L T ↔ ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p :=
  ⟨unramifiedAt_of_galUnramifiedOutside L T, fun h p hp hpT w hw =>
    inertia_le_of_unramifiedAt L p hp (h ⟨p, hp⟩ hpT) w hw⟩


/-! ## The Hom field: the core theorem (Minkowski + infinite Galois theory + the bridge)

N5 L544-563, with the Weil restriction `W₀ = Res_{K/ℚ} A` replaced by what the argument uses of
it: a free `ℤ`-module `M` of rank `r` (the geometric endomorphism lattice of `W₀`, i.e. the direct
sum of the Hom groups among the conjugates of `A`) with a `ℤ`-linear action of `G_ℚ` that is
continuous (every element has an open stabilizer: each geometric homomorphism is defined over a
number field) and on which every inertia group over a prime `p ∉ T` acts trivially. -/

section Core

variable {M : Type*} [AddCommGroup M]

/-- The `GL_r(ℤ)`-realization of the automorphisms of a free `ℤ`-module with a basis. -/
noncomputable def toGL {r : ℕ} (b : Module.Basis (Fin r) ℤ M) :
    (M ≃ₗ[ℤ] M) →* Matrix.GeneralLinearGroup (Fin r) ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ M).symm.toMonoidHom

theorem toGL_injective {r : ℕ} (b : Module.Basis (Fin r) ℤ M) :
    Function.Injective (toGL b) := by
  intro f g h
  have h1 := congrArg (fun u : Matrix.GeneralLinearGroup (Fin r) ℤ =>
    (u : Matrix (Fin r) (Fin r) ℤ)) h
  have h2 : (f : M →ₗ[ℤ] M) = g := (LinearMap.toMatrixAlgEquiv b).injective h1
  exact LinearEquiv.toLinearMap_injective h2

theorem toGL_eq_one_iff {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (f : M ≃ₗ[ℤ] M) :
    toGL b f = 1 ↔ f = 1 :=
  ⟨fun h => toGL_injective b (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

/-- An automorphism is the identity iff it fixes a basis. -/
theorem eq_one_iff_basis {ι : Type*} (b : Module.Basis ι ℤ M) (f : M ≃ₗ[ℤ] M) :
    f = 1 ↔ ∀ i, f (b i) = b i := by
  constructor
  · intro h i; rw [h]; rfl
  · intro h
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    simpa using h i

/-- **G4, the Hom field (core, proved).** Let `K ⊆ ℚ̄` be finite Galois, unramified outside `T`
(Galois form), and let `G_ℚ` act `ℤ`-linearly on a free `ℤ`-module `M` with basis indexed by
`Fin r`, continuously (open stabilizers), with every inertia group over every prime `p ∉ T`
acting trivially. Then there is a finite Galois `L ⊇ K` such that `G_L` acts trivially on `M`
(`L` defines every element of `M`), `[L:ℚ] ≤ [K:ℚ]·3^{r²}` (Minkowski), and `L` is unramified
outside `T`, in both the Galois form and glue-descent's ideal-theoretic form. -/
theorem homField_core (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ Module.finrank ℚ K * 3 ^ (r ^ 2) ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  classical
  let ρ' : Gal →* Matrix.GeneralLinearGroup (Fin r) ℤ := (toGL b).comp ρ
  have hker : ρ'.ker = ρ.ker := by
    ext σ
    simp only [MonoidHom.mem_ker]
    exact toGL_eq_one_iff b (ρ σ)
  -- the kernel is open
  have hset : (ρ.ker : Set Gal) = ⋂ i, {σ : Gal | ρ σ (b i) = b i} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    exact eq_one_iff_basis b (ρ σ)
  have hNopen : IsOpen (ρ.ker : Set Gal) := by
    rw [hset]; exact isOpen_iInter_of_finite fun i => hcont (b i)
  have hNclosed : IsClosed (ρ.ker : Set Gal) := Subgroup.isClosed_of_isOpen _ hNopen
  let NC : ClosedSubgroup Gal := { toSubgroup := ρ.ker, isClosed' := hNclosed }
  let E : IntermediateField ℚ Qbar := IntermediateField.fixedField NC.toSubgroup
  have hE : E.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField NC
  haveI hEfd : FiniteDimensional ℚ E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      show IsOpen (E.fixingSubgroup : Set Gal)
      rw [hE]; exact hNopen)
  haveI hEgal : IsGalois ℚ E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (by rw [hE]; exact ρ.normal_ker)
  -- `[E:ℚ] = |ρ(G_ℚ)| ≤ 3^{r²}`
  have hcardE : Module.finrank ℚ E = Nat.card ρ'.range := by
    rw [← IsGalois.card_aut_eq_finrank]
    have e1 := QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := ℚ)
      (K₁ := Qbar) E) (AlgEquiv.restrictNormalHom_surjective (E := Qbar))
    have e2 := QuotientGroup.quotientKerEquivRange ρ'
    have c1 : Nat.card (E ≃ₐ[ℚ] E) =
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) E).ker.index :=
      (Nat.card_congr e1.toEquiv).symm
    have c2 : Nat.card ρ'.range = ρ'.ker.index := (Nat.card_congr e2.toEquiv).symm
    rw [c1, c2, IntermediateField.restrictNormalHom_ker, hE, hker]
  haveI : Finite ρ'.range := by
    apply Nat.finite_of_card_ne_zero
    rw [← hcardE]; exact Module.finrank_pos.ne'
  have hE3 : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := by
    rw [hcardE]; exact GlueRepo.TorsionFree.card_le_three_pow ρ'.range
  -- `L = E ⊔ K`
  refine ⟨E ⊔ K, inferInstance, inferInstance, le_sup_right, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    have h1 : σ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hσ
    rw [hE] at h1
    exact h1
  · calc Module.finrank ℚ ↥(E ⊔ K) ≤ Module.finrank ℚ E * Module.finrank ℚ K :=
          IntermediateField.finrank_sup_le E K
      _ ≤ 3 ^ (r ^ 2) * Module.finrank ℚ K := Nat.mul_le_mul_right _ hE3
      _ = Module.finrank ℚ K * 3 ^ (r ^ 2) := Nat.mul_comm _ _
  · have hgal : GalUnramifiedOutside (E ⊔ K) T := by
      intro p hp hpT w hw s hs
      rw [IntermediateField.fixingSubgroup_sup]
      refine ⟨?_, hK p hp hpT w hw hs⟩
      rw [hE]
      exact hinert p hp hpT w hw s hs
    exact hgal
  · apply unramifiedAt_of_galUnramifiedOutside
    intro p hp hpT w hw s hs
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨?_, hK p hp hpT w hw hs⟩
    rw [hE]
    exact hinert p hp hpT w hw s hs

/-- **G4 with the manuscript's numbers.** If `[K:ℚ] ≤ F₀ = 324!` and `r ≤ 16F₀²` (N5 L547-548),
the Hom field has `[L:ℚ] ≤ D = F₀·3^{256F₀⁴}` (`ZInQ.heightD`). -/
theorem homField_le_heightD (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {r : ℕ} (hr : r ≤ 16 * ZInQ.heightF0 ^ 2) (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  obtain ⟨L, h1, h2, hKL, hdef, hdeg, hgal, hram⟩ := homField_core K b ρ hcont T hK hinert
  refine ⟨L, h1, h2, hKL, hdef, ?_, hgal, hram⟩
  exact hdeg.trans (GlueRepo.Numerics.a8_degree ZInQ.Compiler.Precision.heightD_eq hKF le_rfl hr)

end Core


/-! ## The lattice of the conjugates: rank, faithfulness, and the abelian-variety instantiation

The manuscript's `End(W₀_ℚ̄) = ⊕_{σ,τ} Hom(σA, τA)`: here the direct sum over ordered pairs of
`n` abelian varieties over `ℚ̄` (the conjugates of `A`, `n ≤ [K:ℚ] ≤ F₀`), as a product of
`PkgI3.AbVar.Hom` groups. -/

section Lattice

/-- **Rank of the lattice (glue, proved).** A product over ordered pairs `(i, j) ∈ n × n` of free
finite `ℤ`-modules of rank `≤ c` is free and finite of rank `≤ c·n²`. -/
theorem pi_rank_le {ι : Type*} [Fintype ι] {c : ℕ} (H : ι × ι → Type*) [∀ ij, AddCommGroup (H ij)]
    [∀ ij, Module.Free ℤ (H ij)] [∀ ij, Module.Finite ℤ (H ij)]
    (hH : ∀ ij, Module.finrank ℤ (H ij) ≤ c) :
    Module.finrank ℤ (∀ ij, H ij) ≤ c * Fintype.card ι ^ 2 := by
  rw [Module.finrank_pi_fintype]
  calc ∑ ij, Module.finrank ℤ (H ij) ≤ ∑ _ij : ι × ι, c :=
        Finset.sum_le_sum fun ij _ => hH ij
    _ = c * Fintype.card ι ^ 2 := by simp [Fintype.card_prod, sq, mul_comm]

/-- **Inertia acts trivially on the lattice (glue, proved; N5 L559-561).** If the lattice `M`
embeds equivariantly and injectively into a module `N` (in the application: `ℓ`-adic
realization, `Hom(σA, τA) → Hom_{ℤ_ℓ}(T_ℓ σA, T_ℓ τA)`, injective by Mumford §19 Thm 3, the leaf
`PkgI3.HomFreeFinite`), then every `s` acting trivially on `N` (in the application: inertia at
`p ∉ T`, by Néron–Ogg–Shafarevich, the leaf `PkgI2.NeronOggShafarevich`) acts trivially on `M`. -/
theorem trivial_of_faithful {G M N : Type*} [Group G] [AddCommGroup M] [AddCommGroup N]
    (ρ : G →* (M ≃ₗ[ℤ] M)) (τ : G →* (N ≃ₗ[ℤ] N)) (ι : M →+ N) (hι : Function.Injective ι)
    (heq : ∀ g m, ι (ρ g m) = τ g (ι m)) (s : G) (hs : τ s = 1) : ρ s = 1 := by
  apply LinearEquiv.ext
  intro m
  apply hι
  rw [heq, hs]
  rfl

/-- The `ℓ`-adic side: if `s` acts trivially on the Tate modules `T i`, it acts trivially on
`Hom_{ℤ_ℓ}(T i, T j)` by conjugation. -/
theorem conj_trivial {R : Type*} [CommRing R] {T₁ T₂ : Type*} [AddCommGroup T₁] [Module R T₁]
    [AddCommGroup T₂] [Module R T₂] (a₁ : T₁ ≃ₗ[R] T₁) (a₂ : T₂ ≃ₗ[R] T₂) (h₁ : a₁ = 1)
    (h₂ : a₂ = 1) (φ : T₁ →ₗ[R] T₂) :
    (a₂ : T₂ →ₗ[R] T₂) ∘ₗ φ ∘ₗ (a₁.symm : T₁ →ₗ[R] T₁) = φ := by
  subst h₁; subst h₂; rfl

open PkgI3 PkgI3.AbVar CategoryTheory MonObj

/-- The geometric Hom lattice of `n` abelian varieties over `ℚ̄`: `⊕_{(i,j)} Hom(A i, A j)`. -/
abbrev HomLattice {Idx : Type} (A : Idx → AbVar Qbar) : Type :=
  ∀ ij : Idx × Idx, AbVar.Hom (A ij.1) (A ij.2)

/-- **Mumford's bound on the lattice (from the leaf `HomFreeFinite`).** For abelian surfaces
`A i` over `ℚ̄`, the lattice `⊕ Hom(A i, A j)` is free and finite of rank `≤ 16n²`. -/
theorem homLattice_free (hHFF : HomFreeFinite) {Idx : Type} [Fintype Idx] (A : Idx → AbVar Qbar)
    (hdim : ∀ i, (A i).dim = 2) :
    Module.Free ℤ (HomLattice A) ∧ Module.Finite ℤ (HomLattice A) ∧
      Module.finrank ℤ (HomLattice A) ≤ 16 * Fintype.card Idx ^ 2 := by
  haveI : ∀ ij : Idx × Idx, Module.Free ℤ (AbVar.Hom (A ij.1) (A ij.2)) :=
    fun ij => (hHFF Qbar (A ij.1) (A ij.2)).1
  haveI : ∀ ij : Idx × Idx, Module.Finite ℤ (AbVar.Hom (A ij.1) (A ij.2)) :=
    fun ij => (hHFF Qbar (A ij.1) (A ij.2)).2.1
  refine ⟨inferInstance, inferInstance, pi_rank_le _ fun ij => ?_⟩
  have h := (hHFF Qbar (A ij.1) (A ij.2)).2.2.1
  rw [hdim, hdim] at h
  have h16 : ((Module.finrank ℤ (AbVar.Hom (A ij.1) (A ij.2)) : ℕ∞) : WithBot ℕ∞) ≤
      (((16 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    refine h.trans (le_of_eq ?_)
    rfl
  exact_mod_cast h16

/-- **G4 on the abelian-variety layer.** Let `K ⊆ ℚ̄` be finite Galois with `[K:ℚ] ≤ F₀`,
unramified outside `T`; let `A 0, …, A (n-1)` be abelian surfaces over `ℚ̄` (the conjugates of
the fibre object, indexed by a finite type of size `≤ F₀`, e.g. the embeddings `K → ℚ̄`), and let `G_ℚ` act `ℤ`-linearly on `⊕ Hom(A i, A j)` (the conjugation
action; its construction is the open part of G4) continuously and with every inertia group over
`p ∉ T` acting trivially. Then the Hom field `L ⊇ K` exists: finite Galois, `[L:ℚ] ≤ D`, every
element of the lattice is fixed by `G_L`, and `L` is unramified outside `T` (both forms).
Leaf used: `PkgI3.HomFreeFinite` (Mumford §19 Thm 3). -/
theorem homField_of_conjugates (hHFF : HomFreeFinite)
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {Idx : Type} [Fintype Idx] (hn : Fintype.card Idx ≤ ZInQ.heightF0) (A : Idx → AbVar Qbar)
    (hdim : ∀ i, (A i).dim = 2)
    (ρ : Gal →* (HomLattice A ≃ₗ[ℤ] HomLattice A))
    (hcont : ∀ m : HomLattice A, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  obtain ⟨hfree, hfin, hrank⟩ := homLattice_free hHFF A hdim
  have hr : Module.finrank ℤ (HomLattice A) ≤ 16 * ZInQ.heightF0 ^ 2 :=
    hrank.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2))
  exact homField_le_heightD K hKF hr (Module.finBasisOfFinrankEq ℤ (HomLattice A) rfl) ρ hcont T
    hK hinert

/-! ### The conjugation action, characterized

For `σ ∈ G_ℚ`, a conjugate of an abelian variety `X` over `ℚ̄` is an `X'` with a pullback square
`X' → X` over `Spec σ : Spec ℚ̄ → Spec ℚ̄` (the relation used by leaf-qm-fp's `IsBaseChangeOf`).
`ConjData` records the conjugates of a finite family (`A (σ·i)` is the `σ`-conjugate of `A i`),
and `IsConjAction D ρ` says that `ρ σ` sends `f : A i → A j` to its conjugate
`σf : A (σ·i) → A (σ·j)`, the morphism with `σf ∘ g_{σ,i} = g_{σ,j} ∘ f`. Such a `ρ` is unique
(`isConjAction_unique`): the action in `homField_of_conjugates` is then *the* conjugation action
of `G_ℚ` on the geometric Hom groups among the conjugates (the endomorphism lattice of the Weil
restriction), not an arbitrary one. Its existence (`ConjActionExists`) is open. -/

open AlgebraicGeometry

/-- `Spec σ : Spec ℚ̄ → Spec ℚ̄`. -/
noncomputable abbrev specGal (σ : Gal) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar))

/-- Conjugation data for a finite family of abelian varieties over `ℚ̄`: a permutation action of
`G_ℚ` on the indices and, for every `σ` and `i`, a pullback square exhibiting `A (σ·i)` as the
base change of `A i` along `Spec σ`. -/
structure ConjData (Idx : Type) where
  A : Idx → AbVar Qbar
  act : Gal → Equiv.Perm Idx
  g : ∀ (σ : Gal) (i : Idx), (A (act σ i)).X.left ⟶ (A i).X.left
  pb : ∀ (σ : Gal) (i : Idx),
    IsPullback (g σ i) (A (act σ i)).X.hom (A i).X.hom (specGal σ)

/-- `ρ` is the conjugation action for the data `D`. -/
def IsConjAction {Idx : Type} (D : ConjData Idx)
    (ρ : Gal → HomLattice D.A → HomLattice D.A) : Prop :=
  ∀ (σ : Gal) (f : HomLattice D.A) (i j : Idx),
    (ρ σ f (D.act σ i, D.act σ j)).hom.left ≫ D.g σ j = D.g σ i ≫ (f (i, j)).hom.left

/-- **The conjugation action is unique (glue, proved).** -/
theorem isConjAction_unique {Idx : Type} (D : ConjData Idx)
    {ρ ρ' : Gal → HomLattice D.A → HomLattice D.A}
    (h : IsConjAction D ρ) (h' : IsConjAction D ρ') : ρ = ρ' := by
  funext σ f
  funext ij
  obtain ⟨i', j'⟩ := ij
  obtain ⟨i, rfl⟩ := (D.act σ).surjective i'
  obtain ⟨j, rfl⟩ := (D.act σ).surjective j'
  apply AbVar.Hom.ext'
  apply CategoryTheory.Over.OverMorphism.ext
  apply (D.pb σ j).hom_ext
  · rw [h σ f i j, h' σ f i j]
  · rw [CategoryTheory.Over.w, CategoryTheory.Over.w]

/-- **Open glue target (the Weil-restriction step of G4).** The conjugates carry a `ℤ`-linear
action of `G_ℚ` on their Hom lattice that is the conjugation action. Proof sketch (STANDARD,
not formalized): the lift `σf` exists by the pullback property; it is a homomorphism because
the squares are compatible with the group laws (the base change of a group scheme along
`Spec σ` is a group scheme, and `g_{σ,i}` is a homomorphism over `Spec σ`); additivity and the
group law `ρ(στ) = ρ(σ)ρ(τ)` follow from the uniqueness of lifts (`isConjAction_unique`'s
argument) once the squares compose (`g_{στ,i} = g_{τ,σ⁻¹…}`-pasting, which needs the data to be
chosen coherently, e.g. from a model `A/K` over a number field). -/
def ConjActionExists {Idx : Type} (D : ConjData Idx) : Prop :=
  ∃ ρ : Gal →* (HomLattice D.A ≃ₗ[ℤ] HomLattice D.A), IsConjAction D (fun σ f => ρ σ f)


/-! ### The conjugates of a model over a number field: genuine `ConjData`

For `A/K` with `K ⊆ ℚ̄` a number field, the conjugates are the base changes `A_e = A ×_{K,e} ℚ̄`
along the embeddings `e : K → ℚ̄`; `G_ℚ` permutes the embeddings, and pullback pasting gives the
squares `A_{σ∘e} → A_e` over `Spec σ`. This constructs `ConjData` for the manuscript's family
(`[K:ℚ]` conjugates, `AlgHom.card`), so the open part of the Weil-restriction step is exactly
`ConjActionExists (conjData A)` and the two properties of the action used by G4 (continuity,
inertia). -/

/-- Base change of an abelian variety along a ring homomorphism `f : K → L` of fields
(as `PkgI3.AbVar.baseChange`, for an arbitrary embedding). -/
noncomputable def bcAlong {K L : Type} [Field K] [Field L] (A : AbVar K) (f : K →+* L) :
    AbVar L :=
  let F := CategoryTheory.Over.pullback (Spec.map (CommRingCat.ofHom f))
  letI : GrpObj (F.obj A.X) := Functor.grpObjObj
  haveI : IsProper (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : Smooth (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : GeometricallyIntegral (F.obj A.X).hom := by dsimp [F]; infer_instance
  { X := F.obj A.X }

variable (K : IntermediateField ℚ Qbar)

/-- `Spec e : Spec ℚ̄ → Spec K` for an embedding `e : K → ℚ̄`. -/
noncomputable abbrev specEmb (e : K →ₐ[ℚ] Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (e : K →+* Qbar))

/-- `G_ℚ` permutes the embeddings `K → ℚ̄`: `σ · e = σ ∘ e`. -/
noncomputable def embAct (σ : Gal) : Equiv.Perm (K →ₐ[ℚ] Qbar) where
  toFun e := (σ : Qbar →ₐ[ℚ] Qbar).comp e
  invFun e := ((σ⁻¹ : Gal) : Qbar →ₐ[ℚ] Qbar).comp e
  left_inv e := by
    ext x
    show (σ⁻¹ * σ) (e x) = e x
    rw [inv_mul_cancel]; rfl
  right_inv e := by
    ext x
    show (σ * σ⁻¹) (e x) = e x
    rw [mul_inv_cancel]; rfl

theorem specEmb_act (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    specEmb K (embAct K σ e) = specGal σ ≫ specEmb K e := by
  rw [specEmb, specEmb, specGal, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The square `A_{σ∘e} → A_e` over `Spec σ`. -/
noncomputable def conjMap (A : AbVar K) (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    (bcAlong A ((embAct K σ e : K →ₐ[ℚ] Qbar) : K →+* Qbar)).X.left ⟶
      (bcAlong A (e : K →+* Qbar)).X.left :=
  (IsPullback.of_hasPullback A.X.hom (specEmb K e)).lift
    (Limits.pullback.fst A.X.hom (specEmb K (embAct K σ e)))
    (Limits.pullback.snd A.X.hom (specEmb K (embAct K σ e)) ≫ specGal σ)
    ((Limits.pullback.condition).trans
      ((congrArg (fun φ => Limits.pullback.snd A.X.hom (specEmb K (embAct K σ e)) ≫ φ)
        (specEmb_act K σ e)).trans (Category.assoc _ _ _).symm))

theorem conjMap_isPullback (A : AbVar K) (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    IsPullback (conjMap K A σ e)
      (bcAlong A ((embAct K σ e : K →ₐ[ℚ] Qbar) : K →+* Qbar)).X.hom
      (bcAlong A (e : K →+* Qbar)).X.hom (specGal σ) := by
  have s : IsPullback (Limits.pullback.fst A.X.hom (specEmb K (embAct K σ e)))
      (Limits.pullback.snd A.X.hom (specEmb K (embAct K σ e))) A.X.hom
      (specGal σ ≫ specEmb K e) := by
    rw [← specEmb_act]; exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right' s (IsPullback.of_hasPullback A.X.hom (specEmb K e))

/-- **The conjugation data of a model `A/K`** (constructed, no hypothesis): the `[K:ℚ]`
conjugates `A_e`, permuted by `G_ℚ`, with their pullback squares over `Spec σ`. -/
noncomputable def conjData (A : AbVar K) : ConjData (K →ₐ[ℚ] Qbar) where
  A e := bcAlong A (e : K →+* Qbar)
  act σ := embAct K σ
  g σ e := conjMap K A σ e
  pb σ e := conjMap_isPullback K A σ e

/-- There are `[K:ℚ]` conjugates. -/
theorem card_conjugates [FiniteDimensional ℚ K] :
    Fintype.card (K →ₐ[ℚ] Qbar) = Module.finrank ℚ K :=
  AlgHom.card ℚ K Qbar


/-- **G4 for a model `A/K` (the manuscript's statement, N5 L544-563).** Let `K ⊆ ℚ̄` be finite
Galois with `[K:ℚ] ≤ F₀`, unramified outside `T` (G2), and `A/K` an abelian surface whose
conjugates `A_e` are surfaces. Let `ρ` be the conjugation action of `G_ℚ` on
`⊕_{e,e'} Hom(A_e, A_{e'})` (`IsConjAction (conjData K A) ρ`; unique by `isConjAction_unique`),
continuous, with trivial inertia outside `T`. Then the Hom field `L ⊇ K` exists: finite Galois,
`[L:ℚ] ≤ D`, every geometric homomorphism among the conjugates is fixed by `G_L`, `L`
unramified outside `T` (both forms). Leaf: `PkgI3.HomFreeFinite`. -/
theorem homField_of_model (hHFF : HomFreeFinite) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (ρ : Gal →* (HomLattice (conjData K A).A ≃ₗ[ℤ] HomLattice (conjData K A).A))
    (_hρ : IsConjAction (conjData K A) (fun σ f => ρ σ f))
    (hcont : ∀ m : HomLattice (conjData K A).A, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_conjugates hHFF K hKF (by rw [card_conjugates]; exact hKF) (conjData K A).A hdim ρ
    hcont T hK hinert


end Lattice

/-! ## What G7 receives: the Hom field feeds `GlueDescent.B3Q.b3_degree_le_QM`

`b3_degree_le_QM` needs a finite Galois `L` with `[L:ℚ] ≤ D`, unramified outside `T = ramSet S u`
(ideal-theoretic form), and the cocycle `ε` of the scalar descent data inflated from `Gal(L/ℚ)`.
The first three are G4's output above; the last is G7's own instantiation (the descent data
`μ_σ` are elements of the lattice, so a field defining the lattice defines `ε`), kept here as the
hypothesis `hdesc`. -/

section Feed

/-- **G4 → G7.** The Hom field of `homField_le_heightD`, with `T = ramSet S u`, is a valid input
of `GlueDescent.B3Q.b3_degree_le_QM`: the scalar-descent output (`χ`, `β`, `L' ⊇ L` Galois with
`[L':ℚ] ≤ Q_R·M_S(u)`) follows. -/
theorem b3_of_homField (hHasse : GlueDescent.B2Q.LeafHasse)
    (hTwo : GlueDescent.B2Q.LeafLocalTwo) (hSq : GlueDescent.B2Q.LeafSqrtCrit)
    (hUnr : GlueDescent.B2Q.LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ) {M : Type*} [AddCommGroup M]
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {r : ℕ} (hr : r ≤ 16 * ZInQ.heightF0 ^ 2) (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (hK : GalUnramifiedOutside K (GlueDescent.ramSet S u))
    (hinert : ∀ p : ℕ, p.Prime → p ∉ GlueDescent.ramSet S u → ∀ w : ValuationSubring Qbar,
      LiesOver w p → ∀ s ∈ inertiaGQ w, ρ s = 1)
    (hdesc : ∀ L : IntermediateField ℚ Qbar, (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) →
      ∃ ε : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → ℂˣ, GlueDescent.B2.IsSignCocycle ε ∧
        GlueDescent.B2Q.InflatedFrom L ε ∧ ε 1 1 = 1)
    (η : GlueDescent.B2Q.GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (L : IntermediateField ℚ Qbar) (ε : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → ℂˣ)
      (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GlueDescent.B2Q.GQ → ℂˣ)
      (L' : IntermediateField ℚ Qbar),
      Module.finrank ℚ L ≤ ZInQ.heightD ∧ K ≤ L ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = GlueDescent.B2Q.galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u := by
  obtain ⟨L, hfd, hgal, hKL, hdef, hdeg, -, hram⟩ :=
    homField_le_heightD K hKF hr b ρ hcont (GlueDescent.ramSet S u) hK hinert
  obtain ⟨ε, hε, hinf, h11⟩ := hdesc L hdef
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', -, hdeg'⟩ :=
    GlueDescent.B3Q.b3_degree_le_QM hHasse hTwo hSq hUnr S hS R hRD hRS hR12 u L hdeg ε hε hinf
      h11 hram η hη hηl
  exact ⟨L, ε, N, hN, χ, β, L', hdeg, hKL, hβl, hβs, hβe, hle, hfd', hgal', hdeg'⟩

end Feed

end G4WeilRes

#print axioms G4WeilRes.unramifiedAt_of_inertia_le
#print axioms G4WeilRes.galUnramifiedOutside_iff
#print axioms G4WeilRes.homField_core
#print axioms G4WeilRes.homField_le_heightD
#print axioms G4WeilRes.homField_of_conjugates
#print axioms G4WeilRes.b3_of_homField
#print axioms G4WeilRes.isConjAction_unique
#print axioms G4WeilRes.conjData
#print axioms G4WeilRes.homField_of_model
