import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8Reduction

/-!
# Theorem 5.3, Lane RC32 round 5: lifting the decomposition group to `Gal(ℚ̄_r/ℚ_r)`

The third conjunct of `LocalGaloisDecomposition` (`CommonCoordinate8Reduction.lean`): along an
embedding `ι : ℚ̄ → ℚ̄_r`, every `g ∈ G_ℚ` that preserves the valuation ring of `w ∘ ι` is the
restriction of some `σ ∈ Gal(ℚ̄_r/ℚ_r)` (Neukirch, *Algebraic Number Theory*, II.9.6). The route
avoids completions of number fields:

* `galRes ι σ`: `σ ∈ Gal(ℚ̄_r/ℚ_r)` restricted to `ι(ℚ̄)`, the algebraic part (normal over `ℚ`),
  read back in `G_ℚ`; `ι ∘ galRes ι σ = σ ∘ ι` (`galRes_spec`); a continuous group homomorphism
  (`galResHom`, `continuous_galResHom`), so its range is closed (`Gal(ℚ̄_r/ℚ_r)` is compact);
* `fixed_of_mem_range`: if `g` preserves `w ∘ ι`-integrality, it fixes every `x ∈ ℚ̄` with
  `ι x ∈ ℚ_r` — `ℚ` is dense in `ℚ_r`, and `g` is an isometry for `w ∘ ι` fixing `ℚ`;
* `mem_range_galResHom`: hence `g` fixes the fixed field of the range, so it lies in the range
  (the infinite Galois correspondence for the closed range, Mathlib's
  `InfiniteGalois.fixingSubgroup_fixedField`);
* `exists_lift_of_integral_iff`: the lift `σ` with `σ ∘ ι = ι ∘ g`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain Topology Filter
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.AddressGenuine (Zbar)
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary (primeIdealQ)
open scoped WithZero

variable {r : ℕ} {hr : r.Prime}

instance charZero_Qr : CharZero (Qr r hr) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (Qr r hr)).injective

/-! ## Restriction to the algebraic part -/

section Restrict

variable (ι : Qbar →ₐ[ℚ] Qrbar r hr)

instance normal_fieldRange : Normal ℚ ι.fieldRange :=
  Normal.of_algEquiv ι.equivFieldRange

/-- **The restriction of `σ ∈ Gal(ℚ̄_r/ℚ_r)` to `ι(ℚ̄)`**, read in `G_ℚ` (definition). -/
def galRes (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) : GalQ :=
  ι.equivFieldRange.trans
    (((σ.restrictScalars ℚ).restrictNormal ι.fieldRange).trans ι.equivFieldRange.symm)

theorem coe_equivFieldRange (x : Qbar) :
    ((ι.equivFieldRange x : ι.fieldRange) : Qrbar r hr) = ι x :=
  AlgHom.equivFieldRange_apply_coe ι x

/-- `ι ∘ galRes ι σ = σ ∘ ι` (PROVED). -/
theorem galRes_spec (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) (x : Qbar) :
    ι (galRes ι σ x) = σ (ι x) := by
  have h1 : ∀ z : ι.fieldRange, ι (ι.equivFieldRange.symm z) = z := fun z => by
    rw [← coe_equivFieldRange, AlgEquiv.apply_symm_apply]
  change ι (ι.equivFieldRange.symm
    (((σ.restrictScalars ℚ).restrictNormal ι.fieldRange) (ι.equivFieldRange x))) = _
  rw [h1]
  have h2 := AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) ι.fieldRange
    (ι.equivFieldRange x)
  rw [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
    coe_equivFieldRange] at h2
  exact h2

/-- `galRes ι` as a group homomorphism (PROVED). -/
def galResHom : (Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) →* GalQ where
  toFun := galRes ι
  map_one' := AlgEquiv.ext fun x => by
    have hinj : Function.Injective ι := ι.injective
    apply hinj
    rw [galRes_spec]
    rfl
  map_mul' σ τ := AlgEquiv.ext fun x => by
    have hinj : Function.Injective ι := ι.injective
    apply hinj
    rw [AlgEquiv.mul_apply, galRes_spec, galRes_spec, galRes_spec]
    rfl

theorem galResHom_apply (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) :
    galResHom ι σ = galRes ι σ := rfl

/-- **`galRes ι` is continuous** for the Krull topologies (PROVED): the fixing group of a finite
`F ⊆ ℚ̄` contains the image of the fixing group of the finite extension `ℚ_r(ι(F))`. -/
theorem continuous_galResHom : Continuous (galResHom ι) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨F, hF, hFU⟩ := hU
  have hFG : F.FG := IntermediateField.fg_of_fg_toSubalgebra _
    (Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.mp hF))
  obtain ⟨s, hs⟩ := hFG
  let V : IntermediateField (Qr r hr) (Qrbar r hr) :=
    IntermediateField.adjoin (Qr r hr) ((fun t => ι t) '' (s : Set Qbar))
  have hVfin : FiniteDimensional (Qr r hr) V := by
    have : Finite ((fun t => ι t) '' (s : Set Qbar)) := (s.finite_toSet.image _).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x _ =>
      Algebra.IsIntegral.isIntegral (R := Qr r hr) x
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (V.fixingSubgroup_isOpen.mem_nhds V.fixingSubgroup.one_mem) ?_
  intro σ hσ
  apply hFU
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  have hgen : ∀ t ∈ (s : Set Qbar), galRes ι σ t = t := fun t ht => by
    have hinj : Function.Injective ι := ι.injective
    apply hinj
    rw [galRes_spec]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _
      (IntermediateField.subset_adjoin _ _ ⟨t, ht, rfl⟩)
  intro x hx
  rw [← hs] at hx
  have hle : IntermediateField.adjoin ℚ (s : Set Qbar) ≤
      IntermediateField.fixedField (Subgroup.zpowers (galRes ι σ)) := by
    rw [IntermediateField.adjoin_le_iff]
    intro t ht
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : galRes ι σ ∈ MulAction.stabilizer GalQ t := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact hgen t ht
    have hf' : f ∈ MulAction.stabilizer GalQ t := (Subgroup.zpowers_le.mpr hst) hf
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hf'
    exact hf'
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) _ (Subgroup.mem_zpowers _)

/-- The range of `galRes ι` is closed (PROVED: compact image in a Hausdorff group). -/
theorem isClosed_range_galResHom : IsClosed (Set.range (galResHom ι)) :=
  (isCompact_range (continuous_galResHom ι)).isClosed

/-- The range of `galRes ι` as a closed subgroup of `G_ℚ`. -/
def galResRange : ClosedSubgroup GalQ where
  toSubgroup := (galResHom ι).range
  isClosed' := by
    change IsClosed ((galResHom ι).range : Set GalQ)
    rw [MonoidHom.coe_range]
    exact isClosed_range_galResHom ι

/-- **An element of `G_ℚ` fixing everything that `Gal(ℚ̄_r/ℚ_r)` fixes is a restriction**
(PROVED: the infinite Galois correspondence for the closed range). -/
theorem mem_range_galResHom (g : GalQ)
    (hfix : ∀ x : Qbar, (∀ σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr, σ (ι x) = ι x) → g x = x) :
    g ∈ (galResHom ι).range := by
  have hcorr := InfiniteGalois.fixingSubgroup_fixedField (galResRange ι)
  have hmem : g ∈ (IntermediateField.fixedField (galResRange ι).toSubgroup).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply hfix
    intro σ
    rw [← galRes_spec]
    congr 1
    exact (IntermediateField.mem_fixedField_iff _ _).mp hx _ ⟨σ, rfl⟩
  rw [hcorr] at hmem
  exact hmem

end Restrict

/-! ## The density argument -/

section Density

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {w : Valuation (Qrbar r hr) Γ}

/-- Strict form of the integrality comparison (PROVED). -/
theorem lt_one_iff_of_integral_iff (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hiso : ∀ z : Qbar, w (ι (g z)) ≤ 1 ↔ w (ι z) ≤ 1) (z : Qbar) :
    w (ι (g z)) < 1 ↔ w (ι z) < 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : ι z ≠ 0 := (map_ne_zero ι).mpr hz
  have hgz : ι (g z) ≠ 0 := (map_ne_zero ι).mpr ((map_ne_zero g).mpr hz)
  have h := hiso z⁻¹
  simp only [map_inv₀] at h
  rw [← not_le, ← not_le, ← inv_le_one₀ ((w.pos_iff).mpr hgz),
    ← inv_le_one₀ ((w.pos_iff).mpr hz'), h]

/-- Scaled form (PROVED): `w(ι(g z)) < w(c)` iff `w(ι z) < w(c)` for `c ∈ ℚ^×`. -/
theorem lt_iff_of_integral_iff (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hiso : ∀ z : Qbar, w (ι (g z)) ≤ 1 ↔ w (ι z) ≤ 1) (z : Qbar) {c : ℚ} (hc : c ≠ 0) :
    w (ι (g z)) < w (ι (c : Qbar)) ↔ w (ι z) < w (ι (c : Qbar)) := by
  have hc' : ι (c : Qbar) ≠ 0 := by
    rw [map_ratCast]; exact_mod_cast hc
  have hpos : 0 < w (ι (c : Qbar)) := (w.pos_iff).mpr hc'
  have h := lt_one_iff_of_integral_iff ι g hiso (z / (c : Qbar))
  simp only [map_div₀, map_ratCast g] at h
  rwa [div_lt_one₀ hpos, div_lt_one₀ hpos] at h

/-- **Density** (PROVED): every element of `ℚ_r` is approximated by rationals to any precision
`w(c)`, `c ∈ ℚ^×`. -/
theorem exists_rat_approx (hw : ExtendsVr w) (a : Qr r hr) {c : ℚ} (hc : c ≠ 0) :
    ∃ q : ℚ, w (algebraMap (Qr r hr) (Qrbar r hr) (algebraMap ℚ (Qr r hr) q - a)) <
      w (algebraMap (Qr r hr) (Qrbar r hr) (algebraMap ℚ (Qr r hr) c)) := by
  let v : Valuation (Qr r hr) ℤᵐ⁰ := Valued.v
  have hc' : algebraMap ℚ (Qr r hr) c ≠ 0 := (map_ne_zero _).mpr hc
  let S : Set (Qr r hr) := {b | v (b - a) < v (algebraMap ℚ (Qr r hr) c)}
  have hS : IsOpen S := by
    have hball := Valued.isOpen_ball (Qr r hr) (v.restrict (algebraMap ℚ (Qr r hr) c))
    have : S = (fun b => b - a) ⁻¹' {x | v.restrict x < v.restrict (algebraMap ℚ (Qr r hr) c)} := by
      ext b
      simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Valuation.restrict_lt_iff]
    rw [this]
    exact hball.preimage (continuous_sub_right a)
  have hne : S.Nonempty := ⟨a, by
    simp only [S, Set.mem_ofPred_eq, sub_self, map_zero]
    exact (v.pos_iff).mpr hc'⟩
  obtain ⟨q, hq⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 ℚ) (K := ℚ)
    (v := primeIdealQ r hr)).exists_mem_open hS hne
  refine ⟨q, ?_⟩
  have := (Valuation.IsEquiv.lt_iff_lt hw).mpr hq
  simpa using this

/-- **The decomposition group fixes the algebraic part of `ℚ_r`** (PROVED): if `g` preserves
`w ∘ ι`-integrality and `ι x ∈ ℚ_r`, then `g x = x`. -/
theorem fixed_of_mem_range (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hiso : ∀ z : Qbar, w (ι (g z)) ≤ 1 ↔ w (ι z) ≤ 1) (x : Qbar) (a : Qr r hr)
    (ha : algebraMap (Qr r hr) (Qrbar r hr) a = ι x) : g x = x := by
  by_contra hne
  set y := g x - x with hy
  have hy0 : y ≠ 0 := sub_ne_zero.mpr hne
  have hyalg : IsAlgebraic ℤ y⁻¹ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Qbar).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨n, hn0, hnint⟩ := IsAlgebraic.exists_integral_multiple hyalg
  have h1 := le_one_of_mem_Zbar hw ι ⟨n • y⁻¹, hnint⟩
  have hιy : ι y ≠ 0 := (map_ne_zero ι).mpr hy0
  have hwy : 0 < w (ι y) := (w.pos_iff).mpr hιy
  have hn : w (ι ((n : ℚ) : Qbar)) ≤ w (ι y) := by
    simp only [zsmul_eq_mul, map_mul, map_inv₀, map_intCast] at h1
    rw [map_ratCast, Rat.cast_intCast]
    rwa [mul_inv_le_iff₀ hwy, one_mul] at h1
  set c : ℚ := n * r with hcdef
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hn0) hr0
  have hwr : w (ι ((r : ℚ) : Qbar)) < 1 := by
    rw [map_ratCast, Rat.cast_natCast]
    have := (intCast_lt_one_iff hw (r : ℤ)).mpr dvd_rfl
    exact_mod_cast this
  have hwn : 0 < w (ι ((n : ℚ) : Qbar)) := by
    refine (w.pos_iff).mpr ?_
    rw [map_ratCast]; exact_mod_cast hn0
  have hcy : w (ι (c : Qbar)) < w (ι y) := by
    rw [hcdef, Rat.cast_mul, map_mul, map_mul]
    exact lt_of_lt_of_le (mul_lt_of_lt_one_right hwn hwr) hn
  obtain ⟨q, hq⟩ := exists_rat_approx hw a hc
  set z := x - (q : Qbar) with hz
  have hzq : w (ι z) < w (ι (c : Qbar)) := by
    have e1 : algebraMap (Qr r hr) (Qrbar r hr) (algebraMap ℚ (Qr r hr) q - a) = -ι z := by
      rw [map_sub, ha, hz, map_sub, ← IsScalarTower.algebraMap_apply, map_ratCast]
      simp
    have e2 : algebraMap (Qr r hr) (Qrbar r hr) (algebraMap ℚ (Qr r hr) c) = ι (c : Qbar) := by
      rw [← IsScalarTower.algebraMap_apply, eq_ratCast, map_ratCast]
    rw [e1, e2, Valuation.map_neg] at hq
    exact hq
  have hgz : w (ι (g z)) < w (ι (c : Qbar)) := (lt_iff_of_integral_iff ι g hiso z hc).mpr hzq
  have hyz : ι y = ι (g z) - ι z := by
    rw [hy, hz, map_sub g, map_ratCast g]
    rw [map_sub, map_sub, map_sub]
    ring
  have : w (ι y) < w (ι y) := by
    calc w (ι y) = w (ι (g z) - ι z) := by rw [hyz]
      _ ≤ max (w (ι (g z))) (w (ι z)) := w.map_sub _ _
      _ < w (ι (c : Qbar)) := max_lt hgz hzq
      _ < w (ι y) := hcy
  exact lt_irrefl _ this

/-- **The lift of an integrality-preserving element of `G_ℚ`** (PROVED): if `g` preserves
`w ∘ ι`-integrality, there is `σ ∈ Gal(ℚ̄_r/ℚ_r)` with `σ ∘ ι = ι ∘ g`. -/
theorem exists_lift_of_integral_iff (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hiso : ∀ z : Qbar, w (ι (g z)) ≤ 1 ↔ w (ι z) ≤ 1) :
    ∃ σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr, ∀ x : Qbar, σ (ι x) = ι (g x) := by
  have hmem := mem_range_galResHom ι g fun x hx => by
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := Qr r hr) (ι x)).mpr hx
    exact fixed_of_mem_range hw ι g hiso x a ha
  obtain ⟨σ, hσ⟩ := hmem
  refine ⟨σ, fun x => ?_⟩
  rw [← hσ, galResHom_apply, galRes_spec]

end Density

end ZInQ.Manuscript.RC.Wiring
