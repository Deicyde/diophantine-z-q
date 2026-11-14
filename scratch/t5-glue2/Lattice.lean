import ZInQKernel.Contrib.TYZGenus.ShimuraModFn
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# t5-glue2, part 2: `IdeleLatticeScale` from the idelic description of ring classes

Verbatim copies (from `scratch/t5-glue/parts/CM.lean`, `Heeg.lean`, `LatHat.lean`) of the adelic
objects `AfK`, `latHat`, `finPart`, `icl`, `sInvLat`, of the glue Prop `IdeleLatticeScale`, and of
the lemmas used (`K ∩ 𝔞̂ = 𝔞`); then the new reduction (§3).
-/

noncomputable section

set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace T5Glue2

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-! ## §1. Verbatim copies (t5-glue) -/

/-- The finite adeles `𝔸_{K,f}` of `K = ℚ(√−m)`. -/
abbrev AfK (m : ℕ) [NeZero m] := FiniteAdeleRing (𝓞 (QNeg m)) (QNeg m)

/-- `𝔞̂ ⊂ 𝔸_{K,f}`: the closure of (the image of) a subset `𝔞 ⊂ K`; for a lattice `𝔞`,
`𝔞̂ = 𝔞 ⊗ ℤ̂`. -/
def latHat (m : ℕ) [NeZero m] (𝔞 : Set (QNeg m)) : Set (AfK m) :=
  closure (algebraMap (QNeg m) (AfK m) '' 𝔞)

/-- The finite component `s_f ∈ 𝔸_{K,f}` of an idele `s` of `K`. -/
def finPart {m : ℕ} [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : AfK m :=
  (s : AdeleRing (𝓞 (QNeg m)) (QNeg m)).2

/-- The idele class of an idele. -/
def icl {m : ℕ} [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    IdeleClassGroup (𝓞 (QNeg m)) (QNeg m) :=
  QuotientGroup.mk s

/-- `s⁻¹𝔞 = K ∩ s_f⁻¹𝔞̂ = {x ∈ K : s_f x ∈ 𝔞̂}` (Shimura 1971, §5.2). -/
def sInvLat (m : ℕ) [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (𝔞 : Set (QNeg m)) :
    Set (QNeg m) :=
  {x | finPart s * algebraMap (QNeg m) (AfK m) x ∈ latHat m 𝔞}


section Lemmas

variable {m : ℕ} [NeZero m]

theorem kappa_rat (q : ℚ) : kappa m (algebraMap ℚ (QNeg m) q) = (q : ℂ) := by
  rw [← kappaAlg_apply, AlgHom.commutes]; simp

theorem kappa_injective : Function.Injective (kappa m) := by
  intro a b h
  rw [← kappaAlg_apply, ← kappaAlg_apply] at h
  exact (kappaAlg m).toRingHom.injective h

theorem kappa_add (a b : QNeg m) : kappa m (a + b) = kappa m a + kappa m b := by
  simp only [← kappaAlg_apply, map_add]

theorem kappa_intCast_mul (n : ℤ) (a : QNeg m) : kappa m (n * a) = n * kappa m a := by
  simp only [← kappaAlg_apply, map_mul, map_intCast]

/-- `τ_Q ∈ κ(K)`. -/
theorem exists_kappa_tau {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D) :
    ∃ t : QNeg m, kappa m t = Q.tau := by
  have hA : (Q.A : ℂ) ≠ 0 := heegner_A_ne_zero Q
  set c₀ : ℝ := if m % 4 = 3 then (f : ℝ) else 2 * f with hc₀
  have hc : ∃ q : ℚ, (q : ℝ) = c₀ := by
    by_cases h : m % 4 = 3
    · exact ⟨f, by simp [hc₀, h]⟩
    · exact ⟨2 * f, by simp [hc₀, h]⟩
  obtain ⟨q, hq⟩ := hc
  refine ⟨⟨-(Q.B : ℚ) / (2 * Q.A), q / (2 * Q.A)⟩, ?_⟩
  have hs : Real.sqrt (-(D : ℝ)) = c₀ * Real.sqrt m := by rw [hD]; exact sqrt_neg_discOf m f
  simp only [kappa, HeegnerForm.tau, cmPoint, hs]
  push_cast
  rw [← hq]
  field_simp
  push_cast
  ring

theorem lat_subset_range {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D) :
    (Q.lat : Set ℂ) ⊆ Set.range (kappa m) := by
  obtain ⟨t, ht⟩ := exists_kappa_tau (m := m) hD Q
  intro z hz
  rw [SetLike.mem_coe, HeegnerForm.lat, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, rfl⟩ := hz
  refine ⟨(a : QNeg m) * 1 + (b : QNeg m) * t, ?_⟩
  rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht]
  simp [kappa, zsmul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem preimage_lat_eq_span {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D)
    {t : QNeg m} (ht : kappa m t = Q.tau) :
    kappa m ⁻¹' (Q.lat : Set ℂ) = (Submodule.span ℤ {(1 : QNeg m), t} : Set (QNeg m)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, HeegnerForm.lat, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, kappa_injective ?_⟩
    simp only [zsmul_eq_mul] at hab ⊢
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht, ← hab]
    simp [kappa, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    simp only [zsmul_eq_mul]
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht]
    simp [kappa, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

end Lemmas

/-- **GLUE IDELE-SCALE (the lattice computation, shimura-modfn §1).** Under the hypotheses of
`IdeleLatticeHeegner`: `κ(s⁻¹𝔞) = c'·⟨1, τ_{Q'}⟩` and `κ(s⁻¹𝔞_N) = c'·⟨1/N, τ_{Q'}⟩` for one
`c' ≠ 0`, where `𝔞 = κ⁻¹⟨1, τ_Q⟩`, `𝔞_N = κ⁻¹⟨1/N, τ_Q⟩`. (`s = k·s_J·w`, `k ∈ Kˣ`, `w ∈ Ô^×ℂˣ`;
both lattices are `κ(O)`-stable (`⟨1, τ_Q⟩` has multiplier ring `O`, `Q` being primitive of
discriminant `disc O`; `⟨1/N, τ_Q⟩ = N⁻¹⟨1, Nτ_Q⟩` comes from `[A/N, B, CN]`, possibly imprimitive,
with multiplier ring `⊇ O`; kernel `kappa_mul_mem_lat`, `kappa_mul_mem_latN_gen`), so `w` fixes their
closures and `s⁻¹(𝔞, 𝔞_N) = k⁻¹(J ∩ O)⁻¹(𝔞, 𝔞_N)`; localizing `κ(J ∩ O)·L' = c·L` (at `p ∤ f`,
`(J ∩ O)_p = J_p = s_{J,p}𝒪_p`; at `p ∣ f`, `(J ∩ O)_p = O_p`) gives `κ((J ∩ O)⁻¹𝔞) = c⁻¹⟨1, τ_{Q'}⟩`,
and likewise for `𝔞_N` with the same `c`. Needs the identity
`ker(ringClassIdeleQuotient) = Kˣ·Ô^×·ℂˣ`, which Tau Ceti states through ray classes only.) -/
def IdeleLatticeScale : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
  ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)),
    ringClassIdeleQuotient (conductorOrder (QNeg m) f) (icl s) =
      (conductorOrder (QNeg m) f).picClass J →
  ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
    idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
    idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
    ∃ c' : ℂ, c' ≠ 0 ∧
      kappa m '' sInvLat m s (kappa m ⁻¹' (Q.lat : Set ℂ)) = c' • (Q'.lat : Set ℂ) ∧
      kappa m '' sInvLat m s (kappa m ⁻¹' (Q.latN : Set ℂ)) = c' • (Q'.latN : Set ℂ)


section Aux

variable {m : ℕ} [NeZero m]

theorem latHat_eq_closure (M : Submodule ℤ (QNeg m)) :
    latHat m (M : Set (QNeg m)) =
      ((M.toAddSubgroup.map (algebraMap (QNeg m) (AfK m)).toAddMonoidHom).topologicalClosure :
        Set (AfK m)) := by
  rw [AddSubgroup.topologicalClosure_coe, latHat]
  rfl

theorem latHat_sub_mem (M : Submodule ℤ (QNeg m)) {x y : AfK m}
    (hx : x ∈ latHat m (M : Set (QNeg m))) (hy : y ∈ latHat m (M : Set (QNeg m))) :
    x - y ∈ latHat m (M : Set (QNeg m)) := by
  rw [latHat_eq_closure] at hx hy ⊢
  exact AddSubgroup.sub_mem _ hx hy

theorem latHat_add_mem (M : Submodule ℤ (QNeg m)) {x y : AfK m}
    (hx : x ∈ latHat m (M : Set (QNeg m))) (hy : y ∈ latHat m (M : Set (QNeg m))) :
    x + y ∈ latHat m (M : Set (QNeg m)) := by
  rw [latHat_eq_closure] at hx hy ⊢
  exact AddSubgroup.add_mem _ hx hy

theorem mem_latHat_of_mem {𝔞 : Set (QNeg m)} {x : QNeg m} (hx : x ∈ 𝔞) :
    algebraMap (QNeg m) (AfK m) x ∈ latHat m 𝔞 :=
  subset_closure ⟨x, hx, rfl⟩

theorem latHat_mono {𝔞 𝔟 : Set (QNeg m)} (h : 𝔞 ⊆ 𝔟) : latHat m 𝔞 ⊆ latHat m 𝔟 :=
  closure_mono (Set.image_mono h)

/-- `κ⁻¹(L)` for a `ℤ`-submodule `L ⊂ ℂ`, as a submodule of `K`. -/
def kappaComap (L : Submodule ℤ ℂ) : Submodule ℤ (QNeg m) := L.comap (kappaLin m)

theorem coe_kappaComap (L : Submodule ℤ ℂ) :
    ((kappaComap (m := m) L : Submodule ℤ (QNeg m)) : Set (QNeg m)) = kappa m ⁻¹' (L : Set ℂ) := by
  ext x; simp [kappaComap, kappaLin_apply]

theorem kappa_sub (a b : QNeg m) : kappa m (a - b) = kappa m a - kappa m b := by
  simp only [← kappaAlg_apply, map_sub]

end Aux

section LatHatProof

variable {m : ℕ} [NeZero m]

/-- Adeles `y` with `n⁻¹y` integral at every finite place (`n·𝒪̂`). -/
def intAd (m : ℕ) [NeZero m] (n : ℕ) : Set (AfK m) :=
  {y | ∀ v : HeightOneSpectrum (𝓞 (QNeg m)),
    (algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y) v ∈ v.adicCompletionIntegers (QNeg m)}

theorem isClosed_intAd (n : ℕ) : IsClosed (intAd m n) := by
  unfold intAd
  rw [Set.ofPred_forall]
  refine isClosed_iInter fun v => ?_
  have hmul : Continuous fun y : AfK m => algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y :=
    continuous_const.mul continuous_id
  have hc : Continuous fun y : AfK m =>
      (algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y) v :=
    (RestrictedProduct.continuous_eval v).comp hmul
  have hcl : IsClosed ((v.adicCompletionIntegers (QNeg m) : Set (v.adicCompletion (QNeg m)))) :=
    Valued.isClosed_integer _
  exact hcl.preimage hc

theorem algebraMap_mem_intAd_iff (n : ℕ) (z : QNeg m) :
    algebraMap (QNeg m) (AfK m) z ∈ intAd m n ↔
      (n : QNeg m)⁻¹ * z ∈ Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m)) := by
  unfold intAd
  simp only [Set.mem_setOf_eq, ← map_mul]
  constructor
  · intro h
    have := HeightOneSpectrum.mem_integers_of_valuation_le_one (QNeg m) ((n : QNeg m)⁻¹ * z)
      (fun v => by
        have h1 := h v
        rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
        exact h1)
    exact this
  · rintro ⟨r, hr⟩ v
    rw [FiniteAdeleRing.algebraMap_apply, ← hr]
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

/-- **`K ∩ 𝔞̂ = 𝔞`** for `𝔞 = ℤa + ℤb` with `n𝓞_K ⊆ 𝔞` and `d·a, d·b ∈ 𝓞_K`. -/
theorem latHat_inter_of_sandwich (a b : QNeg m) (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (hn𝔞 : ∀ y : 𝓞 (QNeg m), (n : QNeg m) * y ∈ Submodule.span ℤ {a, b})
    (hda : (d : QNeg m) * a ∈ Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m)))
    (hdb : (d : QNeg m) * b ∈ Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m))) :
    {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈
        latHat m (Submodule.span ℤ {a, b} : Set (QNeg m))} = Submodule.span ℤ {a, b} := by
  set 𝔞 := Submodule.span ℤ {a, b} with h𝔞
  have hn0 : (n : QNeg m) ≠ 0 := by exact_mod_cast hn.ne'
  set M : ℕ := n * d with hM
  have hM0 : 0 < M := Nat.mul_pos hn hd
  -- finitely many coset representatives `i a + j b`
  let S : Finset (QNeg m) :=
    ((Finset.range M) ×ˢ (Finset.range M)).image fun p => (p.1 : QNeg m) * a + (p.2 : QNeg m) * b
  let U : Set (AfK m) := ⋃ s ∈ S, (fun y => y - algebraMap (QNeg m) (AfK m) s) ⁻¹' intAd m n
  have hUc : IsClosed U := by
    refine (S.finite_toSet).isClosed_biUnion fun s _ => ?_
    exact (isClosed_intAd n).preimage (continuous_id.sub continuous_const)
  -- integrality of `d·(p'a + q'b)`
  have hdint : ∀ p q : ℤ, (d : QNeg m) * ((p : QNeg m) * a + (q : QNeg m) * b) ∈
      Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m)) := by
    intro p q
    obtain ⟨ra, hra⟩ := hda
    obtain ⟨rb, hrb⟩ := hdb
    refine ⟨(p : 𝓞 (QNeg m)) * ra + (q : 𝓞 (QNeg m)) * rb, ?_⟩
    rw [map_add, map_mul, map_mul, hra, hrb, map_intCast, map_intCast]; ring
  have hsub : algebraMap (QNeg m) (AfK m) '' (𝔞 : Set (QNeg m)) ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, h𝔞, Submodule.mem_span_pair] at hx
    obtain ⟨p, q, rfl⟩ := hx
    have hMi : (0 : ℤ) < M := by exact_mod_cast hM0
    set i := p % (M : ℤ)
    set j := q % (M : ℤ)
    have hp : p = i + M * (p / M) := by have := Int.emod_add_ediv_mul p M; linarith
    have hq : q = j + M * (q / M) := by have := Int.emod_add_ediv_mul q M; linarith
    have hi0 : 0 ≤ i := Int.emod_nonneg p (by omega)
    have hiM : i < M := Int.emod_lt_of_pos p hMi
    have hj0 : 0 ≤ j := Int.emod_nonneg q (by omega)
    have hjM : j < M := Int.emod_lt_of_pos q hMi
    refine Set.mem_iUnion₂.2 ⟨(i.toNat : QNeg m) * a + (j.toNat : QNeg m) * b, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨(i.toNat, j.toNat), Finset.mem_product.2
        ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩, rfl⟩
    · show algebraMap (QNeg m) (AfK m) (p • a + q • b) -
        algebraMap (QNeg m) (AfK m) ((i.toNat : QNeg m) * a + (j.toNat : QNeg m) * b) ∈ intAd m n
      rw [← map_sub, algebraMap_mem_intAd_iff]
      have hit : ((i.toNat : ℕ) : QNeg m) = (i : QNeg m) := by
        have : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi0
        exact_mod_cast this
      have hjt : ((j.toNat : ℕ) : QNeg m) = (j : QNeg m) := by
        have : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
        exact_mod_cast this
      have e : (n : QNeg m)⁻¹ * (p • a + q • b - ((i.toNat : QNeg m) * a + (j.toNat : QNeg m) * b)) =
          (d : QNeg m) * (((p / M : ℤ) : QNeg m) * a + ((q / M : ℤ) : QNeg m) * b) := by
        rw [hit, hjt, zsmul_eq_mul, zsmul_eq_mul]
        conv_lhs => rw [hp, hq]
        push_cast [hM]
        field_simp
        ring
      rw [e]
      exact hdint _ _
  have hcl : latHat m (𝔞 : Set (QNeg m)) ⊆ U := closure_minimal hsub hUc
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (hcl hx)
    simp only [Set.mem_preimage] at hxs
    rw [← map_sub, algebraMap_mem_intAd_iff] at hxs
    obtain ⟨r, hr⟩ := hxs
    obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.1 hs
    have hr' : (r : QNeg m) = (n : QNeg m)⁻¹ * (x - ((i : QNeg m) * a + (j : QNeg m) * b)) := hr
    have hxe : x = ((i : QNeg m) * a + (j : QNeg m) * b) + (n : QNeg m) * r := by
      rw [hr']; field_simp; ring
    rw [SetLike.mem_coe, hxe]
    refine 𝔞.add_mem ?_ (hn𝔞 r)
    have h1 : (i : QNeg m) * a = (i : ℤ) • a := by rw [zsmul_eq_mul]; push_cast; rfl
    have h2 : (j : QNeg m) * b = (j : ℤ) • b := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [h1, h2]
    exact 𝔞.add_mem (𝔞.smul_mem _ (Submodule.subset_span (by simp)))
      (𝔞.smul_mem _ (Submodule.subset_span (by simp)))
  · intro hx
    exact mem_latHat_of_mem hx

end LatHatProof

section Heegner

variable {m : ℕ} [NeZero m]

/-- `c₀ = f` (`m ≡ 3 mod 4`) or `2f`: `√(−disc O) = c₀√m`. -/
def cz (m f : ℕ) : ℕ := if m % 4 = 3 then f else 2 * f

/-- `τ_Q = (−B + c₀√−m)/(2A) ∈ K`. -/
def tK {N : ℕ} {D : ℤ} (m : ℕ) (Q : HeegnerForm N D) (c : ℕ) : QNeg m :=
  ⟨-(Q.B : ℚ) / (2 * Q.A), (c : ℚ) / (2 * Q.A)⟩

theorem kappa_tK {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D) :
    kappa m (tK m Q (cz m f)) = Q.tau := by
  have hA : (Q.A : ℂ) ≠ 0 := heegner_A_ne_zero Q
  have hs : Real.sqrt (-(D : ℝ)) = (cz m f : ℝ) * Real.sqrt m := by
    rw [hD, sqrt_neg_discOf m f]; unfold cz; split_ifs <;> push_cast <;> ring
  simp only [kappa, tK, HeegnerForm.tau, cmPoint, hs]
  push_cast
  field_simp

theorem cz_pos {f : ℕ} [NeZero f] : 0 < cz m f := by
  have := Nat.pos_of_ne_zero (NeZero.ne f)
  unfold cz; split_ifs <;> omega

theorem natCast_mul_mk (d : ℕ) (z : QNeg m) : (d : QNeg m) * z = ⟨d * z.re, d * z.im⟩ := by
  ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_natCast,
    QuadraticAlgebra.im_natCast]

theorem zsmul_mk (X : ℤ) (z : QNeg m) : X • z = ⟨X * z.re, X * z.im⟩ := by
  ext <;> simp [zsmul_eq_mul]

/-- `2c₀·𝓞_K ⊆ ℤ + ℤτ_Q` (kernel `two_coords`). -/
theorem two_cz_mul_mem (hsq : Squarefree m) {f : ℕ} [NeZero f] {D : ℤ} (hD : D = discOf m f)
    {N : ℕ} (Q : HeegnerForm N D) (y : 𝓞 (QNeg m)) :
    ((2 * cz m f : ℕ) : QNeg m) * y ∈ Submodule.span ℤ {(1 : QNeg m), tK m Q (cz m f)} := by
  have hA : (0 : ℤ) < Q.A := Q.A_pos
  have hAq : (Q.A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  obtain ⟨α, β, Nn, hα, hβ, -⟩ := two_coords hsq y
  rw [Submodule.mem_span_pair]
  refine ⟨cz m f * α + β * Q.B, 2 * Q.A * β, ?_⟩
  have hre : (y : QNeg m).re = α / 2 := by linarith
  have him : (y : QNeg m).im = β / 2 := by linarith
  rw [natCast_mul_mk, zsmul_mk, zsmul_mk]
  ext
  · simp only [QuadraticAlgebra.re_add, tK, QuadraticAlgebra.re_one, hre]
    push_cast
    field_simp
    ring
  · simp only [QuadraticAlgebra.im_add, tK, QuadraticAlgebra.im_one, him]
    push_cast
    field_simp
    ring

/-- **`K ∩ 𝔞̂ = 𝔞` for `𝔞 = κ⁻¹⟨1, τ_Q⟩`** (`n = 2c₀`, `d = 2A`). -/
theorem latHat_inter_heegner (hsq : Squarefree m) {f : ℕ} [NeZero f] {D : ℤ} (hD : D = discOf m f)
    {N : ℕ} (Q : HeegnerForm N D) :
    {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈ latHat m (kappa m ⁻¹' (Q.lat : Set ℂ))} =
      kappa m ⁻¹' (Q.lat : Set ℂ) := by
  have ht := kappa_tK (m := m) hD Q
  rw [preimage_lat_eq_span hD Q ht]
  have hA : (0 : ℤ) < Q.A := Q.A_pos
  have hAq : (Q.A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hAt : ((Q.A.toNat : ℕ) : ℚ) = Q.A := by
    have : ((Q.A.toNat : ℕ) : ℤ) = Q.A := Int.toNat_of_nonneg hA.le
    exact_mod_cast this
  refine latHat_inter_of_sandwich 1 (tK m Q (cz m f)) (2 * cz m f) (2 * Q.A.toNat)
    (by have := cz_pos (m := m) (f := f); omega) (by omega) ?_ ?_ ?_
  · exact two_cz_mul_mem hsq hD Q
  · refine ⟨((2 * Q.A.toNat : ℕ) : 𝓞 (QNeg m)), ?_⟩
    rw [map_natCast, mul_one]
  · refine ⟨(-Q.B : 𝓞 (QNeg m)) + (cz m f : 𝓞 (QNeg m)) * sqrtNeg m, ?_⟩
    have hsq' : algebraMap (𝓞 (QNeg m)) (QNeg m) (sqrtNeg m) = QuadraticAlgebra.omega := coe_sqrtNeg
    rw [map_add, map_mul, map_neg, map_intCast, map_natCast, hsq', natCast_mul_mk (2 * Q.A.toNat)]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK]
      push_cast [hAt]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK]
      push_cast [hAt]
      field_simp
      ring

end Heegner

-- NEW

end T5Glue2
