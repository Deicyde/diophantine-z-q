import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.TYZGenus.ShimuraFricke
import ZInQKernel.Contrib.TYZGenus.ShimuraTheta
import ZInQKernel.Contrib.TYZGenus.ShimuraThetaDup
import ZInQKernel.Contrib.TYZGenus.ShimuraZn

/-!
# hx-used: the eta route (helper of `ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean`)

Task hx-used (2026-11-15). Copied from `scratch/hx-used/EtaRoute.lean`. Report: `docs/research/hx-used.md`.

The two level-32 instances of `Shimura.ShimuraReciprocityModFn` that the consumers of `hX` use
(`g = X0.xC`, `g = X0.yC`) follow from the printed main theorem of CM `T5Glue.ShimuraMainCM` and one explicit
identity `XEtaWeierstrass` (x0-32's eta quotient `x` as a weight-0 ratio of Weierstrass values of the lattice
`⟨1/16, τ⟩` at torsion points), with no canonical-model input:
`srAt_x`, `srAt_y : XEtaWeierstrass → ShimuraMainCM → ShimuraReciprocityModFnAt 32 _`.

Method: for a Heegner pair `(Q, Q')` and an idele `s` with `σ = [s, K]`, the kernel's `IdeleLatticeScale`
(gt-ringclass) gives `s⁻¹⟨1, τ_Q⟩ = c'⟨1, τ_{Q'}⟩`, `s⁻¹⟨1/32, τ_Q⟩ = c'⟨1/32, τ_{Q'}⟩`; from these,
`s⁻¹⟨1/M, τ_Q⟩ = c'⟨1/M, τ_{Q'}⟩` for `M = 16, 2` (`sInv_latM`) and the images of the torsion points `1/32`, `τ/8`,
`τ/2` are pinned down modulo the lattices (`exists_v1`, `exists_vt`); `ShimuraMainCM` at the lattices `⟨1/16, τ_Q⟩`
and `⟨1/2, τ_Q⟩` then moves the `℘`-ratio of `XEtaWeierstrass` and of its Fricke transform to the corresponding
ratio at `τ_{Q'}` (`transport16`, `transport2`); `y` is a polynomial in `x` and `x∘W₃₂` (`yC_formula`, from the
proved Fricke relation).

No `sorry`, no `axiom`.
-/

noncomputable section

set_option maxRecDepth 20000

namespace X0EtaRoute

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise
open T5Glue

variable {m : ℕ} [NeZero m]

/-- `⟨1/M, τ_Q⟩ ⊂ ℂ`. -/
def latM {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) (M : ℕ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {1 / (M : ℂ), Q.tau}

/-- `1/M ∈ K`. -/
def invK (m M : ℕ) [NeZero m] : QNeg m := algebraMap ℚ (QNeg m) (1 / (M : ℚ))

theorem kappa_invK (M : ℕ) : kappa m (invK m M) = 1 / (M : ℂ) := by
  rw [invK, kappa_rat]; push_cast; rfl

theorem preimage_latM_eq_span {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D)
    (M : ℕ) {t : QNeg m} (ht : kappa m t = Q.tau) :
    kappa m ⁻¹' (latM Q M : Set ℂ) = (Submodule.span ℤ {invK m M, t} : Set (QNeg m)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, latM, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, kappa_injective ?_⟩
    simp only [zsmul_eq_mul] at hab ⊢
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht, kappa_invK, ← hab]
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    simp only [zsmul_eq_mul]
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht, kappa_invK]

theorem latM_subset_range {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D)
    (M : ℕ) : (latM Q M : Set ℂ) ⊆ Set.range (kappa m) := by
  obtain ⟨t, ht⟩ := exists_kappa_tau (m := m) hD Q
  intro z hz
  rw [SetLike.mem_coe, latM, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, rfl⟩ := hz
  refine ⟨(a : QNeg m) * invK m M + (b : QNeg m) * t, ?_⟩
  rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht, kappa_invK]
  simp [zsmul_eq_mul]

/-- **`K ∩ 𝔟̂ = 𝔟` for `𝔟 = κ⁻¹⟨1/M, τ_Q⟩`** (`n = 2c₀`, `d = 2AM`), as `latHat_inter_heegner`. -/
theorem latHat_inter_latM (hsq : Squarefree m) {f : ℕ} [NeZero f] {D : ℤ} (hD : D = discOf m f)
    {N : ℕ} (Q : HeegnerForm N D) {M : ℕ} (hM : 0 < M) :
    {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈ latHat m (kappa m ⁻¹' (latM Q M : Set ℂ))} =
      kappa m ⁻¹' (latM Q M : Set ℂ) := by
  have ht := kappa_tK (m := m) hD Q
  rw [preimage_latM_eq_span hD Q M ht]
  have hA : (0 : ℤ) < Q.A := Q.A_pos
  have hAq : (Q.A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hAt : ((Q.A.toNat : ℕ) : ℚ) = Q.A := by
    have : ((Q.A.toNat : ℕ) : ℤ) = Q.A := Int.toNat_of_nonneg hA.le
    exact_mod_cast this
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  refine latHat_inter_of_sandwich (invK m M) (tK m Q (cz m f)) (2 * cz m f) (2 * Q.A.toNat * M)
    (by have := cz_pos (m := m) (f := f); omega) (Nat.mul_pos (Nat.mul_pos two_pos (by omega)) hM) ?_ ?_ ?_
  · intro y
    have h1 := two_cz_mul_mem hsq hD Q y
    refine (Submodule.span_le.mpr ?_) h1
    rintro z (rfl | rfl)
    · rw [SetLike.mem_coe, Submodule.mem_span_pair]
      refine ⟨M, 0, ?_⟩
      have hMK : (M : QNeg m) ≠ 0 := by exact_mod_cast hM.ne'
      simp only [invK, zero_smul, add_zero, zsmul_eq_mul, Int.cast_natCast, map_div₀, map_one,
        map_natCast]
      field_simp
    · exact Submodule.subset_span (by simp)
  · refine ⟨((2 * Q.A.toNat : ℕ) : 𝓞 (QNeg m)), ?_⟩
    have hMK : (M : QNeg m) ≠ 0 := by exact_mod_cast hM.ne'
    rw [map_natCast]
    simp only [invK, map_div₀, map_one, map_natCast]
    push_cast
    field_simp
  · refine ⟨((M : ℕ) : 𝓞 (QNeg m)) * ((-Q.B : 𝓞 (QNeg m)) + (cz m f : 𝓞 (QNeg m)) * sqrtNeg m), ?_⟩
    have hsq' : algebraMap (𝓞 (QNeg m)) (QNeg m) (sqrtNeg m) = QuadraticAlgebra.omega := coe_sqrtNeg
    rw [map_mul, map_add, map_mul, map_neg, map_intCast, map_natCast, map_natCast, hsq',
      natCast_mul_mk (2 * Q.A.toNat * M)]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK, QuadraticAlgebra.im_add,
        QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast]
      push_cast [hAt]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast]
      push_cast [hAt]
      field_simp
      ring

/-! ## Part 2. Integer and lattice helpers -/

theorem dvd_pow_eight_sub_one {p : ℤ} (hp : Odd p) : (32 : ℤ) ∣ p ^ 8 - 1 := by
  obtain ⟨k, rfl⟩ := hp
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self k
  refine ⟨r * (2 * k ^ 2 + 2 * k + 1) * (8 * k ^ 4 + 16 * k ^ 3 + 12 * k ^ 2 + 4 * k + 1), ?_⟩
  linear_combination 16 * (2 * k ^ 2 + 2 * k + 1) * (8 * k ^ 4 + 16 * k ^ 3 + 12 * k ^ 2 + 4 * k + 1) * hr

/-- The period pair `(1/M, τ)`. -/
def ppM (M : ℕ) (hM : M ≠ 0) (τ : UpperHalfPlane) : PeriodPair :=
  ⟨1 / (M : ℂ), τ, by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him : t * τ.im = 0 := by
      have := congrArg Complex.im h
      simpa [Complex.real_smul] using this
    have ht : t = 0 := by
      rcases mul_eq_zero.1 him with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt τ.im_pos)
    subst ht
    simp only [zero_smul, add_zero, Complex.real_smul] at h
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
    refine ⟨?_, rfl⟩
    have h2 : (s : ℂ) = 0 := by
      have := congrArg (fun z => z * (M : ℂ)) h
      simpa [hM'] using this
    exact_mod_cast h2⟩

theorem ppM_lattice {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) (M : ℕ) (hM : M ≠ 0) :
    (ppM M hM Q.tauH).lattice = latM Q M := rfl

theorem latM_one {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : latM Q 1 = Q.lat := by
  simp [latM, HeegnerForm.lat]

theorem latM_N {D : ℤ} (Q : HeegnerForm 32 D) : latM Q 32 = Q.latN := rfl

theorem notMem_of_coeffs (P : PeriodPair) (α β : ℚ) (h : α.den ≠ 1 ∨ β.den ≠ 1) {z : ℂ}
    (hz : z = α * P.ω₁ + β * P.ω₂) : z ∉ P.lattice := by
  rw [hz, PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice]
  tauto

theorem mem_smul_span_pair {c α β z : ℂ} :
    z ∈ c • ((Submodule.span ℤ {α, β} : Submodule ℤ ℂ) : Set ℂ) ↔
      ∃ a b : ℤ, z = c * (a * α + b * β) := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_pair] at hy
    obtain ⟨a, b, rfl⟩ := hy
    exact ⟨a, b, by simp [zsmul_eq_mul, smul_eq_mul]⟩
  · rintro ⟨a, b, rfl⟩
    refine ⟨a * α + b * β, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_pair]
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩

theorem latHat_zsmul_mem (M : Submodule ℤ (QNeg m)) (n : ℤ) {x : AfK m}
    (hx : x ∈ latHat m (M : Set (QNeg m))) : n • x ∈ latHat m (M : Set (QNeg m)) := by
  rw [latHat_eq_closure] at hx ⊢
  exact AddSubgroup.zsmul_mem _ hx n

/-- `κ⁻¹(L)` as a submodule; its coercion is the preimage. -/
abbrev KL (m : ℕ) [NeZero m] (L : Submodule ℤ ℂ) : Submodule ℤ (QNeg m) := kappaComap (m := m) L

theorem coe_KL (L : Submodule ℤ ℂ) : ((KL m L : Submodule ℤ (QNeg m)) : Set (QNeg m)) =
    kappa m ⁻¹' (L : Set ℂ) := coe_kappaComap L

theorem mem_sInv_iff {s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)} {X : Set (QNeg m)} {c : ℂ}
    {L : Set ℂ} (h : kappa m '' sInvLat m s X = c • L) {x : QNeg m} :
    x ∈ sInvLat m s X ↔ kappa m x ∈ c • L := by
  constructor
  · intro hx; rw [← h]; exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← kappa_injective hyx]

theorem mem_sInvLat_iff {s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)} {X : Set (QNeg m)} {x : QNeg m} :
    x ∈ sInvLat m s X ↔ finPart s * algebraMap (QNeg m) (AfK m) x ∈ latHat m X := Iff.rfl

/-! ## Part 3. The idelic transport at level 32 -/

section Transport

variable {f : ℕ} [NeZero f] {D : ℤ}

/-- The data of one transport: `s⁻¹⟨1, τ_Q⟩ = c'⟨1, τ_{Q'}⟩`, `s⁻¹⟨1/32, τ_Q⟩ = c'⟨1/32, τ_{Q'}⟩`
(the conclusion of `T5Glue.IdeleLatticeScale` at `N = 32`). -/
structure TData (m : ℕ) [NeZero m] (f : ℕ) (D : ℤ) where
  hsq : Squarefree m
  hD : D = discOf m f
  Q : HeegnerForm 32 D
  Q' : HeegnerForm 32 D
  s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)
  c : ℂ
  hc : c ≠ 0
  hlat : kappa m '' sInvLat m s (kappa m ⁻¹' (Q.lat : Set ℂ)) = c • (Q'.lat : Set ℂ)
  hlatN : kappa m '' sInvLat m s (kappa m ⁻¹' (Q.latN : Set ℂ)) = c • (Q'.latN : Set ℂ)

variable (T : TData m f D)

/-- `u₁ = 1/32 ∈ K`. -/
abbrev u1 (m : ℕ) [NeZero m] : QNeg m := invK m 32

theorem kappa_u1 : kappa m (u1 m) = 1 / 32 := by
  rw [u1, kappa_invK]; norm_num

theorem lat_le_latM (Q : HeegnerForm 32 D) {M : ℕ} (hM : 0 < M) : Q.lat ≤ latM Q M := by
  rw [HeegnerForm.lat, latM, Submodule.span_le]
  rintro z (rfl | rfl)
  · rw [SetLike.mem_coe, Submodule.mem_span_pair]
    refine ⟨M, 0, ?_⟩
    have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    simp [zsmul_eq_mul]; field_simp
  · exact Submodule.subset_span (by simp)

theorem latM_le_latN (Q : HeegnerForm 32 D) {M d : ℕ} (hdM : d * M = 32) : latM Q M ≤ Q.latN := by
  rw [latM, HeegnerForm.latN, Submodule.span_le]
  rintro z (rfl | rfl)
  · rw [SetLike.mem_coe, Submodule.mem_span_pair]
    refine ⟨d, 0, ?_⟩
    have hM : (M : ℂ) ≠ 0 := by
      have : M ≠ 0 := by rintro rfl; simp at hdM
      exact_mod_cast this
    have h32 : ((32 : ℕ) : ℂ) = (d : ℂ) * M := by rw [← hdM]; push_cast; ring
    simp only [zsmul_eq_mul, Int.cast_natCast, zero_smul, add_zero, h32]
    have hd : (d : ℂ) ≠ 0 := by
      have : d ≠ 0 := by rintro rfl; simp at hdM
      exact_mod_cast this
    field_simp
  · exact Submodule.subset_span (by simp)

/-- `𝔞̂ ⊆ 𝔟̂` for `κ⁻¹⟨1,τ⟩ ⊆ κ⁻¹L`. -/
theorem latHat_lat_sub {L : Submodule ℤ ℂ} (Q : HeegnerForm 32 D) (h : Q.lat ≤ L) :
    latHat m (kappa m ⁻¹' (Q.lat : Set ℂ)) ⊆ latHat m (kappa m ⁻¹' (L : Set ℂ)) :=
  latHat_mono (Set.preimage_mono h)

/-- **`s⁻¹(1/32)`**: some `v₁ ∈ K` with `s_f v₁ − 1/32 ∈ 𝔞̂` and `κ(v₁) = c'(p₁/32 + q₁τ')`, `p₁` odd. -/
theorem exists_v1 : ∃ (v : QNeg m) (p q : ℤ),
    finPart T.s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) (u1 m) ∈
      latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) ∧
    kappa m v = T.c * (p * (1 / 32) + q * T.Q'.tau) ∧ Odd p := by
  obtain ⟨v, hv⟩ := strongApprox m T.hsq f D T.hD 32 T.Q T.s (u1 m)
  have hlatN := T.hlatN
  -- `v ∈ s⁻¹𝔞_N`
  have hvN : v ∈ sInvLat m T.s (kappa m ⁻¹' (T.Q.latN : Set ℂ)) := by
    rw [mem_sInvLat_iff, ← coe_KL]
    have h1 : finPart T.s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) (u1 m) ∈
        latHat m ((KL m T.Q.latN : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
      rw [coe_KL]; exact latHat_lat_sub T.Q (lat_le_latN T.Q (by norm_num)) hv
    have h2 : algebraMap (QNeg m) (AfK m) (u1 m) ∈
        latHat m ((KL m T.Q.latN : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
      apply mem_latHat_of_mem
      rw [coe_KL, Set.mem_preimage, kappa_u1]
      exact Submodule.subset_span (by simp)
    have := latHat_add_mem _ h1 h2
    simpa using this
  rw [mem_sInv_iff hlatN, HeegnerForm.latN, mem_smul_span_pair] at hvN
  obtain ⟨p, q, hpq⟩ := hvN
  refine ⟨v, p, q, hv, by rw [hpq]; push_cast; ring, ?_⟩
  -- `p` odd
  by_contra hp
  rw [Int.not_odd_iff_even] at hp
  obtain ⟨r, rfl⟩ := hp
  have h16 : (16 : ℤ) • v ∈ sInvLat m T.s (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    rw [mem_sInv_iff T.hlat, HeegnerForm.lat, mem_smul_span_pair]
    refine ⟨r, 16 * q, ?_⟩
    rw [zsmul_eq_mul, kappa_intCast_mul, hpq]; push_cast; ring
  rw [mem_sInvLat_iff, ← coe_KL] at h16
  have h3 := latHat_sub_mem _ h16 (latHat_zsmul_mem _ 16 (by rw [coe_KL]; exact hv))
  rw [map_zsmul, smul_sub, mul_smul_comm, sub_sub_cancel, ← map_zsmul, coe_KL] at h3
  have h4 := (Set.ext_iff.1 (latHatInter m T.hsq f D T.hD 32 T.Q) _).1 h3
  rw [Set.mem_preimage, zsmul_eq_mul, kappa_intCast_mul, kappa_u1] at h4
  apply notMem_of_coeffs (pp T.Q.tauH) (1 / 2) 0 (Or.inl (by norm_num)) (z := ((16 : ℤ) : ℂ) * (1 / 32))
    (by simp [pp]; norm_num)
  exact h4

/-- `j/32 ∈ ⟨1/M, τ_Q⟩` forces `d ∣ j` (`dM = 32`). -/
theorem dvd_of_mem_latM (Q : HeegnerForm 32 D) {M d : ℕ} (hdM : d * M = 32) {j : ℤ}
    (h : (j : ℂ) * (1 / 32) ∈ latM Q M) : (d : ℤ) ∣ j := by
  have hM0 : M ≠ 0 := by rintro rfl; simp at hdM
  have hd0 : d ≠ 0 := by rintro rfl; simp at hdM
  rw [← ppM_lattice Q M hM0] at h
  have h' : ((j * M / 32 : ℚ) : ℂ) * (ppM M hM0 Q.tauH).ω₁ + ((0 : ℚ) : ℂ) * (ppM M hM0 Q.tauH).ω₂ ∈
      (ppM M hM0 Q.tauH).lattice := by
    convert h using 1
    simp only [ppM]
    have : (M : ℂ) ≠ 0 := by exact_mod_cast hM0
    push_cast
    field_simp
    ring
  rw [PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice] at h'
  obtain ⟨h1, -⟩ := h'
  have h2 : ((j * M / 32 : ℚ)) = ((j * M / 32 : ℚ).num : ℚ) := by
    exact (Rat.coe_int_num_of_den_eq_one h1).symm
  set k := (j * M / 32 : ℚ).num
  have h3 : (j : ℚ) * M = 32 * k := by
    have : (32 : ℚ) ≠ 0 := by norm_num
    field_simp at h2; linarith
  have h4 : j * M = 32 * k := by exact_mod_cast h3
  refine ⟨k, ?_⟩
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM0
  have h5 : (32 : ℤ) = d * M := by exact_mod_cast hdM.symm
  rw [h5] at h4
  have : j * M = (d * k) * M := by linarith
  exact mul_right_cancel₀ hM' this

/-- **`s⁻¹⟨1/M, τ_Q⟩ = c'⟨1/M, τ_{Q'}⟩`** for `dM = 32`. -/
theorem sInv_latM {M d : ℕ} (hdM : d * M = 32) :
    kappa m '' sInvLat m T.s (kappa m ⁻¹' (latM T.Q M : Set ℂ)) = T.c • (latM T.Q' M : Set ℂ) := by
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hdM)
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hdM)
  have hinvM : 1 / (M : ℂ) = d / 32 := by
    have : (32 : ℂ) = d * M := by exact_mod_cast hdM.symm
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [this]; field_simp
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have h32 : (32 : ℂ) = d * M := by exact_mod_cast hdM.symm
  obtain ⟨v1, p1, q1, hv1, hk1, hp1⟩ := exists_v1 T
  set alg := algebraMap (QNeg m) (AfK m)
  have hsub : latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) ⊆ latHat m (kappa m ⁻¹' (latM T.Q M : Set ℂ)) :=
    latHat_lat_sub T.Q (lat_le_latM T.Q hM0)
  -- `x − j v₁ ∈ s⁻¹𝔞` gives `s_f x − j u₁ ∈ 𝔞̂`
  have key : ∀ (x : QNeg m) (j : ℤ), x - j • v1 ∈ sInvLat m T.s (kappa m ⁻¹' (T.Q.lat : Set ℂ)) →
      finPart T.s * alg x - j • alg (u1 m) ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    intro x j hx
    rw [mem_sInvLat_iff, ← (coe_KL (m := m))] at hx
    have h2 := latHat_zsmul_mem _ j (by rw [(coe_KL (m := m))]; exact hv1)
    have := latHat_add_mem _ hx h2
    rw [(coe_KL (m := m))] at this
    convert this using 1
    rw [map_sub, map_zsmul, mul_sub, smul_sub, mul_smul_comm]; abel
  have hp8 := dvd_pow_eight_sub_one hp1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- `x ∈ s⁻¹𝔞_N`
    have hxN : x ∈ sInvLat m T.s (kappa m ⁻¹' (T.Q.latN : Set ℂ)) :=
      latHat_mono (Set.preimage_mono (latM_le_latN T.Q hdM)) hx
    rw [mem_sInv_iff T.hlatN, HeegnerForm.latN, mem_smul_span_pair] at hxN
    obtain ⟨p, q, hpq⟩ := hxN
    set j : ℤ := p * p1 ^ 7 with hj
    obtain ⟨k8, hk8⟩ := hp8
    have hxj : x - j • v1 ∈ sInvLat m T.s (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
      rw [mem_sInv_iff T.hlat, HeegnerForm.lat, mem_smul_span_pair]
      refine ⟨-p * k8, q - j * q1, ?_⟩
      rw [kappa_sub, zsmul_eq_mul, kappa_intCast_mul, hpq, hk1, hj]
      have : (p1 : ℂ) ^ 8 = 1 + 32 * k8 := by
        have := congrArg (fun z : ℤ => (z : ℂ)) hk8; push_cast at this; linear_combination this
      push_cast
      linear_combination (-T.c * p / 32) * this
    have h1 := hsub (key x j hxj)
    have h2 : alg (j • u1 m) ∈ latHat m (kappa m ⁻¹' (latM T.Q M : Set ℂ)) := by
      rw [← (coe_KL (m := m))] at h1 hx ⊢
      have := latHat_sub_mem _ hx h1
      rw [sub_sub_cancel] at this
      rwa [map_zsmul]
    have h3 := (Set.ext_iff.1 (latHat_inter_latM T.hsq T.hD T.Q hM0) _).1 h2
    rw [Set.mem_preimage, zsmul_eq_mul, kappa_intCast_mul, kappa_u1] at h3
    obtain ⟨e, he⟩ := dvd_of_mem_latM T.Q hdM h3
    -- `d ∣ p`
    have hdp : (d : ℤ) ∣ p := by
      have h32d : (d : ℤ) ∣ 32 := ⟨M, by exact_mod_cast hdM.symm⟩
      have : p = j * p1 - p * (p1 ^ 8 - 1) := by rw [hj]; ring
      rw [this, hk8]
      exact dvd_sub (dvd_mul_of_dvd_left ⟨e, he⟩ _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h32d _) _)
    obtain ⟨a, ha⟩ := hdp
    rw [latM, mem_smul_span_pair]
    refine ⟨a, q, ?_⟩
    rw [hpq, ha]; push_cast; rw [h32]; field_simp
  · intro hy
    rw [latM, mem_smul_span_pair] at hy
    obtain ⟨a, b, rfl⟩ := hy
    set j : ℤ := d * a * p1 ^ 7 with hj
    obtain ⟨k8, hk8⟩ := hp8
    have hz : T.c * ((-a * k8 * d : ℤ) + ((b - j * q1 : ℤ) : ℂ) * T.Q'.tau) ∈ T.c • (T.Q'.lat : Set ℂ) := by
      rw [HeegnerForm.lat, mem_smul_span_pair]; exact ⟨-a * k8 * d, b - j * q1, by ring⟩
    rw [← T.hlat] at hz
    obtain ⟨w, hw, hwk⟩ := hz
    refine ⟨j • v1 + w, ?_, ?_⟩
    · rw [mem_sInvLat_iff, ← (coe_KL (m := m))]
      have hju : alg (j • u1 m) ∈ latHat m ((KL m (latM T.Q M) : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
        apply mem_latHat_of_mem
        rw [(coe_KL (m := m)), Set.mem_preimage, zsmul_eq_mul, kappa_intCast_mul, kappa_u1, latM,
          SetLike.mem_coe, Submodule.mem_span_pair]
        refine ⟨a * p1 ^ 7, 0, ?_⟩
        simp only [zsmul_eq_mul, zero_smul, add_zero, hj, hinvM]
        push_cast
        ring
      have hv1' : finPart T.s * alg v1 - alg (u1 m) ∈ latHat m ((KL m (latM T.Q M) : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
        rw [(coe_KL (m := m))]; exact hsub hv1
      have hw' : finPart T.s * alg w ∈ latHat m ((KL m (latM T.Q M) : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
        rw [(coe_KL (m := m))]; exact hsub hw
      have := latHat_add_mem _ (latHat_add_mem _ hju (latHat_zsmul_mem _ j hv1')) hw'
      convert this using 1
      rw [map_add, map_zsmul, map_zsmul, mul_add, mul_smul_comm, smul_sub]; abel
    · rw [kappa_add, zsmul_eq_mul, kappa_intCast_mul, hk1, hwk, hj]
      have : (p1 : ℂ) ^ 8 = 1 + 32 * k8 := by
        have := congrArg (fun z : ℤ => (z : ℂ)) hk8; push_cast at this; linear_combination this
      push_cast
      rw [hinvM]
      linear_combination (T.c * a * d / 32) * this

/-- `t/n ∈ K` with `κ(t) = τ_Q`. -/
abbrev tn (m : ℕ) [NeZero m] (Q : HeegnerForm 32 D) (f n : ℕ) : QNeg m :=
  algebraMap ℚ (QNeg m) (1 / (n : ℚ)) * tK m Q (cz m f)

theorem kappa_tn (hD : D = discOf m f) (Q : HeegnerForm 32 D) (n : ℕ) :
    kappa m (tn m Q f n) = Q.tau / n := by
  rw [tn, kappa_mul_eq, kappa_rat, kappa_tK hD Q]; push_cast; ring

/-- **`s⁻¹(τ/n)`** for `n = 2n'`, `M = 2M'`, `dM = 32`: some `v` with `s_f v − τ/n ∈ 𝔞̂` and
`κ(v) = c'(p/n + qτ'/n)`, `q` odd. -/
theorem exists_vt {n M d : ℕ} (hn : 0 < n) (hn2 : 2 ∣ n) (hM2 : 2 ∣ M) (hdM : d * M = 32) :
    ∃ (v : QNeg m) (p q : ℤ),
      finPart T.s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) (tn m T.Q f n) ∈
        latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) ∧
      kappa m v = T.c * (p / n + q * T.Q'.tau / n) ∧ Odd q := by
  obtain ⟨v, hv⟩ := strongApprox m T.hsq f D T.hD 32 T.Q T.s (tn m T.Q f n)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hdM)
  -- `n v ∈ s⁻¹𝔞`
  have hnv : (n : ℤ) • v ∈ sInvLat m T.s (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    rw [mem_sInvLat_iff, ← (coe_KL (m := m))]
    have h1 := latHat_zsmul_mem _ (n : ℤ) (by rw [(coe_KL (m := m))]; exact hv)
    have h2 : algebraMap (QNeg m) (AfK m) ((n : ℤ) • tn m T.Q f n) ∈
        latHat m ((KL m T.Q.lat : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
      apply mem_latHat_of_mem
      rw [(coe_KL (m := m)), Set.mem_preimage, zsmul_eq_mul, kappa_intCast_mul, kappa_tn T.hD]
      have : ((n : ℤ) : ℂ) * (T.Q.tau / n) = T.Q.tau := by push_cast; field_simp
      rw [this]; exact Submodule.subset_span (by simp)
    have := latHat_add_mem _ h1 h2
    convert this using 1
    rw [map_zsmul, map_zsmul, mul_smul_comm, smul_sub]; abel
  rw [mem_sInv_iff T.hlat, HeegnerForm.lat, mem_smul_span_pair] at hnv
  obtain ⟨p, q, hpq⟩ := hnv
  have hk : kappa m v = T.c * (p / n + q * T.Q'.tau / n) := by
    rw [zsmul_eq_mul, kappa_intCast_mul] at hpq
    have : kappa m v = (((n : ℤ) : ℂ))⁻¹ * (T.c * (p * 1 + q * T.Q'.tau)) := by
      rw [← hpq]; push_cast; field_simp
    rw [this]; push_cast; field_simp
  refine ⟨v, p, q, hv, hk, ?_⟩
  by_contra hq
  rw [Int.not_odd_iff_even] at hq
  obtain ⟨r, rfl⟩ := hq
  obtain ⟨n', rfl⟩ := hn2
  obtain ⟨M', rfl⟩ := hM2
  have hn'C : (n' : ℂ) ≠ 0 := by
    have : n' ≠ 0 := by rintro rfl; simp at hn
    exact_mod_cast this
  have hM'C : (M' : ℂ) ≠ 0 := by
    have : M' ≠ 0 := by rintro rfl; simp at hM0
    exact_mod_cast this
  -- `n' v ∈ s⁻¹𝔟_M`
  have hv' : (n' : ℤ) • v ∈ sInvLat m T.s (kappa m ⁻¹' (latM T.Q (2 * M') : Set ℂ)) := by
    rw [mem_sInv_iff (sInv_latM T hdM), latM, mem_smul_span_pair]
    refine ⟨p * M', r, ?_⟩
    rw [zsmul_eq_mul, kappa_intCast_mul, hk]; push_cast; field_simp; ring
  rw [mem_sInvLat_iff, ← (coe_KL (m := m))] at hv'
  have h3 := latHat_sub_mem _ hv' (latHat_zsmul_mem _ (n' : ℤ)
    (by rw [(coe_KL (m := m))]; exact latHat_lat_sub T.Q (lat_le_latM T.Q hM0) hv))
  rw [map_zsmul, smul_sub, mul_smul_comm, sub_sub_cancel, ← map_zsmul, (coe_KL (m := m))] at h3
  have h4 := (Set.ext_iff.1 (latHat_inter_latM T.hsq T.hD T.Q hM0) _).1 h3
  rw [Set.mem_preimage, zsmul_eq_mul, kappa_intCast_mul, kappa_tn T.hD] at h4
  have hM00 : 2 * M' ≠ 0 := hM0.ne'
  rw [← ppM_lattice T.Q (2 * M') hM00] at h4
  apply notMem_of_coeffs (ppM (2 * M') hM00 T.Q.tauH) 0 (1 / 2) (Or.inr (by norm_num)) _ h4
  simp only [ppM]; push_cast; field_simp
  show T.Q.tau * ↑M' = 0 + ↑M' * T.Q.tau
  ring

end Transport

/-! ## Part 5. Weierstrass values: scaling, periodicity, the two orbits of points -/

/-- `(cω₁, cω₂)`. -/
def ppMul (c : ℂ) (hc : c ≠ 0) (P : PeriodPair) : PeriodPair :=
  ⟨c * P.ω₁, c * P.ω₂, by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : c * (s • P.ω₁ + t • P.ω₂) = 0 := by
      simp only [Complex.real_smul] at h ⊢; linear_combination h
    have h2 : s • P.ω₁ + t • P.ω₂ = 0 := by
      rcases mul_eq_zero.1 h1 with h' | h'
      · exact absurd h' hc
      · exact h'
    exact (LinearIndependent.pair_iff.1 P.indep) s t h2⟩

theorem ppMul_isScale (c : ℂ) (hc : c ≠ 0) (P : PeriodPair) : IsScale (ppMul c hc P) P c := by
  refine ⟨hc, ?_⟩
  ext x
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_smul_set, smul_eq_mul, ppMul]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a * P.ω₁ + b * P.ω₂, ⟨a, b, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨a, b, rfl⟩, rfl⟩
    exact ⟨a, b, by ring⟩

theorem wp_congr (P : PeriodPair) {z z' : ℂ} (a b : ℤ) (h : z = z' + (a * P.ω₁ + b * P.ω₂)) :
    P.weierstrassP z = P.weierstrassP z' := by
  rw [h, P.weierstrassP_add_coe z' ⟨a * P.ω₁ + b * P.ω₂, PeriodPair.mem_lattice.2 ⟨a, b, rfl⟩⟩]

theorem wp_congr_neg (P : PeriodPair) {z z' : ℂ} (a b : ℤ) (h : z = -z' + (a * P.ω₁ + b * P.ω₂)) :
    P.weierstrassP z = P.weierstrassP z' := by
  rw [wp_congr P a b h, PeriodPair.weierstrassP_neg]

theorem odd_mod_eight {q : ℤ} (hq : Odd q) :
    q = 8 * (q / 8) + 1 ∨ q = 8 * (q / 8) + 3 ∨ q = 8 * (q / 8) + 5 ∨ q = 8 * (q / 8) + 7 := by
  obtain ⟨k, rfl⟩ := hq
  omega

/-- **The orbit of `(τ/8, 3τ/8, 1/32 + τ/8)` in `⟨1/16, τ⟩`** under `τ/8 ↦ qτ/8`, `q` odd. -/
theorem wp16_cases (τ : UpperHalfPlane) {q : ℤ} (hq : Odd q) :
    let P := ppM 16 (by norm_num) τ
    (P.weierstrassP (q * τ / 8) = P.weierstrassP (τ / 8) ∧
      P.weierstrassP (3 * q * τ / 8) = P.weierstrassP (3 * τ / 8) ∧
      P.weierstrassP (1 / 32 + q * τ / 8) = P.weierstrassP (1 / 32 + τ / 8)) ∨
    (P.weierstrassP (q * τ / 8) = P.weierstrassP (3 * τ / 8) ∧
      P.weierstrassP (3 * q * τ / 8) = P.weierstrassP (τ / 8) ∧
      P.weierstrassP (1 / 32 + q * τ / 8) = P.weierstrassP (1 / 32 + 3 * τ / 8)) := by
  intro P
  set k := q / 8
  have hω : P.ω₁ = 1 / 16 ∧ P.ω₂ = τ := ⟨by simp [P, ppM], rfl⟩
  rcases odd_mod_eight hq with h | h | h | h
  · left
    have hc : (q : ℂ) = 8 * k + 1 := by exact_mod_cast h
    refine ⟨wp_congr P 0 k ?_, wp_congr P 0 (3 * k) ?_, wp_congr P 0 k ?_⟩ <;>
      (rw [hω.1, hω.2, hc]; push_cast; ring)
  · right
    have hc : (q : ℂ) = 8 * k + 3 := by exact_mod_cast h
    refine ⟨wp_congr P 0 k ?_, wp_congr P 0 (3 * k + 1) ?_, wp_congr P 0 k ?_⟩ <;>
      (rw [hω.1, hω.2, hc]; push_cast; ring)
  · right
    have hc : (q : ℂ) = 8 * k + 5 := by exact_mod_cast h
    refine ⟨wp_congr_neg P 0 (k + 1) ?_, wp_congr_neg P 0 (3 * k + 2) ?_, wp_congr_neg P 1 (k + 1) ?_⟩ <;>
      (rw [hω.1, hω.2, hc]; push_cast; ring)
  · left
    have hc : (q : ℂ) = 8 * k + 7 := by exact_mod_cast h
    refine ⟨wp_congr_neg P 0 (k + 1) ?_, wp_congr_neg P 0 (3 * k + 3) ?_, wp_congr_neg P 1 (k + 1) ?_⟩ <;>
      (rw [hω.1, hω.2, hc]; push_cast; ring)

/-- **The orbit of `(1/16, 3/16, τ/2 + 1/16)` in `⟨1/2, τ⟩`** under `1/16 ↦ p/16`, `p` odd. -/
theorem wp2_cases (τ : UpperHalfPlane) {p : ℤ} (hp : Odd p) :
    let P := ppM 2 (by norm_num) τ
    (P.weierstrassP (p / 16) = P.weierstrassP (1 / 16) ∧
      P.weierstrassP (3 * p / 16) = P.weierstrassP (3 / 16) ∧
      P.weierstrassP (τ / 2 + p / 16) = P.weierstrassP (τ / 2 + 1 / 16)) ∨
    (P.weierstrassP (p / 16) = P.weierstrassP (3 / 16) ∧
      P.weierstrassP (3 * p / 16) = P.weierstrassP (1 / 16) ∧
      P.weierstrassP (τ / 2 + p / 16) = P.weierstrassP (τ / 2 + 3 / 16)) := by
  intro P
  set k := p / 8
  have hω : P.ω₁ = 1 / 2 ∧ P.ω₂ = τ := ⟨by simp [P, ppM], rfl⟩
  rcases odd_mod_eight hp with h | h | h | h
  · left
    have hc : (p : ℂ) = 8 * k + 1 := by exact_mod_cast h
    refine ⟨wp_congr P k 0 ?_, wp_congr P (3 * k) 0 ?_, wp_congr P k 0 ?_⟩ <;>
      (rw [hω.1, hω.2, hc]; push_cast; ring)
  · right
    have hc : (p : ℂ) = 8 * k + 3 := by exact_mod_cast h
    refine ⟨wp_congr P k 0 ?_, wp_congr P (3 * k + 1) 0 ?_, wp_congr P k 0 ?_⟩ <;>
      (rw [hω.1, hω.2, hc]; push_cast; ring)
  · right
    have hc : (p : ℂ) = 8 * k + 5 := by exact_mod_cast h
    refine ⟨wp_congr_neg P (k + 1) 0 ?_, wp_congr_neg P (3 * k + 2) 0 ?_, wp_congr_neg P (k + 1) 1 ?_⟩ <;>
      (rw [hω.1, hω.2, hc]; push_cast; ring)
  · left
    have hc : (p : ℂ) = 8 * k + 7 := by exact_mod_cast h
    refine ⟨wp_congr_neg P (k + 1) 0 ?_, wp_congr_neg P (3 * k + 3) 0 ?_, wp_congr_neg P (k + 1) 1 ?_⟩ <;>
      (rw [hω.1, hω.2, hc]; push_cast; ring)

/-- Ratios of differences are invariant under a common scaling. -/
theorem ratio_conj (σ : ℂ ≃+* ℂ) {a b c a' b' c' k : ℂ} (hk : k ≠ 0) (ha : σ a = k * a')
    (hb : σ b = k * b') (hc : σ c = k * c') : σ ((a - c) / (b - c)) = (a' - c') / (b' - c') := by
  rw [map_div₀, map_sub, map_sub, ha, hb, hc, ← mul_sub, ← mul_sub, mul_div_mul_left _ _ hk]

/-! ## Part 6. The transport of the two `℘`-ratios -/

/-- `(℘(a) − ℘(c))/(℘(b) − ℘(c))`. -/
def wpRatio (P : PeriodPair) (a b c : ℂ) : ℂ :=
  (P.weierstrassP a - P.weierstrassP c) / (P.weierstrassP b - P.weierstrassP c)

section Transport2

variable {f : ℕ} [NeZero f] {D : ℤ} (T : TData m f D)

/-- One application of `ShimuraMainCM` at the lattice `⟨1/M, τ_Q⟩`. -/
theorem cm_point {M d : ℕ} (hdM : d * M = 32) (hCM : ShimuraMainCM)
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (hs : ArtinCond m e σ T.s) (hM : M ≠ 0) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ∀ (u v : QNeg m) (w : ℂ),
      kappa m u ∉ (ppM M hM T.Q.tauH).lattice →
      finPart T.s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈
        latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) →
      kappa m v = T.c * w →
      σ ((ppM M hM T.Q.tauH).weierstrassP (kappa m u)) =
        (μ ^ 2 * (T.c ^ 2)⁻¹) * (ppM M hM T.Q'.tauH).weierstrassP w := by
  have hM0 : 0 < M := Nat.pos_of_ne_zero hM
  have hP : ((ppM M hM T.Q.tauH).lattice : Set ℂ) = kappa m '' (kappa m ⁻¹' (latM T.Q M : Set ℂ)) := by
    rw [ppM_lattice]; exact (Set.image_preimage_eq_of_subset (latM_subset_range T.hD T.Q M)).symm
  have hsc := ppMul_isScale T.c T.hc (ppM M hM T.Q'.tauH)
  have hP' : ((ppMul T.c T.hc (ppM M hM T.Q'.tauH)).lattice : Set ℂ) =
      kappa m '' sInvLat m T.s (kappa m ⁻¹' (latM T.Q M : Set ℂ)) := by
    rw [hsc.2, sInv_latM T hdM, ppM_lattice]
  obtain ⟨μ, hμ, hpts⟩ := hCM m T.hsq e he σ T.s hs _ _ _ hP hP'
  refine ⟨μ, hμ.1, fun u v w hu hv hw => ?_⟩
  have h1 := (hpts u v hu (latHat_lat_sub T.Q (lat_le_latM T.Q hM0) hv)).1
  rw [h1, hw, hsc.weierstrassP]
  ring

/-- **Transport of the `⟨1/16, τ⟩`-ratio** of (Ix): `σ` maps it to one of the two forms at `τ'`. -/
theorem transport16 (hCM : ShimuraMainCM) (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (hs : ArtinCond m e σ T.s) :
    let P := ppM 16 (by norm_num) T.Q.tauH
    let R := ppM 16 (by norm_num) T.Q'.tauH
    let τ : ℂ := T.Q.tauH
    let τ' : ℂ := T.Q'.tauH
    σ (wpRatio P (1 / 32) (3 * τ / 8) (1 / 32 + τ / 8)) = wpRatio R (1 / 32) (3 * τ' / 8) (1 / 32 + τ' / 8) ∨
    σ (wpRatio P (1 / 32) (3 * τ / 8) (1 / 32 + τ / 8)) = wpRatio R (1 / 32) (τ' / 8) (1 / 32 + 3 * τ' / 8) := by
  intro P R τ τ'
  obtain ⟨μ, hμ, hpt⟩ := cm_point T (d := 2) (by norm_num) hCM e he σ hs (by norm_num : (16 : ℕ) ≠ 0)
  obtain ⟨v1, p1, q1, hv1, hk1, hp1⟩ := exists_v1 T
  obtain ⟨v2, p2, q2, hv2, hk2, hq2⟩ := exists_vt T (n := 8) (M := 16) (d := 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨a1, ha1⟩ := hp1
  have hk0 : μ ^ 2 * (T.c ^ 2)⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hμ) (inv_ne_zero (pow_ne_zero 2 T.hc))
  have hωR : R.ω₁ = 1 / 16 ∧ R.ω₂ = τ' := ⟨by simp [R, ppM], rfl⟩
  have hωP : P.ω₁ = 1 / 16 ∧ P.ω₂ = τ := ⟨by simp [P, ppM], rfl⟩
  have htau : T.Q.tau = τ := rfl
  have htau' : T.Q'.tau = τ' := rfl
  have hu2 := kappa_tn (m := m) T.hD T.Q 8
  rw [htau] at hu2
  push_cast at hu2
  set alg := algebraMap (QNeg m) (AfK m)
  have hsub : ∀ {x y : AfK m}, x ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) →
      y ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) → x + y ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    intro x y hx hy
    rw [← (coe_KL (m := m))] at hx hy ⊢; exact latHat_add_mem _ hx hy
  have hzs : ∀ (n : ℤ) {x : AfK m}, x ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) →
      n • x ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    intro n x hx
    rw [← (coe_KL (m := m))] at hx ⊢; exact latHat_zsmul_mem _ n hx
  -- the three points
  have e1 := hpt (u1 m) v1 (p1 * (1 / 32) + q1 * τ')
    (by
      rw [kappa_u1]
      exact notMem_of_coeffs P (1 / 2) 0 (Or.inl (by norm_num)) (by rw [hωP.1]; push_cast; ring))
    hv1 (by rw [hk1, htau'])
  have e3 := hpt ((3 : ℤ) • tn m T.Q f 8) ((3 : ℤ) • v2) (3 * p2 / 8 + 3 * q2 * τ' / 8)
    (by
      rw [zsmul_eq_mul, kappa_intCast_mul, hu2]
      exact notMem_of_coeffs P 0 (3 / 8) (Or.inr (by norm_num)) (by rw [hωP.2]; push_cast; ring))
    (by
      have := hzs 3 hv2
      convert this using 1
      rw [map_zsmul, map_zsmul, mul_smul_comm, smul_sub])
    (by rw [zsmul_eq_mul, kappa_intCast_mul, hk2, htau']; push_cast; ring)
  have e4 := hpt (u1 m + tn m T.Q f 8) (v1 + v2) ((p1 * (1 / 32) + q1 * τ') + (p2 / 8 + q2 * τ' / 8))
    (by
      rw [kappa_add, kappa_u1, hu2]
      exact notMem_of_coeffs P (1 / 2) (1 / 8) (Or.inl (by norm_num))
        (by rw [hωP.1, hωP.2]; push_cast; ring))
    (by
      have := hsub hv1 hv2
      convert this using 1
      rw [map_add, map_add, mul_add]; abel)
    (by rw [kappa_add, hk1, hk2, htau']; ring)
  rw [kappa_u1] at e1
  rw [zsmul_eq_mul, kappa_intCast_mul, hu2] at e3
  rw [kappa_add, kappa_u1, hu2] at e4
  -- reduce the transported points
  have r1 : R.weierstrassP (p1 * (1 / 32) + q1 * τ') = R.weierstrassP (1 / 32) :=
    wp_congr R a1 q1 (by rw [hωR.1, hωR.2, ha1]; push_cast; ring)
  have r3 : R.weierstrassP (3 * p2 / 8 + 3 * q2 * τ' / 8) = R.weierstrassP (3 * q2 * τ' / 8) :=
    wp_congr R (6 * p2) 0 (by rw [hωR.1, hωR.2]; push_cast; ring)
  have r4 : R.weierstrassP ((p1 * (1 / 32) + q1 * τ') + (p2 / 8 + q2 * τ' / 8)) =
      R.weierstrassP (1 / 32 + q2 * τ' / 8) :=
    wp_congr R (a1 + 2 * p2) q1 (by rw [hωR.1, hωR.2, ha1]; push_cast; ring)
  rw [r1] at e1; rw [r3] at e3; rw [r4] at e4
  have e3' : σ (P.weierstrassP (3 * τ / 8)) = μ ^ 2 * (T.c ^ 2)⁻¹ * R.weierstrassP (3 * q2 * τ' / 8) := by
    convert e3 using 3; push_cast; ring
  rcases wp16_cases T.Q'.tauH hq2 with ⟨-, h3, h4⟩ | ⟨-, h3, h4⟩
  · left
    exact ratio_conj σ hk0 e1 (by rw [e3', h3]) (by rw [e4, h4])
  · right
    exact ratio_conj σ hk0 e1 (by rw [e3', h3]) (by rw [e4, h4])

/-- **Transport of the `⟨1/2, τ⟩`-ratio** of (IxW). -/
theorem transport2 (hCM : ShimuraMainCM) (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (hs : ArtinCond m e σ T.s) :
    let P := ppM 2 (by norm_num) T.Q.tauH
    let R := ppM 2 (by norm_num) T.Q'.tauH
    let τ : ℂ := T.Q.tauH
    let τ' : ℂ := T.Q'.tauH
    σ (wpRatio P (τ / 2) (3 / 16) (τ / 2 + 1 / 16)) = wpRatio R (τ' / 2) (3 / 16) (τ' / 2 + 1 / 16) ∨
    σ (wpRatio P (τ / 2) (3 / 16) (τ / 2 + 1 / 16)) = wpRatio R (τ' / 2) (1 / 16) (τ' / 2 + 3 / 16) := by
  intro P R τ τ'
  obtain ⟨μ, hμ, hpt⟩ := cm_point T (d := 16) (by norm_num) hCM e he σ hs (by norm_num : (2 : ℕ) ≠ 0)
  obtain ⟨v1, p1, q1, hv1, hk1, hp1⟩ := exists_v1 T
  obtain ⟨v2, p2, q2, hv2, hk2, hq2⟩ := exists_vt T (n := 2) (M := 2) (d := 16) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨b2, hb2⟩ := hq2
  have hk0 : μ ^ 2 * (T.c ^ 2)⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hμ) (inv_ne_zero (pow_ne_zero 2 T.hc))
  have hωR : R.ω₁ = 1 / 2 ∧ R.ω₂ = τ' := ⟨by simp [R, ppM], rfl⟩
  have hωP : P.ω₁ = 1 / 2 ∧ P.ω₂ = τ := ⟨by simp [P, ppM], rfl⟩
  have htau : T.Q.tau = τ := rfl
  have htau' : T.Q'.tau = τ' := rfl
  have hu2 := kappa_tn (m := m) T.hD T.Q 2
  rw [htau] at hu2
  push_cast at hu2
  push_cast at hk2
  set alg := algebraMap (QNeg m) (AfK m)
  have hsub : ∀ {x y : AfK m}, x ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) →
      y ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) → x + y ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    intro x y hx hy
    rw [← (coe_KL (m := m))] at hx hy ⊢; exact latHat_add_mem _ hx hy
  have hzs : ∀ (n : ℤ) {x : AfK m}, x ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) →
      n • x ∈ latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    intro n x hx
    rw [← (coe_KL (m := m))] at hx ⊢; exact latHat_zsmul_mem _ n hx
  have hzs1 : ∀ n : ℤ, finPart T.s * alg (n • v1) - alg (n • u1 m) ∈
      latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    intro n
    have := hzs n hv1
    convert this using 1
    rw [map_zsmul, map_zsmul, mul_smul_comm, smul_sub]
  have e1 := hpt (tn m T.Q f 2) v2 (p2 / 2 + q2 * τ' / 2)
    (by
      rw [hu2]
      exact notMem_of_coeffs P 0 (1 / 2) (Or.inr (by norm_num)) (by rw [hωP.2]; push_cast; ring))
    hv2 (by rw [hk2, htau'])
  have e2 := hpt ((6 : ℤ) • u1 m) ((6 : ℤ) • v1) (6 * p1 / 32 + 6 * q1 * τ')
    (by
      rw [zsmul_eq_mul, kappa_intCast_mul, kappa_u1]
      exact notMem_of_coeffs P (3 / 8) 0 (Or.inl (by norm_num)) (by rw [hωP.1]; push_cast; ring))
    (hzs1 6) (by rw [zsmul_eq_mul, kappa_intCast_mul, hk1, htau']; push_cast; ring)
  have e3 := hpt (tn m T.Q f 2 + (2 : ℤ) • u1 m) (v2 + (2 : ℤ) • v1)
    ((p2 / 2 + q2 * τ' / 2) + (2 * p1 / 32 + 2 * q1 * τ'))
    (by
      rw [kappa_add, zsmul_eq_mul, kappa_intCast_mul, kappa_u1, hu2]
      exact notMem_of_coeffs P (1 / 8) (1 / 2) (Or.inl (by norm_num))
        (by rw [hωP.1, hωP.2]; push_cast; ring))
    (by
      have := hsub hv2 (hzs1 2)
      convert this using 1
      rw [map_add, map_add, mul_add]; abel)
    (by rw [kappa_add, zsmul_eq_mul, kappa_intCast_mul, hk1, hk2, htau']; push_cast; ring)
  rw [hu2] at e1
  rw [zsmul_eq_mul, kappa_intCast_mul, kappa_u1] at e2
  rw [kappa_add, zsmul_eq_mul, kappa_intCast_mul, kappa_u1, hu2] at e3
  have r1 : R.weierstrassP (p2 / 2 + q2 * τ' / 2) = R.weierstrassP (τ' / 2) :=
    wp_congr R p2 b2 (by rw [hωR.1, hωR.2, hb2]; push_cast; ring)
  have r2 : R.weierstrassP (6 * p1 / 32 + 6 * q1 * τ') = R.weierstrassP (3 * p1 / 16) :=
    wp_congr R 0 (6 * q1) (by rw [hωR.1, hωR.2]; push_cast; ring)
  have r3 : R.weierstrassP ((p2 / 2 + q2 * τ' / 2) + (2 * p1 / 32 + 2 * q1 * τ')) =
      R.weierstrassP (τ' / 2 + p1 / 16) :=
    wp_congr R p2 (b2 + 2 * q1) (by rw [hωR.1, hωR.2, hb2]; push_cast; ring)
  rw [r1] at e1; rw [r2] at e2; rw [r3] at e3
  have e2' : σ (P.weierstrassP (3 / 16)) = μ ^ 2 * (T.c ^ 2)⁻¹ * R.weierstrassP (3 * p1 / 16) := by
    convert e2 using 3; push_cast; ring
  have e3' : σ (P.weierstrassP (τ / 2 + 1 / 16)) = μ ^ 2 * (T.c ^ 2)⁻¹ * R.weierstrassP (τ' / 2 + p1 / 16) := by
    convert e3 using 3; push_cast; ring
  rcases wp2_cases T.Q'.tauH hp1 with ⟨-, h3, h4⟩ | ⟨-, h3, h4⟩
  · left
    exact ratio_conj σ hk0 e1 (by rw [e2', h3]) (by rw [e3', h4])
  · right
    exact ratio_conj σ hk0 e1 (by rw [e2', h3]) (by rw [e3', h4])

end Transport2

/-! ## Part 7. The identity (Ix), its Fricke transform, and `y` from `x` -/

/-- The two forms of (Ix) (the second follows from the first: `xEtaWeierstrassPair_of`). x0-32's eta quotient
`x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2` is a weight-0 ratio of Weierstrass values of the lattice
`⟨1/16, τ⟩` at three of its torsion points, in two ways:
`x(τ) = 2 − 4(℘(1/32) − ℘(1/32 + τ/8))/(℘(3τ/8) − ℘(1/32 + τ/8))`
`     = 2 − 4(℘(1/32) − ℘(1/32 + 3τ/8))/(℘(τ/8) − ℘(1/32 + 3τ/8))`, `℘ = ℘_{⟨1/16, τ⟩}`.
Found by a search over the points of `E[8]` and checked at 12 random points of `ℍ` to 36 digits
(`scratch/hx-used/num/search_x.py`, `check_xy.py`). Classical in nature (Jacobi's theta/`℘`
relations; `x = 2θ₀₀(16τ)/θ₁₀(16τ)` is the kernel's `Shimura.xC_theta`), no printed source located. -/
def XEtaWeierstrassPair : Prop :=
  ∀ τ : UpperHalfPlane,
    ZInQ.Contrib.TYZGenus.X0.xC τ = 2 - 4 * wpRatio (ppM 16 (by norm_num) τ) (1 / 32) (3 * τ / 8) (1 / 32 + τ / 8) ∧
    ZInQ.Contrib.TYZGenus.X0.xC τ = 2 - 4 * wpRatio (ppM 16 (by norm_num) τ) (1 / 32) (τ / 8) (1 / 32 + 3 * τ / 8)


theorem wpRatio_scale {P Q : PeriodPair} {c : ℂ} (h : IsScale P Q c) (a b d : ℂ) :
    wpRatio P (c * a) (c * b) (c * d) = wpRatio Q a b d := by
  simp only [wpRatio, h.weierstrassP]
  have hc : ((c ^ 2)⁻¹ : ℂ) ≠ 0 := inv_ne_zero (pow_ne_zero 2 h.1)
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hc]

/-- **GLUE X-ETA-WP (an identity of explicit functions on `ℍ`).** x0-32's eta quotient
`x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2` is a weight-0 ratio of Weierstrass values of the lattice
`⟨1/16, τ⟩` at three of its torsion points:
`x(τ) = 2 − 4(℘(1/32) − ℘(1/32 + τ/8))/(℘(3τ/8) − ℘(1/32 + τ/8))`, `℘ = ℘_{⟨1/16, τ⟩}` (Mathlib's
`PeriodPair.weierstrassP` of the period pair `(1/16, τ)`). Found by a search over the points of
`(1/8)⟨1/16, τ⟩` and checked at 12 random points of `ℍ` to 36 digits (`scratch/hx-used/num/search_x.py`,
`check_xy.py`). Classical in nature (Jacobi's relations between `θ` and `℘`; the kernel proves
`x = 2θ₀₀(16τ)/θ₁₀(16τ)`, `Shimura.xC_theta`); no printed source located. -/
def XEtaWeierstrass : Prop :=
  ∀ τ : UpperHalfPlane,
    ZInQ.Contrib.TYZGenus.X0.xC τ = 2 - 4 * wpRatio (ppM 16 (by norm_num) τ) (1 / 32) (3 * τ / 8) (1 / 32 + τ / 8)

/-- `γ₃ = [[3, 1], [32, 11]] ∈ Γ₀(32)`. -/
def gamma3 : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![3, 1; 32, 11], by rw [Matrix.det_fin_two_of]; norm_num⟩

theorem gamma3_mem : gamma3 ∈ CongruenceSubgroup.Gamma0 32 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [gamma3]
  decide

/-- `⟨1/16, γ₃τ⟩ = (32τ + 11)⁻¹·⟨1/16, τ⟩`. -/
theorem isScale_gamma3 (τ : UpperHalfPlane) :
    IsScale (ppM 16 (by norm_num) (gamma3 • τ)) (ppM 16 (by norm_num) τ) (1 / (32 * (τ : ℂ) + 11)) := by
  have hden : (32 * (τ : ℂ) + 11) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact (ne_of_gt τ.im_pos) (by linarith)
  have hg : ((gamma3 • τ : UpperHalfPlane) : ℂ) = (3 * τ + 1) / (32 * τ + 11) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [gamma3]
  have hden' : (11 + (τ : ℂ) * 32) ≠ 0 := by rw [add_comm, mul_comm]; exact hden
  refine ⟨by simp [hden], ?_⟩
  ext x
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_smul_set, smul_eq_mul, ppM, hg]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨((11 * a + 16 * b : ℤ) : ℂ) * (1 / 16) + ((2 * a + 3 * b : ℤ) : ℂ) * τ,
      ⟨11 * a + 16 * b, 2 * a + 3 * b, rfl⟩, ?_⟩
    push_cast; field_simp; ring
  · rintro ⟨y, ⟨a, b, rfl⟩, rfl⟩
    refine ⟨3 * a - 16 * b, -2 * a + 11 * b, ?_⟩
    have hu : (32 * (τ : ℂ) + 11) * (32 * (τ : ℂ) + 11)⁻¹ = 1 := mul_inv_cancel₀ hden
    push_cast
    linear_combination (-(3 * (a : ℂ) - 16 * b) / 16) * hu

/-- **The second form of (Ix) from the first** (`x(γ₃τ) = x(τ)`, kernel's `Shimura.etaModelInvariant`). -/
theorem xEtaWeierstrassPair_of (hX : XEtaWeierstrass) : XEtaWeierstrassPair := by
  intro τ
  refine ⟨hX τ, ?_⟩
  have hden : (32 * (τ : ℂ) + 11) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact (ne_of_gt τ.im_pos) (by linarith)
  have hg : ((gamma3 • τ : UpperHalfPlane) : ℂ) = (3 * τ + 1) / (32 * τ + 11) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [gamma3]
  have hinv := (etaModelInvariant gamma3 gamma3_mem τ).1
  have hden' : (11 + (τ : ℂ) * 32) ≠ 0 := by rw [add_comm, mul_comm]; exact hden
  rw [← hinv, hX (gamma3 • τ)]
  have hω : (ppM 16 (by norm_num) τ).ω₁ = 1 / 16 ∧ (ppM 16 (by norm_num) τ).ω₂ = τ :=
    ⟨by simp [ppM], rfl⟩
  have e : wpRatio (ppM 16 (by norm_num) (gamma3 • τ)) (1 / 32) (3 * ((gamma3 • τ : UpperHalfPlane) : ℂ) / 8)
      (1 / 32 + ((gamma3 • τ : UpperHalfPlane) : ℂ) / 8) =
      wpRatio (ppM 16 (by norm_num) (gamma3 • τ)) ((1 / (32 * (τ : ℂ) + 11)) * ((τ : ℂ) + 11 / 32))
        ((1 / (32 * (τ : ℂ) + 11)) * (9 * (τ : ℂ) / 8 + 3 / 8))
        ((1 / (32 * (τ : ℂ) + 11)) * (11 * (τ : ℂ) / 8 + 15 / 32)) := by
    congr 1 <;> (try rw [hg]) <;> field_simp <;> ring
  rw [e, wpRatio_scale (isScale_gamma3 τ)]
  have r1 : (ppM 16 (by norm_num) τ).weierstrassP ((τ : ℂ) + 11 / 32) =
      (ppM 16 (by norm_num) τ).weierstrassP (1 / 32) :=
    wp_congr _ 5 1 (by rw [hω.1, hω.2]; push_cast; ring)
  have r2 : (ppM 16 (by norm_num) τ).weierstrassP (9 * (τ : ℂ) / 8 + 3 / 8) =
      (ppM 16 (by norm_num) τ).weierstrassP ((τ : ℂ) / 8) :=
    wp_congr _ 6 1 (by rw [hω.1, hω.2]; push_cast; ring)
  have r3 : (ppM 16 (by norm_num) τ).weierstrassP (11 * (τ : ℂ) / 8 + 15 / 32) =
      (ppM 16 (by norm_num) τ).weierstrassP (1 / 32 + 3 * (τ : ℂ) / 8) :=
    wp_congr _ 7 1 (by rw [hω.1, hω.2]; push_cast; ring)
  rw [wpRatio, wpRatio, r1, r2, r3]


/-- **GLUE THETA-WP-8 (Jacobi's `θ` against `℘` at 8-torsion; an identity of explicit functions on `ℍ`).**
For the lattice `⟨1, w⟩`, `w ∈ ℍ`, with Mathlib's `jacobiTheta₂` (`θ(z; w) = Σₙ e^{2πinz + πin²w}`) and
`℘ = ℘_{⟨1, w⟩}` (Mathlib's `PeriodPair.weierstrassP`):
`θ(0; w) / (e^{πiw/4} θ(w/2; w)) = 1 − 2(℘(1/2) − ℘(1/2 + w/8))/(℘(3w/8) − ℘(1/2 + w/8))`.
The left side is `θ₀₀(w)/θ₁₀(w)` in the classical notation. Checked at 12 random points of `ℍ` to 40 digits
(`scratch/hx-used/num/check_theta.py`); found as the form of `XEtaWeierstrass` under the kernel's proved
`x = 2θ₀₀(16τ)/θ₁₀(16τ)` (`Shimura.xC_theta`). Classical in nature (Jacobi's relations between theta constants and
`℘` at torsion points, e.g. via `℘(u) − ℘(v) = −σ(u − v)σ(u + v)/(σ(u)²σ(v)²)` and `σ ∝ e^{ηz²/2}θ₁`); no printed
source located (theorem numbers would be UNVERIFIED in any case). -/
def ThetaWeierstrass8 : Prop :=
  ∀ w : UpperHalfPlane,
    jacobiTheta₂ 0 w / (cexp (Real.pi * I * w / 4) * jacobiTheta₂ ((w : ℂ) / 2) w) =
      1 - 2 * wpRatio (pp w) (1 / 2) (3 * (w : ℂ) / 8) (1 / 2 + (w : ℂ) / 8)

/-- `16τ ∈ ℍ`. -/
def mul16 (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨16 * (τ : ℂ), by
    have := ZInQ.Contrib.TYZGenus.X0.mul_mem_upperHalfPlaneSet (d := 16) (by norm_num) τ
    simpa using this⟩

/-- `⟨1/16, τ⟩ = (1/16)·⟨1, 16τ⟩`. -/
theorem isScale_16 (τ : UpperHalfPlane) :
    IsScale (ppM 16 (by norm_num) τ) (pp (mul16 τ)) (1 / 16) := by
  refine ⟨by norm_num, ?_⟩
  ext x
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_smul_set, smul_eq_mul, ppM, pp, mul16]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a * 1 + b * (16 * (τ : ℂ)), ⟨a, b, rfl⟩, by push_cast; ring⟩
  · rintro ⟨y, ⟨a, b, rfl⟩, rfl⟩
    exact ⟨a, b, by push_cast; ring⟩

/-- **`XEtaWeierstrass` from its theta form** (with the kernel's `Shimura.xC_theta`). -/
theorem xEtaWeierstrass_of_theta (h : ThetaWeierstrass8) : XEtaWeierstrass := by
  intro τ
  have hw := h (mul16 τ)
  have hm : ((mul16 τ : UpperHalfPlane) : ℂ) = 16 * (τ : ℂ) := rfl
  rw [hm] at hw
  have hQ : Qt (τ : ℂ) ^ 2 = cexp (Real.pi * I * (16 * (τ : ℂ)) / 4) := by
    rw [Qt_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h8 : (16 * (τ : ℂ)) / 2 = 8 * τ := by ring
  rw [h8] at hw
  rw [xC_theta τ, hQ, mul_div_assoc, hw]
  have e : wpRatio (pp (mul16 τ)) (1 / 2) (3 * (16 * (τ : ℂ)) / 8) (1 / 2 + 16 * (τ : ℂ) / 8) =
      wpRatio (ppM 16 (by norm_num) τ) ((1 / 16) * (1 / 2)) ((1 / 16) * (3 * (16 * (τ : ℂ)) / 8))
        ((1 / 16) * (1 / 2 + 16 * (τ : ℂ) / 8)) := by
    rw [wpRatio_scale (isScale_16 τ)]
  have e2 : wpRatio (ppM 16 (by norm_num) τ) ((1 / 16) * (1 / 2)) ((1 / 16) * (3 * (16 * (τ : ℂ)) / 8))
        ((1 / 16) * (1 / 2 + 16 * (τ : ℂ) / 8)) =
      wpRatio (ppM 16 (by norm_num) τ) (1 / 32) (3 * (τ : ℂ) / 8) (1 / 32 + (τ : ℂ) / 8) := by
    congr 1 <;> ring
  rw [e, e2]
  ring

/-- `⟨1/16, −1/(32τ)⟩ = (−1/(16τ))·⟨1/2, τ⟩`. -/
theorem isScale_fricke (τ : UpperHalfPlane) :
    IsScale (ppM 16 (by norm_num) (frickeH τ)) (ppM 2 (by norm_num) τ) (-1 / (16 * (τ : ℂ))) := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  refine ⟨by simp [hτ], ?_⟩
  ext x
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_smul_set, smul_eq_mul, ppM, frickeH]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨b * (1 / 2) + (-a : ℤ) * τ, ⟨b, -a, rfl⟩, ?_⟩
    push_cast; field_simp; ring
  · rintro ⟨y, ⟨a, b, rfl⟩, rfl⟩
    refine ⟨-b, a, ?_⟩
    push_cast; field_simp; ring

/-- **(IxW)**: the Fricke transform of (Ix), `x(−1/(32τ))` through `℘_{⟨1/2, τ⟩}`. -/
theorem xC_fricke_wp (hX : XEtaWeierstrassPair) (τ : UpperHalfPlane) :
    ZInQ.Contrib.TYZGenus.X0.xC (frickeH τ) = 2 - 4 * wpRatio (ppM 2 (by norm_num) τ) (τ / 2) (3 / 16) (τ / 2 + 1 / 16) ∧
    ZInQ.Contrib.TYZGenus.X0.xC (frickeH τ) = 2 - 4 * wpRatio (ppM 2 (by norm_num) τ) (τ / 2) (1 / 16) (τ / 2 + 3 / 16) := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hs := isScale_fricke τ
  set P := ppM 2 (by norm_num) τ
  have hω : P.ω₁ = 1 / 2 ∧ P.ω₂ = τ := ⟨by simp [P, ppM], rfl⟩
  have hf : ((frickeH τ : UpperHalfPlane) : ℂ) = -1 / (32 * (τ : ℂ)) := rfl
  obtain ⟨h1, h2⟩ := hX (frickeH τ)
  have n1 : P.weierstrassP (-(τ : ℂ) / 2) = P.weierstrassP (τ / 2) :=
    wp_congr_neg P 0 0 (by ring)
  have n2 : ∀ z : ℂ, P.weierstrassP (-(τ : ℂ) / 2 + z) = P.weierstrassP (τ / 2 + z) := fun z =>
    wp_congr P 0 (-1) (by rw [hω.2]; push_cast; ring)
  constructor
  · rw [h1]
    have e : wpRatio (ppM 16 (by norm_num) (frickeH τ)) (1 / 32) (3 * (frickeH τ : ℂ) / 8)
        (1 / 32 + (frickeH τ : ℂ) / 8) =
        wpRatio (ppM 16 (by norm_num) (frickeH τ)) ((-1 / (16 * (τ : ℂ))) * (-(τ : ℂ) / 2)) ((-1 / (16 * (τ : ℂ))) * (3 / 16))
        ((-1 / (16 * (τ : ℂ))) * (-(τ : ℂ) / 2 + 1 / 16)) := by
      congr 1 <;> (try rw [hf]) <;> field_simp <;> ring
    rw [e, wpRatio_scale hs]
    simp only [wpRatio, n1, n2]
  · rw [h2]
    have e : wpRatio (ppM 16 (by norm_num) (frickeH τ)) (1 / 32) ((frickeH τ : ℂ) / 8)
        (1 / 32 + 3 * (frickeH τ : ℂ) / 8) =
        wpRatio (ppM 16 (by norm_num) (frickeH τ)) ((-1 / (16 * (τ : ℂ))) * (-(τ : ℂ) / 2)) ((-1 / (16 * (τ : ℂ))) * (1 / 16))
        ((-1 / (16 * (τ : ℂ))) * (-(τ : ℂ) / 2 + 3 / 16)) := by
      congr 1 <;> (try rw [hf]) <;> field_simp <;> ring
    rw [e, wpRatio_scale hs]
    simp only [wpRatio, n1, n2]

open WeierstrassCurve.Affine in
/-- **`y` from `x` and `x∘W₃₂`** (the proved Fricke relation `φ(−1/(32τ)) = T − φ(τ)`, `T = (2, −4)`):
`8y = x³ + 4x + 16 − (x − 2)²(x(−1/(32τ)) + x + 2)`. -/
theorem yC_formula (τ : UpperHalfPlane) :
    ZInQ.Contrib.TYZGenus.X0.yC τ = (ZInQ.Contrib.TYZGenus.X0.xC τ ^ 3 + 4 * ZInQ.Contrib.TYZGenus.X0.xC τ + 16 -
      (ZInQ.Contrib.TYZGenus.X0.xC τ - 2) ^ 2 * (ZInQ.Contrib.TYZGenus.X0.xC (frickeH τ) + ZInQ.Contrib.TYZGenus.X0.xC τ + 2)) / 8 := by
  have hF := etaModelFricke τ (frickeH τ) rfl
  obtain ⟨h, hP⟩ := ZInQ.Contrib.TYZGenus.X0.phiC_eq_some etaModelEquation τ
  obtain ⟨h', hP'⟩ := ZInQ.Contrib.TYZGenus.X0.phiC_eq_some etaModelEquation (frickeH τ)
  have hx2 := xC_sub_two_ne_zero τ
  have hne : (2 : ℂ) ≠ ZInQ.Contrib.TYZGenus.X0.xC τ := fun h0 => hx2 (by rw [← h0]; ring)
  have key : ZInQ.Contrib.TYZGenus.X0.phiC (frickeH τ) = ZInQ.Contrib.TYZGenus.X0.ptTC + -ZInQ.Contrib.TYZGenus.X0.phiC τ := by
    rw [← hF]; abel
  rw [hP, hP', Point.neg_some, ZInQ.Contrib.TYZGenus.X0.ptTC, Point.add_of_X_ne hne] at key
  simp only [Point.some.injEq] at key
  obtain ⟨kx, -⟩ := key
  rw [negY_AC, slope_of_X_ne hne] at kx
  simp only [addX, curveAC_a₁, curveAC_a₂, zero_mul, add_zero, sub_zero] at kx
  have heq := etaModelEquation τ
  have h2x : (2 : ℂ) - ZInQ.Contrib.TYZGenus.X0.xC τ ≠ 0 := sub_ne_zero.2 hne
  have hsq : (ZInQ.Contrib.TYZGenus.X0.xC τ - 2) ^ 2 *
      (ZInQ.Contrib.TYZGenus.X0.xC (frickeH τ) + ZInQ.Contrib.TYZGenus.X0.xC τ + 2) =
      (ZInQ.Contrib.TYZGenus.X0.yC τ - 4) ^ 2 := by
    rw [kx]; field_simp; ring
  rw [hsq]
  linear_combination (1 / 8 : ℂ) * heq

/-! ## Part 8. Assembly: the level-32 instances of `ShimuraReciprocityModFn` from `hCM` and (Ix) -/

theorem conj_two_sub_four {σ : ℂ ≃+* ℂ} {r r' : ℂ} (h : σ r = r') :
    σ (2 - 4 * r) = 2 - 4 * r' := by
  rw [map_sub, map_mul, h, map_ofNat, map_ofNat]

section Assembly

variable {f : ℕ} [NeZero f] {D : ℤ}

theorem x_conj (hX : XEtaWeierstrassPair) (hCM : ShimuraMainCM) (T : TData m f D)
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (hs : ArtinCond m e σ T.s) :
    σ (ZInQ.Contrib.TYZGenus.X0.xC T.Q.tauH) = ZInQ.Contrib.TYZGenus.X0.xC T.Q'.tauH := by
  have h := transport16 T hCM e he σ hs
  simp only at h
  rcases h with h | h
  · rw [(hX T.Q.tauH).1, (hX T.Q'.tauH).1]; exact conj_two_sub_four h
  · rw [(hX T.Q.tauH).1, (hX T.Q'.tauH).2]; exact conj_two_sub_four h

theorem xW_conj (hX : XEtaWeierstrassPair) (hCM : ShimuraMainCM) (T : TData m f D)
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (hs : ArtinCond m e σ T.s) :
    σ (ZInQ.Contrib.TYZGenus.X0.xC (frickeH T.Q.tauH)) = ZInQ.Contrib.TYZGenus.X0.xC (frickeH T.Q'.tauH) := by
  have h := transport2 T hCM e he σ hs
  simp only at h
  rcases h with h | h
  · rw [(xC_fricke_wp hX T.Q.tauH).1, (xC_fricke_wp hX T.Q'.tauH).1]; exact conj_two_sub_four h
  · rw [(xC_fricke_wp hX T.Q.tauH).1, (xC_fricke_wp hX T.Q'.tauH).2]; exact conj_two_sub_four h

theorem y_conj (hX : XEtaWeierstrassPair) (hCM : ShimuraMainCM) (T : TData m f D)
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (hs : ArtinCond m e σ T.s) :
    σ (ZInQ.Contrib.TYZGenus.X0.yC T.Q.tauH) = ZInQ.Contrib.TYZGenus.X0.yC T.Q'.tauH := by
  rw [yC_formula T.Q.tauH, yC_formula T.Q'.tauH]
  simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat]
  rw [x_conj hX hCM T e he σ hs, xW_conj hX hCM T e he σ hs]

end Assembly

/-- The conclusion of `Shimura.ShimuraReciprocityModFn` for one `(N, g)` (verbatim body of
`ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean:76` with `N`, `g` fixed). -/
def _root_.X0ModuliUsed.ShimuraReciprocityModFnAt (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'

/-- **`ShimuraReciprocityModFnAt 32 g`** for any `g` that every transport conjugates correctly. -/
theorem srAt_of_conj (g : UpperHalfPlane → ℂ)
    (hconj : ∀ {m f : ℕ} [NeZero m] [NeZero f] {D : ℤ} (T : TData m f D)
      (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
      ∀ (σ : ℂ ≃+* ℂ), ArtinCond m e σ T.s → σ (g T.Q.tauH) = g T.Q'.tauH) :
    X0ModuliUsed.ShimuraReciprocityModFnAt 32 g := by
  intro m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN
  have hfin1 : finPart (1 : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) = 1 := by
    simp only [finPart, Units.val_one, Prod.snd_one]
  have hsInv : ∀ X : Set (QNeg m), {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈ latHat m X} = X →
      sInvLat m 1 X = X := by
    intro X hX
    simp only [sInvLat, hfin1, one_mul]
    exact hX
  have hlat1 : kappa m '' sInvLat m 1 (kappa m ⁻¹' (Q.lat : Set ℂ)) = (1 : ℂ) • (Q.lat : Set ℂ) := by
    rw [hsInv _ (latHatInter m hsq f D hD 32 Q), one_smul]
    exact Set.image_preimage_eq_of_subset (lat_subset_range hD Q)
  have hlatN1 : kappa m '' sInvLat m 1 (kappa m ⁻¹' (Q.latN : Set ℂ)) = (1 : ℂ) • (Q.latN : Set ℂ) := by
    rw [← latM_N, hsInv _ (latHat_inter_latM hsq hD Q (by norm_num)), one_smul]
    exact Set.image_preimage_eq_of_subset (latM_subset_range hD Q 32)
  obtain ⟨b, hb⟩ := T5Glue.fixedAlgebraic (g Q.tauH) fun σ₀ hσ₀ => by
    have hs1 : ArtinCond m e σ₀ 1 := by
      intro F _ _ _ x
      rw [show icl (1 : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) = 1 from QuotientGroup.mk_one _, map_one,
        AlgEquiv.one_apply]
      exact hσ₀ _
    exact hconj ⟨hsq, hD, Q, Q, 1, 1, one_ne_zero, hlat1, hlatN1⟩ e he σ₀ hs1
  obtain ⟨σ, hσ⟩ := T5Glue.autExtends ρ
  have hσK : ∀ k : QNeg m, σ (kappa m k) = kappa m k := by
    intro k
    rw [← kappa_eq_of_normalized e he k, hσ]
    have h1 := hρ (algebraMap (QNeg m) (ringClassField (conductorOrder (QNeg m) f)) k)
    rw [AlgEquiv.commutes] at h1
    exact congrArg ιC h1
  obtain ⟨s, hs⟩ := T5Glue.artinLift_of_abs T5Glue.absArtinSurjectiveQNeg m hsq e he σ hσK
  have hcl := ringClass_of_artin (m := m) (f := f) e σ s hs ρ hσ J hρ
  obtain ⟨c', hc', hlat, hlatN⟩ := T5Glue.ideleLatticeScale_of T5Glue.ringClassLattice
    T5Glue.invertibleColon 32 (by norm_num) m f hsq J s hcl D hD Q Q' c hL hLN
  refine ⟨b, ρ b, hb, ?_, rfl⟩
  rw [← hσ, hb]
  exact hconj ⟨hsq, hD, Q, Q', s, c', hc', hlat, hlatN⟩ e he σ hs

/-- **`ShimuraReciprocityModFn` at level 32 for x0-32's `x`**, from `ShimuraMainCM` and (Ix). -/
theorem srAt_x (hX : XEtaWeierstrass) (hCM : ShimuraMainCM) :
    X0ModuliUsed.ShimuraReciprocityModFnAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ) :=
  srAt_of_conj _ fun T e he σ hs => x_conj (xEtaWeierstrassPair_of hX) hCM T e he σ hs

/-- **`ShimuraReciprocityModFn` at level 32 for x0-32's `y`**, from `ShimuraMainCM` and (Ix). -/
theorem srAt_y (hX : XEtaWeierstrass) (hCM : ShimuraMainCM) :
    X0ModuliUsed.ShimuraReciprocityModFnAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ) :=
  srAt_of_conj _ fun T e he σ hs => y_conj (xEtaWeierstrassPair_of hX) hCM T e he σ hs

/-- `srAt_x` from the theta form of the glue. -/
theorem srAt_x_theta (hT : ThetaWeierstrass8) (hCM : ShimuraMainCM) :
    X0ModuliUsed.ShimuraReciprocityModFnAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ) :=
  srAt_x (xEtaWeierstrass_of_theta hT) hCM

/-- `srAt_y` from the theta form of the glue. -/
theorem srAt_y_theta (hT : ThetaWeierstrass8) (hCM : ShimuraMainCM) :
    X0ModuliUsed.ShimuraReciprocityModFnAt 32 (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ) :=
  srAt_y (xEtaWeierstrass_of_theta hT) hCM


end X0EtaRoute
