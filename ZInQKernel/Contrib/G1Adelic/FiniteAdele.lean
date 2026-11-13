import ZInQKernel.Contrib.G1Adelic.Basic

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum GlueVigneras
open scoped RestrictedProduct Quaternion

namespace G1Adelic.FA

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### Quaternion algebras `ℍ[R, 2, 0, -3]` are functorial in ring homomorphisms -/

section QMap

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `ℍ[R, 2, 0, -3] →+* ℍ[S, 2, 0, -3]` induced by `f : R →+* S`, coordinatewise. -/
def qmap (f : R →+* S) : ℍ[R, 2, 0, -3] →+* ℍ[S, 2, 0, -3] where
  toFun x := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [map_ofNat]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] theorem qmap_re (f : R →+* S) (x : ℍ[R, 2, 0, -3]) : (qmap f x).re = f x.re := rfl
@[simp] theorem qmap_imI (f : R →+* S) (x : ℍ[R, 2, 0, -3]) : (qmap f x).imI = f x.imI := rfl
@[simp] theorem qmap_imJ (f : R →+* S) (x : ℍ[R, 2, 0, -3]) : (qmap f x).imJ = f x.imJ := rfl
@[simp] theorem qmap_imK (f : R →+* S) (x : ℍ[R, 2, 0, -3]) : (qmap f x).imK = f x.imK := rfl

theorem qmap_comp_apply {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) (x : ℍ[R, 2, 0, -3]) :
    qmap g (qmap f x) = qmap (g.comp f) x := rfl

theorem qmap_algebraMap (f : R →+* S) (c : R) :
    qmap f (algebraMap R ℍ[R, 2, 0, -3] c) = algebraMap S ℍ[S, 2, 0, -3] (f c) := by
  ext <;> simp

end QMap

/-! ### The finite adeles `𝔸ᶠ[ℤ, ℚ]` and the places of `ℚ` -/

/-- Mathlib's finite adele ring `𝔸ᶠ[ℤ, ℚ]`. -/
abbrev AF := FiniteAdeleRing ℤ ℚ

/-- `B ⊗ 𝔸ᶠ = ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]`. -/
abbrev HA := ℍ[AF, 2, 0, -3]

/-- Mathlib's bijection between the finite places of `ℚ` and the primes. -/
noncomputable abbrev pe : HeightOneSpectrum ℤ ≃ Nat.Primes := primesEquiv

/-- Mathlib's `ℚ_v ≃ ℚ_p` (`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`), behind an
irreducible definition (an `opaque` wrapper), so that neither the elaborator nor the kernel ever
unfolds it; it is used only through `phi_def` in `mem_integers_iff`. No cast along
`primesEquiv (primesEquiv.symm p) = p` is ever needed. -/
noncomputable irreducible_def phi (v : HeightOneSpectrum ℤ) :
    v.adicCompletion ℚ ≃A[ℚ] ℚ_[((pe v : Nat.Primes) : ℕ)] :=
  adicCompletion.padicEquiv v

theorem mem_integers_iff (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔ ‖phi v x‖ ≤ 1 := by
  rw [phi_def]
  constructor
  · intro h; exact (adicCompletion.padicEquiv_bijOn v).mapsTo h
  · intro h
    obtain ⟨y, hy, hxy⟩ := (adicCompletion.padicEquiv_bijOn v).surjOn h
    rwa [(adicCompletion.padicEquiv v).injective hxy] at hy

theorem symm_mem_integers_iff (v : HeightOneSpectrum ℤ) (z : ℚ_[((pe v : Nat.Primes) : ℕ)]) :
    (phi v).symm z ∈ v.adicCompletionIntegers ℚ ↔ ‖z‖ ≤ 1 := by
  rw [mem_integers_iff, ContinuousAlgEquiv.apply_symm_apply]

/-- Evaluation `𝔸ᶠ → ℚ_v`. -/
noncomputable def evAF (v : HeightOneSpectrum ℤ) : AF →+* v.adicCompletion ℚ :=
  RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ) v

@[simp] theorem evAF_apply (v : HeightOneSpectrum ℤ) (a : AF) : evAF v a = a v := rfl

/-- Cofinite statements transfer along `primesEquiv`. -/
theorem eventually_of_pe {Q : Nat.Primes → Prop} (h : ∀ᶠ v in Filter.cofinite, Q (pe v)) :
    ∀ᶠ p in Filter.cofinite, Q p := by
  have := pe.symm.injective.tendsto_cofinite.eventually h
  simpa only [Equiv.apply_symm_apply] using this

theorem pe_eventually {Q : Nat.Primes → Prop} (h : ∀ᶠ p in Filter.cofinite, Q p) :
    ∀ᶠ v in Filter.cofinite, Q (pe v) :=
  pe.injective.tendsto_cofinite.eventually h


/-- `ℚ_p → ℚ_v` and `ℚ_v → ℚ_p` as ring homomorphisms. -/
noncomputable def phiR (v : HeightOneSpectrum ℤ) : ℚ_[((pe v : Nat.Primes) : ℕ)] →+* v.adicCompletion ℚ :=
  ((phi v).symm.toAlgEquiv.toRingEquiv : _ →+* _)

noncomputable def phiF (v : HeightOneSpectrum ℤ) : v.adicCompletion ℚ →+* ℚ_[((pe v : Nat.Primes) : ℕ)] :=
  ((phi v).toAlgEquiv.toRingEquiv : _ →+* _)

@[simp] theorem phiR_apply (v : HeightOneSpectrum ℤ) (z : ℚ_[((pe v : Nat.Primes) : ℕ)]) :
    phiR v z = (phi v).symm z := rfl

@[simp] theorem phiF_apply (v : HeightOneSpectrum ℤ) (z : v.adicCompletion ℚ) :
    phiF v z = phi v z := rfl

theorem qmap_phiF_phiR (v : HeightOneSpectrum ℤ) (x : Bp ((pe v : Nat.Primes) : ℕ)) :
    qmap (phiF v) (qmap (phiR v) x) = x := by
  ext <;> simp

theorem qmap_phiR_phiF (v : HeightOneSpectrum ℤ) (x : ℍ[v.adicCompletion ℚ, 2, 0, -3]) :
    qmap (phiR v) (qmap (phiF v) x) = x := by
  ext <;> simp

/-! ### `𝒪_p` for `p ≠ 2` is `ℤ_p⟨1, i, j, k⟩` -/

theorem std_of_mem_Op {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2) {x : Bp p} (hx : x ∈ Op p) :
    x.re ∈ PadicInt.subring p ∧ x.imI ∈ PadicInt.subring p ∧ x.imJ ∈ PadicInt.subring p ∧
      x.imK ∈ PadicInt.subring p := by
  rw [mem_Op_iff_coord] at hx
  have h2n : ‖(2 : ℚ_[p])‖ = 1 := by
    have := norm_int_eq_one (p := p) (k := 2) (by
      intro hd
      have := Int.le_of_dvd (by norm_num) hd
      have hp := (Fact.out : p.Prime).two_le
      omega)
    simpa using this
  have hJ : ‖x.imJ‖ ≤ 1 := by
    have := hx 2; simp only [coord] at this
    simpa [norm_mul, h2n] using this
  have hK : ‖x.imK‖ ≤ 1 := by
    have := hx 3; simp only [coord] at this
    simpa [norm_mul, h2n] using this
  have h0 : x.re - x.imJ ∈ PadicInt.subring p := hx 0
  have h1 : x.imI - x.imK ∈ PadicInt.subring p := hx 1
  refine ⟨?_, ?_, hJ, hK⟩
  · simpa using (PadicInt.subring p).add_mem h0 hJ
  · simpa using (PadicInt.subring p).add_mem h1 hK

theorem mem_Op_of_std {p : ℕ} [Fact p.Prime] {x : Bp p}
    (h : x.re ∈ PadicInt.subring p ∧ x.imI ∈ PadicInt.subring p ∧ x.imJ ∈ PadicInt.subring p ∧
      x.imK ∈ PadicInt.subring p) : x ∈ Op p := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have two : (2 : ℚ_[p]) ∈ PadicInt.subring p := by
    simp
  rw [mem_Op_iff_coord]
  intro k
  fin_cases k
  · exact (PadicInt.subring p).sub_mem h0 h2
  · exact (PadicInt.subring p).sub_mem h1 h3
  · exact (PadicInt.subring p).mul_mem two h2
  · exact (PadicInt.subring p).mul_mem two h3

/-! ### `ℍ[𝔸ᶠ, 2, 0, -3]` is the restricted product of the `ℍ[ℚ_v, 2, 0, -3]` -/

/-- `ℍ[ℤ_v, 2, 0, -3] ⊆ ℍ[ℚ_v, 2, 0, -3]`. -/
noncomputable def Hstd (v : HeightOneSpectrum ℤ) : Subring ℍ[v.adicCompletion ℚ, 2, 0, -3] :=
  (qmap (v.adicCompletionIntegers ℚ).toSubring.subtype).range

theorem mem_Hstd {v : HeightOneSpectrum ℤ} {x : ℍ[v.adicCompletion ℚ, 2, 0, -3]} :
    x ∈ Hstd v ↔ x.re ∈ v.adicCompletionIntegers ℚ ∧ x.imI ∈ v.adicCompletionIntegers ℚ ∧
      x.imJ ∈ v.adicCompletionIntegers ℚ ∧ x.imK ∈ v.adicCompletionIntegers ℚ := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.re.2, y.imI.2, y.imJ.2, y.imK.2⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨⟨⟨_, h0⟩, ⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩, rfl⟩

/-- `Πʳ_v [ℍ[ℚ_v, 2, 0, -3], ℍ[ℤ_v, 2, 0, -3]]`. -/
abbrev QP := Πʳ v : HeightOneSpectrum ℤ, [ℍ[v.adicCompletion ℚ, 2, 0, -3], Hstd v]

/-- A finite adele from its components. -/
def mkAF (f : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ)
    (hf : ∀ᶠ v in Filter.cofinite, f v ∈ v.adicCompletionIntegers ℚ) : AF :=
  (⟨f, hf⟩ : Πʳ v : HeightOneSpectrum ℤ, [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ])

@[simp] theorem mkAF_apply (f : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ)
    (hf : ∀ᶠ v in Filter.cofinite, f v ∈ v.adicCompletionIntegers ℚ) (v : HeightOneSpectrum ℤ) :
    mkAF f hf v = f v := rfl

/-- `QP → ℍ[𝔸ᶠ, 2, 0, -3]`. -/
noncomputable def toHA (x : QP) : HA :=
  ⟨mkAF (fun v => (x v).re) (x.2.mono fun _ h => (mem_Hstd.mp h).1),
   mkAF (fun v => (x v).imI) (x.2.mono fun _ h => (mem_Hstd.mp h).2.1),
   mkAF (fun v => (x v).imJ) (x.2.mono fun _ h => (mem_Hstd.mp h).2.2.1),
   mkAF (fun v => (x v).imK) (x.2.mono fun _ h => (mem_Hstd.mp h).2.2.2)⟩

/-- `ℍ[𝔸ᶠ, 2, 0, -3] →+* QP`, componentwise evaluation. -/
noncomputable def ofHA : HA →+* QP where
  toFun q := ⟨fun v => qmap (evAF v) q, by
    filter_upwards [FiniteAdeleRing.cofinite_mem_adicCompletionIntegers q.re,
      FiniteAdeleRing.cofinite_mem_adicCompletionIntegers q.imI,
      FiniteAdeleRing.cofinite_mem_adicCompletionIntegers q.imJ,
      FiniteAdeleRing.cofinite_mem_adicCompletionIntegers q.imK] with v h0 h1 h2 h3
    exact mem_Hstd.mpr ⟨h0, h1, h2, h3⟩⟩
  map_one' := RestrictedProduct.ext _ _ fun v => map_one (qmap (evAF v))
  map_mul' a b := RestrictedProduct.ext _ _ fun v => map_mul (qmap (evAF v)) a b
  map_zero' := RestrictedProduct.ext _ _ fun v => map_zero (qmap (evAF v))
  map_add' a b := RestrictedProduct.ext _ _ fun v => map_add (qmap (evAF v)) a b

@[simp] theorem ofHA_apply (q : HA) (v : HeightOneSpectrum ℤ) : ofHA q v = qmap (evAF v) q := rfl

/-- **`ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3] ≃+* Πʳ_v [ℍ[ℚ_v, 2, 0, -3], ℍ[ℤ_v, 2, 0, -3]]`.** -/
noncomputable def quatRP : HA ≃+* QP where
  toFun := ofHA
  invFun := toHA
  left_inv q := by ext <;> rfl
  right_inv x := RestrictedProduct.ext _ _ fun v => by ext <;> rfl
  map_mul' := map_mul ofHA
  map_add' := map_add ofHA

theorem HA_ext {a b : HA} (h : ∀ v, qmap (evAF v) a = qmap (evAF v) b) : a = b :=
  quatRP.injective (RestrictedProduct.ext _ _ h)


/-! ### Reindexing along `primesEquiv`: `B̂ = Πʳ_p [B_p, 𝒪_p] ≃+* Πʳ_v [ℍ[ℚ_v], ℍ[ℤ_v]]` -/

theorem mapsTo_qmap_phiR : ∀ᶠ v in Filter.cofinite,
    Set.MapsTo (qmap (phiR v)) (OpSub ((pe v : Nat.Primes) : ℕ) : Set _) (Hstd v) := by
  filter_upwards [pe_eventually (Filter.eventually_cofinite_ne P2)] with v hv
  intro x hx
  have h2 : ((pe v : Nat.Primes) : ℕ) ≠ 2 := fun h => hv (Subtype.ext h)
  obtain ⟨h0, h1, h2', h3⟩ := std_of_mem_Op h2 hx
  exact mem_Hstd.mpr ⟨(symm_mem_integers_iff v _).mpr h0, (symm_mem_integers_iff v _).mpr h1,
    (symm_mem_integers_iff v _).mpr h2', (symm_mem_integers_iff v _).mpr h3⟩

/-- The reindexing `B̂ →+* QP`, `y ↦ (v ↦ y_{p(v)})` read through `ℚ_p ≃ ℚ_v`. -/
noncomputable def Rd : BA →+* QP :=
  RestrictedProduct.mapAlongRingHom (fun p : Nat.Primes => Bp (p : ℕ))
    (fun v : HeightOneSpectrum ℤ => ℍ[v.adicCompletion ℚ, 2, 0, -3]) pe
    pe.injective.tendsto_cofinite (fun v => qmap (phiR v)) mapsTo_qmap_phiR

@[simp] theorem Rd_apply (y : BA) (v : HeightOneSpectrum ℤ) :
    Rd y v = qmap (phiR v) (y (pe v)) := rfl

theorem Rd_injective : Function.Injective Rd := by
  intro y₁ y₂ h
  apply RestrictedProduct.ext _ _
  intro p
  obtain ⟨v, rfl⟩ := pe.surjective p
  have := congrArg (fun z : QP => qmap (phiF v) (z v)) h
  simpa only [Rd_apply, qmap_phiF_phiR] using this

/-- A family indexed by the places, reindexed by the primes. The witness is hidden behind an
existential so that the kernel never unfolds `Equiv.piCongrLeft` (whose cast along
`primesEquiv (primesEquiv.symm p) = p` it cannot reduce). -/
theorem exists_reindex (w : ∀ v : HeightOneSpectrum ℤ, Bp ((pe v : Nat.Primes) : ℕ)) :
    ∃ y₀ : ∀ p : Nat.Primes, Bp (p : ℕ), ∀ v, y₀ (pe v) = w v :=
  ⟨Equiv.piCongrLeft (fun p : Nat.Primes => Bp (p : ℕ)) pe w,
    Equiv.piCongrLeft_apply_apply (fun p : Nat.Primes => Bp (p : ℕ)) pe w⟩

theorem Rd_surjective : Function.Surjective Rd := by
  intro z
  obtain ⟨y₀, hy₀⟩ := exists_reindex (fun v => qmap (phiF v) (z v))
  have hmem : ∀ᶠ p : Nat.Primes in Filter.cofinite, y₀ p ∈ (OpSub (p : ℕ) : Set (Bp (p : ℕ))) := by
    apply eventually_of_pe
    filter_upwards [z.2] with v hv
    rw [hy₀]
    obtain ⟨h0, h1, h2, h3⟩ := mem_Hstd.mp hv
    exact mem_Op_of_std ⟨(mem_integers_iff v _).mp h0, (mem_integers_iff v _).mp h1,
      (mem_integers_iff v _).mp h2, (mem_integers_iff v _).mp h3⟩
  refine ⟨RestrictedProduct.mk y₀ hmem, RestrictedProduct.ext _ _ fun v => ?_⟩
  rw [Rd_apply, RestrictedProduct.mk_apply, hy₀, qmap_phiR_phiF]

/-- **`B̂ ≃+* B ⊗ 𝔸ᶠ`**: t30-adelic's restricted product `Πʳ_p [B_p, 𝒪_p]` is isomorphic to
`ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]`, componentwise by Mathlib's `ℚ_v ≃ ℚ_p` and reindexed along
`primesEquiv`. -/
noncomputable def Theta : BA ≃+* HA :=
  (RingEquiv.ofBijective Rd ⟨Rd_injective, Rd_surjective⟩).trans quatRP.symm

theorem qmap_evAF_Theta (y : BA) (v : HeightOneSpectrum ℤ) :
    qmap (evAF v) (Theta y) = qmap (phiR v) (y (pe v)) := rfl

theorem Theta_re (y : BA) (v : HeightOneSpectrum ℤ) :
    (Theta y).re v = (phi v).symm (y (pe v)).re := rfl
theorem Theta_imI (y : BA) (v : HeightOneSpectrum ℤ) :
    (Theta y).imI v = (phi v).symm (y (pe v)).imI := rfl
theorem Theta_imJ (y : BA) (v : HeightOneSpectrum ℤ) :
    (Theta y).imJ v = (phi v).symm (y (pe v)).imJ := rfl
theorem Theta_imK (y : BA) (v : HeightOneSpectrum ℤ) :
    (Theta y).imK v = (phi v).symm (y (pe v)).imK := rfl


/-! ### `ℤ̂` and `𝒪̂` inside Mathlib's `𝔸ᶠ[ℤ, ℚ]` and `ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]` -/

/-- `ℤ̂ = ∏_v ℤ_v ⊆ 𝔸ᶠ[ℤ, ℚ]`. -/
def ZhatAF : Set AF := {a | ∀ v : HeightOneSpectrum ℤ, a v ∈ v.adicCompletionIntegers ℚ}

/-- Coordinates in N5's basis `1, i, (1 + j)/2, (i + ij)/2` of the order `𝒪`:
`x = c₀ + c₁ i + c₂ (1 + j)/2 + c₃ (i + ij)/2` with `c = qcoord x`. -/
def qcoord {R : Type*} [CommRing R] (x : ℍ[R, 2, 0, -3]) : Fin 4 → R :=
  ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK]

theorem qcoord_qmap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : ℍ[R, 2, 0, -3])
    (k : Fin 4) : qcoord (qmap f x) k = f (qcoord x k) := by
  fin_cases k <;> simp [qcoord, map_ofNat]

theorem coord_eq_qcoord (p : ℕ) [Fact p.Prime] (x : Bp p) : coord p x = qcoord x := rfl

/-- **`𝒪̂ = 𝒪 ⊗ ℤ̂ ⊆ B ⊗ 𝔸ᶠ`**: the elements of `ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]` whose coordinates in N5's
basis of `𝒪` lie in `ℤ̂`. -/
def OhatAF : Set HA := {x | ∀ k, qcoord x k ∈ ZhatAF}

theorem qcoord_Theta_apply (y : BA) (k : Fin 4) (v : HeightOneSpectrum ℤ) :
    (qcoord (Theta y) k) v = (phi v).symm (coord ((pe v : Nat.Primes) : ℕ) (y (pe v)) k) := by
  rw [← evAF_apply, ← qcoord_qmap, qmap_evAF_Theta, qcoord_qmap, phiR_apply, coord_eq_qcoord]

theorem Theta_mem_OhatAF (y : BA) : Theta y ∈ OhatAF ↔ y ∈ Ohat := by
  simp only [OhatAF, ZhatAF, Ohat, Set.mem_ofPred_eq, qcoord_Theta_apply, symm_mem_integers_iff]
  rw [← pe.forall_congr_right]
  simp only [mem_Op_iff_coord]
  exact ⟨fun h v k => h k v, fun h k v => h v k⟩

theorem mem_OhatAF_iff (x : HA) : x ∈ OhatAF ↔ Theta.symm x ∈ Ohat := by
  rw [← Theta_mem_OhatAF, RingEquiv.apply_symm_apply]

/-- `𝒪̂` as a subring of `ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]`. -/
noncomputable def OhatSubAF : Subring HA where
  carrier := OhatAF
  mul_mem' {a b} ha hb := by
    rw [mem_OhatAF_iff] at *
    rw [map_mul]
    exact fun p => (OpSub (p : ℕ)).mul_mem (ha p) (hb p)
  one_mem' := by
    rw [mem_OhatAF_iff, map_one]; exact fun p => (OpSub (p : ℕ)).one_mem
  add_mem' {a b} ha hb := by
    rw [mem_OhatAF_iff] at *
    rw [map_add]
    exact fun p => (OpSub (p : ℕ)).add_mem (ha p) (hb p)
  zero_mem' := by
    rw [mem_OhatAF_iff, map_zero]; exact fun p => (OpSub (p : ℕ)).zero_mem
  neg_mem' {a} ha := by
    rw [mem_OhatAF_iff] at *
    rw [map_neg]
    exact fun p => (OpSub (p : ℕ)).neg_mem (ha p)

/-! ### The subgroups `N`, `K₀`, `𝔸ᶠ^×`, `K₃` of `(B ⊗ 𝔸ᶠ)^×` -/

/-- The normalizer `N = {x ∈ (B ⊗ 𝔸ᶠ)^× : x 𝒪̂ x⁻¹ = 𝒪̂}`. -/
noncomputable def NAF : Subgroup HAˣ where
  carrier := {x | ∀ y : HA, y ∈ OhatAF ↔ (x : HA) * y * ((x⁻¹ : HAˣ) : HA) ∈ OhatAF}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro a b ha hb y
    rw [hb y, ha]
    simp only [Units.val_mul, mul_inv_rev]
    simp only [mul_assoc]
  inv_mem' := by
    intro a ha y
    simp only [inv_inv]
    have : (a : HA) * ((((a⁻¹ : HAˣ) : HA)) * y * (a : HA)) * ((a⁻¹ : HAˣ) : HA) = y := by
      simp only [← mul_assoc, Units.mul_inv, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [ha (((a⁻¹ : HAˣ) : HA) * y * (a : HA)), this]

/-- `K₀ = 𝒪̂^×`. -/
noncomputable def K0AF : Subgroup HAˣ := OhatSubAF.toSubmonoid.units

/-- `𝔸ᶠ[ℤ, ℚ]^×`, the central scalars of `(B ⊗ 𝔸ᶠ)^×`. -/
noncomputable def ZAF : Subgroup HAˣ := (Units.map (algebraMap AF HA : AF →* HA)).range

/-- `K₃ = {u ∈ 𝒪̂^× : u ≡ 1 mod 3𝒪̂}`. -/
noncomputable def K3AF : Subgroup HAˣ where
  carrier := {u | u ∈ K0AF ∧ ∃ w ∈ OhatAF, (u : HA) - 1 = 3 * w}
  one_mem' := ⟨K0AF.one_mem, 0, OhatSubAF.zero_mem, by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, w, hw, huw⟩ ⟨hv, w', hw', hvw⟩
    refine ⟨K0AF.mul_mem hu hv, w * (v : HA) + w', ?_, ?_⟩
    · exact OhatSubAF.add_mem (OhatSubAF.mul_mem hw ((Submonoid.mem_units_iff _ _).mp hv).1) hw'
    · rw [Units.val_mul, show (u : HA) * v - 1 = ((u : HA) - 1) * v + ((v : HA) - 1) by
        rw [sub_mul, one_mul]; abel, huw, hvw, mul_add, mul_assoc]
  inv_mem' := by
    rintro u ⟨hu, w, hw, huw⟩
    refine ⟨K0AF.inv_mem hu, -(((u⁻¹ : HAˣ) : HA) * w), ?_, ?_⟩
    · exact OhatSubAF.neg_mem (OhatSubAF.mul_mem ((Submonoid.mem_units_iff _ _).mp hu).2 hw)
    · have h1 : ((u⁻¹ : HAˣ) : HA) * (u : HA) = 1 := Units.inv_mul u
      rw [show ((u⁻¹ : HAˣ) : HA) - 1 = -(((u⁻¹ : HAˣ) : HA) * ((u : HA) - 1)) by
        rw [mul_sub, h1, mul_one, neg_sub], huw]
      noncomm_ring


/-! ### Transport along `Theta` -/

/-- `Theta` on units: `B̂^× ≃* (B ⊗ 𝔸ᶠ)^×`. -/
noncomputable def ThetaU : BAˣ ≃* HAˣ := Units.mapEquiv Theta.toMulEquiv

theorem ThetaU_val (x : BAˣ) : (ThetaU x : HA) = Theta x := rfl

theorem ThetaU_inv_val (x : BAˣ) : (((ThetaU x)⁻¹ : HAˣ) : HA) = Theta ((x⁻¹ : BAˣ) : BA) := by
  rw [← map_inv]; rfl

theorem map_eq_of_mem_iff {H : Subgroup BAˣ} {H' : Subgroup HAˣ} (h : ∀ y, ThetaU y ∈ H' ↔ y ∈ H) :
    H.map ThetaU.toMonoidHom = H' := by
  ext x
  rw [Subgroup.mem_map_equiv, ← h, MulEquiv.apply_symm_apply]

theorem mem_NAF_iff (y : BAˣ) : ThetaU y ∈ NAF ↔ y ∈ Nhat := by
  change (∀ z : HA, z ∈ OhatAF ↔ (ThetaU y : HA) * z * (((ThetaU y)⁻¹ : HAˣ) : HA) ∈ OhatAF) ↔
    ∀ z : BA, z ∈ Ohat ↔ (y : BA) * z * ((y⁻¹ : BAˣ) : BA) ∈ Ohat
  rw [← Theta.toEquiv.forall_congr_right]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ThetaU_val, ThetaU_inv_val, ← map_mul,
    Theta_mem_OhatAF]

theorem mem_K0AF_iff (y : BAˣ) : ThetaU y ∈ K0AF ↔ y ∈ K0 := by
  rw [K0AF, Submonoid.mem_units_iff]
  change Theta y ∈ OhatAF ∧ (((ThetaU y)⁻¹ : HAˣ) : HA) ∈ OhatAF ↔ _
  rw [ThetaU_inv_val, Theta_mem_OhatAF, Theta_mem_OhatAF]
  rfl

theorem scalar_iff (y : BA) : (∀ p : Nat.Primes, ∃ c : ℚ_[(p : ℕ)], y p = algebraMap _ _ c) ↔
    ∃ a : AF, Theta y = algebraMap AF HA a := by
  constructor
  · intro h
    refine ⟨(Theta y).re, HA_ext fun v => ?_⟩
    rw [qmap_evAF_Theta, qmap_algebraMap]
    obtain ⟨c, hc⟩ := h (pe v)
    rw [hc, qmap_algebraMap, evAF_apply, Theta_re, hc]
    simp [QuaternionAlgebra.algebraMap_eq]
  · rintro ⟨a, ha⟩ p
    obtain ⟨v, rfl⟩ := pe.surjective p
    have h1 := congrArg (qmap (evAF v)) ha
    rw [qmap_evAF_Theta, qmap_algebraMap] at h1
    have h2 := congrArg (qmap (phiF v)) h1
    rw [qmap_phiF_phiR, qmap_algebraMap] at h2
    exact ⟨_, h2⟩

theorem mem_ZAF_iff (y : BAˣ) : ThetaU y ∈ ZAF ↔ y ∈ Zhat := by
  constructor
  · rintro ⟨a, ha⟩
    exact (scalar_iff (y : BA)).mpr ⟨a, by rw [← ThetaU_val, ← ha]; rfl⟩
  · intro hy
    obtain ⟨a₁, h₁⟩ := (scalar_iff (y : BA)).mp hy
    obtain ⟨a₂, h₂⟩ := (scalar_iff ((y⁻¹ : BAˣ) : BA)).mp (Zhat.inv_mem hy)
    have e1 : a₁ * a₂ = 1 := by
      apply QuaternionAlgebra.algebraMap_injective (c₁ := (2 : AF)) (c₂ := 0) (c₃ := -3)
      rw [map_mul, ← h₁, ← h₂, ← map_mul, Units.mul_inv, map_one, map_one]
    have e2 : a₂ * a₁ = 1 := by rw [mul_comm, e1]
    refine ⟨⟨a₁, a₂, e1, e2⟩, Units.ext ?_⟩
    change algebraMap AF HA a₁ = Theta y
    rw [h₁]


theorem qcoord_algebraMap_mul (a : AF) (z : HA) (k : Fin 4) :
    qcoord (algebraMap AF HA a * z) k = a * qcoord z k := by
  fin_cases k <;> simp [qcoord, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem norm_third_coord_le {y : BAˣ} (hy : y ∈ K3) (p : Nat.Primes) (k : Fin 4) :
    ‖((1 / 3 : ℚ) : ℚ_[(p : ℕ)]) * coord (p : ℕ) ((y : BA) p - 1) k‖ ≤ 1 := by
  by_cases h : p = P3
  · subst h
    obtain ⟨n, hn⟩ := hy.2
    rw [hn, GlueVigneras.coord_smul, coord_combp, ← mul_assoc,
      show ((1 / 3 : ℚ) : ℚ_[q3]) * 3 = 1 by push_cast; norm_num, one_mul]
    exact PadicInt.norm_le_one _
  · have h3 : ‖((1 / 3 : ℚ) : ℚ_[(p : ℕ)])‖ = 1 := by
      have := norm_int_eq_one (p := (p : ℕ)) (k := 3) (by
        intro hd
        have hd' : (p : ℕ) ∣ 3 := by exact_mod_cast hd
        have := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_three).mp hd'
        exact h (Subtype.ext this))
      push_cast
      rw [norm_div, norm_one]
      simp only [Int.cast_ofNat] at this
      rw [this, div_one]
    have hm : (y : BA) p - 1 ∈ Op (p : ℕ) :=
      (OpSub (p : ℕ)).sub_mem (hy.1.1 p) (OpSub (p : ℕ)).one_mem
    rw [norm_mul, h3, one_mul]
    exact (mem_Op_iff_coord _ _).mp hm k

theorem mem_K3AF_iff (y : BAˣ) : ThetaU y ∈ K3AF ↔ y ∈ K3 := by
  constructor
  · rintro ⟨hK, w, hw, hwy⟩
    refine ⟨(mem_K0AF_iff y).mp hK, ?_⟩
    rw [mem_OhatAF_iff] at hw
    have e : (y : BA) - 1 = 3 * Theta.symm w := by
      apply Theta.injective
      rw [map_sub, map_one, map_mul, map_ofNat, RingEquiv.apply_symm_apply, ← hwy]
      rfl
    have e3 := congrArg (RestrictedProduct.evalRingHom (fun p : Nat.Primes => Bp (p : ℕ)) P3) e
    simp only [map_sub, map_one, map_mul, map_ofNat, RestrictedProduct.evalRingHom_apply] at e3
    obtain ⟨n, hn⟩ := hw P3
    refine ⟨n, ?_⟩
    rw [e3, ← hn, Algebra.smul_def, map_ofNat]
  · intro hy
    refine ⟨(mem_K0AF_iff y).mpr hy.1,
      algebraMap AF HA (algebraMap ℚ AF (1 / 3)) * Theta ((y : BA) - 1), ?_, ?_⟩
    · intro k v
      rw [qcoord_algebraMap_mul, ← evAF_apply, map_mul, evAF_apply, evAF_apply,
        qcoord_Theta_apply, mem_integers_iff, map_mul, ContinuousAlgEquiv.apply_symm_apply]
      have hv : (algebraMap ℚ AF (1 / 3)) v = algebraMap ℚ (v.adicCompletion ℚ) (1 / 3) := rfl
      rw [hv, AlgHomClass.commutes, eq_ratCast]
      have := norm_third_coord_le hy (pe v) k
      rwa [show ((y : BA) - 1) (pe v) = (y : BA) (pe v) - 1 from rfl]
    · have h3 : (3 : HA) * algebraMap AF HA (algebraMap ℚ AF (1 / 3)) = 1 := by
        have : (3 : AF) * algebraMap ℚ AF (1 / 3) = 1 := by
          rw [← map_ofNat (algebraMap ℚ AF) 3, ← map_mul]; norm_num
        have h' := congrArg (algebraMap AF HA) this
        rwa [map_mul, map_ofNat, map_one] at h'
      rw [← mul_assoc, h3, one_mul, map_sub, map_one]
      rfl

/-! ### The count over Mathlib's `𝔸ᶠ[ℤ, ℚ]` -/

theorem map_Nhat : Nhat.map ThetaU.toMonoidHom = NAF := map_eq_of_mem_iff mem_NAF_iff
theorem map_K0 : K0.map ThetaU.toMonoidHom = K0AF := map_eq_of_mem_iff mem_K0AF_iff
theorem map_Zhat : Zhat.map ThetaU.toMonoidHom = ZAF := map_eq_of_mem_iff mem_ZAF_iff
theorem map_K3 : K3.map ThetaU.toMonoidHom = K3AF := map_eq_of_mem_iff mem_K3AF_iff

/-- **`[N : 𝔸ᶠ^× K₀] = 4`** over `ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]`. -/
theorem relIndex_eq_four_AF : (ZAF ⊔ K0AF).relIndex NAF = 4 := by
  rw [← map_Zhat, ← map_K0, ← map_Nhat, ← Subgroup.map_sup,
    Subgroup.relIndex_map_map_of_injective (f := ThetaU.toMonoidHom) _ _ ThetaU.injective]
  exact relIndex_eq_four

/-- **`[K₀ : (𝔸ᶠ^× ∩ K₀) K₃] = 36`** over `ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]`. -/
theorem relIndex_K3_AF : ((ZAF ⊓ K0AF) ⊔ K3AF).relIndex K0AF = 36 := by
  rw [← map_Zhat, ← map_K0, ← map_K3, ← Subgroup.map_inf_eq _ _ ThetaU.toMonoidHom ThetaU.injective,
    ← Subgroup.map_sup, Subgroup.relIndex_map_map_of_injective (f := ThetaU.toMonoidHom) _ _ ThetaU.injective]
  exact relIndex_K3

/-- **`|Γ'| = [N : 𝔸ᶠ^× K₃] = 144`** over Mathlib's finite adeles: `N` the normalizer of
`𝒪̂ = 𝒪 ⊗ ℤ̂` in `(B ⊗ 𝔸ᶠ)^× = ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]^×`, `𝔸ᶠ[ℤ, ℚ]^×` the central scalars,
`K₃ = {u ∈ 𝒪̂^× : u ≡ 1 mod 3𝒪̂}`. -/
theorem gamma_order_AF : (ZAF ⊔ K3AF).relIndex NAF = 144 := by
  rw [← map_Zhat, ← map_K3, ← map_Nhat, ← Subgroup.map_sup,
    Subgroup.relIndex_map_map_of_injective (f := ThetaU.toMonoidHom) _ _ ThetaU.injective]
  exact gamma_order

end G1Adelic.FA

#print axioms G1Adelic.FA.Theta
#print axioms G1Adelic.FA.gamma_order_AF
#print axioms G1Adelic.FA.relIndex_eq_four_AF
#print axioms G1Adelic.FA.relIndex_K3_AF
