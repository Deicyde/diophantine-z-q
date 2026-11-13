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

end G1Adelic.FA
