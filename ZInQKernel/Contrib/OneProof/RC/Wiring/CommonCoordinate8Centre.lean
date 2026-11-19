import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate7

/-!
# Theorem 5.3, Lane RC32 round 5: the centre of an embedding `ℚ̄ → ℚ̄_r`

The round-four input `DecompositionFrobeniusQ r hr` (`CommonCoordinate7LocalGlobal.lean`) asks,
for every arithmetic Frobenius `h ∈ G_ℚ` at `r` (the tree's `ChebFD.C10.IsFrobAt h r`: a prime `P`
of `ℤ̄` over `r` with `h x ≡ x^r (mod P)` for all `x ∈ ℤ̄`), for an embedding `ι : ℚ̄ → ℚ̄_r`, a
valuation `w` of `ℚ̄_r` extending `v_r`, and an arithmetic Frobenius `σ` of `Gal(ℚ̄_r/ℚ_r)` for `w`
(the RC53 group's `IsArithmeticFrobeniusOnClosureQ`: `w(σ y − y^r) < 1` whenever `w(y) ≤ 1`) with
`σ ∘ ι = ι ∘ h`. This file carries out the first two steps of the classical argument (Neukirch,
*Algebraic Number Theory*, II.8–9; Serre, *Local Fields*, II §3), for any valuation `w` of `ℚ̄_r`
extending `v_r`:

* `IsFrobAtC10.smul_le`, `IsFrobAtC10.smul_eq`: a Frobenius element at `P` lies in the
  decomposition group of `P` (`h • P = P`);
* `ExtendsVr w`; `intCast_le_one`, `intCast_lt_one_iff`: on `ℤ`, `w` is the `r`-adic valuation;
* `le_one_of_mem_Zbar`: `w(ι x) ≤ 1` on `ℤ̄` (valuation rings are integrally closed);
* `centre w ι`: the prime `{x ∈ ℤ̄ : w(ι x) < 1}` of `ℤ̄`, over `r` (`centre_under`);
* `exists_embedding_centre`: for every prime `P` of `ℤ̄` over `r` there is an embedding with
  centre `P` (any embedding composed with an element of `G_ℚ`; `G_ℚ` acts transitively on the primes
  of `ℤ̄` over `r`, Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` with lane
  RC24's `G_ℚ`-invariance of `ℤ̄`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.AddressGenuine (Zbar coe_smul_Zbar)
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary (primeIdealQ valued_algebraMap_Q)
open scoped WithZero Pointwise

/-! ## Frobenius elements lie in the decomposition group -/

/-- `C10.IsFrobAt h r` at a given prime `P` of `ℤ̄`: `h x − x^r ∈ P` for every `x ∈ ℤ̄`. -/
def FrobAtPrime (h : GalQ) (r : ℕ) (P : Ideal Zbar) : Prop :=
  P.IsPrime ∧ P.under ℤ = Ideal.span {(r : ℤ)} ∧ ∀ x : Zbar, h • x - x ^ r ∈ P

/-- **The tree's Frobenius predicate, unpacked** (PROVED): `C10.IsFrobAt h r` says there is a prime
`P` of `ℤ̄` over `r` with `h x − x^r ∈ P` for every `x ∈ ℤ̄`. -/
theorem isFrobAtC10_iff (h : GalQ) (r : ℕ) :
    ZInQ.Contrib.ChebFD.C10.IsFrobAt h r ↔ ∃ P : Ideal Zbar, FrobAtPrime h r P := by
  constructor
  · rintro ⟨P, hP, hPr, hF⟩
    refine ⟨P, hP, hPr, fun x => hF x _ ?_⟩
    push_cast
    rw [coe_smul_Zbar]
  · rintro ⟨P, hP, hPr, hF⟩
    refine ⟨P, hP, hPr, fun x y hy => ?_⟩
    have : y = h • x - x ^ r := by
      apply Subtype.ext
      rw [hy]
      push_cast
      rw [coe_smul_Zbar]
    rw [this]
    exact hF x

/-- A Frobenius element at `P` maps `P` into `P` (PROVED): `h x = (h x − x^r) + x^r`. -/
theorem FrobAtPrime.smul_mem {h : GalQ} {r : ℕ} {P : Ideal Zbar} (hF : FrobAtPrime h r P)
    (hr : 0 < r) {x : Zbar} (hx : x ∈ P) : h • x ∈ P := by
  have : h • x = (h • x - x ^ r) + x ^ r := by ring
  rw [this]
  exact P.add_mem (hF.2.2 x) (P.pow_mem_of_mem hx r hr)

/-- The primes of `ℤ̄` over a rational prime are maximal (PROVED: `ℤ̄` is integral over `ℤ`). -/
theorem isMaximal_of_under {r : ℕ} (hr : r.Prime) {P : Ideal Zbar} [P.IsPrime]
    (hP : P.under ℤ = Ideal.span {(r : ℤ)}) : P.IsMaximal := by
  have := Fact.mk hr
  have : (P.under ℤ).IsMaximal := by
    rw [hP]
    exact Int.ideal_span_isMaximal_of_prime r
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap ℤ Zbar)
    (Algebra.IsIntegral.isIntegral (R := ℤ) (A := Zbar)) P this

/-- **A Frobenius element at `P` lies in the decomposition group of `P`** (PROVED): `h • P ≤ P`, and
both are maximal. -/
theorem FrobAtPrime.smul_eq {h : GalQ} {r : ℕ} (hr : r.Prime) {P : Ideal Zbar}
    (hF : FrobAtPrime h r P) : h • P = P := by
  have := hF.1
  have hmax := isMaximal_of_under hr hF.2.1
  have hle : h • P ≤ P := by
    intro y hy
    rw [Ideal.pointwise_smul_eq_comap] at hy
    have : y = h • (h⁻¹ • y) := by rw [smul_inv_smul]
    rw [this]
    exact hF.smul_mem hr.pos hy
  have hne : h • P ≠ ⊤ := by
    intro htop
    have h1 : (1 : Zbar) ∈ h • P := by rw [htop]; exact Submodule.mem_top
    rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap, map_one] at h1
    exact hmax.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hmax' : (h • P).IsMaximal := by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ (MulSemiringAction.toRingEquiv _ _ h⁻¹).surjective
  exact hmax'.eq_of_le hmax.ne_top hle

/-! ## Valuations of `ℚ̄_r` extending `v_r`, and the centre of an embedding -/

section Centre

variable {r : ℕ} {hr : r.Prime}

/-- A valuation `w` of `ℚ̄_r` extends `v_r` (up to equivalence) — the hypothesis of the RC53 group's
dictionary. -/
def ExtendsVr {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation (Qrbar r hr) Γ) :
    Prop :=
  (w.comap (algebraMap (Qr r hr) (Qrbar r hr))).IsEquiv (Valued.v : Valuation (Qr r hr) ℤᵐ⁰)

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {w : Valuation (Qrbar r hr) Γ}

theorem valued_intCast (n : ℤ) :
    (Valued.v : Valuation (Qr r hr) ℤᵐ⁰) (n : Qr r hr) =
      (primeIdealQ r hr).intValuation (n : 𝓞 ℚ) := by
  have h1 : ((n : ℚ) : Qr r hr) = (n : Qr r hr) := by push_cast; rfl
  rw [← h1]
  change Valued.v (algebraMap ℚ (Qr r hr) (n : ℚ)) = _
  rw [valued_algebraMap_Q, ← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)]
  simp

/-- `w ≤ 1` on `ℤ` (PROVED). -/
theorem intCast_le_one (hw : ExtendsVr w) (n : ℤ) : w (n : Qrbar r hr) ≤ 1 := by
  have h := (Valuation.IsEquiv.le_one_iff_le_one hw (x := (n : Qr r hr))).mpr (by
    rw [valued_intCast]; exact HeightOneSpectrum.intValuation_le_one _ _)
  simpa using h

/-- `w(n) < 1` exactly when `r ∣ n` (PROVED). -/
theorem intCast_lt_one_iff (hw : ExtendsVr w) (n : ℤ) :
    w (n : Qrbar r hr) < 1 ↔ (r : ℤ) ∣ n := by
  have h := Valuation.IsEquiv.lt_one_iff_lt_one hw (x := (n : Qr r hr))
  simp only [Valuation.comap_apply, map_intCast] at h
  rw [h, valued_intCast, ← intCast_mem_primeIdealQ_iff hr]
  exact (primeIdealQ r hr).intValuation_lt_one_iff_mem (n : 𝓞 ℚ)

/-- **`w(ι x) ≤ 1` on `ℤ̄`** (PROVED): `ι x` is integral over `ℤ`, hence over the valuation ring
of `w`, which is integrally closed. -/
theorem le_one_of_mem_Zbar (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (x : Zbar) :
    w (ι x) ≤ 1 := by
  have hint : IsIntegral ℤ (ι (x : Qbar)) := by
    have h := x.2
    exact h.map (ι.restrictScalars ℤ)
  have hZ : ∀ n : ℤ, algebraMap ℤ (Qrbar r hr) n ∈ w.integer := fun n => by
    rw [eq_intCast]; exact intCast_le_one hw n
  let f : ℤ →+* w.integer := (algebraMap ℤ (Qrbar r hr)).codRestrict w.integer hZ
  let _ : Algebra ℤ w.integer := f.toAlgebra
  have hint' : IsIntegral w.integer (ι (x : Qbar)) := by
    obtain ⟨p, hp, hp0⟩ := hint
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hp0 using 2
    exact RingHom.ext_int _ _
  exact (Valuation.integer.integers w).mem_of_integral hint'

/-- **The centre of an embedding** (definition): `{x ∈ ℤ̄ : w(ι x) < 1}`. -/
def centre (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) : Ideal Zbar where
  carrier := {x | w (ι x) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, map_add] at ha hb ⊢
    exact lt_of_le_of_lt (w.map_add _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul] at hx ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (le_one_of_mem_Zbar hw ι c)) hx

theorem mem_centre (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (x : Zbar) :
    x ∈ centre hw ι ↔ w (ι x) < 1 := Iff.rfl

/-- The centre is a prime ideal (PROVED). -/
instance centre_isPrime (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) :
    (centre hw ι).IsPrime where
  ne_top' h := by
    have h1 : (1 : Zbar) ∈ centre hw ι := by rw [h]; exact Submodule.mem_top
    rw [mem_centre] at h1
    simp at h1
  mem_or_mem' {x y} hxy := by
    rw [mem_centre, mem_centre]
    rw [mem_centre, Subalgebra.coe_mul, map_mul, map_mul] at hxy
    by_contra hcon
    push Not at hcon
    have hx := le_antisymm (le_one_of_mem_Zbar hw ι x) hcon.1
    have hy := le_antisymm (le_one_of_mem_Zbar hw ι y) hcon.2
    rw [hx, hy, mul_one] at hxy
    exact lt_irrefl _ hxy

/-- **The centre lies over `r`** (PROVED). -/
theorem centre_under (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) :
    (centre hw ι).under ℤ = Ideal.span {(r : ℤ)} := by
  ext n
  rw [Ideal.under_def, Ideal.mem_comap, mem_centre, Ideal.mem_span_singleton, eq_intCast]
  have : ι ((n : Zbar) : Qbar) = (n : Qrbar r hr) := by
    rw [show ((n : Zbar) : Qbar) = (n : Qbar) by push_cast; rfl, map_intCast]
  rw [this]
  exact intCast_lt_one_iff hw n

/-- Composing with `g ∈ G_ℚ` moves the centre by `g⁻¹` (PROVED). -/
theorem centre_comp (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ) :
    ∀ x : Zbar, x ∈ centre hw (ι.comp (g : Qbar →ₐ[ℚ] Qbar)) ↔ g • x ∈ centre hw ι := by
  intro x
  rw [mem_centre, mem_centre, coe_smul_Zbar]
  rfl

/-- **An embedding with a prescribed centre** (PROVED): for every prime `P` of `ℤ̄` over `r` there
is a `ℚ`-embedding `ι : ℚ̄ → ℚ̄_r` with centre `P` — any embedding composed with an element of
`G_ℚ`, which acts transitively on the primes of `ℤ̄` over `r`. -/
theorem exists_embedding_centre (hw : ExtendsVr w) (P : Ideal Zbar) [P.IsPrime]
    (hP : P.under ℤ = Ideal.span {(r : ℤ)}) :
    ∃ ι : Qbar →ₐ[ℚ] Qrbar r hr, centre hw ι = P := by
  let ι₀ : Qbar →ₐ[ℚ] Qrbar r hr := IsAlgClosed.lift
  let _ : TopologicalSpace Zbar := ⊥
  have : DiscreteTopology Zbar := ⟨rfl⟩
  have : ContinuousSMul GalQ Zbar := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) (x : Qbar) using 1
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ)
    (G := GalQ) P (centre hw ι₀) (by rw [hP, centre_under])
  refine ⟨ι₀.comp (g : Qbar →ₐ[ℚ] Qbar), Ideal.ext fun x => ?_⟩
  rw [centre_comp, hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]

end Centre

end ZInQ.Manuscript.RC.Wiring
