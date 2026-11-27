import ZInQKernel.Contrib.OneProof.RayClassShimura
import ZInQKernel.Contrib.OneProof.GR512Bridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Conductor
import Mathlib.LinearAlgebra.Unimodular

/-!
# The ring-class kernel of an idele with `q̂(s) ∈ 𝒪̂^×`

Let `K` be a quadratic field, `q : K → B` an embedding of `ℚ`-algebras into
`B = (2, −3 | ℚ)`, and `R = q⁻¹(𝒪)` the order of `K` cut out by the maximal order `𝒪` of `B`.
For an idele `s` of `K` with `q̂(s), q̂(s)⁻¹ ∈ 𝒪̂`, the class of `s` lies in the kernel of the
ring-class quotient `C_K → Pic R`; hence its Artin symbol on the ring class field of `R` is
trivial (`ringClassIdeleQuotient_mk_eq_one`, `ideleClassArtinMap_ringClassField_eq_one`).

*Proof.* Write `𝒪_K = ℤ ⊕ ℤω` and let `f` be the index of `R` in `𝒪_K`, so that
`R = ℤ + f𝒪_K`. The lattice `q(R) = q(K) ∩ 𝒪` is saturated in `𝒪`; in the coordinates
`c = (c₀, c₁, c₂, c₃)` of `q(ω)` in the basis `1, i, (1+j)/2, (i+k)/2` of `𝒪` this says that
`f c ∈ ℤ⁴` and that `f c₁, f c₂, f c₃` are coprime (`saturation`, `exists_bezout`). A finite
adele of `K` is `x = a₀ + a₁ω` with `aᵢ ∈ 𝔸_f`, and `q̂(x)` has coordinates
`(a₀ + a₁c₀, a₁c₁, a₁c₂, a₁c₃)`; so `q̂(x) ∈ 𝒪̂` forces `a₁ ∈ fℤ̂` and `a₀ ∈ ℤ̂`, that is,
`x = m + f z` with `m ∈ ℤ` and `z` integral (`exists_int_add_index_mul`). Applied to `s` and
`s⁻¹`, this shows that `s` is a unit at every finite place and that `m` is prime to `f`. Then
`m s⁻¹ ≡ 1` modulo the conductor `f𝒪_K`, so the ray class of `s⁻¹` modulo the conductor is the
class of the ideal `m𝒪_K`, which has the generator `m ∈ R`.

The two side conditions on `R` are proved as well: `R ⊆ 𝒪_K` because elements of `𝒪` are integral
over `ℤ` (`comap_le_integralClosure`), and `[𝒪_K : R] ≠ 0` because every element of `K` has a
positive integer multiple in `R` (`conductor_comap_ne_zero`). The main results are stated with
these two conditions as hypotheses and, with primed names, unconditionally.
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
open ShimuraCFT RayClassCFT
open scoped TensorProduct FiniteAdeleExtension

/-! ## Coordinates on `B ⊗ R` -/

section Coord

variable {R : Type*} [CommRing R]

theorem cQ_add' (x y : ShimuraGlue.BR R) : cQ (x + y) = cQ x + cQ y := by
  funext i
  fin_cases i <;> simp [cQ] <;> ring

theorem cQ_algebraMap_mul (a : R) (x : ShimuraGlue.BR R) :
    cQ (algebraMap R (ShimuraGlue.BR R) a * x) = fun i => a * cQ x i := by
  rw [← Algebra.smul_def]
  funext i
  fin_cases i <;> simp [cQ] <;> ring

theorem cQ_algebraMap (a : R) :
    cQ (algebraMap R (ShimuraGlue.BR R) a) = ![a, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [cQ, QuaternionAlgebra.algebraMap_eq]

end Coord

/-! ## Finite adeles of `K` -/

section Adeles

variable {K : Type} [Field K] [NumberField K]

/-- Evaluation of a finite adele at a finite place, as a ring homomorphism. -/
def evK (w : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K →+* w.adicCompletion K where
  toFun a := a w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evK_apply (w : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 K) K) :
    evK w a = a w := rfl

/-- The extension to `K` of an element of `ℤ̂` is integral at every finite place. -/
theorem extension_mem_integers {a : AQ} (ha : a ∈ ZhatQ) (w : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleExtension (𝓞 ℚ) ℚ (𝓞 K) K a w ∈ w.adicCompletionIntegers K := by
  rw [finiteAdeleExtension_apply]
  exact adicCompletionExtension_mem_adicCompletionIntegers ℚ K (w.under (𝓞 ℚ)) w ⟨_, ha _⟩

/-- An algebraic integer is integral at every finite place. -/
theorem algebraMap_mem_integers (y : 𝓞 K) (w : HeightOneSpectrum (𝓞 K)) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (y : K) w ∈ w.adicCompletionIntegers K := by
  rw [FiniteAdeleRing.algebraMap_apply, mem_adicCompletionIntegers,
    valuedAdicCompletion_eq_valuation']
  exact valuation_le_one w y

/-- Base change of finite adeles on pure tensors. -/
theorem baseChange_tmul (a : AQ) (k : K) :
    finiteAdeleBaseChangeAlgEquiv ℚ K (a ⊗ₜ k) =
      finiteAdeleExtension (𝓞 ℚ) ℚ (𝓞 K) K a * algebraMap K (FiniteAdeleRing (𝓞 K) K) k :=
  finiteAdeleBaseChangeHom_tmul ℚ K a k

/-- `q̂` on pure tensors. -/
theorem qT_tmul (q : K →ₐ[ℚ] LeafQM.B) (a : AQ) (k : K) :
    qT q (a ⊗ₜ k) = algebraMap AQ BAQ a * bEmb (q k) := by
  simp only [qT, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.comp_apply]

/-- Every element of `𝔸_f ⊗ K` is `a₀ ⊗ 1 + a₁ ⊗ ω` for a non-rational `ω`. -/
theorem tmul_decomp (hK : Module.finrank ℚ K = 2) {ω : K} (hω : ∀ r : ℚ, ω ≠ r)
    (x : AQ ⊗[ℚ] K) : ∃ a₀ a₁ : AQ, x = a₀ ⊗ₜ (1 : K) + a₁ ⊗ₜ ω := by
  induction x using TensorProduct.inductionOn with
  | tmul a k =>
    obtain ⟨r, t, rfl⟩ := exists_rat_repr hK hω k
    refine ⟨r • a, t • a, ?_⟩
    have e1 : ((r : ℚ) : K) = r • (1 : K) := by rw [Rat.smul_def, mul_one]
    have e2 : ((t : ℚ) : K) * ω = t • ω := (Rat.smul_def t ω).symm
    rw [e1, e2, TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨a₀, a₁, rfl⟩ := hx
    obtain ⟨b₀, b₁, rfl⟩ := hy
    exact ⟨a₀ + b₀, a₁ + b₁, by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

end Adeles

/-! ## The order `R = q⁻¹(𝒪)` and saturation -/

section Order

variable {K : Type} [Field K] [NumberField K]

/-- A `ℤ`-basis `1, ω` of `𝒪_K` for a quadratic field `K`. -/
theorem exists_basis_one (hK : Module.finrank ℚ K = 2) :
    ∃ b : Module.Basis (Fin 2) ℤ (𝓞 K), b 0 = 1 :=
  (Module.Free.isUnimodular_one (R := ℤ) (A := 𝓞 K)).exists_basis_zero_eq
    (by rw [RingOfIntegers.rank, hK])

omit [NumberField K] in
/-- Coordinates of an algebraic integer in a basis `1, ω` of `𝒪_K`. -/
theorem decomp_basis (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (hb : b 0 = 1) (y : 𝓞 K) :
    algebraMap (𝓞 K) K y = ((b.coord 0 y : ℤ) : K) +
      ((b.coord 1 y : ℤ) : K) * algebraMap (𝓞 K) K (b 1) := by
  have h : y = (b.coord 0 y : 𝓞 K) + b.coord 1 y • b 1 := by
    simpa [Fin.sum_univ_two, hb, Algebra.smul_def] using (b.sum_repr y).symm
  conv_lhs => rw [h]
  rw [map_add, map_zsmul, map_intCast, zsmul_eq_mul]

/-- The second basis vector `ω` is not rational. -/
theorem omega_not_rat (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (hb : b 0 = 1) :
    ∀ r : ℚ, (b 1 : K) ≠ r := by
  intro r hr
  have hint : IsIntegral ℤ (r : K) := hr ▸ RingOfIntegers.isIntegral_coe (b 1)
  obtain ⟨n, rfl⟩ := exists_int_of_isIntegral hint
  have h1 : b 1 = n • b 0 := by
    rw [hb, zsmul_one]
    apply RingOfIntegers.ext
    simpa using hr
  have h2 : b.repr (b 1) 1 = b.repr (n • b 0) 1 := by rw [← h1]
  rw [map_zsmul, Module.Basis.repr_self, Module.Basis.repr_self] at h2
  simp at h2

theorem omega_not_rat' (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (hb : b 0 = 1) :
    ∀ r : ℚ, algebraMap (𝓞 K) K (b 1) ≠ r :=
  omega_not_rat b hb

/-- `q` on rational numbers. -/
theorem q_ratCast (q : K →ₐ[ℚ] LeafQM.B) (r : ℚ) : q (r : K) = algebraMap ℚ LeafQM.B r := by
  rw [← eq_ratCast (algebraMap ℚ K) r, AlgHom.commutes]

/-- **Saturation**: `q(R) = q(K) ∩ 𝒪`. If `t c₁, t c₂, t c₃ ∈ ℤ` for the coordinates `c` of
`q(ω)`, then `t ∈ fℤ`. -/
theorem saturation (hK : Module.finrank ℚ K = 2) (q : K →ₐ[ℚ] LeafQM.B)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (hb : b 0 = 1) (t : ℚ)
    (h1 : ∃ n : ℤ, t * cQ (q (algebraMap (𝓞 K) K (b 1))) 1 = n) (h2 : ∃ n : ℤ, t * cQ (q (algebraMap (𝓞 K) K (b 1))) 2 = n)
    (h3 : ∃ n : ℤ, t * cQ (q (algebraMap (𝓞 K) K (b 1))) 3 = n) :
    ∃ k : ℤ, t = ((GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf).index : ℚ) * k := by
  set O := GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf with hO
  set ω : K := algebraMap (𝓞 K) K (b 1) with hω
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  obtain ⟨n3, hn3⟩ := h3
  set y : K := ((-(t * cQ (q ω) 0) : ℚ) : K) + (t : K) * ω with hy
  have hqy : q y = LeafQM.ofInt ![0, n1, n2, n3] := by
    apply eq_ofInt_of_cQ
    intro i
    have e : q y = algebraMap ℚ LeafQM.B (-(t * cQ (q ω) 0)) +
        algebraMap ℚ LeafQM.B t * q ω := by
      rw [hy, map_add, map_mul, q_ratCast, q_ratCast]
    rw [e, cQ_add', cQ_algebraMap, cQ_algebraMap_mul]
    fin_cases i <;> simp [hn1, hn2, hn3]
  have hyR : y ∈ LeafQM.O.comap q.toRingHom := by
    show q y ∈ LeafQM.O
    rw [hqy]
    exact ⟨_, rfl⟩
  have hyint : y ∈ integralClosure ℤ K := hR hyR
  set y' : 𝓞 K := ⟨y, hyint⟩ with hy'
  have hy'O : y' ∈ O.toRingOfIntegers := hyR
  obtain ⟨a, z, hz⟩ :=
    (NumberFieldOrder.mem_toRingOfIntegers_iff_exists_int_add_index_mul O hK y').1 hy'O
  have hzK := decomp_basis b hb z
  rw [← hω] at hzK
  have hyK : ((-(t * cQ (q ω) 0) : ℚ) : K) + (t : K) * ω =
      (((a + O.index * b.coord 0 z : ℤ) : ℚ) : K) + (((O.index * b.coord 1 z : ℤ) : ℚ) : K) * ω := by
    have e2 : y = algebraMap (𝓞 K) K ((a : 𝓞 K) + (O.index : 𝓞 K) * z) := by
      rw [← hz]
      rfl
    rw [map_add, map_mul, map_intCast, map_natCast, hzK] at e2
    rw [← hy, e2]
    push_cast
    ring
  obtain ⟨-, ht⟩ := repr_unique (omega_not_rat' b hb) hyK
  exact ⟨b.coord 1 z, by rw [ht]; push_cast; ring⟩

/-- **Coprimality**: `f q(ω)` has integer coordinates `m`, and `m₁, m₂, m₃` are coprime. -/
theorem exists_bezout (hK : Module.finrank ℚ K = 2) (q : K →ₐ[ℚ] LeafQM.B)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (hb : b 0 = 1) :
    ∃ (m : Fin 4 → ℤ) (u₁ u₂ u₃ : ℤ),
      (∀ i, ((GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf).index : ℚ) * cQ (q (algebraMap (𝓞 K) K (b 1))) i = m i) ∧
        u₁ * m 1 + u₂ * m 2 + u₃ * m 3 = 1 := by
  set O := GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf with hO
  set ω : K := algebraMap (𝓞 K) K (b 1) with hω
  have hf0 : (O.index : ℚ) ≠ 0 := by exact_mod_cast O.index_ne_zero
  have hfω : ((O.index : 𝓞 K) * b 1 : 𝓞 K) ∈ O.toRingOfIntegers :=
    O.conductor_le_toRingOfIntegers
      (O.conductor.mul_mem_right (b 1) O.natCast_index_mem_conductor)
  have hqO : q ((O.index : K) * ω) ∈ LeafQM.O := by
    have h : (((O.index : 𝓞 K) * b 1 : 𝓞 K) : K) ∈ LeafQM.O.comap q.toRingHom := hfω
    have e : (((O.index : 𝓞 K) * b 1 : 𝓞 K) : K) = (O.index : K) * ω := by
      push_cast
      rfl
    rw [e] at h
    exact h
  obtain ⟨m, hm⟩ := hqO
  have hmc : ∀ i, (O.index : ℚ) * cQ (q ω) i = m i := by
    intro i
    have h1 := congrFun (congrArg cQ hm) i
    rw [cQ_ofInt, map_mul, map_natCast, ← map_natCast (algebraMap ℚ LeafQM.B) O.index,
      cQ_algebraMap_mul] at h1
    exact h1
  set G : ℤ := (Int.gcd (m 2) (m 3) : ℤ) with hG
  set g : ℕ := Int.gcd (m 1) G with hg
  have hg1 : (g : ℤ) ∣ m 1 := Int.gcd_dvd_left ..
  have hgG : (g : ℤ) ∣ G := Int.gcd_dvd_right ..
  have hg2 : (g : ℤ) ∣ m 2 := hgG.trans (Int.gcd_dvd_left ..)
  have hg3 : (g : ℤ) ∣ m 3 := hgG.trans (Int.gcd_dvd_right ..)
  have hsat := saturation hK q hR hf b hb
  by_cases hg0 : g = 0
  · exfalso
    obtain ⟨h1, hG0⟩ := Int.gcd_eq_zero_iff.1 hg0
    have hG0' : Int.gcd (m 2) (m 3) = 0 := by
      rw [hG] at hG0
      exact_mod_cast hG0
    obtain ⟨h2, h3⟩ := Int.gcd_eq_zero_iff.1 hG0'
    have hc : ∀ i, m i = 0 → (O.index : ℚ) / 2 * cQ (q ω) i = ((0 : ℤ) : ℚ) := by
      intro i hi
      rw [div_mul_eq_mul_div, hmc i, hi]
      simp
    obtain ⟨k, hk⟩ := hsat ((O.index : ℚ) / 2) ⟨0, hc 1 h1⟩ ⟨0, hc 2 h2⟩ ⟨0, hc 3 h3⟩
    have h4 : (O.index : ℚ) * (2 * k) = (O.index : ℚ) * 1 := by
      calc (O.index : ℚ) * (2 * k) = 2 * ((O.index : ℚ) * k) := by ring
        _ = 2 * ((O.index : ℚ) / 2) := by rw [hk]
        _ = (O.index : ℚ) * 1 := by ring
    have h5 : (2 : ℚ) * k = 1 := mul_left_cancel₀ hf0 h4
    have h6 : (2 : ℤ) * k = 1 := by exact_mod_cast h5
    omega
  · obtain ⟨e1, he1⟩ := hg1
    obtain ⟨e2, he2⟩ := hg2
    obtain ⟨e3, he3⟩ := hg3
    have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg0
    have hc : ∀ i e, m i = (g : ℤ) * e → (O.index : ℚ) / g * cQ (q ω) i = ((e : ℤ) : ℚ) := by
      intro i e he
      rw [div_mul_eq_mul_div, hmc i, he]
      push_cast
      field_simp
    obtain ⟨k, hk⟩ := hsat ((O.index : ℚ) / g) ⟨e1, hc 1 e1 he1⟩ ⟨e2, hc 2 e2 he2⟩
      ⟨e3, hc 3 e3 he3⟩
    have h4 : (O.index : ℚ) * ((g : ℚ) * k) = (O.index : ℚ) * 1 := by
      calc (O.index : ℚ) * ((g : ℚ) * k) = (g : ℚ) * ((O.index : ℚ) * k) := by ring
        _ = (g : ℚ) * ((O.index : ℚ) / g) := by rw [hk]
        _ = (O.index : ℚ) * 1 := by field_simp
    have h5 : (g : ℚ) * k = 1 := mul_left_cancel₀ hf0 h4
    have h6 : (g : ℤ) * k = 1 := by exact_mod_cast h5
    have hg1' : (g : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h6
    have b1 := Int.gcd_eq_gcd_ab (m 1) G
    have b2 := Int.gcd_eq_gcd_ab (m 2) (m 3)
    refine ⟨m, Int.gcdA (m 1) G, Int.gcdB (m 1) G * Int.gcdA (m 2) (m 3),
      Int.gcdB (m 1) G * Int.gcdB (m 2) (m 3), hmc, ?_⟩
    have b1' : (1 : ℤ) = m 1 * Int.gcdA (m 1) G + G * Int.gcdB (m 1) G := by
      rw [← hg1']
      exact b1
    have b2' : G = m 2 * Int.gcdA (m 2) (m 3) + m 3 * Int.gcdB (m 2) (m 3) := b2
    rw [b1', b2']
    ring

end Order

/-! ## Finite adeles with integral image in `𝒪̂` -/

section Integral

variable {K : Type} [Field K] [NumberField K]

/-- **`q̂(x) ∈ 𝒪̂` forces `x ∈ R ⊗ ℤ̂`**: `x = m + f z` with `m ∈ ℤ` nonzero, `f` the index of
`R = q⁻¹(𝒪)` and `z` integral at every finite place. -/
theorem exists_int_add_index_mul (hK : Module.finrank ℚ K = 2) (q : K →ₐ[ℚ] LeafQM.B)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (x : FiniteAdeleRing (𝓞 K) K) (hx : qHat q x ∈ OhatQ) :
    ∃ (m : ℤ) (z : FiniteAdeleRing (𝓞 K) K), m ≠ 0 ∧
      (∀ w, z w ∈ w.adicCompletionIntegers K) ∧
      x = (m : FiniteAdeleRing (𝓞 K) K) +
        ((GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf).index : FiniteAdeleRing (𝓞 K) K) * z := by
  obtain ⟨b, hb⟩ := exists_basis_one (K := K) hK
  set f := (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf).index with hfdef
  set ω : K := algebraMap (𝓞 K) K (b 1) with hω
  have hf0 : 0 < f := Nat.pos_of_ne_zero (NumberFieldOrder.index_ne_zero _)
  obtain ⟨mv, u₁, u₂, u₃, hmv, hu⟩ := exists_bezout hK q hR hf b hb
  obtain ⟨a₀, a₁, ha⟩ :=
    tmul_decomp hK (omega_not_rat' b hb) ((finiteAdeleBaseChangeAlgEquiv ℚ K).symm x)
  have hxa : x = finiteAdeleExtension (𝓞 ℚ) ℚ (𝓞 K) K a₀ +
      finiteAdeleExtension (𝓞 ℚ) ℚ (𝓞 K) K a₁ * algebraMap K (FiniteAdeleRing (𝓞 K) K) ω := by
    have h := congrArg (finiteAdeleBaseChangeAlgEquiv ℚ K) ha
    rw [AlgEquiv.apply_symm_apply, map_add, baseChange_tmul, baseChange_tmul, map_one,
      mul_one] at h
    exact h
  have hqx : qHat q x = algebraMap AQ BAQ a₀ + algebraMap AQ BAQ a₁ * bEmb (q ω) := by
    show qT q ((finiteAdeleBaseChangeAlgEquiv ℚ K).symm x) = _
    rw [ha, map_add, qT_tmul, qT_tmul, map_one, map_one, mul_one]
  have hc : ∀ i, cQ (qHat q x) i ∈ ZhatQ := by
    obtain ⟨n, hn, he⟩ := hx
    intro i
    rw [he, cQ_ofQ]
    exact hn i
  have hcx : ∀ i, cQ (qHat q x) i = ![a₀, 0, 0, 0] i + a₁ * algebraMap ℚ AQ (cQ (q ω) i) := by
    intro i
    rw [hqx, cQ_add', cQ_algebraMap, cQ_algebraMap_mul, cQ_bEmb]
    rfl
  have hcm : ∀ i, (f : AQ) * algebraMap ℚ AQ (cQ (q ω) i) = (mv i : AQ) := by
    intro i
    rw [← map_natCast (algebraMap ℚ AQ), ← map_mul, hmv i, map_intCast]
  set β : AQ := (u₁ : AQ) * cQ (qHat q x) 1 + (u₂ : AQ) * cQ (qHat q x) 2 +
    (u₃ : AQ) * cQ (qHat q x) 3 with hβdef
  have hβ : β ∈ ZhatQ :=
    ZhatS.add_mem (ZhatS.add_mem (ZhatS.mul_mem (intCast_mem _ _) (hc 1))
      (ZhatS.mul_mem (intCast_mem _ _) (hc 2))) (ZhatS.mul_mem (intCast_mem _ _) (hc 3))
  have ha₁ : a₁ = (f : AQ) * β := by
    have e1 : cQ (qHat q x) 1 = a₁ * algebraMap ℚ AQ (cQ (q ω) 1) := by rw [hcx]; simp
    have e2 : cQ (qHat q x) 2 = a₁ * algebraMap ℚ AQ (cQ (q ω) 2) := by rw [hcx]; simp
    have e3 : cQ (qHat q x) 3 = a₁ * algebraMap ℚ AQ (cQ (q ω) 3) := by rw [hcx]; simp
    have hu' : ((u₁ * mv 1 + u₂ * mv 2 + u₃ * mv 3 : ℤ) : AQ) = 1 := by rw [hu]; simp
    calc a₁ = a₁ * ((u₁ * mv 1 + u₂ * mv 2 + u₃ * mv 3 : ℤ) : AQ) := by rw [hu', mul_one]
      _ = (f : AQ) * β := by
        rw [hβdef, e1, e2, e3]
        push_cast
        rw [← hcm 1, ← hcm 2, ← hcm 3]
        ring
  have ha₀ : a₀ ∈ ZhatQ := by
    have e0 : cQ (qHat q x) 0 = a₀ + a₁ * algebraMap ℚ AQ (cQ (q ω) 0) := by rw [hcx]; simp
    have h0 : a₀ = cQ (qHat q x) 0 - β * (mv 0 : AQ) := by
      rw [e0, ha₁, ← hcm 0]
      ring
    rw [h0]
    exact ZhatS.sub_mem (hc 0) (ZhatS.mul_mem hβ (intCast_mem _ _))
  obtain ⟨m, γ, hγ, hm⟩ := exists_int_approx ha₀ f hf0
  set z : FiniteAdeleRing (𝓞 K) K := finiteAdeleExtension (𝓞 ℚ) ℚ (𝓞 K) K γ +
    finiteAdeleExtension (𝓞 ℚ) ℚ (𝓞 K) K β * algebraMap K (FiniteAdeleRing (𝓞 K) K) ω with hz
  have hzint : ∀ w, z w ∈ w.adicCompletionIntegers K := by
    intro w
    rw [← evK_apply, hz, map_add, map_mul, evK_apply, evK_apply, evK_apply]
    exact add_mem (extension_mem_integers hγ w)
      (mul_mem (extension_mem_integers hβ w) (algebraMap_mem_integers (b 1) w))
  have hxz : x = (m : FiniteAdeleRing (𝓞 K) K) + (f : FiniteAdeleRing (𝓞 K) K) * z := by
    rw [hxa, hm, ha₁, map_add, map_mul, map_mul, map_intCast, map_natCast, hz]
    ring
  by_cases hm0 : m = 0
  · refine ⟨f, z - 1, by exact_mod_cast hf0.ne', fun w => ?_, ?_⟩
    · rw [← evK_apply, map_sub, map_one, evK_apply]
      exact sub_mem (hzint w) (one_mem _)
    · rw [hxz, hm0]
      push_cast
      ring
  · exact ⟨m, z, hm0, hzint, hxz⟩

end Integral

/-! ## The ring-class kernel -/

section Kernel

variable {K : Type} [Field K] [NumberField K]

theorem valued_intCast (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    Valued.v ((n : ℤ) : v.adicCompletion K) = v.valuation K (algebraMap (𝓞 K) K (n : 𝓞 K)) := by
  have e : ((n : ℤ) : v.adicCompletion K) =
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K (n : 𝓞 K))) v := by
    rw [map_intCast, map_intCast, ← evK_apply, map_intCast]
  rw [e, FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation']

theorem valued_natCast (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion K) = v.valuation K (algebraMap (𝓞 K) K (n : 𝓞 K)) := by
  have e : ((n : ℕ) : v.adicCompletion K) =
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K (n : 𝓞 K))) v := by
    rw [map_natCast, map_natCast, ← evK_apply, map_natCast]
  rw [e, FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation']

/-- **The ring-class kernel.** For an idele `s` of the quadratic field `K` with
`q̂(s), q̂(s)⁻¹ ∈ 𝒪̂`, the class of `s` is trivial in `Pic R`, `R = q⁻¹(𝒪)`. -/
theorem ringClassIdeleQuotient_mk_eq_one (hK : Module.finrank ℚ K = 2) (q : K →ₐ[ℚ] LeafQM.B)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (s : IdeleGroup (𝓞 K) K) (hs : qHatU q s ∈ OhatU) :
    ringClassIdeleQuotient (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf) (QuotientGroup.mk s) = 1 := by
  set O := GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf with hO
  -- the integral decompositions of `s` and `s⁻¹`
  have h1 : qHat q ((IdeleGroup.toFiniteIdele (𝓞 K) K s : FiniteAdeleRing (𝓞 K) K)) ∈ OhatQ :=
    hs.1
  have h2 : qHat q ((IdeleGroup.toFiniteIdele (𝓞 K) K s⁻¹ : FiniteAdeleRing (𝓞 K) K)) ∈
      OhatQ := by
    have h := hs.2
    rw [← map_inv] at h
    exact h
  obtain ⟨m, z, hm0, hz, hsz⟩ := exists_int_add_index_mul hK q hR hf _ h1
  obtain ⟨m', z', -, hz', hsz'⟩ := exists_int_add_index_mul hK q hR hf _ h2
  have hcomp : ∀ (t : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)),
      (v.ideleFiniteCoord t : v.adicCompletion K) =
        (IdeleGroup.toFiniteIdele (𝓞 K) K t : FiniteAdeleRing (𝓞 K) K) v := by
    intro t v
    rw [HeightOneSpectrum.coe_ideleFiniteCoord, IdeleGroup.coe_toFiniteIdele]
  have hval : ∀ (t : IdeleGroup (𝓞 K) K) (n : ℤ) (y : FiniteAdeleRing (𝓞 K) K),
      (IdeleGroup.toFiniteIdele (𝓞 K) K t : FiniteAdeleRing (𝓞 K) K) =
        (n : FiniteAdeleRing (𝓞 K) K) + (O.index : FiniteAdeleRing (𝓞 K) K) * y →
      ∀ v : HeightOneSpectrum (𝓞 K), (v.ideleFiniteCoord t : v.adicCompletion K) =
        (n : v.adicCompletion K) + (O.index : v.adicCompletion K) * y v := by
    intro t n y h v
    rw [hcomp, h, ← evK_apply, map_add, map_mul, map_intCast, map_natCast, evK_apply]
  have hint : ∀ (n : ℤ) (y : FiniteAdeleRing (𝓞 K) K), (∀ w, y w ∈ w.adicCompletionIntegers K) →
      ∀ w : HeightOneSpectrum (𝓞 K),
        (n : w.adicCompletion K) + (O.index : w.adicCompletion K) * y w ∈
          w.adicCompletionIntegers K := by
    intro n y hy w
    exact add_mem (intCast_mem _ n) (mul_mem (natCast_mem _ _) (hy w))
  -- `s` is a unit at every finite place
  have hunit : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (v.ideleFiniteCoord s : v.adicCompletion K) = 1 := by
    intro v
    have ha : Valued.v (v.ideleFiniteCoord s : v.adicCompletion K) ≤ 1 := by
      rw [hval s m z hsz v]
      exact (mem_adicCompletionIntegers ..).1 (hint m z hz v)
    have hb : Valued.v (v.ideleFiniteCoord s⁻¹ : v.adicCompletion K) ≤ 1 := by
      rw [hval s⁻¹ m' z' hsz' v]
      exact (mem_adicCompletionIntegers ..).1 (hint m' z' hz' v)
    have hprod : Valued.v (v.ideleFiniteCoord s : v.adicCompletion K) *
        Valued.v (v.ideleFiniteCoord s⁻¹ : v.adicCompletion K) = 1 := by
      rw [← Valuation.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
        Units.val_one, Valuation.map_one]
    have h3 : Valued.v (v.ideleFiniteCoord s : v.adicCompletion K) *
        Valued.v (v.ideleFiniteCoord s⁻¹ : v.adicCompletion K) ≤
          Valued.v (v.ideleFiniteCoord s : v.adicCompletion K) * 1 := by gcongr
    rw [hprod, mul_one] at h3
    exact le_antisymm ha h3
  -- the index lies in every prime of the support of the conductor
  have hfv : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ O.conductorModulus.finitePart →
      ∀ e : ℕ, v.asIdeal ^ e ∣ O.conductorModulus.finitePart →
        (O.index : 𝓞 K) ∈ v.asIdeal ^ e := by
    intro v _ e he
    rw [NumberFieldOrder.conductorModulus_finitePart] at he
    exact Ideal.le_of_dvd he O.natCast_index_mem_conductor
  -- `m 𝒪_K` is prime to the conductor
  have hJ : Ideal.span {(m : 𝓞 K)} ∈ integralIdealsPrimeTo O.conductorModulus := by
    rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff]
    refine ⟨by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hm0, fun v hv hdvd => ?_⟩
    have hmv : (m : 𝓞 K) ∈ v.asIdeal := Ideal.dvd_span_singleton.1 hdvd
    have hv' := (Modulus.mem_support_iff _ v).1 hv
    have hfv1 : (O.index : 𝓞 K) ∈ v.asIdeal := by
      simpa using hfv v hv' 1 (by simpa using hv')
    have hlt : Valued.v (v.ideleFiniteCoord s : v.adicCompletion K) < 1 := by
      rw [hval s m z hsz v]
      apply Valuation.map_add_lt
      · rw [valued_intCast]
        exact (valuation_lt_one_iff_mem v _).2 hmv
      · rw [Valuation.map_mul, valued_natCast]
        have hzv : Valued.v (z v) ≤ 1 := (mem_adicCompletionIntegers ..).1 (hz v)
        have hf1 : v.valuation K (algebraMap (𝓞 K) K (O.index : 𝓞 K)) < 1 :=
          (valuation_lt_one_iff_mem v _).2 hfv1
        calc v.valuation K (algebraMap (𝓞 K) K (O.index : 𝓞 K)) * Valued.v (z v)
            ≤ v.valuation K (algebraMap (𝓞 K) K (O.index : 𝓞 K)) * 1 := by gcongr
          _ < 1 := by rw [mul_one]; exact hf1
    rw [hunit v] at hlt
    exact lt_irrefl _ hlt
  -- `m s⁻¹` is congruent to one modulo the conductor
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0
  set x : IdeleGroup (𝓞 K) K := IdeleGroup.unitEmbedding (𝓞 K) K (Units.mk0 (m : K) hmK) * s⁻¹
    with hxdef
  have hx : x ∈ ideleCongrOneSubgroup O.conductorModulus := by
    rw [mem_ideleCongrOneSubgroup_iff]
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · have hS := hval s m z hsz v
      have hS0 : (v.ideleFiniteCoord s : v.adicCompletion K) ≠ 0 := (v.ideleFiniteCoord s).ne_zero
      have hxv : (v.ideleFiniteCoord x : v.adicCompletion K) =
          (m : v.adicCompletion K) * (v.ideleFiniteCoord s : v.adicCompletion K)⁻¹ := by
        rw [hxdef, map_mul, Units.val_mul, HeightOneSpectrum.ideleFiniteCoord_unitEmbedding,
          Units.coe_map, map_inv, Units.val_inv_eq_inv_val]
        simp
      have e : (v.ideleFiniteCoord x : v.adicCompletion K) - 1 =
          -((O.index : v.adicCompletion K) * z v) *
            (v.ideleFiniteCoord s : v.adicCompletion K)⁻¹ := by
        rw [hxv]
        field_simp
        rw [hS]
        ring
      rw [e, Valuation.map_mul, Valuation.map_neg, Valuation.map_mul, map_inv₀, hunit v, inv_one,
        mul_one, valued_natCast]
      have hzv : Valued.v (z v) ≤ 1 := (mem_adicCompletionIntegers ..).1 (hz v)
      calc v.valuation K (algebraMap (𝓞 K) K (O.index : 𝓞 K)) * Valued.v (z v)
          ≤ v.valuation K (algebraMap (𝓞 K) K (O.index : 𝓞 K)) * 1 := by gcongr
        _ ≤ WithZero.exp (-(O.conductorModulus.exponent v : ℤ)) := by
          rw [mul_one, valuation_of_algebraMap]
          exact (intValuation_le_pow_iff_mem v _ _).2
            (hfv v hv _ (Modulus.pow_exponent_dvd_finitePart _ v))
    · rw [NumberFieldOrder.conductorModulus_infinitePart] at hw
      simp at hw
  -- the classes of `x` and `s⁻¹` agree
  have hmk : (QuotientGroup.mk x : IdeleClassGroup (𝓞 K) K) = QuotientGroup.mk s⁻¹ := by
    rw [hxdef, mul_comm, QuotientGroup.mk_mul_of_mem s⁻¹ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)]
  -- `s` is a unit at every finite place, so the ideal of `x` is `m 𝒪_K`
  have hideal : FiniteAdeleRing.toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K s) = 1 := by
    rw [toFractionalIdeal_toFiniteIdele_eq_one_iff]
    exact hunit
  have hray : rayClassQuotient O.conductorModulus (QuotientGroup.mk s⁻¹) =
      idealClass O.conductorModulus ⟨_, hJ⟩ := by
    rw [← hmk, rayClassQuotient_mk_of_mem hx, idealClass_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [TauCeti.NumberFieldArithmetic.coe_integralIdealsAwayHom]
    simp only [hxdef, map_mul, map_inv, IdeleGroup.toFiniteIdele_unitEmbedding,
      FiniteAdeleRing.toFractionalIdeal_unitEmbedding, hideal, inv_one, mul_one]
    simp [FractionalIdeal.coeIdeal_span_singleton]
  have hker : (QuotientGroup.mk s⁻¹ : IdeleClassGroup (𝓞 K) K) ∈ (ringClassIdeleQuotient O).ker :=
    (mem_ker_ringClassIdeleQuotient_iff O).2
      ⟨⟨_, hJ⟩, hray.symm, (m : 𝓞 K), O.toRingOfIntegers.intCast_mem m, rfl⟩
  rw [MonoidHom.mem_ker, QuotientGroup.mk_inv, map_inv, inv_eq_one] at hker
  exact hker

/-- **The Artin symbol of `s` on the ring class field of `R = q⁻¹(𝒪)` is trivial.** -/
theorem ideleClassArtinMap_ringClassField_eq_one (hK : Module.finrank ℚ K = 2)
    (q : K →ₐ[ℚ] LeafQM.B)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (s : IdeleGroup (𝓞 K) K) (hs : qHatU q s ∈ OhatU) :
    ideleClassArtinMap K (ringClassField (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf)) (QuotientGroup.mk s) =
      1 := by
  rw [← ringClassArtinEquiv_ringClassIdeleQuotient,
    ringClassIdeleQuotient_mk_eq_one hK q hR hf s hs, map_one]

end Kernel

/-! ## The two side conditions: `R ⊆ 𝒪_K` and `[𝒪_K : R] ≠ 0` -/

section Side

variable {K : Type} [Field K] [NumberField K]

/-- Elements of `𝒪` are integral over `ℤ`: `x = n₀ + n₁i + n₂(1+j)/2 + n₃(i+k)/2` satisfies
`x² − (2n₀ + n₂)x + (n₀² + n₀n₂ + n₂² − 2n₁² − 2n₁n₃ − 2n₃²) = 0`. -/
theorem isIntegral_of_mem_O {x : LeafQM.B} (hx : x ∈ LeafQM.O) : IsIntegral ℤ x := by
  obtain ⟨n, rfl⟩ := hx
  set T : ℤ := 2 * n 0 + n 2 with hT
  set N : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2 with hN
  refine ⟨Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C N, ?_, ?_⟩
  · monicity!
  · rw [← Polynomial.aeval_def]
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    simp only [eq_intCast]
    ext <;> simp [LeafQM.ofInt, sq] <;> (try simp only [hT, hN]) <;> push_cast <;> ring

/-- `R = q⁻¹(𝒪)` consists of algebraic integers. -/
theorem comap_le_integralClosure (q : K →ₐ[ℚ] LeafQM.B) :
    LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring := by
  intro y hy
  have h1 : IsIntegral ℤ (q y) := isIntegral_of_mem_O hy
  exact (isIntegral_algHom_iff (q.restrictScalars ℤ) q.toRingHom.injective).1 h1

/-- Every element of `K` has a positive integer multiple in `R = q⁻¹(𝒪)`. -/
theorem exists_natCast_mul_mem (q : K →ₐ[ℚ] LeafQM.B) (y : K) :
    ∃ D : ℕ, 0 < D ∧ (D : K) * y ∈ LeafQM.O.comap q.toRingHom := by
  set c := cQ (q y) with hc
  set D : ℕ := (c 0).den * (c 1).den * (c 2).den * (c 3).den with hD
  refine ⟨D, by positivity, ?_⟩
  show q ((D : K) * y) ∈ LeafQM.O
  have h0 := Rat.mul_den_eq_num (c 0)
  have h1 := Rat.mul_den_eq_num (c 1)
  have h2 := Rat.mul_den_eq_num (c 2)
  have h3 := Rat.mul_den_eq_num (c 3)
  have hcoord : ∀ i, ∃ n : ℤ, cQ (q ((D : K) * y)) i = n := by
    intro i
    rw [map_mul, map_natCast, ← map_natCast (algebraMap ℚ LeafQM.B) D, cQ_algebraMap_mul]
    fin_cases i
    · exact ⟨(c 0).num * (c 1).den * (c 2).den * (c 3).den, by
        simp only [hD]; push_cast; linear_combination ((c 1).den * (c 2).den * (c 3).den : ℚ) * h0⟩
    · exact ⟨(c 0).den * (c 1).num * (c 2).den * (c 3).den, by
        simp only [hD]; push_cast; linear_combination ((c 0).den * (c 2).den * (c 3).den : ℚ) * h1⟩
    · exact ⟨(c 0).den * (c 1).den * (c 2).num * (c 3).den, by
        simp only [hD]; push_cast; linear_combination ((c 0).den * (c 1).den * (c 3).den : ℚ) * h2⟩
    · exact ⟨(c 0).den * (c 1).den * (c 2).den * (c 3).num, by
        simp only [hD]; push_cast; linear_combination ((c 0).den * (c 1).den * (c 2).den : ℚ) * h3⟩
  choose n hn using hcoord
  rw [eq_ofInt_of_cQ _ n hn]
  exact ⟨n, rfl⟩

/-- `R = q⁻¹(𝒪)` as an order of `K` (its `ℚ`-span is `K` by `exists_natCast_mul_mem`). -/
def orderOfEmb (q : K →ₐ[ℚ] LeafQM.B) : NumberFieldOrder K where
  toSubalgebra := GR512Bridge.intSubalgebra (LeafQM.O.comap q.toRingHom)
  finite := by
    have h : GR512Bridge.intSubalgebra (LeafQM.O.comap q.toRingHom) ≤ integralClosure ℤ K :=
      fun x hx => comap_le_integralClosure q hx
    have : Module.Finite ℤ (integralClosure ℤ K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))
    exact Module.Finite.of_injective (Subalgebra.inclusion h).toLinearMap
      (Subalgebra.inclusion_injective h)
  spans := by
    refine Submodule.eq_top_iff'.2 fun y => ?_
    obtain ⟨D, hD, hDy⟩ := exists_natCast_mul_mem q y
    have hD' : ((D : ℚ)) ≠ 0 := by exact_mod_cast hD.ne'
    have e : y = (D : ℚ)⁻¹ • ((D : K) * y) := by
      rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
        inv_mul_cancel₀ (by exact_mod_cast hD.ne'), one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hDy)

/-- **`[𝒪_K : R] ≠ 0`** for `R = q⁻¹(𝒪)`. -/
theorem conductor_comap_ne_zero (q : K →ₐ[ℚ] LeafQM.B) :
    LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0 := by
  have h := (orderOfEmb q).index_ne_zero
  rw [NumberFieldOrder.index_eq_addSubgroup_index] at h
  let e : 𝓞 K →+ (integralClosure ℤ K).toSubring.toAddSubgroup :=
    { toFun := fun x => ⟨(x : K), x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he : Function.Surjective e := fun x => ⟨⟨x.1, x.2⟩, rfl⟩
  have hcomap : ((LeafQM.O.comap q.toRingHom).toAddSubgroup.addSubgroupOf
      (integralClosure ℤ K).toSubring.toAddSubgroup).comap e =
      (Subalgebra.toSubmodule (orderOfEmb q).toRingOfIntegers).toAddSubgroup := by
    ext x
    rfl
  unfold LeafQM.AV.conductor AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective _ he, hcomap]
  exact h

/-- **The ring-class kernel**, with the two side conditions proved. -/
theorem ringClassIdeleQuotient_mk_eq_one' (hK : Module.finrank ℚ K = 2) (q : K →ₐ[ℚ] LeafQM.B)
    (s : IdeleGroup (𝓞 K) K) (hs : qHatU q s ∈ OhatU) :
    ringClassIdeleQuotient (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom)
      (comap_le_integralClosure q) (conductor_comap_ne_zero q)) (QuotientGroup.mk s) = 1 :=
  ringClassIdeleQuotient_mk_eq_one hK q _ _ s hs

/-- **The Artin symbol on the ring class field of `R = q⁻¹(𝒪)` is trivial**, with the two side
conditions proved. -/
theorem ideleClassArtinMap_ringClassField_eq_one' (hK : Module.finrank ℚ K = 2)
    (q : K →ₐ[ℚ] LeafQM.B) (s : IdeleGroup (𝓞 K) K) (hs : qHatU q s ∈ OhatU) :
    ideleClassArtinMap K (ringClassField (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom)
      (comap_le_integralClosure q) (conductor_comap_ne_zero q))) (QuotientGroup.mk s) = 1 :=
  ideleClassArtinMap_ringClassField_eq_one hK q _ _ s hs

end Side

end HDec.CMBranch.CMjReroute
