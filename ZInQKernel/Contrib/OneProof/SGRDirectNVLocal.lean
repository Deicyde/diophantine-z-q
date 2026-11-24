import ZInQKernel.Contrib.OneProof.SGRDirectElkies

/-!
# nv-local: `NVLocalInertia` from the local geometry of tame covers (`TameBranchNormal`)

`SGRDirect.NVLocalInertia` (h-b1 §3 Lemma NV step 3; `SGRDirectNV.lean`) is the one open Prop of route NV, by
which `SGRDirect.heckeVertWitness_of_nvElkies` proves `HDec.HeckeRestNV.HeckeVertWitness` without the integral
model of the Shimura curve. This file proves it from one strictly smaller GLUE Prop of general commutative
algebra, with no project-specific definitions:

* `TameBranchNormal` (GLUE, local algebra of tame covers): for a tame Galois cover of a two-dimensional regular
  local ring `R_m`, `m = (f, g)`, unramified off the normal-crossings divisor `fg = 0`, the branch of `f = 0`
  through each closed point is unique and normal there.

Compiled here (standard axioms):

* `eq_one_of_inertia_of_unram`, `primeOf`, `inertia_primeOf`, `eq_one_of_primeOf`: an automorphism of a number
  field in the inertia group of an unramified prime is trivial, and the prime `{c₁/c₂ : c₁ ∈ 𝔓}` of the ring of
  integers of the residue field of a normal branch;
* `exists_branch`: through every closed point `𝔓` over `(p, X − b)` passes a branch of `X = b` (going down);
* `BranchRegular` (the same statement for the Hecke-cover setting, over `ℤ[X]`, `ℚ[X]` and `ℚ(X)`) and
  `nvLocalInertia_of_branchRegular : BranchRegular → NVLocalInertia` (with `g = 1`);
* `branchRegular_of_tame : TameBranchNormal → BranchRegular`, through `ramificationIdx_map_localization`,
  `isLocalization_B` (the `ℚ[X]`-closure is the localization of the `ℤ[X]`-closure at the nonzero integers),
  `unram_near` (from `BranchData` and distinctness mod `p`), `maximal_eq_span`, `span_secGen_eq` (Gauss);
* `nvLocalInertia_of_tame`, and `heckeVertWitness_of_tame`: `HeckeVertWitness` from the bundle fields `r1r2`,
  `t5`, `qmAutCard`, `serreRigidity3`, `alFixedPoints`, `elkiesX6StarPrinted` and `TameBranchNormal`.
-/

open Polynomial CategoryTheory AlgebraicGeometry IsLocalRing
open GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV HDec.TSHecke LeafQM LeafQM.AV

set_option linter.style.haveILetI false

noncomputable section

namespace SGRDirect.NVLocal

/-- **An inertia automorphism at an unramified prime is trivial.** -/
theorem eq_one_of_inertia_of_unram {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K))
    [P.IsPrime] (hun : P.ramificationIdx ℤ = 1) (σ : K ≃ₐ[ℚ] K)
    (hσ : ∀ x : 𝓞 K, σ • x - x ∈ P) : σ = 1 := by
  set G := Subgroup.zpowers σ
  haveI : Finite G := inferInstance
  set K₀ := FixedPoints.subfield G K
  haveI : CharZero K₀ := inferInstance
  haveI : FiniteDimensional ℚ K₀ := by
    exact Module.Finite.of_injective ((algebraMap K₀ K).toRatAlgHom.toLinearMap)
      (algebraMap K₀ K).injective
  haveI : NumberField K₀ := ⟨⟩
  haveI : FaithfulSMul G K := ⟨fun {g₁ g₂} h => Subtype.ext (AlgEquiv.ext h)⟩
  haveI : IsGaloisGroup G K₀ K := IsGaloisGroup.fixedPoints G K
  haveI : IsGaloisGroup G (𝓞 K₀) (𝓞 K) := IsGaloisGroup.of_isFractionRing G (𝓞 K₀) (𝓞 K) K₀ K
  set P₀ := P.under (𝓞 K₀)
  haveI : P₀.IsPrime := Ideal.IsPrime.under _ P
  haveI : P.LiesOver P₀ := ⟨rfl⟩
  have hg : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) ∈ P.inertia G := by
    intro x
    exact hσ x
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := G) P₀ P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P₀ P G] at hcard
  have htow := Ideal.ramificationIdx_tower (R := ℤ) P₀ P
  rw [hun] at htow
  have h1 : P.ramificationIdx (𝓞 K₀) = 1 := (Nat.eq_one_of_mul_eq_one_left htow.symm)
  rw [h1] at hcard
  have : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) = 1 := by
    have hb : P.inertia G = ⊥ := Subgroup.card_eq_one.mp hcard
    rw [hb] at hg
    exact hg
  exact congrArg Subtype.val this


/-- The prime of `𝓞 L` cut out by a prime `𝔓` of a ring `C` mapping to `L` whose localization contains `𝓞 L`. -/
def primeOf {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr) [𝔓.IsPrime]
    (ψ : Cr →+* L) (_hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) : Ideal (𝓞 L) where
  carrier := {y | ∃ d₁ d₂ : Cr, d₁ ∈ 𝔓 ∧ d₂ ∉ 𝔓 ∧ (y : L) * ψ d₂ = ψ d₁}
  zero_mem' := ⟨0, 1, 𝔓.zero_mem, fun h => (Ideal.IsPrime.ne_top inferInstance)
    ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    rintro x y ⟨a₁, a₂, ha₁, ha₂, hx⟩ ⟨b₁, b₂, hb₁, hb₂, hy⟩
    refine ⟨a₁ * b₂ + b₁ * a₂, a₂ * b₂, 𝔓.add_mem (𝔓.mul_mem_right _ ha₁) (𝔓.mul_mem_right _ hb₁),
      fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha₂ hb₂, ?_⟩
    simp only [show ((x + y : 𝓞 L) : L) = (x : L) + y from rfl, map_add, map_mul, ← hx, ← hy]
    ring
  smul_mem' := by
    rintro r x ⟨d₁, d₂, hd₁, hd₂, hx⟩
    obtain ⟨c₁, c₂, hc₂, hr⟩ := hN r
    refine ⟨c₁ * d₁, c₂ * d₂, 𝔓.mul_mem_left _ hd₁,
      fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hc₂ hd₂, ?_⟩
    simp only [show ((r • x : 𝓞 L) : L) = (r : L) * x from rfl, map_mul, ← hx, ← hr]
    ring

theorem primeOf_isPrime {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr)
    [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) :
    (primeOf 𝔓 ψ hker hN).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    rintro ⟨d₁, d₂, hd₁, hd₂, h⟩
    apply hd₂
    have h' : ψ (d₂ - d₁) = 0 := by
      rw [map_sub, ← h]; simp
    have := 𝔓.add_mem (hker _ h') hd₁
    simpa using this
  · rintro x y ⟨d₁, d₂, hd₁, hd₂, hxy⟩
    obtain ⟨a₁, a₂, ha₂, hx⟩ := hN x
    obtain ⟨b₁, b₂, hb₂, hy⟩ := hN y
    have key : ψ (a₁ * b₁ * d₂ - d₁ * a₂ * b₂) = 0 := by
      simp only [map_sub, map_mul]
      rw [← hx, ← hy, ← hxy, show ((x * y : 𝓞 L) : L) = (x : L) * y from rfl]
      ring
    have h1 : a₁ * b₁ * d₂ ∈ 𝔓 := by
      have := 𝔓.add_mem (hker _ key) (𝔓.mul_mem_right b₂ (𝔓.mul_mem_right a₂ hd₁))
      simpa using this
    rcases (Ideal.IsPrime.mem_or_mem inferInstance h1) with h2 | h2
    · rcases (Ideal.IsPrime.mem_or_mem inferInstance h2) with h3 | h3
      · exact Or.inl ⟨a₁, a₂, h3, ha₂, hx⟩
      · exact Or.inr ⟨b₁, b₂, h3, hb₂, hy⟩
    · exact absurd h2 hd₂

theorem mem_primeOf_of_mem {L : Type*} [Field L] {Cr : Type*} [CommRing Cr] (𝔓 : Ideal Cr)
    [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (p : ℕ)
    (hp : (p : Cr) ∈ 𝔓) : ((p : ℤ) : 𝓞 L) ∈ primeOf 𝔓 ψ hker hN := by
  refine ⟨p, 1, hp, fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simp

theorem inertia_primeOf {L : Type*} [Field L] [CharZero L] {Cr : Type*} [CommRing Cr]
    (𝔓 : Ideal Cr) [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ c : Cr, ∃ c' : Cr, σ (ψ c) = ψ c' ∧ c' - c ∈ 𝔓) :
    ∀ y : 𝓞 L, σ • y - y ∈ primeOf 𝔓 ψ hker hN := by
  intro y
  obtain ⟨c₁, c₂, hc₂, hy⟩ := hN y
  obtain ⟨c₁', hσ₁, h₁⟩ := hσ c₁
  obtain ⟨c₂', hσ₂, h₂⟩ := hσ c₂
  have hc₂' : c₂' ∉ 𝔓 := by
    intro h
    apply hc₂
    have := 𝔓.sub_mem h h₂
    simpa using this
  refine ⟨c₁' * c₂ - c₁ * c₂', c₂ * c₂', ?_,
    fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hc₂ hc₂', ?_⟩
  · have : c₁' * c₂ - c₁ * c₂' = (c₁' - c₁) * c₂ - c₁ * (c₂' - c₂) := by ring
    rw [this]
    exact 𝔓.sub_mem (𝔓.mul_mem_right _ h₁) (𝔓.mul_mem_left _ h₂)
  · have hσy : σ (y : L) * ψ c₂' = ψ c₁' := by
      rw [← hσ₂, ← hσ₁, ← map_mul, hy]
    have hcoe : ((σ • y : 𝓞 L) : L) = σ (y : L) := rfl
    simp only [show ((σ • y - y : 𝓞 L) : L) = ((σ • y : 𝓞 L) : L) - y from rfl, hcoe, map_sub,
      map_mul, ← hσy, ← hy]
    ring


/-- **An inertia automorphism is trivial** (assembled): the prime `primeOf` is unramified. -/
theorem eq_one_of_primeOf {L : Type*} [Field L] [NumberField L] {Cr : Type*} [CommRing Cr]
    (𝔓 : Ideal Cr) [𝔓.IsPrime] (ψ : Cr →+* L) (hker : ∀ c, ψ c = 0 → c ∈ 𝔓)
    (hN : ∀ y : 𝓞 L, ∃ c₁ c₂ : Cr, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁) (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ c : Cr, ∃ c' : Cr, σ (ψ c) = ψ c' ∧ c' - c ∈ 𝔓) (p : ℕ) (hp : (p : Cr) ∈ 𝔓)
    (hun : ∀ P : Ideal (𝓞 L), P.IsPrime → ((p : ℤ) : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1) :
    σ = 1 := by
  haveI := primeOf_isPrime 𝔓 ψ hker hN
  exact eq_one_of_inertia_of_unram (primeOf 𝔓 ψ hker hN)
    (hun _ inferInstance (mem_primeOf_of_mem 𝔓 ψ hker hN p hp)) σ (inertia_primeOf 𝔓 ψ hker hN σ hσ)

/-! ## The inclusion `ℤ[X]`-closure → `ℚ[X]`-closure and the Galois action -/

/-- The inclusion of the integral closure of `ℤ[X]` in `E` into that of `ℚ[X]`. -/
def zqIncl (E : Type) [Field E] [Algebra ℚ[X] E] :
    letI := intPolyAlg E
    integralClosure ℤ[X] E →+* integralClosure ℚ[X] E :=
  letI := intPolyAlg E
  { toFun := fun c => ⟨(c : E), by
      obtain ⟨f, hf, hf0⟩ := c.2
      refine ⟨f.map (Polynomial.mapRingHom (Int.castRingHom ℚ)), hf.map _, ?_⟩
      rw [eval₂_map]
      exact hf0⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E]

/-- A `ℚ(X)`-automorphism of `E` acting on the integral closure of `ℚ[X]`. -/
def galB (g : Gal(E/RatFunc ℚ)) : integralClosure ℚ[X] E ≃+* integralClosure ℚ[X] E where
  toFun x := ⟨g x, x.2.map ((g : E →ₐ[RatFunc ℚ] E).restrictScalars ℚ[X])⟩
  invFun x := ⟨g⁻¹ x, x.2.map (((g⁻¹ : Gal(E/RatFunc ℚ)) : E →ₐ[RatFunc ℚ] E).restrictScalars ℚ[X])⟩
  left_inv x := Subtype.ext (by
    show g⁻¹ (g (x : E)) = x
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
  right_inv x := Subtype.ext (by
    show g (g⁻¹ (x : E)) = x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])
  map_mul' x y := Subtype.ext (map_mul g (x : E) y)
  map_add' x y := Subtype.ext (map_add g (x : E) y)

theorem galB_apply (g : Gal(E/RatFunc ℚ)) (x : integralClosure ℚ[X] E) :
    ((galB g x : integralClosure ℚ[X] E) : E) = g x := rfl

/-- A `ℚ(X)`-automorphism maps the integral closure of `ℤ[X]` to itself. -/
theorem galC_mem (g : Gal(E/RatFunc ℚ)) :
    letI := intPolyAlg E
    ∀ c : integralClosure ℤ[X] E, ∃ c' : integralClosure ℤ[X] E, (c' : E) = g c := by
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  intro c
  exact ⟨⟨g c, c.2.map ((g : E →ₐ[RatFunc ℚ] E).restrictScalars ℤ[X])⟩, rfl⟩



omit [Algebra (RatFunc ℚ) E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] in
/-- Clearing denominators: every element of the `ℚ[X]`-closure has a nonzero integer multiple in the
`ℤ[X]`-closure. -/
theorem exists_int_mul_mem (y : integralClosure ℚ[X] E) :
    letI := intPolyAlg E
    ∃ k : ℤ, k ≠ 0 ∧ ∃ c : integralClosure ℤ[X] E, (c : E) = (k : E) * y := by
  letI := intPolyAlg E
  letI : Algebra ℤ[X] ℚ[X] := Polynomial.algebra ℤ ℚ
  haveI : IsLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])) ℚ[X] :=
    Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  haveI : IsScalarTower ℤ[X] ℚ[X] E := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap ℚ[X] E (x.map (Int.castRingHom ℚ)) = algebraMap ℚ[X] E (algebraMap ℤ[X] ℚ[X] x)
    rw [Polynomial.algebraMap_def ℤ ℚ]
    congr 2)
  obtain ⟨⟨_, ⟨k, hk, rfl⟩⟩, hint⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization
      ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])) (y : E) y.2
  refine ⟨k, nonZeroDivisors.ne_zero hk, ⟨_, hint⟩, ?_⟩
  show (C k : ℤ[X]) • (y : E) = (k : E) * y
  rw [Algebra.smul_def]
  congr 1
  show algebraMap ℚ[X] E ((C k).map (Int.castRingHom ℚ)) = (k : E)
  simp



/-- **A branch of `X = b` through every closed point over `(p, dX − a)`** (going down for the integral
closure of `ℤ[X]`, then the localization `B = (ℤ ∖ 0)⁻¹ C`). -/
theorem exists_branch (p : ℕ) [Fact p.Prime] (b : ℚ) (hb : 0 ≤ padicValRat p b) :
    letI := intPolyAlg E
    ∀ 𝔓 : Ideal (integralClosure ℤ[X] E), 𝔓.IsMaximal →
      C (p : ℤ) ∈ 𝔓.under ℤ[X] → C (b.den : ℤ) * X - C b.num ∈ 𝔓.under ℤ[X] →
      ∃ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime ∧ Q.under ℚ[X] = Ideal.span {X - C b} ∧
        Q.comap (zqIncl E) ≤ 𝔓 := by
  letI := intPolyAlg E
  intro 𝔓 h𝔓 hp𝔓 hb𝔓
  set m := 𝔓.under ℤ[X] with hmdef
  haveI : m.IsMaximal := Ideal.IsMaximal.under ℤ[X] 𝔓
  have hspan : (Ideal.span {X - C b} : Ideal ℚ[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C b)
  set h : Ideal ℤ[X] := (Ideal.span {X - C b}).comap (Polynomial.mapRingHom (Int.castRingHom ℚ))
    with hhdef
  haveI : h.IsPrime := Ideal.comap_isPrime _ _
  have hhm : h ≤ m := by
    intro u hu
    rw [hhdef, Ideal.mem_comap, Ideal.mem_span_singleton, coe_mapRingHom, dvd_iff_isRoot] at hu
    rw [mem_m_iff p b hb m hp𝔓 hb𝔓]
    have h0 : (nval b u : ℚ) = 0 := by
      rw [nval_cast, IsRoot.def.mp hu, mul_zero]
    rw [Int.cast_eq_zero.mp h0]
    exact dvd_zero _
  haveI : 𝔓.LiesOver m := ⟨rfl⟩
  have hinjE : Function.Injective (algebraMap ℤ[X] (integralClosure ℤ[X] E)) := by
    intro x y hxy
    apply algebraMap_int_injective (E := E)
    have := congrArg (fun z : integralClosure ℤ[X] E => (z : E)) hxy
    simpa using this
  haveI : FaithfulSMul ℤ[X] (integralClosure ℤ[X] E) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjE
  obtain ⟨QC, hQC𝔓, hQCp, hQCl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := h) (q := m) 𝔓 hhm
  have hQCu : QC.under ℤ[X] = h := hQCl.over.symm
  -- nonzero integers are not in `QC`
  have hint_not : ∀ k : ℤ, k ≠ 0 → (k : integralClosure ℤ[X] E) ∉ QC := by
    intro k hk hkQ
    have h1 : (C k : ℤ[X]) ∈ h := by
      rw [← hQCu, Ideal.under_def, Ideal.mem_comap]
      simpa using hkQ
    rw [hhdef, Ideal.mem_comap, Ideal.mem_span_singleton, coe_mapRingHom, Polynomial.map_C,
      eq_intCast] at h1
    have h2 := Polynomial.natDegree_le_of_dvd h1 (by simpa using hk)
    simp at h2
  -- the prime `Q` of `B` above `QC`
  let Q : Ideal (integralClosure ℚ[X] E) :=
    { carrier := {y | ∃ k : ℤ, k ≠ 0 ∧ ∃ c ∈ QC, (c : E) = (k : E) * y}
      zero_mem' := ⟨1, one_ne_zero, 0, QC.zero_mem, by simp⟩
      add_mem' := by
        rintro y₁ y₂ ⟨k₁, hk₁, c₁, hc₁, e₁⟩ ⟨k₂, hk₂, c₂, hc₂, e₂⟩
        refine ⟨k₁ * k₂, mul_ne_zero hk₁ hk₂, (k₂ : integralClosure ℤ[X] E) * c₁ + k₁ * c₂,
          QC.add_mem (QC.mul_mem_left _ hc₁) (QC.mul_mem_left _ hc₂), ?_⟩
        simp only [AddMemClass.coe_add,
          MulMemClass.coe_mul, SubringClass.coe_intCast, e₁, e₂, Int.cast_mul]
        ring
      smul_mem' := by
        rintro z y ⟨k, hk, c, hc, e⟩
        obtain ⟨k₀, hk₀, c₀, e₀⟩ := exists_int_mul_mem z
        refine ⟨k₀ * k, mul_ne_zero hk₀ hk, c₀ * c, QC.mul_mem_left _ hc, ?_⟩
        simp only [smul_eq_mul, MulMemClass.coe_mul, e, e₀, Int.cast_mul]
        ring }
  have hmemQ : ∀ y, y ∈ Q ↔ ∃ k : ℤ, k ≠ 0 ∧ ∃ c ∈ QC, (c : E) = (k : E) * y := fun _ => Iff.rfl
  have hQprime : Q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmemQ]
      rintro ⟨k, hk, c, hc, e⟩
      apply hint_not k hk
      have : c = (k : integralClosure ℤ[X] E) := Subtype.ext (by simpa using e)
      rwa [← this]
    · intro y z hyz
      rw [hmemQ] at hyz
      obtain ⟨k, hk, c, hc, e⟩ := hyz
      obtain ⟨k₁, hk₁, c₁, e₁⟩ := exists_int_mul_mem y
      obtain ⟨k₂, hk₂, c₂, e₂⟩ := exists_int_mul_mem z
      have hmul : (k : integralClosure ℤ[X] E) * (c₁ * c₂) =
          ((k₁ * k₂ : ℤ) : integralClosure ℤ[X] E) * c := by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul, SubringClass.coe_intCast, e₁, e₂, e, Int.cast_mul]
        ring
      have hin : (k : integralClosure ℤ[X] E) * (c₁ * c₂) ∈ QC := by
        rw [hmul]; exact QC.mul_mem_left _ hc
      rcases hQCp.mem_or_mem hin with h1 | h1
      · exact absurd h1 (hint_not k hk)
      rcases hQCp.mem_or_mem h1 with h2 | h2
      · exact Or.inl ⟨k₁, hk₁, c₁, h2, e₁⟩
      · exact Or.inr ⟨k₂, hk₂, c₂, h2, e₂⟩
  refine ⟨Q, hQprime, ?_, ?_⟩
  · -- `Q` lies over `X − b`
    have hle : Ideal.span {X - C b} ≤ Q.under ℚ[X] := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℚ[X] (integralClosure ℚ[X] E) (X - C b) ∈ Q
      refine ⟨b.den, by exact_mod_cast b.den_nz, algebraMap ℤ[X] (integralClosure ℤ[X] E)
        (C (b.den : ℤ) * X - C b.num), ?_, ?_⟩
      · rw [← Ideal.mem_comap, ← Ideal.under_def, hQCu, hhdef, Ideal.mem_comap,
          Ideal.mem_span_singleton]
        refine ⟨C (b.den : ℚ), ?_⟩
        rw [coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_C, Polynomial.map_X]
        simp only [eq_intCast, Int.cast_natCast]
        rw [← Rat.mul_den_eq_num b, C_mul]
        ring
      · show algebraMap ℚ[X] E ((C (b.den : ℤ) * X - C b.num).map (Int.castRingHom ℚ)) =
          ((b.den : ℤ) : E) * algebraMap ℚ[X] E (X - C b)
        rw [show (((b.den : ℤ) : E)) = algebraMap ℚ[X] E (C (b.den : ℚ)) by simp, ← map_mul]
        congr 1
        rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_C, Polynomial.map_X]
        simp only [eq_intCast, Int.cast_natCast]
        rw [← Rat.mul_den_eq_num b, C_mul]
        ring
    haveI : (Q.under ℚ[X]).IsPrime := Ideal.IsPrime.under _ Q
    exact (hspan.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  · intro c hc
    rw [Ideal.mem_comap, hmemQ] at hc
    obtain ⟨k, hk, c', hc', e⟩ := hc
    have : c' = (k : integralClosure ℤ[X] E) * c := Subtype.ext (e.trans (by push_cast; rfl))
    rw [this] at hc'
    rcases hQCp.mem_or_mem hc' with h1 | h1
    · exact absurd h1 (hint_not k hk)
    · exact hQC𝔓 h1

/-- **GLUE (local geometry of tame covers at a closed point; h-b1 §3 Lemma NV step 3, geometric half).**
Hypotheses as in `NVLocalInertia` minus the residue fields. Let `C` and `B` be the integral closures of `ℤ[X]`
and `ℚ[X]` in `E`, and `𝔓` a maximal ideal of `C` over `m_b = (p, dX − a)` (`b = a/d`). Then the branch of
`X = b` through `𝔓` is unique and normal there: for every prime `Q` of `B` over `X − b` with `Q ∩ C ⊆ 𝔓`
(one exists: `exists_branch`), every other such prime equals `Q`, and every element of `B/Q` integral over `ℤ`
is a quotient `c₁/c₂` of images of `c₁, c₂ ∈ C` with `c₂ ∉ 𝔓` (the localization of `C/(Q ∩ C)` at `𝔓` contains
the ring of integers of the number field `B/Q`, i.e. it is normal).
*Proof route* (not compiled): Abhyankar's lemma (SGA 1 XIII 5.2–5.3, UNVERIFIED numbers) at the closed point:
after the Kummer base change `A' = ℤ_(p)[ζ_N, p^{1/N}][r]_{(p^{1/N}, r)}`, `r^N = X − b`, `N = |G|`, the
normalization is unramified in codimension one (the kernel's T2 at both divisors; base change of the
unramified horizontal primes, by `BranchData` and distinctness mod `p`), hence étale by purity
(`PropTSGlue.purityGlobalDim2`, proved); its specialization along `r = 0` is étale over the DVR
`ℤ_(p)[ζ_N, p^{1/N}]`, hence normal, which gives a unique and normal branch upstairs; going down and
invariants under the tame group `Gal(E(ζ_N, r, p^{1/N})/E)` descend both to `E`. -/
def BranchRegular : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf → Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    ∀ b ∈ S,
    letI := intPolyAlg E
    ∀ 𝔓 : Ideal (integralClosure ℤ[X] E), 𝔓.IsMaximal →
      C (p : ℤ) ∈ 𝔓.under ℤ[X] → C (b.den : ℤ) * X - C b.num ∈ 𝔓.under ℤ[X] →
      ∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime → Q.under ℚ[X] = Ideal.span {X - C b} →
        Q.comap (zqIncl E) ≤ 𝔓 →
        (∀ Q' : Ideal (integralClosure ℚ[X] E), Q'.IsPrime →
          Q'.under ℚ[X] = Ideal.span {X - C b} → Q'.comap (zqIncl E) ≤ 𝔓 → Q' = Q) ∧
        (∀ z : integralClosure ℚ[X] E ⧸ Q, IsIntegral ℤ z →
          ∃ c₁ c₂ : integralClosure ℤ[X] E, c₂ ∉ 𝔓 ∧
            Ideal.Quotient.mk Q (zqIncl E c₂) * z = Ideal.Quotient.mk Q (zqIncl E c₁))

set_option maxHeartbeats 1600000 in
/-- **`NVLocalInertia` from `BranchRegular`** (compiled). `τ` in the inertia of a vertical prime `q` fixes a
maximal ideal `𝔓 ⊇ q` over `m_b`, hence the unique branch `Q` through `𝔓`; it acts on the number field `B/Q`
inside the inertia group of the prime `{c₁/c₂ : c₁ ∈ 𝔓}` of its ring of integers, which is unramified; so it acts
trivially on `B/Q`, i.e. `τ ∈ I_Q` (`g = 1`). -/
theorem nvLocalInertia_of_branchRegular (h : BranchRegular) : NVLocalInertia := by
  intro E _ _ _ _ _ _ S n nInf p hp hB hdeg hint hdist b hb hres
  letI := intPolyAlg E
  intro q hq hqu τ hτ
  haveI : Fact p.Prime := ⟨hp⟩
  -- the maximal ideal `𝔓 ⊇ q` over `m_b`
  obtain ⟨m, hm, hpm, hbm⟩ := exists_secIdeal p b (hint b hb)
  have hqm : q.under ℤ[X] ≤ m := by
    rw [hqu, vertPrime, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
    exact hpm
  obtain ⟨𝔓, hq𝔓, h𝔓p, h𝔓u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m q hqm
  haveI := h𝔓p
  haveI : 𝔓.LiesOver m := ⟨h𝔓u.symm⟩
  have h𝔓max : 𝔓.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal 𝔓 m
  obtain ⟨Q, hQ, hQu, hQ𝔓⟩ := exists_branch p b (hint b hb) 𝔓 h𝔓max (h𝔓u ▸ hpm) (h𝔓u ▸ hbm)
  obtain ⟨hUB, hN⟩ :=
    h E S n nInf p hp hB hdeg hint hdist b hb 𝔓 h𝔓max (h𝔓u ▸ hpm) (h𝔓u ▸ hbm) Q hQ hQu hQ𝔓
  haveI := hQ
  have hq𝔓' : ∀ x, x ∈ q → x ∈ 𝔓 := fun x hx => hq𝔓 hx
  -- `τ` maps `Q` to itself (unibranch)
  have hτC : ∀ c : integralClosure ℤ[X] E, ∃ c' : integralClosure ℤ[X] E,
      (c' : E) = τ c ∧ c' - c ∈ 𝔓 := by
    intro c
    obtain ⟨c', hc', hcq⟩ := hτ c
    exact ⟨c', hc', hq𝔓' _ hcq⟩
  have hQτ : Q = Q.map (galB τ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E) := by
    symm
    haveI : (Q.map (galB τ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E)).IsPrime :=
      Ideal.map_isPrime_of_equiv (galB τ)
    refine hUB _ inferInstance ?_ ?_
    · ext f
      have : (galB τ).symm (algebraMap ℚ[X] (integralClosure ℚ[X] E) f) =
          algebraMap ℚ[X] (integralClosure ℚ[X] E) f := by
        apply Subtype.ext
        show τ⁻¹ (algebraMap ℚ[X] E f) = algebraMap ℚ[X] E f
        exact gal_fix τ⁻¹ f
      rw [Ideal.under_def, Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap, this, ← hQu,
        Ideal.under_def, Ideal.mem_comap]
    · intro c hc
      rw [Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap] at hc
      obtain ⟨c'', hc''⟩ := galC_mem τ⁻¹ c
      have h1 : (galB τ).symm (zqIncl E c) = zqIncl E c'' := by
        apply Subtype.ext
        show τ⁻¹ (c : E) = c''
        rw [hc'']
      rw [h1] at hc
      have h2 : c'' ∈ 𝔓 := hQ𝔓 hc
      obtain ⟨c₃, hc₃, hc₃𝔓⟩ := hτC c''
      have h3 : c₃ = c := by
        apply Subtype.ext
        rw [hc₃, hc'']
        show τ (τ⁻¹ (c : E)) = c
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
      rw [h3] at hc₃𝔓
      have := 𝔓.add_mem hc₃𝔓 h2
      simpa using this
  -- `Q` is maximal, `κ = B/Q` is a field
  have hspan : (Ideal.span {X - C b} : Ideal ℚ[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C b)
  haveI : Q.LiesOver (Ideal.span {X - C b}) := ⟨hQu.symm⟩
  haveI hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {X - C b})
  letI : Field (integralClosure ℚ[X] E ⧸ Q) := Ideal.Quotient.field Q
  -- an embedding `φ : κ → ℚ̄`
  have key : ∀ f : ℚ[X], Ideal.Quotient.mk Q (algebraMap ℚ[X] (integralClosure ℚ[X] E) f) =
      Ideal.Quotient.mk Q (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C (f.eval b))) := by
    intro f
    rw [Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap, ← Ideal.under_def, hQu,
      Ideal.mem_span_singleton]
    exact X_sub_C_dvd_sub_C_eval
  obtain ⟨φ⟩ : Nonempty (integralClosure ℚ[X] E ⧸ Q →+* Qbar) := by
    letI alg : Algebra ℚ (integralClosure ℚ[X] E ⧸ Q) :=
      ((Ideal.Quotient.mk Q).comp ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp C)).toAlgebra
    haveI : Algebra.IsAlgebraic ℚ (integralClosure ℚ[X] E ⧸ Q) := by
      refine ⟨fun z => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨f, hf, hy0⟩ := Algebra.IsIntegral.isIntegral (R := ℚ[X]) y
      have hcomp : (Ideal.Quotient.mk Q).comp (algebraMap ℚ[X] (integralClosure ℚ[X] E)) =
          (algebraMap ℚ (integralClosure ℚ[X] E ⧸ Q)).comp (Polynomial.evalRingHom b) := by
        ext f
        · simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, coe_evalRingHom, eval_C]
        · simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, coe_evalRingHom, eval_X]
          rw [key X, eval_X]
      refine (IsIntegral.isAlgebraic ⟨f.map (Polynomial.evalRingHom b), hf.map _, ?_⟩)
      rw [eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hy0, map_zero]
    haveI : Module.IsTorsionFree ℚ (integralClosure ℚ[X] E ⧸ Q) :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr (RingHom.injective _)
    haveI : Module.IsTorsionFree ℚ Qbar :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr (RingHom.injective _)
    exact ⟨(IsAlgClosed.lift (R := ℚ) (M := Qbar) (S := integralClosure ℚ[X] E ⧸ Q)).toRingHom⟩
  -- the number field `L = φ(κ)` and `e : κ ≃ L`
  set L := IntermediateField.adjoin ℚ (Set.range φ) with hLdef
  haveI : FiniteDimensional ℚ L := finiteDimensional_residue E b Q hQu φ
  haveI : NumberField L := ⟨⟩
  have hunL : UnramifiedAt L p := hres Q hQ hQu φ
  let f : integralClosure ℚ[X] E ⧸ Q →+* L :=
    { toFun := fun z => ⟨φ z, IntermediateField.subset_adjoin _ _ ⟨z, rfl⟩⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ x y)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun x y => Subtype.ext (φ.map_add x y) }
  have hfsurj : Function.Surjective f := by
    have hle : L ≤ (φ.fieldRange).toIntermediateField (fun q : ℚ =>
        ⟨(q : integralClosure ℚ[X] E ⧸ Q), (map_ratCast φ q).trans (eq_ratCast _ q).symm⟩) := by
      rw [hLdef, IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact ⟨z, rfl⟩
    rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hle hy
    exact ⟨z, Subtype.ext hz⟩
  let e : integralClosure ℚ[X] E ⧸ Q ≃+* L := RingEquiv.ofBijective f ⟨f.injective, hfsurj⟩
  have he : ∀ z, (e z : Qbar) = φ z := fun z => rfl
  -- `σ`: the action of `τ` on `κ`, transported to `L`
  let σκ : integralClosure ℚ[X] E ⧸ Q ≃+* integralClosure ℚ[X] E ⧸ Q :=
    Ideal.quotientEquiv Q Q (galB τ) hQτ
  have hσκ : ∀ y, σκ (Ideal.Quotient.mk Q y) = Ideal.Quotient.mk Q (galB τ y) := fun y => rfl
  let σL : L ≃+* L := (e.symm.trans σκ).trans e
  let σ : L ≃ₐ[ℚ] L := AlgEquiv.ofRingEquiv (f := σL) (fun x => by
    rw [eq_ratCast (algebraMap ℚ L), map_ratCast])
  -- `ψ : C → L`
  let ψ : integralClosure ℤ[X] E →+* L :=
    e.toRingHom.comp ((Ideal.Quotient.mk Q).comp (zqIncl E))
  have hψ : ∀ c, ψ c = e (Ideal.Quotient.mk Q (zqIncl E c)) := fun c => rfl
  have hker : ∀ c, ψ c = 0 → c ∈ 𝔓 := by
    intro c hc
    rw [hψ, map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem] at hc
    exact hQ𝔓 hc
  have hNL : ∀ y : 𝓞 L, ∃ c₁ c₂ : integralClosure ℤ[X] E, c₂ ∉ 𝔓 ∧ (y : L) * ψ c₂ = ψ c₁ := by
    intro y
    have hy : IsIntegral ℤ (e.symm (y : L)) :=
      (y.2 : IsIntegral ℤ (y : L)).map (e.symm.toRingHom.toIntAlgHom)
    obtain ⟨c₁, c₂, hc₂, hc⟩ := hN _ hy
    refine ⟨c₁, c₂, hc₂, ?_⟩
    rw [hψ, hψ, ← hc, map_mul, RingEquiv.apply_symm_apply, mul_comm]
  have hσψ : ∀ c : integralClosure ℤ[X] E, ∃ c' : integralClosure ℤ[X] E,
      σ (ψ c) = ψ c' ∧ c' - c ∈ 𝔓 := by
    intro c
    obtain ⟨c', hc', hc'𝔓⟩ := hτC c
    refine ⟨c', ?_, hc'𝔓⟩
    show e (σκ (e.symm (e (Ideal.Quotient.mk Q (zqIncl E c))))) = ψ c'
    rw [RingEquiv.symm_apply_apply, hσκ, hψ]
    congr 2
    apply Subtype.ext
    rw [galB_apply]
    exact hc'.symm
  have hp𝔓 : (p : integralClosure ℤ[X] E) ∈ 𝔓 := by
    have h1 : algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ)) ∈ 𝔓 := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, h𝔓u]; exact hpm
    simpa using h1
  have hσ1 : σ = 1 := eq_one_of_primeOf 𝔓 ψ hker hNL σ hσψ p hp𝔓 hunL
  -- conclusion: `τ ∈ I_Q`
  refine ⟨Q, hQ, hQu, 1, ?_⟩
  rw [one_mul, inv_one, mul_one]
  intro y
  refine ⟨galB τ y, galB_apply τ y, ?_⟩
  rw [← Ideal.Quotient.eq, ← hσκ]
  have h2 : σL (e (Ideal.Quotient.mk Q y)) = e (Ideal.Quotient.mk Q y) := by
    have := congrArg (fun g : L ≃ₐ[ℚ] L => g (e (Ideal.Quotient.mk Q y))) hσ1
    rw [AlgEquiv.one_apply] at this
    exact this
  have h3 : e (σκ (Ideal.Quotient.mk Q y)) = e (Ideal.Quotient.mk Q y) := by
    rw [← h2]
    show e (σκ (Ideal.Quotient.mk Q y)) = e (σκ (e.symm (e (Ideal.Quotient.mk Q y))))
    rw [RingEquiv.symm_apply_apply]
  exact e.injective h3

/-- **The ramification index is unchanged by localizing the base at a submonoid** missing the prime
(Mathlib's `IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx`, for any submonoid). -/
theorem ramificationIdx_map_localization {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S]
    [CommRing Rₘ] [CommRing Sₘ] [Algebra R S] [Algebra R Rₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] [IsScalarTower R Rₘ Sₘ] (M : Submonoid R)
    [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    (P : Ideal S) [P.IsPrime] (hP : Disjoint (M : Set R) (P.under R)) :
    (P.map (algebraMap S Sₘ)).ramificationIdx Rₘ = P.ramificationIdx R := by
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid S M : Submonoid S) : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxP
    exact Set.disjoint_left.mp hP hx hxP
  haveI hPm : (P.map (algebraMap S Sₘ)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ Sₘ P inferInstance hdisj
  have hcomap : (P.map (algebraMap S Sₘ)).comap (algebraMap S Sₘ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ Sₘ inferInstance hdisj
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def]
  let R₁ := Localization.AtPrime (P.map (algebraMap S Sₘ))
  let R₂ := Localization.AtPrime P
  haveI : (P.map (algebraMap S Sₘ)).LiesOver P := ⟨hcomap.symm⟩
  let : Algebra R₂ R₁ := Localization.AtPrime.algebraOfLiesOver P (P.map (algebraMap S Sₘ))
  haveI : IsLocalization.AtPrime R₁ P := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S M) R₁ (P.map (algebraMap S Sₘ))
    exact hcomap.symm
  have h : Function.Bijective (algebraMap R₂ R₁) :=
    (Localization.algEquiv P.primeCompl R₁).bijective
  have hunder : (P.map (algebraMap S Sₘ)).under Rₘ = (P.under R).map (algebraMap R Rₘ) := by
    rw [← IsLocalization.map_under M Rₘ ((P.map (algebraMap S Sₘ)).under Rₘ)]
    congr 1
    have hc : Ideal.under S (P.map (algebraMap S Sₘ)) = P := hcomap
    rw [Ideal.under_under, ← Ideal.under_under (B := S), hc]
  have hcomp : (algebraMap R₂ R₁).comp (algebraMap R R₂) = (algebraMap Rₘ R₁).comp (algebraMap R Rₘ) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have key : (P.under R).map (algebraMap R R₂) =
      (((P.map (algebraMap S Sₘ)).under Rₘ).map (algebraMap Rₘ R₁)).comap (algebraMap R₂ R₁) := by
    rw [hunder, Ideal.map_map, ← hcomp, ← Ideal.map_map, Ideal.comap_map_of_bijective _ h]
  rw [Module.length_quotient, Module.length_quotient, key, Ideal.coheight_comap_of_surjective _ h.2]


/-- **GLUE (local algebra of tame covers; the geometric half of h-b1 §3 step 3 in general form).**
Let `R` be a noetherian domain with fraction field `K`, `m` a maximal ideal with `R_m` regular local of
dimension `2` and `m = (f, g)`, `(f)` prime, and residue characteristic `p` (`p ∈ m`). Let `L/K` be finite
Galois of degree `< p` (so all ramification near `m` is tame), with integral closure `S` of `R`, unramified
(`e = 1`) at every height-one prime `P ⊆ m` not containing `f` or `g` (the branch locus near `m` lies in the
normal-crossings divisor `fg = 0`). Then at every maximal ideal `𝔓` of `S` over `m`, the branch of `f = 0` is
unique and normal: all primes of `S` over `(f)` contained in `𝔓` coincide, and for such a prime `Q` the
localization of `S/Q` at `𝔓` is integrally closed (every element of a fraction field of `S/Q` integral over
`S/Q` is a quotient `a/s` with `s ∉ 𝔓`).
*Proof route* (not compiled): Abhyankar's lemma (SGA 1 XIII 5.2–5.3, UNVERIFIED numbers): after the Kummer base
change `R_m[ζ_N][T, U]/(T^N − f, U^N − g)` (`N = [L : K]`, invertible; a regular local ring of dimension `2`
after localizing), the normalization of `L` is unramified in codimension one (Abhyankar's lemma for DVRs, the
kernel's T2, at `(T)` and `(U)`; base change at the other height-one primes), hence étale by purity (the
chain's `PropTSGlue.purityGlobalDim2`, proved); its specialization along `T = 0` is étale over a DVR, hence
normal, so each closed point carries a unique normal branch; going down and the Reynolds operator of the tame
group `Gal(L(ζ_N, T, U)/L)` (with CRT, the branches upstairs being comaximal at `𝔓`) descend both to `S`
(docs/research/nv-local.md §2.3). -/
def TameBranchNormal : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L] (m : Ideal R) [m.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime m) → ringKrullDim (Localization.AtPrime m) = 2 →
    ∀ f g : R, m = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : R) ∈ m → Module.finrank K L < p →
    (∀ P : Ideal R, P.IsPrime → P.height = 1 → P ≤ m → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure R L), P'.IsPrime → P'.under R = P →
        P'.ramificationIdx R = 1) →
    ∀ 𝔓 : Ideal (integralClosure R L), 𝔓.IsMaximal → 𝔓.under R = m →
    ∀ Q : Ideal (integralClosure R L), Q.IsPrime → Q.under R = Ideal.span {f} → Q ≤ 𝔓 →
      (∀ Q' : Ideal (integralClosure R L), Q'.IsPrime → Q'.under R = Ideal.span {f} → Q' ≤ 𝔓 →
        Q' = Q) ∧
      (∀ (F : Type) [CommRing F] [Algebra (integralClosure R L ⧸ Q) F]
          [IsFractionRing (integralClosure R L ⧸ Q) F] (z : F),
        IsIntegral (integralClosure R L ⧸ Q) z →
        ∃ a s : integralClosure R L, s ∉ 𝔓 ∧
          algebraMap _ F (Ideal.Quotient.mk Q s) * z = algebraMap _ F (Ideal.Quotient.mk Q a))

/-! ## `BranchRegular` from `TameBranchNormal` -/

/-- `m = (dX − a, p)` for a maximal ideal of `ℤ[X]` containing both (`b = a/d`, `p ∤ d`). -/
theorem maximal_eq_span (p : ℕ) [hp : Fact p.Prime] (b : ℚ) (hb : 0 ≤ padicValRat p b)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m)
    (hbm : C (b.den : ℤ) * X - C b.num ∈ m) :
    m = Ideal.span {C (b.den : ℤ) * X - C b.num, C (p : ℤ)} := by
  apply le_antisymm
  · intro u hu
    have h1 := homog_mem (Ideal.span {C (b.den : ℤ) * X - C b.num, C (p : ℤ)}) b.num b.den
      (Ideal.subset_span (by simp)) u
    have hdv : (p : ℤ) ∣ nval b u := (mem_m_iff p b hb m hpm hbm u).mp hu
    obtain ⟨t, ht⟩ := hdv
    have h2 : C (nval b u) ∈ Ideal.span {C (b.den : ℤ) * X - C b.num, C (p : ℤ)} := by
      rw [ht, C_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have h3 : C ((b.den : ℤ) ^ u.natDegree) * u ∈
        Ideal.span {C (b.den : ℤ) * X - C b.num, C (p : ℤ)} := by
      have := Ideal.add_mem _ h1 h2
      simpa [nval] using this
    -- `d^k` is invertible mod `p`
    have hcop : IsCoprime ((b.den : ℤ) ^ u.natDegree) (p : ℤ) := by
      apply IsCoprime.pow_left
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hnd := not_dvd_den_of_nonneg p b hb
      have : Nat.Coprime b.den p :=
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd))
      exact_mod_cast this
    obtain ⟨α, β, hαβ⟩ := hcop
    have : u = C α * (C ((b.den : ℤ) ^ u.natDegree) * u) + C β * u * C (p : ℤ) := by
      have h := congrArg (C : ℤ → ℤ[X]) hαβ
      rw [C_add, C_mul, C_mul, C_1] at h
      linear_combination (-u) * h
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hbm
    · exact hpm


/-- `dX − a` is primitive (`b = a/d` in lowest terms). -/
theorem secGen_isPrimitive (b : ℚ) : (C (b.den : ℤ) * X - C b.num).IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have e1 : (C (b.den : ℤ) * X - C b.num).coeff 1 = (b.den : ℤ) := by
    rw [coeff_sub, coeff_C_mul, coeff_X_one, coeff_C]; simp
  have e0 : (C (b.den : ℤ) * X - C b.num).coeff 0 = -b.num := by
    rw [coeff_sub, coeff_C_mul, coeff_X_zero, coeff_C]; simp
  have h1 : r ∣ (b.den : ℤ) := e1 ▸ hr 1
  have h0 : r ∣ b.num := dvd_neg.mp (e0 ▸ hr 0)
  have hcop : IsCoprime b.num (b.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact b.reduced
  exact hcop.isUnit_of_dvd' h0 h1

theorem secGen_map (b : ℚ) :
    (C (b.den : ℤ) * X - C b.num).map (Int.castRingHom ℚ) = C (b.den : ℚ) * (X - C b) := by
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
  simp only [eq_intCast, Int.cast_natCast]
  rw [← Rat.mul_den_eq_num b, C_mul]
  ring

/-- The prime `(dX − a)` of `ℤ[X]` is the kernel of `X ↦ b` (Gauss's lemma). -/
theorem span_secGen_eq (b : ℚ) : Ideal.span {C (b.den : ℤ) * X - C b.num} =
    (Ideal.span {X - C b}).comap (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
  ext u
  rw [Ideal.mem_span_singleton, Ideal.mem_comap, Ideal.mem_span_singleton, coe_mapRingHom,
    IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (secGen_isPrimitive b)]
  have hmap : (C (b.den : ℤ) * X - C b.num).map (Int.castRingHom ℚ) = C (b.den : ℚ) * (X - C b) := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
    simp only [eq_intCast, Int.cast_natCast]
    rw [← Rat.mul_den_eq_num b, C_mul]
    ring
  rw [hmap]
  have hu : IsUnit (C (b.den : ℚ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast b.den_nz))
  exact hu.mul_left_dvd

theorem span_secGen_isPrime (b : ℚ) : (Ideal.span {C (b.den : ℤ) * X - C b.num}).IsPrime := by
  rw [span_secGen_eq]
  haveI : (Ideal.span {X - C b} : Ideal ℚ[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C b)
  exact Ideal.comap_isPrime _ _


section Loc

variable (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E]

/-- The nonzero integers in `ℤ[X]`. -/
abbrev intSub : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])

omit [Algebra (RatFunc ℚ) E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] in
/-- The `ℚ[X]`-closure is the localization of the `ℤ[X]`-closure at the nonzero integers. -/
theorem isLocalization_B :
    letI := intPolyAlg E
    letI : Algebra (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := (zqIncl E).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) intSub)
      (integralClosure ℚ[X] E) := by
  letI := intPolyAlg E
  letI : Algebra (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := (zqIncl E).toAlgebra
  have hcoe : ∀ k : ℤ, (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
      (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) : E) = (k : E) := by
    intro k
    show algebraMap ℚ[X] E ((C k).map (Int.castRingHom ℚ)) = (k : E)
    simp
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩⟩
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hk
    refine ⟨⟨algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k) |> algebraMap _ (integralClosure ℚ[X] E),
      algebraMap ℚ[X] (integralClosure ℚ[X] E) (C (k : ℚ)⁻¹), ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show ((algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
        (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) : E)) * algebraMap ℚ[X] E (C (k : ℚ)⁻¹) = 1
      rw [hcoe, show (k : E) = algebraMap ℚ[X] E (C (k : ℚ)) by simp, ← map_mul, ← C_mul,
        mul_inv_cancel₀ hk0, C_1, map_one]
    · apply Subtype.ext
      show algebraMap ℚ[X] E (C (k : ℚ)⁻¹) * ((algebraMap (integralClosure ℤ[X] E)
        (integralClosure ℚ[X] E) (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) : E)) = 1
      rw [hcoe, show (k : E) = algebraMap ℚ[X] E (C (k : ℚ)) by simp, ← map_mul, ← C_mul,
        inv_mul_cancel₀ hk0, C_1, map_one]
  · intro z
    obtain ⟨k, hk, c, hc⟩ := exists_int_mul_mem z
    refine ⟨⟨c, ⟨_, ⟨C k, ⟨k, mem_nonZeroDivisors_of_ne_zero hk, rfl⟩, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    show (z : E) * ((algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
      (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) : E)) = c
    rw [hcoe, hc, mul_comm]
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : x = y := Subtype.ext (congrArg (fun w : integralClosure ℚ[X] E => (w : E)) hxy)
    rw [this]

omit [IsScalarTower ℚ[X] (RatFunc ℚ) E] in
/-- **Height-one primes near `m` off `(dX − a)` and `(p)` are unramified** (from `BranchData` and the
distinctness mod `p`; the ramification index is transported from the `ℚ[X]`-closure by
`ramificationIdx_map_localization`). -/
theorem unram_near (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ) [hp : Fact p.Prime]
    (hB : BranchData E S n nInf) (hint : ∀ b ∈ S, 0 ≤ padicValRat p b)
    (hdist : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) (b : ℚ) (hb : b ∈ S)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m)
    (hbm : C (b.den : ℤ) * X - C b.num ∈ m) :
    letI := intPolyAlg E
    ∀ P : Ideal ℤ[X], P.IsPrime → P.height = 1 → P ≤ m → C (b.den : ℤ) * X - C b.num ∉ P →
      C (p : ℤ) ∉ P → ∀ P' : Ideal (integralClosure ℤ[X] E), P'.IsPrime → P'.under ℤ[X] = P →
        P'.ramificationIdx ℤ[X] = 1 := by
  letI := intPolyAlg E
  intro P hP _ hPm hfP hgP P' hP' hP'u
  letI : Algebra (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := (zqIncl E).toAlgebra
  letI : Algebra ℤ[X] ℚ[X] := Polynomial.algebra ℤ ℚ
  letI : Algebra ℤ[X] (integralClosure ℚ[X] E) :=
    ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp (algebraMap ℤ[X] ℚ[X])).toAlgebra
  haveI : IsScalarTower ℤ[X] ℚ[X] (integralClosure ℚ[X] E) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext (by
      show algebraMap ℚ[X] E (algebraMap ℤ[X] ℚ[X] x) = algebraMap ℚ[X] E (x.map (Int.castRingHom ℚ))
      rw [Polynomial.algebraMap_def ℤ ℚ]
      congr 2))
  haveI : IsLocalization intSub ℚ[X] := Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  haveI := isLocalization_B E
  haveI := hP'
  -- `P` contains no nonzero integer
  have hPZ : P.comap (C : ℤ →+* ℤ[X]) = ⊥ := by
    by_contra hne
    haveI : (P.comap (C : ℤ →+* ℤ[X])).IsPrime := Ideal.comap_isPrime _ _
    have hmax : (P.comap (C : ℤ →+* ℤ[X])).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
    have hle : P.comap (C : ℤ →+* ℤ[X]) ≤ m.comap C := Ideal.comap_mono hPm
    have hmne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›)
    have heq := hmax.eq_of_le hmne hle
    apply hgP
    rw [← Ideal.mem_comap, heq, Ideal.mem_comap]
    exact hpm
  have hdisj : Disjoint ((intSub : Submonoid ℤ[X]) : Set ℤ[X]) (P'.under ℤ[X]) := by
    rw [hP'u, Set.disjoint_left]
    rintro _ ⟨k, hk, rfl⟩ hkP
    have : k ∈ P.comap (C : ℤ →+* ℤ[X]) := hkP
    rw [hPZ, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hk this
  have hdisj' : Disjoint ((Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) intSub :
      Submonoid (integralClosure ℤ[X] E)) : Set (integralClosure ℤ[X] E)) (P' : Set _) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxP
    exact Set.disjoint_left.mp hdisj hx hxP
  haveI hPB : (P'.map (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P' inferInstance hdisj'
  have hcomapB : (P'.map (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E))).comap
      (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)) = P' :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance hdisj'
  rw [← ramificationIdx_map_localization (Rₘ := ℚ[X]) (Sₘ := integralClosure ℚ[X] E) intSub P' hdisj]
  refine hB.1 _ hPB ?_
  intro b' hb' hcon
  set F : ℤ[X] := C (b'.den : ℤ) * X - C b'.num with hFdef
  have hFm : algebraMap ℚ[X] (integralClosure ℚ[X] E) (F.map (Int.castRingHom ℚ)) ∈
      P'.map (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)) := by
    rw [← Ideal.mem_comap, ← Ideal.under_def, hcon]
    have hF : F ∈ Ideal.span {F} := Ideal.mem_span_singleton_self F
    rw [hFdef, span_secGen_eq b', Ideal.mem_comap] at hF
    exact hF
  have hFP : F ∈ P := by
    rw [← hP'u, Ideal.under_def, Ideal.mem_comap, ← hcomapB, Ideal.mem_comap,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X] ℚ[X],
      Polynomial.algebraMap_def ℤ ℚ]
    exact hFm
  by_cases hbb : b' = b
  · rw [hFdef, hbb] at hFP
    exact hfP hFP
  · apply (notMem_of_val_zero p b (hint b hb) m (Ideal.IsMaximal.ne_top ‹_›) hpm hbm F ?_ ?_)
      (hPm hFP)
    · rw [hFdef, secGen_map, eval_mul, eval_C, eval_sub, eval_X, eval_C]
      exact mul_ne_zero (by exact_mod_cast b'.den_nz) (sub_ne_zero.mpr (Ne.symm hbb))
    · rw [hFdef, secGen_map, eval_mul, eval_C, eval_sub, eval_X, eval_C,
        padicValRat.mul (by exact_mod_cast b'.den_nz) (sub_ne_zero.mpr (Ne.symm hbb)),
        hdist b hb b' hb' (Ne.symm hbb), padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (not_dvd_den_of_nonneg p b' (hint b' hb'))]
      simp

end Loc

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **`BranchRegular` from `TameBranchNormal`** (compiled): take `R = ℤ[X]`, `m = (dX − a, p)`, `f = dX − a`,
`g = p`; `ℤ[X]_m` is regular of dimension `2` (`regular_dim2_intPoly`), the other height-one primes near `m`
are unramified (`unram_near`), the branch `Q` of `B` gives the prime `Q ∩ C` of `C` over `(f)`, and `B/Q` is a
fraction field of `C/(Q ∩ C)` (`B` is the localization of `C` at the nonzero integers). -/
theorem branchRegular_of_tame (h : TameBranchNormal) : BranchRegular := by
  intro E _ _ _ _ _ _ S n nInf p hp hB hdeg hint hdist b hb
  letI := intPolyAlg E
  intro 𝔓 h𝔓 hp𝔓 hb𝔓 Q hQ hQu hQ𝔓
  haveI : Fact p.Prime := ⟨hp⟩
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  haveI := isFractionRing_int
  set m := 𝔓.under ℤ[X] with hmdef
  haveI : m.IsMaximal := Ideal.IsMaximal.under ℤ[X] 𝔓
  have hmne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊥ := by
    intro h0
    have : (p : ℤ) ∈ m.comap (C : ℤ →+* ℤ[X]) := hp𝔓
    rw [h0, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  obtain ⟨hreg, hdim⟩ := regular_dim2_intPoly m hmne
  have hm := maximal_eq_span p b (hint b hb) m hp𝔓 hb𝔓
  have hpR : (p : ℤ[X]) ∈ m := by rw [← map_natCast C p]; exact hp𝔓
  have hunr := unram_near E S n nInf p hB hint hdist b hb m hp𝔓 hb𝔓
  have hcomp : (zqIncl E).comp (algebraMap ℤ[X] (integralClosure ℤ[X] E)) =
      (algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    exact RingHom.ext (fun x => Subtype.ext rfl)
  have hunderC : ∀ Q' : Ideal (integralClosure ℚ[X] E), Q'.under ℚ[X] = Ideal.span {X - C b} →
      (Q'.comap (zqIncl E)).under ℤ[X] = Ideal.span {C (b.den : ℤ) * X - C b.num} := by
    intro Q' hQ'u
    rw [span_secGen_eq, ← hQ'u, Ideal.under_def, Ideal.under_def, Ideal.comap_comap, hcomp,
      ← Ideal.comap_comap]
  letI : Algebra (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := (zqIncl E).toAlgebra
  haveI hloc := isLocalization_B E
  let QC := Q.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E))
  haveI : QC.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨hUB, hN⟩ := h ℤ[X] (RatFunc ℚ) E m hreg hdim _ _ hm (span_secGen_isPrime b) p hp hpR hdeg
    hunr 𝔓 h𝔓 rfl QC inferInstance (hunderC Q hQu) hQ𝔓
  refine ⟨?_, ?_⟩
  · intro Q' hQ' hQ'u hQ'𝔓
    haveI : (Q'.comap (zqIncl E)).IsPrime := Ideal.comap_isPrime _ _
    have hc := hUB (Q'.comap (zqIncl E)) inferInstance (hunderC Q' hQ'u) hQ'𝔓
    rw [← IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) intSub)
      (integralClosure ℚ[X] E) Q', ← IsLocalization.map_under
      (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) intSub) (integralClosure ℚ[X] E) Q]
    exact congrArg (Ideal.map _) hc
  · intro z hz
    have hspan : (Ideal.span {X - C b} : Ideal ℚ[X]).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C b)
    haveI : Q.LiesOver (Ideal.span {X - C b}) := ⟨hQu.symm⟩
    haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {X - C b})
    letI alg : Algebra (integralClosure ℤ[X] E ⧸ QC) (integralClosure ℚ[X] E ⧸ Q) :=
      Ideal.Quotient.algebraQuotientOfLEComap le_rfl
    have hinj : Function.Injective (algebraMap (integralClosure ℤ[X] E ⧸ QC)
        (integralClosure ℚ[X] E ⧸ Q)) := Ideal.algebraMap_quotient_injective
    have hmk : ∀ c, algebraMap (integralClosure ℤ[X] E ⧸ QC) (integralClosure ℚ[X] E ⧸ Q)
        (Ideal.Quotient.mk QC c) = Ideal.Quotient.mk Q (zqIncl E c) := fun _ => rfl
    have hkQ : ∀ k : ℤ, k ≠ 0 → zqIncl E (k : integralClosure ℤ[X] E) ∉ Q := by
      intro k hk hkQ
      have hu : IsUnit (zqIncl E (k : integralClosure ℤ[X] E)) := by
        rw [map_intCast]
        refine isUnit_iff_exists.mpr ⟨algebraMap ℚ[X] (integralClosure ℚ[X] E) (C (k : ℚ)⁻¹), ?_, ?_⟩
        · apply Subtype.ext
          show (k : E) * algebraMap ℚ[X] E (C (k : ℚ)⁻¹) = 1
          rw [show (k : E) = algebraMap ℚ[X] E (C (k : ℚ)) by simp, ← map_mul, ← C_mul,
            mul_inv_cancel₀ (by exact_mod_cast hk), C_1, map_one]
        · apply Subtype.ext
          show algebraMap ℚ[X] E (C (k : ℚ)⁻¹) * (k : E) = 1
          rw [show (k : E) = algebraMap ℚ[X] E (C (k : ℚ)) by simp, ← map_mul, ← C_mul,
            inv_mul_cancel₀ (by exact_mod_cast hk), C_1, map_one]
      exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem _ hkQ hu)
    haveI : IsFractionRing (integralClosure ℤ[X] E ⧸ QC) (integralClosure ℚ[X] E ⧸ Q) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, hx⟩
        have hx0 := hinj.ne (nonZeroDivisors.ne_zero hx)
        rw [map_zero] at hx0
        obtain ⟨y, hy⟩ := Ideal.Quotient.exists_inv hx0
        exact IsUnit.of_mul_eq_one _ hy
      · intro w
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
        obtain ⟨k, hk, c, hc⟩ := exists_int_mul_mem y
        have hk0 : Ideal.Quotient.mk QC (k : integralClosure ℤ[X] E) ≠ 0 := by
          intro h0
          apply hkQ k hk
          rw [← Ideal.Quotient.eq_zero_iff_mem, ← hmk, h0, map_zero]
        refine ⟨⟨Ideal.Quotient.mk QC c, ⟨_, mem_nonZeroDivisors_of_ne_zero hk0⟩⟩, ?_⟩
        show Ideal.Quotient.mk Q y * algebraMap _ _ (Ideal.Quotient.mk QC (k : integralClosure ℤ[X] E)) =
          algebraMap _ _ (Ideal.Quotient.mk QC c)
        rw [hmk, hmk, ← map_mul]
        congr 1
        apply Subtype.ext
        show (y : E) * ((k : integralClosure ℤ[X] E) : E) = c
        rw [hc]; push_cast; ring
      · intro x y hxy
        exact ⟨1, by rw [hinj hxy]⟩
    haveI : IsScalarTower ℤ (integralClosure ℤ[X] E ⧸ QC) (integralClosure ℚ[X] E ⧸ Q) :=
      ⟨fun n a w => by
        rw [Algebra.smul_def, Algebra.smul_def, zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast,
          mul_assoc]⟩
    have hz' : IsIntegral (integralClosure ℤ[X] E ⧸ QC) z := hz.tower_top
    obtain ⟨a, s, hs, hsz⟩ := hN (integralClosure ℚ[X] E ⧸ Q) z hz'
    exact ⟨a, s, hs, hsz⟩


/-- **`NVLocalInertia` from `TameBranchNormal`** (compiled). -/
theorem nvLocalInertia_of_tame (h : TameBranchNormal) : NVLocalInertia :=
  nvLocalInertia_of_branchRegular (branchRegular_of_tame h)

/-- **`HeckeVertWitness` by route NV from the bundle fields and `BranchRegular`** (compiled): the inputs of
`SGRDirect.heckeVertWitness_of_nvElkies` with `NVLocalInertia` replaced by `BranchRegular`. -/
theorem heckeVertWitness_of_branchRegular (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hBR : BranchRegular) (hEl : QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted) : HDec.HeckeRestNV.HeckeVertWitness :=
  heckeVertWitness_of_nvElkies hRR hT hA hS hW (nvLocalInertia_of_branchRegular hBR) hEl


/-- **`HeckeVertWitness` by route NV from the bundle fields and `TameBranchNormal`** (compiled): the inputs of
`SGRDirect.heckeVertWitness_of_nvElkies` with `NVLocalInertia` replaced by the general commutative-algebra
Prop `TameBranchNormal`. -/
theorem heckeVertWitness_of_tame (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hTB : TameBranchNormal) (hEl : QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted) :
    HDec.HeckeRestNV.HeckeVertWitness :=
  heckeVertWitness_of_branchRegular hRR hT hA hS hW (branchRegular_of_tame hTB) hEl

end SGRDirect.NVLocal
