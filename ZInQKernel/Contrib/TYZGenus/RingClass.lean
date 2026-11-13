import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field
import ZInQKernel.RouteK.Rank5b.Sec3.RedeiStatement
import ZInQKernel.Contrib.TYZDecomp.CurveA
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
import ZInQKernel.RouteK.Redei.FourRank

/-!
# Ring class fields and genus data for Tian–Yuan–Zhang §3 (task ring-class)

Groundwork for splitting the genus-point package `TYZGenusPackage`
(`ZInQKernel/Contrib/TYZDecomp/Leaves.lean`, `docs/research/tyz-decomp.md` §4.2, item 3).
TYZ = Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*,
arXiv:1411.4728v1 (Asian J. Math. 21 (2017), refereed). The source `Period7.tex` is **not on this
host**; every line number `Lnnnn` below is quoted from the project notes that read it
(`nt-tyz.md`, `rv-nt-tyz.md`, `rv-tyz-inputs.md`, `rv-pn-encoding.md`, `tyz-t1.md`), not re-read here.

The objects, all built from Tau Ceti's ring class fields
(`TauCeti.ClassFieldTheory.ringClassField`, vendored under `ZInQKernel/Contrib/TauCeti/`):

* `conductorOrder K f`: the order `ℤ + f 𝓞_K` of a number field (conductor `f` when `K` is
  quadratic).
* `K_d = QNeg d = ℚ(√−d)` (the field of `gCl`); `O4 d = ℤ + 4𝓞_{K_d}`. For `d ≡ 5 (mod 8)`,
  `𝓞_{K_d} = ℤ[√−d]` and `O4 d = ℤ[4√−d]`, of discriminant `−64d`: the order of TYZ's CM points
  for `d ≡ 5` (the fixed point of TYZ's embedding L1203–1205 is a Heegner point of discriminant
  `−64n`, `tyz-t1.md` §3.1).
* `H4 d = H_{d,4}`: the ring class field of `O4 d` (TYZ Proposition 3.2(1), L1253–1258: "the ring
  class field of conductor 4").
* `hilbertField d = H_d`: the ring class field of the maximal order (Hilbert class field).
* `sigmaClass d ∈ Pic(O4 d)`: the class of `σ_{1+2ϖ}`, `ϖ = 1 + √−d` (a uniformizer at the
  ramified prime above 2; `Nϖ = d + 1`, cf. "`σ_ϖ|_{ℚ^ab} = r₂(Nϖ) = r₂(n+1)`",
  `rv-tyz-inputs.md` §1.5). As an ideal class: the contraction to `O4 d` of `(3 + 2√−d)𝓞_K`.
* `Hprime d = H'_d`: the fixed field of `σ_{1+2ϖ}` in `H_{d,4}` (TYZ Proposition 3.2(1),
  L1255–1256).
* `genusField O`: the fixed field of the squares `Pic(O)²` in the ring class field of `O`;
  its Galois group is `Pic(O)/Pic(O)²`, dual to the genus characters.
* In `ℚ̄ = CurveA.Qbar`: `H4bar d`, `Hprimebar d`, `Lni n = L_n(i) = ℚ(i, √p : p ∣ n)` (L1322) and
  `HHprime n = ℍ'_n = L_n(i) · Π_{d₀ ∣ n, d₀ ≡ 5 (8)} H'_{d₀}` (L1320; for odd `n` there is no
  `d₀ ≡ 6`).

Bridges to `PropN.GenusData` (whose only class-group input is `gNat e = gCl e = #(2 Cl(ℚ(√−e)))`):
see the theorems of the last sections.
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.TYZGenus.RingClass

open ZInQ.RouteK.Rank5b

/-! ### The order `ℤ + f 𝓞_K` -/

section ConductorOrder

variable (K : Type) [Field K] [NumberField K]

/-- `ℤ + f 𝓞_K` as a `ℤ`-subalgebra of `K`. -/
def conductorOrderSubalgebra (f : ℕ) : Subalgebra ℤ K where
  carrier := {x | ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * (y : K)}
  mul_mem' := by
    rintro _ _ ⟨a, y, rfl⟩ ⟨b, z, rfl⟩
    refine ⟨a * b, a * z + b * y + f * y * z, ?_⟩
    simp only [map_add, map_mul, map_intCast, map_natCast, Int.cast_mul]
    ring
  add_mem' := by
    rintro _ _ ⟨a, y, rfl⟩ ⟨b, z, rfl⟩
    exact ⟨a + b, y + z, by simp only [map_add, Int.cast_add]; ring⟩
  algebraMap_mem' := fun r => ⟨r, 0, by simp⟩

omit [NumberField K] in
theorem mem_conductorOrderSubalgebra {f : ℕ} {x : K} :
    x ∈ conductorOrderSubalgebra K f ↔ ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * (y : K) :=
  Iff.rfl

theorem conductorOrderSubalgebra_le_integralClosure (f : ℕ) :
    conductorOrderSubalgebra K f ≤ integralClosure ℤ K := by
  rintro _ ⟨a, y, rfl⟩
  exact (integralClosure ℤ K).add_mem ((integralClosure ℤ K).algebraMap_mem a)
    ((integralClosure ℤ K).mul_mem ((integralClosure ℤ K).natCast_mem f) y.2)

/-- **The order `ℤ + f 𝓞_K`** of a number field `K`, `f ≠ 0`. -/
def conductorOrder (f : ℕ) [NeZero f] : NumberFieldOrder K where
  toSubalgebra := conductorOrderSubalgebra K f
  finite := by
    have h := conductorOrderSubalgebra_le_integralClosure K f
    have : Module.Finite ℤ (integralClosure ℤ K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))
    exact Module.Finite.of_injective (Subalgebra.inclusion h).toLinearMap
      (Subalgebra.inclusion_injective h)
  spans := by
    apply top_unique
    rw [← (maximalNumberFieldOrder K).spans]
    apply Submodule.span_le.mpr
    intro y hy
    have hf : ((f : ℚ)) ≠ 0 := by exact_mod_cast NeZero.ne f
    have hmem : (f : K) * y ∈ conductorOrderSubalgebra K f :=
      ⟨0, ⟨y, hy⟩, by rw [Int.cast_zero, zero_add]; rfl⟩
    have : y = (f : ℚ)⁻¹ • ((f : K) * y) := by
      rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast, inv_mul_cancel₀ (by exact_mod_cast hf),
        one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

@[simp]
theorem conductorOrder_toSubalgebra (f : ℕ) [NeZero f] :
    (conductorOrder K f).toSubalgebra = conductorOrderSubalgebra K f :=
  rfl

end ConductorOrder

/-! ### Genus fields of orders -/

section Genus

variable {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- The subgroup of squares `Pic(O)²`. -/
def picSquares : Subgroup (Pic O) := (powMonoidHom 2 : Pic O →* Pic O).range

/-- **The genus field of an order** `O`: the fixed field in the ring class field of the image of
`Pic(O)²` under `ringClassArtinEquiv`, as a subfield of `Kˢ`. Its Galois group over `K` is
`Pic(O)/Pic(O)²` (the genus characters are the characters of this group). -/
def genusField : IntermediateField K (SeparableClosure K) :=
  IntermediateField.lift
    (IntermediateField.fixedField ((picSquares O).map (ringClassArtinEquiv O).toMonoidHom))

/-- The 2-torsion `Pic(O)[2]`. -/
def picTwoTorsion : Subgroup (Pic O) := (powMonoidHom 2 : Pic O →* Pic O).ker

end Genus

/-! ### The orders and fields of TYZ §3 -/

section TYZ

/-- `√−d` in `𝓞_{K_d}`, `K_d = ℚ(√−d)` (Mathlib's `QuadraticAlgebra ℚ (−d) 0`, generator `ω`). -/
def sqrtNeg (d : ℕ) [NeZero d] : 𝓞 (QNeg d) :=
  ⟨QuadraticAlgebra.omega, by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp [QuadraticAlgebra.omega_pow_two_eq_add]⟩

/-- `O_{d,4} = ℤ + 4𝓞_{K_d}`, the order of conductor 4 of `K_d = ℚ(√−d)`; for `d ≡ 5 (mod 8)` it is
`ℤ[4√−d]`, discriminant `−64d`. -/
abbrev O4 (d : ℕ) [NeZero d] : NumberFieldOrder (QNeg d) := conductorOrder (QNeg d) 4

/-- **`H_{d,4}`**, the ring class field of conductor 4 of `K_d` (TYZ Proposition 3.2(1),
L1253–1258). -/
abbrev H4 (d : ℕ) [NeZero d] : IntermediateField (QNeg d) (SeparableClosure (QNeg d)) :=
  ringClassField (O4 d)

/-- **`H_d`**, the Hilbert class field of `K_d`: the ring class field of the maximal order. -/
abbrev hilbertField (d : ℕ) [NeZero d] : IntermediateField (QNeg d) (SeparableClosure (QNeg d)) :=
  ringClassField (maximalNumberFieldOrder (QNeg d))

/-- The Artin isomorphism `Pic(O_{d,4}) ≃* Gal(H_{d,4}/K_d)` (Tau Ceti). -/
abbrev artin4 (d : ℕ) [NeZero d] : Pic (O4 d) ≃* Gal(H4 d/QNeg d) := ringClassArtinEquiv (O4 d)

/-- `α_d = 3 + 2√−d = 1 + 2ϖ`, `ϖ = 1 + √−d`. -/
def alpha (d : ℕ) [NeZero d] : 𝓞 (QNeg d) := 3 + 2 * sqrtNeg d

open Classical in
/-- **The class of `σ_{1+2ϖ}` in `Pic(O_{d,4})`**: the Picard class of the contraction of
`(1 + 2ϖ)𝓞_K = (3 + 2√−d)𝓞_K`, an ideal prime to the conductor (`alphaIdeal_mem`; the `else`
branch is never taken). The idele `1 + 2ϖ` at the place 2 and the ideal `(1+2ϖ)𝓞_K` have inverse
Artin symbols; `sigmaClass` has order 2, so the subgroup it generates is the same. -/
def sigmaClass (d : ℕ) [NeZero d] : Pic (O4 d) :=
  if h : Ideal.span {alpha d} ∈ integralIdealsPrimeTo (O4 d).conductorModulus then
    (O4 d).picClass ⟨_, h⟩
  else 1

/-- **`H'_d`**: the fixed field of `σ_{1+2ϖ}` in `H_{d,4}` (TYZ Proposition 3.2(1), L1255–1256:
`H'_d(√2) = H_{d,4}` and `H'_d` is fixed by `σ_{1+2ϖ}`), as a subfield of `K_dˢ`. -/
def Hprime (d : ℕ) [NeZero d] : IntermediateField (QNeg d) (SeparableClosure (QNeg d)) :=
  IntermediateField.lift
    (IntermediateField.fixedField (Subgroup.zpowers (artin4 d (sigmaClass d))))

/-! #### In `ℚ̄` -/

open ZInQ.Contrib.TYZDecomp.CurveA

instance (d : ℕ) [NeZero d] : Algebra.IsAlgebraic ℚ (SeparableClosure (QNeg d)) :=
  Algebra.IsAlgebraic.trans ℚ (QNeg d) (SeparableClosure (QNeg d))

/-- A fixed `ℚ`-embedding `K_dˢ → ℚ̄` (any; `H_{d,4}` and `H'_d` are Galois over `ℚ`, so their
images do not depend on it: `H4bar_eq_map`, `Hprimebar_eq_map`). -/
def embed (d : ℕ) [NeZero d] : SeparableClosure (QNeg d) →ₐ[ℚ] Qbar := IsAlgClosed.lift

/-- `H_{d,4} ⊂ ℚ̄` (`⊥` at `d = 0`). -/
def H4bar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((H4 d).restrictScalars ℚ).map (embed d)

/-- `H'_d ⊂ ℚ̄` (`⊥` at `d = 0`). -/
def Hprimebar (d : ℕ) : IntermediateField ℚ Qbar :=
  if h : d = 0 then ⊥ else
    haveI : NeZero d := ⟨h⟩; ((Hprime d).restrictScalars ℚ).map (embed d)

/-- `L_n(i) = ℚ(i, √d : d ∣ n) = ℚ(i, √p : p ∣ n)` (TYZ L1322, via `rv-pn-encoding.md`). -/
def Lni (n : ℕ) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ
    ({x : Qbar | x ^ 2 = -1} ∪ {x : Qbar | ∃ p ∈ n.primeFactors, x ^ 2 = (p : Qbar)})

/-- **`ℍ'_n = L_n(i) · Π_{d₀ ∣ n, d₀ ≡ 5 (mod 8)} H'_{d₀}`** (TYZ L1320 for odd `n`). -/
def HHprime (n : ℕ) : IntermediateField ℚ Qbar :=
  Lni n ⊔ ⨆ d₀ ∈ n.divisors.filter (fun d => d % 8 = 5), Hprimebar d₀

end TYZ

/-! ### Statements to be proved (targets of this task)

Each is a `Prop`; the theorems proving them follow in later sections, or are listed as unproved in
`docs/research/ring-class.md`. -/

/-- The degree of `H_{d,4}` over `K_d` is `#Pic(O_{d,4})` (Tau Ceti `finrank_ringClassField`). -/
def FinrankH4 : Prop :=
  ∀ d : ℕ, ∀ _ : NeZero d, Module.finrank (QNeg d) (H4 d) = Nat.card (Pic (O4 d))

/-- `gCl e = #Pic(𝓞_{K_e})²`: TYZ's `g(e)` in Tau Ceti's terms. -/
def GClEqPicSquares : Prop :=
  ∀ e : ℕ, ∀ _ : NeZero e,
    gCl e = Nat.card (picSquares (maximalNumberFieldOrder (QNeg e)))

/-- `gCl e = [H_e : G_e]`: `g(e)` is the degree of the Hilbert class field over the genus field. -/
def GClEqRelfinrank : Prop :=
  ∀ e : ℕ, ∀ _ : NeZero e,
    gCl e = (genusField (maximalNumberFieldOrder (QNeg e))).relfinrank (hilbertField e)

/-- The genus field has degree `#(Pic O / Pic(O)²) = #Pic(O)[2]` over `K`. -/
def FinrankGenusField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K),
    Module.finrank K (genusField O) = Nat.card (picTwoTorsion O) ∧
    Module.finrank K (genusField O) * Nat.card (picSquares O) = Nat.card (Pic O)

/-- `H_d ⊂ H_{d,4}` (ring class fields reverse inclusion of orders). -/
def HilbertLeH4 : Prop := ∀ d : ℕ, ∀ _ : NeZero d, hilbertField d ≤ H4 d

/-- `σ_{1+2ϖ}` is an element of order 2 of `Pic(O_{d,4})` in the kernel of
`Pic(O_{d,4}) → Cl(K_d)`, for squarefree `d ≡ 5 (mod 8)`; hence `[H_{d,4} : H'_d] = 2`. -/
def SigmaClassOrderTwo : Prop :=
  ∀ d : ℕ, ∀ _ : NeZero d, d % 8 = 5 → Squarefree d →
    orderOf (sigmaClass d) = 2 ∧ (Hprime d).relfinrank (H4 d) = 2

/-! ## Proofs -/


section Galois
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem comap_val_lift {E : IntermediateField K L} (F : IntermediateField K E) :
    (IntermediateField.lift F).comap E.val = F := by
  ext x
  simp [IntermediateField.mem_comap, IntermediateField.mem_lift]

theorem finrank_lift {E : IntermediateField K L} (F : IntermediateField K E) :
    Module.finrank K (IntermediateField.lift F) = Module.finrank K F :=
  (IntermediateField.liftAlgEquiv F).toLinearEquiv.finrank_eq.symm

theorem relfinrank_lift {E : IntermediateField K L} (F : IntermediateField K E) :
    (IntermediateField.lift F).relfinrank E = Module.finrank F E := by
  have h := IntermediateField.finrank_comap (IntermediateField.lift F) E.val
  rw [IntermediateField.fieldRange_val, comap_val_lift] at h
  exact h.symm

theorem relfinrank_lift_fixedField {E : IntermediateField K L} [FiniteDimensional K E]
    (H : Subgroup Gal(E/K)) :
    (IntermediateField.lift (IntermediateField.fixedField H)).relfinrank E = Nat.card H := by
  rw [relfinrank_lift, IntermediateField.finrank_fixedField_eq_card]

theorem finrank_lift_fixedField_mul {E : IntermediateField K L} [FiniteDimensional K E]
    (H : Subgroup Gal(E/K)) :
    Module.finrank K (IntermediateField.lift (IntermediateField.fixedField H)) * Nat.card H =
      Module.finrank K E := by
  rw [finrank_lift, ← IntermediateField.finrank_fixedField_eq_card H, Module.finrank_mul_finrank]

end Galois

section Genus
variable {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)

theorem card_picSquares_map :
    Nat.card ((picSquares O).map (ringClassArtinEquiv O).toMonoidHom) = Nat.card (picSquares O) :=
  Nat.card_congr ((picSquares O).equivMapOfInjective _ (ringClassArtinEquiv O).injective).toEquiv.symm

theorem genusField_le : genusField O ≤ ringClassField O := IntermediateField.lift_le _

theorem relfinrank_genusField :
    (genusField O).relfinrank (ringClassField O) = Nat.card (picSquares O) := by
  rw [genusField, relfinrank_lift_fixedField, card_picSquares_map]

theorem finrank_genusField_mul :
    Module.finrank K (genusField O) * Nat.card (picSquares O) = Nat.card (Pic O) := by
  rw [← card_picSquares_map, genusField, finrank_lift_fixedField_mul, finrank_ringClassField]

theorem card_picTwoTorsion_mul : Nat.card (picTwoTorsion O) * Nat.card (picSquares O) = Nat.card (Pic O) :=
  Subgroup.card_ker_mul_card_range _

theorem finrank_genusField : Module.finrank K (genusField O) = Nat.card (picTwoTorsion O) := by
  have h1 := finrank_genusField_mul O
  have h2 := card_picTwoTorsion_mul O
  have hpos : 0 < Nat.card (picSquares O) := Nat.card_pos
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem finrankGenusField : FinrankGenusField := fun _ _ _ O => ⟨finrank_genusField O, finrank_genusField_mul O⟩

theorem finrankH4 : FinrankH4 := fun _ _ => finrank_ringClassField _

end Genus

theorem gCl_eq_card_picSquares (e : ℕ) [NeZero e] :
    ZInQ.RouteK.Rank5b.gCl e = Nat.card (picSquares (maximalNumberFieldOrder (ZInQ.RouteK.Rank5b.QNeg e))) := rfl


/-! ### Hilbert class field and ring class fields -/

section Hilbert


variable {K : Type} [Field K] [NumberField K]

theorem ker_le_ker_maximal (O : NumberFieldOrder K) :
    (ringClassIdeleQuotient O).ker ≤ (ringClassIdeleQuotient (maximalNumberFieldOrder K)).ker := by
  intro c hc
  rw [ker_ringClassIdeleQuotient_maximalNumberFieldOrder, ← ker_rayClassQuotient, MonoidHom.mem_ker]
  obtain ⟨J, hJ, β, -, hJβ⟩ := (mem_ker_ringClassIdeleQuotient_iff O).1 hc
  rw [← classMap_rayClassQuotient (Modulus.one_dvd O.conductorModulus), ← hJ, classMap_idealClass,
    idealClass_eq_one_iff_exists_generator]
  refine ⟨β, by simp, fun w hw => by simp at hw, ?_⟩
  simpa using hJβ

theorem ringClassField_maximal_le (O : NumberFieldOrder K) :
    ringClassField (maximalNumberFieldOrder K) ≤ ringClassField O := by
  rw [ringClassField_def, ringClassField_def, ← globalClassField_orderReversing]
  change ((ringClassNormSubgroup O).1.toSubgroup ≤ (ringClassNormSubgroup _).1.toSubgroup)
  rw [ringClassNormSubgroup_toSubgroup, ringClassNormSubgroup_toSubgroup]
  exact ker_le_ker_maximal O

theorem ringClassField_maximal_eq_hilbertClassField :
    ringClassField (maximalNumberFieldOrder K) = hilbertClassField K := by
  rw [ringClassField_def, hilbertClassField, rayClassField_def]
  congr 3
  apply Subtype.ext
  apply OpenSubgroup.toSubgroup_injective
  change (ringClassNormSubgroup _).1.toSubgroup = (rayNormSubgroup _).1.toSubgroup
  rw [ringClassNormSubgroup_toSubgroup, rayNormSubgroup_toSubgroup,
    ker_ringClassIdeleQuotient_maximalNumberFieldOrder]


end Hilbert


open ZInQ.RouteK.Redei

section Arith
variable {d : ℕ} [NeZero d]

theorem sqrtNeg_eq : sqrtNeg d = omegaO d := rfl

theorem sqrtNeg_mul_self : sqrtNeg d * sqrtNeg d = -(d : 𝓞 (QNeg d)) := omegaO_sq d

theorem coe_sqrtNeg : ((sqrtNeg d : 𝓞 (QNeg d)) : QNeg d) = QuadraticAlgebra.omega := rfl

/-- `2 re z ∈ ℤ` for `z ∈ 𝓞_K`. -/
theorem exists_two_re (z : 𝓞 (QNeg d)) : ∃ m : ℤ, 2 * (z : QNeg d).re = m := by
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := d)
  refine exists_int_of_coe_eq_algebraMap (z + σ • z) _ ?_
  have h1 : ((z + σ • z : 𝓞 (QNeg d)) : QNeg d) = (z : QNeg d) + star (z : QNeg d) := by
    rw [← conj_apply σ hσ]
    simp [RingOfIntegers.coe_eq_algebraMap]
  rw [h1, ← QuadraticAlgebra.algebraMap_trace_eq_add_star, QuadraticAlgebra.trace_def]
  simp

/-- `re² + d im² ∈ ℤ` for `z ∈ 𝓞_K`; it is the norm. -/
theorem normZ_eq_re_im (z : 𝓞 (QNeg d)) :
    ((Algebra.norm ℤ z : ℤ) : ℚ) = (z : QNeg d).re ^ 2 + d * (z : QNeg d).im ^ 2 := by
  rw [← algNorm_coe, algNorm_eq d, QuadraticAlgebra.norm_def]
  ring

theorem normZ_unit (u : (𝓞 (QNeg d))ˣ) : Algebra.norm ℤ (u : 𝓞 (QNeg d)) = 1 := by
  have h := IsUnit.map (Algebra.norm ℤ) u.isUnit
  rcases Int.isUnit_iff.1 h with h | h
  · exact h
  · have := normZ_nonneg (n := d) (u : 𝓞 (QNeg d)); omega

/-- For `d ≡ 5 (mod 8)` the units of `𝓞_{K_d}` are `±1`. -/
theorem unit_eq (hd : d % 8 = 5) (u : (𝓞 (QNeg d))ˣ) :
    (u : 𝓞 (QNeg d)) = 1 ∨ (u : 𝓞 (QNeg d)) = -1 := by
  obtain ⟨m, hm⟩ := exists_two_re (u : 𝓞 (QNeg d))
  obtain ⟨k, hk⟩ := exists_two_re ((u : 𝓞 (QNeg d)) * sqrtNeg d)
  have hN := normZ_eq_re_im (u : 𝓞 (QNeg d))
  rw [normZ_unit] at hN
  set x := ((u : 𝓞 (QNeg d)) : QNeg d).re
  set y := ((u : 𝓞 (QNeg d)) : QNeg d).im
  have hre : (((u : 𝓞 (QNeg d)) * sqrtNeg d : 𝓞 (QNeg d)) : QNeg d).re = -(d : ℚ) * y := by
    simp [RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg, y]
  rw [hre] at hk
  have hd0 : (0 : ℤ) < d := by have := NeZero.ne d; omega
  have hZ : (d : ℤ) * m ^ 2 + k ^ 2 = 4 * d := by
    have : (d : ℚ) * (m : ℚ) ^ 2 + (k : ℚ) ^ 2 = 4 * d := by
      rw [← hm, ← hk]; linear_combination (4 * (d : ℚ)) * hN.symm
    exact_mod_cast this
  have hm2 : m ^ 2 ≤ 4 := by
    by_contra h; push Not at h; nlinarith [sq_nonneg k]
  have hmlo : -2 ≤ m := by nlinarith [sq_nonneg (m + 2)]
  have hmhi : m ≤ 2 := by nlinarith [sq_nonneg (m - 2)]
  have hd8 : ((d : ℕ) : ZMod 8) = 5 := by
    rw [← ZMod.natCast_mod, hd]; rfl
  have hd32 : ((d : ℕ) : ZMod 32) = 5 ∨ ((d : ℕ) : ZMod 32) = 13 ∨ ((d : ℕ) : ZMod 32) = 21 ∨
      ((d : ℕ) : ZMod 32) = 29 := by
    rw [← ZMod.natCast_mod]
    have h32 : d % 32 = 5 ∨ d % 32 = 13 ∨ d % 32 = 21 ∨ d % 32 = 29 := by omega
    rcases h32 with h | h | h | h <;> rw [h] <;> simp
  have k3 : ∀ a : ZMod 8, a ^ 2 ≠ 3 * 5 := by decide
  have k4 : ∀ a b : ZMod 32, (b = 5 ∨ b = 13 ∨ b = 21 ∨ b = 29) → a ^ 2 ≠ 4 * b := by decide
  have hu : ∀ e : ℚ, (e = 1 ∨ e = -1) → x = e → y = 0 →
      (u : 𝓞 (QNeg d)) = 1 ∨ (u : 𝓞 (QNeg d)) = -1 := by
    rintro e (rfl | rfl) hx hy
    · left; apply RingOfIntegers.ext; ext
      · change x = _; rw [hx]; simp only [map_neg, map_one, QuadraticAlgebra.re_neg]; rfl
      · change y = _; rw [hy]; simp only [map_neg, map_one, QuadraticAlgebra.im_neg, neg_zero]; rfl
    · right; apply RingOfIntegers.ext; ext
      · change x = _; rw [hx]; simp only [map_neg, map_one, QuadraticAlgebra.re_neg]; rfl
      · change y = _; rw [hy]; simp only [map_neg, map_one, QuadraticAlgebra.im_neg, neg_zero]; rfl
  have hk0 : ∀ mm : ℤ, (mm = 2 ∨ mm = -2) → m = mm → k = 0 := by
    rintro mm (rfl | rfl) rfl <;> nlinarith [sq_nonneg k]
  rcases (show m = -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 ∨ m = 2 by omega) with h | h | h | h | h
  · have hkz := hk0 _ (Or.inr rfl) h
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne d
    refine hu (-1) (Or.inr rfl) ?_ ?_
    · rw [h] at hm; push_cast at hm; linarith
    · rw [hkz] at hk; push_cast at hk
      have : (d : ℚ) * y = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hdq
  · exfalso
    have : k ^ 2 = 3 * (d : ℤ) := by subst h; linarith
    have h8 := congrArg (fun t : ℤ => (t : ZMod 8)) this
    push_cast at h8; rw [hd8] at h8; exact k3 _ h8
  · exfalso
    have : k ^ 2 = 4 * (d : ℤ) := by subst h; linarith
    have h32 := congrArg (fun t : ℤ => (t : ZMod 32)) this
    push_cast at h32; exact k4 _ _ hd32 h32
  · exfalso
    have : k ^ 2 = 3 * (d : ℤ) := by subst h; linarith
    have h8 := congrArg (fun t : ℤ => (t : ZMod 8)) this
    push_cast at h8; rw [hd8] at h8; exact k3 _ h8
  · have hkz := hk0 _ (Or.inl rfl) h
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne d
    refine hu 1 (Or.inl rfl) ?_ ?_
    · rw [h] at hm; push_cast at hm; linarith
    · rw [hkz] at hk; push_cast at hk
      have : (d : ℚ) * y = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hdq
theorem alpha_mul_conj : alpha d * (3 - 2 * sqrtNeg d) + 4 * (-(2 + (d : 𝓞 (QNeg d)))) = 1 := by
  unfold alpha; linear_combination (-4 : 𝓞 (QNeg d)) * sqrtNeg_mul_self (d := d)

theorem alpha_sq : alpha d ^ 2 = (((9 - 4 * d : ℤ)) : 𝓞 (QNeg d)) + 4 * (3 * sqrtNeg d) := by
  unfold alpha; push_cast; linear_combination (4 : 𝓞 (QNeg d)) * sqrtNeg_mul_self (d := d)

end Arith

theorem natCast_mul_mem_conductor (K : Type) [Field K] [NumberField K] (f : ℕ) [NeZero f]
    (y : 𝓞 K) : (f : 𝓞 K) * y ∈ (conductorOrder K f).conductor := by
  rw [NumberFieldOrder.mem_conductor_iff]
  intro z
  exact ⟨0, y * z, by simp only [map_mul, map_natCast, Int.cast_zero, zero_add]; ring⟩

section Sigma
variable {d : ℕ} [NeZero d]

theorem alphaIdeal_mem :
    Ideal.span {alpha d} ∈ integralIdealsPrimeTo (O4 d).conductorModulus := by
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
    conductorModulus_finitePart]
  have key := alpha_mul_conj (d := d)
  refine ⟨?_, ?_⟩
  · intro h
    rw [Ideal.span_singleton_eq_bot] at h
    rw [h, zero_mul, zero_add] at key
    have h1 : ((4 * (-(2 + (d : ℤ))) : ℤ) : 𝓞 (QNeg d)) = ((1 : ℤ) : 𝓞 (QNeg d)) := by
      push_cast; exact key
    have := intCast_injective (n := d) h1
    omega
  · rw [Ideal.eq_top_iff_one, ← key]
    refine Ideal.add_mem _ (Ideal.mem_sup_left
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))) (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg d) 4 (-(2 + (d : 𝓞 (QNeg d))))

theorem sigmaClass_eq : sigmaClass d = (O4 d).picClass ⟨_, alphaIdeal_mem⟩ := by
  unfold sigmaClass; rw [dite_eq_left alphaIdeal_mem]

theorem sigmaClass_sq : sigmaClass d ^ 2 = 1 := by
  rw [sigmaClass_eq, ← map_pow, picClass_eq_one_iff]
  refine ⟨alpha d ^ 2, ?_, ?_⟩
  · rw [mem_toRingOfIntegers, alpha_sq]
    exact ⟨9 - 4 * d, 3 * sqrtNeg d, by simp only [map_add, map_mul, map_intCast, map_ofNat]; push_cast; ring⟩
  · rw [SubmonoidClass.coe_pow, Ideal.span_singleton_pow]

/-- `±(3 + 2√−d) ∉ ℤ + 4𝓞_K` for `d ≡ 5 (mod 8)`. -/
theorem not_mem_O4 (hd : d % 8 = 5) (s : ℤ) (hs : s = 1 ∨ s = -1) (a : ℤ) (z : 𝓞 (QNeg d)) :
    (s : QNeg d) * ((alpha d : 𝓞 (QNeg d)) : QNeg d) ≠ a + 4 * (z : QNeg d) := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  simp [alpha, RingOfIntegers.coe_eq_algebraMap, coe_sqrtNeg, map_ofNat, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat] at him
  obtain ⟨j, hj⟩ := exists_two_re z
  have hN := normZ_eq_re_im z
  have hz2 : (z : QNeg d).im ^ 2 = 1 / 4 := by
    rcases hs with rfl | rfl <;> push_cast at him <;> nlinarith
  have h4 : (j : ℚ) ^ 2 + d = 4 * (Algebra.norm ℤ z : ℤ) := by
    rw [← hj, hN, hz2]; ring
  have h4' : j ^ 2 + (d : ℤ) = 4 * Algebra.norm ℤ z := by exact_mod_cast h4
  have hm := congrArg (fun t : ℤ => (t : ZMod 4)) h4'
  push_cast at hm
  have hd4 : ((d : ℕ) : ZMod 4) = 1 := by
    rw [← ZMod.natCast_mod, show d % 4 = 1 by omega]; rfl
  rw [hd4, show (4 : ZMod 4) = 0 from rfl, zero_mul] at hm
  generalize (j : ZMod 4) = b at hm
  revert b; decide

theorem sigmaClass_ne_one (hd : d % 8 = 5) : sigmaClass d ≠ 1 := by
  rw [sigmaClass_eq]
  intro h
  rw [picClass_eq_one_iff] at h
  obtain ⟨β, hβ, hJ⟩ := h
  rw [Ideal.span_singleton_eq_span_singleton] at hJ
  obtain ⟨u, hu⟩ := hJ
  rw [mem_toRingOfIntegers] at hβ
  obtain ⟨a, z, hz⟩ := hβ
  rw [← hu] at hz
  rcases unit_eq hd u with h1 | h1 <;> rw [h1] at hz
  · exact not_mem_O4 hd 1 (Or.inl rfl) a z (by simpa using hz)
  · exact not_mem_O4 hd (-1) (Or.inr rfl) a z (by simpa using hz)

theorem orderOf_sigmaClass (hd : d % 8 = 5) : orderOf (sigmaClass d) = 2 :=
  orderOf_eq_prime sigmaClass_sq (sigmaClass_ne_one hd)

end Sigma

end ZInQ.Contrib.TYZGenus.RingClass
