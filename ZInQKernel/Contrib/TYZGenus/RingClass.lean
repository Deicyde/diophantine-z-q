import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field
import ZInQKernel.RouteK.Rank5b.Sec3.RedeiStatement
import ZInQKernel.Contrib.TYZDecomp.CurveA

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

end ZInQ.Contrib.TYZGenus.RingClass
