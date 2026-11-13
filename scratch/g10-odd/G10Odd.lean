import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.HDecomp.I3Linalg.C2

/-! # g10-odd: the glue Prop `G10Glue` (oddness of `r_ℓ`, glue step G10)

Check with `lake env lean scratch/g10-odd/G10Odd.lean` (after
`lake build ZInQKernel.HDecomp.LeafPush2.T ZInQKernel.HDecomp.I3Linalg.C2`).

* §1 copies `G10Glue` **verbatim** from `scratch/g0-mod-galois/part_galois.lean`, with what it
  depends on: the two opaque placeholders `HSyn.T11_RiemannGAGA`, `HSyn.T12_ArtinComparison`
  (verbatim from `scratch/g0-split/Split.lean`), and `resQ`, `Vb`, `tate`, `Intertwines`,
  `G10Out` (verbatim from part_galois.lean). `PkgI3.AbVar`, `PkgI3.FaltingsTate`,
  `PkgI3.EndDivision` (ZInQKernel/HDecomp/Objects.lean), `PkgI4.GaloisRep`, `IsOdd`,
  `IsComplexConj` (ZInQKernel/HDecomp/Conductor/LadicCond.lean) and `GlueI3.repBaseChange`
  (ZInQKernel/HDecomp/I3Linalg/C2.lean) are imported; their bodies are the same as the copies in
  Split.lean.
* §2 proves the algebraic part: an involution of `ℚ̄_ℓ²` that is not `±1` has determinant `−1`;
  complex conjugations are involutions; so `r` is odd as soon as no `r(c)` is `±1`.
* §3 names the remaining glue, `ConjTwistNontrivial` (complex conjugation does not normalize the
  Tate representation of `G_K` trivially), and proves `G10Glue` from it (`g10Glue_of_conjTwist`).
  The opaque `T11`/`T12` hypotheses of `G10Glue` are not used (they carry no content).
* §4 states the corrected form `G10GlueConcrete` (the opaque placeholders replaced by the concrete
  leaves T11a, T11b, T35 of `ZInQKernel/HDecomp/LeafPush2/T.lean`) and proves it from
  `ConjTwistFromLeaves` (the same glue with those leaves as hypotheses).
-/

noncomputable section

/-! ## §1. Verbatim copies -/

namespace HSyn

/-- **T11. Riemann's theorem, GAGA, rigidity.** `End⁰(A_ℂ)` is the algebra of endomorphisms of
the rational Hodge structure `H₁(A(ℂ), ℚ)`, and `Hom(A, B) = Hom(A_ℂ, B_ℂ)` over `ℚ̄` (Mumford
§§1-3; Serre 1956; Conrad 2006, §3; UNVERIFIED). Missing: analytification (large). -/
opaque T11_RiemannGAGA : Prop

/-- **T12. Artin comparison.** `V_ℓ(A) ≅ H₁(A(ℂ), ℚ) ⊗ ℚ_ℓ`, compatibly with complex conjugation
(SGA 4 XI 4.4, UNVERIFIED; elementary for abelian varieties via `ℂ²/Λ`). Missing: as T11. -/
opaque T12_ArtinComparison : Prop

end HSyn

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-- **Output of G10:** `r` is odd (`det r(c) = −1` for every complex conjugation `c`). -/
def G10Out {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) : Prop := r.IsOdd

/-- **G10, oddness (GLUE, unproved; h-trust C5, model reviews).** From T11 (Riemann, GAGA) and T12
(Artin comparison) with R9b (Faltings): if `K` is Galois over `ℚ`, `A/K` an abelian surface with
`End_K(A)` of rank 4, a division ring (`PkgI3.EndDivision`) and noncommutative (so `End⁰_K(A)`
is a quaternion algebra over `ℚ`), and `r : G_ℚ → GL₂(ℚ̄_ℓ)` with
`ℚ̄_ℓ ⊗ V_ℓ(A) ≅ r|G_K ⊕ r|G_K`, then `r` is odd. Argument (model review, SPECULATIVE until
written; each step STANDARD): `r(c)² = 1`; if `r(c) = ±1` then `ρ(c)` is scalar and, `G_K` being
normal, `c` induces a `G_K`-equivariant map `V_ℓ(cA) → V_ℓ(A)`, which by Faltings (R9b) lies in
`Hom(cA, A) ⊗ ℚ_ℓ`; by Artin comparison (T12) it is the antiholomorphic `F_∞`, a rational map,
contradicting holomorphy of homomorphisms (T11). So `r(c)` is not scalar, and `det r(c) = −1`.
(This is N5 L742-751's Betti argument; the rank/division/noncommutativity hypotheses are not
needed by it but are kept, being true for Glazer's `A`.) -/
def G10Glue : Prop :=
  HSyn.T11_RiemannGAGA → HSyn.T12_ArtinComparison → PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Module.finrank ℤ (PkgI3.AbVar.End A) = 4 → PkgI3.EndDivision A →
    (∃ x y : PkgI3.AbVar.End A, x * y ≠ y * x) →
    Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G10Out r

/-! ## §2. The algebraic part (proved) -/

open scoped TensorProduct

/-- A `2 × 2` involution over a field that is not `±1` has determinant `−1` (trace `0`). -/
theorem det_eq_neg_one_of_sq_eq_one {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (h2 : M * M = 1) (h1 : M ≠ 1) (hm1 : M ≠ -1) : M.det = -1 := by
  have e00 := congrFun (congrFun h2 0) 0
  have e01 := congrFun (congrFun h2 0) 1
  have e10 := congrFun (congrFun h2 1) 0
  have e11 := congrFun (congrFun h2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two]
  by_cases ht : M 0 0 + M 1 1 = 0
  · have : M 1 1 = -M 0 0 := by linear_combination ht
    rw [this]; linear_combination -e00
  · have hb : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right ht
    have hc : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right ht
    rw [hb, hc] at e00 e11
    have ha : M 0 0 = 1 ∨ M 0 0 = -1 := by
      have : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination e00
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    have hd : M 1 1 = 1 ∨ M 1 1 = -1 := by
      have : (M 1 1 - 1) * (M 1 1 + 1) = 0 := by linear_combination e11
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    exfalso
    rcases ha with ha | ha <;> rcases hd with hd | hd
    · exact h1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd])
    · exact ht (by rw [ha, hd]; ring)
    · exact ht (by rw [ha, hd]; ring)
    · exact hm1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd])

/-- A complex conjugation is an involution. -/
theorem isComplexConj_mul_self {c : PkgI4.GQ} (hc : PkgI4.IsComplexConj c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  apply AlgEquiv.ext; intro x
  apply j.toRingHom.injective
  change j (c (c x)) = j x
  rw [hj, hj, Complex.conj_conj]

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem GaloisRep.mat_mul (r : GaloisRep ℓ 2) (g h : PkgI4.GQ) :
    r.mat (g * h) = r.mat g * r.mat h := by
  simp [PkgI4.GaloisRep.mat, map_mul, Units.val_mul]

theorem GaloisRep.mat_one (r : GaloisRep ℓ 2) : r.mat 1 = 1 := by
  simp [PkgI4.GaloisRep.mat]

/-- **Oddness from non-scalarity (proved).** If no complex conjugation acts by `±1`, then `r` is
odd. -/
theorem isOdd_of_not_pm_one (r : GaloisRep ℓ 2)
    (h : ∀ c, PkgI4.IsComplexConj c → r.mat c ≠ 1 ∧ r.mat c ≠ -1) : r.IsOdd := by
  intro c hc
  have h2 : r.mat c * r.mat c = 1 := by
    rw [← GaloisRep.mat_mul, isComplexConj_mul_self hc, GaloisRep.mat_one]
  exact det_eq_neg_one_of_sq_eq_one _ h2 (h c hc).1 (h c hc).2

/-- `v ↦ 1 ⊗ v` is injective for a field extension (flatness of vector spaces). -/
theorem one_tmul_injective (k E V : Type*) [Field k] [Field E] [Algebra k E] [AddCommGroup V]
    [Module k V] : Function.Injective (fun v : V => (1 : E) ⊗ₜ[k] v) := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := V)
    (Algebra.linearMap k E) (algebraMap k E).injective
  intro x y hxy
  apply (TensorProduct.lid k V).symm.injective
  apply hinj
  simpa using hxy

/-- Base change along a field extension is injective on linear maps. -/
theorem baseChange_injective' (k E V : Type*) [Field k] [Field E] [Algebra k E] [AddCommGroup V]
    [Module k V] {f g : V →ₗ[k] V} (h : f.baseChange E = g.baseChange E) : f = g := by
  ext v
  apply one_tmul_injective k E V
  have := LinearMap.congr_fun h ((1 : E) ⊗ₜ[k] v)
  simpa using this

/-! ## §3. The remaining glue, and `G10Glue` from it -/

/-- **G10 core: complex conjugation twists the Tate representation of `G_K` nontrivially (GLUE,
unproved; STANDARD).** For a number field `K` Galois over `ℚ`, an abelian surface `A/K`, a prime
`ℓ` and a complex conjugation `c ∈ G_ℚ`, it is not the case that `ρ_ℓ(τ) = ρ_ℓ(σ)` on `V_ℓ(A)`
whenever `τ, σ ∈ G_K` satisfy `τ = c σ c⁻¹` in `G_ℚ` (`resQ`).

Proof (STANDARD; N5 L742-751, h-trust C5): suppose it is. Let `ι : ℚ̄ → ℂ` realize `c`, `c̄ = c|_K`
(`K` normal), `A^c = A ⊗_{K,c̄} K`. The `c`-semilinear bijection `A(K̄) → A^c(K̄)` gives
`c_* : V_ℓ(A) → V_ℓ(A^c)` with `c_* ρ_A(σ) = ρ_{A^c}(cσc⁻¹) c_*`; by the assumption `c_*` is
`G_K`-equivariant, so by Faltings (`PkgI3.FaltingsTate`, R9b) `c_* ∈ Hom(A, A^c) ⊗ ℚ_ℓ`. By the
Artin comparison at `ι` (T12, through the uniformization T35 and T5), `c_* = F_* ⊗ 1` for the
antiholomorphic `F : A(ℂ) → A^c(ℂ)`, `F_* : H₁(A(ℂ),ℚ) → H₁(A^c(ℂ),ℚ)` `ℚ`-rational; since
`(W ⊗ ℚ_ℓ) ∩ Hom_ℚ(H, H') = W` for the `ℚ`-subspace `W = Hom(A, A^c) ⊗ ℚ`, `F_* ∈ W`, so `F_*` is
`ℂ`-linear by T11 (`F_* J = J' F_*`) and `ℂ`-antilinear (`F_* J = −J' F_*`), hence `F_* = 0`,
contradicting `F_*` bijective and `H ≠ 0` (`dim A = 2`). The case `c ∈ G_K` (`c̄ = id`,
`A^c = A`) is the same with `c_* = ρ_A(c)`. -/
def ConjTwistNontrivial : Prop :=
  PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime], A.dim = 2 → ∀ c : PkgI4.GQ, PkgI4.IsComplexConj c →
    ¬ ∀ σ τ : Field.absoluteGaloisGroup K, resQ K τ = c * resQ K σ * c⁻¹ →
      A.galRep ℓ τ = A.galRep ℓ σ

/-- If `r(c)` is central (here `±1`), the Tate action is unchanged by the `c`-twist. -/
theorem galRep_eq_of_central {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hI : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) (c : PkgI4.GQ)
    (hcen : ∀ X, r.mat c * X = X * r.mat c) (σ τ : Field.absoluteGaloisGroup K)
    (hτ : resQ K τ = c * resQ K σ * c⁻¹) : A.galRep ℓ τ = A.galRep ℓ σ := by
  have hm : r.mat (resQ K τ) = r.mat (resQ K σ) := by
    rw [hτ, GaloisRep.mat_mul, GaloisRep.mat_mul, hcen, _root_.mul_assoc, ← GaloisRep.mat_mul,
      _root_.mul_inv_cancel, GaloisRep.mat_one, _root_.mul_one]
  have ht : tate A ℓ τ = tate A ℓ σ := by
    apply LinearMap.ext; intro v
    apply e.injective
    rw [hI τ v, hI σ v]
    simp only [hm]
  exact baseChange_injective' ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) ht

/-- **The conclusion of `G10Glue` from `ConjTwistNontrivial` (proved),** without the opaque
hypotheses and without the rank, division and noncommutativity hypotheses. -/
theorem g10Out_of_conjTwist (h : ConjTwistNontrivial) (hF : PkgI3.FaltingsTate) (K : Type)
    [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hdim : A.dim = 2) (hI : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) :
    G10Out r := by
  apply isOdd_of_not_pm_one
  intro c hc
  have key := h hF K A ℓ hdim c hc
  constructor
  · intro h1
    exact key (galRep_eq_of_central A r e hI c (fun X => by rw [h1, _root_.one_mul, _root_.mul_one]))
  · intro h1
    exact key (galRep_eq_of_central A r e hI c (fun X => by rw [h1]; simp))

/-- **`G10Glue` from `ConjTwistNontrivial` (proved).** The opaque hypotheses `T11_RiemannGAGA`,
`T12_ArtinComparison` and the rank, division and noncommutativity hypotheses are not used. -/
theorem g10Glue_of_conjTwist (h : ConjTwistNontrivial) : G10Glue := by
  intro _ _ hF K _ _ _ A ℓ _ r e hdim _ _ _ hI
  exact g10Out_of_conjTwist h hF K A ℓ r e hdim hI

/-! ## §4. Split by whether `c ∈ G_K`, through a number-field form of T12 -/

/-- **T12 over a number field (GLUE target, unproved; same proof as `T12_ComplexConjEigen`).**
For an abelian variety `A` of dimension `g` over a number field `K` and `σ ∈ G_K` whose image in
`G_ℚ` is a complex conjugation (so `σ` fixes `K` pointwise through a real embedding), `σ` acts on
`V_ℓ(A)` with `+1`- and `−1`-eigenspaces of dimension `g` each. Source: Artin's comparison at the
real place (SGA 4 XI 4.4; for abelian varieties through the uniformization T35 and T5, as for
`ZInQ.LeafPush2.T12_ComplexConjEigen`) plus the eigenspace computation for an antiholomorphic
involution of `ℂ^g/Λ`. `T12_ComplexConjEigen` is the case `K = ℚ` up to the inner automorphism
by which `resQ ℚ` differs from the identity. -/
def T12K_ComplexConjEigen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K), PkgI4.IsComplexConj (resQ K σ) →
      Module.finrank ℚ_[ℓ] (LinearMap.ker (A.galRep ℓ σ - 1)) = g ∧
        Module.finrank ℚ_[ℓ] (LinearMap.ker (A.galRep ℓ σ + 1)) = g

/-- **G10 core outside `G_K` (GLUE, unproved; STANDARD).** `ConjTwistNontrivial` restricted to
complex conjugations not in (the image of) `G_K`; same proof (Faltings, Artin comparison at `ι`
for the conjugate variety `A^c`, holomorphy). -/
def ConjTwistOutside : Prop :=
  PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime], A.dim = 2 → ∀ c : PkgI4.GQ, PkgI4.IsComplexConj c → c ∉ (resQ K).range →
    ¬ ∀ σ τ : Field.absoluteGaloisGroup K, resQ K τ = c * resQ K σ * c⁻¹ →
      A.galRep ℓ τ = A.galRep ℓ σ

theorem conjTwistOutside_of_conjTwistNontrivial (h : ConjTwistNontrivial) : ConjTwistOutside :=
  fun hF K _ _ _ A ℓ _ hd c hc _ => h hF K A ℓ hd c hc

/-- `±1` on `V_ℓ(A)` is incompatible with eigenspaces of dimension `2` for both signs. -/
theorem ker_two_eq_bot {V : Type*} [AddCommGroup V] [Module ℚ_[ℓ] V] (f : V →ₗ[ℚ_[ℓ]] V)
    (hf : f = 1 ∨ f = -1) : LinearMap.ker (f + 1) = ⊥ ∨ LinearMap.ker (f - 1) = ⊥ := by
  have two : (2 : ℚ_[ℓ]) ≠ 0 := two_ne_zero
  rcases hf with rfl | rfl
  · left
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have : (2 : ℚ_[ℓ]) • v = 0 := by
      rw [two_smul]; simpa using hv
    exact (smul_eq_zero.mp this).resolve_left two
  · right
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have : (2 : ℚ_[ℓ]) • v = 0 := by
      rw [two_smul]
      have : -v - v = 0 := by simpa using hv
      have h2 : v + v = -(-v - v) := by abel
      rw [h2, this, neg_zero]
    exact (smul_eq_zero.mp this).resolve_left two

/-- **Inside `G_K` (proved from `T12K_ComplexConjEigen`).** If `c = resQ K σ` is a complex
conjugation and `ℚ̄_ℓ ⊗ V_ℓ(A) ≅ r|G_K ⊕ r|G_K` with `dim A = 2`, then `r(c) ≠ ±1`. -/
theorem not_pm_one_of_mem_range (hT : T12K_ComplexConjEigen) {K : Type} [Field K]
    [NumberField K] (A : PkgI3.AbVar K) (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hdim : A.dim = 2) (hI : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e)
    (σ : Field.absoluteGaloisGroup K) (hc : PkgI4.IsComplexConj (resQ K σ)) :
    r.mat (resQ K σ) ≠ 1 ∧ r.mat (resQ K σ) ≠ -1 := by
  have hd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  obtain ⟨h1, h2⟩ := hT K A 2 hd ℓ σ hc
  have reduce : ∀ (s : Module.End ℚ_[ℓ] (A.V ℓ)) (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)),
      r.mat (resQ K σ) = M → (∀ v, e (s.baseChange (PadicAlgCl ℓ) v) =
        (M.mulVec (e v).1, M.mulVec (e v).2)) → A.galRep ℓ σ = s := by
    intro s M hM hs
    apply baseChange_injective' ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)
    apply LinearMap.ext; intro v
    apply e.injective
    have h := hI σ v
    simp only [hM] at h
    exact h.trans (hs v).symm
  have fin0 : ∀ W : Submodule ℚ_[ℓ] (A.V ℓ), W = ⊥ → Module.finrank ℚ_[ℓ] W = 0 := by
    rintro W rfl; exact finrank_bot _ _
  constructor
  · intro hm
    have hs : A.galRep ℓ σ = 1 := reduce 1 1 hm (fun v => by
      simp [LinearMap.baseChange_one])
    rcases ker_two_eq_bot (A.galRep ℓ σ) (Or.inl hs) with h | h
    · have := fin0 _ h; omega
    · have := fin0 _ h; omega
  · intro hm
    have hs : A.galRep ℓ σ = -1 := reduce (-1) (-1) hm (fun v => by
      rw [LinearMap.baseChange_neg, LinearMap.baseChange_one]
      simp only [Matrix.neg_mulVec, Matrix.one_mulVec]
      ext <;> simp)
    rcases ker_two_eq_bot (A.galRep ℓ σ) (Or.inr hs) with h | h
    · have := fin0 _ h; omega
    · have := fin0 _ h; omega

/-- **`G10Glue` from `T12K_ComplexConjEigen` and `ConjTwistOutside` (proved).** -/
theorem g10Glue_of_T12K_conjTwistOutside (hT : T12K_ComplexConjEigen)
    (hO : ConjTwistOutside) : G10Glue := by
  intro _ _ hF K _ _ _ A ℓ _ r e hdim _ _ _ hI
  apply isOdd_of_not_pm_one
  intro c hc
  by_cases hmem : c ∈ (resQ K).range
  · obtain ⟨σ, rfl⟩ := hmem
    exact not_pm_one_of_mem_range hT A r e hdim hI σ hc
  · have key := hO hF K A ℓ hdim c hc hmem
    constructor
    · intro h1
      exact key (galRep_eq_of_central A r e hI c (fun X => by
        rw [h1, _root_.one_mul, _root_.mul_one]))
    · intro h1
      exact key (galRep_eq_of_central A r e hI c (fun X => by rw [h1]; simp))

/-- **Totally real case (proved from `T12K_ComplexConjEigen` alone):** if every complex
conjugation lies in (the image of) `G_K`, e.g. `K` totally real, `r` is odd. -/
theorem isOdd_of_T12K_of_forall_mem (hT : T12K_ComplexConjEigen) {K : Type} [Field K]
    [NumberField K] (A : PkgI3.AbVar K) (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hdim : A.dim = 2) (hI : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e)
    (hall : ∀ c, PkgI4.IsComplexConj c → c ∈ (resQ K).range) : r.IsOdd := by
  apply isOdd_of_not_pm_one
  intro c hc
  obtain ⟨σ, rfl⟩ := hall c hc
  exact not_pm_one_of_mem_range hT A r e hdim hI σ hc

/-! ## §5. Corrected statement over the concrete leaves -/

open ZInQ.LeafPush2 in
/-- **G10, corrected statement (GLUE).** `G10Glue` with the opaque placeholders
`HSyn.T11_RiemannGAGA`, `HSyn.T12_ArtinComparison` replaced by the concrete textbook leaves of
`ZInQKernel/HDecomp/LeafPush2/T.lean`: T11(a) `T11a_RiemannEnd`, T11(b) `T11b_Rigidity` and T35
`UniformizationExists`, together with T5 (`PkgI2.TorsionStructure`) and T26
(`PkgI3.TateModuleFree`), the inputs of the Artin comparison (T12 is glue, so it is not a
hypothesis). The conclusion is unchanged. -/
def G10GlueConcrete : Prop :=
  T11a_RiemannEnd → T11b_Rigidity → UniformizationExists → PkgI2.TorsionStructure.{0} →
  PkgI3.TateModuleFree → PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Module.finrank ℤ (PkgI3.AbVar.End A) = 4 → PkgI3.EndDivision A →
    (∃ x y : PkgI3.AbVar.End A, x * y ≠ y * x) →
    Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G10Out r

open ZInQ.LeafPush2 in
/-- **G10 core from the leaves (GLUE, unproved; STANDARD).** `ConjTwistNontrivial` with T11(a),
T11(b), T35, T5 and T26 available: the leaves its proof (docstring of `ConjTwistNontrivial`, §6)
uses besides Faltings. The remaining work is glue: the conjugate variety `A^c`, the Artin
comparison `T_ℓ(A) ≅ Λ ⊗ ℤ_ℓ` at `ι` (from T35 and T5, as for `T12_ComplexConjEigen`) compatible
with `c_*` and `F_*`, and the instantiation of `betti_skeleton`. -/
def ConjTwistFromLeaves : Prop :=
  T11a_RiemannEnd → T11b_Rigidity → UniformizationExists → PkgI2.TorsionStructure.{0} →
  PkgI3.TateModuleFree → ConjTwistNontrivial

theorem g10GlueConcrete_of_conjTwistFromLeaves (h : ConjTwistFromLeaves) : G10GlueConcrete := by
  intro h11a h11b h35 h5 h26 hF K _ _ _ A ℓ _ r e hdim _ _ _ hI
  exact g10Out_of_conjTwist (h h11a h11b h35 h5 h26) hF K A ℓ r e hdim hI

/-! ## §6. The linear-algebra skeleton of `ConjTwistNontrivial` (proved)

The proof of `ConjTwistNontrivial` (its docstring) has four geometric inputs and one piece of
linear algebra. With `H = H₁(A(ℂ),ℚ)`, `H' = H₁(A^c(ℂ),ℚ)`, `W ⊆ Hom_ℚ(H, H')` the image of
`Hom(A, A^c) ⊗ ℚ`, `J, J'` the complex structures on `H ⊗ ℝ`, `H' ⊗ ℝ`, `F = F_*` the map induced by
complex conjugation `A(ℂ) → A^c(ℂ)`, and `E = ℚ_ℓ`:
(i) Faltings: `c_*` lies in the `E`-span of `W` (inside `Hom_E(V_ℓ A, V_ℓ A^c)`);
(ii) Artin comparison at `ι`: `V_ℓ ≅ E ⊗ H₁` carrying `c_*` to `F ⊗ 1`;
(iii) T11: elements of `W` are holomorphic (`φ J = J' φ`);
(iv) `F` is antiholomorphic (`F J = −J' F`).
`betti_skeleton` is the linear algebra: (i)-(iv) force `F = 0`. -/

/-- Base change along a field extension is injective on linear maps `V → V'`. -/
theorem baseChange_injective₂ (k E V V' : Type*) [Field k] [Field E] [Algebra k E]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V'] {f g : V →ₗ[k] V'}
    (h : f.baseChange E = g.baseChange E) : f = g := by
  ext v
  apply one_tmul_injective k E V'
  have := LinearMap.congr_fun h ((1 : E) ⊗ₜ[k] v)
  simpa using this

/-- **Rationality (proved).** If `1 ⊗ x` lies in the `E`-span of `1 ⊗ W` inside `E ⊗_k U`, then
`x ∈ W`: `(W ⊗ E) ∩ U = W`. -/
theorem mem_of_one_tmul_mem_span (k E U : Type*) [Field k] [Field E] [Algebra k E]
    [AddCommGroup U] [Module k U] (W : Submodule k U) (x : U)
    (h : (1 : E) ⊗ₜ[k] x ∈ Submodule.span E ((fun w : U => (1 : E) ⊗ₜ[k] w) '' (W : Set U))) :
    x ∈ W := by
  let q : E ⊗[k] U →ₗ[E] E ⊗[k] (U ⧸ W) := W.mkQ.baseChange E
  have hspan : Submodule.span E ((fun w : U => (1 : E) ⊗ₜ[k] w) '' (W : Set U)) ≤
      LinearMap.ker q := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp [q, (Submodule.Quotient.mk_eq_zero W).mpr hw]
  have hx : q ((1 : E) ⊗ₜ[k] x) = 0 := hspan h
  have h2 : (1 : E) ⊗ₜ[k] (W.mkQ x) = (1 : E) ⊗ₜ[k] (0 : U ⧸ W) := by
    rw [TensorProduct.tmul_zero]; simpa [q] using hx
  exact (Submodule.Quotient.mk_eq_zero W).mp (one_tmul_injective k E (U ⧸ W) h2)

/-- A map that is both linear and antilinear for complex structures (`J'` injective) is `0`. -/
theorem eq_zero_of_holo_of_antiholo {R M N : Type*} [Field R] [CharZero R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (J : M →ₗ[R] M) (J' : N →ₗ[R] N)
    (hJ' : Function.Injective J') (F : M →ₗ[R] N) (h1 : F ∘ₗ J = J' ∘ₗ F)
    (h2 : F ∘ₗ J = -(J' ∘ₗ F)) : F = 0 := by
  ext m
  have a := LinearMap.congr_fun h1 m
  have b := LinearMap.congr_fun h2 m
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.neg_apply] at a b
  have h3 : (2 : R) • J' (F m) = 0 := by
    rw [two_smul]
    have : J' (F m) = -J' (F m) := a.symm.trans b
    nth_rewrite 1 [this]; exact neg_add_cancel _
  have h4 : J' (F m) = J' 0 := by
    rw [map_zero]; exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  simpa using hJ' h4

/-- **The Betti skeleton (proved).** `H, H'` rational vector spaces with complex structures
`J, J'` on `H ⊗ ℝ, H' ⊗ ℝ`; `W ⊆ Hom_ℚ(H, H')` consisting of holomorphic maps (T11); `F`
antiholomorphic; `can : E ⊗ Hom_ℚ(H, H') → Hom_E(E ⊗ H, E ⊗ H')` the canonical map, injective
(standard for `H` finite-dimensional); `F ⊗ 1` in the `E`-span of `W ⊗ 1` (Faltings + Artin
comparison). Then `F = 0`. -/
theorem betti_skeleton (E : Type*) [Field E] [Algebra ℚ E] {H H' : Type*} [AddCommGroup H]
    [Module ℚ H] [AddCommGroup H'] [Module ℚ H']
    (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H')
    (hJ' : Function.Injective J') (W : Submodule ℚ (H →ₗ[ℚ] H'))
    (hW : ∀ φ ∈ W, φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ)
    (F : H →ₗ[ℚ] H') (hF : F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ))
    (can : E ⊗[ℚ] (H →ₗ[ℚ] H') →ₗ[E] (E ⊗[ℚ] H →ₗ[E] E ⊗[ℚ] H')) (hι : Function.Injective can)
    (hι1 : ∀ φ, can ((1 : E) ⊗ₜ[ℚ] φ) = φ.baseChange E)
    (hFal : F.baseChange E ∈
      Submodule.span E ((fun φ : H →ₗ[ℚ] H' => φ.baseChange E) '' (W : Set (H →ₗ[ℚ] H')))) :
    F = 0 := by
  have himg : (fun φ : H →ₗ[ℚ] H' => φ.baseChange E) '' (W : Set (H →ₗ[ℚ] H')) =
      can '' ((fun w : H →ₗ[ℚ] H' => (1 : E) ⊗ₜ[ℚ] w) '' (W : Set (H →ₗ[ℚ] H'))) := by
    rw [Set.image_image]; simp only [hι1]
  rw [himg, Submodule.span_image, ← hι1] at hFal
  obtain ⟨y, hy, hyF⟩ := hFal
  rw [hι hyF] at hy
  have hFW : F ∈ W := mem_of_one_tmul_mem_span ℚ E _ W F hy
  have h0 : F.baseChange ℝ = 0 :=
    eq_zero_of_holo_of_antiholo J J' hJ' (F.baseChange ℝ) (hW F hFW) hF
  apply baseChange_injective₂ ℚ ℝ H H'
  rw [h0, LinearMap.baseChange_zero]

/-! ## §7. `T12K_ComplexConjEigen` contains `T12_ComplexConjEigen` (proved)

`qEmbRing` and `resQ_spec` are copied verbatim from scratch/g0-mod-galois/part_galois.lean. -/

/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- If `τ ∈ G_K` acts on `K̄` as complex conjugation through some embedding `K̄ → ℂ`, then
`resQ K τ` is a complex conjugation. -/
theorem isComplexConj_resQ (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (j : AlgebraicClosure K →+* ℂ)
    (hj : ∀ x, j (τ x) = starRingEnd ℂ (j x)) : PkgI4.IsComplexConj (resQ K τ) :=
  ⟨(j.comp (qEmbRing K)).toRatAlgHom, fun x => by
    simp only [RingHom.toRatAlgHom_apply, RingHom.coe_comp, Function.comp_apply]
    rw [resQ_spec, hj]⟩

/-- **`T12K_ComplexConjEigen → T12_ComplexConjEigen` (proved).** -/
theorem t12_of_t12K (h : T12K_ComplexConjEigen) : ZInQ.LeafPush2.T12_ComplexConjEigen := by
  intro A g hg ℓ _ c hc
  obtain ⟨j, hj⟩ := hc
  exact h ℚ A g hg ℓ c (isComplexConj_resQ ℚ c j.toRingHom hj)

end G0Galois

#print axioms G0Galois.g10Glue_of_conjTwist
#print axioms G0Galois.g10Glue_of_T12K_conjTwistOutside
#print axioms G0Galois.isOdd_of_T12K_of_forall_mem
#print axioms G0Galois.g10GlueConcrete_of_conjTwistFromLeaves
#print axioms G0Galois.betti_skeleton
#print axioms G0Galois.t12_of_t12K
