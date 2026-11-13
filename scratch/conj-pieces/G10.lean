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
* §5 states the corrected form `G10GlueConcrete` (the opaque placeholders replaced by the concrete
  leaves T11a, T11b, T35 of `ZInQKernel/HDecomp/LeafPush2/T.lean`, T5, T26) and proves it from
  `ConjTwistFromLeaves` (the same glue with those leaves as hypotheses). §4 also splits G10 into
  a number-field T12 (`T12K_ComplexConjEigen`, for `c ∈ G_K`) and `ConjTwistOutside`.
* §6 proves the linear algebra of `ConjTwistNontrivial`'s proof (`betti_skeleton`,
  `betti_skeleton_fd`); §7 proves `T12K_ComplexConjEigen → T12_ComplexConjEigen`; §8 proves that
  `G_K` is normal in `G_ℚ` through `resQ` for `K/ℚ` Galois (`exists_resQ_conj`), so the twist
  condition in `ConjTwistNontrivial` is not vacuous.
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

/-- **Rationality for matrices (proved).** If `X.map (algebraMap k E)` lies in the `E`-span of
`W.map`, then `X ∈ W`. -/
theorem matrix_mem_of_map_mem_span {k E m n : Type*} [Field k] [Field E] [Algebra k E]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Submodule k (Matrix m n k))
    (X : Matrix m n k)
    (h : X.map (algebraMap k E) ∈
      Submodule.span E ((fun Y : Matrix m n k => Y.map (algebraMap k E)) '' (W : Set _))) :
    X ∈ W := by
  by_contra hX
  obtain ⟨mu, hmuX, hmuW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hX inferInstance
  have hmuW' : ∀ Y ∈ W, mu Y = 0 := fun Y hY => by
    have : mu Y ∈ W.map mu := ⟨Y, hY, rfl⟩
    rwa [hmuW, Submodule.mem_bot] at this
  let muE : Matrix m n E →ₗ[E] E := ∑ i, ∑ j,
    algebraMap k E (mu (Matrix.single i j 1)) • Matrix.entryLinearMap E E i j
  have key : ∀ Y : Matrix m n k, muE (Y.map (algebraMap k E)) = algebraMap k E (mu Y) := by
    intro Y
    conv_rhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [muE, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.entryLinearMap_apply, Matrix.map_apply, map_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hs : Matrix.single i j (Y i j) = Y i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, _root_.mul_one]
    rw [hs, map_smul, smul_eq_mul, map_mul, mul_comm]
  have hle : Submodule.span E ((fun Y : Matrix m n k => Y.map (algebraMap k E)) '' (W : Set _)) ≤
      LinearMap.ker muE := by
    rw [Submodule.span_le]
    rintro _ ⟨Y, hY, rfl⟩
    simp [key, hmuW' Y hY]
  have h0 : muE (X.map (algebraMap k E)) = 0 := hle h
  rw [key] at h0
  exact hmuX ((algebraMap k E).injective (by rw [h0, map_zero]))

/-- **Rationality for linear maps (proved).** For finite-dimensional `H, H'`, if `F ⊗ 1` lies in
the `E`-span of `{φ ⊗ 1 : φ ∈ W}` inside `Hom_E(E ⊗ H, E ⊗ H')`, then `F ∈ W`. -/
theorem mem_of_baseChange_mem_span (k E : Type*) [Field k] [Field E] [Algebra k E]
    {H H' : Type*} [AddCommGroup H] [Module k H] [FiniteDimensional k H] [AddCommGroup H']
    [Module k H'] [FiniteDimensional k H'] (W : Submodule k (H →ₗ[k] H')) (F : H →ₗ[k] H')
    (hFal : F.baseChange E ∈
      Submodule.span E ((fun φ : H →ₗ[k] H' => φ.baseChange E) '' (W : Set (H →ₗ[k] H')))) :
    F ∈ W := by
  let b := Module.finBasis k H
  let b' := Module.finBasis k H'
  let T := LinearMap.toMatrix b b'
  let TE := LinearMap.toMatrix (Algebra.TensorProduct.basis E b) (Algebra.TensorProduct.basis E b')
  have hT : T F ∈ W.map T.toLinearMap := by
    apply matrix_mem_of_map_mem_span (E := E)
    have h1 := Submodule.mem_map_of_mem (f := TE.toLinearMap) hFal
    rw [Submodule.map_span, Set.image_image] at h1
    simp only [LinearEquiv.coe_coe, TE, LinearMap.toMatrix_baseChange] at h1
    rw [Submodule.map_coe, Set.image_image]
    exact h1
  obtain ⟨G, hG, hTG⟩ := hT
  rwa [T.injective hTG] at hG

/-- **The Betti skeleton, finite-dimensional form (proved).** As `betti_skeleton`, without the
canonical map: `H, H'` finite-dimensional, `F ⊗ 1` in the `E`-span of `{φ ⊗ 1 : φ ∈ W}`. -/
theorem betti_skeleton_fd (E : Type*) [Field E] [Algebra ℚ E] {H H' : Type*} [AddCommGroup H]
    [Module ℚ H] [FiniteDimensional ℚ H] [AddCommGroup H'] [Module ℚ H'] [FiniteDimensional ℚ H']
    (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H')
    (hJ' : Function.Injective J') (W : Submodule ℚ (H →ₗ[ℚ] H'))
    (hW : ∀ φ ∈ W, φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ)
    (F : H →ₗ[ℚ] H') (hF : F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ))
    (hFal : F.baseChange E ∈
      Submodule.span E ((fun φ : H →ₗ[ℚ] H' => φ.baseChange E) '' (W : Set (H →ₗ[ℚ] H')))) :
    F = 0 := by
  have hFW : F ∈ W := mem_of_baseChange_mem_span ℚ E W F hFal
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

/-! ## §8. Non-vacuity of the twist condition (proved)

For `K/ℚ` Galois, every `c σ c⁻¹` with `σ ∈ G_K` is `resQ K τ` for some `τ ∈ G_K`, so the
quantifier `∀ σ τ, resQ K τ = c * resQ K σ * c⁻¹ → …` in `ConjTwistNontrivial` constrains every
`σ`, and the Prop says what its docstring says. -/

/-- `qEmbRing K : ℚ̄ → K̄` is bijective (`K̄` is algebraic over `ℚ`). -/
theorem qEmbRing_bijective (K : Type) [Field K] [NumberField K] :
    Function.Bijective (qEmbRing K) := by
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)
  let g : AlgebraicClosure K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let h : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (g.toRingHom.comp (qEmbRing K)).toRatAlgHom
  have hb : Function.Bijective h := Algebra.IsAlgebraic.algHom_bijective h
  refine ⟨(qEmbRing K).injective, fun z => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (g z)
  exact ⟨x, g.toRingHom.injective hx⟩

/-- Elements of `ℚ̄` landing in `K` are fixed by `resQ K σ`. -/
theorem resQ_fix (K : Type) [Field K] [NumberField K] (σ : Field.absoluteGaloisGroup K)
    (u : AlgebraicClosure ℚ)
    (hu : qEmbRing K u ∈ (algebraMap K (AlgebraicClosure K)).range) : resQ K σ u = u := by
  obtain ⟨k, hk⟩ := hu
  apply (qEmbRing K).injective
  refine (resQ_spec K σ u).trans ?_
  rw [← hk]
  exact AlgEquiv.commutes (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k

/-- For `K/ℚ` Galois, the elements of `ℚ̄` landing in `K` form a `G_ℚ`-stable set. -/
theorem range_stable (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (g : PkgI4.GQ)
    (u : AlgebraicClosure ℚ)
    (hu : qEmbRing K u ∈ (algebraMap K (AlgebraicClosure K)).range) :
    qEmbRing K (g u) ∈ (algebraMap K (AlgebraicClosure K)).range := by
  obtain ⟨k, hk⟩ := hu
  have hsplit : ((minpoly ℚ k).map (algebraMap ℚ K)).Splits :=
    Normal.splits (IsGalois.to_normal) k
  have hp0 : (minpoly ℚ k).map (algebraMap ℚ K) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral k))
  apply hsplit.mem_range_of_isRoot hp0
  rw [Polynomial.map_map, Polynomial.IsRoot, Polynomial.eval_map]
  have e1 : (algebraMap K (AlgebraicClosure K)).comp (algebraMap ℚ K) =
      (qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have e2 : (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
      (algebraMap ℚ (AlgebraicClosure ℚ)) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    Subsingleton.elim _ _
  have hu0 : Polynomial.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) u (minpoly ℚ k) = 0 := by
    apply (qEmbRing K).injective
    rw [Polynomial.hom_eval₂, ← e1, ← hk, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      minpoly.aeval, map_zero, map_zero]
  rw [e1, ← Polynomial.hom_eval₂]
  have : Polynomial.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) (g u) (minpoly ℚ k) = 0 := by
    have := Polynomial.hom_eval₂ (minpoly ℚ k) (algebraMap ℚ (AlgebraicClosure ℚ))
      (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) u
    rw [e2, hu0, map_zero] at this
    exact this.symm
  rw [this, map_zero]

/-- **Non-vacuity of the twist condition (proved).** For `K/ℚ` Galois, `G_K` is normal in `G_ℚ`
through `resQ`: every `g σ g⁻¹` (`σ ∈ G_K`, `g ∈ G_ℚ`) is `resQ K τ` for some `τ ∈ G_K`. -/
theorem exists_resQ_conj (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (g : PkgI4.GQ)
    (σ : Field.absoluteGaloisGroup K) : ∃ τ, resQ K τ = g * resQ K σ * g⁻¹ := by
  let Φ : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (qEmbRing K) (qEmbRing_bijective K)
  let h : PkgI4.GQ := g * resQ K σ * g⁻¹
  let τr : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    (Φ.symm.trans (h : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)).trans Φ
  have hfix : ∀ k : K, τr (algebraMap K (AlgebraicClosure K) k) =
      algebraMap K (AlgebraicClosure K) k := by
    intro k
    obtain ⟨x₀, hx₀⟩ := (qEmbRing_bijective K).2 (algebraMap K (AlgebraicClosure K) k)
    have hΦ : Φ.symm (algebraMap K (AlgebraicClosure K) k) = x₀ := by
      rw [← hx₀]; exact Φ.symm_apply_apply x₀
    have h1 := range_stable K g⁻¹ x₀ ⟨k, hx₀.symm⟩
    have h2 : resQ K σ (g⁻¹ x₀) = g⁻¹ x₀ := resQ_fix K σ _ h1
    have h3 : h x₀ = x₀ := by
      change g (resQ K σ (g⁻¹ x₀)) = x₀
      rw [h2]; exact AlgEquiv.apply_symm_apply g x₀
    change Φ (h (Φ.symm (algebraMap K (AlgebraicClosure K) k))) = _
    rw [hΦ, h3]; exact hx₀
  refine ⟨AlgEquiv.ofRingEquiv (f := τr) hfix, ?_⟩
  apply AlgEquiv.ext; intro x
  apply (qEmbRing K).injective
  refine (resQ_spec K _ x).trans ?_
  change Φ (h (Φ.symm (Φ x))) = _
  rw [Φ.symm_apply_apply]; rfl


/-! # conj-pieces G10 assembly

Everything above is `scratch/g10-odd/G10Odd.lean` verbatim up to its `end G0Galois`.
Below: `scratch/conj-pieces/ConjPieces.lean` from conj-twist's §2 on (conj-twist's §1 is a
verbatim copy of G10Odd declarations, already present above), then the G10 corollaries. -/

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj

/-! ## §2. Faltings in `ℚ_ℓ`-form (proved from `FaltingsTate` and `TateModuleFree`) -/

/-- The `ℚ_ℓ`-span of `{V_ℓ(f) : f ∈ Hom_K(A, B)}` inside `Hom_{ℚ_ℓ}(V_ℓ A, V_ℓ B)`. -/
def homSpanV {K : Type} [Field K] (A B : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Submodule ℚ_[ℓ] (A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) :=
  Submodule.span ℚ_[ℓ] (Set.range fun f : PkgI3.AbVar.Hom A B =>
    (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ])

open PkgI3 PkgI3.AbVar in
/-- **Faltings, `ℚ_ℓ`-form (proved).** For abelian varieties `A, B` over a number field, every
`G_K`-equivariant `ℚ_ℓ`-linear map `V_ℓ(A) → V_ℓ(B)` lies in the `ℚ_ℓ`-span of
`{V_ℓ(f) : f ∈ Hom_K(A, B)}`. From `FaltingsTate` (Faltings 1983, Satz 4 / Kor. 1) and
`TateModuleFree` (T26): `T_ℓ A` is finitely presented, so `s • φ` maps `T_ℓ A` into `T_ℓ B` for
some `s ≠ 0`, and the lift is equivariant (the proof of `PkgI3.exists_hom_ne_zero_of_equivariant`). -/
theorem faltingsV (hF : FaltingsTate) (hT : TateModuleFree)
    {K : Type} [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ)
    (heq : ∀ σ, φ ∘ₗ A.galRep ℓ σ = B.galRep ℓ σ ∘ₗ φ) : φ ∈ homSpanV A B ℓ := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfinA, -⟩ := hT K A ℓ hℓK
  obtain ⟨hfreeB, -, -⟩ := hT K B ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιB : B.T ℓ →ₗ[ℤ_[ℓ]] B.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (B.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιB := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιB ((φ.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hιB : Function.Injective ιB := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιB).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hιBσ : ∀ σ x, ιB (B.galT σ x) = B.galRep ℓ σ (ιB x) := fun σ x => by
    simp [ιB, galRep, LinearMap.baseChange_tmul]
  have hsφ : ∀ x, ιB (h x) = (s : ℤ_[ℓ]) • φ (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιB
    rw [hsφ, hιAσ, hιBσ, hsφ]
    have := congrArg (fun g => g (ιA x)) (heq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A B) := by
    rw [(hF K A B ℓ).2]; exact hheq
  have hmem : ∀ z, (tateHomZl ℓ A B z).baseChange ℚ_[ℓ] ∈ homSpanV A B ℓ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      have e : tateHomZl ℓ A B (a ⊗ₜ f) = a • tateHom ℓ A B f := rfl
      rw [e, LinearMap.baseChange_smul]
      have : (a • (tateHom ℓ A B f).baseChange ℚ_[ℓ]) =
          (algebraMap ℤ_[ℓ] ℚ_[ℓ] a) • (tateHom ℓ A B f).baseChange ℚ_[ℓ] :=
        (algebraMap_smul ℚ_[ℓ] a _).symm
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
    | add y z hy hz =>
      rw [map_add, LinearMap.baseChange_add]; exact Submodule.add_mem _ hy hz
  have hc : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) ≠ 0 := by
    simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0
  have hφ : φ = (algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • h.baseChange ℚ_[ℓ] := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    apply LinearMap.ext
    intro x
    change φ ((1 : ℚ_[ℓ]) ⊗ₜ x) =
      (algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • h.baseChange ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ x)
    rw [LinearMap.baseChange_tmul]
    have h1 : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] h x : B.V ℓ) = (s : ℤ_[ℓ]) • φ ((1 : ℚ_[ℓ]) ⊗ₜ x) :=
      hsφ x
    rw [h1, ← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]), smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hφ, ← hz]
  exact Submodule.smul_mem _ _ (hmem z)

/-! ## §3. From `c ∈ G_ℚ` to an automorphism of `K̄` (proved) -/

/-- `σ ∈ G_K` as a `K`-automorphism of `K̄` (for application to elements). -/
abbrev gA {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- **Complex conjugation on `K̄` (proved).** For `K/ℚ` Galois and a complex conjugation
`c ∈ G_ℚ`, transport `c` along `qEmbRing K : ℚ̄ ≅ K̄` to `cc : K̄ ≅ K̄`. Then `cc` is complex
conjugation for the embedding `ι = j ∘ qEmbRing⁻¹` (`j` realizing `c`), maps `K` to itself (`K`
normal), is an involution, and `τ ∘ cc = cc ∘ σ` in `Aut(K̄)` implies
`resQ K τ = c · resQ K σ · c⁻¹` in `G_ℚ`. -/
theorem conjData (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (c : PkgI4.GQ)
    (hc : PkgI4.IsComplexConj c) :
    ∃ (cc : AlgebraicClosure K ≃+* AlgebraicClosure K) (emb : AlgebraicClosure K →+* ℂ),
      (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) ∧
      (∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') ∧
      (∀ x, cc (cc x) = x) ∧
      (∀ σ τ : Field.absoluteGaloisGroup K, (∀ x, gA τ (cc x) = cc (gA σ x)) →
        resQ K τ = c * resQ K σ * c⁻¹) := by
  have c2 := isComplexConj_mul_self hc
  obtain ⟨j, hj⟩ := hc
  let Φ : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (qEmbRing K) (qEmbRing_bijective K)
  let cc : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    (Φ.symm.trans (c : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)).trans Φ
  have hcc : ∀ u, cc (Φ u) = Φ (c u) := fun u => by
    change Φ (c (Φ.symm (Φ u))) = _
    rw [Φ.symm_apply_apply]
  have hΦ : ∀ u, Φ u = qEmbRing K u := fun _ => rfl
  refine ⟨cc, j.toRingHom.comp Φ.symm.toRingHom, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨u, rfl⟩ := Φ.surjective x
    rw [hcc]
    change j (Φ.symm (Φ (c u))) = starRingEnd ℂ (j (Φ.symm (Φ u)))
    rw [Φ.symm_apply_apply, Φ.symm_apply_apply, hj]
  · intro k
    obtain ⟨u, hu⟩ := Φ.surjective (algebraMap K _ k)
    obtain ⟨k', hk'⟩ := range_stable K c u ⟨k, hu.symm⟩
    exact ⟨k', by rw [← hu, hcc]; exact hk'.symm⟩
  · intro x
    obtain ⟨u, rfl⟩ := Φ.surjective x
    rw [hcc, hcc]
    congr 1
    exact congrArg (fun g : PkgI4.GQ => g u) c2
  · intro σ τ hστ
    apply AlgEquiv.ext; intro u
    apply (qEmbRing K).injective
    have e1 : (c * resQ K σ * c⁻¹) u = c (resQ K σ (c⁻¹ u)) := rfl
    have a1 : qEmbRing K (resQ K τ u) = gA τ (Φ u) := resQ_spec K τ u
    have a2 : Φ (resQ K σ (c⁻¹ u)) = gA σ (Φ (c⁻¹ u)) := resQ_spec K σ _
    have a3 : Φ u = cc (Φ (c⁻¹ u)) := by
      rw [hcc]; congr 1; exact (AlgEquiv.apply_symm_apply c u).symm
    rw [a1, e1]
    change gA τ (Φ u) = Φ (c (resQ K σ (c⁻¹ u)))
    rw [← hcc, a2, ← hστ, ← a3]

/-- **Every `τ ∈ G_K` is a `cc`-twist (proved):** `σ = cc τ cc` fixes `K`. -/
theorem exists_twist (K : Type) [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k')
    (h2 : ∀ x, cc (cc x) = x) (τ : Field.absoluteGaloisGroup K) :
    ∃ σ : Field.absoluteGaloisGroup K, ∀ x, gA τ (cc x) = cc (gA σ x) := by
  let σr : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    (cc.trans ((gA τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : AlgebraicClosure K ≃+* AlgebraicClosure K)).trans cc
  have hfix : ∀ k : K, σr (algebraMap K _ k) = algebraMap K _ k := by
    intro k
    obtain ⟨k', hk'⟩ := hK k
    change cc (gA τ (cc (algebraMap K _ k))) = _
    rw [hk', AlgEquiv.commutes, ← hk', h2]
  refine ⟨AlgEquiv.ofRingEquiv (f := σr) hfix, fun x => ?_⟩
  change gA τ (cc x) = cc (cc (gA τ (cc x)))
  rw [h2]

/-! ## §4. The remaining glue and the reduction -/

/-- The `ℚ`-subspace of `Hom_ℚ(H, H')` of maps that are holomorphic for complex structures `J, J'`
on `H ⊗ ℝ`, `H' ⊗ ℝ`. -/
def holoSub {H H' : Type} [AddCommGroup H] [Module ℚ H] [AddCommGroup H'] [Module ℚ H']
    (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') :
    Submodule ℚ (H →ₗ[ℚ] H') where
  carrier := {φ | φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ}
  add_mem' := by
    intro φ ψ hφ hψ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.baseChange_add, LinearMap.add_comp, LinearMap.comp_add, hφ, hψ]
  zero_mem' := by simp
  smul_mem' := by
    intro q φ hφ
    simp only [Set.mem_setOf_eq] at *
    apply LinearMap.ext; intro x
    have := LinearMap.congr_fun hφ x
    simp only [LinearMap.coe_comp, Function.comp_apply] at this ⊢
    rw [LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.smul_apply, this,
      LinearMap.map_smul_of_tower]

/-- **G10 core, geometric input (GLUE, unproved; STANDARD).** Conjugate variety plus Artin
comparison at a complex place, with holomorphy of homomorphisms. For a number field `K`, an
abelian surface `A/K`, a prime `ℓ`, a ring automorphism `cc` of `K̄` mapping `K` to itself and an
embedding `ι : K̄ → ℂ` with `ι ∘ cc = conj ∘ ι`, there are
* an abelian variety `B/K` and a `ℚ_ℓ`-linear `C : V_ℓ(A) → V_ℓ(B)` with the twisted equivariance
  `C ρ_A(σ) = ρ_B(τ) C` whenever `τ ∘ cc = cc ∘ σ`. Witness: `B = A^s = A ×_{K,s} K`, `s = cc|_K`,
  and `C = c_*`, the transport of `K̄`-points `P ↦ P ∘ Spec(cc)` (`A^s(K̄) = A(K̄ via s)`);
* finite-dimensional `ℚ`-spaces `H, H'` with `ℚ_ℓ ⊗ H ≅ V_ℓ(A)` (`α`), `ℚ_ℓ ⊗ H' ≅ V_ℓ(B)` (`β`),
  ℝ-linear `J, J'` on `ℝ ⊗ H, ℝ ⊗ H'` (`J'` injective) and a nonzero `ℚ`-linear `F : H → H'`.
  Witness: `H = H₁(A(ℂ)_ι, ℚ)`, `H' = H₁(B(ℂ)_ι, ℚ) = H₁(A(ℂ)_{conj ∘ ι}, ℚ)` (the lattices of
  the uniformizations T35, `ℝ ⊗ H = ℂ^g`), `J, J'` multiplication by `i`, `α, β` the Artin
  comparison through `ι` (`A(K̄)[ℓⁿ] ≅ A(ℂ)[ℓⁿ] = ℓ⁻ⁿΛ/Λ`, bijective by T5), `F = F_*` the map
  of complex conjugation `A(ℂ)_ι → A(ℂ)_{conj ∘ ι}` on `H₁` (bijective, `H ≠ 0` as `dim A = 2`);
such that `F` is antiholomorphic (`F J = −J' F`), `C` corresponds to `F ⊗ 1` (`ι ∘ cc = conj ∘ ι`),
and each `f ∈ Hom_K(A, B)` corresponds to `φ ⊗ 1` for a holomorphic `φ : H → H'` (`φ = H₁(f)`,
holomorphic as `f` is a morphism of varieties: T11(a) in Hom form, Mumford §1, Birkenhake–Lange
1.2.1; UNVERIFIED numbers). Sources: SGA 4 XI 4.4 (Artin comparison), Mumford §1, §4 (T35, T5);
N5 L742-751, h-trust C5. -/
def ConjBettiData : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (cc : AlgebraicClosure K ≃+* AlgebraicClosure K) (emb : AlgebraicClosure K →+* ℂ),
    A.dim = 2 → (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) →
    (∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') →
    ∃ (B : PkgI3.AbVar K) (C : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ),
      (∀ σ τ : Field.absoluteGaloisGroup K, (∀ x, gA τ (cc x) = cc (gA σ x)) →
          C ∘ₗ A.galRep ℓ σ = B.galRep ℓ τ ∘ₗ C) ∧
      ∃ (H H' : Type) (_ : AddCommGroup H) (_ : Module ℚ H) (_ : FiniteDimensional ℚ H)
        (_ : AddCommGroup H') (_ : Module ℚ H') (_ : FiniteDimensional ℚ H')
        (α : ℚ_[ℓ] ⊗[ℚ] H ≃ₗ[ℚ_[ℓ]] A.V ℓ) (β : ℚ_[ℓ] ⊗[ℚ] H' ≃ₗ[ℚ_[ℓ]] B.V ℓ)
        (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') (F : H →ₗ[ℚ] H'),
        Function.Injective J' ∧ F ≠ 0 ∧
        F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ) ∧
        β.symm.toLinearMap ∘ₗ C ∘ₗ α.toLinearMap = F.baseChange ℚ_[ℓ] ∧
        ∀ f : PkgI3.AbVar.Hom A B, ∃ φ : H →ₗ[ℚ] H',
          φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ ∧
          β.symm.toLinearMap ∘ₗ (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] ∘ₗ
            α.toLinearMap = φ.baseChange ℚ_[ℓ]

/-- **`ConjTwistNontrivial` from T26 and `ConjBettiData` (proved).** If `ρ_A(τ) = ρ_A(σ)` whenever
`resQ τ = c resQ σ c⁻¹`, the twisted-equivariant `C` is `G_K`-equivariant, so lies in the span of
`Hom(A, B)` (`faltingsV`); on the Betti side `F ⊗ 1` lies in the span of holomorphic `φ ⊗ 1`, so
`F = 0` (`betti_skeleton_fd`), a contradiction. -/
theorem conjTwistNontrivial_of_conjBettiData (hT : PkgI3.TateModuleFree)
    (hB : ConjBettiData) : ConjTwistNontrivial := by
  intro hF K _ _ _ A ℓ _ hdim c hc hall
  obtain ⟨cc, emb, hι, hK, h2, hres⟩ := conjData K c hc
  obtain ⟨B, C, htw, H, H', _, _, _, _, _, _, α, β, J, J', F, hJ', hF0, hanti, hCF, hhol⟩ :=
    hB K A ℓ cc emb hdim hι hK
  have heq : ∀ τ, C ∘ₗ A.galRep ℓ τ = B.galRep ℓ τ ∘ₗ C := by
    intro τ
    obtain ⟨σ, hσ⟩ := exists_twist K cc hK h2 τ
    rw [hall σ τ (hres σ τ hσ), htw σ τ hσ]
  have hCmem := faltingsV hF hT A B ℓ C heq
  let Tr : (A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) ≃ₗ[ℚ_[ℓ]] (ℚ_[ℓ] ⊗[ℚ] H →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] H') :=
    LinearEquiv.arrowCongr α.symm β.symm
  have hTr : ∀ M, Tr M = β.symm.toLinearMap ∘ₗ M ∘ₗ α.toLinearMap := fun M => by
    apply LinearMap.ext; intro x
    simp [Tr, LinearEquiv.arrowCongr_apply]
  have hle : homSpanV A B ℓ ≤ (Submodule.span ℚ_[ℓ]
      ((fun φ : H →ₗ[ℚ] H' => φ.baseChange ℚ_[ℓ]) ''
        (holoSub J J' : Set (H →ₗ[ℚ] H')))).comap Tr.toLinearMap := by
    rw [homSpanV, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    obtain ⟨φ, hφJ, hφ⟩ := hhol f
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hTr]
    rw [hφ]
    exact Submodule.subset_span ⟨φ, hφJ, rfl⟩
  have hFmem := hle hCmem
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, hTr, hCF] at hFmem
  exact hF0 (betti_skeleton_fd ℚ_[ℓ] J J' hJ' (holoSub J J') (fun φ hφ => hφ) F hanti hFmem)

/-- **`ConjTwistFromLeaves` from `ConjBettiData` (proved).** T26 is among its hypotheses. -/
theorem conjTwistFromLeaves_of_conjBettiData (hB : ConjBettiData) : ConjTwistFromLeaves :=
  fun _ _ _ _ hT => conjTwistNontrivial_of_conjBettiData hT hB

/-! ## §5. The conjugate variety and the transport `c_*` (proved), and the Betti glue

`conjVar A s = A ×_{Spec K, Spec s} Spec K` for a ring endomorphism `s` of `K` (Mathlib's
`Over.pullback`, as `PkgI3.AbVar.baseChange`), and for an automorphism `cc` of `K̄` extending `s`,
the transport of points `A(K̄) → A^s(K̄)`, `P ↦ P ∘ Spec(cc)` read through the adjunction
`Over.map ⊣ Over.pullback` (the recipe of scratch/unram-tate/BCPoints.lean). It carries the
action of `σ` to that of `τ` whenever `τ ∘ cc = cc ∘ σ`. -/

open PkgI3 in
/-- `Spec(s) : Spec K → Spec K`. -/
abbrev specS {K : Type} [Field K] (s : K →+* K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom s)

/-- **The conjugate abelian variety** `A^s = A ×_{Spec K, Spec s} Spec K` (pullback along
`Spec(s)`; group structure transported by the monoidal functor `Over.pullback`). -/
def conjVar {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K) : PkgI3.AbVar K :=
  let f := specS s
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

section Transport

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K)
  (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k))

/-- The adjunction bijection for `Over.map (Spec s) ⊣ Over.pullback (Spec s)` is
multiplicative. -/
theorem homEquiv_mul_conj (X : Over (Spec (CommRingCat.of K)))
    (p q : (Over.map (specS s)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (specS s)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (specS s)).homEquiv X A.X p *
        (Over.mapPullbackAdj (specS s)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- `Spec(cc)`, as a morphism over `K` from `Spec K̄` (structure map `Spec(s) ∘ Spec(alg)`) to
`Spec K̄`. -/
def ccHom : (Over.map (specS s)).obj (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)) ⟶
    PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K))) (by
    simp only [Over.map_obj_hom, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact hs x)

/-- **The transport `c_*` on `K̄`-points (proved):** `A(K̄) → A^s(K̄)`, a group homomorphism. -/
def conjPt : A.Pt (AlgebraicClosure K) →* (conjVar A s).Pt (AlgebraicClosure K) :=
  MonoidHom.mk' (fun P => (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P))
    (fun P Q => by
      change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ (P * Q)) = _
      rw [MonObj.comp_mul, homEquiv_mul_conj]
      rfl)

/-- **Twisted equivariance of `c_*` on points (proved):** if `τ ∘ cc = cc ∘ σ` then
`c_*(σ P) = τ c_*(P)`. -/
theorem conjPt_galAct (σ τ : Field.absoluteGaloisGroup K)
    (h : ∀ x, gA τ (cc x) = cc (gA σ x)) (P : A.Pt (AlgebraicClosure K)) :
    conjPt A s cc hs (A.galAct (gA σ) P) = (conjVar A s).galAct (gA τ) (conjPt A s cc hs P) := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ PkgI3.AbVar.galHom (gA σ) ≫ P) =
    PkgI3.AbVar.galHom (gA τ) ≫ (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P)
  have hsq : ccHom s cc hs ≫ PkgI3.AbVar.galHom (gA σ) =
      (Over.map (specS s)).map (PkgI3.AbVar.galHom (gA τ)) ≫ ccHom s cc hs := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
        Spec.map (CommRingCat.ofHom ((gA σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →+* AlgebraicClosure K)) =
      Spec.map (CommRingCat.ofHom ((gA τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →+* AlgebraicClosure K)) ≫
        Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, hsq, Category.assoc, Adjunction.homEquiv_naturality_left]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`c_*` on Tate modules (proved):** `T_ℓ(A) → T_ℓ(A^s)`. -/
def conjT : A.T ℓ →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (conjPt A s cc hs))

/-- **`c_*` on `V_ℓ` (proved):** `V_ℓ(A) → V_ℓ(A^s)`. -/
def conjV : A.V ℓ →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ :=
  (conjT A s cc hs ℓ).baseChange ℚ_[ℓ]

theorem conjT_galT (σ τ : Field.absoluteGaloisGroup K) (h : ∀ x, gA τ (cc x) = cc (gA σ x)) :
    conjT A s cc hs ℓ ∘ₗ A.galT σ = (conjVar A s).galT τ ∘ₗ conjT A s cc hs ℓ := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  exact congrArg Additive.ofMul (conjPt_galAct A s cc hs σ τ h (Additive.toMul (x.1 n)))

/-- **Twisted equivariance of `c_*` on `V_ℓ` (proved):** `c_* ρ_A(σ) = ρ_{A^s}(τ) c_*` whenever
`τ ∘ cc = cc ∘ σ`. -/
theorem conjV_galRep (σ τ : Field.absoluteGaloisGroup K)
    (h : ∀ x, gA τ (cc x) = cc (gA σ x)) :
    conjV A s cc hs ℓ ∘ₗ A.galRep ℓ σ = (conjVar A s).galRep ℓ τ ∘ₗ conjV A s cc hs ℓ := by
  change (conjT A s cc hs ℓ).baseChange ℚ_[ℓ] ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
    ((conjVar A s).galT τ).baseChange ℚ_[ℓ] ∘ₗ (conjT A s cc hs ℓ).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, conjT_galT A s cc hs ℓ σ τ h]

end Transport

/-- The function `cc|_K : K → K` for an automorphism `cc` of `K̄` mapping `K` into itself. -/
def sFun {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) : K :=
  Classical.choose (hK k)

theorem sFun_spec {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) :
    algebraMap K (AlgebraicClosure K) (sFun cc hK k) = cc (algebraMap K _ k) :=
  (Classical.choose_spec (hK k)).symm

/-- The ring endomorphism `s = cc|_K` of `K`. -/
def restrictK {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') : K →+* K where
  toFun := sFun cc hK
  map_one' := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [sFun_spec]; simp)
  map_mul' a b := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [map_mul, sFun_spec, sFun_spec, sFun_spec, map_mul, map_mul])
  map_zero' := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [sFun_spec]; simp)
  map_add' a b := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [map_add, sFun_spec, sFun_spec, sFun_spec, map_add, map_add])

theorem restrictK_spec {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) :
    cc (algebraMap K _ k) = algebraMap K _ (restrictK cc hK k) :=
  (sFun_spec cc hK k).symm

/-- **G10 core, Betti input for the concrete `c_*` (GLUE, unproved; STANDARD).** For a number
field `K`, an abelian surface `A/K`, a prime `ℓ`, a ring endomorphism `s` of `K`, an automorphism
`cc` of `K̄` extending `s` and an embedding `ι : K̄ → ℂ` with `ι ∘ cc = conj ∘ ι`: there are
finite-dimensional `ℚ`-spaces `H, H'`, `ℚ_ℓ`-isomorphisms `α : ℚ_ℓ ⊗ H ≅ V_ℓ(A)`,
`β : ℚ_ℓ ⊗ H' ≅ V_ℓ(A^s)`, ℝ-linear `J, J'` on `ℝ ⊗ H, ℝ ⊗ H'` (`J'` injective) and a nonzero
`F : H → H'`, such that `F J = −J' F`, `β⁻¹ c_* α = F ⊗ 1` for the transport
`c_* = conjV A s cc hs ℓ` (§5), and every `f ∈ Hom_K(A, A^s)` acts as `φ ⊗ 1` with `φ J = J' φ`.
Witness (STANDARD): `H = H₁(A(ℂ)_ι, ℚ)`, `H' = H₁(A^s(ℂ)_ι, ℚ) = H₁(A(ℂ)_{conj∘ι}, ℚ)` (lattices
of the uniformizations T35, `ℝ ⊗ H = ℂ^g`), `J, J'` multiplication by `i`, `α, β` Artin's
comparison through `ι` (`A(K̄)[ℓⁿ] → A(ℂ)[ℓⁿ] = ℓ⁻ⁿΛ/Λ` bijective, by T5 over `K̄` and over `ℂ`;
SGA 4 XI 4.4), `F = F_*` for complex conjugation `A(ℂ)_ι → A(ℂ)_{conj∘ι}`, `P ↦ P ∘ Spec(conj)`,
antiholomorphic and bijective, `H ≠ 0` as `dim A = 2`; `β⁻¹ c_* α = F ⊗ 1` because
`P ∘ Spec(cc) ∘ Spec(ι) = P ∘ Spec(ι) ∘ Spec(conj)`; `φ = H₁(f)`, holomorphic because `f` is a
morphism of varieties (T11(a) in Hom form: Mumford §1, Birkenhake–Lange 1.2.1, UNVERIFIED
numbers). N5 L742-751, h-trust C5. -/
def ConjBettiComparison : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (s : K →+* K) (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ),
    A.dim = 2 → (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) →
      ∃ (H H' : Type) (_ : AddCommGroup H) (_ : Module ℚ H) (_ : FiniteDimensional ℚ H)
        (_ : AddCommGroup H') (_ : Module ℚ H') (_ : FiniteDimensional ℚ H')
        (α : ℚ_[ℓ] ⊗[ℚ] H ≃ₗ[ℚ_[ℓ]] A.V ℓ) (β : ℚ_[ℓ] ⊗[ℚ] H' ≃ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ)
        (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') (F : H →ₗ[ℚ] H'),
        Function.Injective J' ∧ F ≠ 0 ∧
        F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ) ∧
        β.symm.toLinearMap ∘ₗ conjV A s cc hs ℓ ∘ₗ α.toLinearMap = F.baseChange ℚ_[ℓ] ∧
        ∀ f : PkgI3.AbVar.Hom A (conjVar A s), ∃ φ : H →ₗ[ℚ] H',
          φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ ∧
          β.symm.toLinearMap ∘ₗ (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] ∘ₗ
            α.toLinearMap = φ.baseChange ℚ_[ℓ]

/-- **`ConjBettiData` from `ConjBettiComparison` (proved):** `B = conjVar A s` with
`s = cc|_K`, `C = conjV`, twisted equivariance by `conjV_galRep`. -/
theorem conjBettiData_of_comparison (h : ConjBettiComparison) : ConjBettiData := by
  intro K _ _ A ℓ _ cc emb hdim hι hK
  obtain ⟨H, H', i1, i2, i3, i4, i5, i6, α, β, J, J', F, hrest⟩ :=
    h K A ℓ (restrictK cc hK) cc (restrictK_spec cc hK) emb hdim hι
  exact ⟨conjVar A (restrictK cc hK), conjV A (restrictK cc hK) cc (restrictK_spec cc hK) ℓ,
    fun σ τ hστ => conjV_galRep A _ cc _ ℓ σ τ hστ,
    H, H', i1, i2, i3, i4, i5, i6, α, β, J, J', F, hrest⟩

/-- **`ConjTwistNontrivial` from T26 and `ConjBettiComparison` (proved).** -/
theorem conjTwistNontrivial_of_comparison (hT : PkgI3.TateModuleFree)
    (h : ConjBettiComparison) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_conjBettiData hT (conjBettiData_of_comparison h)

/-- **`ConjTwistFromLeaves` from `ConjBettiComparison` (proved).** -/
theorem conjTwistFromLeaves_of_comparison (h : ConjBettiComparison) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_conjBettiData (conjBettiData_of_comparison h)

/-! ## §6. The next split of `ConjBettiComparison` (statements compile; the assembly is not
formalized)

`ConjBettiComparison` follows (STANDARD argument, docs/research/conj-twist.md §3) from T35
(`UniformizationExists`, applied to `A` and `A^s` at `σ = ι ∘ alg`) and the five Props below.
`toC` is the comparison of `K̄`-points with complex points through `ι : K̄ → ℂ`. -/

open ZInQ.LeafPush2 (CPts cptObj IsUniformization)

/-- `Spec(ι) : Spec ℂ → Spec K̄` over `K`. -/
def embHom {K : Type} [Field K] (emb : AlgebraicClosure K →+* ℂ) :
    cptObj (emb.comp (algebraMap K (AlgebraicClosure K))) ⟶
      PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom emb)) (by
    simp only [cptObj, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- **Comparison of points through `ι` (proved to be a homomorphism):** `A(K̄) → A(ℂ)_{ι∘alg}`,
`P ↦ P ∘ Spec(ι)`. -/
def toC {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) :
    A.Pt (AlgebraicClosure K) →* CPts A (emb.comp (algebraMap K (AlgebraicClosure K))) where
  toFun P := embHom emb ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- **N1. Torsion comparison (GLUE, unproved; STANDARD).** `toC` is injective (`Spec ℂ → Spec K̄`
is faithfully flat, hence an epimorphism of schemes) and every `n`-torsion complex point
(`n ≥ 1`) comes from `A(K̄)`: `A(K̄)[n]` and `A(ℂ)[n]` both have `n^{2g}` elements (T5 over `K̄`
and over `ℂ`) and `toC` is injective. Equivalently, `A[n]` is finite étale in characteristic `0`
(Mumford §4, §6; UNVERIFIED numbers). -/
def ArtinTorsion : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (n : ℕ), 0 < n →
    Function.Injective (toC A emb) ∧
      ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))), Q ^ n = 1 →
        ∃ P, toC A emb P = Q

/-- **N4. Tate module of a uniformized abelian variety (GLUE, unproved; STANDARD).** For a
uniformization `Φ : ℂ^g → A(ℂ)_{ι∘alg}` with lattice `Λ` (T35), there is a `ℤ_ℓ`-isomorphism
`α : ℤ_ℓ ⊗ Λ ≅ T_ℓ(A)` with `toC (α(1 ⊗ λ))ₙ = Φ(ℓ⁻ⁿ λ)` for `λ ∈ Λ`. (The sequence
`Φ(ℓ⁻ⁿλ)` is compatible and `Φ(λ) = 1`; it comes from `A(K̄)` by N1; bijectivity is
`T_ℓ = lim Λ/ℓⁿΛ = Λ ⊗ ℤ_ℓ`, `Λ ≅ ℤ^{2g}`. Mumford §1, §4; this is Artin's comparison for
abelian varieties, SGA 4 XI 4.4; UNVERIFIED numbers.) The formula pins `α` and makes it natural
for homomorphisms and for `c_*` (by injectivity of `toC`). -/
def TateLattice : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ α : TensorProduct ℤ ℤ_[ℓ] Λ ≃ₗ[ℤ_[ℓ]] A.T ℓ,
      ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ))

/-- **N2. T11(a) in Hom form (textbook LEAF; Birkenhake–Lange, *Complex abelian varieties*,
Prop. 1.2.1, with holomorphy of algebraic morphisms; Mumford §1; UNVERIFIED numbers).** For
abelian varieties `A, B` over `K`, `σ : K → ℂ` and uniformizations `Φ_A, Φ_B` of `A(ℂ)_σ`,
`B(ℂ)_σ`, every homomorphism `f : A → B` lifts to a `ℂ`-linear map `M` with
`Φ_B(Mz) = f(Φ_A(z))`. (`T11a_RiemannEnd`'s second half is the case `A = B` over `ℂ`.) -/
def HomLinearLift : Prop :=
  ∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- `Spec(conj) : Spec ℂ → Spec ℂ`, over `K` from `σ ∘ s` to `σ`, when `σ ∘ s = conj ∘ σ`. -/
def conjHom {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : cptObj (σ.comp s) ⟶ cptObj σ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) (by
    simp only [cptObj, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

/-- Complex conjugation `A(ℂ)_σ → A(ℂ)_{σ∘s}` when `σ ∘ s = conj ∘ σ`: `Q ↦ Q ∘ Spec(conj)`. -/
def conjCs {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) : CPts A (σ.comp s) :=
  conjHom σ s h ≫ Q

/-- `(Over.map Spec(s)).obj (Spec ℂ via σ) ⟶ Spec ℂ via σ ∘ s` (the identity of `Spec ℂ`). -/
def mapPtIso {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K) :
    (Over.map (specS s)).obj (cptObj σ) ⟶ cptObj (σ.comp s) :=
  Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_hom, cptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- The map `A(ℂ)_σ → A^s(ℂ)_σ`, `Q ↦ Q ∘ Spec(conj)` read through `A^s(ℂ)_σ = A(ℂ)_{σ∘s}`
(adjunction `Over.map ⊣ Over.pullback`). -/
def twistC {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) : CPts (conjVar A s) σ :=
  (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjCs A σ s h Q)

/-- **N3. Complex conjugation is antiholomorphic (GLUE, unproved; STANDARD).** If
`σ ∘ s = conj ∘ σ`, then for uniformizations `Φ` of `A(ℂ)_σ` and `Φ'` of `A^s(ℂ)_σ` the map
`twistC` lifts to an injective `ℝ`-linear, `ℂ`-antilinear `N` (`N(iz) = −iN(z)`) with
`Φ'(Nz) = twistC(Φ z)`. (`z ↦ twistC(Φ(z̄))` is a holomorphic uniformization of
`A^s(ℂ)_σ = A(ℂ)_{conj∘σ}`; two uniformizations differ by a `ℂ`-linear isomorphism, BL 1.2.1.) -/
def ConjAntiLift : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) (Φ' : (Fin g → ℂ) → CPts (conjVar A s) σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ → IsUniformization σ Λ' Φ' →
    ∃ N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ z, N (Complex.I • z) = -(Complex.I • N z)) ∧
      Function.Injective N ∧ ∀ z, Φ' (N z) = twistC A σ s h (Φ z)

/-- **N5. Dimension of the conjugate (GLUE, unproved; STANDARD).** For a number field `K`, every
ring endomorphism `s` is an automorphism, so `Spec(s)` is an isomorphism and so is
`A^s → A`; Krull dimension is preserved. -/
def ConjVarDim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (s : K →+* K),
    (conjVar A s).dim = A.dim

/-- **`toC` intertwines `c_*` with `twistC` (proved):** `toC (c_* P) = twistC (toC P)` for
`σ = ι ∘ alg`, `ι ∘ cc = conj ∘ ι`. This is the identity `Spec(ι) ≫ Spec(cc) = Spec(conj) ≫ Spec(ι)`
read through the adjunction; it is the "`β⁻¹ c_* α = F ⊗ 1`" part of `ConjBettiComparison` at
the level of points. -/
theorem toC_conjPt {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K)
    (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ)
    (hι : ∀ x, emb (cc x) = starRingEnd ℂ (emb x))
    (h : (emb.comp (algebraMap K _)).comp s = (starRingEnd ℂ).comp (emb.comp (algebraMap K _)))
    (P : A.Pt (AlgebraicClosure K)) :
    toC (conjVar A s) emb (conjPt A s cc hs P) =
      twistC A (emb.comp (algebraMap K _)) s h (toC A emb P) := by
  change embHom emb ≫ (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P) =
    (Over.mapPullbackAdj (specS s)).homEquiv _ _
      (mapPtIso _ s ≫ conjCs A _ s h (embHom emb ≫ P))
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  simp only [conjCs, ← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom emb) ≫
      Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K)) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom emb)
  rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact hι x

/-! ## §7. Naturality of the comparison of N4 (proved from N1)

With N1, the formula of N4 pins `α`, and `α` is natural: for a homomorphism `f` with linear lift
`M` (N2), `T_ℓ(f) ∘ α_A = α_B ∘ (M ⊗ 1)` on `1 ⊗ Λ_A`; for `c_*` with antilinear lift `N` (N3),
`c_* ∘ α_A = α_{A^s} ∘ (N ⊗ 1)` on `1 ⊗ Λ_A`. These are the two compatibilities
`β⁻¹ V(f) α = φ ⊗ 1` and `β⁻¹ c_* α = F ⊗ 1` of `ConjBettiComparison`, before tensoring with `ℚ`
and `ℚ_ℓ`. -/

/-- The lattice point `λ` lies in the kernel of `Φ`, and a linear lift maps lattices to lattices:
`Φ_B(Mλ) = f(Φ_A(λ)) = f(1) = 1`. -/
theorem lift_mem_lattice {K : Type} [Field K] {A B : PkgI3.AbVar K} {σ : K →+* ℂ} {g h : ℕ}
    {ΛA : Submodule ℤ (Fin g → ℂ)} {ΛB : Submodule ℤ (Fin h → ℂ)}
    {ΦA : (Fin g → ℂ) → CPts A σ} {ΦB : (Fin h → ℂ) → CPts B σ}
    (hA : IsUniformization σ ΛA ΦA) (hB : IsUniformization σ ΛB ΦB) (f : PkgI3.AbVar.Hom A B)
    (M : (Fin g → ℂ) → (Fin h → ℂ)) (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (lam : ΛA) :
    M lam ∈ ΛB := by
  rw [← hB.2.1, hM, (hA.2.1 _).mpr lam.2]
  exact MonObj.one_comp f.hom

/-- **Naturality for homomorphisms (proved from N1).** -/
theorem homT_tateLattice (hN1 : ArtinTorsion) {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (emb : AlgebraicClosure K →+* ℂ) {g h : ℕ} {ΛA : Submodule ℤ (Fin g → ℂ)}
    {ΛB : Submodule ℤ (Fin h → ℂ)}
    {ΦA : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))}
    {ΦB : (Fin h → ℂ) → CPts B (emb.comp (algebraMap K (AlgebraicClosure K)))}
    (ℓ : ℕ) [Fact ℓ.Prime]
    (αA : TensorProduct ℤ ℤ_[ℓ] ΛA →ₗ[ℤ_[ℓ]] A.T ℓ)
    (hαA : ∀ (lam : ΛA) (n : ℕ), toC A emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n)) =
        ΦA (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (αB : TensorProduct ℤ ℤ_[ℓ] ΛB →ₗ[ℤ_[ℓ]] B.T ℓ)
    (hαB : ∀ (lam : ΛB) (n : ℕ), toC B emb (Additive.toMul ((αB (1 ⊗ₜ lam)).1 n)) =
        ΦB (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin h → ℂ)))
    (f : PkgI3.AbVar.Hom A B) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (lam : ΛA) (hlam : M lam ∈ ΛB) :
    PkgI3.AbVar.homT f (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ ⟨M lam, hlam⟩) := by
  apply Subtype.ext; funext n
  apply Additive.toMul.injective
  apply (hN1 K B emb 1 one_pos).1
  change toC B emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n) ≫ f.hom) = _
  rw [hαB]
  change embHom emb ≫ Additive.toMul ((αA (1 ⊗ₜ lam)).1 n) ≫ f.hom = _
  rw [← Category.assoc]
  change toC A emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n)) ≫ f.hom = _
  rw [hαA, ← hM, map_smul]

/-- **Naturality for `c_*` (proved from N1 and `toC_conjPt`).** -/
theorem conjT_tateLattice (hN1 : ArtinTorsion) {K : Type} [Field K] (A : PkgI3.AbVar K)
    (s : K →+* K) (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ)
    (hι : ∀ x, emb (cc x) = starRingEnd ℂ (emb x))
    (h : (emb.comp (algebraMap K _)).comp s = (starRingEnd ℂ).comp (emb.comp (algebraMap K _)))
    {g : ℕ} {Λ Λ' : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))}
    {Φ' : (Fin g → ℂ) → CPts (conjVar A s) (emb.comp (algebraMap K (AlgebraicClosure K)))}
    (ℓ : ℕ) [Fact ℓ.Prime]
    (α : TensorProduct ℤ ℤ_[ℓ] Λ →ₗ[ℤ_[ℓ]] A.T ℓ)
    (hα : ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (α' : TensorProduct ℤ ℤ_[ℓ] Λ' →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ)
    (hα' : ∀ (lam : Λ') (n : ℕ),
        toC (conjVar A s) emb (Additive.toMul ((α' (1 ⊗ₜ lam)).1 n)) =
        Φ' (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (hN : ∀ z, Φ' (N z) = twistC A (emb.comp (algebraMap K _)) s h (Φ z))
    (lam : Λ) (hlam : N lam ∈ Λ') :
    conjT A s cc hs ℓ (α (1 ⊗ₜ lam)) = α' (1 ⊗ₜ ⟨N lam, hlam⟩) := by
  apply Subtype.ext; funext n
  apply Additive.toMul.injective
  apply (hN1 K (conjVar A s) emb 1 one_pos).1
  change toC (conjVar A s) emb (conjPt A s cc hs (Additive.toMul ((α (1 ⊗ₜ lam)).1 n))) = _
  rw [hα', toC_conjPt A s cc hs emb hι h, hα, ← hN]
  congr 1
  have e : ∀ v : Fin g → ℂ, ((ℓ : ℂ) ^ n)⁻¹ • v = (((ℓ : ℝ) ^ n)⁻¹ : ℝ) • v := fun v => by
    ext i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast; rfl
  rw [e, e, map_smul]

/-! ## §8. The linear algebra of the lattice argument (proved)

The lattices replace the abstract `H` of `ConjBettiComparison`: with `ℤ`-bases of `Λ_A`, `Λ_B`,
the matrices of `c_*` and of `V_ℓ(f)` on `ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)` (through `ℚ_ℓ ⊗ α`, §10) are the
integer matrices of the lifts `N` and `M_f` on the lattices (§7). Faltings puts the first in the `ℚ_ℓ`-span of the others,
rationality (`matrix_mem_of_map_mem_span`) in their `ℚ`-span, so `N` is a `ℚ`-combination of
`ℂ`-linear maps on a basis of `ℂ^g` over `ℝ`, hence `ℂ`-linear; it is antilinear and nonzero. -/

section LatticeAlgebra

open Module

/-- **A lattice map determines the real-linear map (proved).** -/
theorem toLin_of_lattice {g : ℕ} {ΛA ΛB : Submodule ℤ (Fin g → ℂ)} {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    (bA : Basis ιA ℤ ΛA) (bB : Basis ιB ℤ ΛB) (bAℝ : Basis ιA ℝ (Fin g → ℂ))
    (bBℝ : Basis ιB ℝ (Fin g → ℂ)) (hbA : ∀ i, bAℝ i = bA i) (hbB : ∀ i, bBℝ i = bB i)
    (u : ΛA →ₗ[ℤ] ΛB) (Y : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (hu : ∀ lam, (u lam : Fin g → ℂ) = Y lam) :
    Matrix.toLin bAℝ bBℝ ((LinearMap.toMatrix bA bB u).map (Int.castRingHom ℝ)) = Y := by
  apply bAℝ.ext; intro j
  rw [Matrix.toLin_self, hbA j, ← hu]
  conv_rhs => rw [← bB.sum_repr (u (bA j))]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, hbB i, Submodule.coe_smul, eq_intCast,
    Int.cast_smul_eq_zsmul]

/-- **The lattice contradiction (proved).** If the integer matrix of an antilinear nonzero `N`
lies in the `E`-span (`E ⊇ ℚ`) of the integer matrices of `ℂ`-linear maps `M_f`, then `False`. -/
theorem lattice_contradiction {g : ℕ} {ΛA ΛB : Submodule ℤ (Fin g → ℂ)} {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    (bA : Basis ιA ℤ ΛA) (bB : Basis ιB ℤ ΛB) (bAℝ : Basis ιA ℝ (Fin g → ℂ))
    (bBℝ : Basis ιB ℝ (Fin g → ℂ)) (hbA : ∀ i, bAℝ i = bA i) (hbB : ∀ i, bBℝ i = bB i)
    (E : Type*) [Field E] [CharZero E] {S : Type*} (uM : S → (ΛA →ₗ[ℤ] ΛB))
    (M : S → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (hM : ∀ f lam, (uM f lam : Fin g → ℂ) = M f lam)
    (uN : ΛA →ₗ[ℤ] ΛB) (N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (hN : ∀ lam, (uN lam : Fin g → ℂ) = N lam)
    (hanti : ∀ z, N (Complex.I • z) = -(Complex.I • N z)) (hN0 : N ≠ 0)
    (hspan : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom E) ∈ Submodule.span E
      (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom E))) :
    False := by
  let W : Submodule ℚ (Matrix ιB ιA ℚ) := Submodule.span ℚ
    (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom ℚ))
  have hmapE : ∀ X : Matrix ιB ιA ℤ,
      (X.map (Int.castRingHom ℚ)).map (algebraMap ℚ E) = X.map (Int.castRingHom E) := by
    intro X; rw [Matrix.map_map]; congr 1; ext x; simp
  have hmapR : ∀ X : Matrix ιB ιA ℤ,
      (X.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) = X.map (Int.castRingHom ℝ) := by
    intro X; rw [Matrix.map_map]; congr 1
  have hXN : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom ℚ) ∈ W := by
    apply matrix_mem_of_map_mem_span (E := E)
    rw [hmapE]
    refine Submodule.span_mono ?_ hspan
    rintro _ ⟨f, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨f, rfl⟩, hmapE _⟩
  have hP : ∀ X ∈ W, ∀ z, Matrix.toLin bAℝ bBℝ (X.map (algebraMap ℚ ℝ)) (Complex.I • z) =
      Complex.I • Matrix.toLin bAℝ bBℝ (X.map (algebraMap ℚ ℝ)) z := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      intro z
      rw [hmapR, toLin_of_lattice bA bB bAℝ bBℝ hbA hbB (uM f) ((M f).restrictScalars ℝ)
        (hM f)]
      exact (M f).map_smul Complex.I z
    | zero => intro z; simp
    | add x y _ _ hx hy =>
      intro z
      have e : (x + y).map (algebraMap ℚ ℝ) = x.map (algebraMap ℚ ℝ) + y.map (algebraMap ℚ ℝ) :=
        Matrix.map_add _ (map_add _) x y
      rw [e, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy, smul_add]
    | smul q x _ hx =>
      intro z
      have e : (q • x).map (algebraMap ℚ ℝ) = (q : ℝ) • x.map (algebraMap ℚ ℝ) := by
        ext i j; simp [Matrix.map_apply, Algebra.smul_def]
      rw [e, LinearEquiv.map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hx, smul_comm]
  have hNlin := hP _ hXN
  rw [hmapR, toLin_of_lattice bA bB bAℝ bBℝ hbA hbB uN N hN] at hNlin
  apply hN0
  apply LinearMap.ext; intro z
  have h1 : Complex.I • N z = -(Complex.I • N z) := (hNlin z).symm.trans (hanti z)
  have h2 : Complex.I • N z = 0 := by
    have : (2 : ℂ) • (Complex.I • N z) = 0 := by
      rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.mp h2).resolve_left Complex.I_ne_zero

end LatticeAlgebra

/-- `twistC` maps `1` to `1` (proved). -/
theorem twistC_one {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : twistC A σ s h 1 = 1 := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ 1) = 1
  rw [MonObj.comp_one, MonObj.comp_one, Adjunction.homEquiv_unit, Functor.map_one,
    MonObj.comp_one]
  rfl

/-! ## §9. N5 `ConjVarDim` (proved) -/

/-- A ring endomorphism of a number field is bijective. -/
theorem ringHom_bijective_of_numberField (K : Type) [Field K] [NumberField K] (s : K →+* K) :
    Function.Bijective s := by
  have hinj : Function.Injective s := s.injective
  refine ⟨hinj, ?_⟩
  have h := (LinearMap.injective_iff_surjective (f := s.toRatAlgHom.toLinearMap)).mp hinj
  exact h

/-- **N5 (proved).** For a number field, `dim A^s = dim A`: `Spec(s)` is an isomorphism, so the
projection `A^s → A` is an isomorphism of schemes, hence a homeomorphism. -/
theorem conjVarDim : ConjVarDim := by
  intro K _ _ A s
  have hb := ringHom_bijective_of_numberField K s
  let e : K ≃+* K := RingEquiv.ofBijective s hb
  haveI : IsIso (CommRingCat.ofHom s) :=
    ⟨⟨CommRingCat.ofHom (e.symm : K →+* K), by ext x; exact e.symm_apply_apply x,
      by ext x; exact e.apply_symm_apply x⟩⟩
  have : IsIso (specS s) := by unfold specS; infer_instance
  change topologicalKrullDim (conjVar A s).X.left = topologicalKrullDim A.X.left
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph (Limits.pullback.fst A.X.hom (specS s))).isHomeomorph

/-! ## §9b. N3 from N2 and a smaller glue N3a (proved reduction)

`ConjAntiLiftLat` is N3 for number fields and full lattices (all that §10 uses). It follows from
N2 (`HomLinearLift` for the identity of `A^s`) and N3a (`ConjUniformization`): the conjugate
`z ↦ twistC(Φ z̄)` of a uniformization of `A(ℂ)_σ` is a uniformization of `A^s(ℂ)_σ`. -/

/-- Complex conjugation on `ℂ^g`, as an `ℝ`-linear map. -/
def conjL (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun z i := starRingEnd ℂ (z i)
  map_add' z w := by funext i; simp
  map_smul' r z := by funext i; simp

theorem conjL_conjL {g : ℕ} (z : Fin g → ℂ) : conjL g (conjL g z) = z := by
  funext i; simp [conjL]

theorem conjL_I {g : ℕ} (z : Fin g → ℂ) :
    conjL g (Complex.I • z) = -(Complex.I • conjL g z) := by
  funext i; simp [conjL]

/-- **N3a. The conjugate of a uniformization (GLUE, unproved; STANDARD).** If `σ ∘ s = conj ∘ σ`
and `Φ` uniformizes `A(ℂ)_σ` with kernel `Λ`, then `z ↦ twistC(Φ(z̄))` uniformizes `A^s(ℂ)_σ`
with kernel `Λ̄ = {z | z̄ ∈ Λ}`. (`A^s(ℂ)_σ = A(ℂ)_{σ∘s} = A(ℂ)_{conj∘σ}`, and on affine charts
`twistC` conjugates the values of regular functions, so `z ↦ s(twistC(Φ z̄)) = conj(s'(Φ z))`-type
compositions are holomorphic; the group-theoretic clauses follow from `twistC` being a bijective
homomorphism.) -/
def ConjUniformization : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    IsUniformization σ (Λ.comap ((conjL g).restrictScalars ℤ))
      (fun z => twistC A σ s h (Φ (conjL g z)))

/-- **N3 for number fields and full lattices (GLUE; implied by `ConjAntiLift`).** -/
def ConjAntiLiftLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) (Φ' : (Fin g → ℂ) → CPts (conjVar A s) σ),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization σ Λ Φ → IsUniformization σ Λ' Φ' →
    ∃ N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ z, N (Complex.I • z) = -(Complex.I • N z)) ∧
      Function.Injective N ∧ ∀ z, Φ' (N z) = twistC A σ s h (Φ z)

theorem conjAntiLiftLat_of_conjAntiLift (h : ConjAntiLift) : ConjAntiLiftLat :=
  fun K _ _ A σ s hs g Λ Λ' Φ Φ' hd _ _ hΦ hΦ' => h K A σ s hs g Λ Λ' Φ Φ' hd hΦ hΦ'

/-- `Spec(conj)` back from `σ` to `σ ∘ s`. -/
def conjHomInv {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : cptObj σ ⟶ cptObj (σ.comp s) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) (by
    simp only [cptObj, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    congr 2
    ext x
    simp)

/-- The inverse of `mapPtIso`. -/
def mapPtIsoInv {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K) :
    cptObj (σ.comp s) ⟶ (Over.map (specS s)).obj (cptObj σ) :=
  Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_hom, cptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

theorem twistC_inj_aux {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) :
    conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
    Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) = 𝟙 _
  rw [Category.id_comp, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

/-- `twistC` is injective (proved). -/
theorem twistC_injective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : Function.Injective (twistC A σ s h) := by
  intro Q Q' hQ
  have h1 : mapPtIso σ s ≫ conjHom σ s h ≫ Q = mapPtIso σ s ≫ conjHom σ s h ≫ Q' :=
    ((Over.mapPullbackAdj (specS s)).homEquiv _ _).injective hQ
  calc Q = (conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h) ≫ Q := by
        rw [twistC_inj_aux, Category.id_comp]
    _ = conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ (mapPtIso σ s ≫ conjHom σ s h ≫ Q) := by
        simp only [Category.assoc]
    _ = conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ (mapPtIso σ s ≫ conjHom σ s h ≫ Q') := by
        rw [h1]
    _ = (conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h) ≫ Q' := by
        simp only [Category.assoc]
    _ = Q' := by rw [twistC_inj_aux, Category.id_comp]

/-- A vector all of whose real multiples lie in a full lattice is `0` (proved). -/
theorem eq_zero_of_real_smul_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (z : Fin g → ℂ) (hz : ∀ t : ℝ, t • z ∈ Λ) : z = 0 := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let bℝ := b.ofZLatticeBasis ℝ Λ
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, bℝ.repr z j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (bℝ.repr.injective (Finsupp.ext fun j => by simp [hall j]))
  have hmem := hz (2 * bℝ.repr z j)⁻¹
  have e1 : bℝ.repr ((2 * bℝ.repr z j)⁻¹ • z) j = 1 / 2 := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    field_simp
  have e2 : bℝ.repr ((2 * bℝ.repr z j)⁻¹ • z) j = (b.repr ⟨_, hmem⟩ j : ℝ) :=
    Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b ⟨_, hmem⟩ j
  rw [e1] at e2
  have : (2 : ℝ) * (b.repr ⟨_, hmem⟩ j : ℝ) = 1 := by rw [← e2]; norm_num
  have h3 : (2 * b.repr ⟨_, hmem⟩ j : ℤ) = 1 := by exact_mod_cast this
  omega

/-- **`ConjAntiLiftLat` from N2 and N3a (proved).** -/
theorem conjAntiLiftLat_of (hN2 : HomLinearLift) (hN3a : ConjUniformization) :
    ConjAntiLiftLat := by
  intro K _ _ A σ s h g Λ Λ' Φ Φ' hd _ hlat hΦ hΦ'
  have hd' : (conjVar A s).dim = (g : WithBot ℕ∞) := by rw [conjVarDim]; exact hd
  have hψ := hN3a K A σ s h g Λ Φ hd hΦ
  obtain ⟨M, hM⟩ := hN2 K (conjVar A s) (conjVar A s) σ g g _ Λ' _ Φ' hd' hd' hψ hΦ' 1
  have hM' : ∀ z, Φ' (M z) = twistC A σ s h (Φ (conjL g z)) := fun z => by
    rw [hM z]; exact Category.comp_id _
  refine ⟨(M.restrictScalars ℝ) ∘ₗ conjL g, fun z => ?_, ?_, fun z => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [conjL_I, map_neg, M.map_smul]
  · intro z w hzw
    have key : ∀ v, M (conjL g v) = 0 → v = 0 := by
      intro v hv
      apply eq_zero_of_real_smul_mem Λ v
      intro t
      rw [← hΦ.2.1]
      apply twistC_injective A σ s h
      rw [twistC_one, ← conjL_conjL (t • v), ← hM', map_smul, ← Complex.coe_smul,
        M.map_smul, hv, smul_zero]
      exact (hΦ'.2.1 0).mpr (Submodule.zero_mem _)
    have : M (conjL g (z - w)) = 0 := by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars] at hzw
      rw [map_sub, map_sub, hzw, sub_self]
    exact sub_eq_zero.mp (key _ this)
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [hM', conjL_conjL]

/-! ## §10. A weaker N4 suffices: an injective comparison (proved reduction)

Only injectivity of `α` is used: `ℚ_ℓ` is flat over `ℤ_ℓ`, so `ι = ℚ_ℓ ⊗ α` is injective, and
postcomposition with `ι_B` is injective on `Hom` spaces. The matrices are then taken on
`ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)`, where `c_*` and `V_ℓ(f)` become the base changes of `N|_Λ` and `M_f|_Λ`. -/

/-- **N4' (GLUE; weaker than `TateLattice`).** As `TateLattice` with `α` only an injective
`ℤ_ℓ`-linear map. -/
def TateLatticeInj : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ α : TensorProduct ℤ ℤ_[ℓ] Λ →ₗ[ℤ_[ℓ]] A.T ℓ,
      Function.Injective α ∧
      ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ))

theorem tateLatticeInj_of_tateLattice (h : TateLattice) : TateLatticeInj := by
  intro K _ A emb g Λ Φ hd _ hlat hΦ ℓ _
  obtain ⟨α, hα⟩ := h K A emb g Λ Φ hd hlat hΦ ℓ
  exact ⟨α.toLinearMap, α.injective, hα⟩

/-- **`ConjTwistNontrivial` from T26, T35, N1, N2, N3 and N4' (proved).** -/
theorem conjTwistNontrivial_of_latticeInj (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLiftLat) (hN4 : TateLatticeInj) : ConjTwistNontrivial := by
  classical
  intro hF K _ _ _ A ℓ _ hdim c hc hall
  obtain ⟨cc, emb, hι, hK, h2, hres⟩ := conjData K c hc
  let s := restrictK cc hK
  have hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k) := restrictK_spec cc hK
  let σ : K →+* ℂ := emb.comp (algebraMap K (AlgebraicClosure K))
  have hσs : σ.comp s = (starRingEnd ℂ).comp σ := by
    apply RingHom.ext; intro k
    change emb (algebraMap K _ (s k)) = starRingEnd ℂ (emb (algebraMap K _ k))
    rw [← hs, hι]
  have hd2 : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hd2' : (conjVar A s).dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [conjVarDim]; exact hd2
  obtain ⟨ΛA, ΦA, hdA, hlatA, hA⟩ := h35 K A σ 2 hd2
  obtain ⟨ΛB, ΦB, hdB, hlatB, hB⟩ := h35 K (conjVar A s) σ 2 hd2'
  obtain ⟨N, hNanti, hNinj, hN⟩ := hN3 K A σ s hσs 2 ΛA ΛB ΦA ΦB hd2 hlatA hA hB
  obtain ⟨αA, -, hαA⟩ := hN4 K A emb 2 ΛA ΦA hd2 hlatA hA ℓ
  obtain ⟨αB, hαBinj, hαB⟩ := hN4 K (conjVar A s) emb 2 ΛB ΦB hd2' hlatB hB ℓ
  choose M hM using fun f => hN2 K A (conjVar A s) σ 2 2 ΛA ΛB ΦA ΦB hd2 hd2' hA hB f
  have heq : ∀ τ, conjV A s cc hs ℓ ∘ₗ A.galRep ℓ τ =
      (conjVar A s).galRep ℓ τ ∘ₗ conjV A s cc hs ℓ := by
    intro τ
    obtain ⟨σ', hσ'⟩ := exists_twist K cc hK h2 τ
    rw [hall σ' τ (hres σ' τ hσ'), conjV_galRep A s cc hs ℓ σ' τ hσ']
  have hspan := faltingsV hF hT A (conjVar A s) ℓ _ heq
  have hNlat : ∀ lam : ΛA, N lam ∈ ΛB := fun lam => by
    rw [← hB.2.1, hN, (hA.2.1 _).mpr lam.2]
    exact twistC_one A σ s hσs
  have hMlat : ∀ f (lam : ΛA), M f lam ∈ ΛB := fun f lam =>
    lift_mem_lattice hA hB f (M f) (hM f) lam
  let uN : ΛA →ₗ[ℤ] ΛB :=
    { toFun := fun lam => ⟨N lam, hNlat lam⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by
        simp only [RingHom.id_apply, Submodule.coe_smul]; exact map_zsmul N n _) }
  let uM : PkgI3.AbVar.Hom A (conjVar A s) → (ΛA →ₗ[ℤ] ΛB) := fun f =>
    { toFun := fun lam => ⟨M f lam, hMlat f lam⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by
        simp only [RingHom.id_apply, Submodule.coe_smul]; exact map_zsmul (M f) n _) }
  have hCN : ∀ lam, conjT A s cc hs ℓ (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ uN lam) := fun lam =>
    conjT_tateLattice hN1 A s cc hs emb hι hσs ℓ αA hαA αB hαB N hN lam (hNlat lam)
  have hMf : ∀ f lam, PkgI3.AbVar.homT f (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ uM f lam) :=
    fun f lam => homT_tateLattice hN1 emb ℓ αA hαA αB hαB f (M f) (hM f) lam (hMlat f lam)
  -- `ℚ_ℓ ⊗ α`
  let ιA := αA.baseChange ℚ_[ℓ]
  let ιB := αB.baseChange ℚ_[ℓ]
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  have hιB : Function.Injective ιB := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ_[ℓ]) αB hαBinj
    rwa [← LinearMap.baseChange_eq_lTensor] at this
  let lift : (ΛA →ₗ[ℤ] ΛB) → (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛB)) := fun u => (u.baseChange ℤ_[ℓ]).baseChange ℚ_[ℓ]
  have hcomp : ∀ (Tm : A.T ℓ →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ) (u : ΛA →ₗ[ℤ] ΛB),
      (∀ lam, Tm (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ u lam)) →
      Tm.baseChange ℚ_[ℓ] ∘ₗ ιA = ιB ∘ₗ lift u := by
    intro Tm u h
    simp only [ιA, ιB, lift, ← LinearMap.baseChange_comp]
    congr 1
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    apply LinearMap.ext
    intro lam
    change Tm (αA (1 ⊗ₜ lam)) = αB ((u.baseChange ℤ_[ℓ]) (1 ⊗ₜ lam))
    rw [h, LinearMap.baseChange_tmul]
  let Pre : (A.V ℓ →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) →ₗ[ℚ_[ℓ]]
      (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) :=
    { toFun := fun X => X ∘ₗ ιA
      map_add' := fun X Y => LinearMap.add_comp _ _ _
      map_smul' := fun a X => LinearMap.smul_comp _ _ _ }
  let Post : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛB)) →ₗ[ℚ_[ℓ]]
      (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) :=
    { toFun := fun Y => ιB ∘ₗ Y
      map_add' := fun X Y => LinearMap.comp_add _ _ _
      map_smul' := fun a X => LinearMap.comp_smul _ _ _ }
  have hPost : Function.Injective Post := fun Y Y' h =>
    LinearMap.ext fun x => hιB (LinearMap.congr_fun h x)
  have key : lift uN ∈ Submodule.span ℚ_[ℓ] (Set.range fun f => lift (uM f)) := by
    have h1 := Submodule.mem_map_of_mem (f := Pre) hspan
    rw [homSpanV, Submodule.map_span, ← Set.range_comp] at h1
    have e1 : (⇑Pre ∘ fun f : PkgI3.AbVar.Hom A (conjVar A s) =>
        (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ]) = ⇑Post ∘ fun f => lift (uM f) := by
      funext f
      exact hcomp _ _ (hMf f)
    have e2 : Pre (conjV A s cc hs ℓ) = Post (lift uN) := hcomp _ _ hCN
    rw [e1, Set.range_comp, ← Submodule.map_span, e2] at h1
    obtain ⟨y, hy, hyN⟩ := h1
    rwa [hPost hyN] at hy
  -- bases and matrices
  haveI := ZLattice.module_finite ℝ ΛA
  haveI := ZLattice.module_free ℝ ΛA
  haveI := ZLattice.module_finite ℝ ΛB
  haveI := ZLattice.module_free ℝ ΛB
  let bA := Module.Free.chooseBasis ℤ ΛA
  let bB := Module.Free.chooseBasis ℤ ΛB
  let bAℝ := bA.ofZLatticeBasis ℝ ΛA
  let bBℝ := bB.ofZLatticeBasis ℝ ΛB
  let TM := LinearMap.toMatrix (Algebra.TensorProduct.basis ℚ_[ℓ]
      (Algebra.TensorProduct.basis ℤ_[ℓ] bA))
    (Algebra.TensorProduct.basis ℚ_[ℓ] (Algebra.TensorProduct.basis ℤ_[ℓ] bB))
  have hTM : ∀ u, TM (lift u) = (LinearMap.toMatrix bA bB u).map (Int.castRingHom ℚ_[ℓ]) := by
    intro u
    simp only [TM, lift, LinearMap.toMatrix_baseChange, Matrix.map_map]
    congr 1
  have hspan' : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom ℚ_[ℓ]) ∈
      Submodule.span ℚ_[ℓ]
        (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom ℚ_[ℓ])) := by
    have h1 := Submodule.mem_map_of_mem (f := TM.toLinearMap) key
    rw [Submodule.map_span, ← Set.range_comp] at h1
    rw [← hTM]
    convert h1 using 3
    funext f
    exact (hTM (uM f)).symm
  have hN0 : N ≠ 0 := by
    intro h0
    have : (Pi.single 0 1 : Fin 2 → ℂ) = 0 := hNinj (by rw [h0]; simp)
    have := congrFun this 0
    simp at this
  exact lattice_contradiction bA bB bAℝ bBℝ (fun i => by simp [bAℝ]) (fun i => by simp [bBℝ])
    ℚ_[ℓ] uM M (fun f lam => rfl) uN N (fun lam => rfl) hNanti hN0 hspan'

/-- **`ConjTwistNontrivial` from T26, T35, N1, N2, N3 and N4 (proved; N5 is proved).** -/
theorem conjTwistNontrivial_of_lattice (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLattice) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN1 hN2 (conjAntiLiftLat_of_conjAntiLift hN3)
    (tateLatticeInj_of_tateLattice hN4)

/-- **`ConjTwistFromLeaves` from N1, N2, N3, N4' (proved):** T35 and T26 are among its
hypotheses. -/
theorem conjTwistFromLeaves_of_latticeInj (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLatticeInj) : ConjTwistFromLeaves :=
  fun _ _ h35 _ hT => conjTwistNontrivial_of_latticeInj hT h35 hN1 hN2
    (conjAntiLiftLat_of_conjAntiLift hN3) hN4

/-- **`ConjTwistFromLeaves` from N1, N2, N3, N4 (proved).** -/
theorem conjTwistFromLeaves_of_lattice (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLattice) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_latticeInj hN1 hN2 hN3 (tateLatticeInj_of_tateLattice hN4)

/-! ## §11. N4' from N1 (proved): the injective comparison `ℤ_ℓ ⊗ Λ → T_ℓ(A)`

`x(λ)ₙ` is the unique `K̄`-point with `toC(x(λ)ₙ) = Φ(ℓ⁻ⁿλ)` (N1); `λ ↦ x(λ)` is additive, and its
`ℤ_ℓ`-linear extension is injective: if `Σ aᵢ x(bᵢ) = 0`, then `Φ(ℓ⁻ⁿ Σ (aᵢ mod ℓⁿ) bᵢ) = 1`, so
`Σ (aᵢ mod ℓⁿ) bᵢ ∈ ℓⁿΛ` and `ℓⁿ ∣ (aᵢ mod ℓⁿ)`, for every `n`. -/

section TateLatticeProof

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) {g : ℕ}
  (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))

theorem phi_zero (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  have := congrArg (fun x => (Φ 0)⁻¹ * x) h
  simp only [inv_mul_cancel, inv_mul_cancel_left] at this
  exact this.symm

theorem phi_nsmul (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (k : ℕ) (z : Fin g → ℂ) :
    Φ (k • z) = Φ z ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero, phi_zero A emb Φ hadd]
  | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem phi_sum (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) {J : Type*} (s : Finset J)
    (f : J → (Fin g → ℂ)) : Φ (∑ i ∈ s, f i) = ∏ i ∈ s, Φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phi_zero A emb Φ hadd]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem ell_ne_zero : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.out.ne_zero

theorem smul_inv_pow (n : ℕ) (v : Fin g → ℂ) : (ℓ ^ n : ℕ) • (((ℓ : ℂ) ^ n)⁻¹ • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  push_cast
  rw [mul_inv_cancel₀ (pow_ne_zero _ (ell_ne_zero ℓ)), one_smul]

theorem smul_inv_succ (n : ℕ) (v : Fin g → ℂ) :
    ℓ • (((ℓ : ℂ) ^ (n + 1))⁻¹ • v) = ((ℓ : ℂ) ^ n)⁻¹ • v := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have := ell_ne_zero ℓ
  field_simp
  ring

variable {Λ : Submodule ℤ (Fin g → ℂ)}
  (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)

include hadd hker in
theorem phi_tors (lam : Λ) (n : ℕ) : Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) ^ (ℓ ^ n) = 1 := by
  rw [← phi_nsmul A emb Φ hadd, smul_inv_pow, (hker _).mpr lam.2]

variable (hN1 : ArtinTorsion)

/-- `x(λ)ₙ ∈ A(K̄)` with `toC(x(λ)ₙ) = Φ(ℓ⁻ⁿλ)`. -/
def xPt (lam : Λ) (n : ℕ) : A.Pt (AlgebraicClosure K) :=
  Classical.choose ((hN1 K A emb (ℓ ^ n) (pow_pos hℓ.out.pos n)).2 _
    (phi_tors A emb Φ ℓ hadd hker lam n))

theorem xPt_spec (lam : Λ) (n : ℕ) :
    toC A emb (xPt A emb Φ ℓ hadd hker hN1 lam n) = Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) :=
  Classical.choose_spec ((hN1 K A emb (ℓ ^ n) (pow_pos hℓ.out.pos n)).2 _
    (phi_tors A emb Φ ℓ hadd hker lam n))

/-- `x(λ) ∈ T_ℓ(A)`. -/
def xSeq (lam : Λ) : A.T ℓ :=
  ⟨fun n => Additive.ofMul (xPt A emb Φ ℓ hadd hker hN1 lam n), by
    refine ⟨?_, fun n => ?_⟩
    · apply Additive.toMul.injective
      change xPt A emb Φ ℓ hadd hker hN1 lam 0 = 1
      apply (hN1 K A emb 1 one_pos).1
      rw [xPt_spec, map_one, pow_zero, inv_one, one_smul]
      exact (hker _).mpr lam.2
    · apply Additive.toMul.injective
      change xPt A emb Φ ℓ hadd hker hN1 lam (n + 1) ^ ℓ = xPt A emb Φ ℓ hadd hker hN1 lam n
      apply (hN1 K A emb 1 one_pos).1
      rw [map_pow, xPt_spec, xPt_spec, ← phi_nsmul A emb Φ hadd, smul_inv_succ]⟩

theorem xSeq_apply (lam : Λ) (n : ℕ) :
    toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hN1 lam).1 n)) =
      Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) :=
  xPt_spec A emb Φ ℓ hadd hker hN1 lam n

/-- `λ ↦ x(λ)`, additive. -/
def xHom : Λ →+ A.T ℓ :=
  AddMonoidHom.mk' (xSeq A emb Φ ℓ hadd hker hN1) (fun a b => by
    apply Subtype.ext; funext n
    apply Additive.toMul.injective
    apply (hN1 K A emb 1 one_pos).1
    change toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hN1 (a + b)).1 n)) =
      toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hN1 a).1 n) *
        Additive.toMul ((xSeq A emb Φ ℓ hadd hker hN1 b).1 n))
    rw [map_mul, xSeq_apply, xSeq_apply, xSeq_apply, ← hadd, Submodule.coe_add, smul_add])

/-- `λ ↦ x(λ)`, `ℤ`-linear. -/
def xLin : Λ →ₗ[ℤ] A.T ℓ :=
  { xHom A emb Φ ℓ hadd hker hN1 with
    map_smul' := fun n x => by
      simp only [RingHom.id_apply]
      exact map_zsmul (xHom A emb Φ ℓ hadd hker hN1) n x }

end TateLatticeProof

section TateLatticeInjProof

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) {g : ℕ}
  (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {Λ : Submodule ℤ (Fin g → ℂ)}
  (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ) (hN1 : ArtinTorsion)

/-- **Injectivity of the comparison (proved from N1).** -/
theorem xLin_liftBaseChange_injective [Module.Free ℤ Λ] [Module.Finite ℤ Λ] :
    Function.Injective ((xLin A emb Φ ℓ hadd hker hN1).liftBaseChange ℤ_[ℓ]) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let bZ := Algebra.TensorProduct.basis ℤ_[ℓ] b
  set α := (xLin A emb Φ ℓ hadd hker hN1).liftBaseChange ℤ_[ℓ] with hαdef
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  apply bZ.repr.injective
  refine Finsupp.ext fun j => ?_
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [map_zero]
  set a : Module.Free.ChooseBasisIndex ℤ Λ → ℤ_[ℓ] := fun i => bZ.repr v i with ha
  set k : Module.Free.ChooseBasisIndex ℤ Λ → ℕ := fun i => (PadicInt.toZModPow n (a i)).val
    with hk
  have hαv : α v = ∑ i, a i • xLin A emb Φ ℓ hadd hker hN1 (b i) := by
    conv_lhs => rw [← bZ.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.TensorProduct.basis_apply, hαdef, LinearMap.liftBaseChange_one_tmul]
  have hent : Additive.toMul ((α v).1 n) =
      ∏ i, Additive.toMul ((xLin A emb Φ ℓ hadd hker hN1 (b i)).1 n) ^ k i := by
    rw [hαv, AddSubgroup.val_finset_sum, Finset.sum_apply, toMul_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [PkgI3.Tate.smul_apply, toMul_nsmul]
  have h0 : Additive.toMul ((α v).1 n) = 1 := by rw [hv]; rfl
  let w : Λ := ∑ i, k i • b i
  have hC : Φ (((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ)) = 1 := by
    have e1 : toC A emb (Additive.toMul ((α v).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ)) := by
      rw [hent, map_prod]
      simp only [map_pow]
      have e2 : ∀ i, toC A emb (Additive.toMul ((xLin A emb Φ ℓ hadd hker hN1 (b i)).1 n)) =
          Φ (((ℓ : ℂ) ^ n)⁻¹ • ((b i : Λ) : Fin g → ℂ)) := fun i =>
        xSeq_apply A emb Φ ℓ hadd hker hN1 (b i) n
      simp only [e2, ← phi_nsmul A emb Φ hadd]
      rw [← phi_sum A emb Φ hadd]
      congr 1
      simp only [w, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
    rw [← e1, h0, map_one]
  have hw : ((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ) ∈ Λ := (hker _).mp hC
  let mu : Λ := ⟨((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ), hw⟩
  have hwμ : w = (ℓ ^ n : ℕ) • mu := by
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower]
    exact (smul_inv_pow ℓ n (w : Fin g → ℂ)).symm
  have hrepr := congrArg (fun x => b.repr x j) hwμ
  simp only [w, map_sum, map_nsmul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hrepr
  have hdvd : (ℓ ^ n : ℕ) ∣ k j := by
    have h1 : ((ℓ ^ n : ℕ) : ℤ) ∣ ((k j : ℕ) : ℤ) := by
      refine ⟨b.repr mu j, ?_⟩
      simpa [nsmul_eq_mul] using hrepr
    exact Int.natCast_dvd_natCast.mp h1
  have hlt : k j < ℓ ^ n := ZMod.val_lt _
  exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hdvd hlt)

end TateLatticeInjProof

/-- **N4' from N1 (proved).** -/
theorem tateLatticeInj_of_artinTorsion (hN1 : ArtinTorsion) : TateLatticeInj := by
  intro K _ A emb g Λ Φ _ _ hlat hΦ ℓ _
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  refine ⟨(xLin A emb Φ ℓ hΦ.1 hΦ.2.1 hN1).liftBaseChange ℤ_[ℓ],
    xLin_liftBaseChange_injective A emb Φ ℓ hΦ.1 hΦ.2.1 hN1, fun lam n => ?_⟩
  rw [LinearMap.liftBaseChange_one_tmul]
  exact xSeq_apply A emb Φ ℓ hΦ.1 hΦ.2.1 hN1 lam n

/-- **`ConjTwistNontrivial` from T26, T35, N1, N2, N3 (proved).** -/
theorem conjTwistNontrivial_of_N123 (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN1 hN2 (conjAntiLiftLat_of_conjAntiLift hN3)
    (tateLatticeInj_of_artinTorsion hN1)

/-- **`ConjTwistFromLeaves` from N1, N2, N3 (proved).** -/
theorem conjTwistFromLeaves_of_N123 (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_latticeInj hN1 hN2 hN3 (tateLatticeInj_of_artinTorsion hN1)

/-! ## §12. The injectivity half of N1 (proved)

`Spec ℂ → Spec K̄` is surjective, hence dominant, `Spec K̄` is reduced and `A → Spec K` is
separated (proper), so two `K̄`-points agreeing after `Spec ℂ → Spec K̄` are equal (Mathlib's
`ext_of_isDominant_of_isSeparated`). What remains of N1 is the torsion surjectivity. -/

/-- **`toC` is injective (proved).** -/
theorem toC_injective {K : Type} [Field K] (A : PkgI3.AbVar K)
    (emb : AlgebraicClosure K →+* ℂ) : Function.Injective (toC A emb) := by
  intro P P' h
  apply Over.OverMorphism.ext
  have hU : Spec.map (CommRingCat.ofHom emb) ≫ P.left =
      Spec.map (CommRingCat.ofHom emb) ≫ P'.left := by
    have := congrArg CommaMorphism.left h
    exact this
  haveI : IsReduced (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).left := by
    change IsReduced (Spec (CommRingCat.of (AlgebraicClosure K))); infer_instance
  have h0 : Surjective (Spec.map (CommRingCat.ofHom emb)) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint ℂ, Subsingleton.elim _ _⟩⟩
  let ι' : Spec (CommRingCat.of ℂ) ⟶ (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).left :=
    Spec.map (CommRingCat.ofHom emb)
  haveI : Surjective ι' := h0
  exact ext_of_isDominant_of_isSeparated A.X.hom (by rw [Over.w P, Over.w P']) ι' hU

/-- **N1-surj. Torsion comparison, surjectivity (GLUE, unproved; STANDARD).** Every `n`-torsion
point of `A(ℂ)_{ι∘alg}` (`n ≥ 1`) comes from `A(K̄)`. (`toC` is injective, `toC_injective`; both
`A(K̄)[n]` and `A(ℂ)[n]` have `n^{2g}` elements, by T5 over `K̄` and over `ℂ`; equivalently `A[n]`
is finite étale in characteristic `0`. Mumford §4, §6, UNVERIFIED numbers.) -/
def ArtinTorsionSurj : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (n : ℕ), 0 < n →
    ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))), Q ^ n = 1 →
      ∃ P, toC A emb P = Q

theorem artinTorsion_of_surj (h : ArtinTorsionSurj) : ArtinTorsion :=
  fun K _ A emb n hn => ⟨toC_injective A emb, h K A emb n hn⟩

/-- **`ConjTwistNontrivial` from T26, T35, N1-surj, N2, N3 (proved).** -/
theorem conjTwistNontrivial_of_surj (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_N123 hT h35 (artinTorsion_of_surj hS) hN2 hN3

/-- **`ConjTwistFromLeaves` from N1-surj, N2, N3 (proved).** -/
theorem conjTwistFromLeaves_of_surj (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_N123 (artinTorsion_of_surj hS) hN2 hN3

/-- **Main result: `ConjTwistNontrivial` from T26, T35, N1-surj, N2 and N3a (proved).** -/
theorem conjTwistNontrivial_main (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3a : ConjUniformization) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 (artinTorsion_of_surj hS) hN2
    (conjAntiLiftLat_of hN2 hN3a) (tateLatticeInj_of_artinTorsion (artinTorsion_of_surj hS))

/-- **Main result: `ConjTwistFromLeaves` from N1-surj, N2 and N3a (proved).** -/
theorem conjTwistFromLeaves_main (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3a : ConjUniformization) : ConjTwistFromLeaves :=
  fun _ _ h35 _ hT => conjTwistNontrivial_main hT h35 hS hN2 hN3a

end G0Galois

#print axioms G0Galois.faltingsV
#print axioms G0Galois.conjData
#print axioms G0Galois.conjTwistNontrivial_of_conjBettiData
#print axioms G0Galois.conjTwistFromLeaves_of_conjBettiData
#print axioms G0Galois.conjV_galRep
#print axioms G0Galois.conjBettiData_of_comparison
#print axioms G0Galois.conjTwistNontrivial_of_comparison
#print axioms G0Galois.conjTwistFromLeaves_of_comparison
#print axioms G0Galois.toC_conjPt
#print axioms G0Galois.homT_tateLattice
#print axioms G0Galois.conjT_tateLattice
#print axioms G0Galois.lattice_contradiction
#print axioms G0Galois.conjTwistNontrivial_of_lattice
#print axioms G0Galois.conjTwistFromLeaves_of_lattice
#print axioms G0Galois.conjVarDim
#print axioms G0Galois.conjTwistNontrivial_of_latticeInj
#print axioms G0Galois.conjTwistFromLeaves_of_latticeInj
#print axioms G0Galois.tateLatticeInj_of_artinTorsion
#print axioms G0Galois.conjTwistNontrivial_of_N123
#print axioms G0Galois.conjTwistFromLeaves_of_N123
#print axioms G0Galois.toC_injective
#print axioms G0Galois.conjTwistNontrivial_of_surj
#print axioms G0Galois.conjTwistFromLeaves_of_surj
#print axioms G0Galois.conjAntiLiftLat_of
#print axioms G0Galois.conjTwistNontrivial_main
#print axioms G0Galois.conjTwistFromLeaves_main

/-! # conj-pieces: the three glue Props of conj-twist, assembled

Everything above this point is `scratch/conj-twist/ConjTwist.lean` verbatim. Below:
§A `ArtinTorsionSurj` from the leaf `MulIsogeny` (from `Artin.lean`), §B `HomLinearLift` from the
analytic leaf `HoloHomLift` (from `Holo.lean`), §C `ConjUniformization` reduced to `ConjHolo` and
proved for number fields (from `Conj.lean`), §D the assembled main theorems. -/

namespace G0FibreSimple

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

end G0FibreSimple

namespace G0Galois

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ZInQ.LeafPush2 (CPts cptObj IsUniformization cDom cEvalAt)

/-! ## §A. `ArtinTorsionSurj` from `MulIsogeny` -/

/-! ## Proof -/

/-- `[n]` as a morphism: `((n : ℤ) : End A).hom = (𝟙 A)ⁿ` (proved). -/
theorem intCast_end_hom {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℕ) :
    ((n : ℤ) : PkgI3.AbVar.End A).hom = (𝟙 A.X) ^ n := by
  rw [Int.cast_natCast, ← nsmul_one]
  change (Additive.toMul (n • (1 : PkgI3.AbVar.End A))).1 = _
  rw [toMul_nsmul, SubmonoidClass.coe_pow]
  rfl

/-- `Q ≫ [n] = Qⁿ` (proved). -/
theorem comp_mulN {K : Type} [Field K] (A : PkgI3.AbVar K) {Y : Over (Spec (CommRingCat.of K))}
    (Q : Y ⟶ A.X) (n : ℕ) : Q ≫ ((n : ℤ) : PkgI3.AbVar.End A).hom = Q ^ n := by
  rw [intCast_end_hom, MonObj.comp_pow, Category.comp_id]

/-- The image of the unit section is a closed point (proved): for every `K`-scheme `Y` and
`y ∈ Y`, `{(1 : Y ⟶ A)(y)}` is closed. -/
theorem isClosed_one_apply {K : Type} [Field K] (A : PkgI3.AbVar K)
    {Y : Over (Spec (CommRingCat.of K))} (y : Y.left) :
    IsClosed ({(1 : Y ⟶ A.X).left y} : Set A.X.left) := by
  have : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of K)))).left := by
    change Subsingleton (Spec (CommRingCat.of K)); infer_instance
  have hη : IsClosedImmersion (η[A.X]).left :=
    isClosedImmersion_of_comp_eq_id A.X.hom _ (by simp)
  have hcl := (η[A.X]).left.isClosedEmbedding.isClosed_range
  convert hcl using 1
  ext z
  constructor
  · rintro rfl
    exact ⟨(toUnit Y).left y, by rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]⟩
  · rintro ⟨a, rfl⟩
    rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
    exact congrArg _ (Subsingleton.elim _ _)

/-- A point of a scheme lying in a closed, discrete subset is closed (proved). -/
theorem isClosed_singleton_of_mem {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    (hd : IsDiscrete S) {x : X} (hx : x ∈ S) : IsClosed ({x} : Set X) := by
  have := hd.to_subtype
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hyS : y ∈ S := closure_minimal (by simpa using hx) hS hy
  have h1 : (⟨y, hyS⟩ : S) ∈ closure ({⟨x, hx⟩} : Set S) := by
    rw [closure_subtype]
    simp [hy]
  rw [(isClosed_discrete _).closure_eq] at h1
  simpa using congrArg Subtype.val h1

/-- A complex number integral over `σ(K)`, `σ = ι ∘ alg`, lies in `ι(K̄)` (proved). -/
theorem mem_range_emb {K : Type} [Field K] (emb : AlgebraicClosure K →+* ℂ) {R : Type} [CommRing R]
    (φ0 : K →+* R) (hint : φ0.IsIntegral) (φ : R →+* ℂ)
    (hσ : φ.comp φ0 = emb.comp (algebraMap K (AlgebraicClosure K))) (a : R) :
    ∃ b, emb b = φ a := by
  obtain ⟨p, hpm, hpa⟩ := hint a
  let F := emb.fieldRange
  have : IsAlgClosed F := IsAlgClosed.of_ringEquiv _ _ emb.rangeRestrictFieldEquiv
  let σF : K →+* F := emb.rangeRestrictField.comp (algebraMap K _)
  have hcomp : (algebraMap F ℂ).comp σF = φ.comp φ0 := by
    rw [hσ]; ext k; rfl
  have hint' : IsIntegral F (φ a) := ⟨p.map σF, hpm.map _, by
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hpa, map_zero]⟩
  have h1 := IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint')
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one F _ h1
  obtain ⟨b, hb⟩ := RingHom.mem_fieldRange.mp c.2
  exact ⟨b, by rw [hb]; exact hc⟩

/-- **`ArtinTorsionSurj` from the leaf `MulIsogeny` (proved).** -/
theorem artinTorsionSurj_of_mulIsogeny (hM : G0FibreSimple.MulIsogeny) : ArtinTorsionSurj := by
  intro K _ A emb n hn Q hQ
  have : CharZero K := (emb.comp (algebraMap K (AlgebraicClosure K))).charZero
  set N := ((n : ℤ) : PkgI3.AbVar.End A).hom with hNdef
  have hfin : IsFinite N.left := (hM K A n (by exact_mod_cast hn.ne')).1
  have hQN : Q ≫ N = 1 := by rw [hNdef, comp_mulN, hQ]
  set pr := Scheme.SpecToEquivOfField ℂ A.X.left Q.left with hpr
  have hQ' : Q.left = Spec.map pr.2 ≫ A.X.left.fromSpecResidueField pr.1 :=
    ((Scheme.SpecToEquivOfField ℂ A.X.left).left_inv Q.left).symm
  -- the image point is closed
  have hx : IsClosed ({pr.1} : Set A.X.left) := by
    have hpt : pr.1 = Q.left (IsLocalRing.closedPoint ℂ) := rfl
    have hS := (isClosed_one_apply A (Y := cptObj (emb.comp (algebraMap K (AlgebraicClosure K))))
      (IsLocalRing.closedPoint ℂ)).preimage
      N.left.continuous
    refine isClosed_singleton_of_mem hS
      (N.left.isDiscrete_preimage_singleton _) ?_
    rw [hpt, Set.mem_preimage, Set.mem_singleton_iff,
      show N.left (Q.left (IsLocalRing.closedPoint ℂ)) = (Q.left ≫ N.left) (IsLocalRing.closedPoint ℂ)
        from (Scheme.Hom.comp_apply _ _ _).symm, ← Over.comp_left, hQN]
  -- its residue field is finite over `K`
  have hci : IsClosedImmersion (A.X.left.fromSpecResidueField pr.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hF : IsFinite (A.X.left.fromSpecResidueField pr.1 ≫ A.X.hom) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  obtain ⟨φ0, hφ0⟩ := Spec.map_surjective (A.X.left.fromSpecResidueField pr.1 ≫ A.X.hom)
  have hint : φ0.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ0]; infer_instance
  have hσ : φ0 ≫ pr.2 = CommRingCat.ofHom (emb.comp (algebraMap K (AlgebraicClosure K))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ0, ← Category.assoc, ← hQ']
    exact Over.w Q
  have hσ' : pr.2.hom.comp φ0.hom = emb.comp (algebraMap K (AlgebraicClosure K)) := congrArg CommRingCat.Hom.hom hσ
  -- the lift `ψ : κ(x) → K̄`
  have hrange : ∀ a, pr.2.hom a ∈ emb.fieldRange := fun a =>
    RingHom.mem_fieldRange.mpr (mem_range_emb emb φ0.hom hint pr.2.hom hσ' a)
  let ψ : A.X.left.residueField pr.1 →+* AlgebraicClosure K :=
    (emb.rangeRestrictFieldEquiv.symm : emb.fieldRange →+* AlgebraicClosure K).comp
      (pr.2.hom.codRestrict emb.fieldRange hrange)
  have hψ : ∀ a, emb (ψ a) = pr.2.hom a := fun a => by
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    rfl
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ A.X.left.fromSpecResidueField pr.1) ?_, ?_⟩
  · simp only [PkgI3.AbVar.ptObj, Over.mk_hom, Category.assoc]
    rw [← hφ0, ← Spec.map_comp]
    congr 1
    ext k
    apply emb.injective
    change emb (ψ (φ0.hom k)) = emb (algebraMap K _ k)
    rw [hψ]
    exact congrArg (fun f : K →+* ℂ => f k) hσ'
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom emb) ≫ Spec.map (CommRingCat.ofHom ψ) ≫
      A.X.left.fromSpecResidueField pr.1 = Q.left
    rw [hQ', ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact hψ a


/-! ## §B. `HomLinearLift` from `HoloHomLift` -/

/-- **N2′. Holomorphic homomorphisms into a uniformized abelian variety are linear (textbook
LEAF).** Let `B` be an abelian variety over `K`, `σ : K → ℂ`, `h = dim B`, and `Φ_B` a
uniformization of `B(ℂ)_σ` (`IsUniformization`). If `Ψ : ℂ^g → B(ℂ)_σ` is a homomorphism which is
holomorphic in the same sense (the preimage of every affine-chart domain is open and every regular
function is holomorphic on it), then `Ψ = Φ_B ∘ M` for a `ℂ`-linear `M : ℂ^g → ℂ^h`.

Source: Mumford, *Abelian varieties*, §1 (`B(ℂ)_σ ≅ ℂ^h/Λ_B` as complex Lie groups, with GAGA,
Serre 1956), and Birkenhake–Lange, *Complex abelian varieties*, Prop. 1.2.1 (a holomorphic map
of complex tori lifts to an affine map of the universal covers; a homomorphism lifts to a linear
one); UNVERIFIED numbers. The predicate makes `Ψ` a continuous, hence holomorphic,
homomorphism into the complex Lie group `B(ℂ)_σ`, so `Ψ = exp ∘ L`; `Φ_B = exp ∘ T` with `T` a
linear isomorphism (`Φ_B` is onto), and `M = T⁻¹L`. It involves one variety and no algebraic
morphism; `HomLinearLift` is the case `Ψ = f ∘ Φ_A`. -/
def HoloHomLift : Prop :=
  ∀ (K : Type) [Field K] (B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛB : Submodule ℤ (Fin h → ℂ)) (ΦB : (Fin h → ℂ) → CPts B σ) (Ψ : (Fin g → ℂ) → CPts B σ),
    B.dim = (h : WithBot ℕ∞) → IsUniformization σ ΛB ΦB →
    (∀ z w, Ψ (z + w) = Ψ z * Ψ w) → (∀ U, IsOpen (cDom Ψ U)) →
    (∀ U (s : Γ(B.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Ψ z) U s) (cDom Ψ U)) →
    ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), ∀ z, ΦB (M z) = Ψ z

/-! ## Algebraic morphisms preserve holomorphy (proved) -/

/-- `Ψ ∘ φ` meets the chart `U` exactly where `Ψ` meets `φ⁻¹U` (proved). -/
theorem cDom_comp {K : Type} [Field K] {A B : PkgI3.AbVar K} {σ : K →+* ℂ} {g : ℕ}
    (Φ : (Fin g → ℂ) → CPts A σ) (φ : A.X ⟶ B.X) (U : B.X.left.Opens) :
    cDom (fun z => Φ z ≫ φ) U = cDom Φ (φ.left ⁻¹ᵁ U) := rfl

/-- Evaluating a regular function at `p ≫ φ` is evaluating its pullback at `p` (proved). -/
theorem cEvalAt_comp {K : Type} [Field K] {A B : PkgI3.AbVar K} {σ : K →+* ℂ} (p : CPts A σ)
    (φ : A.X ⟶ B.X) (U : B.X.left.Opens) (s : Γ(B.X.left, U)) :
    cEvalAt (p ≫ φ) U s = cEvalAt p (φ.left ⁻¹ᵁ U) (φ.left.app U s) := by
  unfold cEvalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (φ.left ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

/-- **N2 from N2′ (proved).** -/
theorem homLinearLift_of_holoHomLift (hL : HoloHomLift) : HomLinearLift := by
  intro K _ A B σ g h ΛA ΛB ΦA ΦB _ hB hΦA hΦB f
  refine hL K B σ g h ΛB ΦB (fun z => ΦA z ≫ f.hom) hB hΦB (fun z w => ?_) (fun U => ?_)
    (fun U s => ?_)
  · change ΦA (z + w) ≫ f.hom = (ΦA z ≫ f.hom) * (ΦA w ≫ f.hom)
    rw [hΦA.1, MonObj.mul_comp]
  · rw [cDom_comp]
    exact hΦA.2.2.2.1 _
  · rw [cDom_comp]
    have := hΦA.2.2.2.2 (f.hom.left ⁻¹ᵁ U) (f.hom.left.app U s)
    refine this.congr fun z _ => ?_
    exact cEvalAt_comp (ΦA z) f.hom U s


/-! ## §2. The group-theoretic clauses and the analytic glue `ConjHolo` -/

/-- `twistC` is a homomorphism (proved). -/
theorem twistC_mul {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (P Q : CPts A σ) :
    twistC A σ s h (P * Q) = twistC A σ s h P * twistC A σ s h Q := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ (P * Q)) =
    (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ P) *
      (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ Q)
  rw [MonObj.comp_mul, MonObj.comp_mul, homEquiv_mul_conj]

theorem twistC_surj_aux {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) :
    mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫
    Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 _ = 𝟙 _
  rw [Category.id_comp, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

/-- `twistC` is surjective (proved). -/
theorem twistC_surjective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : Function.Surjective (twistC A σ s h) := by
  intro R
  refine ⟨conjHomInv σ s h ≫ mapPtIsoInv σ s ≫
    ((Over.mapPullbackAdj (specS s)).homEquiv _ _).symm R, ?_⟩
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫
    conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ ((Over.mapPullbackAdj (specS s)).homEquiv _ _).symm R) = R
  have e : mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s ≫
      ((Over.mapPullbackAdj (specS s)).homEquiv _ _).symm R =
      (mapPtIso σ s ≫ conjHom σ s h ≫ conjHomInv σ s h ≫ mapPtIsoInv σ s) ≫
        ((Over.mapPullbackAdj (specS s)).homEquiv _ _).symm R := by
    simp only [Category.assoc]
  rw [e, twistC_surj_aux, Category.id_comp]
  exact Equiv.apply_symm_apply _ _

/-- **N3a-holo. Conjugation preserves holomorphy (GLUE; STANDARD).** If `σ ∘ s = conj ∘ σ` and
`Ψ : ℂ^g → A(ℂ)_σ` is holomorphic in the sense of `IsUniformization` (preimages of affine-chart
domains open, regular functions holomorphic there), so is `z ↦ twistC(Ψ(z̄))` into `A^s(ℂ)_σ`.
These are the two analytic clauses of `ConjUniformization`. (On the affine pieces
`W ×_{Spec K, Spec s} Spec K` of `A^s`, a regular function `Σ aᵢ ⊗ bᵢ` takes at `twistC(Ψ z̄)` the
value `conj(Σ aᵢ(Ψ z̄)·conj(σ bᵢ))`, and `z ↦ conj(f(z̄))` is holomorphic when `f` is.) Proved
below when `s` is bijective (`conjHolo_of_bijective`), e.g. for every number field. -/
def ConjHolo : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Ψ : (Fin g → ℂ) → CPts A σ),
    (∀ U, IsOpen (cDom Ψ U)) →
    (∀ U (t : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Ψ z) U t) (cDom Ψ U)) →
    (∀ V, IsOpen (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V)) ∧
    ∀ V (t : Γ((conjVar A s).X.left, V)), DifferentiableOn ℂ
      (fun z => cEvalAt (twistC A σ s h (Ψ (conjL g z))) V t)
      (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V)

/-- The conjugate of a uniformization, given the analytic clauses (proved). -/
theorem isUniformization_twist {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (s : K →+* K) (h : σ.comp s = (starRingEnd ℂ).comp σ) {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → CPts A σ} (hΦ : IsUniformization σ Λ Φ)
    (hO : ∀ V, IsOpen (cDom (fun z => twistC A σ s h (Φ (conjL g z))) V))
    (hH : ∀ V (t : Γ((conjVar A s).X.left, V)), DifferentiableOn ℂ
      (fun z => cEvalAt (twistC A σ s h (Φ (conjL g z))) V t)
      (cDom (fun z => twistC A σ s h (Φ (conjL g z))) V)) :
    IsUniformization σ (Λ.comap ((conjL g).restrictScalars ℤ))
      (fun z => twistC A σ s h (Φ (conjL g z))) := by
  refine ⟨fun z w => ?_, fun z => ?_, ?_, hO, hH⟩
  · change twistC A σ s h (Φ (conjL g (z + w))) =
      twistC A σ s h (Φ (conjL g z)) * twistC A σ s h (Φ (conjL g w))
    rw [map_add, hΦ.1, twistC_mul]
  · change twistC A σ s h (Φ (conjL g z)) = 1 ↔ conjL g z ∈ Λ
    rw [← hΦ.2.1, ← twistC_one A σ s h]
    exact (twistC_injective A σ s h).eq_iff
  · intro R
    obtain ⟨Q, rfl⟩ := twistC_surjective A σ s h R
    obtain ⟨w, rfl⟩ := hΦ.2.2.1 Q
    exact ⟨conjL g w, by simp only [conjL_conjL]⟩

/-- **`ConjUniformization` from the analytic glue `ConjHolo` (proved).** -/
theorem conjUniformization_of_conjHolo (hC : ConjHolo) : ConjUniformization := by
  intro K _ A σ s h g Λ Φ _ hΦ
  obtain ⟨hO, hH⟩ := hC K A σ s h g Φ hΦ.2.2.2.1 hΦ.2.2.2.2
  exact isUniformization_twist A σ s h hΦ hO hH

/-! ## §3. `ConjHolo` for bijective `s` (proved), hence `ConjUniformization` for number fields -/

theorem top_le_preimage_spec (f : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))
    (W : (Spec (CommRingCat.of ℂ)).Opens) : ⊤ ≤ f ⁻¹ᵁ W ↔ ⊤ ≤ W := by
  constructor
  · intro hW x _
    have hx : f x ∈ W := hW trivial
    rwa [Subsingleton.elim (f x) x] at hx
  · intro hW x _
    exact hW trivial

theorem appLE_of_eq {X Y : Scheme} {f f' : X ⟶ Y} (e : f = f') (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) : f.appLE U V hf = f'.appLE U V (e ▸ hf) := by
  subst e; rfl

/-- If `r ≫ fst = c ≫ q` with `c : Spec ℂ → Spec ℂ`, then `r` meets `fst⁻¹U` iff `q` meets `U`
(proved). -/
theorem top_le_of_comp_eq {P X : Scheme} (r : Spec (CommRingCat.of ℂ) ⟶ P) (fst : P ⟶ X)
    (q : Spec (CommRingCat.of ℂ) ⟶ X) (c : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))
    (hr : r ≫ fst = c ≫ q) (U : X.Opens) : ⊤ ≤ r ⁻¹ᵁ fst ⁻¹ᵁ U ↔ ⊤ ≤ q ⁻¹ᵁ U := by
  change ⊤ ≤ (r ≫ fst) ⁻¹ᵁ U ↔ _
  rw [hr]
  exact top_le_preimage_spec c (q ⁻¹ᵁ U)

/-- If `r ≫ fst = Spec(conj) ≫ q`, the value at `r` of the pullback along `fst` of a regular
function is the conjugate of its value at `q` (proved). -/
theorem eval_of_comp_eq_conj {P X : Scheme} (r : Spec (CommRingCat.of ℂ) ⟶ P) (fst : P ⟶ X)
    (q : Spec (CommRingCat.of ℂ) ⟶ X)
    (hr : r ≫ fst = Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ q) (U : X.Opens)
    (a : Γ(X, U)) (h1 : ⊤ ≤ r ⁻¹ᵁ fst ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (r.appLE (fst ⁻¹ᵁ U) ⊤ h1 (fst.app U a)) =
      starRingEnd ℂ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ hq a)) := by
  have h1' : ⊤ ≤ (r ≫ fst) ⁻¹ᵁ U := by rw [Scheme.Hom.comp_preimage]; exact h1
  have e1 : r.appLE (fst ⁻¹ᵁ U) ⊤ h1 (fst.app U a) = (r ≫ fst).appLE U ⊤ h1' a := by
    rw [Scheme.Hom.comp_appLE]; rfl
  rw [e1, appLE_of_eq hr,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) q U ⊤ ⊤
      hq le_top, CommRingCat.comp_apply,
    show (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))).appTop from Scheme.Hom.appLE_eq_app _]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (q.appLE U ⊤ hq a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (starRingEnd ℂ)))

/-- The first component of the adjunction bijection is the given map (proved). -/
theorem homEquiv_left_fst {X Y : Scheme} (f : X ⟶ Y) (x : Over X) (y : Over Y)
    (u : (Over.map f).obj x ⟶ y) :
    ((Over.mapPullbackAdj f).homEquiv x y u).left ≫ pullback.fst y.hom f = u.left := by
  simp [Adjunction.homEquiv_unit]

/-- The projection `A^s = A ×_{Spec K, Spec s} Spec K → A`. -/
def cfst {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K) :
    (conjVar A s).X.left ⟶ A.X.left :=
  pullback.fst A.X.hom (specS s)

/-- `Spec(conj)` on `Spec ℂ`, typed as an endomorphism of `(cptObj σ).left`. -/
def cconj {K : Type} [Field K] (σ : K →+* ℂ) : (cptObj σ).left ⟶ (cptObj σ).left :=
  Spec.map (CommRingCat.ofHom (starRingEnd ℂ))

/-- The first component of `twistC Q` is `Spec(conj) ≫ Q` (proved). -/
theorem twistC_left_fst {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) :
    (twistC A σ s h Q).left ≫ cfst A s = cconj σ ≫ Q.left := by
  refine (homEquiv_left_fst (specS s) (cptObj σ) A.X (mapPtIso σ s ≫ conjCs A σ s h Q)).trans ?_
  exact Category.id_comp _

/-- Evaluating a pulled-back regular function at `twistC Q` conjugates its value at `Q`
(proved). -/
theorem cEvalAt_twistC {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) (U : A.X.left.Opens)
    (a : Γ(A.X.left, U)) :
    cEvalAt (A := conjVar A s) (twistC A σ s h Q) (cfst A s ⁻¹ᵁ U)
      ((cfst A s).app U a) = starRingEnd ℂ (cEvalAt Q U a) := by
  unfold cEvalAt
  have hiff : ⊤ ≤ (twistC A σ s h Q).left ⁻¹ᵁ (cfst A s ⁻¹ᵁ U) ↔ ⊤ ≤ Q.left ⁻¹ᵁ U :=
    top_le_of_comp_eq _ _ _ _ (twistC_left_fst A σ s h Q) U
  by_cases hQ : ⊤ ≤ Q.left ⁻¹ᵁ U
  · have h1 := hiff.mpr hQ
    rw [dif_pos h1, dif_pos hQ]
    exact eval_of_comp_eq_conj _ _ _ (twistC_left_fst A σ s h Q) U a h1 hQ
  · have h1 : ¬ ⊤ ≤ (twistC A σ s h Q).left ⁻¹ᵁ (cfst A s ⁻¹ᵁ U) := fun h' => hQ (hiff.mp h')
    rw [dif_neg h1, dif_neg hQ, map_zero]

/-- `z ↦ conj(F(z̄))` is holomorphic on `conj⁻¹ D` when `F` is holomorphic on the open set `D`
(proved). -/
theorem differentiableOn_conj_conj {g : ℕ} {F : (Fin g → ℂ) → ℂ} {D : Set (Fin g → ℂ)}
    (hF : DifferentiableOn ℂ F D) (hD : IsOpen D) :
    DifferentiableOn ℂ (fun z => starRingEnd ℂ (F (conjL g z))) (conjL g ⁻¹' D) := by
  intro z hz
  have hFz : DifferentiableAt ℂ F (conjL g z) := hF.differentiableAt (hD.mem_nhds hz)
  set L := fderiv ℂ F (conjL g z)
  have hL : HasFDerivAt F L (conjL g z) := hFz.hasFDerivAt
  let cL : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (conjL g)
  have hcL : HasFDerivAt (fun z => conjL g z) cL z := cL.hasFDerivAt
  have hR : HasFDerivAt (fun z => starRingEnd ℂ (F (conjL g z)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((L.restrictScalars ℝ).comp cL)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z ((hL.restrictScalars ℝ).comp z hcL)
  let L'l : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => starRingEnd ℂ (L (conjL g v))
      map_add' := fun v w => by simp [map_add]
      map_smul' := fun c v => by
        have : conjL g (c • v) = starRingEnd ℂ c • conjL g v := by
          funext i; simp [conjL]
        simp [this] }
  let L' : (Fin g → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap L'l
  have hC : HasFDerivAt (fun z => starRingEnd ℂ (F (conjL g z))) L' z :=
    hasFDerivAt_of_restrictScalars ℝ hR (by ext v; rfl)
  exact hC.differentiableAt.differentiableWithinAt

/-- **`ConjHolo` for bijective `s` (proved).** `Spec(s)` is an isomorphism, so is the projection
`A^s → A`; every open of `A^s` and every regular function on it is pulled back from `A`
(`cEvalAt_twistC`). -/
theorem conjHolo_of_bijective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (s : K →+* K) (hb : Function.Bijective s) (h : σ.comp s = (starRingEnd ℂ).comp σ) {g : ℕ}
    (Ψ : (Fin g → ℂ) → CPts A σ) (hO : ∀ U, IsOpen (cDom Ψ U))
    (hH : ∀ U (t : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Ψ z) U t) (cDom Ψ U)) :
    (∀ V, IsOpen (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V)) ∧
    ∀ V (t : Γ((conjVar A s).X.left, V)), DifferentiableOn ℂ
      (fun z => cEvalAt (twistC A σ s h (Ψ (conjL g z))) V t)
      (cDom (fun z => twistC A σ s h (Ψ (conjL g z))) V) := by
  let e : K ≃+* K := RingEquiv.ofBijective s hb
  have : IsIso (CommRingCat.ofHom s) :=
    ⟨⟨CommRingCat.ofHom (e.symm : K →+* K), by ext x; exact e.symm_apply_apply x,
      by ext x; exact e.apply_symm_apply x⟩⟩
  have : IsIso (specS s) := by unfold specS; infer_instance
  have : IsIso (cfst A s) := (inferInstance : IsIso (pullback.fst A.X.hom (specS s)))
  have hV : ∀ V : (conjVar A s).X.left.Opens,
      ∃ U, cfst A s ⁻¹ᵁ U = V := fun V =>
    ⟨(inv (cfst A s)) ⁻¹ᵁ V, by
      ext x
      change (inv (cfst A s)) (cfst A s x) ∈ V ↔ x ∈ V
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl⟩
  have hdom : ∀ U, cDom (fun z => twistC A σ s h (Ψ (conjL g z)))
      (cfst A s ⁻¹ᵁ U) = conjL g ⁻¹' cDom Ψ U := by
    intro U
    ext z
    exact top_le_of_comp_eq _ _ _ _ (twistC_left_fst A σ s h (Ψ (conjL g z))) U
  have hcont : Continuous (conjL g) := LinearMap.continuous_of_finiteDimensional _
  refine ⟨fun V => ?_, fun V t => ?_⟩
  · obtain ⟨U, rfl⟩ := hV V
    rw [hdom]
    exact (hO U).preimage hcont
  · obtain ⟨U, rfl⟩ := hV V
    obtain ⟨a, rfl⟩ : ∃ a, (cfst A s).app U a = t :=
      ⟨inv ((cfst A s).app U) t, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    rw [hdom]
    refine (differentiableOn_conj_conj (hH U a) (hO U)).congr fun z _ => ?_
    exact cEvalAt_twistC A σ s h (Ψ (conjL g z)) U a

/-- **N3a for number fields** (`ConjUniformization` with `[NumberField K]`; the only case used by
conj-twist's `conjAntiLiftLat_of`). -/
def ConjUniformizationNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    IsUniformization σ (Λ.comap ((conjL g).restrictScalars ℤ))
      (fun z => twistC A σ s h (Φ (conjL g z)))

/-- **`ConjUniformizationNF` (proved, no hypotheses).** -/
theorem conjUniformizationNF : ConjUniformizationNF := by
  intro K _ _ A σ s h g Λ Φ _ hΦ
  obtain ⟨hO, hH⟩ := conjHolo_of_bijective A σ s (ringHom_bijective_of_numberField K s) h Φ
    hΦ.2.2.2.1 hΦ.2.2.2.2
  exact isUniformization_twist A σ s h hΦ hO hH


/-! ## §D. Assembly -/

/-- **N3 for number fields from N2 alone (proved):** conj-twist's `conjAntiLiftLat_of` with
`ConjUniformization` replaced by the proved `conjUniformizationNF`. -/
theorem conjAntiLiftLat_of_homLinearLift (hN2 : HomLinearLift) : ConjAntiLiftLat := by
  intro K _ _ A σ s h g Λ Λ' Φ Φ' hd _ hlat hΦ hΦ'
  have hd' : (conjVar A s).dim = (g : WithBot ℕ∞) := by rw [conjVarDim]; exact hd
  have hψ := conjUniformizationNF K A σ s h g Λ Φ hd hΦ
  obtain ⟨M, hM⟩ := hN2 K (conjVar A s) (conjVar A s) σ g g _ Λ' _ Φ' hd' hd' hψ hΦ' 1
  have hM' : ∀ z, Φ' (M z) = twistC A σ s h (Φ (conjL g z)) := fun z => by
    rw [hM z]; exact Category.comp_id _
  refine ⟨(M.restrictScalars ℝ) ∘ₗ conjL g, fun z => ?_, ?_, fun z => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [conjL_I, map_neg, M.map_smul]
  · intro z w hzw
    have key : ∀ v, M (conjL g v) = 0 → v = 0 := by
      intro v hv
      apply eq_zero_of_real_smul_mem Λ v
      intro t
      rw [← hΦ.2.1]
      apply twistC_injective A σ s h
      rw [twistC_one, ← conjL_conjL (t • v), ← hM', map_smul, ← Complex.coe_smul,
        M.map_smul, hv, smul_zero]
      exact (hΦ'.2.1 0).mpr (Submodule.zero_mem _)
    have : M (conjL g (z - w)) = 0 := by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars] at hzw
      rw [map_sub, map_sub, hzw, sub_self]
    exact sub_eq_zero.mp (key _ this)
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [hM', conjL_conjL]

/-- **`ConjTwistNontrivial` from T26, T35, N1-surj and N2 (proved; N3a no longer needed).** -/
theorem conjTwistNontrivial_of_surj_N2 (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hS : ArtinTorsionSurj) (hN2 : HomLinearLift) :
    ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 (artinTorsion_of_surj hS) hN2
    (conjAntiLiftLat_of_homLinearLift hN2)
    (tateLatticeInj_of_artinTorsion (artinTorsion_of_surj hS))

/-- **Main result: `ConjTwistNontrivial` from the leaves T26 (`TateModuleFree`), T35
(`UniformizationExists`), `MulIsogeny` and `HoloHomLift` (proved).** `FaltingsTate` is a
hypothesis inside `ConjTwistNontrivial` itself. -/
theorem conjTwistNontrivial_leaves (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hM : G0FibreSimple.MulIsogeny)
    (hL : HoloHomLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_surj_N2 hT h35 (artinTorsionSurj_of_mulIsogeny hM)
    (homLinearLift_of_holoHomLift hL)

/-- **Main result: `ConjTwistFromLeaves` from `MulIsogeny` and `HoloHomLift` (proved).** -/
theorem conjTwistFromLeaves_leaves (hM : G0FibreSimple.MulIsogeny) (hL : HoloHomLift) :
    ConjTwistFromLeaves :=
  fun _ _ h35 _ hT => conjTwistNontrivial_leaves hT h35 hM hL

/-- **The three glue Props of conj-twist (proved):** `ArtinTorsionSurj` from `MulIsogeny`,
`HomLinearLift` from `HoloHomLift`, `ConjUniformization` from `ConjHolo`; with conj-twist's
`conjTwistFromLeaves_main`. -/
theorem conjTwistFromLeaves_of_pieces (hM : G0FibreSimple.MulIsogeny) (hL : HoloHomLift)
    (hC : ConjHolo) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_main (artinTorsionSurj_of_mulIsogeny hM) (homLinearLift_of_holoHomLift hL)
    (conjUniformization_of_conjHolo hC)

#print axioms artinTorsionSurj_of_mulIsogeny
#print axioms homLinearLift_of_holoHomLift
#print axioms conjUniformization_of_conjHolo
#print axioms conjUniformizationNF
#print axioms conjAntiLiftLat_of_homLinearLift
#print axioms conjTwistNontrivial_of_surj_N2
#print axioms conjTwistNontrivial_leaves
#print axioms conjTwistFromLeaves_leaves
#print axioms conjTwistFromLeaves_of_pieces


/-! ## §E. G10 from the leaves (proved) -/

/-- **G10 (corrected concrete form) from `MulIsogeny` and `HoloHomLift`.** -/
theorem g10GlueConcrete_of_leaves (hM : G0FibreSimple.MulIsogeny) (hL : HoloHomLift) :
    G10GlueConcrete :=
  g10GlueConcrete_of_conjTwistFromLeaves (conjTwistFromLeaves_leaves hM hL)

/-- **G10 (g0-assemble's form) from T26, T35, `MulIsogeny` and `HoloHomLift`.** -/
theorem g10Glue_of_leaves (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hM : G0FibreSimple.MulIsogeny) (hL : HoloHomLift) : G10Glue :=
  g10Glue_of_conjTwist (conjTwistNontrivial_leaves hT h35 hM hL)

#print axioms g10GlueConcrete_of_leaves
#print axioms g10Glue_of_leaves

end G0Galois



#print axioms G0Galois.g10Glue_of_conjTwist
#print axioms G0Galois.g10Glue_of_T12K_conjTwistOutside
#print axioms G0Galois.isOdd_of_T12K_of_forall_mem
#print axioms G0Galois.g10GlueConcrete_of_conjTwistFromLeaves
#print axioms G0Galois.betti_skeleton
#print axioms G0Galois.t12_of_t12K
#print axioms G0Galois.exists_resQ_conj
#print axioms G0Galois.betti_skeleton_fd
