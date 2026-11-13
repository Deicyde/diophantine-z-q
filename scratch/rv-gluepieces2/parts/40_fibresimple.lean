


/-!
# g0-fibresimple: g0-split's missing piece 4, `FibreSimple`, from strictly smaller named Props

`HSyn.G0Split.FibreSimple` (scratch/g0-split/Split.lean, copied verbatim with everything it
depends on in `FSPrefix.lean`) is proved below (`fibreSimple_of_pieces`) from

* the leaves T27 (`PkgI3.QMDichotomyYu`, Yu 2013 Thm 1.1) and T6 (`PkgI3.HomFreeFinite`,
  Mumford §19 Thm 3), fields `t27`, `t6` of `TextbookLeaves`, and
* the textbook leaves `MulIsogeny` (Mumford §4: `[n]` is an isogeny) and `RigidityHom`
  (Mumford §4 Cor. 1: a morphism preserving `0` is a homomorphism), and
* two named glue Props: `FiniteDescends` (finiteness descends along a field extension; scheme
  theory, FS1b′) and `FibreComTrivial` (NoCM on the fibre, FS5),

with proved glue lemmas: base change along `Spec L → Spec K` is faithful
(`baseChangeFaithful_proof`, from Mathlib's fpqc descent), simplicity descends along field
extensions (`endDivisionDescent_of`, `isogenyDescends_of`, from FS1b′), simplicity is invariant under isomorphism of `k`-schemes
(`endDivisionOfSchemeIso_of_rigidity`, from `RigidityHom`), `End⁰(A)` a division algebra ⇒ nonzero endomorphisms are isogenies
(`end0Division_of_homFree`, from T6 and `MulIsogeny`), the QM structure gives `B = ℍ[ℚ,2,-3] →ₐ[ℚ] End⁰(A)`
(`qm_embeds_end0`), `B` is a division algebra (`B6_isUnit`), and the CM case of Yu's dichotomy
has a non-integral `𝒪`-centralizer (`centralizerOfMatrixEnd0_of_homFree`, from T6).

§5 records a finding: `R1fpProps`, `R2fpProps` do not determine `Φ` on closed points
(`r1fpProps_twistBy`, `r2fpProps_twistBy`), so `FibreComTrivial` (and `FibreSimple` itself) is
stronger than NoCM for the true moduli data; see docs/research/g0-fibresimple.md §2.
-/

noncomputable section

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn HSyn.G0Split
open scoped Quaternion TensorProduct

/-! ## §1 Proved glue: `B` is a division algebra -/

/-- `B = (2, -3)_ℚ` is a division algebra: every nonzero element is a unit (the norm form
`a² - 2b² + 3c² - 6d²` is anisotropic, `GlueDescent.aniso_rat`). -/
theorem B6_isUnit (x : ℍ[ℚ, 2, -3]) (hx : x ≠ 0) : IsUnit x := by
  set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 with hn_def
  have hn : n ≠ 0 := fun h0 => by
    obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext h1 h2 h3 h4)
  have hs : star x * x = algebraMap ℚ ℍ[ℚ, 2, -3] n := GlueDescent.B6_star_mul x
  have hs' : x * star x = algebraMap ℚ ℍ[ℚ, 2, -3] n := by
    rw [QuaternionAlgebra.mul_star_eq_coe]
    congr 1
    simp [QuaternionAlgebra.re_mul]
    ring
  refine ⟨⟨x, n⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, hs', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  · rw [smul_mul_assoc, hs, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]

/-- Division transported along an algebra isomorphism. -/
theorem division_of_algEquiv {D E : Type*} [Ring D] [Ring E] [Algebra ℚ D] [Algebra ℚ E]
    (e : D ≃ₐ[ℚ] E) (hE : ∀ x : E, x ≠ 0 → IsUnit x) : ∀ x : D, x ≠ 0 → IsUnit x := by
  intro x hx
  have h1 : e x ≠ 0 := by
    intro h; apply hx; rw [← e.symm_apply_apply x, h, map_zero]
  have := (hE (e x) h1).map e.symm
  rwa [e.symm_apply_apply] at this

/-! ## §2 Proved glue: a QM structure gives `B →ₐ[ℚ] End⁰(A)` -/

/-- `i ∈ 𝒪`. -/
def oi : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def oj : LeafQM.O := ⟨LeafQM.ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem coe_two_O : ((2 : LeafQM.O) : LeafQM.B) = 2 := map_ofNat LeafQM.O.subtype 2
theorem coe_three_O : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  rw [coe_two_O, Subring.coe_mul]
  ext <;> simp [oi, LeafQM.ofInt] <;> rfl

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  rw [Subring.coe_neg, coe_three_O, Subring.coe_mul]
  ext <;> simp [oj, LeafQM.ofInt] <;> rfl

theorem oj_mul_oi : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- **Glue (proved): the QM structure gives `B ↪ End⁰(A)`.** For a QM structure
`ι : 𝒪 → End_k(A)` (`LeafQM.AV.QMStr`), the elements `1 ⊗ ι(i)`, `1 ⊗ ι(j)` of
`End⁰(A) = ℚ ⊗ End(A)` satisfy `i² = 2`, `j² = -3`, `ji = -ij`, so `B = ℍ[ℚ,2,-3]` maps to
`End⁰(A)` (`QuaternionAlgebra.Basis.liftHom`). This is Yu's hypothesis "`B` embeds in `End⁰(A)`"
(injectivity is automatic: `B` is simple and `End⁰(A) ≠ 0` when a QM structure exists). -/
def qmBasis {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    QuaternionAlgebra.Basis (PkgI3.AbVar.End0 A) (2 : ℚ) 0 (-3) :=
  let g : LeafQM.O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A).toRingHom.comp
      q.iota
  { i := g oi
    j := g oj
    k := g oi * g oj
    i_mul_i := by
      rw [← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
        map_ofNat]
    j_mul_j := by
      rw [← map_mul, oj_mul_oj, map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
        map_ofNat]
    i_mul_j := rfl
    j_mul_i := by
      rw [← map_mul, oj_mul_oi, map_neg, map_mul, zero_smul, zero_sub] }

theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩

/-! ## §3 The named glue pieces (unproved; each true by the cited textbook argument) -/

/-- **Glue piece FS1 (descent of simplicity along a field extension; G5-G6 on the model `A/K`).**
If every nonzero endomorphism of `A_L` is an isogeny, the same holds for `A` over `K`.
*Why true* (STANDARD): `End_K(A) → End_L(A_L)` is injective (`Spec L → Spec K` is faithfully
flat and quasi-compact, so base change is faithful on morphisms, EGA IV₂ 2.7 / Stacks 023Q,
UNVERIFIED numbers), and "finite and surjective" descends along such base change (finiteness:
Stacks 02L4, UNVERIFIED; surjectivity: `A_L → A` is surjective). Glue. -/
def EndDivisionDescent : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K),
    PkgI3.EndDivision (LeafAdopt.abVarEquiv L (A.baseChange L)) →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K A)

/-- **Glue piece FS2 (rigidity: simplicity is invariant under scheme isomorphism).** If two
abelian varieties over `k` have isomorphic underlying `k`-schemes, and every nonzero endomorphism
of one is an isogeny, the same holds for the other. *Why true* (STANDARD): by rigidity
(Mumford, *Abelian varieties*, §4 Cor. 1, UNVERIFIED number) a `k`-isomorphism `φ` followed by the
translation by `-φ(0)` is an isomorphism of group schemes, and conjugation by it identifies the
endomorphism rings, preserving "finite and surjective". `FibreOver` gives only an isomorphism of
`ℚ̄`-schemes, so this step is needed. Glue. -/
def EndDivisionOfSchemeIso : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k), Nonempty (A.X ≅ B.X) →
    PkgI3.EndDivision B → PkgI3.EndDivision A

/-- **Glue piece FS3 (`End⁰(A)` a division algebra ⇒ every nonzero endomorphism is an isogeny;
Mumford §19 Cor. 2 direction "End⁰ division ⇒ simple", UNVERIFIED number).** *Why true*
(STANDARD): `End(A)` is torsion-free (Mumford §19 Thm 3), so `f ≠ 0` gives `1 ⊗ f ≠ 0` in
`End⁰(A)`; a unit there gives `g` with `g ∘ f = [n]`, `n ≠ 0`; `[n]` is an isogeny (Mumford §4),
so `ker f` is finite, `f(A)` is closed of dimension `dim A`, hence `f` is surjective, and
proper quasi-finite, hence finite. Glue (textbook). -/
def EndDivisionOfEnd0Division : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k),
    (∀ x : PkgI3.AbVar.End0 A, x ≠ 0 → IsUnit x) → PkgI3.EndDivision A

/-- **Glue piece FS4 (the CM case of Yu's dichotomy has a non-integral `𝒪`-centralizer).** If
`End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, for an abelian variety with QM by `𝒪`, then the centralizer
`End_𝒪(A) = com q` contains a non-integer. *Why true* (STANDARD linear algebra): the image of
`B` in `M₂(k)`, `k = ℚ(√d)`, spans `M₂(k)` over `k` (`B ⊗ k` is simple of `k`-dimension 4), so
its centralizer is the centre `k`; `n√d` lies in the image of `End(A)` for some `n ≥ 1`, and
commutation and non-integrality pass from `End⁰(A)` to `End(A)` because `End(A)` is torsion-free
(Mumford §19 Thm 3). Glue. -/
def CentralizerOfMatrixEnd0 : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (q : QMStr A) (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 A ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    ∃ φ ∈ com q, ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End A)

/-- **Glue piece FS5 = G6 (NoCM, rv-h-cm §7.2, on the actual fibre object).** For `u ∉ 𝒞` and an
object `P` of `Y₃` at a `ℚ̄`-point over `J(u)`, the centralizer `End_𝒪(P.A)` is `ℤ` (the point is
not a CM point). *Why true* (rv-h-cm §7.2, model-checked, no human review): `R1fpProps`,
`R2fpProps` pin down `Y₃` and the Hauptmodul (g0-split §3); the fibre of `X₆ → P¹` over `t(u)` is
a free `W`-orbit with residue field `ℚ(i)` (Elkies' model; `GlueRepo.PR.fibre_free`, proved); a CM
order `R` has conductor prime to 6 with 2, 3 non-split (Vignéras, (Emb)); González–Rotger
Thm 5.12 (leaf R5, `LeafQM.AV.R5ptProps`) and Prop. 5.6 then force `R = ℤ[i]` (excluded since
`t(u) ≠ 1`, `F(u) ≠ 0`) or `#CM(R) = 2 < 4 = #W·x`. Unproved: the Kummer model of `X₆ → P¹`
(function-field Galois theory), the identification of an arbitrary `(Y, Φ, π)` with the bundle's
`X₆`, the class-number arithmetic. Glue, using the leaves R1, R2, R5. -/
def FibreComTrivial : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-! ## §4 The piece, from T27 and FS1-FS5 -/

/-- **`FibreSimple` (g0-split's missing piece 4), from the leaf T27 and the glue FS1-FS5.** -/
theorem fibreSimple_of_pieces (t27 : PkgI3.QMDichotomyYu) (h1 : EndDivisionDescent)
    (h2 : EndDivisionOfSchemeIso) (h3 : EndDivisionOfEnd0Division)
    (h4 : CentralizerOfMatrixEnd0) (h5 : FibreComTrivial) : FibreSimple := by
  intro Y Φ π hR1 hR2 u hu K A hF
  obtain ⟨emb, y, P, hP, hval, hiso⟩ := hF
  let _ : Algebra K.K LeafQM.AV.Qbar := emb.toAlgebra
  -- G5 (T27 at `B = (2,-3)`): `End⁰(P.A) ≅ B` or `≅ M₂(ℚ(√d))`.
  have hY := PkgI3.qmDichotomy_B6 t27 LeafQM.AV.Qbar P.A P.surface B6_isUnit (qm_embeds_end0 P.q)
  -- G6 (NoCM): the second case is excluded.
  have hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) := by
    rcases hY with hB | ⟨d, hd, hM⟩
    · exact hB
    · exfalso
      obtain ⟨φ, hφ, hne⟩ := h4 LeafQM.AV.Qbar P.A P.q d hd hM
      obtain ⟨n, hn⟩ := h5 Y Φ π hR1 hR2 u hu y P hP hval φ hφ
      exact hne n hn
  obtain ⟨e⟩ := hB
  have hPdiv : PkgI3.EndDivision P.A := h3 LeafQM.AV.Qbar P.A (division_of_algEquiv e B6_isUnit)
  have hAbar : PkgI3.EndDivision (LeafAdopt.abVarEquiv LeafQM.AV.Qbar (A.baseChange LeafQM.AV.Qbar)) :=
    h2 LeafQM.AV.Qbar _ P.A hiso hPdiv
  exact h1 K.K LeafQM.AV.Qbar A hAbar


/-! ## §4′ Proved: `CentralizerOfMatrixEnd0` from the leaf T6 (`PkgI3.HomFreeFinite`) -/

/-- **FS4 is proved from T6** (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3: `Hom(A, B)` is a free
`ℤ`-module; `TextbookLeaves.t6`). Proof: the scalar matrix `√d` is central in `M₂(ℚ(√d))`, so
`c' = e⁻¹(√d)` is central in `End⁰(A)` and is not a rational scalar (`(√d)² = d < 0`); `ℚ ⊗ End(A)`
is the localization of `End(A)` at `ℤ \ {0}`, so `s • c' = 1 ⊗ φ` for some `φ ∈ End(A)`,
`s ≠ 0`; freeness makes `m ↦ 1 ⊗ m` injective, so `φ` commutes with `ι(𝒪)` and is not an
integer. -/
theorem centralizerOfMatrixEnd0_of_homFree (hHF : PkgI3.HomFreeFinite) :
    CentralizerOfMatrixEnd0 := by
  intro k _ _ A q d hd hM
  obtain ⟨e⟩ := hM
  set c' : PkgI3.AbVar.End0 A :=
    e.symm (Matrix.scalar (Fin 2) (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d))) with hc'
  have hcen : ∀ x : PkgI3.AbVar.End0 A, c' * x = x * c' := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hc', e.apply_symm_apply]
    exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') (e x)).eq
  have hnq : ∀ t : ℚ, c' ≠ algebraMap ℚ _ t := by
    intro t ht
    have h1 : Matrix.scalar (Fin 2) (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d)) =
        algebraMap ℚ _ t := by
      rw [← AlgEquiv.commutes e t, ← ht, hc', e.apply_symm_apply]
    have h2 : AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d) =
        AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C d) t := by
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, AdjoinRoot.algebraMap_eq]
        using this
    have hdeg : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num
    have h3 := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C d)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h3
    rw [h2, ← map_pow, ← map_sub] at h3
    have h4 : t ^ 2 - d = 0 :=
      (AdjoinRoot.of.injective_of_degree_ne_zero hdeg) (h3.trans (map_zero _).symm)
    nlinarith [sq_nonneg t]
  have hfree : Module.Free ℤ (PkgI3.AbVar.End A) := (hHF k A A).1
  let f := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  obtain ⟨⟨φ, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f c'
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] φ = (s : ℤ) • c' := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) f).mp hm
    rw [Submonoid.smul_def] at hs'
    exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')
  refine ⟨φ, ?_, ?_⟩
  · rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have key : (1 : ℚ) ⊗ₜ[ℤ] (q.iota a * φ - φ * q.iota a) = 0 := by
      have e1 : ∀ x y : PkgI3.AbVar.End A,
          (1 : ℚ) ⊗ₜ[ℤ] (x * y) = ((1 : ℚ) ⊗ₜ[ℤ] x) * ((1 : ℚ) ⊗ₜ[ℤ] y) := by
        intro x y; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
      rw [TensorProduct.tmul_sub, e1, e1, hs', mul_smul_comm, smul_mul_assoc, ← smul_sub,
        hcen, sub_self, smul_zero]
    exact sub_eq_zero.mp (hinj _ key)
  · intro n hn
    apply hnq ((n : ℚ) / (s : ℤ))
    have h1 : algebraMap ℚ (PkgI3.AbVar.End0 A) ((s : ℤ) : ℚ) * c' =
        algebraMap ℚ (PkgI3.AbVar.End0 A) (n : ℚ) := by
      rw [map_intCast, map_intCast, ← zsmul_eq_mul, ← hs', hn]
      exact map_intCast (Algebra.TensorProduct.includeRight :
        PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) n
    have hs1 : ((s : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs0
    calc c' = algebraMap ℚ (PkgI3.AbVar.End0 A) (((s : ℤ) : ℚ)⁻¹) *
          (algebraMap ℚ (PkgI3.AbVar.End0 A) ((s : ℤ) : ℚ) * c') := by
          rw [← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hs1, map_one, _root_.one_mul]
      _ = algebraMap ℚ _ ((n : ℚ) / (s : ℤ)) := by
          rw [h1, ← map_mul, div_eq_inv_mul]

/-- `FibreSimple` from the two leaves T6, T27 and the four remaining glue pieces. -/
theorem fibreSimple_of_pieces' (t6 : PkgI3.HomFreeFinite) (t27 : PkgI3.QMDichotomyYu)
    (h1 : EndDivisionDescent) (h2 : EndDivisionOfSchemeIso) (h3 : EndDivisionOfEnd0Division)
    (h5 : FibreComTrivial) : FibreSimple :=
  fibreSimple_of_pieces t27 h1 h2 h3 (centralizerOfMatrixEnd0_of_homFree t6) h5


/-! ## §4″ FS3 from T6 and the textbook leaf `MulIsogeny` -/

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

/-- **FS3 is proved from T6 (`PkgI3.HomFreeFinite`) and `MulIsogeny`.** If `1 ⊗ f` is a unit of
`End⁰(A)` with inverse `u⁻¹`, clearing denominators gives `g` and `s ≠ 0` with `g ∘ f = [s]` and
`f ∘ g = [s]` (freeness of `End(A)` makes `m ↦ 1 ⊗ m` injective). `[s]` is finite and surjective,
so `f` is finite (Mathlib `IsFinite.of_comp`, `g` separated since `A` is proper) and surjective
(`Surjective.of_comp`). -/
theorem end0Division_of_homFree (hHF : PkgI3.HomFreeFinite) (hMul : MulIsogeny) :
    EndDivisionOfEnd0Division := by
  intro k _ _ A hdiv f hf
  have hfree : Module.Free ℤ (PkgI3.AbVar.End A) := (hHF k A A).1
  let F := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) F :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ F).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) F).mp hm
    rw [Submonoid.smul_def] at hs'
    exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')
  have e1 : ∀ x y : PkgI3.AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (x * y) = ((1 : ℚ) ⊗ₜ[ℤ] x) * ((1 : ℚ) ⊗ₜ[ℤ] y) := by
    intro x y; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hx : (1 : ℚ) ⊗ₜ[ℤ] f ≠ 0 := fun h => hf (hinj f h)
  obtain ⟨u, hu⟩ := hdiv _ hx
  obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) F (↑u⁻¹ : PkgI3.AbVar.End0 A)
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] g = (s : ℤ) • (↑u⁻¹ : PkgI3.AbVar.End0 A) := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hcast : (1 : ℚ) ⊗ₜ[ℤ] ((s : ℤ) : PkgI3.AbVar.End A) = ((s : ℤ) : PkgI3.AbVar.End0 A) :=
    map_intCast (Algebra.TensorProduct.includeRight :
      PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) _
  have hgf : g * f = ((s : ℤ) : PkgI3.AbVar.End A) := by
    apply sub_eq_zero.mp; apply hinj
    rw [TensorProduct.tmul_sub, e1, hs', ← hu, smul_mul_assoc, Units.inv_mul, hcast,
      zsmul_eq_mul, _root_.mul_one, sub_self]
  have hfg : f * g = ((s : ℤ) : PkgI3.AbVar.End A) := by
    apply sub_eq_zero.mp; apply hinj
    rw [TensorProduct.tmul_sub, e1, hs', ← hu, mul_smul_comm, Units.mul_inv, hcast,
      zsmul_eq_mul, _root_.mul_one, sub_self]
  obtain ⟨hfin, hsurj⟩ := hMul k A (s : ℤ) hs0
  rw [← hgf] at hfin
  rw [← hfg] at hsurj
  change IsFinite (f.hom ≫ g.hom).left at hfin
  change Surjective (g.hom ≫ f.hom).left at hsurj
  rw [Over.comp_left] at hfin hsurj
  have hsep : IsSeparated (g.hom.left ≫ A.X.hom) := by rw [Over.w g.hom]; infer_instance
  have : IsSeparated g.hom.left := IsSeparated.of_comp (f := g.hom.left) (g := A.X.hom)
  exact ⟨IsFinite.of_comp f.hom.left g.hom.left, Surjective.of_comp g.hom.left f.hom.left⟩

/-- `FibreSimple` from the leaves T6, T27, `MulIsogeny` and the three glue pieces FS1, FS2, FS5. -/
theorem fibreSimple_of_pieces'' (t6 : PkgI3.HomFreeFinite) (t27 : PkgI3.QMDichotomyYu)
    (hMul : MulIsogeny) (h1 : EndDivisionDescent) (h2 : EndDivisionOfSchemeIso)
    (h5 : FibreComTrivial) : FibreSimple :=
  fibreSimple_of_pieces' t6 t27 h1 h2 (end0Division_of_homFree t6 hMul) h5


/-! ## §4‴ FS2 from the textbook leaf `RigidityHom` -/

/-- **Textbook leaf (rigidity; Mumford, *Abelian varieties*, §4 Cor. 1; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Cor. 2.2, over any field; locators UNVERIFIED).** A morphism
of `k`-schemes between abelian varieties that sends the identity to the identity is a
homomorphism. -/
def RigidityHom : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k) (h : A.X ⟶ B.X), η[A.X] ≫ h = η[B.X] → IsMonHom h

/-- **FS2 is proved from `RigidityHom`.** For a `k`-isomorphism `e : A.X ≅ B.X`, put
`b = e(0)`, `ψ = e - b` and `ψ' = e⁻¹ ∘ (· + b)` (translations, in the group of morphisms into
the group object). They are inverse, preserve the identity, hence are homomorphisms by rigidity;
conjugation by them carries nonzero endomorphisms of `A` to nonzero endomorphisms of `B`, and
"finite and surjective" back. -/
theorem endDivisionOfSchemeIso_of_rigidity (hR : RigidityHom) : EndDivisionOfSchemeIso := by
  intro k _ A B ⟨e⟩ hB
  set b : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B.X := η[A.X] ≫ e.hom with hb
  set ψ : A.X ⟶ B.X := e.hom * (toUnit A.X ≫ b⁻¹) with hψdef
  set ψ' : B.X ⟶ A.X := (𝟙 B.X * (toUnit B.X ≫ b)) ≫ e.inv with hψ'def
  have hu : η[A.X] ≫ toUnit A.X = 𝟙 _ := toUnit_unique _ _
  have hu' : η[B.X] ≫ toUnit B.X = 𝟙 _ := toUnit_unique _ _
  have h1 : ψ ≫ ψ' = 𝟙 A.X := by
    rw [hψ'def, ← Category.assoc, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, toUnit_unique (ψ ≫ toUnit B.X) (toUnit A.X), hψdef, _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one, e.hom_inv_id]
  have h2 : ψ' ≫ ψ = 𝟙 B.X := by
    have k1 : ψ' ≫ e.hom = 𝟙 B.X * (toUnit B.X ≫ b) := by
      rw [hψ'def, Category.assoc, e.inv_hom_id, Category.comp_id]
    have k2 : ψ' ≫ toUnit A.X ≫ b⁻¹ = toUnit B.X ≫ b⁻¹ := by
      rw [← Category.assoc, toUnit_unique (ψ' ≫ toUnit A.X) (toUnit B.X)]
    rw [hψdef, MonObj.comp_mul, k1, k2, _root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel,
      MonObj.comp_one, _root_.mul_one]
  have h3 : η[A.X] ≫ ψ = η[B.X] := by
    rw [hψdef, MonObj.comp_mul, ← Category.assoc, hu, Category.id_comp, ← hb, mul_inv_cancel,
      MonObj.one_eq_one]
  have h4 : η[B.X] ≫ ψ' = η[A.X] := by
    rw [hψ'def, ← Category.assoc, MonObj.comp_mul, Category.comp_id, ← Category.assoc, hu',
      Category.id_comp, MonObj.one_eq_one, _root_.one_mul, hb, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  have hψ : IsMonHom ψ := hR k A B ψ h3
  have hψ' : IsMonHom ψ' := hR k B A ψ' h4
  intro f hf
  let g : PkgI3.AbVar.End B := PkgI3.AbVar.Hom.mk' (ψ' ≫ f.hom ≫ ψ)
  have hfg : f.hom = ψ ≫ g.hom ≫ ψ' := by
    change f.hom = ψ ≫ (ψ' ≫ f.hom ≫ ψ) ≫ ψ'
    simp only [Category.assoc, h1, Category.comp_id]
    rw [← Category.assoc, h1, Category.id_comp]
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf
    apply PkgI3.AbVar.Hom.ext'
    rw [hfg, hg, PkgI3.AbVar.Hom.hom_zero, MonObj.one_comp, MonObj.comp_one,
      PkgI3.AbVar.Hom.hom_zero]
  obtain ⟨hfin, hsurj⟩ := hB g hg0
  have : IsIso ψ.left := ⟨ψ'.left, by rw [← Over.comp_left, h1]; rfl,
    by rw [← Over.comp_left, h2]; rfl⟩
  have : IsIso ψ'.left := ⟨ψ.left, by rw [← Over.comp_left, h2]; rfl,
    by rw [← Over.comp_left, h1]; rfl⟩
  rw [hfg]
  show IsFinite (ψ ≫ g.hom ≫ ψ').left ∧ Surjective (ψ ≫ g.hom ≫ ψ').left
  rw [Over.comp_left, Over.comp_left]
  exact ⟨inferInstance, inferInstance⟩


/-! ## §4⁗ FS1 from two scheme-theoretic descent statements -/

/-- **Glue piece FS1a (base change along a field extension is faithful).** For `L/K` a field
extension, `Over.pullback (Spec L → Spec K)` is faithful. *Why true* (STANDARD): `X_L → X` is
faithfully flat and quasi-compact, hence an epimorphism of schemes (Mathlib's
`AlgebraicGeometry.effectiveEpi_base_of_flat` covers the base map; the general statement is EGA
IV₂ 2.7 / Stacks 023Q, UNVERIFIED numbers). Glue (scheme theory). -/
def BaseChangeFaithful : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (X Y : Over (Spec (CommRingCat.of K)))
    (g h : X ⟶ Y),
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map h → g = h

/-- **Glue piece FS1b ("finite and surjective" descends along a field extension).** *Why true*
(STANDARD): finiteness is fpqc local on the target (EGA IV₂ 2.7.1, UNVERIFIED number) and the
base change square of `g` along the surjection `Y_L → Y` is a pullback; surjectivity descends
because `X_L → X` is surjective. Mathlib has the fpqc descent machinery
(`Morphisms/FlatDescent.lean`) but not this instance. Glue (scheme theory). -/
def IsogenyDescends : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (X Y : Over (Spec (CommRingCat.of K)))
    (g : X ⟶ Y),
    PkgI3.AbVar.IsIsogenyMor
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g) →
      PkgI3.AbVar.IsIsogenyMor g

open scoped CategoryTheory.Obj in
/-- **FS1 is proved from FS1a and FS1b.** A nonzero `f ∈ End_K(A)` base-changes to
`f_L = F(f)`, a homomorphism for the transported group structure; `f_L ≠ 0` because `F` is
faithful and `F(1) = 1` (`Functor.map_one`); `f_L` is an isogeny by hypothesis, and this
descends. -/
theorem endDivisionDescent_of (hFa : BaseChangeFaithful) (hDe : IsogenyDescends) :
    EndDivisionDescent := by
  intro K L _ _ _ A hL f hf
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  have hmon : @IsMonHom _ _ _ _ _ (LeafAdopt.abVarEquiv L (A.baseChange L)).grp.toMonObj
      (LeafAdopt.abVarEquiv L (A.baseChange L)).grp.toMonObj (F.map f.hom) :=
    Functor.map.instIsMonHom (F := F) (f := f.hom)
  let fL : PkgI3.AbVar.End (LeafAdopt.abVarEquiv L (A.baseChange L)) :=
    @PkgI3.AbVar.Hom.mk' _ _ _ _ (F.map f.hom) hmon
  have hfL : fL ≠ 0 := by
    intro h
    apply hf
    apply PkgI3.AbVar.Hom.ext'
    apply hFa K L _ _ f.hom 1
    have h1 : F.map f.hom = (0 : PkgI3.AbVar.End (LeafAdopt.abVarEquiv L (A.baseChange L))).hom :=
      congrArg PkgI3.AbVar.Hom.hom h
    have h2 : F.map (1 : A.X ⟶ A.X) =
        (0 : PkgI3.AbVar.End (LeafAdopt.abVarEquiv L (A.baseChange L))).hom :=
      Functor.map_one F
    exact h1.trans h2.symm
  exact hDe K L _ _ f.hom (hL fL hfL :)


/-- `Spec L → Spec K` is flat and surjective (`L/K` is faithfully flat). -/
theorem specMap_flat_surjective (K L : Type) [Field K] [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

/-- **FS1a is proved (Mathlib's fpqc descent):** `Over.pullback` along a surjective, flat,
quasi-compact morphism is faithful (`AlgebraicGeometry` instance in
`Morphisms/FlatDescent.lean`), and `Spec L → Spec K` is one. -/
theorem baseChangeFaithful_proof : BaseChangeFaithful := by
  intro K L _ _ _ X Y g h hgh
  obtain ⟨h1, h2⟩ := specMap_flat_surjective K L
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map_injective hgh

/-- **Glue piece FS1b′ (finiteness descends along a field extension).** *Why true* (STANDARD):
finiteness is fpqc local on the target (EGA IV₂ 2.7.1, UNVERIFIED number). Mathlib v4.35 has
`RingHom.Finite.codescendsAlong_faithfullyFlat` and `HasAffineProperty.descendsAlong_of_affineAnd`,
but not the descent of `IsAffineHom` that the latter needs. Glue (scheme theory). -/
def FiniteDescends : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (X Y : Over (Spec (CommRingCat.of K)))
    (g : X ⟶ Y),
    IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g).left →
      IsFinite g.left

/-- **FS1b from FS1b′:** surjectivity descends (`X_L → X` is surjective). -/
theorem isogenyDescends_of (hFin : FiniteDescends) : IsogenyDescends := by
  intro K L _ _ _ X Y g ⟨hf, hs⟩
  refine ⟨hFin K L X Y g hf, ?_⟩
  obtain ⟨h1, h2⟩ := specMap_flat_surjective K L
  set φ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hsq : ((Over.pullback φ).map g).left ≫ pullback.fst Y.hom φ =
      pullback.fst X.hom φ ≫ g.left := by
    simp
  have : Surjective (pullback.fst X.hom φ ≫ g.left) := by
    rw [← hsq]; infer_instance
  exact Surjective.of_comp (pullback.fst X.hom φ) g.left

/-- The unproved glue pieces as one bundle: FS1b′ (finiteness descends along a field
extension; scheme theory) and FS5 (NoCM on the fibre). FS1 is proved from FS1a (proved, Mathlib)
and FS1b (from FS1b′); FS2 from `RigidityHom`; FS3 from T6 and `MulIsogeny`; FS4 from T6. -/
structure FibreSimplePieces : Prop where
  finiteDescends : FiniteDescends
  comTrivial : FibreComTrivial

/-- **`FibreSimple` from the leaf bundle** (`TextbookLeaves.t6` = Mumford §19 Thm 3,
`TextbookLeaves.t27` = Yu Thm 1.1), **the textbook leaves `MulIsogeny` (Mumford §4) and
`RigidityHom` (Mumford §4 Cor. 1), and the glue pieces FS1b′ (finiteness descends along field
extensions) and FS5 (NoCM on the fibre).** -/
theorem fibreSimple_of_leaves (t : HSyn.TextbookLeaves) (hMul : MulIsogeny) (hRig : RigidityHom)
    (p : FibreSimplePieces) : FibreSimple :=
  fibreSimple_of_pieces'' t.t6 t.t27 hMul
    (endDivisionDescent_of baseChangeFaithful_proof (isogenyDescends_of p.finiteDescends))
    (endDivisionOfSchemeIso_of_rigidity hRig) p.comTrivial

/-! ## §5 Finding: `R1fpProps`, `R2fpProps` do not determine `Φ` on closed points

`FibreSimple` (and `FibreComTrivial`) quantify over every `(Y, Φ, π)` with `R1fpProps`,
`R2fpProps`. Composing `Φ` with any natural automorphism `σ` of the field-point functor of `Y`
that permutes the `π`-fibres and fixes the three CM fibres gives new data satisfying both clause
lists (`r1fpProps_twistBy`, `r2fpProps_twistBy`, proved). For such `σ`, the object attached to
a point `y` over `J(u)` is the object of the point `σ y`, which lies over `π(σ y)`. -/

/-- A natural automorphism of the field-valued points of `Y` (natural in `ℚ`-embeddings of
fields). Example: a bijection of closed points of `Y` together with `ℚ`-isomorphisms of their
residue fields (a `K`-point is a point `p` with `κ(p) → K`). -/
structure PtAuto (Y : Over (Spec (CommRingCat.of ℚ))) where
  σ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)
  natural : ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y), σ L (fieldMap f ≫ y) = fieldMap f ≫ σ K y

/-- `Φ ∘ σ`. -/
def twistBy {Y : Over (Spec (CommRingCat.of ℚ))} (Φ : PtEquiv Y) (s : PtAuto Y) : PtEquiv Y :=
  fun K _ _ => (s.σ K).trans (Φ K)

/-- **Proved: `R1fpProps` is invariant under `Φ ↦ Φ ∘ σ`.** -/
theorem r1fpProps_twistBy {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (s : PtAuto Y)
    (hfu : R1famProps Y (twistBy Φ s) ∧ R1univProps Y (twistBy Φ s)) :
    R1fpProps Y (twistBy Φ s) := by
  obtain ⟨hp, hs, hq, hnat, -, -⟩ := h1
  refine ⟨hp, hs, hq, ?_, hfu.1, hfu.2⟩
  intro K L _ _ _ _ f y P hP
  obtain ⟨Q, hQ, hb⟩ := hnat K L f (s.σ K y) P hP
  refine ⟨Q, ?_, hb⟩
  change Φ L (s.σ L (fieldMap f ≫ y)) = M3.mk Q
  rw [s.natural]
  exact hQ

/-- **Proved: `R2fpProps` is invariant under `Φ ↦ Φ ∘ σ`** when `σ` permutes the `π`-fibres of
`ℚ̄`-points and fixes the fibres over `0, ∞, −16/27` (no other condition). -/
theorem r2fpProps_twistBy {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (s : PtAuto Y)
    (hfib : ∀ y y' : fieldPt LeafQM.AV.Qbar ⟶ Y,
      π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y).left =
          π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y').left ↔
        π.val (K := LeafQM.AV.Qbar) y.left = π.val (K := LeafQM.AV.Qbar) y'.left)
    (hcm : ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (c : OnePoint LeafQM.AV.Qbar),
      (c = OnePoint.some 0 ∨ c = OnePoint.infty ∨ c = OnePoint.some (-16 / 27)) →
      π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y).left = c →
        π.val (K := LeafQM.AV.Qbar) y.left = c) :
    R2fpProps Y (twistBy Φ s) π := by
  intro y y' P Q hP hQ
  obtain ⟨hf, h4, h3, h24⟩ := h2 (s.σ LeafQM.AV.Qbar y) (s.σ LeafQM.AV.Qbar y') P Q hP hQ
  refine ⟨(hfib y y').symm.trans hf, fun c => hcm y _ (Or.inl rfl) (h4 c),
    fun c => hcm y _ (Or.inr (Or.inl rfl)) (h3 c), fun c => hcm y _ (Or.inr (Or.inr rfl)) (h24 c)⟩

/-- **Proved: what `FibreComTrivial` asserts about the given data.** Applied to `(Y, Φ ∘ σ, π)`,
it asserts that the object at `σ y` has trivial `𝒪`-centralizer for every `y` over `J(u)` and
every fibre-permuting `σ` fixing the CM fibres: that is, NoCM over every rational value `t₂`
whose fibre `σ` can exchange with the fibre over `J(u)`. -/
theorem fibreComTrivial_twisted (h5 : FibreComTrivial)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (s : PtAuto Y)
    (hfu : R1famProps Y (twistBy Φ s) ∧ R1univProps Y (twistBy Φ s))
    (hfib : ∀ y y' : fieldPt LeafQM.AV.Qbar ⟶ Y,
      π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y).left =
          π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y').left ↔
        π.val (K := LeafQM.AV.Qbar) y.left = π.val (K := LeafQM.AV.Qbar) y'.left)
    (hcm : ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (c : OnePoint LeafQM.AV.Qbar),
      (c = OnePoint.some 0 ∨ c = OnePoint.infty ∨ c = OnePoint.some (-16 / 27)) →
      π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y).left = c →
        π.val (K := LeafQM.AV.Qbar) y.left = c)
    (u : ℚ) (hu : u ∉ contactSet) (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar)
    (hP : Φ LeafQM.AV.Qbar (s.σ LeafQM.AV.Qbar y) = M3.mk P)
    (hy : π.val (K := LeafQM.AV.Qbar) y.left =
      OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u))) :
    ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A) :=
  h5 Y (twistBy Φ s) π (r1fpProps_twistBy h1 s hfu) (r2fpProps_twistBy h2 s hfib hcm) u hu y P hP hy

end G0FibreSimple

end

