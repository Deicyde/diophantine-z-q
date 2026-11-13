
/-! ## §G N1a split: the case `End⁰(A) ≅ B` proved from T6; the CM case named

The block from `B6_isUnit` to `qm_embeds_end0` is copied verbatim from
`scratch/g0-fibresimple/olean/Tail.lean` (lines 40-116, proved there). -/

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

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

/-- The centre of `B = ℍ[ℚ, 2, -3]` is `ℚ`. -/
theorem B6_central_eq (z : ℍ[ℚ, 2, -3]) (hz : ∀ y : ℍ[ℚ, 2, -3], z * y = y * z) :
    z = algebraMap ℚ _ z.re := by
  have hi := hz ⟨0, 1, 0, 0⟩
  have hj := hz ⟨0, 0, 1, 0⟩
  have hi2 := congrArg QuaternionAlgebra.imJ hi
  have hi3 := congrArg QuaternionAlgebra.imK hi
  have hj1 := congrArg QuaternionAlgebra.imI hj
  have hj3 := congrArg QuaternionAlgebra.imK hj
  simp at hi2 hi3 hj1 hj3
  ext <;> simp <;> linarith

/-- `m ↦ 1 ⊗ m`, `End(A) → End⁰(A)`, is injective when `End(A)` is a free `ℤ`-module (T6). -/
theorem tmul_one_injective {k : Type} [Field k] {A : PkgI3.AbVar k}
    (hfree : Module.Free ℤ (PkgI3.AbVar.End A)) (m : PkgI3.AbVar.End A)
    (hm : (1 : ℚ) ⊗ₜ[ℤ] m = 0) : m = 0 := by
  let f := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) f).mp hm
  rw [Submonoid.smul_def] at hs'
  exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')

/-- **N1a, case `End⁰(A) ≅ B` (proved from T6).** If `End⁰(A) ≅ ℍ[ℚ, 2, -3]` for an abelian
variety with a QM structure `q`, then every element of `com q = End_𝒪(A)` is an integer: `1 ⊗ φ`
commutes with the image of `B`, which is all of `End⁰(A)` (an injective map of 4-dimensional
`ℚ`-spaces), so it is a rational scalar `c` (`B6_central_eq`); `φ` is integral over `ℤ` (`End(A)`
is a finitely generated `ℤ`-module, T6), hence so is `c`, so `c ∈ ℤ`; and `m ↦ 1 ⊗ m` is
injective (T6). -/
theorem com_int_of_end0_quat (hHF : PkgI3.HomFreeFinite) {k : Type} [Field k]
    {A : PkgI3.AbVar k} (q : QMStr A) (e : PkgI3.AbVar.End0 A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) :
    ∀ φ ∈ com q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End A) := by
  intro φ hφ
  obtain ⟨hfree, hfin, -, -⟩ := hHF k A A
  let L : ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A := (qmBasis q).liftHom
  have : Nontrivial (PkgI3.AbVar.End0 A) := e.toRingEquiv.nontrivial
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have := (B6_isUnit b hb0).map L
    rw [hb] at this
    exact not_isUnit_zero this
  have : FiniteDimensional ℚ (PkgI3.AbVar.End0 A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hLsurj : Function.Surjective L.toLinearMap := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [QuaternionAlgebra.finrank_eq_four, e.toLinearEquiv.finrank_eq,
        QuaternionAlgebra.finrank_eq_four])]
    exact hLinj
  set x : PkgI3.AbVar.End0 A := (1 : ℚ) ⊗ₜ[ℤ] φ with hx
  have e1 : ∀ a b : PkgI3.AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hcomm_g : ∀ a : LeafQM.O, Commute x ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) := by
    intro a
    rw [com, Subring.mem_centralizer_iff] at hφ
    have h := hφ (q.iota a) ⟨a, rfl⟩
    show x * _ = _ * x
    rw [hx, ← e1, ← e1, h]
  have hcomm : ∀ y : PkgI3.AbVar.End0 A, x * y = y * x := by
    intro y
    obtain ⟨b, rfl⟩ := hLsurj y
    change Commute x ((qmBasis q).lift b)
    simp only [QuaternionAlgebra.Basis.lift]
    have h0 : Commute x (algebraMap ℚ (PkgI3.AbVar.End0 A) b.re) := (Algebra.commutes _ _).symm
    exact ((h0.add_right ((hcomm_g oi).smul_right _)).add_right
      ((hcomm_g oj).smul_right _)).add_right (((hcomm_g oi).mul_right (hcomm_g oj)).smul_right _)
  -- `x` is a rational scalar
  have hex : e x = algebraMap ℚ _ (e x).re := by
    apply B6_central_eq
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hcomm]
  set c : ℚ := (e x).re
  have hxc : x = algebraMap ℚ _ c := by
    apply e.injective; rw [hex, AlgEquiv.commutes]
  -- `c` is an integer
  have hint : IsIntegral ℤ φ := Algebra.IsIntegral.isIntegral φ
  obtain ⟨p, hpm, hp⟩ := hint
  have hpc : Polynomial.aeval c p = 0 := by
    have h1 : Polynomial.aeval x p = 0 := by
      have := Polynomial.aeval_algHom_apply
        (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A)
        φ p
      rw [← Polynomial.aeval_def] at hp
      rw [hp, map_zero] at this
      exact this
    rw [hxc, Polynomial.aeval_algebraMap_apply] at h1
    exact (algebraMap ℚ (PkgI3.AbVar.End0 A)).injective (h1.trans (map_zero _).symm)
  have hcint : IsIntegral ℤ c := ⟨p, hpm, by rw [← Polynomial.aeval_def]; exact hpc⟩
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
  refine ⟨n, sub_eq_zero.mp (tmul_one_injective hfree _ ?_)⟩
  have h1 : (1 : ℚ) ⊗ₜ[ℤ] (n : PkgI3.AbVar.End A) = (n : PkgI3.AbVar.End0 A) :=
    map_intCast (Algebra.TensorProduct.includeRight :
      PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) n
  have h2 : algebraMap ℚ (PkgI3.AbVar.End0 A) c = (n : PkgI3.AbVar.End0 A) := by
    rw [← hn, show algebraMap ℤ ℚ n = (n : ℚ) from rfl, map_intCast]
  rw [TensorProduct.tmul_sub, ← hx, hxc, h1, h2, sub_self]


/-- **N1a-CM (glue; G6, the CM case of Yu's dichotomy): the CM order.** If
`End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, for a QM abelian surface `(A, ι)` over `ℚ̄`, then
`com ι = End_𝒪(A)` is isomorphic to a subring of finite index of `𝒪_k`, `k` imaginary quadratic.
*Why true* (STANDARD linear algebra; Shimura): `B ⊗ ℚ(√d) ≅ M₂(ℚ(√d))` (`B ⊗ k` is central simple
of `k`-dimension 4 and maps to `M₂(k)`), so the centralizer of `B` in `End⁰(A)` is the centre
`k = ℚ(√d)`; `com ι = End(A) ∩ k` is a finitely generated `ℤ`-module (T6) of integral elements
(`End(A)` is finite over `ℤ`), containing `ℤ` and a non-integer `n√d` (FS4,
`centralizerOfMatrixEnd0_of_homFree`), hence a subring of finite index of `𝒪_k`. Glue (not
compiled: building `k` and the order as Lean objects from the isomorphism). -/
def ComOfMatrixEnd0 : Prop :=
  ∀ (A : AbVar Qbar) (q : QMStr A) (d : ℚ), d < 0 →
    Nonempty (AbVar.End0 A ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com q ≃+* R)

/-- **N1a from T27 (Yu), T6 and N1a-CM.** -/
theorem comIntOrQuadOrder_of (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite)
    (hCM : ComOfMatrixEnd0) : ComIntOrQuadOrder := by
  intro P
  rcases PkgI3.qmDichotomy_B6 t27 Qbar P.A P.surface B6_isUnit (qm_embeds_end0 P.q) with
    he | ⟨d, hd, hM⟩
  · obtain ⟨e⟩ := he
    exact Or.inl (com_int_of_end0_quat t6 P.q e)
  · exact Or.inr (hCM P.A P.q d hd hM)

/-- **FS5 with the repaired clauses, from the leaves and named glue**: the bundle, R5fpCount,
T27, T6 (in `TextbookLeaves`), N1b, and the glue `MobiusGlue`, N1a-CM, N2. -/
theorem fibreComTrivialFull_of_leaves (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hCM : ComOfMatrixEnd0)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL hM (comIntOrQuadOrder_of t27 t6 hCM) hB hK hC

end FS5NoCM

#print axioms FS5NoCM.B6_central_eq
#print axioms FS5NoCM.com_int_of_end0_quat
#print axioms FS5NoCM.comIntOrQuadOrder_of
#print axioms FS5NoCM.fibreComTrivialFull_of_leaves
