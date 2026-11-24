import ZInQKernel.Contrib.OneProof.SGRDirectNV
import ZInQKernel.Contrib.OneProof.HeckeSqrtCharacter
import ZInQKernel.Contrib.OneProof.HeckeSqrtKummer
import ZInQKernel.Contrib.OneProof.Y3ToP1j
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.GAGAMorphism

noncomputable section

open Polynomial CategoryTheory AlgebraicGeometry
open _root_.LeafQM _root_.LeafQM.AV
open GlueDescent.B2Q
open HDec HDec.PropTSRed HDec.PropTSGlue HDec.TSHecke HDec.HeckeRest

namespace SGRDirect.HeckeSqrt

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
  [IsGalois (RatFunc ℚ) E]
  {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {Φ : PtEquiv Y}

local notation "B₀" => integralClosure ℚ[X] E
local notation "G₀" => Gal(E / RatFunc ℚ)

private theorem sign_ne_zero (k : Fin 4) : sign k ≠ 0 := by
  fin_cases k <;> norm_num [sign, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- The character cutting out the quadratic subfield is the second bit on the four twists. -/
def character (D : Chart Y π E) (h1 : R1fpProps Y Φ) (hh : R1heckeProps Y Φ)
    (h2 : R2fpProps Y Φ π) (hT : ObjBridge.TorsionStructure) (hW : ALFixedPoints) : G₀ →* ℚˣ where
  toFun g := Units.mk0 _ (sign_ne_zero (index D h1 hh h2 hT g))
  map_mul' g h := by
    apply Units.ext
    change sign (index D h1 hh h2 hT (g * h)) = sign (index D h1 hh h2 hT g) * sign (index D h1 hh h2 hT h)
    rw [trace_unique h2 hW (trace_index D h1 hh h2 hT (g * h))
      (trace_mul (trace_index D h1 hh h2 hT g) (trace_index D h1 hh h2 hT h)), sign_xr]
  map_one' := by
    apply Units.ext
    have h : Trace D Φ (1 : G₀) 0 := by
      intro ψ P Q hp hq
      have hr : ringAction (1 : G₀) = RingHom.id B₀ := RingHom.ext fun _ => Subtype.ext rfl
      rw [hr, RingHom.comp_id] at hq
      obtain ⟨i⟩ := Quotient.exact (hp.symm.trans hq)
      refine ⟨qmCongr (qmIso_of_iso i) (RingEquiv.refl _) ?_ (fun _ => rfl)⟩
      intro a
      change P.q.iota (_root_.HDec.LeafQM.AV.Pin.Exact.rep 0 a) = P.q.iota a
      rw [rep_zero]
    change sign (index D h1 hh h2 hT (1 : G₀)) = 1
    rw [trace_unique h2 hW (trace_index D h1 hh h2 hT 1) h]
    rfl

private theorem exists_at_coordinate (P : Y3P1j.Y3ToP1jAt Y Φ π) (t : OnePoint Qbar) :
    ∃ y : fieldPt Qbar ⟶ Y, ∃ A : QML3 Qbar, Φ Qbar y = M3.mk A ∧ π.val (K := Qbar) y.left = t := by
  obtain ⟨y, hy⟩ := P.2.1 t
  exact ⟨y, _, (Quotient.out_eq _).symm, hy⟩

theorem cm_objects (hy : Y3P1j.Y3ToP1j) (h1 : R1fpProps Y Φ) :
    (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q) := by
  obtain ⟨π', hπ'⟩ := hy Y Φ h1
  obtain ⟨y₄, P₄, h₄, e₄⟩ := exists_at_coordinate hπ' (OnePoint.some 0)
  obtain ⟨y₃, P₃, h₃, e₃⟩ := exists_at_coordinate hπ' OnePoint.infty
  obtain ⟨y₂₄, P₂₄, h₂₄, e₂₄⟩ := exists_at_coordinate hπ' (OnePoint.some (-16 / 27))
  exact ⟨⟨_, (hπ'.1 y₄ y₄ P₄ P₄ h₄ h₄).2.1.2 e₄⟩,
    ⟨_, (hπ'.1 y₃ y₃ P₃ P₃ h₃ h₃).2.2.1.2 e₃⟩,
    ⟨_, (hπ'.1 y₂₄ y₂₄ P₂₄ P₂₄ h₂₄ h₂₄).2.2.2.2 e₂₄⟩⟩

omit [Algebra (RatFunc ℚ) E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
  [IsGalois (RatFunc ℚ) E] in
theorem exists_residue_hom (Q : Ideal B₀) [Q.IsPrime] (b : ℚ)
    (hQ : Q.under ℚ[X] = Ideal.span {X - C b}) :
    ∃ ψ : B₀ →+* Qbar, RingHom.ker ψ = Q ∧ ψ (algebraMap ℚ[X] B₀ X) = algebraMap ℚ Qbar b := by
  let φ := Polynomial.eval₂RingHom (algebraMap ℚ Qbar) (algebraMap ℚ Qbar b)
  have hker : RingHom.ker (algebraMap ℚ[X] (B₀ ⧸ Q)) = RingHom.ker φ := by
    rw [ker_eval_rat, ← hQ]
    ext a
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply ℚ[X] B₀ (B₀ ⧸ Q),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  have : Algebra.IsIntegral ℚ[X] (B₀ ⧸ Q) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ ℚ[X] Q)
      (Ideal.Quotient.mkₐ_surjective ℚ[X] Q)
  obtain ⟨L, hL⟩ := GFC.exists_extend (Λ := Qbar) (R := ℚ[X]) (S := B₀ ⧸ Q) φ (by rw [hker])
  have : IsDomain (B₀ ⧸ Q) := Ideal.Quotient.isDomain Q
  have : Q.IsMaximal := by
    have hmax : (Q.under ℚ[X]).IsMaximal := by
      apply Ideal.IsPrime.isMaximal (inferInstance : (Q.under ℚ[X]).IsPrime)
      rw [hQ, ne_eq, Ideal.span_singleton_eq_bot]
      exact X_sub_C_ne_zero b
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℚ[X]) Q hmax
  let : Field (B₀ ⧸ Q) := Ideal.Quotient.field Q
  refine ⟨L.comp (Ideal.Quotient.mk Q), ?_, ?_⟩
  · ext z
    rw [RingHom.mem_ker, RingHom.comp_apply, ← L.map_zero, L.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
  · have e := RingHom.congr_fun hL X
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply ℚ[X] B₀ (B₀ ⧸ Q),
      Ideal.Quotient.algebraMap_eq] at e
    change L (Ideal.Quotient.mk Q (algebraMap ℚ[X] B₀ X)) = algebraMap ℚ Qbar b
    change L (Ideal.Quotient.mk Q (algebraMap ℚ[X] B₀ X)) =
      Polynomial.eval₂ (algebraMap ℚ Qbar) (algebraMap ℚ Qbar b) X at e
    rw [Polynomial.eval₂_X] at e
    exact e

theorem inertia_trivial_of_ramificationIdx_eq_one (Q : Ideal B₀) [Q.IsPrime]
    (he : Q.ramificationIdx ℚ[X] = 1) : Q.inertia G₀ = ⊥ := by
  have : Module.IsTorsionFree ℚ[X] E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr poly_injective
  have : Module.IsTorsionFree ℚ[X] B₀ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b h =>
      poly_injective (congrArg (fun x : B₀ => (x : E)) h)
  have : Module.Finite ℚ[X] B₀ := IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E B₀
  have : IsFractionRing B₀ E := IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  have : IsGaloisGroup G₀ ℚ[X] B₀ := IsGaloisGroup.of_isFractionRing G₀ ℚ[X] B₀ (RatFunc ℚ) E
  let p := Q.under ℚ[X]
  have : p.IsPrime := Ideal.IsPrime.under ℚ[X] Q
  have : Q.LiesOver p := ⟨rfl⟩
  have : CharZero p.ResidueField := charZero_of_injective_ringHom
    ((algebraMap ℚ[X] p.ResidueField).comp Polynomial.C).injective
  have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := G₀) p Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p Q G₀, he] at hc
  by_contra h
  have := (Subgroup.one_lt_card_iff_ne_bot _).2 h
  omega

end SGRDirect.HeckeSqrt

namespace SGRDirect

open HeckeSqrt

set_option maxHeartbeats 1000000 in
/-- ON THE SPOT (provenance (c)): use the second bit of the Hecke twist on
the finite chart. The CM(−24) stabilizer has sign minus, and the CM
implications exclude negative sign over 0. In the sign eigenspace,
squarefree normalization and the inertia indices leave just `27X + 16`.
This is a global function field argument; the manuscript's tame local
equation (L481–526) is not used. -/
theorem heckeSqrtBranchAny_of_y3 (hy : Y3P1j.Y3ToP1j)
    (hT : ObjBridge.TorsionStructure) (hU : ZInQ.LeafPush2.UniformizationExists)
    (hC : HDec.HomUnify.HomLatticeCorr) (hA : QMAutCard) (hS : SerreRigidity3)
    (hW : ALFixedPoints) : HeckeSqrtBranchAny := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN
  classical
  obtain ⟨h, hO, himg, hval⟩ := hN
  let D : Chart Y π E := ⟨h, hO, himg, hval⟩
  let χ := character D h1 hh h2 hT hW
  let B := integralClosure ℚ[X] E
  let p₀ : ℚ[X] := X - C (-16 / 27)
  have hc := cm_objects hy h1
  obtain ⟨P, hP⟩ := hc.2.2
  obtain ⟨i⟩ := cm24_fixed hT hU hC hA P.forget hP
  obtain ⟨ψ, τ, hi, hτ⟩ := exists_inertia_trace_three h1 hh h2 hT P hP i (D := D)
  have hneg : (χ τ : ℚ) = -1 := by
    change sign (index D h1 hh h2 hT τ) = -1
    rw [trace_unique h2 hW (trace_index D h1 hh h2 hT τ) hτ]
    rfl
  obtain ⟨s, f, _, hf, hs, hact⟩ := squarefree_eigenvector χ (fun g => by
    change sign (index D h1 hh h2 hT g) = 1 ∨ sign (index D h1 hh h2 hT g) = -1
    generalize index D h1 hh h2 hT g = k
    fin_cases k <;> decide) τ hneg
  have hbranch := heckeBranch_of ramOfFibreCount HeckeRestCurve.curveChartInf
    (heckeFibreSizes_of hT hA hS hW) hT hc Y Φ π h1 hh h2 E ⟨h, hO, himg, hval⟩
  have hsupport (p : ℚ[X]) (hp : Irreducible p) (hpf : p ∣ f) :
      Ideal.span {p} = Ideal.span {p₀} := by
    by_contra hn
    have : (Ideal.span {p} : Ideal ℚ[X]).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
    have hle : (⊥ : Ideal B).under ℚ[X] ≤ Ideal.span {p} := by
      intro a ha
      have hz : algebraMap ℚ[X] E a = 0 :=
        congrArg (fun b : B => (b : E)) (Ideal.mem_bot.mp ha)
      have : a = 0 := poly_injective (hz.trans (map_zero _).symm)
      simp [this]
    obtain ⟨Q, -, hQ, hQu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {p}) (⊥ : Ideal B) hle
    have := hQ
    have hQu' : Q.under ℚ[X] = Ideal.span {p} := hQu
    apply prime_support χ s f hf hs hact p hp hpf Q hQu'
    by_cases hz : Q.under ℚ[X] = Ideal.span {X - C (0 : ℚ)}
    · obtain ⟨ξ, hξ, hX⟩ := exists_residue_hom Q 0 hz
      intro g hg
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      change sign (index D h1 hh h2 hT g) = 1
      exact trace_sign_at_zero h2 hW (trace_index D h1 hh h2 hT g) ξ (by simpa using hX)
        (hξ ▸ (mem_inertia_iff Q g).1 hg)
    · have hno : ∀ b ∈ ({0, -16 / 27} : Finset ℚ), Q.under ℚ[X] ≠ Ideal.span {X - C b} := by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hz
        · exact fun e => hn (hQu'.symm.trans e)
      rw [inertia_trivial_of_ramificationIdx_eq_one Q (hbranch.1 Q hQ hno)]
      exact bot_le
  have hnonunit : ¬ IsUnit f := by
    intro hu
    have hm := radicand_mem_of_neg χ s f hs hact _ τ ((mem_inertia_iff _ _).2 hi) hneg
    exact (RingHom.ker_isPrime ψ).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hm (hu.map (algebraMap ℚ[X] B)))
  obtain ⟨p, hp, hpf⟩ := WfDvdMonoid.exists_irreducible_factor hnonunit hf.ne_zero
  have hpf₀ : p₀ ∣ f := by
    have hm : f ∈ (Ideal.span {p} : Ideal ℚ[X]) := Ideal.mem_span_singleton.mpr hpf
    rwa [hsupport p hp hpf, Ideal.mem_span_singleton] at hm
  obtain ⟨g, hg⟩ := hpf₀
  have hu : IsUnit g := by
    by_contra hn
    have hg₀ : g ≠ 0 := fun h0 => hf.ne_zero (by rw [hg, h0, mul_zero])
    obtain ⟨p', hp', hpg⟩ := WfDvdMonoid.exists_irreducible_factor hn hg₀
    have hspan := hsupport p' hp' (hg ▸ (dvd_mul_of_dvd_right hpg p₀ : p' ∣ p₀ * g))
    have hpg₀ : p₀ ∣ g := by
      have hm : g ∈ (Ideal.span {p'} : Ideal ℚ[X]) := Ideal.mem_span_singleton.mpr hpg
      rwa [hspan, Ideal.mem_span_singleton] at hm
    obtain ⟨d, hd⟩ := hpg₀
    have hunit := hf p₀ ⟨d, by rw [hg, hd, mul_assoc]⟩
    exact (Polynomial.irreducible_X_sub_C (-16 / 27 : ℚ)).not_isUnit hunit
  obtain ⟨a, ha, rfl⟩ := Polynomial.isUnit_iff.mp hu
  refine ⟨a / 27, s, div_ne_zero ha.ne_zero (by norm_num), hs.trans ?_⟩
  congr 1
  have e : (C 27 * X + C 16 : ℚ[X]) = C 27 * p₀ := by
    dsimp [p₀]
    rw [mul_sub, ← C_mul]
    norm_num
  rw [hg, e, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ (by norm_num : (27 : ℚ) ≠ 0), mul_comm]

/-- ON THE SPOT (provenance (c)): the Hecke sign gives the desired quadratic
subfield, with only the existing `Y₃ → ℙ¹ⱼ` row as an argument. The torsion,
uniformization, lattice, automorphism and rigidity inputs are the kernel theorems
already used by the consumer. -/
theorem heckeSqrtBranchAny_proof (hy : Y3P1j.Y3ToP1j) : SGRDirect.HeckeSqrtBranchAny := by
  let hM := _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  let hG := _root_.ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof
  let hL := _root_.uniformizationLeafAll_proof
  let hU := _root_.AvSplit.Final.h38 hL hM
  let hC := _root_.AvSplit.Final.h69 hL hG
  let hA := HDec.QMSplit.Aut.rows_of_C (HDec.QMLattice.qmCentralizerCMC_of hL hG hM) GR56.t11b
  exact heckeSqrtBranchAny_of_y3 hy (_root_.ObjBridge.torsionStructure_iff.mpr (_root_.AvSplit.Final.h25 hM))
    hU hC hA.1 (HDec.HSyn.serreRigidity3_of_T35_5 hU hC) hA.2.1

end SGRDirect

#print axioms SGRDirect.heckeSqrtBranchAny_proof
