import ZInQKernel.Contrib.OneProof.BShTracesGeometry
import ZInQKernel.Contrib.OneProof.BShFamilySplit
import ZInQKernel.Contrib.OneProof.BShFamilyLattice
import Mathlib.FieldTheory.Galois.Basic

/-! ON THE SPOT (provenance (c)): the normalized prime division polynomial
splits in every local meromorphic germ field. -/

noncomputable section

namespace BShFamily

open Filter Polynomial UpperHalfPlane PeriodPair T5Glue X1Igusa.Weber
open BShTraces ShimuraPointDict LeafModCurves AlgebraicGeometry CategoryTheory
open WeierstrassCurve AfTateLam
open scoped Topology

/-- The short curve with fourth and sixth coefficients `-G*q`. Here `q` is
one quarter; passing it separately lets us work in the ring of functions. -/
def shortModel {R : Type*} [CommRing R] (G q : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, -(G * q), -(G * q)⟩

theorem map_shortModel {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (G q : R) :
    (shortModel G q).map f = shortModel (f G) (f q) := by
  simp [shortModel, WeierstrassCurve.map]

theorem shortModel_quarter {F : Type*} [Field F] (G : F) :
    shortModel G ((4 : F)⁻¹) = curveG G := by
  simp only [shortModel, curveG, div_eq_mul_inv]

/-- The monic normalization of the prime division polynomial. -/
def division {R : Type*} [CommRing R] (E : WeierstrassCurve R) (p : ℕ) (ip : R) : R[X] :=
  C (ip ^ 2) * E.ΨSq p

theorem map_division {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (E : WeierstrassCurve R) (p : ℕ) (ip : R) :
    (division E p ip).map f = division (E.map f) p (f ip) := by
  simp only [division, Polynomial.map_mul, map_C, Polynomial.map_pow, map_pow, map_ΨSq]

theorem division_natDegree_le {R : Type*} [CommRing R]
    (E : WeierstrassCurve R) (p : ℕ) (ip : R) :
    (division E p ip).natDegree ≤ p ^ 2 - 1 := by
  exact (natDegree_C_mul_le _ _).trans (by simpa only [Int.natAbs_natCast] using
    (E.natDegree_ΨSq_le (p : ℤ)))

theorem division_monic {R : Type*} [CommRing R] [Nontrivial R]
    (E : WeierstrassCurve R) (p : ℕ) (ip : R) (h : ip * (p : R) = 1) :
    (division E p ip).Monic := by
  have hc : (division E p ip).coeff (p ^ 2 - 1) = 1 := by
    have hc' := E.coeff_ΨSq (p : ℤ)
    simp only [Int.natAbs_natCast, Int.cast_natCast] at hc'
    rw [division, coeff_C_mul, hc', ← mul_pow, h, one_pow]
  have hd := division_natDegree_le E p ip
  unfold Monic leadingCoeff
  rw [natDegree_eq_of_le_of_coeff_ne_zero hd (hc ▸ one_ne_zero), hc]

theorem division_eval_eq_zero {F : Type*} [Field F] (E : WeierstrassCurve F)
    (p : ℕ) (ip x : F) (h : ip ≠ 0) :
    (division E p ip).eval x = 0 ↔ (E.ΨSq p).eval x = 0 := by
  rw [division, eval_mul, eval_C, mul_eq_zero]
  exact or_iff_right (pow_ne_zero _ h)

/-- The parameter `G` of the normalized short curve as a function of the
model's generic j-coordinate. -/
def modelG {F : Type*} [Field F] (j : F) : F := 27 * j / (j - 1728)

/-- The normalized x-coordinate of the model's mark. -/
def modelX {F : Type*} [Field F] (j t : F) : F := 46656 * t / (j - 1728)

theorem modelG_pointwise (s : ℍ) (h₃ : (pp s).g₃ ≠ 0) :
    modelG (Jf s) = (pp s).g₂ ^ 3 / (pp s).g₃ ^ 2 := by
  have h₃' : G3f s ≠ 0 := by simpa [G3f, ofComplex_apply] using h₃
  suffices h : modelG (Jf s) = G2f s ^ 3 / G3f s ^ 2 by
    simpa only [G2f, G3f, ofComplex_apply] using h
  unfold modelG
  rw [Jf_sub, Jf_eq]
  field_simp [h₃', Dlf_ne (s : ℂ)]
  <;> ring

theorem modelX_pointwise (N : ℕ) (s : ℍ) (h₃ : (pp s).g₃ ≠ 0) :
    modelX (Jf s) (Wf N s) = normX s (1 / (N : ℂ)) := by
  have h₃' : G3f s ≠ 0 := by simpa [G3f, ofComplex_apply] using h₃
  unfold modelX
  rw [Jf_sub, Wf]
  have hh : normX s (1 / (N : ℂ)) = G2f s / G3f s * Pf N s := by
    simp [normX, G2f, G3f, Pf, ofComplex_apply]
  rw [hh]
  field_simp [h₃', Dlf_ne (s : ℂ)]

variable {X : Over SpecQ} [IsIntegral X.left] {N : ℕ} {jX tX : X.left.functionField}
local notation "K" => X.left.functionField

local instance : CharZero K := charZero_of_injective_ringHom (baseMap X).injective

theorem restrict_modelGenerators (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ) :
    restrict τ (meromorphicFieldGerm hN hG τ jX) =
      ((fun s : ℍ => Jf s) : Germ (𝓝[≠] τ) ℂ) ∧
    restrict τ (meromorphicFieldGerm hN hG τ tX) =
      ((fun s : ℍ => Wf N s) : Germ (𝓝[≠] τ) ℂ) := by
  obtain ⟨hj, ht⟩ := fieldGerm_coordinates hN hG τ
  exact ⟨restrict_eq_coe hj, restrict_eq_coe ht⟩

theorem restrict_modelG (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ) :
    restrict τ (meromorphicFieldGerm hN hG τ (modelG jX)) =
      ((fun s : ℍ => (pp s).g₂ ^ 3 / (pp s).g₃ ^ 2) : Germ (𝓝[≠] τ) ℂ) := by
  have h := (restrict_modelGenerators hN hG τ).1
  have hn : ∀ᶠ s : ℍ in 𝓝[≠] τ, Jf s - 1728 ≠ 0 := by
    filter_upwards [eventually_good τ] with s hs
    rw [Jf_sub]
    exact div_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (by simpa [G3f, ofComplex_apply] using hs.2))) (Dlf_ne (s : ℂ))
  rw [modelG, map_div₀, restrict_div
    (show restrict τ (meromorphicFieldGerm hN hG τ (27 * jX)) =
      ((fun s : ℍ => 27 * Jf s) : Germ (𝓝[≠] τ) ℂ) by simp only [map_mul, map_ofNat, h]; rfl)
    (show restrict τ (meromorphicFieldGerm hN hG τ (jX - 1728)) =
      ((fun s : ℍ => Jf s - 1728) : Germ (𝓝[≠] τ) ℂ) by simp only [map_sub, map_ofNat, h]; rfl) hn]
  exact Germ.coe_eq.mpr ((eventually_good τ).mono fun s hs => modelG_pointwise s hs.2)

theorem restrict_modelX (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ) :
    restrict τ (meromorphicFieldGerm hN hG τ (modelX jX tX)) =
      ((fun s : ℍ => normX s (1 / (N : ℂ))) : Germ (𝓝[≠] τ) ℂ) := by
  obtain ⟨hj, ht⟩ := restrict_modelGenerators hN hG τ
  have hn : ∀ᶠ s : ℍ in 𝓝[≠] τ, Jf s - 1728 ≠ 0 := by
    filter_upwards [eventually_good τ] with s hs
    rw [Jf_sub]
    exact div_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (by simpa [G3f, ofComplex_apply] using hs.2))) (Dlf_ne (s : ℂ))
  rw [modelX, map_div₀, restrict_div
    (show restrict τ (meromorphicFieldGerm hN hG τ (46656 * tX)) =
      ((fun s : ℍ => 46656 * Wf N s) : Germ (𝓝[≠] τ) ℂ) by simp only [map_mul, map_ofNat, ht]; rfl)
    (show restrict τ (meromorphicFieldGerm hN hG τ (jX - 1728)) =
      ((fun s : ℍ => Jf s - 1728) : Germ (𝓝[≠] τ) ℂ) by simp only [map_sub, map_ofNat, hj]; rfl) hn]
  exact Germ.coe_eq.mpr ((eventually_good τ).mono fun s hs => modelX_pointwise N s hs.2)

/-- Base change to every meromorphic germ field splits the generic prime
division polynomial over the prescribed embedding of the model field. -/
theorem splits_local (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    {p : ℕ} (hp : p.Prime) (τ : ℍ) :
    (((curveG (modelG jX)).ΨSq p).map (meromorphicFieldGerm hN hG τ)).Splits := by
  classical
  let m := meromorphicFieldGerm hN hG τ
  let d := p ^ 2 - 1
  let E := curveG (modelG jX)
  let q : ℍ → ℂ := fun _ => (4 : ℂ)⁻¹
  let ip : ℍ → ℂ := fun _ => (p : ℂ)⁻¹
  let G : ℍ → ℂ := fun s => (pp s).g₂ ^ 3 / (pp s).g₃ ^ 2
  let F := shortModel G q
  let A := division F p ip
  let P := (division E p ((p : K)⁻¹)).map m
  have hn : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hA : A.Monic := division_monic F p ip (funext fun _ => inv_mul_cancel₀ hn)
  let e := Germ.coeRingHom (𝓝[≠] τ) (R := ℂ)
  have hq : e q = restrict τ (m ((4 : K)⁻¹)) := by
    rw [← one_div, map_div₀, restrict_div_eq]
    simp only [map_one, map_ofNat]
    change (q : Germ (𝓝[≠] τ) ℂ) = ((fun _ : ℍ => 1 / (4 : ℂ)) : Germ (𝓝[≠] τ) ℂ)
    simp only [q, one_div]
  have hip : e ip = restrict τ (m ((p : K)⁻¹)) := by
    rw [← one_div, map_div₀, restrict_div_eq]
    simp only [map_one, map_natCast]
    change (ip : Germ (𝓝[≠] τ) ℂ) = ((fun _ : ℍ => 1 / (p : ℂ)) : Germ (𝓝[≠] τ) ℂ)
    simp only [ip, one_div]
  have he : A.map e = P.map (restrict τ) := by
    change (division (shortModel G q) p ip).map e =
      ((division E p ((p : K)⁻¹)).map m).map (restrict τ)
    rw [map_division, map_shortModel,
      show E = shortModel (modelG jX) ((4 : K)⁻¹) from (shortModel_quarter _).symm]
    simp only [map_division, map_shortModel]
    have hg := restrict_modelG hN hG τ
    change restrict τ (m (modelG jX)) = e G at hg
    rw [hq, hip, hg]
  choose r hr using fun (a : Line p × Multiple p) => exists_torsion_section hp a.1 a.2 τ
  let f : Line p × Multiple p → ℍ → ℂ :=
    fun a s => normX s ((a.2.val.val : ℂ) * generator p a.1 s)
  have hsec (a : Line p × Multiple p) :
      restrict τ (r a) = (f a : Germ (𝓝[≠] τ) ℂ) := by
    simpa [f, ofComplex_apply] using restrict_eq_coe (hr a)
  have hP := splits_of_eventually_exhaustion (restrict τ) P A hA he r f hsec d (by
    filter_upwards [eventually_good τ] with s hs
    change (A.map _).natDegree ≤ d ∧ ∀ x, (A.map _).eval x = 0 → _
    have hsA : A.map (Pi.evalRingHom (fun _ : ℍ => ℂ) s) =
        division (curveG (G s)) p ((p : ℂ)⁻¹) := by
      rw [show A = division (shortModel G q) p ip by rfl, map_division, map_shortModel]
      exact congrArg (fun C => division C p ((p : ℂ)⁻¹)) (shortModel_quarter _)
    rw [hsA]
    refine ⟨division_natDegree_le _ _ _, fun x hx => ?_⟩
    obtain ⟨i,k,hh⟩ := (eval_division_eq_zero_iff hp s hs.1 hs.2 x).mp
      ((division_eval_eq_zero _ _ _ _ (inv_ne_zero hn)).mp hx)
    exact ⟨(i,k), hh⟩)
  have hdvd : ((E.ΨSq p).map m) ∣ P := by
    refine ⟨(Polynomial.C (((p : K)⁻¹) ^ 2)).map m, ?_⟩
    rw [show P = (Polynomial.C (((p : K)⁻¹) ^ 2) * E.ΨSq p).map m by rfl,
      Polynomial.map_mul, mul_comm]
  exact hP.of_dvd (monic_of_injective (restrict τ).injective (he ▸ hA.map _)).ne_zero hdvd

#print axioms map_shortModel
#print axioms shortModel_quarter
#print axioms map_division
#print axioms division_natDegree_le
#print axioms division_monic
#print axioms division_eval_eq_zero
#print axioms modelG_pointwise
#print axioms modelX_pointwise
#print axioms restrict_modelGenerators
#print axioms restrict_modelG
#print axioms restrict_modelX
#print axioms splits_local

end BShFamily
