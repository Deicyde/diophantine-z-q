import ZInQKernel.Contrib.OneProof.BShFamilyLocal
import ZInQKernel.Contrib.OneProof.BShFamilyKernels
import ZInQKernel.Contrib.OneProof.BShFamilyResidues

/-! ON THE SPOT (provenance (c)): match the roots and multiplication over
the local meromorphic field with the analytic torsion atlas. -/

noncomputable section

namespace BShFamily

open Filter Polynomial UpperHalfPlane PeriodPair T5Glue X1Igusa.Weber
open BShTraces ShimuraPointDict LeafModCurves AlgebraicGeometry CategoryTheory
open WeierstrassCurve AfTateLam
open scoped Topology

/-- The normalized x-coordinate of a fixed analytic torsion section. -/
def sectionAt {p : ℕ} (hp : p.Prime) (τ : ℍ) (i : Line p) (k : Multiple p) :
    MeromorphicGerm (τ : ℂ) :=
  (exists_torsion_section hp i k τ).choose

theorem restrict_sectionAt {p : ℕ} (hp : p.Prime) (τ : ℍ) (i : Line p) (k : Multiple p) :
    restrict τ (sectionAt hp τ i k) =
      ((fun s : ℍ => normX s ((k.val.val : ℂ) * generator p i s)) : Germ (𝓝[≠] τ) ℂ) := by
  simpa only [sectionAt, ofComplex_apply] using
    restrict_eq_coe (exists_torsion_section hp i k τ).choose_spec

/-- Evaluating a polynomial of functions commutes with passage to a germ. -/
theorem eval_germ_polynomial (τ : ℍ) (P : (ℍ → ℂ)[X]) (f : ℍ → ℂ) :
    (P.map (Germ.coeRingHom (𝓝[≠] τ))).eval (f : Germ (𝓝[≠] τ) ℂ) =
      ((fun s : ℍ => (P.map (Pi.evalRingHom (fun _ : ℍ => ℂ) s)).eval (f s)) :
        Germ (𝓝[≠] τ) ℂ) := by
  rw [show (f : Germ (𝓝[≠] τ) ℂ) = Germ.coeRingHom (𝓝[≠] τ) f from rfl,
    Polynomial.eval_map, eval₂_at_apply]
  apply Germ.coe_eq.mpr
  refine Filter.Eventually.of_forall fun s => ?_
  let e := Pi.evalRingHom (fun _ : ℍ => ℂ) s
  change e (P.eval f) = (P.map e).eval (e f)
  rw [Polynomial.eval_map, eval₂_at_apply]

variable {X : Over SpecQ} [IsIntegral X.left] {N : ℕ} {jX tX : X.left.functionField}
local notation "K" => X.left.functionField

/-- The generic model curve over the prescribed local field embedding. -/
def localCurve (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ) :
    WeierstrassCurve (MeromorphicGerm (τ : ℂ)) :=
  (curveG (modelG jX)).map (meromorphicFieldGerm hN hG τ)

theorem restrict_local_poly_eval
    (D : ∀ {R : Type} [CommRing R], WeierstrassCurve R → R[X])
    (hD : ∀ {R S : Type} [CommRing R] [CommRing S] (m : R →+* S) (W : WeierstrassCurve R),
      D (W.map m) = (D W).map m)
    (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ)
    {a : MeromorphicGerm (τ : ℂ)} {f : ℍ → ℂ}
    (ha : restrict τ a = (f : Germ (𝓝[≠] τ) ℂ)) :
    restrict τ ((D (localCurve hN hG τ)).eval a) =
      ((fun s : ℍ => (D (curveG ((pp s).g₂ ^ 3 / (pp s).g₃ ^ 2))).eval (f s)) :
        Germ (𝓝[≠] τ) ℂ) := by
  let G : ℍ → ℂ := fun s => (pp s).g₂ ^ 3 / (pp s).g₃ ^ 2
  let q : ℍ → ℂ := fun _ => (4 : ℂ)⁻¹
  let E := shortModel G q
  let c := Germ.coeRingHom (𝓝[≠] τ) (R := ℂ)
  have hq : c q = restrict τ ((4 : MeromorphicGerm (τ : ℂ))⁻¹) := by
    symm
    rw [← one_div, restrict_div_eq, map_one, map_ofNat]
    change ((fun _ : ℍ => 1 / (4 : ℂ)) : Germ (𝓝[≠] τ) ℂ) = ↑q
    simp only [q, one_div]
  have hE : (localCurve hN hG τ).map (restrict τ) = E.map c := by
    rw [localCurve, ← shortModel_quarter, map_shortModel, map_shortModel,
      show E = shortModel G q from rfl, map_shortModel,
      hq, map_inv₀, map_ofNat]
    have hg := restrict_modelG hN hG τ
    change restrict τ (meromorphicFieldGerm hN hG τ (modelG jX)) = c G at hg
    rw [hg]
  change restrict τ ((D (localCurve hN hG τ)).eval a) = _
  rw [← eval₂_at_apply, ← Polynomial.eval_map, ha, ← hD, hE, hD, eval_germ_polynomial]
  congr 1
  funext s
  rw [← hD, show E = shortModel G q from rfl, map_shortModel, ← shortModel_quarter]
  rfl

/-- The chosen root germs are exhaustive and all are roots. -/
theorem local_roots (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {p : ℕ} (hp : p.Prime)
    (τ : ℍ) (a : MeromorphicGerm (τ : ℂ)) :
    ((localCurve hN hG τ).ΨSq p).eval a = 0 ↔
      ∃ i : Line p, ∃ k : Multiple p, a = sectionAt hp τ i k := by
  classical
  have E {a : MeromorphicGerm (τ : ℂ)} {f : ℍ → ℂ} (hf : restrict τ a = (f : Germ (𝓝[≠] τ) ℂ)) :
      restrict τ (((localCurve hN hG τ).ΨSq p).eval a) =
        ((fun s : ℍ => ((curveG ((pp s).g₂ ^ 3 / (pp s).g₃ ^ 2)).ΨSq p).eval (f s)) :
          Germ (𝓝[≠] τ) ℂ) :=
    restrict_local_poly_eval (fun W => W.ΨSq p) (fun m W => map_ΨSq W m p) hN hG τ hf
  constructor
  · intro h
    obtain ⟨f, hf⟩ := Quotient.exists_rep (restrict τ a)
    change (f : Germ (𝓝[≠] τ) ℂ) = _ at hf
    have hd := E hf.symm
    rw [h, map_zero] at hd
    have hzero := Germ.coe_eq.mp hd.symm
    by_contra! hs
    have hne (b : Line p × Multiple p) : ∀ᶠ s in 𝓝[≠] τ,
        f s - normX s ((b.2.val.val : ℂ) * generator p b.1 s) ≠ 0 := by
      apply restrict_eventually_ne_zero (a := a - sectionAt hp τ b.1 b.2) ?_
        (sub_ne_zero.mpr (hs b.1 b.2))
      rw [map_sub, ← hf, restrict_sectionAt]
      rfl
    have hbad := (eventually_good τ).and (hzero.and (Filter.eventually_all.mpr hne))
    obtain ⟨s, hg, h0, hn⟩ := hbad.exists
    obtain ⟨i,k,hik⟩ := (eval_division_eq_zero_iff hp s hg.1 hg.2 (f s)).mp h0
    exact hn (i,k) (sub_eq_zero.mpr hik)
  · rintro ⟨i,k,rfl⟩
    apply (restrict τ).injective
    rw [E (restrict_sectionAt hp τ i k), map_zero]
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_good τ] with s hs
    exact (eval_division_eq_zero_iff hp s hs.1 hs.2 _).mpr ⟨i,k,rfl⟩

/-- Distinct lines have disjoint nonzero root germs. -/
theorem line_eq_of_sectionAt_eq {p : ℕ} (hp : p.Prime) (τ : ℍ)
    {i j : Line p} {k l : Multiple p}
    (h : sectionAt hp τ i k = sectionAt hp τ j l) : i = j := by
  have he := congrArg (restrict τ) h
  rw [restrict_sectionAt, restrict_sectionAt] at he
  obtain ⟨s, hs, he'⟩ := ((eventually_good τ).and (Germ.coe_eq.mp he)).exists
  exact line_eq_of_coordinates_eq hp s hs.1 hs.2 he'

theorem restrict_mulX (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    (τ : ℍ) (n : ℤ) {a : MeromorphicGerm (τ : ℂ)} {f : ℍ → ℂ}
    (ha : restrict τ a = (f : Germ (𝓝[≠] τ) ℂ)) :
    restrict τ (mulX (localCurve hN hG τ) n a) =
      ((fun s : ℍ => mulX (curveG ((pp s).g₂ ^ 3 / (pp s).g₃ ^ 2)) n (f s)) :
        Germ (𝓝[≠] τ) ℂ) := by
  rw [mulX, restrict_div_eq,
    restrict_local_poly_eval (fun W => W.Φ n) (fun m W => map_Φ W m n) hN hG τ ha,
    restrict_local_poly_eval (fun W => W.ΨSq n) (fun m W => map_ΨSq W m n) hN hG τ ha]
  rfl

/-- Multiplication transports the individual local germs by the same
permutation as on the pointwise torsion sections. -/
theorem mulX_sectionAt (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {p : ℕ} (hp : p.Prime)
    (τ : ℍ) (i : Line p) (k l : Multiple p) :
    mulX (localCurve hN hG τ) l.val.val (sectionAt hp τ i k) =
      sectionAt hp τ i (multiplePerm hp k l) := by
  apply (restrict τ).injective
  rw [restrict_mulX hN hG τ _ (restrict_sectionAt hp τ i k), restrict_sectionAt]
  exact Germ.coe_eq.mpr ((eventually_good τ).mono fun s hs =>
    mulX_of_multiple hp i k l s hs.1 hs.2)

#print axioms restrict_sectionAt
#print axioms eval_germ_polynomial
#print axioms restrict_local_poly_eval
#print axioms local_roots
#print axioms line_eq_of_sectionAt_eq
#print axioms restrict_mulX
#print axioms mulX_sectionAt

end BShFamily
