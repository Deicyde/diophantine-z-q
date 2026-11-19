import ZInQKernel.Contrib.OneProof.ShimuraOrbitsPrime
import ZInQKernel.Contrib.OneProof.ShimuraHeckeJ
import ZInQKernel.Contrib.OneProof.SameDimFinite

/-! The only open input of the fixed Shimura Hecke bridge is the analytic point dictionary. -/

noncomputable section

namespace ShimuraSteps

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar R16Thm1
open AfTateLam AfTateLam.HeckePin CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

/-- For a model in the Hecke bridge, each upper-half-plane parameter has exactly
one complex point satisfying the finite-value tests of `AtTau`. -/
def PointDictionary : Prop :=
  ∀ (N : ℕ), 2 ≤ N →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
      IsCurve X → IsX1Gen N X jX tX →
      ∀ τ : ℍ, ∃! x : CPt X, AtTau N jX tX x τ

namespace Orbits

variable {N : ℕ} {X : Over SpecQ} [IsIntegral X.left] {jX tX : X.left.functionField}
  {J : AbVar ℚ} (aj : X ⟶ J.X)

private def orbitPoint (h : ∀ τ : ℍ, ∃! x : CPt X, AtTau N jX tX x τ) : Orb N → CPt X :=
  Quotient.lift (fun τ => (h τ).exists.choose) (by
    intro τ τ' he
    obtain ⟨g, rfl⟩ : ∃ g : Gamma1 N, g • τ' = τ := he
    obtain ⟨hg, hg'⟩ := mem_Gamma1_iff.mp g.property
    exact (h τ').unique
      ((HeckeJ.tauGammaOne N jX tX g (mem_Gamma0_iff_dvd.mp hg) hg' τ' _).1
        (h (g • τ')).exists.choose_spec) (h τ').exists.choose_spec)

private theorem orbitPoint_eq (h : ∀ τ : ℍ, ∃! x : CPt X, AtTau N jX tX x τ)
    (τ : ℍ) {x : CPt X} (hx : AtTau N jX tX x τ) : orbitPoint h (orb N τ) = x :=
  (h τ).unique (h τ).exists.choose_spec hx

private def clsOrb (x : Orb N → CPt X) : Divisors N →ₗ[ℤ] Additive (J.Pt ℂ) :=
  Finsupp.linearCombination ℤ (fun q => Additive.ofMul (ajC aj (x q)))

private theorem clsOrb_point (x : Orb N → CPt X) (q : Orb N) :
    clsOrb aj x (point q) = Additive.ofMul (ajC aj (x q)) := by simp [clsOrb, point]

private def Compatible (x : Orb N → CPt X) (S : Module.End ℤ (Divisors N))
    (s : AbVar.End J) : Prop :=
  ∀ τ τ' : ℍ, endA s (clsOrb aj x (point (orb N τ) - point (orb N τ'))) =
    clsOrb aj x (S (point (orb N τ) - point (orb N τ')))

private theorem triAct_eq_shift {N n : ℕ} (a : Div N n) (b : ℕ) (τ : ℍ) :
    triAct a.val b (n / a.val) τ = shiftDiv (n / a.val) b (mulNat a.val τ) := by
  apply UpperHalfPlane.ext
  rw [coe_triAct _ _ _ (div_spec a).1 (div_spec a).2.1,
    coe_shiftDiv _ _ (div_spec a).2.1, coe_mulNat _ (div_spec a).1]

private theorem isXi_iff_compatible
    (h : ∀ τ : ℍ, ∃! x : CPt X, AtTau N jX tX x τ) (n : ℕ) (s : AbVar.End J) :
    IsXi (N := N) jX tX aj n s ↔ Compatible aj (orbitPoint h) (R N n) s := by
  have eq (g : Div N n → SL(2, ℤ))
      (hg : ∀ a, (N : ℤ) ∣ g a 1 0 ∧ ((g a 1 1 : ℤ) : ZMod N) = (a.val : ZMod N))
      (τ τ' : ℍ) (x x' : CPt X) (y y' : (a : Div N n) → Fin (n / a.val) → CPt X)
      (hx : AtTau N jX tX x τ) (hx' : AtTau N jX tX x' τ')
      (hy : ∀ a b, AtTau N jX tX (y a b) (g a • triAct a.val b (n / a.val) τ))
      (hy' : ∀ a b, AtTau N jX tX (y' a b) (g a • triAct a.val b (n / a.val) τ')) :
      (endA s (clsOrb aj (orbitPoint h) (point (orb N τ) - point (orb N τ'))) =
        clsOrb aj (orbitPoint h) (R N n (point (orb N τ) - point (orb N τ')))) ↔
        endC s (ajC aj x / ajC aj x') = ∏ a, ∏ b, ajC aj (y a b) / ajC aj (y' a b) := by
    let G (a : Div N n) : Gamma0 N := ⟨g a, mem_Gamma0_iff_dvd.mpr (hg a).1⟩
    have hG : ∀ a, Gamma0Map N (G a) = (a.val : ZMod N) := fun a => (hg a).2
    rw [map_sub (clsOrb aj (orbitPoint h)), clsOrb_point, clsOrb_point,
      orbitPoint_eq h _ hx, orbitPoint_eq h _ hx', ← ofMul_div, endA_apply]
    simp only [map_sub, R_point, sumAt_lifts G hG, map_sum, term, clsOrb_point]
    simp only [G, fun a b => orbitPoint_eq h _ (hy a b), fun a b => orbitPoint_eq h _ (hy' a b)]
    change Additive.ofMul (endC s (ajC aj x / ajC aj x')) =
        (∑ a, ∑ b, Additive.ofMul (ajC aj (y a b))) -
          (∑ a, ∑ b, Additive.ofMul (ajC aj (y' a b))) ↔ _
    let P : J.Pt ℂ := ∏ a, ∏ b, ajC aj (y a b) / ajC aj (y' a b)
    have e : Additive.ofMul (endC s (ajC aj x / ajC aj x')) = Additive.ofMul P ↔
        endC s (ajC aj x / ajC aj x') = P := Additive.ofMul.injective.eq_iff
    change _ ↔ endC s (ajC aj x / ajC aj x') = P
    simpa only [P, ofMul_prod, ofMul_div, Finset.sum_sub_distrib] using e
  constructor
  · intro hs τ τ'
    let g (a : Div N n) := (repLift a : SL(2, ℤ))
    have hg (a : Div N n) : (N : ℤ) ∣ g a 1 0 ∧
        ((g a 1 1 : ℤ) : ZMod N) = (a.val : ZMod N) :=
      ⟨mem_Gamma0_iff_dvd.mp (repLift a).property, lift_residue _ _ _⟩
    choose x hx using fun w => (h w).exists
    let y (w : ℍ) (a : Div N n) (b : Fin (n / a.val)) :=
      x (g a • triAct a.val b (n / a.val) w)
    have hy (w : ℍ) (a : Div N n) (b : Fin (n / a.val)) :
        AtTau N jX tX (y w a b) (g a • triAct a.val b (n / a.val) w) := hx _
    have hz (w : ℍ) (a : Div N n) (b : Fin (n / a.val)) :
        AtTau N jX tX (y w a b) (g a • shiftDiv (n / a.val) b (mulNat a.val w)) := by
      simpa only [triAct_eq_shift] using hy w a b
    exact (eq g hg τ τ' (x τ) (x τ') (y τ) (y τ') (hx τ) (hx τ') (hy τ) (hy τ')).2
      (hs g hg τ τ' (x τ) (x τ') (y τ) (y τ') (hx τ) (hx τ') (hz τ) (hz τ'))
  · intro hs g hg τ τ' x x' y y' hx hx' hy hy'
    exact (eq g hg τ τ' x x' y y' hx hx'
      (fun a b => by simpa only [triAct_eq_shift] using hy a b)
      (fun a b => by simpa only [triAct_eq_shift] using hy' a b)).1 (hs τ τ')

private theorem compatible_diamond
    (h : ∀ τ : ℍ, ∃! x : CPt X, AtTau N jX tX x τ)
    {u : (ZMod N)ˣ} {s : AbVar.End J} (hs : IsDiamond N jX tX aj u s)
    (g : Gamma0 N) (hg : Gamma0Map N g = u) :
    Compatible aj (orbitPoint h) (diamond g) s := by
  intro τ τ'
  choose x hx using fun w => (h w).exists
  have hxO (w : ℍ) := orbitPoint_eq h w (hx w)
  rw [map_sub (clsOrb aj (orbitPoint h)), clsOrb_point, clsOrb_point, hxO τ, hxO τ',
    ← ofMul_div, endA_apply]
  simp only [map_sub, diamond_point, clsOrb_point, hxO, ← ofMul_div]
  rw [hs g (mem_Gamma0_iff_dvd.mp g.property) hg τ τ' _ _ _ _
    (hx τ) (hx τ') (hx _) (hx _)]

private theorem image_R_diff (n : ℕ) (τ τ' : ℍ) :
    R N n (point (orb N τ) - point (orb N τ')) =
      ∑ i : Rep N n,
        (point (orb N ((repLift i.1 : SL(2, ℤ)) • triAct i.1.val i.2.val (n / i.1.val) τ)) -
         point (orb N ((repLift i.1 : SL(2, ℤ)) • triAct i.1.val i.2.val (n / i.1.val) τ'))) := by
  simp only [map_sub, R_point, sumAt, term, Finset.sum_sub_distrib]

private theorem compatible_apply_R_diff (x : Orb N → CPt X)
    {S : Module.End ℤ (Divisors N)} {s : AbVar.End J}
    (hs : Compatible aj x S s) (n : ℕ) (τ τ' : ℍ) :
    endA s (clsOrb aj x (R N n (point (orb N τ) - point (orb N τ')))) =
      clsOrb aj x (S (R N n (point (orb N τ) - point (orb N τ')))) := by
  unfold Compatible at hs
  rw [image_R_diff]
  simp only [map_sum, hs]

theorem isXi_mul_coprime
    (h : ∀ τ : ℍ, ∃! x : CPt X, AtTau N jX tX x τ) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
    {s t : AbVar.End J} (hs : IsXi (N := N) jX tX aj m s) (ht : IsXi (N := N) jX tX aj n t) :
    IsXi (N := N) jX tX aj (m * n) (s * t) := by
  rw [isXi_iff_compatible aj h] at hs ht ⊢
  unfold Compatible at hs ht ⊢
  intro τ τ'
  rw [endA_mul, ht, compatible_apply_R_diff aj _ hs]
  simp only [map_sub, coprime_count_basis hm hn hmn]

private theorem endA_sub' (s t : AbVar.End J) (x : Additive (J.Pt ℂ)) :
    endA (s - t) x = endA s x - endA t x := by
  apply eq_sub_of_add_eq
  rw [← endA_add, sub_add_cancel]

theorem isXi_good_step
    (h : ∀ τ : ℍ, ∃! x : CPt X, AtTau N jX tX x τ)
    (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N) (k : ℕ)
    {T D s t : AbVar.End J} (hT : IsHeckeT N jX tX aj p T)
    (hD : IsDiamond N jX tX aj (unitOf N p.2 hpN) D)
    (hs : IsXi (N := N) jX tX aj ((p : ℕ) ^ k) s)
    (ht : IsXi (N := N) jX tX aj ((p : ℕ) ^ (k + 1)) t) :
    IsXi (N := N) jX tX aj ((p : ℕ) ^ (k + 2)) (T * t - ((p : ℕ) : AbVar.End J) * D * s) := by
  have hT' := HeckeJ.isXi_prime_of_isHeckeT p hT
  rw [isXi_iff_compatible aj h] at hs ht hT' ⊢
  have hc := p.2.coprime_iff_not_dvd.mpr hpN
  let g := lift N p hc
  have hg : Gamma0Map N g = (unitOf N p.2 hpN : ZMod N) := by
    simp [g, unitOf, ZMod.coe_unitOfCoprime]
  have hD' := compatible_diamond aj h hD g hg
  unfold Compatible at hs ht hT' ⊢
  intro τ τ'
  have hcount :
      R N p (R N ((p : ℕ) ^ (k + 1)) (point (orb N τ) - point (orb N τ'))) =
        R N ((p : ℕ) ^ (k + 2)) (point (orb N τ) - point (orb N τ')) +
        (p : ℕ) • diamond g (R N ((p : ℕ) ^ k) (point (orb N τ) - point (orb N τ'))) := by
    simp only [map_sub, good_count_basis p.2 hc, map_nsmul, smul_sub, g]
    abel
  rw [endA_sub', endA_mul, ht, compatible_apply_R_diff aj _ hT', hcount]
  rw [endA_mul, endA_mul, hs, compatible_apply_R_diff aj _ hD']
  rw [show (((p : ℕ) : AbVar.End J)) = (((p : ℕ) : ℤ) : AbVar.End J) by simp,
    endA_intCast, map_add, map_nsmul]
  simp

#print axioms orbitPoint_eq
#print axioms clsOrb_point
#print axioms triAct_eq_shift
#print axioms isXi_iff_compatible
#print axioms compatible_diamond
#print axioms image_R_diff
#print axioms compatible_apply_R_diff
#print axioms isXi_mul_coprime
#print axioms endA_sub'
#print axioms isXi_good_step

end Orbits

/-- The triangular orbit identities discharge both composite action laws in the fixed bridge. -/
theorem shimuraHeckeRelations_of_pointDictionary (h : PointDictionary) : ShimuraHeckeRelations := by
  intro N hN X _ jX tX hC hG P₀ J aj hJ tp δ ht hd
  have hP : X1TauPoints := fun N hN X _ jX tX hC hG τ => (h N hN X jX tX hC hG τ).exists
  have hX := h N hN X jX tX hC hG
  refine HeckeJ.exists_xi_of_compositeActions hP hN hC hG hJ
    (fun τ _ _ hx hy => (hX τ).unique hx hy) ht ?_ ?_
  · intro m n hm hn hmn s t hs ht
    exact Orbits.isXi_mul_coprime aj hX hm hn hmn hs ht
  · intro p hpN k s t hs ht'
    exact Orbits.isXi_good_step aj hX p hpN k (ht p) (hd _) hs ht'

theorem shimuraThm1Af_of_printed_pointDictionary (hPrint : ShimuraThm1AsPrinted)
    (hPoint : PointDictionary) : R16Thm1b.ShimuraThm1Af :=
  shimuraThm1Af_of_printed' hPrint (shimuraHeckeRelations_of_pointDictionary hPoint)

#print axioms shimuraHeckeRelations_of_pointDictionary
#print axioms shimuraThm1Af_of_printed_pointDictionary

end ShimuraSteps
