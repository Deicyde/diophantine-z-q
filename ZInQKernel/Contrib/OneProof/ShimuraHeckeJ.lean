import ZInQKernel.Contrib.OneProof.ShimuraSteps
import ZInQKernel.Contrib.OneProof.ShimuraHeckeJDetection
import ZInQKernel.Contrib.OneProof.ShimuraHeckeJTau

/-!
# Divisor class calculations for the Shimura Hecke bridge

The results here use the exact indexing and point predicate of `ShimuraSteps.IsXi`.
The unresolved inputs are recorded in `docs/research/shimura-hecke-j.md`.
-/

noncomputable section

namespace ShimuraSteps.HeckeJ

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar R16Thm1
open AfTateLam AfTateLam.HeckePin
open scoped MatrixGroups

variable {N : ℕ} {X : Over SpecQ} [IsIntegral X.left] {jX tX : X.left.functionField}
  {J : AbVar ℚ} {aj : X ⟶ J.X}

private abbrev D (N n : ℕ) := ↥(n.divisors.filter fun a => a.Coprime N)

private theorem mem_D_one (hn : n ≠ 0) : 1 ∈ n.divisors.filter (·.Coprime N) := by
  simp [Nat.mem_divisors, hn]

private def dOne (N n : ℕ) (hn : n ≠ 0) : D N n := ⟨1, mem_D_one hn⟩

private theorem exists_xi_matrices (N n : ℕ) :
    ∃ g : D N n → SL(2, ℤ),
      ∀ a, (N : ℤ) ∣ g a 1 0 ∧ ((g a 1 1 : ℤ) : ZMod N) = (a.val : ZMod N) := by
  have h (a : D N n) : ∃ g : SL(2, ℤ),
      (N : ℤ) ∣ g 1 0 ∧ ((g 1 1 : ℤ) : ZMod N) = (a.val : ZMod N) := by
    have ha := (Finset.mem_filter.1 a.property).2
    obtain ⟨g, h₁, h₂⟩ := exists_gamma N (a.val : ℤ)
      (Int.isCoprime_iff_gcd_eq_one.2 (by simpa using ha))
    exact ⟨g, h₁, by simpa using h₂⟩
  choose g hg using h
  exact ⟨g, hg⟩

/-- Comparing the formulas only needs a single legal family of matrix lifts and one choice
of output points at each parameter. No uniqueness of those points is needed for this step. -/
theorem isXi_agree (hx : TauPts N jX tX) {n : ℕ} {s t : AbVar.End J}
    (hs : IsXi (N := N) jX tX aj n s) (ht : IsXi (N := N) jX tX aj n t)
    (τ τ' : UpperHalfPlane) (x x' : CPt X) (hxτ : AtTau N jX tX x τ)
    (hxτ' : AtTau N jX tX x' τ') :
    endC s (ajC aj x / ajC aj x') = endC t (ajC aj x / ajC aj x') := by
  obtain ⟨g, hg⟩ := exists_xi_matrices N n
  choose y hy using hx
  exact (hs g hg τ τ' x x' (fun _ _ => y _) (fun _ _ => y _) hxτ hxτ'
      (fun _ _ => hy _) (fun _ _ => hy _)).trans
    (ht g hg τ τ' x x' (fun _ _ => y _) (fun _ _ => y _) hxτ hxτ'
      (fun _ _ => hy _) (fun _ _ => hy _)).symm

/-- The existing pointed Albanese argument gives pinning at every composite index. -/
theorem isXi_unique (hP : X1TauPoints) (hN : 2 ≤ N)
    (hC : IsCurve X) (hG : IsX1Gen N X jX tX) {P₀ : RatPt X}
    (hJ : IsJacobian X P₀ J aj) {n : ℕ} {s t : AbVar.End J}
    (hs : IsXi (N := N) jX tX aj n s) (ht : IsXi (N := N) jX tX aj n t) :
    s = t :=
  end_eq_of_classes (constOnTauPoints_of_realization hP) hN hC hG hJ s t
    (isXi_agree (hP N hN X jX tX hC hG) hs ht)

/-- The correspondence consisting only of the representatives `τ ↦ (τ + b)/n`. -/
def IsUpper (N : ℕ) (jX tX : X.left.functionField) (aj : X ⟶ J.X)
    (n : ℕ) (t : AbVar.End J) : Prop :=
  ∀ (τ τ' : UpperHalfPlane) (x x' : CPt X) (y y' : Fin n → CPt X),
    AtTau N jX tX x τ → AtTau N jX tX x' τ' →
    (∀ b, AtTau N jX tX (y b) (shiftDiv n b τ)) →
    (∀ b, AtTau N jX tX (y' b) (shiftDiv n b τ')) →
    endC t (ajC aj x / ajC aj x') = ∏ b, ajC aj (y b) / ajC aj (y' b)

private theorem mulNat_one (τ : UpperHalfPlane) : mulNat 1 τ = τ := by
  apply UpperHalfPlane.ext
  simp [mulNat]

private theorem shiftDiv_one_zero (τ : UpperHalfPlane) : shiftDiv 1 0 τ = τ := by
  apply UpperHalfPlane.ext
  simp [shiftDiv]

private theorem shiftDiv_shiftDiv {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i j : ℕ)
    (τ : UpperHalfPlane) :
    shiftDiv m i (shiftDiv n j τ) = shiftDiv (m * n) (j + n * i) τ := by
  apply UpperHalfPlane.ext
  simp only [shiftDiv, dite_eq_left hm, dite_eq_left hn, dite_eq_left (Nat.mul_pos hm hn),
    Nat.cast_add, Nat.cast_mul]
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

private def finOne (N n : ℕ) (hn : n ≠ 0) : Fin n ≃ Fin (n / (dOne N n hn).val) :=
  finCongr (Nat.div_one n).symm

private theorem branch_one {n : ℕ} (hn : n ≠ 0)
    (g : SL(2, ℤ)) (hg0 : (N : ℤ) ∣ g 1 0) (hg1 : ((g 1 1 : ℤ) : ZMod N) = 1)
    (x : CPt X) (τ : UpperHalfPlane) (b : Fin n) :
    AtTau N jX tX x
      (g • shiftDiv (n / (dOne N n hn).val) (finOne N n hn b) (mulNat 1 τ)) ↔
      AtTau N jX tX x (shiftDiv n b τ) := by
  have hb : ((finOne N n hn b : Fin _) : ℕ) = (b : ℕ) := finCongr_apply_coe _ _
  rw [tauGammaOne N jX tX g hg0 hg1, mulNat_one, hb]
  simp [dOne]

private theorem product_one_index {M : Type*} [CommMonoid M] {n : ℕ} (hn : n ≠ 0)
    (hs : ∀ a : D N n, a.val = 1) (f : (a : D N n) → Fin (n / a.val) → M) :
    (∏ a, ∏ b, f a b) = ∏ b, f (dOne N n hn) (finOne N n hn b) := by
  classical
  have hu : (Finset.univ : Finset (D N n)) = {dOne N n hn} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hs a)
  rw [hu, Finset.prod_singleton]
  exact ((finOne N n hn).prod_comp _).symm

/-- If all eligible divisors are `1`, the triangular formula is the upper branch. -/
theorem isXi_of_upper {n : ℕ} (hn : n ≠ 0) (hs : ∀ a : D N n, a.val = 1)
    {t : AbVar.End J} (ht : IsUpper N jX tX aj n t) : IsXi (N := N) jX tX aj n t := by
  intro g hg τ τ' x x' y y' hx hx' hy hy'
  let a := dOne N n hn
  let e := finOne N n hn
  rw [product_one_index hn hs]
  exact ht τ τ' x x' (fun b => y a (e b)) (fun b => y' a (e b)) hx hx'
    (fun b => (branch_one hn (g a) (hg a).1 (by simpa [a, dOne] using (hg a).2)
      _ _ b).1 (hy a (e b)))
    (fun b => (branch_one hn (g a) (hg a).1 (by simpa [a, dOne] using (hg a).2)
      _ _ b).1 (hy' a (e b)))

/-- At index one the upper correspondence is the identity if `AtTau` is single valued. -/
theorem isUpper_one
    (hu : ∀ τ : UpperHalfPlane, ∀ x y : CPt X, AtTau N jX tX x τ → AtTau N jX tX y τ → x = y) :
    IsUpper N jX tX aj 1 (1 : AbVar.End J) := by
  intro τ τ' x x' y y' hx hx' hy hy'
  rw [Fin.prod_univ_one]
  have ey : x = y 0 := hu τ _ _ hx (by simpa [shiftDiv_one_zero] using hy 0)
  have ey' : x' = y' 0 := hu τ' _ _ hx' (by simpa [shiftDiv_one_zero] using hy' 0)
  change (ajC aj x / ajC aj x') ≫ 𝟙 _ = _
  rw [Category.comp_id, ey, ey']

/-- Multiplication of the upper branches is the Euclidean division of the new offset.
This applies to all positive indices, without a coprimality condition. -/
theorem isUpper_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hxAll : TauPts N jX tX)
    {s t : AbVar.End J} (hs : IsUpper N jX tX aj m s) (ht : IsUpper N jX tX aj n t) :
    IsUpper N jX tX aj (m * n) (s * t) := by
  intro τ τ' x x' z z' hx hx' hz hz'
  choose y hy using hxAll
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  have hb (i : Fin m) (j : Fin n) (w : UpperHalfPlane) :
      shiftDiv m i (shiftDiv n j w) = shiftDiv (m * n) (e (i, j)) w :=
    shiftDiv_shiftDiv hm hn i j w
  have h (j : Fin n) : endC s (ajC aj (y (shiftDiv n j τ)) /
      ajC aj (y (shiftDiv n j τ'))) =
      ∏ i : Fin m, ajC aj (z (e (i, j))) / ajC aj (z' (e (i, j))) :=
    by
      apply hs _ _ _ _ _ _ (hy _) (hy _)
      · intro i
        rw [hb]
        exact hz _
      · intro i
        rw [hb]
        exact hz' _
  have ht' := ht τ τ' x x' (fun j => y (shiftDiv n j τ)) (fun j => y (shiftDiv n j τ'))
    hx hx' (fun _ => hy _) (fun _ => hy _)
  change endC s (endC t (ajC aj x / ajC aj x')) = _
  rw [ht']
  let F : (J.Pt ℂ) →* (J.Pt ℂ) :=
    { toFun := endC s
      map_one' := MonObj.one_comp _
      map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
  change F (∏ j : Fin n, ajC aj (y (shiftDiv n j τ)) /
    ajC aj (y (shiftDiv n j τ'))) = _
  rw [map_prod]
  let f (b : Fin (m * n)) := ajC aj (z b) / ajC aj (z' b)
  change _ = ∏ b, f b
  calc
    _ = ∏ j : Fin n, ∏ i : Fin m, f (e (i, j)) := Finset.prod_congr rfl fun j _ => h j
    _ = ∏ ij : Fin m × Fin n, f (e ij) :=
      (Fintype.prod_prod_type_right (fun ij => f (e ij))).symm
    _ = _ := e.prod_comp f

/-- The upper branch of a bad-prime operator is its whole action formula. -/
theorem isXi_bad_prime_pow
    (hu : ∀ τ : UpperHalfPlane, ∀ x y : CPt X, AtTau N jX tX x τ → AtTau N jX tX y τ → x = y)
    (hxAll : TauPts N jX tX) (p : Nat.Primes) (hpN : (p : ℕ) ∣ N)
    {t : AbVar.End J} (ht : IsHeckeT N jX tX aj (p : ℕ) t) (k : ℕ) :
    IsXi (N := N) jX tX aj ((p : ℕ) ^ k) (t ^ k) := by
  have hUp : IsUpper N jX tX aj (p : ℕ) t :=
    fun τ τ' x x' y y' hx hx' hy hy' => (ht τ τ' x x' y y' hx hx' hy hy').1 hpN
  have hPower : ∀ k : ℕ, IsUpper N jX tX aj ((p : ℕ) ^ k) (t ^ k) := by
    intro k
    induction k with
    | zero => simpa using (isUpper_one (aj := aj) hu)
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact isUpper_mul (pow_pos p.2.pos _) p.2.pos hxAll ih hUp
  apply isXi_of_upper (pow_ne_zero _ p.2.ne_zero) _ (hPower k)
  intro a
  obtain ⟨hd, hc⟩ := Finset.mem_filter.1 a.property
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow p.2).1 (Nat.mem_divisors.1 hd).1
  cases i with
  | zero => simpa using hi
  | succ i =>
    exfalso
    exact p.2.not_dvd_one
      (hc.gcd_eq_one ▸ Nat.dvd_gcd (hi ▸ dvd_pow_self (p : ℕ) (Nat.succ_ne_zero i)) hpN)

/-- At a prime index, the old formula implies the triangular formula. The branch
with `a = 1` runs over `Fin p`; at a good prime the `a = p` branch has one term. -/
theorem isXi_prime_of_isHeckeT (p : Nat.Primes) {t : AbVar.End J}
    (ht : IsHeckeT N jX tX aj (p : ℕ) t) : IsXi (N := N) jX tX aj (p : ℕ) t := by
  classical
  by_cases hpN : (p : ℕ) ∣ N
  · apply isXi_of_upper p.2.ne_zero
    · intro a
      obtain ⟨hd, hc⟩ := Finset.mem_filter.1 a.property
      rcases (Nat.dvd_prime p.2).1 (Nat.mem_divisors.1 hd).1 with ha | ha
      · exact ha
      · exact False.elim ((p.2.coprime_iff_not_dvd.1 (ha ▸ hc)) hpN)
    · intro τ τ' x x' y y' hx hx' hy hy'
      exact (ht τ τ' x x' y y' hx hx' hy hy').1 hpN
  · intro g hg τ τ' x x' y y' hx hx' hy hy'
    let a := dOne N (p : ℕ) p.2.ne_zero
    let e := finOne N (p : ℕ) p.2.ne_zero
    let c : D N (p : ℕ) :=
      ⟨p, Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨dvd_rfl, p.2.ne_zero⟩,
        p.2.coprime_iff_not_dvd.2 hpN⟩⟩
    have hca : c ≠ a := fun h => p.2.ne_one (congrArg Subtype.val h)
    have hu : (Finset.univ : Finset (D N (p : ℕ))) = {a, c} := by
      ext d
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have hd := (Nat.mem_divisors.1 (Finset.mem_filter.1 d.property).1).1
      exact ((Nat.dvd_prime p.2).1 hd).imp Subtype.ext Subtype.ext
    have hd : (p : ℕ) / c.val = 1 := Nat.div_self p.2.pos
    let f := finCongr hd.symm
    have h0 : (f 0).val = 0 := finCongr_apply_coe _ _
    have hlast (w : UpperHalfPlane) :
        shiftDiv ((p : ℕ) / c.val) (f 0) (mulNat c.val w) = mulNat (p : ℕ) w := by
      rw [h0, hd, shiftDiv_one_zero]
    rw [hu, Finset.prod_pair hca.symm]
    have hfirst (F : Fin ((p : ℕ) / a.val) → J.Pt ℂ) :
        (∏ b, F b) = ∏ b, F (e b) := (e.prod_comp F).symm
    rw [hfirst]
    have hsingle (F : Fin ((p : ℕ) / c.val) → J.Pt ℂ) :
        (∏ b, F b) = F (f 0) := by rw [← f.prod_comp F, Fin.prod_univ_one]
    rw [hsingle]
    exact (ht τ τ' x x' (fun b => y a (e b)) (fun b => y' a (e b)) hx hx'
      (fun b => (branch_one p.2.ne_zero (g a) (hg a).1 (by simpa [a, dOne] using (hg a).2)
        _ _ b).1 (hy a (e b)))
      (fun b => (branch_one p.2.ne_zero (g a) (hg a).1 (by simpa [a, dOne] using (hg a).2)
        _ _ b).1 (hy' a (e b)))).2 hpN (g c) (hg c).1 (hg c).2 _ _
          (by simpa only [hlast] using hy c (f 0)) (by simpa only [hlast] using hy' c (f 0))

section Assembly

variable {tp : Nat.Primes → AbVar.End J} {δ : (ZMod N)ˣ → AbVar.End J}

/-- Once the formulas are closed under the indicated operations and distinguish
endomorphisms, induction gives existence. Pinning then proves the ring identities
for the chosen family; there is no separate commutativity input. -/
theorem exists_xi_of_actionLaws
    (hpin : ∀ n > 0, ∀ s t : AbVar.End J, IsXi (N := N) jX tX aj n s →
      IsXi (N := N) jX tX aj n t → s = t)
    (h₁ : IsXi (N := N) jX tX aj 1 (1 : AbVar.End J))
    (hprime : ∀ p : Nat.Primes, IsXi (N := N) jX tX aj p (tp p))
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → ∀ s t : AbVar.End J,
      IsXi (N := N) jX tX aj m s → IsXi (N := N) jX tX aj n t →
      IsXi (N := N) jX tX aj (m * n) (s * t))
    (hgood : ∀ (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N) (k : ℕ) (s t : AbVar.End J),
      IsXi (N := N) jX tX aj ((p : ℕ) ^ k) s →
      IsXi (N := N) jX tX aj ((p : ℕ) ^ (k + 1)) t →
      IsXi (N := N) jX tX aj ((p : ℕ) ^ (k + 2))
        (tp p * t - ((p : ℕ) : AbVar.End J) * δ (unitOf N p.2 hpN) * s))
    (hbad : ∀ (p : Nat.Primes), (p : ℕ) ∣ N → ∀ k : ℕ,
      IsXi (N := N) jX tX aj ((p : ℕ) ^ k) (tp p ^ k)) :
    ∃ ξ : ℕ → AbVar.End J, XiAction (N := N) jX tX aj ξ ∧ HeckeRelations tp δ ξ := by
  classical
  have hE : ∀ n : ℕ, ∃ t : AbVar.End J, n = 0 ∧ t = 0 ∨
      0 < n ∧ IsXi (N := N) jX tX aj n t := by
    apply Nat.recOnPrimeCoprime
    · exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    · intro p k hp
      let q : Nat.Primes := ⟨p, hp⟩
      have hq : ∀ k : ℕ, ∃ t : AbVar.End J, IsXi (N := N) jX tX aj (p ^ k) t := by
        by_cases h : p ∣ N
        · intro k
          exact ⟨_, hbad q h k⟩
        · intro k
          induction k using Nat.twoStepInduction with
          | zero => exact ⟨1, by simpa using h₁⟩
          | one => exact ⟨tp q, by simpa using hprime q⟩
          | more k ih₀ ih₁ =>
            obtain ⟨s, hs⟩ := ih₀
            obtain ⟨t, ht⟩ := ih₁
            exact ⟨_, hgood q h k s t hs ht⟩
      obtain ⟨t, ht⟩ := hq k
      exact ⟨t, Or.inr ⟨pow_pos hp.pos _, ht⟩⟩
    · intro m n hm hn hmn ihₘ ihₙ
      obtain ⟨s, hs⟩ := ihₘ
      obtain ⟨t, ht⟩ := ihₙ
      have hm' : 0 < m := by omega
      have hn' : 0 < n := by omega
      exact ⟨s * t, Or.inr ⟨Nat.mul_pos hm' hn',
        hmul m n hm' hn' hmn s t
          ((hs.resolve_left fun h => hm'.ne' h.1).2)
          ((ht.resolve_left fun h => hn'.ne' h.1).2)⟩⟩
  choose ξ hξ using hE
  have hacts (n : ℕ) (hn : 0 < n) : IsXi (N := N) jX tX aj n (ξ n) :=
    ((hξ n).resolve_left fun h => hn.ne' h.1).2
  have hpin' (n : ℕ) (hn : 0 < n) (t : AbVar.End J) :
      IsXi (N := N) jX tX aj n t ↔ t = ξ n :=
    ⟨fun ht => hpin n hn t (ξ n) ht (hacts n hn), fun ht => ht.symm ▸ hacts n hn⟩
  refine ⟨ξ, hpin', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact ((hξ 0).resolve_right fun h => (Nat.lt_irrefl 0) h.1).2
  · exact ((hpin' 1 one_pos 1).1 h₁).symm
  · exact fun p => ((hpin' p p.2.pos (tp p)).1 (hprime p)).symm
  · intro m n hm hn hmn
    exact ((hpin' _ (Nat.mul_pos hm hn) _).1
      (hmul m n hm hn hmn _ _ (hacts m hm) (hacts n hn))).symm
  · intro p hpN k
    exact ((hpin' _ (pow_pos p.2.pos _) _).1
      (hgood p hpN k _ _ (hacts _ (pow_pos p.2.pos _)) (hacts _ (pow_pos p.2.pos _)))).symm
  · intro p hpN k
    exact ((hpin' _ (pow_pos p.2.pos _) _).1 (hbad p hpN k)).symm

/-- The data still needed after the prime and bad-prime calculations are point
realization, single valuedness, and the two composite action identities. This gives the exact original conclusion per model. -/
theorem exists_xi_of_compositeActions
    (hP : X1TauPoints) (hN : 2 ≤ N) (hC : IsCurve X)
    (hG : IsX1Gen N X jX tX) {P₀ : RatPt X} (hJ : IsJacobian X P₀ J aj)
    (hu : ∀ τ : UpperHalfPlane, ∀ x y : CPt X, AtTau N jX tX x τ → AtTau N jX tX y τ → x = y)
    (htp : ∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p))
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → ∀ s t : AbVar.End J,
      IsXi (N := N) jX tX aj m s → IsXi (N := N) jX tX aj n t →
      IsXi (N := N) jX tX aj (m * n) (s * t))
    (hgood : ∀ (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N) (k : ℕ) (s t : AbVar.End J),
      IsXi (N := N) jX tX aj ((p : ℕ) ^ k) s →
      IsXi (N := N) jX tX aj ((p : ℕ) ^ (k + 1)) t →
      IsXi (N := N) jX tX aj ((p : ℕ) ^ (k + 2))
        (tp p * t - ((p : ℕ) : AbVar.End J) * δ (unitOf N p.2 hpN) * s)) :
    ∃ ξ : ℕ → AbVar.End J, XiAction (N := N) jX tX aj ξ ∧ HeckeRelations tp δ ξ := by
  apply exists_xi_of_actionLaws (fun _ _ _ _ => isXi_unique hP hN hC hG hJ) ?_
    (fun p => isXi_prime_of_isHeckeT p (htp p)) hmul hgood
    (fun p hpN k => isXi_bad_prime_pow hu (hP N hN X jX tX hC hG) p hpN (htp p) k)
  apply isXi_of_upper (n := 1) one_ne_zero _ (isUpper_one hu)
  intro a
  exact Nat.dvd_one.mp (Nat.mem_divisors.1 (Finset.mem_filter.1 a.property).1).1

end Assembly

#print axioms mem_D_one
#print axioms exists_xi_matrices
#print axioms mulNat_one
#print axioms shiftDiv_one_zero
#print axioms shiftDiv_shiftDiv
#print axioms branch_one
#print axioms product_one_index
#print axioms isXi_agree
#print axioms isXi_of_upper
#print axioms isUpper_one
#print axioms isUpper_mul
#print axioms isXi_bad_prime_pow
#print axioms isXi_prime_of_isHeckeT
#print axioms isXi_unique
#print axioms exists_xi_of_actionLaws
#print axioms exists_xi_of_compositeActions

end ShimuraSteps.HeckeJ
