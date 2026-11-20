import ZInQKernel.Contrib.OneProof.RC.Adelic.Ideal
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Phase

/-! The global rational-lattice and coefficient comparisons for (O.4). -/

noncomputable section

open scoped Quaternion

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler

variable {O : Type} [CommRing O] {a b : ℚ} {R : Order a b}

/-- The rational vector seen in the order coordinates of the adelic representative. -/
def atRep (z : FiniteUnits R) (q : Prime) (x : B a b) : Bp q.val a b :=
  ↑(z.val q)⁻¹ * toLocal q.val x * (z.val q : Bp q.val a b)

/-- In addition to the exceptional local factors, the product has the characteristic
function of the completed order at every other place. The local factors used with
this definition are understood to vanish outside their own completed orders. -/
def weightAt (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : FiniteUnits R) (x : B a b) : O :=
  open Classical in
  if x ∈ (fromAdelic z).val.leftRing then ∏ q ∈ A.places, w q (atRep z q x) else 0

/-- Evaluate the global Schwartz product at the class representative used by the
ideal-class equivalence. -/
def weight (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : ClassSet R) (x : B a b) : O :=
  weightAt A w (Adelic.classRepresentative z) x

/-- The gate in the global product is exactly the condition that every local
coordinate is integral in the completed order. -/
theorem weightAt_of_local (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : FiniteUnits R) (x : B a b)
    (hx : ∀ q : Prime, atRep z q x ∈ R.completion q.val) :
    weightAt A w z x = ∏ q ∈ A.places, w q (atRep z q x) := by
  classical
  exact ite_eq_left ((mem_leftRing_iff z x).mpr hx)

/-- Positive definiteness cuts a finite norm sphere out of the translated
rational lattice. -/
theorem latticeSphere_finite (ha : a < 0) (hb : b < 0) (z : FiniteUnits R) (n : ℚ) :
    {x : B a b | x ∈ (fromAdelic z).val.leftRing ∧ x.re = 0 ∧ Visibility.nrd x = n}.Finite := by
  let L := (fromAdelic z).val.leftOrder ha hb
  exact (finite_norm_le ha hb L.lattice L.full.fg n).subset
    (fun _ hx => ⟨hx.1, hx.2.2.le⟩)

/-- The `finiteSupp` field for the translated finite product. -/
theorem weight_finiteSupp (ha : a < 0) (hb : b < 0)
    (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O) (z : ClassSet R) (n : ℚ) :
    {x : B a b | x.re = 0 ∧ Visibility.nrd x = n ∧ weight A w z x ≠ 0}.Finite := by
  classical
  refine (latticeSphere_finite ha hb (Adelic.classRepresentative z) n).subset ?_
  rintro x ⟨hre, hn, hx⟩
  refine ⟨?_, hre, hn⟩
  by_contra h
  exact hx (ite_eq_right h)

/-- The local zero factor kills the constant coefficient already before stage reduction. -/
theorem weightAt_zero (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : FiniteUnits R) {q : Prime} (hq : q ∈ A.places) (hzero : w q 0 = 0) :
    weightAt A w z 0 = 0 := by
  classical
  unfold weightAt
  rw [ite_eq_left (Subring.zero_mem _)]
  apply Finset.prod_eq_zero hq
  simpa [atRep] using hzero

/-- The rational sphere used in (O.4). -/
def sphere (a b n : ℚ) : Set (B a b) := {x | x.re = 0 ∧ Visibility.nrd x = n}

/-- The characteristic-zero (or integral coefficient ring) coefficient at a lift. -/
def coefficientAt (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : FiniteUnits R) (n : ℚ) : O :=
  ∑ᶠ x ∈ sphere a b n, weightAt A w z x

/-- The `thetaZero` comparison for the same finite product, at any lift. -/
theorem coefficientAt_zero (ha : a < 0) (hb : b < 0)
    (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : FiniteUnits R) {q : Prime} (hq : q ∈ A.places) (hzero : w q 0 = 0) :
    coefficientAt A w z 0 = 0 := by
  have he : sphere a b 0 = {0} := by
    ext x
    constructor
    · intro hx
      by_contra hn
      exact (Eichler.nrd_pos ha hb (show x ≠ 0 by simpa using hn)).ne' hx.2
    · intro hx
      have : x = 0 := by simpa using hx
      subst x
      simp [sphere, Visibility.nrd]
  simpa only [coefficientAt, he, finsum_mem_singleton] using weightAt_zero A w z hq hzero

/-- Rational conjugation used to change the left representative of a double coset. -/
def rationalConj (u : (B a b)ˣ) : B a b ≃ B a b where
  toFun x := (u : B a b) * x * ↑u⁻¹
  invFun x := (↑u⁻¹ : B a b) * x * ↑u
  left_inv x := by
    simp only [mul_assoc]
    rw [← mul_assoc (↑u⁻¹ : B a b) (↑u : B a b), Units.inv_mul, one_mul, mul_one]
  right_inv x := by
    simp only [mul_assoc]
    rw [← mul_assoc (↑u : B a b) (↑u⁻¹ : B a b), Units.mul_inv, one_mul, mul_one]

theorem atRep_left (u : (B a b)ˣ) (z : FiniteUnits R) (q : Prime) (x : B a b) :
    atRep (diagonal R u * z) q (rationalConj u x) = atRep z q x := by
  let U := Units.map (toLocal q.val).toMonoidHom u
  let Z := z.val q
  have h₁ : (diagonal R u * z).val q = U * Z := rfl
  unfold atRep
  rw [h₁, mul_inv_rev]
  simp only [rationalConj, Equiv.coe_fn_mk, map_mul, Units.val_mul]
  change ((↑Z⁻¹ : Bp q.val a b) * ↑U⁻¹) *
      (↑U * toLocal q.val x * ↑U⁻¹) * (↑U * ↑Z) = _
  simp only [mul_assoc]
  rw [← mul_assoc (↑U⁻¹ : Bp q.val a b) (↑U : Bp q.val a b),
    Units.inv_mul, one_mul, ← mul_assoc (↑U⁻¹ : Bp q.val a b) (↑U : Bp q.val a b),
    Units.inv_mul, one_mul]

/-- A left change of adelic representative transports the rational vector;
there is no assertion of pointwise equality at the untransported vector. -/
theorem weightAt_left (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (u : (B a b)ˣ) (z : FiniteUnits R) (x : B a b) :
    weightAt A w (diagonal R u * z) (rationalConj u x) = weightAt A w z x := by
  classical
  unfold weightAt
  rw [show ((rationalConj u) x ∈ (fromAdelic (diagonal R u * z)).val.leftRing) ↔
      ∀ q : Prime, atRep (diagonal R u * z) q ((rationalConj u) x) ∈ R.completion q.val
    from mem_leftRing_iff _ _]
  simp only [atRep_left]
  rw [show (x ∈ (fromAdelic z).val.leftRing) ↔
      ∀ q : Prime, atRep z q x ∈ R.completion q.val from mem_leftRing_iff _ _]

/-- A rational left translate leaves the whole coefficient unchanged, by
reindexing the norm sphere. This is the left half of representative descent. -/
theorem coefficientAt_left (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (u : (B a b)ˣ) (z : FiniteUnits R) (n : ℚ) :
    coefficientAt A w (diagonal R u * z) n = coefficientAt A w z n := by
  unfold coefficientAt
  symm
  apply finsum_mem_eq_of_bijOn (rationalConj u)
  · have h (v : (B a b)ˣ) (x : B a b) :
        rationalConj v x ∈ sphere a b n ↔ x ∈ sphere a b n := by
      change ((rationalConj v x).re = 0 ∧ Visibility.nrd (rationalConj v x) = n) ↔ _
      exact and_congr (by rw [rationalConj, Equiv.coe_fn_mk, Visibility.quat_re_conj])
        (by rw [rationalConj, Equiv.coe_fn_mk, Visibility.nrd_conj])
    refine ⟨fun x hx => (h u x).mpr hx, (rationalConj u).injective.injOn, ?_⟩
    intro x hx
    exact ⟨(rationalConj u).symm x, (h u _).mp (by simpa only [Equiv.apply_symm_apply]),
      (rationalConj u).apply_symm_apply x⟩
  · intro x _
    exact (weightAt_left A w u z x).symm

/-- Conjugation by a local order unit preserves the integral gate. -/
theorem localUnit_conj_mem (q : Prime) (u : localUnits R q) (x : Bp q.val a b) :
    (↑u.val⁻¹ : Bp q.val a b) * x * (u.val : Bp q.val a b) ∈ R.completion q.val ↔
      x ∈ R.completion q.val := by
  constructor
  · intro hx
    have hh := (R.completion q.val).mul_mem
      ((R.completion q.val).mul_mem u.prop.1 hx) u.prop.2
    simp only [mul_assoc] at hh
    rwa [← mul_assoc (u.val : Bp q.val a b) (↑u.val⁻¹ : Bp q.val a b),
      Units.mul_inv, one_mul, mul_one] at hh
  · intro hx
    exact (R.completion q.val).mul_mem ((R.completion q.val).mul_mem u.prop.2 hx) u.prop.1

theorem atRep_right (z r : FiniteUnits R) (q : Prime) (x : B a b) :
    atRep (z * r) q x =
      (↑(r.val q)⁻¹ : Bp q.val a b) * atRep z q x * (r.val q : Bp q.val a b) := by
  change (↑(z.val q * r.val q)⁻¹ : Bp q.val a b) * toLocal q.val x *
      (↑(z.val q * r.val q) : Bp q.val a b) = _
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  simp [atRep, mul_assoc]

/-- The right factor of the norm character is the product of the local norm
factors on order units. This lemma multiplies their covariance laws. -/
theorem weightAt_right (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (eps : (q : Prime) → localUnits R q → Oˣ)
    (hconj : ∀ q ∈ A.places, ∀ (u : localUnits R q) (y : Bp q.val a b),
      w q ((↑u.val⁻¹ : Bp q.val a b) * y * (u.val : Bp q.val a b)) =
        ((eps q u)⁻¹ : Oˣ) * w q y)
    (z : FiniteUnits R) (r : integralUnits R) (x : B a b) :
    weightAt A w (z * r.val) x =
      (↑((∏ q ∈ A.places, eps q ⟨r.val.val q, r.prop q⟩)⁻¹) : O) * weightAt A w z x := by
  classical
  have he : x ∈ (fromAdelic (z * r.val)).val.leftRing ↔
      x ∈ (fromAdelic z).val.leftRing := by
    rw [mem_leftRing_iff, mem_leftRing_iff]
    exact forall_congr' (fun q => by
      change atRep (z * r.val) q x ∈ R.completion q.val ↔ atRep z q x ∈ R.completion q.val
      rw [atRep_right]
      exact localUnit_conj_mem q ⟨r.val.val q, r.prop q⟩ _)
  unfold weightAt
  rw [he]
  split_ifs with hx
  · simp only [atRep_right]
    calc
      _ = ∏ q ∈ A.places, (↑((eps q ⟨r.val.val q, r.prop q⟩)⁻¹) : O) *
          w q (atRep z q x) :=
        Finset.prod_congr rfl fun q hq => hconj q hq ⟨r.val.val q, r.prop q⟩ _
      _ = _ := by rw [Finset.prod_mul_distrib, ← Units.coe_prod, Finset.prod_inv_distrib]
  · simp

/-- Scalar multiplication commutes with translating to order coordinates. -/
theorem atRep_nsmul (z : FiniteUnits R) (q : Prime) (n : ℕ) (x : B a b) :
    atRep z q (n • x) = n • atRep z q x := by
  unfold atRep
  rw [map_nsmul]
  change (AddMonoidHom.mulRight (z.val q : Bp q.val a b))
    ((AddMonoidHom.mulLeft (↑(z.val q)⁻¹ : Bp q.val a b)) (n • toLocal q.val x)) = _
  rw [map_nsmul, map_nsmul]
  rfl

/-- A unit of the local integer ring acts invertibly on the ambient quaternion
algebra, by restriction of scalars from the local field. -/
theorem localUnit_smul_cancel (q : Prime) (v : ℤ_[q.val]ˣ) (y : Bp q.val a b) :
    ((v⁻¹ : ℤ_[q.val]ˣ) : ℤ_[q.val]) • ((v : ℤ_[q.val]) • y) = y := by
  let V := Units.map (PadicInt.Coe.ringHom (p := q.val)).toMonoidHom v
  change V.inv • (V.val • y) = y
  rw [smul_smul, V.inv_val, one_smul]

/-- The global scaling law at integers which are units at all exceptional places.
The integral gate stays open on the left-order lattice. -/
theorem weightAt_scale (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (hw : ∀ q ∈ A.places, ∀ (v : ℤ_[q.val]ˣ) (y : Bp q.val a b),
      w q ((v : ℤ_[q.val]) • y) = (A.alpha q v : O) * w q y)
    (z : FiniteUnits R) (n : ℕ) (hn : A.Away n)
    (x : B a b) (hx : x ∈ (fromAdelic z).val.leftRing) :
    weightAt A w z (n • x) = (A.scalar n hn : O) * weightAt A w z x := by
  classical
  have hnx : n • x ∈ (fromAdelic z).val.leftRing :=
    (fromAdelic z).val.leftRing.toAddSubgroup.nsmul_mem hx n
  unfold weightAt
  rw [ite_eq_left hnx, ite_eq_left hx, ← Finset.prod_attach A.places, ← Finset.prod_attach A.places]
  simp only [atRep_nsmul]
  unfold PhaseData.scalar
  rw [Units.coe_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _
  simpa only [PhaseData.natUnit_val, Nat.cast_smul_eq_nsmul] using
    hw q.val q.prop (PhaseData.natUnit q.val n (hn q.val q.prop)) (atRep z q.val x)

/-- Pairing the local product with the norm character cancels the right unit
factor pointwise and transports the rational vector by the left factor. -/
theorem weightedAt_change (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (eps : (q : Prime) → localUnits R q → Oˣ)
    (hconj : ∀ q ∈ A.places, ∀ (u : localUnits R q) (y : Bp q.val a b),
      w q ((↑u.val⁻¹ : Bp q.val a b) * y * (u.val : Bp q.val a b)) =
        ((eps q u)⁻¹ : Oˣ) * w q y)
    (χ : FiniteUnits R →* Oˣ)
    (hdiag : ∀ u, χ (diagonal R u) = 1)
    (hχ : ∀ r : integralUnits R, χ r.val = ∏ q ∈ A.places, eps q ⟨r.val.val q, r.prop q⟩)
    (z : FiniteUnits R) (u : (B a b)ˣ) (r : integralUnits R) (x : B a b) :
    (χ (diagonal R u * z * r.val) : O) *
      weightAt A w (diagonal R u * z * r.val) (rationalConj u x) =
    (χ z : O) * weightAt A w z x := by
  rw [weightAt_right A w eps hconj, weightAt_left, ← hχ r, map_mul, map_mul, hdiag u, one_mul,
    Units.val_mul, mul_assoc, ← mul_assoc ((χ r.val : Oˣ) : O),
    show (↑(χ r.val) : O) * ↑((χ r.val)⁻¹) = 1 from (χ r.val).val_inv, one_mul]

/-- Independence of the weighted coefficient under both factors of the adelic
double coset relation. The rational sphere is reindexed on the left. -/
theorem weightedCoefficient_eq (ha : a < 0) (hb : b < 0)
    (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (eps : (q : Prime) → localUnits R q → Oˣ)
    (hconj : ∀ q ∈ A.places, ∀ (u : localUnits R q) (y : Bp q.val a b),
      w q ((↑u.val⁻¹ : Bp q.val a b) * y * (u.val : Bp q.val a b)) =
        ((eps q u)⁻¹ : Oˣ) * w q y)
    (χ : FiniteUnits R →* Oˣ)
    (hdiag : ∀ u, χ (diagonal R u) = 1)
    (hχ : ∀ r : integralUnits R, χ r.val = ∏ q ∈ A.places, eps q ⟨r.val.val q, r.prop q⟩)
    {z z' : FiniteUnits R} (hz : (doubleCosetRel R).r z z') (n : ℚ) :
    (χ z' : O) * coefficientAt A w z' n = (χ z : O) * coefficientAt A w z n := by
  classical
  obtain ⟨u, r, rfl⟩ := hz
  have hrs (t : FiniteUnits R) : (sphere a b n ∩ Function.support (weightAt A w t)).Finite := by
    refine (latticeSphere_finite ha hb t n).subset ?_
    rintro x ⟨hs, hw⟩
    exact ⟨by
      by_contra h
      exact hw (ite_eq_right h), hs.1, hs.2⟩
  unfold coefficientAt
  change (AddMonoidHom.mulLeft (χ (diagonal R u * z * r.val) : O))
      (∑ᶠ x ∈ sphere a b n, weightAt A w (diagonal R u * z * r.val) x) =
    (AddMonoidHom.mulLeft (χ z : O)) (∑ᶠ x ∈ sphere a b n, weightAt A w z x)
  rw [AddMonoidHom.map_finsum_mem' _ (hrs _), AddMonoidHom.map_finsum_mem' _ (hrs _)]
  symm
  apply finsum_mem_eq_of_bijOn (rationalConj u)
  · have h (x : B a b) : rationalConj u x ∈ sphere a b n ↔ x ∈ sphere a b n := by
      change ((rationalConj u x).re = 0 ∧ Visibility.nrd (rationalConj u x) = n) ↔ _
      exact and_congr (by rw [rationalConj, Equiv.coe_fn_mk, Visibility.quat_re_conj])
        (by rw [rationalConj, Equiv.coe_fn_mk, Visibility.nrd_conj])
    refine ⟨fun x hx => (h x).mpr hx, (rationalConj u).injective.injOn, ?_⟩
    intro x hx
    exact ⟨(rationalConj u).symm x, (h _).mp (by simpa only [Equiv.apply_symm_apply]),
      (rationalConj u).apply_symm_apply x⟩
  · intro x _
    exact (weightedAt_change A w eps hconj χ hdiag hχ z u r x).symm

end ZInQ.Manuscript.RC.ThetaJoin
