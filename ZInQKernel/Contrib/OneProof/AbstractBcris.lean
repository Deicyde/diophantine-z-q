import ZInQKernel.Contrib.OneProof.AbstractAcris

/-! # The tree's abstract `B_cris^+ = A_cris[1/p]` and `B_cris = B_cris^+[1/t]` inside `B_dR`

The localizations `PanBergerSplit.BcrisPlus p` and `PanBergerSplit.Bcris p` (every `log [ε]`,
`ε^♯ = 1`, `ε ≠ 1`, inverted) embed into the field `B_dR` through `acrisEmb`, injectively and
`G_{ℚ_p}`-equivariantly, and the image of `B_cris` is `BcrisOf` (Fontaine, Astérisque 223 (1994),
Exposé II, §2.3.4, pp. 78–79; Brinon–Conrad, CMI notes, Def. 9.1.4, p. 131).
-/

noncomputable section

namespace HDec.PkgI4.AbstractPeriods

open BergerBst FontaineSt BmaxOne
open PanBergerSplit (Ainf AinfP theta Acris0 Acris acrisAct logT BcrisPlus Bcris bcrisPlusAct
  bcrisAct tMonoid tGen)
open _root_.ZInQ.Contrib.G9.BdrKer.Cp (xi)

variable (p : ℕ) [Fact p.Prime]

/-! ### Auxiliary facts -/

/-- A nonzero element of the field `B_dR` is a unit. -/
private theorem isUnit_of_ne_zero {x : BdR p} (hx : x ≠ 0) : IsUnit x := by
  obtain ⟨y, hy⟩ : ∃ y : BdR p, x * y = 1 :=
    (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).mul_inv_cancel hx
  exact IsUnit.of_mul_eq_one y hy

/-- `p` is a unit of `B_dR` (the image of the unit `p ∈ ℚ_p`). -/
private theorem isUnit_natCast_p : IsUnit ((p : ℕ) : BdR p) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h := (IsUnit.mk0 _ hp0).map (algebraMap ℚ_[p] (BdR p))
  rwa [map_natCast] at h

/-- If `u t = 1` then `u` is `Ring.inverse t`. -/
private theorem eq_ringInverse_of_mul_eq_one {M₀ : Type*} [CommMonoidWithZero M₀] {u t : M₀}
    (h : u * t = 1) : u = Ring.inverse t := by
  have ht : IsUnit t := IsUnit.of_mul_eq_one_right u h
  calc u = u * (t * Ring.inverse t) := by rw [Ring.mul_inverse_cancel t ht, mul_one]
    _ = Ring.inverse t := by rw [← mul_assoc, h, one_mul]

/-- A ring map out of a localization lands in a subring `T` if the images of the numerators lie
in `T` and the images of the denominators have inverses in `T`. -/
private theorem map_mem_of_isLocalization {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (f : S →+* P) (T : Subring P)
    (h1 : ∀ r, f (algebraMap R S r) ∈ T)
    (h2 : ∀ m ∈ M, ∃ u ∈ T, f (algebraMap R S m) * u = 1) (x : S) : f x ∈ T := by
  obtain ⟨r, m, rfl⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨u, hu, hmu⟩ := h2 m m.2
  have e : f (IsLocalization.mk' S r m) = f (algebraMap R S r) * u := by
    rw [← IsLocalization.mk'_spec S r m, map_mul, mul_assoc, hmu, mul_one]
  rw [e]
  exact T.mul_mem (h1 r) hu

/-! ### `B_cris^+ → B_dR` -/

/-- `B_cris^+ = A_cris[1/p] → B_dR`. -/
def bcrisPlusEmb : BcrisPlus p →+* BdR p :=
  Localization.awayLift ((toBdR p).comp (acrisEmb p)) (p : Acris p) (by
    rw [RingHom.comp_apply, map_natCast, map_natCast]
    exact isUnit_natCast_p p)

theorem bcrisPlusEmb_algebraMap (a : Acris p) :
    bcrisPlusEmb p (algebraMap (Acris p) (BcrisPlus p) a) = toBdR p (acrisEmb p a) := by
  unfold bcrisPlusEmb Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_eq]
  rfl

theorem bcrisPlusEmb_injective : Function.Injective (bcrisPlusEmb p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (p : Acris p)) x
  have h2 : toBdR p (acrisEmb p a) = 0 := by
    rw [← bcrisPlusEmb_algebraMap, ← IsLocalization.mk'_spec (BcrisPlus p) a s, map_mul, hx,
      zero_mul]
  have ha : a = 0 := acrisEmb_injective p
    ((toBdR_injective p (h2.trans (map_zero _).symm)).trans (map_zero _).symm)
  rw [ha, IsLocalization.mk'_zero]

theorem bcrisPlusEmb_bcrisPlusAct (σ : GQp p) (x : BcrisPlus p) :
    bcrisPlusEmb p (bcrisPlusAct p σ x) = bdrAct p σ (bcrisPlusEmb p x) := by
  have h : (bcrisPlusEmb p).comp (bcrisPlusAct p σ) = (bdrAct p σ).comp (bcrisPlusEmb p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : Acris p))
    ext a
    simp only [RingHom.comp_apply]
    rw [PanBergerSplit.bcrisPlusAct_algebraMap, bcrisPlusEmb_algebraMap, bcrisPlusEmb_algebraMap,
      acrisEmb_acrisAct, bdrAct_toBdR]
  exact congrArg (fun φ => φ x) h

/-- The image of a generator `log [ε]` of `tMonoid` is `log [ε] ∈ B_dR`. -/
private theorem bcrisPlusEmb_logT {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    bcrisPlusEmb p (algebraMap (Acris p) (BcrisPlus p) (logT p (PanBergerSplit.theta_teich_sub_one p h))) =
      toBdR p (logTeich p h) := by
  rw [bcrisPlusEmb_algebraMap, acrisEmb_logT p _ (teich_sub_one_mem p h)]
  rfl

/-- Every element of `tMonoid` goes to an element of `B_dR` with an inverse in `BcrisOf`. -/
private theorem exists_mul_eq_one_of_mem_tMonoid {y : BcrisPlus p} (hy : y ∈ tMonoid p) :
    ∃ u ∈ BcrisOf p (eps0_spec p) (xi p) (theta_xi' p), bcrisPlusEmb p y * u = 1 := by
  rw [PanBergerSplit.tMonoid] at hy
  induction hy using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨ε, h, hne, rfl⟩ := hy
    rw [bcrisPlusEmb_logT p h]
    have hne0 : toBdR p (logTeich p h) ≠ 0 := fun h0 =>
      logTeich_ne_zero p h hne ((toBdR_injective p) (h0.trans (map_zero _).symm))
    exact ⟨Ring.inverse (toBdR p (logTeich p h)),
      tInv_mem_of p (eps0_spec p) _ (Algebra.subset_adjoin (Or.inr rfl)) ⟨ε, h, hne, rfl⟩,
      Ring.mul_inverse_cancel _ (isUnit_of_ne_zero p hne0)⟩
  | one => exact ⟨1, Subalgebra.one_mem _, by rw [map_one, mul_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, hxu⟩ := hx
    obtain ⟨v, hv, hyv⟩ := hy
    exact ⟨u * v, Subalgebra.mul_mem _ hu hv, by rw [map_mul, mul_mul_mul_comm, hxu, hyv, one_mul]⟩

/-! ### `B_cris → B_dR` -/

/-- `B_cris = B_cris^+[1/log [ε] : ε^♯ = 1, ε ≠ 1] → B_dR`. -/
def bcrisEmb : Bcris p →+* BdR p :=
  IsLocalization.lift (M := tMonoid p) (S := Bcris p) (g := bcrisPlusEmb p) fun y => by
    obtain ⟨u, -, hu⟩ := exists_mul_eq_one_of_mem_tMonoid p y.2
    exact IsUnit.of_mul_eq_one u hu

theorem bcrisEmb_algebraMap (y : BcrisPlus p) :
    bcrisEmb p (algebraMap (BcrisPlus p) (Bcris p) y) = bcrisPlusEmb p y :=
  IsLocalization.lift_eq _ y

theorem bcrisEmb_acris (a : Acris p) :
    bcrisEmb p (algebraMap (BcrisPlus p) (Bcris p) (algebraMap (Acris p) (BcrisPlus p) a)) =
      toBdR p (acrisEmb p a) := by
  rw [bcrisEmb_algebraMap, bcrisPlusEmb_algebraMap]

theorem bcrisEmb_injective : Function.Injective (bcrisEmb p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq (tMonoid p) x
  have h2 : bcrisPlusEmb p y = 0 := by
    rw [← bcrisEmb_algebraMap, ← IsLocalization.mk'_spec (Bcris p) y s, map_mul, hx, zero_mul]
  have hy : y = 0 := bcrisPlusEmb_injective p (h2.trans (map_zero _).symm)
  rw [hy, IsLocalization.mk'_zero]

theorem bcrisEmb_bcrisAct (σ : GQp p) (x : Bcris p) :
    bcrisEmb p (bcrisAct p σ x) = bdrAct p σ (bcrisEmb p x) := by
  have h : (bcrisEmb p).comp (bcrisAct p σ) = (bdrAct p σ).comp (bcrisEmb p) := by
    apply IsLocalization.ringHom_ext (tMonoid p)
    ext y
    simp only [RingHom.comp_apply]
    rw [PanBergerSplit.bcrisAct_algebraMap, bcrisEmb_algebraMap, bcrisEmb_algebraMap,
      bcrisPlusEmb_bcrisPlusAct]
  exact congrArg (fun φ => φ x) h

theorem bcrisEmb_qp (c : ℚ_[p]) :
    bcrisEmb p (algebraMap ℚ_[p] (Bcris p) c) = algebraMap ℚ_[p] (BdR p) c := by
  have h : (bcrisPlusEmb p).comp (PanBergerSplit.qpToBcrisPlus p) = algebraMap ℚ_[p] (BdR p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply, PanBergerSplit.qpToBcrisPlus, IsLocalization.lift_eq,
      PanBergerSplit.zpToBcrisPlus]
    rw [bcrisPlusEmb_algebraMap, acrisEmb_algebraMap]
    exact toBdR_zpB p z
  change bcrisEmb p (algebraMap (BcrisPlus p) (Bcris p) (PanBergerSplit.qpToBcrisPlus p c)) = _
  rw [bcrisEmb_algebraMap]
  exact congrArg (fun φ => φ c) h

/-! ### The image of `B_cris` -/

/-- The image of `B_cris^+` lies in `BcrisPlusOf`. -/
private theorem bcrisPlusEmb_mem (y : BcrisPlus p) :
    bcrisPlusEmb p y ∈ BcrisPlusOf p (xi p) (theta_xi' p) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  refine map_mem_of_isLocalization (Submonoid.powers (p : Acris p)) (bcrisPlusEmb p)
    (BcrisPlusOf p (xi p) (theta_xi' p)).toSubring (fun a => ?_) (fun m hm => ?_) y
  · rw [bcrisPlusEmb_algebraMap]
    exact Algebra.subset_adjoin ⟨acrisEmb p a, by rw [← range_acrisEmb]; exact ⟨a, rfl⟩, rfl⟩
  · obtain ⟨k, rfl⟩ := hm
    refine ⟨algebraMap ℚ_[p] (BdR p) (((p : ℚ_[p]) ^ k)⁻¹), Subalgebra.algebraMap_mem _ _, ?_⟩
    rw [bcrisPlusEmb_algebraMap, map_pow, map_pow, map_natCast, map_natCast,
      ← map_natCast (algebraMap ℚ_[p] (BdR p)), ← map_pow, ← map_mul,
      mul_inv_cancel₀ (pow_ne_zero _ hp0), map_one]

/-- The image of `B_cris` lies in `BcrisOf`. -/
private theorem bcrisEmb_mem (x : Bcris p) :
    bcrisEmb p x ∈ BcrisOf p (eps0_spec p) (xi p) (theta_xi' p) := by
  refine map_mem_of_isLocalization (tMonoid p) (bcrisEmb p)
    (BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)).toSubring (fun y => ?_) (fun m hm => ?_) x
  · rw [bcrisEmb_algebraMap]
    exact bcrisPlusOf_le_bcrisOf p (eps0_spec p) (xi p) (theta_xi' p) (bcrisPlusEmb_mem p y)
  · rw [bcrisEmb_algebraMap]
    exact exists_mul_eq_one_of_mem_tMonoid p hm

/-- `1/t` (`t = log [ε₀]`) is in the image of `B_cris`. -/
private theorem exists_bcrisEmb_eq_inv_t :
    ∃ x : Bcris p, bcrisEmb p x = Ring.inverse (tOf p (eps0_spec p)) := by
  have hε := eps0_spec p
  have ht : algebraMap (Acris p) (BcrisPlus p) (logT p (PanBergerSplit.theta_teich_sub_one p hε.1)) ∈
      tMonoid p :=
    Submonoid.subset_closure ⟨eps0 p, hε.1, ne_one_of_isGenEps p hε, rfl⟩
  refine ⟨IsLocalization.mk' (Bcris p) (1 : BcrisPlus p) ⟨_, ht⟩, eq_ringInverse_of_mul_eq_one ?_⟩
  have hspec : IsLocalization.mk' (Bcris p) (1 : BcrisPlus p) ⟨_, ht⟩ *
      algebraMap (BcrisPlus p) (Bcris p)
        (algebraMap (Acris p) (BcrisPlus p) (logT p (PanBergerSplit.theta_teich_sub_one p hε.1))) =
      algebraMap (BcrisPlus p) (Bcris p) 1 :=
    IsLocalization.mk'_spec _ _ _
  have himg : bcrisEmb p (algebraMap (BcrisPlus p) (Bcris p)
      (algebraMap (Acris p) (BcrisPlus p) (logT p (PanBergerSplit.theta_teich_sub_one p hε.1)))) =
      tOf p hε := by
    rw [bcrisEmb_algebraMap, bcrisPlusEmb_logT]
    rfl
  rw [← himg, ← map_mul, hspec, map_one, map_one]

/-- `bcrisEmb` as a `ℚ_p`-algebra map. -/
private def bcrisAlgHom : Bcris p →ₐ[ℚ_[p]] BdR p :=
  { bcrisEmb p with commutes' := bcrisEmb_qp p }

/-- The image of the abstract `B_cris` is `BcrisOf` (at the chosen `ε₀` and `ξ`). -/
theorem range_bcrisEmb :
    Set.range (bcrisEmb p) = (BcrisOf p (eps0_spec p) (xi p) (theta_xi' p) : Set (BdR p)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact bcrisEmb_mem p x
  · have hle : BcrisOf p (eps0_spec p) (xi p) (theta_xi' p) ≤ (bcrisAlgHom p).range := by
      apply Algebra.adjoin_le
      rintro z (⟨y, hy, rfl⟩ | hz)
      · rw [← range_acrisEmb] at hy
        obtain ⟨a, rfl⟩ := hy
        exact (bcrisAlgHom p).mem_range.mpr
          ⟨algebraMap (BcrisPlus p) (Bcris p) (algebraMap (Acris p) (BcrisPlus p) a),
            bcrisEmb_acris p a⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨x, hx⟩ := exists_bcrisEmb_eq_inv_t p
        exact (bcrisAlgHom p).mem_range.mpr ⟨x, hx⟩
    intro z hz
    obtain ⟨x, hx⟩ := (bcrisAlgHom p).mem_range.mp (hle hz)
    exact ⟨x, hx⟩

end HDec.PkgI4.AbstractPeriods
