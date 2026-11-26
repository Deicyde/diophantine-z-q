import ZInQKernel.Contrib.OneProof.AbstractBcris
import ZInQKernel.Contrib.OneProof.FontaineAbstract

/-! # The tree's abstract `B_st = B_cris[X]` inside `B_dR`

`PanBergerSplit.Bst p` is the polynomial ring over the abstract `B_cris`, with `σ(X) = X + log [u_σ]`
for the chosen root `p♭ = PanBergerSplit.pFlat p` of `p` and `u_σ = σ(p♭)/p♭`
(Fontaine, Astérisque 223 (1994), Exposé II, §3; Brinon–Conrad, CMI notes, Def. 9.2.3, p. 138).
Sending `X` to `log [p♭] = log [p̃] + log [η]` (`η = p♭/p̃`, `p̃ = Cp.pFlat p`) gives an injective,
`G_{ℚ_p}`-equivariant ring map to `B_dR` with image `BstFOf` (Fontaine II, Théorème 4.2.4,
p. 86; Brinon–Conrad, Thm 9.2.10, p. 143), hence an equivariant `ℚ_p`-algebra isomorphism of the
abstract `B_st` with `BstFOf` (`bstEquiv`).
-/

noncomputable section

namespace HDec.PkgI4.AbstractPeriods

open BergerBst FontaineSt BmaxOne
open PanBergerSplit (Ainf AinfP theta Acris0 Acris acrisAct logT BcrisPlus Bcris bcrisPlusAct
  bcrisAct tMonoid tGen stAct logU uSigma flatAct)
open _root_.ZInQ.Contrib.G9.BdrKer.Cp (xi)

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. The chosen roots of `p` and the Kummer units -/

theorem untilt_pFlat : PreTilt.untilt (PanBergerSplit.pFlat p) = (p : 𝓞_ℂ_[p]) := by
  have h : ∃ x : PreTilt 𝓞_ℂ_[p] p, PreTilt.untilt x = (p : 𝓞_ℂ_[p]) :=
    ⟨_, ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p⟩
  exact Classical.epsilon_spec h

/-- The two chosen roots of `p` differ by a unit `η` with `η^♯ = 1`. -/
theorem exists_eta : ∃ u : PreTilt 𝓞_ℂ_[p] p,
    PanBergerSplit.pFlat p = _root_.ZInQ.Contrib.G9.BdrKer.Cp.pFlat p * u ∧ PreTilt.untilt u = 1 := by
  obtain ⟨u, hu⟩ := ZInQ.Contrib.G9.BdrKer.Cp.dvd_of_coeff_zero p
    (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) (ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p)
    (PanBergerSplit.pFlat p) (by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, untilt_pFlat]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  refine ⟨u, hu, ?_⟩
  have h1 : (p : 𝓞_ℂ_[p]) * (PreTilt.untilt u - 1) = 0 := by
    have h2 := congrArg PreTilt.untilt hu
    rw [untilt_pFlat, map_mul, ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat] at h2
    linear_combination -h2
  exact sub_eq_zero.mp (ZInQ.Contrib.G9.BdrKer.Cp.p_regular p _ h1)

/-- `η = p♭/p̃`. -/
def eta : PreTilt 𝓞_ℂ_[p] p := Classical.choose (exists_eta p)

theorem pFlat_eq : PanBergerSplit.pFlat p = _root_.ZInQ.Contrib.G9.BdrKer.Cp.pFlat p * eta p :=
  (Classical.choose_spec (exists_eta p)).1

theorem untilt_eta : PreTilt.untilt (eta p) = 1 :=
  (Classical.choose_spec (exists_eta p)).2

theorem uSigma_spec (σ : GQp p) :
    uSigma p σ * PanBergerSplit.pFlat p = flatAct p σ (PanBergerSplit.pFlat p) := by
  have hσp : PreTilt.untilt (flatAct p σ (PanBergerSplit.pFlat p)) = (p : 𝓞_ℂ_[p]) := by
    rw [DR.untilt_preTiltMap, untilt_pFlat, map_natCast]
  obtain ⟨d, hd⟩ := ZInQ.Contrib.G9.BdrKer.Cp.dvd_of_coeff_zero p (PanBergerSplit.pFlat p)
    (untilt_pFlat p) (flatAct p σ (PanBergerSplit.pFlat p)) (by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, hσp]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  have h : ∃ u : PreTilt 𝓞_ℂ_[p] p,
      u * PanBergerSplit.pFlat p = flatAct p σ (PanBergerSplit.pFlat p) :=
    ⟨d, by rw [hd, mul_comm]⟩
  exact Classical.epsilon_spec h

theorem untilt_uSigma (σ : GQp p) : PreTilt.untilt (uSigma p σ) = 1 := by
  have h := congrArg PreTilt.untilt (uSigma_spec p σ)
  rw [map_mul, untilt_pFlat, DR.untilt_preTiltMap, untilt_pFlat, map_natCast] at h
  have h1 : (p : 𝓞_ℂ_[p]) * (PreTilt.untilt (uSigma p σ) - 1) = 0 := by
    linear_combination h
  exact sub_eq_zero.mp (ZInQ.Contrib.G9.BdrKer.Cp.p_regular p _ h1)

/-- The abstract Kummer period `log [u_σ]` goes to `log [u_σ] ∈ B_dR`. -/
theorem bcrisEmb_logU (σ : GQp p) :
    bcrisEmb p (logU p σ) = toBdR p (logTeich p (untilt_uSigma p σ)) := by
  rw [logU, dite_eq_left (untilt_uSigma p σ), bcrisEmb_acris,
    acrisEmb_logT p _ (teich_sub_one_mem p (untilt_uSigma p σ))]
  rfl

/-! ## §2. The image of the formal variable -/

/-- `log [p♭] = log [p̃] + log [η]`. -/
def logPFlat : BdR p := toBdR p (logPTilde p) + toBdR p (logTeich p (untilt_eta p))

/-- `p̃ ≠ 0`: its untilt is `p`, which is not a unit of `𝓞_ℂ_p`. -/
private theorem cpPFlat_ne_zero : ZInQ.Contrib.G9.BdrKer.Cp.pFlat p ≠ 0 := by
  intro h0
  have h1 := ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p
  rw [h0] at h1
  have h2 : PreTilt.untilt (0 : PreTilt 𝓞_ℂ_[p] p) =
      PreTilt.untilt (0 : PreTilt 𝓞_ℂ_[p] p) * PreTilt.untilt (0 : PreTilt 𝓞_ℂ_[p] p) := by
    rw [← map_mul, mul_zero]
  rw [h1] at h2
  have h3 : (p : 𝓞_ℂ_[p]) * ((p : 𝓞_ℂ_[p]) - 1) = 0 := by
    linear_combination -h2
  have h4 : (p : 𝓞_ℂ_[p]) = 1 := sub_eq_zero.mp (ZInQ.Contrib.G9.BdrKer.Cp.p_regular p _ h3)
  exact (Fact.out : ¬IsUnit (p : 𝓞_ℂ_[p])) (by rw [h4]; exact isUnit_one)

/-- `σ(log [p♭]) = log [p♭] + log [u_σ]`. -/
theorem bdrAct_logPFlat (σ : GQp p) :
    bdrAct p σ (logPFlat p) = logPFlat p + toBdR p (logTeich p (untilt_uSigma p σ)) := by
  obtain ⟨u, hu, hu1⟩ := exists_uSigma p σ
  have hση : PreTilt.untilt (flatAct p σ (eta p)) = 1 := by
    rw [DR.untilt_preTiltMap, untilt_eta, map_one]
  -- `p̃ η u_σ = σ(p̃ η) = p̃ u σ(η)`, and `p̃ ≠ 0` in the domain `𝓞_ℂ_p♭`
  have key : eta p * uSigma p σ = u * flatAct p σ (eta p) := by
    have h1 := uSigma_spec p σ
    rw [pFlat_eq, map_mul, hu] at h1
    apply mul_left_cancel₀ (cpPFlat_ne_zero p)
    linear_combination h1
  have h2 : PreTilt.untilt (eta p * uSigma p σ) = 1 := by
    rw [map_mul, untilt_eta, untilt_uSigma, one_mul]
  have h3 : PreTilt.untilt (u * flatAct p σ (eta p)) = 1 := by
    rw [map_mul, hu1, hση, one_mul]
  have e : toBdR p (logTeich p hu1) + toBdR p (logTeich p hση) =
      toBdR p (logTeich p (untilt_eta p)) + toBdR p (logTeich p (untilt_uSigma p σ)) := by
    rw [← map_add (toBdR p), ← map_add (toBdR p), ← logTeich_mul p hu1 hση h3,
      ← logTeich_mul p (untilt_eta p) (untilt_uSigma p σ) h2, logTeich_congr p key.symm h3 h2]
  rw [logPFlat, map_add, bdrAct_logPTilde p σ hu hu1, bdrAct_logTeich p σ (untilt_eta p)]
  linear_combination e

/-! ## §3. The embedding -/

/-- The abstract `B_st = B_cris[X] → B_dR`, `X ↦ log [p♭]`. -/
def bstEmb : PanBergerSplit.Bst p →+* BdR p := Polynomial.eval₂RingHom (bcrisEmb p) (logPFlat p)

theorem bstEmb_C (b : Bcris p) : bstEmb p (Polynomial.C b) = bcrisEmb p b :=
  Polynomial.eval₂_C _ _

theorem bstEmb_X : bstEmb p Polynomial.X = logPFlat p :=
  Polynomial.eval₂_X _ _

theorem bstEmb_qp (c : ℚ_[p]) :
    bstEmb p (algebraMap ℚ_[p] (PanBergerSplit.Bst p) c) = algebraMap ℚ_[p] (BdR p) c := by
  rw [Polynomial.algebraMap_apply, bstEmb_C, bcrisEmb_qp]

theorem bstEmb_stAct (σ : GQp p) (x : PanBergerSplit.Bst p) :
    bstEmb p (stAct p σ x) = bdrAct p σ (bstEmb p x) := by
  have h : (bstEmb p).comp (stAct p σ) = (bdrAct p σ).comp (bstEmb p) := by
    apply Polynomial.ringHom_ext
    · intro b
      rw [RingHom.comp_apply, RingHom.comp_apply, PanBergerSplit.stAct_C, bstEmb_C, bstEmb_C,
        bcrisEmb_bcrisAct]
    · rw [RingHom.comp_apply, RingHom.comp_apply, bstEmb_X,
        show stAct p σ Polynomial.X = Polynomial.X + Polynomial.C (logU p σ) from
          Polynomial.eval₂_X _ _,
        map_add (bstEmb p), bstEmb_X, bstEmb_C, bcrisEmb_logU, bdrAct_logPFlat]
  exact RingHom.congr_fun h x

/-! The abstract `B_cris` is identified with `BcrisOf` by `bcrisEmb`; under this identification
`bstEmb` is evaluation at `log [p♭] = log [p̃] + log [η]`, a translate of `log [p̃]` by an element
of `BcrisOf`. -/

private theorem bcrisEmb_mem (b : Bcris p) :
    bcrisEmb p b ∈ BcrisOf p (eps0_spec p) (xi p) (theta_xi' p) := by
  have h : bcrisEmb p b ∈ Set.range (bcrisEmb p) := ⟨b, rfl⟩
  rw [range_bcrisEmb] at h
  exact h

/-- `bcrisEmb` with its codomain restricted to `BcrisOf`. -/
private def bcrisCod : Bcris p →+* BcrisOf p (eps0_spec p) (xi p) (theta_xi' p) :=
  (bcrisEmb p).codRestrict _ (bcrisEmb_mem p)

private theorem bcrisCod_injective : Function.Injective (bcrisCod p) := fun _ _ h =>
  bcrisEmb_injective p (congrArg Subtype.val h)

private theorem bcrisCod_surjective : Function.Surjective (bcrisCod p) := by
  intro y
  have hy : (y : BdR p) ∈ Set.range (bcrisEmb p) := by
    rw [range_bcrisEmb]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private theorem algebraMap_comp_bcrisCod :
    (algebraMap (BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)) (BdR p)).comp (bcrisCod p) =
      bcrisEmb p :=
  RingHom.ext fun _ => rfl

private theorem bstEmb_eq_aeval (x : PanBergerSplit.Bst p) :
    bstEmb p x = Polynomial.aeval (R := BcrisOf p (eps0_spec p) (xi p) (theta_xi' p))
      (logPFlat p) (x.map (bcrisCod p)) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_bcrisCod]
  rfl

private theorem logTeich_eta_mem :
    toBdR p (logTeich p (untilt_eta p)) ∈ BcrisOf p (eps0_spec p) (xi p) (theta_xi' p) :=
  Algebra.subset_adjoin (Or.inl ⟨_, logTeich_mem_acris p (untilt_eta p), rfl⟩)

private theorem logPFlat_eq_add :
    logPFlat p = toBdR p (logPTilde p) +
      algebraMap (BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)) (BdR p)
        ⟨toBdR p (logTeich p (untilt_eta p)), logTeich_eta_mem p⟩ :=
  rfl

/-- Transcendence is preserved under translation by a scalar (`P(x + r) = (taylor r P)(x)`). -/
private theorem transcendental_add_algebraMap {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} (hx : Transcendental R x) (r : R) :
    Transcendental R (x + algebraMap R A r) := by
  rw [transcendental_iff_injective] at hx ⊢
  have key : ∀ P : Polynomial R, Polynomial.aeval (x + algebraMap R A r) P =
      Polynomial.aeval x (Polynomial.taylor r P) := by
    intro P
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp, map_add, Polynomial.aeval_X,
      Polynomial.aeval_C]
  intro P Q hPQ
  rw [key, key] at hPQ
  exact Polynomial.taylor_injective r (hx hPQ)

private theorem transcendental_logPFlat :
    Transcendental (BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)) (logPFlat p) := by
  rw [logPFlat_eq_add]
  exact transcendental_add_algebraMap (transcendental_iff_injective.mpr
    (FontaineComparison.injective_semistable_eval p FontaineComparison.fontaineLog431_proof
      (eps0_spec p))) _

theorem bstEmb_injective : Function.Injective (bstEmb p) := by
  intro x y hxy
  rw [bstEmb_eq_aeval p x, bstEmb_eq_aeval p y] at hxy
  exact Polynomial.map_injective _ (bcrisCod_injective p)
    (transcendental_iff_injective.mp (transcendental_logPFlat p) hxy)

/-- Adjoining `log [p♭]` or `log [p̃]` to `BcrisOf` gives the same algebra. -/
private theorem adjoin_logPFlat :
    Algebra.adjoin (BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)) {logPFlat p} =
      Algebra.adjoin (BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)) {toBdR p (logPTilde p)} := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, logPFlat_eq_add]
    exact Subalgebra.add_mem _ (Algebra.self_mem_adjoin_singleton _ _)
      (Subalgebra.algebraMap_mem _ _)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    have e : toBdR p (logPTilde p) = logPFlat p -
        algebraMap (BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)) (BdR p)
          ⟨toBdR p (logTeich p (untilt_eta p)), logTeich_eta_mem p⟩ := by
      rw [logPFlat_eq_add, add_sub_cancel_right]
    rw [e]
    exact Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton _ _)
      (Subalgebra.algebraMap_mem _ _)

theorem range_bstEmb :
    Set.range (bstEmb p) = (BstFOf p (eps0_spec p) (xi p) (theta_xi' p) : Set (BdR p)) := by
  have h1 : Set.range (bstEmb p) = Set.range
      (Polynomial.aeval (R := BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)) (logPFlat p)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.map (bcrisCod p), (bstEmb_eq_aeval p x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := Polynomial.map_surjective _ (bcrisCod_surjective p) y
      exact ⟨x, bstEmb_eq_aeval p x⟩
  rw [h1, LogPTransc.bstFOf_eq_adjoin, Subalgebra.coe_restrictScalars, ← adjoin_logPFlat,
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.coe_range]

/-- The embedding as a `ℚ_p`-algebra map. -/
def bstAlgHom : PanBergerSplit.Bst p →ₐ[ℚ_[p]] BdR p :=
  { bstEmb p with commutes' := bstEmb_qp p }

private theorem range_bstAlgHom :
    (bstAlgHom p).range = BstFOf p (eps0_spec p) (xi p) (theta_xi' p) :=
  SetLike.coe_injective ((AlgHom.coe_range _).trans (range_bstEmb p))

/-- **The abstract `B_st` is the image `BstFOf`**, as `ℚ_p`-algebras. -/
def bstEquiv : PanBergerSplit.Bst p ≃ₐ[ℚ_[p]] BstFOf p (eps0_spec p) (xi p) (theta_xi' p) :=
  (AlgEquiv.ofInjective (bstAlgHom p) (bstEmb_injective p)).trans
    (Subalgebra.equivOfEq _ _ (range_bstAlgHom p))

theorem bstEquiv_apply (x : PanBergerSplit.Bst p) : (bstEquiv p x : BdR p) = bstEmb p x := by
  rfl

end HDec.PkgI4.AbstractPeriods
