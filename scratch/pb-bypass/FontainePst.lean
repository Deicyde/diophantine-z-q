import ZInQKernel.OneProof.H.LPrefix

/-!
# Fontaine's `A_cris`, `B_cris`, `B_st`, and potentially semistable representations (pb-bypass)

Genuine definitions over Mathlib's `A_inf = W(𝓞_ℂ_p♭)` and Fontaine's `θ`, so that Pan's
Theorem 1.0.4 and Berger's Théorème 0.7 can be stated separately, as printed.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace Pst

open Ideal

variable (p : ℕ) [Fact p.Prime]

/-! ### `A_inf`, `A_inf[1/p]`, `θ`, divided powers -/

/-- `A_inf = W(𝓞_ℂ_p♭)` (Mathlib's `PreTilt`). -/
abbrev Ainf := WittVector p (PreTilt 𝓞_ℂ_[p] p)

/-- `A_inf[1/p]`. -/
abbrev AinfP := Localization.Away (p : Ainf p)

/-- Fontaine's `θ : A_inf → 𝓞_ℂ_p` (Mathlib's `WittVector.fontaineTheta`). -/
abbrev theta : Ainf p →+* 𝓞_ℂ_[p] := WittVector.fontaineTheta 𝓞_ℂ_[p] p

/-- The divided power `γ_n(x) = x^n / n!`, in `A_inf[1/p]` (where `n!` is invertible). -/
def dpow (n : ℕ) (x : Ainf p) : AinfP p :=
  qpToLoc p ((n.factorial : ℚ_[p])⁻¹) * (algebraMap (Ainf p) (AinfP p) x) ^ n

/-- Generators of `A_cris^0`: `A_inf` and the divided powers of elements of `ker θ`. -/
def pdGen : Set (AinfP p) :=
  Set.range (algebraMap (Ainf p) (AinfP p)) ∪
    {y | ∃ (n : ℕ) (x : Ainf p), theta p x = 0 ∧ y = dpow p n x}

/-- **`A_cris^0`**: the divided power envelope of `(A_inf, ker θ)` (compatible with the divided
powers of `p`), i.e. the subring `A_inf[x^n/n! : x ∈ ker θ, n ≥ 0]` of `A_inf[1/p]`
(Fontaine, Astérisque 223 (1994), Exp. II §2.3; Brinon–Conrad, CMI notes, §9.1). -/
def Acris0 : Subring (AinfP p) := Subring.closure (pdGen p)

/-- **`A_cris`**: the `p`-adic completion of `A_cris^0`. -/
abbrev Acris := AdicCompletion (Ideal.span {(p : Acris0 p)}) (Acris0 p)

/-- **`B_cris^+ = A_cris[1/p]`**. -/
abbrev BcrisPlus := Localization.Away (p : Acris p)

theorem dpow_mem (n : ℕ) {x : Ainf p} (hx : theta p x = 0) : dpow p n x ∈ Acris0 p :=
  Subring.subset_closure (Or.inr ⟨n, x, hx, rfl⟩)

theorem algebraMap_mem (x : Ainf p) : algebraMap (Ainf p) (AinfP p) x ∈ Acris0 p :=
  Subring.subset_closure (Or.inl ⟨x, rfl⟩)

/-! ### `log [ε]` in `A_cris` -/

/-- The terms `(-1)^{j+1} (j-1)! γ_j(x)` of `log(1 + x) = Σ_{j ≥ 1} (-1)^{j+1} x^j / j`. -/
def logTerm (x : Ainf p) (j : ℕ) : AinfP p :=
  (-1) ^ (j + 1) * ((j - 1).factorial : AinfP p) * dpow p j x

theorem logTerm_mem {x : Ainf p} (hx : theta p x = 0) (j : ℕ) : logTerm p x j ∈ Acris0 p :=
  Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
    (natCast_mem _ _)) (dpow_mem p j hx)

/-- Partial sums `Σ_{1 ≤ j ≤ N} (-1)^{j+1} (j-1)! γ_j(x)`, in `A_cris^0`. -/
def logPartialVal (x : Ainf p) (N : ℕ) : AinfP p :=
  ∑ j ∈ Finset.Ico 1 (N + 1), logTerm p x j

/-- The partial sums as elements of `A_cris^0`. -/
def logPartial {x : Ainf p} (hx : theta p x = 0) (N : ℕ) : Acris0 p :=
  ⟨logPartialVal p x N, Subring.sum_mem _ fun j _ => logTerm_mem p hx j⟩

/-- For `p^n ≤ j - 1`, the term is `p^n` times an element of `A_cris^0`. -/
theorem logTerm_eq_pow_mul {x : Ainf p} (hx : theta p x = 0) {n j : ℕ} (hj : p ^ n ≤ j - 1) :
    ∃ y : Acris0 p, logTerm p x j = (p : AinfP p) ^ n * (y : AinfP p) := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hpos hj
  refine ⟨⟨(-1) ^ (j + 1) * (c : AinfP p) * dpow p j x, Subring.mul_mem _ (Subring.mul_mem _
    (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _) (natCast_mem _ _))
    (dpow_mem p j hx)⟩, ?_⟩
  simp only [logTerm, hc, Nat.cast_mul, Nat.cast_pow]
  ring

theorem logPartial_cauchy {x : Ainf p} (hx : theta p x = 0) (n : ℕ) :
    logPartial p hx (p ^ n) ≡ logPartial p hx (p ^ (n + 1))
      [SMOD ((Ideal.span {(p : Acris0 p)}) ^ n • ⊤ : Submodule (Acris0 p) (Acris0 p))] := by
  have hle : p ^ n + 1 ≤ p ^ (n + 1) + 1 := by
    have := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (show n ≤ n + 1 by omega)
    omega
  -- the difference is a sum of terms divisible by `p^n`
  have key : ∀ j ∈ Finset.Ico (p ^ n + 1) (p ^ (n + 1) + 1),
      ∃ y : Acris0 p, logTerm p x j = (p : AinfP p) ^ n * (y : AinfP p) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact logTerm_eq_pow_mul p hx (by omega)
  choose y hy using key
  rw [SModEq.sub_mem]
  have hdiff : logPartial p hx (p ^ n) - logPartial p hx (p ^ (n + 1)) =
      -((p : Acris0 p) ^ n * ∑ j ∈ (Finset.Ico (p ^ n + 1) (p ^ (n + 1) + 1)).attach,
        y j.1 j.2) := by
    apply Subtype.ext
    change logPartialVal p x (p ^ n) - logPartialVal p x (p ^ (n + 1)) =
      -((p : AinfP p) ^ n * ((∑ j ∈ (Finset.Ico (p ^ n + 1) (p ^ (n + 1) + 1)).attach,
        y j.1 j.2 : Acris0 p) : AinfP p))
    rw [AddSubmonoidClass.coe_finsetSum]
    unfold logPartialVal
    rw [← Finset.sum_Ico_consecutive _ (Nat.le_add_left 1 (p ^ n)) hle, Finset.mul_sum]
    rw [← Finset.sum_attach (Finset.Ico (p ^ n + 1) (p ^ (n + 1) + 1)) (logTerm p x)]
    rw [Finset.sum_congr rfl (fun (j : {j // j ∈ Finset.Ico (p ^ n + 1) (p ^ (n + 1) + 1)}) _ =>
      hy j.1 j.2)]
    ring
  rw [hdiff]
  refine Submodule.neg_mem _ ?_
  rw [← smul_eq_mul]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)
    Submodule.mem_top

/-- **`log(1 + x) ∈ A_cris`** for `x ∈ ker θ`: the limit of the partial sums (the `n`-th
component is the partial sum up to `p^n`, whose remaining terms lie in `p^n A_cris^0`). -/
def logT {x : Ainf p} (hx : theta p x = 0) : Acris p :=
  AdicCompletion.mk _ _ (AdicCompletion.AdicCauchySequence.mk _ _
    (fun n => logPartial p hx (p ^ n)) (logPartial_cauchy p hx))

theorem theta_teich_sub_one {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    theta p (WittVector.teichmuller p ε - 1) = 0 := by
  rw [map_sub, map_one, theta, WittVector.fontaineTheta_teichmuller, h, sub_self]

/-- Generators of the multiplicative set inverted in `B_cris`: `log [ε]` for every `ε ∈ 𝓞_ℂ_p♭`
with `ε^♯ = 1` and `ε ≠ 1`. Every such `ε` is `ε₀^a` for a fixed compatible system `ε₀` of
primitive `p`-power roots of unity and some `a ∈ ℤ_p ∖ {0}`, and `log [ε₀^a] = a·t` with
`t = log [ε₀]`; since `p` is already invertible in `B_cris^+`, inverting them all is inverting `t`. -/
def tGen : Set (BcrisPlus p) :=
  {y | ∃ (ε : PreTilt 𝓞_ℂ_[p] p) (h : PreTilt.untilt ε = 1), ε ≠ 1 ∧
    y = algebraMap (Acris p) (BcrisPlus p) (logT p (theta_teich_sub_one p h))}

/-- The multiplicative set generated by `tGen`. -/
def tMonoid : Submonoid (BcrisPlus p) := Submonoid.closure (tGen p)

/-- **`B_cris = B_cris^+[1/t]`** (the localization; a `def` with its instances, to keep
instance unification cheap). -/
def Bcris : Type := Localization (tMonoid p)

instance : CommRing (Bcris p) := inferInstanceAs (CommRing (Localization (tMonoid p)))

instance : Algebra (BcrisPlus p) (Bcris p) :=
  inferInstanceAs (Algebra (BcrisPlus p) (Localization (tMonoid p)))

instance : IsLocalization (tMonoid p) (Bcris p) :=
  inferInstanceAs (IsLocalization (tMonoid p) (Localization (tMonoid p)))

/-- **`B_st = B_cris[X]`** (Fontaine, Exp. II §3: `B_st = B_cris[u]`, `u` an indeterminate
standing for `log [p♭]`). -/
abbrev Bst := Polynomial (Bcris p)

/-! ### The action of `G_{ℚ_p}` -/

/-- `σ` on `A_inf[1/p]`. -/
def locAct (σ : GQp p) : AinfP p →+* AinfP p := DR.locMap p (oAct p σ)

/-- `σ♭` on `𝓞_ℂ_p♭`. -/
abbrev flatAct (σ : GQp p) : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p :=
  DR.preTiltMap p (oAct p σ)

theorem locAct_algebraMap (σ : GQp p) (w : Ainf p) :
    locAct p σ (algebraMap (Ainf p) (AinfP p) w) =
      algebraMap (Ainf p) (AinfP p) (WittVector.map (flatAct p σ) w) :=
  locMap_algebraMap p (oAct p σ) w

theorem locAct_qpToLoc (σ : GQp p) (c : ℚ_[p]) : locAct p σ (qpToLoc p c) = qpToLoc p c := by
  have h : (locAct p σ).comp (qpToLoc p) = qpToLoc p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply]
    rw [qpToLoc_algebraMap, locAct_algebraMap, wittMap_zpToW]
  exact congrArg (fun φ => φ c) h

theorem theta_wittMap (σ : GQp p) (x : Ainf p) :
    theta p (WittVector.map (flatAct p σ) x) = oAct p σ (theta p x) := by
  have := DR.fontaineTheta_naturality p (oAct p σ)
  exact congrArg (fun φ => φ x) this

theorem locAct_dpow (σ : GQp p) (n : ℕ) (x : Ainf p) :
    locAct p σ (dpow p n x) = dpow p n (WittVector.map (flatAct p σ) x) := by
  simp only [dpow, map_mul, map_pow, locAct_qpToLoc, locAct_algebraMap]

theorem locAct_mem (σ : GQp p) {y : AinfP p} (hy : y ∈ Acris0 p) : locAct p σ y ∈ Acris0 p := by
  have h : Acris0 p ≤ (Acris0 p).comap (locAct p σ) := by
    rw [Acris0, Subring.closure_le]
    rintro z (⟨w, rfl⟩ | ⟨n, x, hx, rfl⟩)
    · show locAct p σ _ ∈ Acris0 p
      rw [locAct_algebraMap]
      exact algebraMap_mem p _
    · show locAct p σ _ ∈ Acris0 p
      rw [locAct_dpow]
      exact dpow_mem p n (by rw [theta_wittMap, hx, map_zero])
  exact h hy

/-- `σ` on `A_cris^0`. -/
def acris0Act (σ : GQp p) : Acris0 p →+* Acris0 p :=
  (locAct p σ).restrict (Acris0 p) (Acris0 p) fun _ hy => locAct_mem p σ hy

/-- `σ` on `A_cris` (by `p`-adic continuity). -/
def acrisAct (σ : GQp p) : Acris p →+* Acris p :=
  DR.adicMap _ _ (acris0Act p σ) (DR.span_p_le_comap p _)

/-- `σ` on `B_cris^+`. -/
def bcrisPlusAct (σ : GQp p) : BcrisPlus p →+* BcrisPlus p :=
  Localization.awayLift ((algebraMap _ _).comp (acrisAct p σ)) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

theorem bcrisPlusAct_algebraMap (σ : GQp p) (a : Acris p) :
    bcrisPlusAct p σ (algebraMap (Acris p) (BcrisPlus p) a) =
      algebraMap (Acris p) (BcrisPlus p) (acrisAct p σ a) := by
  unfold bcrisPlusAct Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_eq]
  rfl

theorem acris0Act_logPartial (σ : GQp p) {x : Ainf p} (hx : theta p x = 0)
    (hx' : theta p (WittVector.map (flatAct p σ) x) = 0) (N : ℕ) :
    acris0Act p σ (logPartial p hx N) = logPartial p hx' N := by
  apply Subtype.ext
  change locAct p σ (logPartialVal p x N) = logPartialVal p _ N
  simp only [logPartialVal, map_sum, logTerm, map_mul, map_pow, map_neg, map_one, map_natCast,
    locAct_dpow]

theorem evalₐ_logT {x : Ainf p} (hx : theta p x = 0) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n (logT p hx) =
      Ideal.Quotient.mk _ (logPartial p hx (p ^ n)) := by
  unfold logT
  exact AdicCompletion.evalₐ_mk _ n _

theorem acrisAct_logT (σ : GQp p) {x : Ainf p} (hx : theta p x = 0)
    (hx' : theta p (WittVector.map (flatAct p σ) x) = 0) :
    acrisAct p σ (logT p hx) = logT p hx' := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  have h1 := DR.adicMap_evalₐ _ _ (acris0Act p σ) (DR.span_p_le_comap p _) n (logT p hx)
  change AdicCompletion.evalₐ _ n
    (DR.adicMap _ _ (acris0Act p σ) (DR.span_p_le_comap p _) (logT p hx)) = _
  rw [h1, evalₐ_logT]
  unfold DR.adicMapAux
  rw [RingHom.comp_apply]
  erw [evalₐ_logT]
  rw [Ideal.quotientMap_mk]
  exact congrArg _ (acris0Act_logPartial p σ hx hx' _)

theorem flatAct_injective (σ : GQp p) : Function.Injective (flatAct p σ) := by
  intro a b h
  have ha := DR.preTiltMap_comp_eq_id p (oAct p σ) (oAct p σ⁻¹) (oAct_inv_apply p σ) a
  have hb := DR.preTiltMap_comp_eq_id p (oAct p σ) (oAct p σ⁻¹) (oAct_inv_apply p σ) b
  rw [← ha, ← hb, h]

theorem tMonoid_le_comap (σ : GQp p) :
    tMonoid p ≤ (tMonoid p).comap (bcrisPlusAct p σ) := by
  rw [tMonoid, Submonoid.closure_le]
  rintro _ ⟨ε, h, hne, rfl⟩
  apply Submonoid.subset_closure
  have h' : PreTilt.untilt (flatAct p σ ε) = 1 := by
    rw [DR.untilt_preTiltMap, h, map_one]
  have hx' : theta p (WittVector.map (flatAct p σ) (WittVector.teichmuller p ε - 1)) = 0 := by
    rw [theta_wittMap, theta_teich_sub_one p h, map_zero]
  refine ⟨flatAct p σ ε, h', fun h1 => hne (flatAct_injective p σ (by rw [h1, map_one])), ?_⟩
  rw [bcrisPlusAct_algebraMap, acrisAct_logT p σ _ hx']
  congr 2
  rw [map_sub, map_one, WittVector.map_teichmuller]

/-- `σ` on `B_cris`. -/
def bcrisAct (σ : GQp p) : Bcris p →+* Bcris p :=
  IsLocalization.map (M := tMonoid p) (T := tMonoid p) (Bcris p) (bcrisPlusAct p σ)
    (tMonoid_le_comap p σ)

/-- A chosen `p♭ ∈ 𝓞_ℂ_p♭` with `(p♭)^♯ = p` (a compatible system of `p`-power roots of `p`). -/
def pFlat : PreTilt 𝓞_ℂ_[p] p :=
  Classical.epsilon fun x => PreTilt.untilt x = (p : 𝓞_ℂ_[p])

/-- `u_σ = σ(p♭)/p♭ ∈ 𝓞_ℂ_p♭` (unique, `𝓞_ℂ_p♭` being a domain); `u_σ^♯ = σ(p)/p = 1`. -/
def uSigma (σ : GQp p) : PreTilt 𝓞_ℂ_[p] p :=
  Classical.epsilon fun u => u * pFlat p = flatAct p σ (pFlat p)

/-- `c(σ)·t = log [u_σ] = log [σ(p♭)] − log [p♭]` in `B_cris` (Kummer cocycle times `t`). -/
def logU (σ : GQp p) : Bcris p :=
  haveI := Classical.propDecidable
  if h : PreTilt.untilt (uSigma p σ) = 1 then
    algebraMap (BcrisPlus p) (Bcris p)
      (algebraMap (Acris p) (BcrisPlus p) (logT p (theta_teich_sub_one p h)))
  else 0

/-- **The action of `σ ∈ G_{ℚ_p}` on `B_st = B_cris[u]`**: `σ` on coefficients and
`σ(u) = u + log [u_σ]` (`u = log [p♭]`, so `σ(u) = log [σ(p♭)] = u + c(σ) t`). -/
def stAct (σ : GQp p) : Bst p →+* Bst p :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (bcrisAct p σ))
    (Polynomial.X + Polynomial.C (logU p σ))

/-! ### `ℚ_p ⊆ B_cris ⊆ B_st`, fixed by `G_{ℚ_p}` -/

/-- `ℤ_p → A_cris^0`. -/
def zpToAcris0 : ℤ_[p] →+* Acris0 p :=
  ((algebraMap (Ainf p) (AinfP p)).comp (zpToW p)).codRestrict (Acris0 p)
    fun z => algebraMap_mem p _

/-- `ℤ_p → B_cris^+`. -/
def zpToBcrisPlus : ℤ_[p] →+* BcrisPlus p :=
  (algebraMap (Acris p) (BcrisPlus p)).comp
    ((algebraMap (Acris0 p) (Acris p)).comp (zpToAcris0 p))

/-- `ℚ_p → B_cris^+`. -/
def qpToBcrisPlus : ℚ_[p] →+* BcrisPlus p :=
  IsLocalization.lift (M := Submonoid.powers (p : ℤ_[p])) (g := zpToBcrisPlus p) (by
    rintro ⟨_, k, rfl⟩
    have := (IsLocalization.Away.algebraMap_isUnit (S := BcrisPlus p) (p : Acris p)).pow k
    rw [map_natCast] at this
    simpa only [zpToBcrisPlus, RingHom.comp_apply, map_pow, map_natCast] using this)

/-- `ℚ_p → B_cris`. -/
def qpToBcris : ℚ_[p] →+* Bcris p :=
  (algebraMap (BcrisPlus p) (Bcris p)).comp (qpToBcrisPlus p)

instance : Algebra ℚ_[p] (Bcris p) := (qpToBcris p).toAlgebra

theorem acris0Act_zp (σ : GQp p) (z : ℤ_[p]) : acris0Act p σ (zpToAcris0 p z) = zpToAcris0 p z := by
  apply Subtype.ext
  change locAct p σ (algebraMap (Ainf p) (AinfP p) (zpToW p z)) =
    algebraMap (Ainf p) (AinfP p) (zpToW p z)
  rw [locAct_algebraMap, wittMap_zpToW]

theorem acrisAct_algebraMap (σ : GQp p) (a : Acris0 p) :
    acrisAct p σ (algebraMap (Acris0 p) (Acris p) a) =
      algebraMap (Acris0 p) (Acris p) (acris0Act p σ a) := by
  have e : ∀ a' : Acris0 p, algebraMap (Acris0 p) (Acris p) a' =
      AdicCompletion.of (Ideal.span {(p : Acris0 p)}) (Acris0 p) a' := fun a' => by
    erw [AdicCompletion.algebraMap_apply]
  rw [e, e]
  exact DR.adicMap_of _ _ _ _ a

theorem bcrisPlusAct_qp (σ : GQp p) (c : ℚ_[p]) :
    bcrisPlusAct p σ (qpToBcrisPlus p c) = qpToBcrisPlus p c := by
  have h : (bcrisPlusAct p σ).comp (qpToBcrisPlus p) = qpToBcrisPlus p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply, qpToBcrisPlus, IsLocalization.lift_eq, zpToBcrisPlus]
    rw [bcrisPlusAct_algebraMap, acrisAct_algebraMap, acris0Act_zp]
  exact congrArg (fun φ => φ c) h

theorem bcrisAct_algebraMap (σ : GQp p) (y : BcrisPlus p) :
    bcrisAct p σ (algebraMap (BcrisPlus p) (Bcris p) y) =
      algebraMap (BcrisPlus p) (Bcris p) (bcrisPlusAct p σ y) :=
  IsLocalization.map_eq (M := tMonoid p) (S := Bcris p) (T := tMonoid p)
    (hy := tMonoid_le_comap p σ) y

theorem bcrisAct_qp (σ : GQp p) (c : ℚ_[p]) :
    bcrisAct p σ (algebraMap ℚ_[p] (Bcris p) c) = algebraMap ℚ_[p] (Bcris p) c := by
  change bcrisAct p σ (qpToBcris p c) = qpToBcris p c
  rw [qpToBcris, RingHom.comp_apply, bcrisAct_algebraMap, bcrisPlusAct_qp]

theorem stAct_C (σ : GQp p) (b : Bcris p) :
    stAct p σ (Polynomial.C b) = Polynomial.C (bcrisAct p σ b) := by
  exact Polynomial.eval₂_C _ _

theorem stAct_algebraMap (σ : GQp p) (c : ℚ_[p]) :
    stAct p σ (algebraMap ℚ_[p] (Bst p) c) = algebraMap ℚ_[p] (Bst p) c := by
  rw [Polynomial.algebraMap_apply]
  rw [stAct_C]
  rw [bcrisAct_qp]

theorem stAct_smul (σ : GQp p) (c : ℚ_[p]) (x : Bst p) :
    stAct p σ (c • x) = c • stAct p σ x := by
  rw [Algebra.smul_def]
  rw [map_mul]
  rw [stAct_algebraMap]
  rw [← Algebra.smul_def]

/-! ### Potentially semistable representations -/

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- `D_st,K(V^∨) = (B_st ⊗_{ℚ_p} V^∨)^{G_K}`, written as `G_K`-equivariant `ℚ_p`-linear maps
`V → B_st`, for `V = E^n` with the `E`-linear action `ρ` and `K ⊆ ℚ̄_p` (`G_K` is the subgroup of
`G_{ℚ_p}` fixing `K`). Same convention as pkg-I4's `ddrSpace` (`IsDeRham`). -/
def dstSpace (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] Bst p) where
  carrier := {φ | ∀ σ ∈ K.fixingSubgroup, ∀ v : Fin n → E,
    φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = stAct p σ (φ v)}
  zero_mem' := by intro σ _ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ hσ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ hσ v, hψ σ hσ v, map_add]
  smul_mem' := by
    intro c φ hφ σ hσ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ hσ v, stAct_smul]

/-- `B_st^{G_K}` (`= K_0`, the maximal absolutely unramified subfield of `K`, by Fontaine). -/
def bstInv (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Submodule ℚ_[p] (Bst p) where
  carrier := {b | ∀ σ ∈ K.fixingSubgroup, stAct p σ b = b}
  zero_mem' := by intro σ _; simp
  add_mem' := by
    intro a b ha hb σ hσ
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [map_add, ha σ hσ, hb σ hσ]
  smul_mem' := by
    intro c b hb σ hσ
    simp only [Set.mem_ofPred_eq] at hb
    rw [stAct_smul, hb σ hσ]

/-- **`ρ|_{G_K}` is semistable** (Fontaine): `dim_{K_0} D_st,K = dim_{ℚ_p} V`, i.e.
`dim_{ℚ_p} D_st,K = [K_0 : ℚ_p] · dim_{ℚ_p} V` with `K_0 = B_st^{G_K}`. Stated for `V^∨`, as
`IsDeRham` (equivalent for the predicate `IsPst` below: `V` is pst iff `V^∨` is; Fontaine,
Astérisque 223, Exp. VIII). -/
def IsSemistableOver (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Prop :=
  Module.finrank ℚ_[p] (dstSpace p K ρ) =
    Module.finrank ℚ_[p] (bstInv p K) * (n * Module.finrank ℚ_[p] E)

/-- **`ρ` is potentially semistable** (Fontaine): semistable on `G_K` for some finite `K/ℚ_p`. -/
def IsPst (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsSemistableOver p K ρ

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is potentially semistable: it takes values in
`GL_n(E)` for a finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation is potentially
semistable (as `LocalIsDeRham`). -/
def LocalIsPst (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPst p ρE

end Pst

/-! ### Pan and Berger, each in its printed form -/

/-- **Pan, Theorem 1.0.4**, `p ≥ 5`. -/
def PanPrinted : Prop :=
  PanFor fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    Pst.LocalIsPst p n ρ

/-- **Berger, Théorème 0.7.** -/
def BergerPrinted : Prop :=
  BergerDR fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    Pst.LocalIsPst p n ρ

theorem panBerger_of_printed (hP : PanPrinted) (hB : BergerPrinted) : PanBerger := by
  intro p _ hp ρ hirr hfr hdr hodd hdist
  exact hP p hp ρ hirr hfr (hB p 2 (ρ.restrictLocal p) (ρ.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous) hdr) hodd hdist

end PkgI4
end HDec

#print axioms HDec.PkgI4.panBerger_of_printed

namespace HDec.PkgI4.Pst

variable (p : ℕ) [Fact p.Prime]

/-- **Normalization check (unconditional).** The trivial one-dimensional representation is
semistable over every `K`: `D_st,K(ℚ_p) ≅ B_st^{G_K}` by `φ ↦ φ(1)`. -/
theorem isSemistableOver_trivial (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsSemistableOver p K (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
  let e : Fin 1 → ℚ_[p] := fun _ => 1
  have hv : ∀ v : Fin 1 → ℚ_[p], v = v 0 • e := fun v => by ext k; fin_cases k; simp [e]
  let F : dstSpace p K (1 : GQp p →* GL (Fin 1) ℚ_[p]) →ₗ[ℚ_[p]] bstInv p K :=
    { toFun := fun φ => ⟨(φ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] Bst p) e, fun σ hσ => by
        have := φ.2 σ hσ e
        simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec] at this
        exact this.symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let G : bstInv p K →ₗ[ℚ_[p]] dstSpace p K (1 : GQp p →* GL (Fin 1) ℚ_[p]) :=
    { toFun := fun b => ⟨(LinearMap.proj (R := ℚ_[p]) (φ := fun _ : Fin 1 => ℚ_[p]) 0).smulRight
          (b : Bst p), fun σ hσ v => by
        simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec, LinearMap.smulRight_apply,
          LinearMap.proj_apply, stAct_smul, b.2 σ hσ]⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun v => by
        change v 0 • ((a + b : bstInv p K) : Bst p) = v 0 • (a : Bst p) + v 0 • (b : Bst p)
        rw [Submodule.coe_add, smul_add])
      map_smul' := fun c b => Subtype.ext (LinearMap.ext fun v => by
        change v 0 • ((c • b : bstInv p K) : Bst p) = c • (v 0 • (b : Bst p))
        rw [Submodule.coe_smul, smul_comm]) }
  let L : dstSpace p K (1 : GQp p →* GL (Fin 1) ℚ_[p]) ≃ₗ[ℚ_[p]] bstInv p K :=
    LinearEquiv.ofLinear F G (LinearMap.ext fun b => Subtype.ext (by
        change (1 : ℚ_[p]) • (b : Bst p) = b
        rw [one_smul]))
      (LinearMap.ext fun φ => Subtype.ext (LinearMap.ext fun v => by
        change v 0 • (φ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] Bst p) e = (φ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] Bst p) v
        conv_rhs => rw [hv v]
        rw [map_smul]))
  rw [IsSemistableOver, L.finrank_eq, Module.finrank_self, mul_one, mul_one]

/-- The trivial representation is potentially semistable (take `K = ℚ_p`). -/
theorem isPst_trivial : IsPst p (1 : GQp p →* GL (Fin 1) ℚ_[p]) :=
  ⟨⊥, inferInstance, isSemistableOver_trivial p ⊥⟩

end HDec.PkgI4.Pst

#print axioms HDec.PkgI4.Pst.isPst_trivial
