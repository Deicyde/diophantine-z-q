import ZInQKernel.Contrib.OneProof.PanBergerFontaine

/-! pb-dimform scratch: model independence of Fontaine's admissibility (dimension form). -/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace PstModel

open Module BergerBst PanBergerSplit
open scoped TensorProduct

/-! ## §1. Rank of a finite power over a domain -/

section RankPi

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-- Over a domain (rank-nullity, `IsDomain.hasRankNullity`), `rank (M^d) = d · rank M`, with no freeness. -/
theorem rank_fin_pi (d : ℕ) : Module.rank R (Fin d → M) = d * Module.rank R M := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← (Fin.consLinearEquiv R (fun _ : Fin (d + 1) => M)).rank_eq]
    rw [LinearMap.rank_eq_of_surjective (f := LinearMap.fst R M (Fin d → M)) LinearMap.fst_surjective,
      LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective, ih]
    push_cast
    ring

theorem finrank_fin_pi (d : ℕ) : finrank R (Fin d → M) = d * finrank R M := by
  unfold finrank
  rw [rank_fin_pi, Cardinal.toNat_mul, Cardinal.toNat_natCast]

/-- The same for a submodule (so that the instance on `↥N` is the submodule's). -/
theorem finrank_fin_pi_sub {M' : Type*} [AddCommGroup M'] [Module R M'] (N : Submodule R M') (d : ℕ) :
    finrank R (Fin d → N) = d * finrank R N :=
  finrank_fin_pi d

end RankPi

/-! ## §2. Changing the coefficient field of a model: `L^n ≅ (E^n)^d` -/

section Model

variable (p : ℕ) [Fact p.Prime]
variable {E L : Type*} [Field E] [Field L] [Algebra ℚ_[p] E] [Algebra ℚ_[p] L] [Algebra E L]
  [IsScalarTower ℚ_[p] E L] {d n : ℕ} (b : Basis (Fin d) E L)

/-- `(E^n)^d ≅ L^n`, `(v_j)_j ↦ (Σ_j v_j(i) b_j)_i`, for an `E`-basis `b` of `L`. -/
def phiE : (Fin d → Fin n → E) ≃ₗ[ℚ_[p]] (Fin n → L) where
  toFun v i := b.equivFun.symm (fun j => v j i)
  invFun w j i := b.equivFun (w i) j
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    exact map_add b.equivFun.symm (fun j => v j i) (fun j => w j i)
  map_smul' c v := by
    funext i
    exact (b.equivFun.symm.restrictScalars ℚ_[p]).map_smul c (fun j => v j i)
  left_inv v := by
    funext j i
    change b.equivFun (b.equivFun.symm (fun j => v j i)) j = v j i
    rw [LinearEquiv.apply_symm_apply]
  right_inv w := by
    funext i
    change b.equivFun.symm (fun j => b.equivFun (w i) j) = w i
    exact b.equivFun.symm_apply_apply (w i)

theorem phiE_apply (v : Fin d → Fin n → E) (i : Fin n) :
    phiE p b v i = ∑ j, v j i • b j := by
  simp [phiE, Basis.equivFun_symm_apply]

variable {p b}
variable {ρE : GQp p →* GL (Fin n) E} {ρL : GQp p →* GL (Fin n) L}

theorem phiE_equivariant
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ) (σ : GQp p)
    (v : Fin d → Fin n → E) :
    phiE p b (fun j => vAct p ρE σ (v j)) = vAct p ρL σ (phiE p b v) := by
  funext i
  rw [vAct_apply p ρL, ← hρ σ]
  simp only [phiE_apply, vAct_apply, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [mul_smul, Algebra.smul_def]
  rfl

theorem phiE_symm_equivariant
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ) (σ : GQp p)
    (w : Fin n → L) (j : Fin d) :
    (phiE p b).symm (vAct p ρL σ w) j = vAct p ρE σ ((phiE p b).symm w j) := by
  have h := phiE_equivariant (b := b) hρ σ ((phiE p b).symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h, LinearEquiv.symm_apply_apply]

variable (p b)

/-- `B ⊗ L^n ≅ (B ⊗ E^n)^d`, linear over any `ℚ_p`-algebra `S` acting on `B`. -/
def psi (S A : Type*) [CommRing S] [Algebra ℚ_[p] S] [AddCommGroup A] [Module ℚ_[p] A] [Module S A]
    [IsScalarTower ℚ_[p] S A] :
    (A ⊗[ℚ_[p]] (Fin n → L)) ≃ₗ[S] (Fin d → A ⊗[ℚ_[p]] (Fin n → E)) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S A) (phiE p b).symm ≪≫ₗ
    TensorProduct.piRight ℚ_[p] S A (fun _ : Fin d => Fin n → E)

theorem psi_tmul (S A : Type*) [CommRing S] [Algebra ℚ_[p] S] [AddCommGroup A] [Module ℚ_[p] A]
    [Module S A] [IsScalarTower ℚ_[p] S A] (a : A) (v : Fin n → L) :
    psi p b S A (a ⊗ₜ v) = fun j => a ⊗ₜ ((phiE p b).symm v j) := by
  simp [psi, TensorProduct.piRightHom_tmul]

end Model

/-! ## §3. `D_B(L^n) ≅ D_B(E^n)^d` over `B^H`, hence the admissibility of the two models is equivalent -/

section DB

variable (p : ℕ) [Fact p.Prime]
variable {E L : Type*} [Field E] [Field L] [Algebra ℚ_[p] E] [Algebra ℚ_[p] L] [Algebra E L]
  [IsScalarTower ℚ_[p] E L] {d n : ℕ} (b : Basis (Fin d) E L)
variable {ρE : GQp p →* GL (Fin n) E} {ρL : GQp p →* GL (Fin n) L}
variable (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p))

theorem psi_inclT (x : B ⊗[ℚ_[p]] (Fin n → L)) (j : Fin d) :
    psi p b ℚ_[p] (BdR p) (inclT p B x) j = inclT p B (psi p b (fixedSub p B H) B x j) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp [inclT, psi_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable {p b} in
theorem psi_act (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ) (σ : GQp p)
    (y : BdR p ⊗[ℚ_[p]] (Fin n → L)) (j : Fin d) :
    psi p b ℚ_[p] (BdR p) (TensorProduct.map (bdrLin p σ) (vAct p ρL σ) y) j =
      TensorProduct.map (bdrLin p σ) (vAct p ρE σ) (psi p b ℚ_[p] (BdR p) y j) := by
  induction y using TensorProduct.inductionOn with
  | tmul a v => simp [psi_tmul, phiE_symm_equivariant hρ]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable {p b B H} in
theorem mem_dB_iff (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ)
    (x : B ⊗[ℚ_[p]] (Fin n → L)) :
    x ∈ dB p B H ρL ↔ ∀ j, psi p b (fixedSub p B H) B x j ∈ dB p B H ρE := by
  change (∀ σ ∈ H, TensorProduct.map (bdrLin p σ) (vAct p ρL σ) (inclT p B x) = inclT p B x) ↔
    ∀ j, ∀ σ ∈ H, TensorProduct.map (bdrLin p σ) (vAct p ρE σ) (inclT p B (psi p b (fixedSub p B H) B x j)) =
      inclT p B (psi p b (fixedSub p B H) B x j)
  constructor
  · intro hx j σ hσ
    have h1 := congrFun (congrArg (psi p b ℚ_[p] (BdR p)) (hx σ hσ)) j
    rwa [psi_act hρ, psi_inclT] at h1
  · intro hx σ hσ
    apply (psi p b ℚ_[p] (BdR p)).injective
    funext j
    rw [psi_act hρ, psi_inclT]
    exact hx j σ hσ

set_option synthInstance.maxHeartbeats 400000 in
/-- **`D_{B,H}(L^n) ≅ D_{B,H}(E^n)^d` as `B^H`-modules** (`d = [L : E]`). -/
def dBEquiv (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ) :
    dB p B H ρL ≃ₗ[fixedSub p B H] (Fin d → dB p B H ρE) where
  toFun x j := ⟨psi p b (fixedSub p B H) B x j, (mem_dB_iff (b := b) (B := B) (H := H) hρ (x : B ⊗[ℚ_[p]] (Fin n → L))).1 x.2 j⟩
  map_add' x y := by
    funext j
    apply Subtype.ext
    simp
  map_smul' c x := by
    funext j
    apply Subtype.ext
    exact congrFun (map_smul (psi p b (fixedSub p B H) B) c (x : B ⊗[ℚ_[p]] (Fin n → L))) j
  invFun f := ⟨(psi p b (fixedSub p B H) B).symm (fun j => (f j : B ⊗[ℚ_[p]] (Fin n → E))),
    (mem_dB_iff (b := b) (B := B) (H := H) hρ _).2 (fun j => by
      rw [LinearEquiv.apply_symm_apply]
      exact (f j).2)⟩
  left_inv x := by
    apply Subtype.ext
    exact (psi p b (fixedSub p B H) B).symm_apply_apply (x : B ⊗[ℚ_[p]] (Fin n → L))
  right_inv f := by
    funext j
    apply Subtype.ext
    exact congrFun ((psi p b (fixedSub p B H) B).apply_symm_apply
      (fun j => (f j : B ⊗[ℚ_[p]] (Fin n → E)))) j

include b in
theorem finrank_V : finrank ℚ_[p] (Fin n → L) = d * finrank ℚ_[p] (Fin n → E) := by
  rw [← (phiE p b (n := n)).finrank_eq, finrank_fin_pi]

include b in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Fontaine's admissibility (dimension form) does not see the coefficient field**: for `E ⊆ L` and the
model `ρ_L = ρ_E ⊗_E L`, `V_E = E^n` is `B`-admissible for `H` iff `V_L = L^n` is, since
`V_L ≅ V_E^{[L:E]}` as `ℚ_p[G]`-modules, so both sides of `dim_{B^H} D_B(V) = dim_{ℚ_p} V` are multiplied by
`[L : E]` (on-the-spot: neither the manuscript nor a cited source states this; standard). -/
theorem isAdmissible_iff_of_basis
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ) :
    IsAdmissible p B H ρL ↔ IsAdmissible p B H ρE := by
  haveI : IsDomain (BdR p) := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).isDomain
  have hd : 0 < d := Fin.pos_iff_nonempty.2 b.index_nonempty
  unfold IsAdmissible
  have key : finrank (fixedSub p B H) (Fin d → dB p B H ρE) = d * finrank (fixedSub p B H) (dB p B H ρE) := by
    have h := finrank_fin_pi_sub (R := fixedSub p B H) (M' := B ⊗[ℚ_[p]] (Fin n → E)) (dB p B H ρE) d
    convert h using 2
  rw [(dBEquiv p b B H hρ).finrank_eq, finrank_V p b, key]
  exact ⟨Nat.eq_of_mul_eq_mul_left hd, fun h => by rw [h]⟩

end DB

/-! ## §4. Models inside `ℚ̄_p` -/

section Models

variable (p : ℕ) [Fact p.Prime] {n : ℕ}

theorem isAdmissible_iff_of_le {E L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hEL : E ≤ L)
    [FiniteDimensional ℚ_[p] L] (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p))
    (ρE : GQp p →* GL (Fin n) E) (ρL : GQp p →* GL (Fin n) L)
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) =
      Matrix.GeneralLinearGroup.map (algebraMap L (PadicAlgCl p)) (ρL σ)) :
    IsAdmissible p B H ρE ↔ IsAdmissible p B H ρL := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[p] E L := IsScalarTower.of_algebraMap_eq (fun c => rfl)
  haveI : FiniteDimensional E L := FiniteDimensional.right ℚ_[p] E L
  haveI : Module.Free E L := Module.Free.of_divisionRing E L
  have hρ' : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ := by
    intro σ
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have h1 := congrArg (fun g : GL (Fin n) (PadicAlgCl p) => g.val i j) (hρ σ)
    simp only [Matrix.GeneralLinearGroup.map_apply] at h1
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact Subtype.ext h1
  exact (isAdmissible_iff_of_basis p (Module.finBasis E L) B H hρ').symm

end Models

/-! ## §5. Potential semistability (dimension form) does not depend on the model -/

section Pst

open FontaineSt BmaxOne

variable (p : ℕ) [Fact p.Prime] {n : ℕ} {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : PanBergerSplit.Ainf p)
  (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)

/-- `IsPstF` is unchanged when the coefficient field of the model is enlarged. -/
theorem isPstF_iff_of_le {E L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hEL : E ≤ L)
    [FiniteDimensional ℚ_[p] L] (ρE : GQp p →* GL (Fin n) E) (ρL : GQp p →* GL (Fin n) L)
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) =
      Matrix.GeneralLinearGroup.map (algebraMap L (PadicAlgCl p)) (ρL σ)) :
    IsPstF p h w hw ρE ↔ IsPstF p h w hw ρL :=
  exists_congr fun K => and_congr_right fun _ =>
    isAdmissible_iff_of_le p hEL (BstFOf p h w hw) K.fixingSubgroup ρE ρL hρ

/-- **Model independence of potential semistability** (dimension form, Fontaine's `B_st`): if
`ρ : G_{ℚ_p} → GL_n(ℚ̄_p)` has two models `ρ_E`, `ρ_{E'}` over finite `E, E' ⊆ ℚ̄_p`, then `ρ_E` is pst iff
`ρ_{E'}` is (compare both with the model over `E ⊔ E'`, `isPstF_iff_of_le`). On-the-spot (standard; not in the
manuscript or a cited source). -/
theorem isPstF_model_iff {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E'] {ρ : GQp p →* GL (Fin n) (PadicAlgCl p)}
    (ρE : GQp p →* GL (Fin n) E) (ρE' : GQp p →* GL (Fin n) E')
    (hE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ)
    (hE' : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E' (PadicAlgCl p)) (ρE' σ) = ρ σ) :
    IsPstF p h w hw ρE ↔ IsPstF p h w hw ρE' := by
  let ρL : GQp p →* GL (Fin n) ↥(E ⊔ E') :=
    (Matrix.GeneralLinearGroup.map (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ E')).toRingHom).comp ρE
  have hL : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap ↥(E ⊔ E') (PadicAlgCl p)) (ρL σ) = ρ σ := by
    intro σ
    rw [← hE σ]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [isPstF_iff_of_le p h w hw le_sup_left ρE ρL (fun σ => (hE σ).trans (hL σ).symm),
    isPstF_iff_of_le p h w hw le_sup_right ρE' ρL (fun σ => (hE' σ).trans (hL σ).symm)]

/-- **The model clause of `LocalIsPstF` is harmless**: for any one model `ρ_E` of `ρ`, `LocalIsPstF ρ` (pst on
some model) holds iff `ρ_E` is pst. -/
theorem localIsPstF_iff_of_model {ρ : GQp p →* GL (Fin n) (PadicAlgCl p)}
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] (ρE : GQp p →* GL (Fin n) E)
    (hE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) :
    LocalIsPstF p h w hw n ρ ↔ IsPstF p h w hw ρE := by
  constructor
  · rintro ⟨E', hE'f, ρE', hE', hpst⟩
    exact (isPstF_model_iff p h w hw ρE ρE' hE hE').2 hpst
  · intro hpst
    exact ⟨E, inferInstance, ρE, hE, hpst⟩

/-- **pst on one finite model iff pst on every finite model** (and some model exists). -/
theorem localIsPstF_iff_forall (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) :
    LocalIsPstF p h w hw n ρ ↔
      (∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
          (ρE : GQp p →* GL (Fin n) E),
          ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
        ∀ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
          (ρE : GQp p →* GL (Fin n) E),
          (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) →
          IsPstF p h w hw ρE := by
  constructor
  · intro hl
    obtain ⟨E, hEf, ρE, hE, _⟩ := id hl
    exact ⟨⟨E, hEf, ρE, hE⟩, fun E' _ ρE' hE' => (localIsPstF_iff_of_model p h w hw E' ρE' hE').1 hl⟩
  · rintro ⟨⟨E, hEf, ρE, hE⟩, hall⟩
    exact ⟨E, hEf, ρE, hE, hall E hEf ρE hE⟩

end Pst

/-! ## §6. `B_cris^+` is the literal printed set of Berger's survey II.3.1

The survey prints `B_cris^+ = {Σ x_n ω^n/n! : x_n ∈ B̃^+, x_n → 0}` with `B̃^+ = A_inf[1/p]` and does not name the
topology in which `x_n → 0`; Brinon-Conrad p. 129 fixes the `p`-adic one for `A_cris` (`a_n ∈ A_inf`). Here
`x_n → 0` in `A_inf[1/p]` for its `p`-adic topology, `A_inf` an open lattice: for every `k`, eventually
`x_n ∈ p^k A_inf` (`PAdicNullLoc`). -/

section Printed

open FontaineSt BmaxOne PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

/-- `x_n → 0` in `B̃^+ = A_inf[1/p]` `p`-adically: for every `k`, `x_n ∈ p^k A_inf` for all large `n`. -/
def PAdicNullLoc (c : ℕ → PanBergerSplit.AinfP p) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ a : PanBergerSplit.Ainf p,
    c n = algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p) ((p : PanBergerSplit.Ainf p) ^ k * a)

/-- **The set printed in Berger's survey II.3.1, literally**: `{Σ x_n ω^n/n! : x_n ∈ B̃^+, x_n → 0}`, the
series evaluated `ker θ`-adically in `B_dR^+` and mapped to `B_dR` (`ω = w`, any generator of `ker θ`). -/
def BcrisPlusPrinted (w : PanBergerSplit.Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    Set (BdR p) :=
  {x | ∃ c : ℕ → PanBergerSplit.AinfP p, PAdicNullLoc p c ∧
    x = toBdR p (evalB p (algebraMap_mem_ith p hw)
      (PowerSeries.mk fun n => c n * qpToLoc p (((n.factorial : ℕ) : ℚ_[p]))⁻¹))}

theorem toBdR_evalB_C_mul {x : PanBergerSplit.AinfP p} (hx : x ∈ Ith p) (r : ℚ_[p])
    (F : (PanBergerSplit.AinfP p)⟦X⟧) :
    toBdR p (evalB p hx (C (qpToLoc p r) * F)) = r • toBdR p (evalB p hx F) := by
  rw [map_mul, map_mul, Algebra.smul_def]
  congr 1
  change toBdR p (psEval (Ith p) hx (C (qpToLoc p r))) = _
  rw [psEval_C]
  rfl

theorem mk_eq_C_mul_dpSeries (r : ℚ_[p]) (f : (PanBergerSplit.Ainf p)⟦X⟧) :
    (PowerSeries.mk fun n => qpToLoc p r *
        algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p) (PowerSeries.coeff n f) *
        qpToLoc p (((n.factorial : ℕ) : ℚ_[p]))⁻¹) = C (qpToLoc p r) * dpSeries p f := by
  ext n
  rw [coeff_mk, coeff_C_mul, dpSeries, coeff_mk, mul_assoc]

theorem qpToLoc_inv_mul :
    qpToLoc p ((p : ℚ_[p])⁻¹) * algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p) (p : PanBergerSplit.Ainf p) = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [map_natCast, ← map_natCast (qpToLoc p) p, ← map_mul, inv_mul_cancel₀ hp0, map_one]

/-- **`B_cris^+` is exactly the literal printed set of survey II.3.1** (with `x_n → 0` `p`-adically in
`A_inf[1/p]`): `BcrisPlusPrinted = p^{−k} A_cris`, so with `bcrisPlusOf_eq_set` it is `BcrisPlusOf`. -/
theorem bcrisPlusPrinted_eq_set {w : PanBergerSplit.Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    BcrisPlusPrinted p w hw = BcrisPlusSet p w hw := by
  have hinj := IsLocalization.injective (PanBergerSplit.AinfP p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ZInQ.Contrib.G9.BdrKer.Cp.witt_p_ne_zero p))
  have hu1 : qpToLoc p ((p : ℚ_[p])⁻¹) * (algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p)) (p : PanBergerSplit.Ainf p) = 1 := qpToLoc_inv_mul p
  apply Set.Subset.antisymm
  · -- printed ⊆ `p^{−K} A_cris`
    rintro x ⟨c, hc, rfl⟩
    obtain ⟨N0, hN0⟩ := hc 0
    have hsurj : ∀ n, ∃ (m : ℕ) (a : PanBergerSplit.Ainf p), (algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p)) (p : PanBergerSplit.Ainf p) ^ m * c n = (algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p)) a := by
      intro n
      obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (p : PanBergerSplit.Ainf p)) (c n)
      refine ⟨m, a, ?_⟩
      rw [← ha, map_pow, mul_comm]
    choose m a0 hma using hsurj
    let K : ℕ := ∑ n ∈ Finset.range N0, m n
    have hK : ∀ n, ∃ a : PanBergerSplit.Ainf p, (algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p)) (p : PanBergerSplit.Ainf p) ^ K * c n = (algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p)) a := by
      intro n
      by_cases hn : n < N0
      · have hle : m n ≤ K := Finset.single_le_sum (fun i _ => Nat.zero_le (m i)) (Finset.mem_range.2 hn)
        refine ⟨(p : PanBergerSplit.Ainf p) ^ (K - m n) * a0 n, ?_⟩
        rw [map_mul, ← hma n, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      · obtain ⟨b, hb⟩ := hN0 n (not_lt.1 hn)
        refine ⟨(p : PanBergerSplit.Ainf p) ^ K * b, ?_⟩
        rw [hb, pow_zero, one_mul, map_mul, map_pow]
    choose a ha using hK
    have hcn : ∀ n, c n = qpToLoc p ((p : ℚ_[p])⁻¹ ^ K) * (algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p)) (a n) := by
      intro n
      rw [map_pow, ← ha n, ← mul_assoc, ← mul_pow, hu1, one_pow, one_mul]
    refine ⟨K, evalB p (algebraMap_mem_ith p hw) (dpSeries p (PowerSeries.mk a)),
      ⟨PowerSeries.mk a, ?_, rfl⟩, ?_⟩
    · intro j
      obtain ⟨Nj, hNj⟩ := hc j
      refine ⟨max Nj N0, fun n hn => ?_⟩
      obtain ⟨b, hb⟩ := hNj n (le_of_max_le_left hn)
      beta_reduce
      rw [PowerSeries.coeff_mk]
      refine ⟨(p : PanBergerSplit.Ainf p) ^ K * b, hinj ?_⟩
      rw [← ha n, hb]
      simp only [map_mul, map_pow]
      ring
    · rw [← toBdR_evalB_C_mul, ← mk_eq_C_mul_dpSeries]
      congr 3
      funext n
      rw [hcn n, PowerSeries.coeff_mk]
  · -- `p^{−k} A_cris` ⊆ printed
    rintro x ⟨k, y, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨fun n => qpToLoc p ((p : ℚ_[p])⁻¹ ^ k) * (algebraMap (PanBergerSplit.Ainf p) (PanBergerSplit.AinfP p)) (PowerSeries.coeff n f), ?_, ?_⟩
    · intro j
      obtain ⟨N, hN⟩ := hf (j + k)
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨b, hb⟩ := hN n hn
      refine ⟨b, ?_⟩
      beta_reduce at hb ⊢
      rw [hb]
      simp only [map_mul, map_pow, pow_add]
      rw [show ∀ (A P B : PanBergerSplit.AinfP p), A ^ k * (P ^ j * P ^ k * B) = (A * P) ^ k * (P ^ j * B) from
        fun A P B => by ring, hu1, one_pow, one_mul]
    · rw [← toBdR_evalB_C_mul, ← mk_eq_C_mul_dpSeries]

/-- **`B_cris^+` (`BcrisPlusOf`, the `ℚ_p`-algebra generated by `A_cris`) is the literal printed set.** -/
theorem bcrisPlusOf_eq_printed {w : PanBergerSplit.Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    (BcrisPlusOf p w hw : Set (BdR p)) = BcrisPlusPrinted p w hw := by
  rw [bcrisPlusOf_eq_set, bcrisPlusPrinted_eq_set]

end Printed

end PstModel
end PkgI4
end HDec
