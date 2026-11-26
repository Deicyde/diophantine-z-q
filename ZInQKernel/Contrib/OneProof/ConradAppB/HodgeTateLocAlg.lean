import ZInQKernel.Contrib.OneProof.ConradAppB.Defs
import ZInQKernel.Contrib.OneProof.C8LocAlg
import ZInQKernel.OneProof.H.TailT
import ZInQKernel.Contrib.OneProof.AxSenTate
import ZInQKernel.Contrib.OneProof.TateTwistInvariants
import ZInQKernel.Contrib.CloudB3W11AxCompletion.GaloisAction
import ZInQKernel.Contrib.CloudB3W11Cyclotomic.InfiniteImage
import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character

/-!
# Conrad's Appendix B over `ℚ_p` from the weight-zero finite-inertia theorem

Let `E/ℚ_p` be finite inside `ℚ̄_p` and let `ψ : G_{ℚ_p} → E^×` be a continuous character which is
Hodge–Tate with a single weight `w` (convention: the cyclotomic character `χ` has weight `−1`). We
prove `HDec.G0Galois.C8Conrad.ConradAppBQp`: `ψ` is locally algebraic of exponent `w`, i.e.
`ψ(Art u) = u^w` for every unit `u ≡ 1 mod p^k` (`k` large) and every Artin lift `Art u`
(B. Conrad, *Lifting global representations with local properties*, App. B, pp. 32-33, base field
`ℚ_p`; J.-P. Serre, *Abelian l-adic representations and elliptic curves*, Ch. III, A.5). The only
input is the rank-one weight-zero case of Sen's theorem, `SenFiniteInertia`: a continuous character
with values in a finite Galois `L/ℚ_p` and with a nonzero period `c ∈ ℂ_p`, `σ(c) = χ(σ) c` on
`G_L`, has finite image on `G_L ∩ I` (S. Sen, *Lie algebras of Galois groups arising from
Hodge–Tate modules*, Ann. of Math. 97 (1973), 160-170; J.-P. Serre, *Groupes algébriques associés
aux modules de Hodge–Tate*, Astérisque 65 (1979), §1.4).

1. **Twist.** `ψ' = ψ · χ^w` has the single weight `0`: `H_i(ψ χ^s) = H_{i-s}(ψ)`, since the maps
   in `H_i` are `ℚ_p`-linear and `χ(σ)^s ∈ ℚ_p`.
2. **Period.** Over the Galois closure `L` of `E`, the weight-zero line gives a nonzero `c ∈ ℂ_p`
   with `σ(c) = ψ'(σ) c` on `G_L` (Tate–Sen coordinates).
3. **Finite inertia.** Sen's theorem gives finitely many values of `ψ'` on `G_L ∩ I`; as `G_L` is
   normal of finite index, all values of `ψ'` on `I` are killed by one `N ≥ 1`.
4. **Local class field theory.** Every unit `z ∈ ℤ_p^×` has an Artin lift in `I`, `χ(Art z) = z⁻¹`,
   and the continuous `ψ` takes one value on all Artin lifts of a given unit (it factors through
   the topological abelianization). By Hensel's lemma every `u ≡ 1 mod p^k` is `z^N` for a unit
   `z`, so for an Artin lift `τ ∈ I` of `z`, `ψ(Art u) = ψ(τ)^N = (ψ'(τ) z^w)^N = z^{Nw} = u^w`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.SenWeightZero



namespace AppB

open Module HDec.G0Galois.C8Conrad

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. The cyclotomic twist shifts the Hodge–Tate weights -/

/-- The cyclotomic character `χ : G_{ℚ_p} → ℤ_p^× ⊆ E^×`. -/
def cycE (E : Type*) [Field E] [Algebra ℚ_[p] E] : _root_.PkgI4.GQp p →* Eˣ :=
  (Units.map ((algebraMap ℚ_[p] E).toMonoidHom.comp
    (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom)).comp
    (ZInQ.Contrib.CloudB3W11Cyclotomic.cycHom p)

/-- A character acts on `E^1` by scalars. -/
theorem charRep_mulVec {E : Type*} [Field E] (ψ : _root_.PkgI4.GQp p →* Eˣ)
    (σ : _root_.PkgI4.GQp p) (v : Fin 1 → E) :
    Matrix.mulVec ((charRep ψ σ : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) v =
      ((ψ σ : Eˣ) : E) • v := by
  ext j
  simp [charRep, Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

theorem twistCycPow_add (σ : _root_.PkgI4.GQp p) (a b : ℤ) :
    HDec.PkgI4.cycPow p σ (a + b) =
      HDec.PkgI4.cycPow p σ a * HDec.PkgI4.cycPow p σ b := by
  simp only [HDec.PkgI4.cycPow, zpow_add, Units.val_mul, PadicInt.coe_mul]

theorem twistCycPow_ne_zero (σ : _root_.PkgI4.GQp p) (a : ℤ) :
    HDec.PkgI4.cycPow p σ a ≠ 0 := by
  rw [HDec.PkgI4.cycPow, Ne, PadicInt.coe_eq_zero]
  exact Units.ne_zero _

section Twist

variable {E : Type*} [Field E] [Algebra ℚ_[p] E]

/-- The twist `ψ · χ^s` of a character `ψ` by the `s`-th power of the cyclotomic character. -/
def cycTwist (ψ : _root_.PkgI4.GQp p →* Eˣ) (s : ℤ) : _root_.PkgI4.GQp p →* Eˣ where
  toFun σ := ψ σ * cycE p E σ ^ s
  map_one' := by simp
  map_mul' σ τ := by rw [map_mul, map_mul, mul_zpow, mul_mul_mul_comm]

theorem cycTwist_apply (ψ : _root_.PkgI4.GQp p →* Eˣ) (s : ℤ)
    (σ : _root_.PkgI4.GQp p) : cycTwist p ψ s σ = ψ σ * cycE p E σ ^ s := rfl

/-- `χ(σ)^s` in `E` is the image of `χ(σ)^s ∈ ℚ_p`. -/
theorem val_cycE_zpow (σ : _root_.PkgI4.GQp p) (s : ℤ) :
    ((cycE p E σ ^ s : Eˣ) : E) = algebraMap ℚ_[p] E (HDec.PkgI4.cycPow p σ s) := by
  show ((Units.map ((algebraMap ℚ_[p] E).toMonoidHom.comp
    (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom)
      (ZInQ.Contrib.CloudB3W11Cyclotomic.cycHom p σ) ^ s : Eˣ) : E) = _
  rw [← map_zpow]
  rfl

variable [FiniteDimensional ℚ_[p] E]

/-- **Twisting shifts the spaces `H_i`**: `H_i(ψ χ^s) = H_{i-s}(ψ)`, because the maps in `H_i` are
`ℚ_p`-linear and `χ(σ)^s ∈ ℚ_p^×`. -/
theorem htSpace_cycTwist (ψ : _root_.PkgI4.GQp p →* Eˣ) (s i : ℤ) :
    HDec.PkgI4.htSpace p (charRep (cycTwist p ψ s)) i =
      HDec.PkgI4.htSpace p (charRep ψ) (i - s) := by
  ext φ
  change (∀ σ v, φ (Matrix.mulVec _ v) = _) ↔ (∀ σ v, φ (Matrix.mulVec _ v) = _)
  refine forall_congr' fun σ => forall_congr' fun v => ?_
  rw [charRep_mulVec, charRep_mulVec, cycTwist_apply, Units.val_mul, val_cycE_zpow,
    mul_comm ((ψ σ : Eˣ) : E), mul_smul, algebraMap_smul,
    map_smul φ (HDec.PkgI4.cycPow p σ s)]
  have hi : HDec.PkgI4.cycPow p σ i =
      HDec.PkgI4.cycPow p σ s * HDec.PkgI4.cycPow p σ (i - s) := by
    rw [← twistCycPow_add]
    congr 1
    ring
  have hc : algebraMap ℚ_[p] ℂ_[p] (HDec.PkgI4.cycPow p σ s) ≠ 0 :=
    (map_ne_zero (algebraMap ℚ_[p] ℂ_[p])).2 (twistCycPow_ne_zero p σ s)
  rw [hi, mul_smul]
  simp only [Algebra.smul_def]
  exact mul_right_inj' hc

/-- The multiplicities of the twist: `m_w(ψ χ^s) = m_{w+s}(ψ)` (the weight of `χ` is `−1`). -/
theorem htMult_cycTwist (ψ : _root_.PkgI4.GQp p →* Eˣ) (s w : ℤ) :
    HDec.PkgI4.htMult p (charRep (cycTwist p ψ s)) w =
      HDec.PkgI4.htMult p (charRep ψ) (w + s) := by
  unfold HDec.PkgI4.htMult
  rw [htSpace_cycTwist, show -w - s = -(w + s) by ring]

/-- **Step 1.** If `ψ` has the single Hodge–Tate weight `w`, then `ψ χ^w` has the single weight `0`. -/
theorem hasHTWeights_cycTwist (ψ : _root_.PkgI4.GQp p →* Eˣ) (w : ℤ)
    (h : HDec.PkgI4.HasHTWeights p (charRep ψ) {w}) :
    HDec.PkgI4.HasHTWeights p (charRep (cycTwist p ψ w)) {0} := by
  intro w'
  rw [htMult_cycTwist, h (w' + w), Multiset.count_singleton, Multiset.count_singleton]
  by_cases hw : w' = 0
  · simp [hw]
  · simp [hw]

end Twist

/-- `σ ↦ χ(σ)^s` is continuous (the cyclotomic character is continuous). -/
theorem continuous_cycPow (s : ℤ) :
    Continuous fun σ : _root_.PkgI4.GQp p =>
      algebraMap ℚ_[p] (PadicAlgCl p) (HDec.PkgI4.cycPow p σ s) := by
  have h1 : Continuous fun σ : _root_.PkgI4.GQp p =>
      (HDec.PkgI4.cyc p σ : ℤ_[p]ˣ) :=
    TauCeti.localCyclotomicCharacter_continuous p ℚ_[p]
  have h2 : Continuous fun σ : _root_.PkgI4.GQp p =>
      ((HDec.PkgI4.cyc p σ ^ s : ℤ_[p]ˣ) : ℤ_[p]) :=
    Units.continuous_val.comp ((continuous_zpow s).comp h1)
  have h3 : Continuous fun x : ℤ_[p] => (x : ℚ_[p]) := continuous_subtype_val
  exact (continuous_algebraMap ℚ_[p] (PadicAlgCl p)).comp (h3.comp h2)

/-- The twist of a continuous character is continuous. -/
theorem continuous_cycTwist (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ψ : _root_.PkgI4.GQp p →* Eˣ)
    (hcont : Continuous fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p)) (s : ℤ) :
    Continuous fun σ => (((cycTwist p ψ s σ : Eˣ) : E) : PadicAlgCl p) := by
  have e : (fun σ => (((cycTwist p ψ s σ : Eˣ) : E) : PadicAlgCl p)) = fun σ =>
      (((ψ σ : Eˣ) : E) : PadicAlgCl p) *
        algebraMap ℚ_[p] (PadicAlgCl p) (HDec.PkgI4.cycPow p σ s) := by
    funext σ
    rw [cycTwist_apply, Units.val_mul, val_cycE_zpow]
    rfl
  rw [e]
  exact hcont.mul (continuous_cycPow p s)

/-! ## §2. A weight-zero period over a finite Galois extension (Tate–Sen coordinates) -/

open ZInQ.Contrib.HodgeSplit in
/-- Over a finite Galois coefficient field `L`, a character of the single weight `0` has a nonzero
period `c ∈ ℂ_p`: `σ(c) = χ(σ) c` for `σ ∈ G_L` (Tate's two theorems over `ℚ_p`). -/
theorem exists_zeroPeriod_of_galois (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L] (χ : _root_.PkgI4.GQp p →* Lˣ)
    (hHT : HDec.PkgI4.HasHTWeights p (HDec.G0Galois.C8Conrad.charRep χ) {0}) :
    ∃ c : ℂ_[p], c ≠ 0 ∧ ∀ σ ∈ L.fixingSubgroup,
      ZInQ.Contrib.G9.PkgI4.cpAct p σ c = algebraMap L ℂ_[p] ((χ σ : Lˣ) : L) * c := by
  have h := htMult_eq_finrank_Ysp p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof L (HDec.G0Galois.C8Conrad.charRep χ) 0
  have hHT₀ : ZInQ.Contrib.G9.PkgI4.htMult p (HDec.G0Galois.C8Conrad.charRep χ) 0 = 1 := by
    change HDec.PkgI4.htMult p (HDec.G0Galois.C8Conrad.charRep χ) 0 = 1
    rw [hHT 0, Multiset.count_singleton_self]
  rw [hHT₀, neg_zero] at h
  have hne : Ysp p (HDec.G0Galois.C8Conrad.charRep χ) 0 L ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at h
    exact one_ne_zero h
  obtain ⟨y, hy, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨y 0, ?_, fun σ hσ => ?_⟩
  · intro hzero
    apply hy₀
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]
    exact hzero
  · have e := congrFun (hy σ hσ) 0
    have hm : ((HDec.G0Galois.C8Conrad.charRep χ σ : GL (Fin 1) L) :
        Matrix (Fin 1) (Fin 1) L) 0 0 = (χ σ : L) := by
      simp [HDec.G0Galois.C8Conrad.charRep, Matrix.algebraMap_matrix_apply]
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.transpose_apply, matC,
      Matrix.map_apply, Pi.smul_apply, vAct, cycPow_zero, one_smul, hm, mul_comm] using e.symm

open ZInQ.Contrib.HodgeSplit in
/-- **Step 2.** A character of the single weight `0` with values in a finite `E` extends its
coefficients to the Galois closure `L` of `E` (same values in `ℚ̄_p`, same weights), where it has a
nonzero weight-zero period. -/
theorem exists_galois_zeroPeriod (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] (ψ : _root_.PkgI4.GQp p →* Eˣ)
    (hHT : HDec.PkgI4.HasHTWeights p (HDec.G0Galois.C8Conrad.charRep ψ) {0}) :
    ∃ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] L)
      (_ : IsGalois ℚ_[p] L) (χ : _root_.PkgI4.GQp p →* Lˣ),
      (∀ σ, (((χ σ : Lˣ) : L) : PadicAlgCl p) = (((ψ σ : Eˣ) : E) : PadicAlgCl p)) ∧
      ∃ c : ℂ_[p], c ≠ 0 ∧ ∀ σ ∈ L.fixingSubgroup,
        ZInQ.Contrib.G9.PkgI4.cpAct p σ c = algebraMap L ℂ_[p] ((χ σ : Lˣ) : L) * c := by
  let L := IntermediateField.normalClosure ℚ_[p] E (PadicAlgCl p)
  have : FiniteDimensional ℚ_[p] L := normalClosure.is_finiteDimensional ℚ_[p] E (PadicAlgCl p)
  have : IsGalois ℚ_[p] L := IsGalois.normalClosure ℚ_[p] E (PadicAlgCl p)
  let j := IntermediateField.inclusion (IntermediateField.le_normalClosure E)
  let χ := (Units.map j.toRingHom.toMonoidHom).comp ψ
  have heq (σ : _root_.PkgI4.GQp p) :
      (((χ σ : Lˣ) : L) : PadicAlgCl p) = (((ψ σ : Eˣ) : E) : PadicAlgCl p) := rfl
  let ρ := (Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p))).comp
    (HDec.G0Galois.C8Conrad.charRep ψ)
  have hLift (σ : _root_.PkgI4.GQp p) :
      Matrix.GeneralLinearGroup.map (algebraMap L (PadicAlgCl p))
        (HDec.G0Galois.C8Conrad.charRep χ σ) = ρ σ := by
    apply Units.ext
    ext i k
    change ((Matrix.GeneralLinearGroup.map (algebraMap L (PadicAlgCl p))
      (HDec.G0Galois.C8Conrad.charRep χ σ) : GL (Fin 1) (PadicAlgCl p)) :
        Matrix (Fin 1) (Fin 1) (PadicAlgCl p)) i k =
      ((Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p))
        (HDec.G0Galois.C8Conrad.charRep ψ σ) : GL (Fin 1) (PadicAlgCl p)) :
          Matrix (Fin 1) (Fin 1) (PadicAlgCl p)) i k
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
    have hi : i = k := Subsingleton.elim i k
    subst hi
    simpa [HDec.G0Galois.C8Conrad.charRep, Matrix.algebraMap_matrix_apply] using heq σ
  have hWeights : HDec.PkgI4.HasHTWeights p (HDec.G0Galois.C8Conrad.charRep χ) {0} :=
    fun w => by
      have h := htMult_eq_of_lifts p ρ (HDec.G0Galois.C8Conrad.charRep χ)
        (HDec.G0Galois.C8Conrad.charRep ψ) hLift (fun _ => rfl) w
      exact h.trans (hHT w)
  exact ⟨L, inferInstance, inferInstance, χ, heq, exists_zeroPeriod_of_galois p L χ hWeights⟩

/-! ## §3. From finitely many values on `G_L ∩ I` to a common exponent on `I` -/

/-- If `χ` has finitely many values on `H ⊓ I`, with `H` normal of finite index, then all values of
`χ` on `I` are killed by a common exponent `N ≥ 1` (`σ^{[G:H]} ∈ H ⊓ I`). -/
theorem exists_pow_eq_one_of_finite_inf {G A : Type*} [Group G] [CommGroup A] (χ : G →* A)
    (H I : Subgroup G) [H.Normal] [H.FiniteIndex]
    (hfin : (Set.range fun σ : ↥(H ⊓ I) => χ σ.1).Finite) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ σ ∈ I, χ σ ^ N = 1 := by
  classical
  let J := (χ.comp (H ⊓ I).subtype).range
  have hJ : (J : Set A).Finite := by
    rw [MonoidHom.coe_range]
    exact hfin
  let _ : Fintype J := hJ.fintype
  refine ⟨H.index * Fintype.card J,
    Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Fintype.card_ne_zero, fun σ hσ => ?_⟩
  have hmem : σ ^ H.index ∈ H ⊓ I := ⟨H.pow_index_mem σ, I.pow_mem hσ _⟩
  let η : J := ⟨χ (σ ^ H.index), MonoidHom.mem_range.mpr ⟨⟨_, hmem⟩, rfl⟩⟩
  have hp : η ^ Fintype.card J = 1 := pow_card_eq_one
  rw [pow_mul, ← map_pow]
  exact congrArg (fun z : J => (z : A)) hp

/-! ## §4. Local inputs: Hensel's lemma and local class field theory of `ℚ_p` -/

/-- **Hensel.** For `N ≠ 0` there is `k` such that every unit `u ≡ 1 mod p^k` of `ℤ_p` is the `N`-th
power of a unit (`X^N − u` at `1`: `‖1 − u‖ < ‖N‖²`). -/
theorem exists_pow_eq_of_toZModPow (N : ℕ) (hN : N ≠ 0) :
    ∃ k : ℕ, ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∃ z : ℤ_[p]ˣ, z ^ N = u := by
  have hNp : (N : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hpos : 0 < ‖(N : ℤ_[p])‖ ^ 2 := pow_pos (norm_pos_iff.2 hNp) 2
  have hp1 : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos hp1
  refine ⟨k, fun u hu => ?_⟩
  have hmem : (u : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hu, map_one, sub_self]
  have hle : ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(k : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ k).2 hmem
  have hpk : (p : ℝ) ^ (-(k : ℤ)) = (p : ℝ)⁻¹ ^ k := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  let F : Polynomial ℤ_[p] := Polynomial.X ^ N - Polynomial.C (u : ℤ_[p])
  have hF : F.aeval (1 : ℤ_[p]) = 1 - (u : ℤ_[p]) := by simp [F]
  have hF' : F.derivative.aeval (1 : ℤ_[p]) = (N : ℤ_[p]) := by
    simp [F, Polynomial.derivative_X_pow]
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hF, hF', norm_sub_rev]
    calc ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := hle
      _ = (p : ℝ)⁻¹ ^ k := hpk
      _ < ‖(N : ℤ_[p])‖ ^ 2 := hk
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hzN : z ^ N = (u : ℤ_[p]) := by
    have e : F.aeval z = z ^ N - (u : ℤ_[p]) := by simp [F]
    rw [e, sub_eq_zero] at hz
    exact hz
  have hzu : IsUnit z := (isUnit_pow_iff hN).1 (hzN ▸ u.isUnit)
  exact ⟨hzu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hzN])⟩

/-- A `p`-adic number of norm one has multiplicative valuation one. -/
theorem mulValuation_eq_one_of_norm_eq_one (x : ℚ_[p]) (h : ‖x‖ = 1) :
    Padic.mulValuation x = 1 := by
  have h1 : ¬ Padic.mulValuation x < Padic.mulValuation (1 : ℚ_[p]) := by
    rw [← Padic.norm_lt_norm_iff_mulValuation_lt, h, norm_one]
    exact lt_irrefl 1
  have h2 : ¬ Padic.mulValuation (1 : ℚ_[p]) < Padic.mulValuation x := by
    rw [← Padic.norm_lt_norm_iff_mulValuation_lt, h, norm_one]
    exact lt_irrefl 1
  rw [Valuation.map_one] at h1 h2
  exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)

/-- A `p`-adic number of norm one has valuation one for the `ValuativeRel` valuation of `ℚ_p`. -/
theorem valuation_eq_one_of_norm_eq_one (x : ℚ_[p]) (h : ‖x‖ = 1) :
    ValuativeRel.valuation ℚ_[p] x = 1 := by
  have he : (ValuativeRel.valuation ℚ_[p]).IsEquiv (Padic.mulValuation (p := p)) :=
    ValuativeRel.isEquiv _ _
  exact (he.eq_one_iff_eq_one).2 (mulValuation_eq_one_of_norm_eq_one p x h)

/-- A unit of `ℤ_p` lies in the depth-zero unit filtration of `ℚ_p`. -/
theorem unitsQp_mem_unitFiltration (u : ℤ_[p]ˣ) :
    unitsQp p u ∈ TauCeti.unitFiltration ℚ_[p] 0 := by
  rw [TauCeti.mem_unitFiltration_zero]
  have hn : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.1 u.isUnit
  exact valuation_eq_one_of_norm_eq_one p _ hn

/-- **Every unit of `ℤ_p` has an Artin lift in the inertia group** (local class field theory: the
Artin symbols of the units are the classes in `G^{ab}` of the inertia elements). -/
theorem exists_inertia_isArtinLift (u : ℤ_[p]ˣ) :
    ∃ τ : _root_.PkgI4.GQp p,
      (show Field.absoluteGaloisGroup ℚ_[p] from τ) ∈ TauCeti.inertiaSubgroup ℚ_[p] ∧
        IsArtinLift p τ (unitsQp p u) := by
  have hmem : TauCeti.ClassFieldTheory.artinMap ℚ_[p] (unitsQp p u) ∈
      (TauCeti.unitFiltration ℚ_[p] 0).map (TauCeti.ClassFieldTheory.artinMap ℚ_[p]) :=
    ⟨_, unitsQp_mem_unitFiltration p u, rfl⟩
  rw [TauCeti.ClassFieldTheory.map_artinMap_unitFiltration_zero] at hmem
  obtain ⟨τ, hτ, hτu⟩ := hmem
  exact ⟨τ, hτ, hτu⟩

/-- Artin lifts are multiplicative: `σ^N` is an Artin lift of `u^N`. -/
theorem isArtinLift_pow {σ : _root_.PkgI4.GQp p} {u : ℤ_[p]ˣ}
    (h : IsArtinLift p σ (unitsQp p u)) (N : ℕ) : IsArtinLift p (σ ^ N) (unitsQp p (u ^ N)) := by
  unfold IsArtinLift at h ⊢
  have e1 : unitsQp p (u ^ N) = unitsQp p u ^ N := by
    simp only [unitsQp, map_pow]
  rw [e1, map_pow, ← h]
  rfl

/-- **A continuous character takes one value on the Artin lifts of a given element**: its target
is commutative and its kernel is closed, so it kills the closure of the commutator subgroup. -/
theorem eq_of_isArtinLift {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ψ : _root_.PkgI4.GQp p →* Eˣ)
    (hcont : Continuous fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p))
    {σ τ : _root_.PkgI4.GQp p} {x : ℚ_[p]ˣ} (hσ : IsArtinLift p σ x)
    (hτ : IsArtinLift p τ x) : ψ σ = ψ τ := by
  let ψG : Field.absoluteGaloisGroup ℚ_[p] →* Eˣ := ψ
  have hclosed : IsClosed (ψG.ker : Set (Field.absoluteGaloisGroup ℚ_[p])) := by
    have e : (ψG.ker : Set (Field.absoluteGaloisGroup ℚ_[p])) =
        (fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p)) ⁻¹' {1} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker]
      constructor
      · intro h
        change (((ψG g : Eˣ) : E) : PadicAlgCl p) = 1
        rw [h]
        rfl
      · intro h
        apply Units.ext
        apply Subtype.ext
        exact h
    rw [e]
    exact isClosed_singleton.preimage hcont
  have hker : (commutator (Field.absoluteGaloisGroup ℚ_[p])).topologicalClosure ≤ ψG.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker ψG) hclosed
  have h : (QuotientGroup.mk (show Field.absoluteGaloisGroup ℚ_[p] from σ) :
      Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      QuotientGroup.mk (show Field.absoluteGaloisGroup ℚ_[p] from τ) := hσ.trans hτ.symm
  rw [QuotientGroup.eq] at h
  have h2 := hker h
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2

/-- In a commutative group, `(x a^{-w})^N = 1` gives `x^N = (a^N)^w`. -/
theorem pow_eq_of_mul_inv_zpow {A : Type*} [CommGroup A] (x a : A) (w : ℤ) (N : ℕ)
    (h : (x * a⁻¹ ^ w) ^ N = 1) : x ^ N = (a ^ N) ^ w := by
  have e : (x * a⁻¹ ^ w) ^ N = x ^ N * ((a ^ N) ^ w)⁻¹ := by
    rw [mul_pow, inv_zpow', ← zpow_natCast (a ^ (-w)), ← zpow_mul, ← zpow_natCast a N, ← zpow_mul,
      ← zpow_neg, show -w * (N : ℤ) = -((N : ℤ) * w) by ring]
  rw [e, mul_inv_eq_one] at h
  exact h

end AppB

/-! ## §5. Conrad's Appendix B over `ℚ_p` -/

open HDec.G0Galois.C8Conrad in
/-- **`ConradAppBQp` from the weight-zero finite-inertia theorem.** A continuous character
`ψ : G_{ℚ_p} → E^×` with the single Hodge–Tate weight `w` is locally algebraic of exponent `w`. -/
theorem conradAppBQp_of_sen (hSen : SenFiniteInertia) : HDec.G0Galois.C8Conrad.ConradAppBQp := by
  intro p _ E _ ψ hcont hw
  obtain ⟨w, hw⟩ := hw
  -- Step 1: the twist `ψ' = ψ χ^w` has the single weight `0`.
  have hw' := AppB.hasHTWeights_cycTwist p ψ w hw
  have hcont' := AppB.continuous_cycTwist p E ψ hcont w
  -- Step 2: a weight-zero period over a finite Galois `L ⊇ E`.
  obtain ⟨L, hLfd, hLgal, χ, hχ, c, hc0, hc⟩ :=
    AppB.exists_galois_zeroPeriod p E (AppB.cycTwist p ψ w) hw'
  have hχcont : Continuous fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p) := by
    have e : (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p)) =
        fun σ => (((AppB.cycTwist p ψ w σ : Eˣ) : E) : PadicAlgCl p) := funext hχ
    rw [e]
    exact hcont'
  -- Step 3: Sen's theorem, and the finite index of `G_L`.
  have hfin := hSen p L χ hχcont c hc0 fun σ hσ => by
    rw [ZInQ.Contrib.CloudB3W11AxCompletion.galois_smul_eq_cpAct]
    exact hc σ hσ
  have : Finite (_root_.PkgI4.GQp p ⧸ L.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen L)
  have : L.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN0, hN⟩ :=
    AppB.exists_pow_eq_one_of_finite_inf χ L.fixingSubgroup (TauCeti.inertiaSubgroup ℚ_[p]) hfin
  have hN' : ∀ σ ∈ TauCeti.inertiaSubgroup ℚ_[p], AppB.cycTwist p ψ w σ ^ N = 1 := by
    intro σ hσ
    have e1 : (((AppB.cycTwist p ψ w σ ^ N : Eˣ) : E) : PadicAlgCl p) =
        (((AppB.cycTwist p ψ w σ : Eˣ) : E) : PadicAlgCl p) ^ N := by
      rw [Units.val_pow_eq_pow_val]
      rfl
    have e2 : (((χ σ ^ N : Lˣ) : L) : PadicAlgCl p) = (((χ σ : Lˣ) : L) : PadicAlgCl p) ^ N := by
      rw [Units.val_pow_eq_pow_val]
      rfl
    apply Units.ext
    apply Subtype.ext
    rw [e1, ← hχ σ, ← e2, hN σ hσ]
    rfl
  -- Step 4: Hensel and local class field theory.
  obtain ⟨k, hk⟩ := AppB.exists_pow_eq_of_toZModPow p N hN0
  refine ⟨w, k, fun u hu σ hσ => ?_⟩
  obtain ⟨z, rfl⟩ := hk u hu
  obtain ⟨τ, hτI, hτ⟩ := AppB.exists_inertia_isArtinLift p z
  have hστ : ψ σ = ψ (τ ^ N) := AppB.eq_of_isArtinLift p ψ hcont hσ (AppB.isArtinLift_pow p hτ N)
  have hcyc : HDec.PkgI4.cyc p τ = z⁻¹ := cyc_of_isArtinLift p τ z hτ
  let F : ℤ_[p] →* E := (algebraMap ℚ_[p] E).toMonoidHom.comp
    (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom
  have hcycE : AppB.cycE p E τ = (Units.map F z)⁻¹ := by
    rw [← map_inv]
    show Units.map F (ZInQ.Contrib.CloudB3W11Cyclotomic.cycHom p τ) = Units.map F z⁻¹
    exact congrArg (Units.map F) hcyc
  have h1 := hN' τ hτI
  rw [AppB.cycTwist_apply, hcycE] at h1
  have key := AppB.pow_eq_of_mul_inv_zpow (ψ τ) (Units.map F z) w N h1
  rw [hστ, map_pow, key, Units.val_zpow_eq_zpow_val, ← map_pow]
  rfl

end ZInQ.Contrib.SenWeightZero
