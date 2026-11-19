import ZInQKernel.Contrib.OneProof.RC.O12EisConst.Forms
import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Hecke
import ZInQKernel.HDecomp.Textbook.BrauerNesbitt

/-! Arithmetic Frobenius on the two normalized Eisenstein characters.
Frobenius density and the tree's proved Brauer–Nesbitt theorem identify an
abstract semisimple model representation from its good Hecke traces
(tex 9666–9668, 9762–9771). The matrix comparison is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12EisConst

open AddressGenuine O12 O12Eisenstein PrintsArith TraceLimits Matrix Filter Topology
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

private def natChar {m : ℕ} (χ : DirichletCharacter K m) : ℕ →* K :=
  χ.toMonoidHom.comp (Nat.castRingHom (ZMod m)).toMonoidHom

private theorem divisorCoeff_prime {m₁ m₂ q : ℕ} (a : DirichletCharacter K m₁)
    (b : DirichletCharacter K m₂) (hq : q.Prime) :
    divisorCoeff a b q = a q + (q : K) * b q := by
  change divisorCoeff a b q = natChar a q + (q : K) * natChar b q
  rw [← ThetaCoeff.eisenstein_at_prime (natChar a) (natChar b) hq]
  unfold divisorCoeff ThetaCoeff.eisenstein
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  have h := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have h₁ : x.1 ≠ 0 := fun e => hq.ne_zero (by simpa [e] using h.symm)
  change _ = (if x.1 = 0 then 0 else natChar a x.1) * ((x.2 : K) * natChar b x.2)
  simp only [h₁, ite_false]
  change a (x.1 : ZMod m₁) * (b (x.2 : ZMod m₂) * (x.2 : K)) =
    a (x.1 : ZMod m₁) * ((x.2 : K) * b (x.2 : ZMod m₂))
  exact congrArg (a (x.1 : ZMod m₁) * ·) (mul_comm _ _)

private theorem dirichlet_at_frob {m q : ℕ} [NeZero m] (χ : DirichletCharacter K m)
    (hq : q.Prime) (hm : q.Coprime m) {g : GalQ} (hg : IsFrobAt g q) :
    (dirichletGalois χ g : K) = χ (q : ZMod m) :=
  congrArg χ (cycChar_of_isFrobAt m hq hm hg)

/-- This evaluation needs only a genuine arithmetic Frobenius, with no
choice of an inertia element at the test prime. -/
theorem weightTwist_at_frob (j : ℤ_[2] →+* K) {q : ℕ} {g : GalQ}
    (hq : q.Prime) (hq₂ : q ≠ 2) (hg : IsFrobAt g q) :
    (weightTwist j g : K) = (q : K) := by
  have h : (cyclotomicCharacter Qbar 2 g.toRingEquiv).val = (q : ℤ_[2]) := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [cyclotomicCharacter.toZModPow, map_natCast]
    exact cycChar_of_isFrobAt (2 ^ n) hq
      ((hq.coprime_iff_not_dvd.mpr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).not.mpr hq₂)).pow_right n) hg
  change j (cyclotomicCharacter Qbar 2 g.toRingEquiv).val = _
  rw [h, map_natCast]

/-- The character sum as an honest `GL₂` homomorphism, with the local
unramified line first. -/
def normalizedRep (E : CharacterPair K p) (j : ℤ_[2] →+* K) :
    GalQ →* GL (Fin 2) K where
  toFun g := ⟨diagonal ![(E.unramLine j g : K), (E.ramLine j g : K)],
    diagonal ![((E.unramLine j g)⁻¹ : K), ((E.ramLine j g)⁻¹ : K)], by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      ext i
      fin_cases i <;> simp, by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      ext i
      fin_cases i <;> simp⟩
  map_one' := Units.ext (by
    change diagonal ![(E.unramLine j 1 : K), (E.ramLine j 1 : K)] = 1
    rw [← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp)
  map_mul' g h := Units.ext (by
    change diagonal ![(E.unramLine j (g * h) : K), (E.ramLine j (g * h) : K)] =
      diagonal ![(E.unramLine j g : K), (E.ramLine j g : K)] *
      diagonal ![(E.unramLine j h : K), (E.ramLine j h : K)]
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp)

theorem normalizedRep_matrix (E : CharacterPair K p) (j : ℤ_[2] →+* K) (g : GalQ) :
    (↑(normalizedRep E j g) : Matrix (Fin 2) (Fin 2) K) =
      diagonal ![(E.unramLine j g : K), (E.ramLine j g : K)] := rfl

/-- At good arithmetic Frobenius, trace is the primitive divisor sum and
determinant is the product nebentypus times the cyclotomic value. -/
theorem normalizedRep_good (E : CharacterPair K p) (j : ℤ_[2] →+* K) {q : ℕ} {g : GalQ}
    (hq : q.Prime) (hq₂ : q ≠ 2) (hu : q.Coprime E.unramLevel)
    (hr : q.Coprime (p * E.awayLevel)) (hg : IsFrobAt g q) :
    (↑(normalizedRep E j g) : Matrix (Fin 2) (Fin 2) K).trace = E.coeff q ∧
    (↑(normalizedRep E j g) : Matrix (Fin 2) (Fin 2) K).det =
      (q : K) * (E.unram q * E.ramified q) := by
  have h₁ := dirichlet_at_frob E.unram hq hu hg
  have h₂ := dirichlet_at_frob E.ramified hq hr hg
  have ht := weightTwist_at_frob j hq hq₂ hg
  cases he : E.twistUnramified <;>
    simp [normalizedRep_matrix, Fin.sum_univ_two, Fin.prod_univ_two,
      CharacterPair.unramLine, CharacterPair.ramLine, CharacterPair.coeff, he,
      h₁, h₂, ht, divisorCoeff_prime _ _ hq] <;> constructor <;> ring

/-- Semisimplicity in the matrix form used by the tree's Brauer–Nesbitt proof. -/
def MatrixSemisimple {G : Type} [Group G] (ρ : G →* GL (Fin 2) K) : Prop :=
  ∀ W : Submodule K (Fin 2 → K),
    (∀ g, W.map (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) K)) ≤ W) →
    ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) K)) ≤ W'

/-- The inertia flip yields the two projections `(1 ± ρ(τ))/2`. Thus any
invariant subspace is a sum of axes, and the unused axes form its complement. -/
theorem normalizedRep_semisimple [CharZero K] (E : CharacterPair K p) (j : ℤ_[2] →+* K)
    (hp₂ : p ≠ 2) (P : LocalPair p) : MatrixSemisimple (normalizedRep E j) := by
  classical
  intro W hW
  let H := Matrix.toLin' (↑(normalizedRep E j P.τ) : Matrix (Fin 2) (Fin 2) K)
  obtain ⟨h₀, h₁⟩ := E.inertia_lines j hp₂ P
  have ht (x : Fin 2 → K) (i : Fin 2) : H x i = (![1, -1] : Fin 2 → K) i * x i := by
    simp only [H, normalizedRep_matrix, h₀, h₁, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have ax (i : Fin 2) (x : Fin 2 → K) (hx : x ∈ W) : Pi.single i (x i) ∈ W := by
    have hx' : H x ∈ W := hW P.τ ⟨x, hx, rfl⟩
    fin_cases i
    · change Pi.single (0 : Fin 2) (x 0) ∈ W
      have h : Pi.single (0 : Fin 2) (x 0) = (2 : K)⁻¹ • (x + H x) := by
        ext a
        fin_cases a <;> simp [ht]
        field_simp
        ring
      rw [h]
      exact W.smul_mem _ (W.add_mem hx hx')
    · change Pi.single (1 : Fin 2) (x 1) ∈ W
      have h : Pi.single (1 : Fin 2) (x 1) = (2 : K)⁻¹ • (x - H x) := by
        ext a
        fin_cases a <;> simp [ht]
        field_simp
        ring
      rw [h]
      exact W.smul_mem _ (W.sub_mem hx hx')
  have ax_smul (i : Fin 2) (a b : K) :
      a • Pi.single i b = Pi.single i (a * b) := by
    ext k
    by_cases h : k = i <;> simp [h]
  let W' : Submodule K (Fin 2 → K) :=
    Submodule.pi Set.univ (fun i => if Pi.single i (1 : K) ∈ W then ⊥ else ⊤)
  have memW' (x : Fin 2 → K) : x ∈ W' ↔ ∀ i, Pi.single i (1 : K) ∈ W → x i = 0 := by
    rw [Submodule.mem_pi]
    simp only [Set.mem_univ, forall_const]
    apply forall_congr'
    intro i
    by_cases hi : Pi.single i (1 : K) ∈ W
    · rw [ite_eq_left hi, Submodule.mem_bot]
      exact ⟨fun h _ => h, fun h => h hi⟩
    · rw [ite_eq_right hi]
      exact ⟨fun _ h => (hi h).elim, fun _ => Submodule.mem_top⟩
  refine ⟨W', ?_, ?_⟩
  · apply isCompl_iff.mpr
    constructor
    · rw [disjoint_iff_inf_le]
      intro x hx
      change x = 0
      funext i
      by_contra hn
      have he := W.smul_mem (x i)⁻¹ (ax i x hx.1)
      rw [ax_smul, inv_mul_cancel₀ hn] at he
      exact hn ((memW' x).mp hx.2 i he)
    · rw [codisjoint_iff_le_sup]
      intro x _
      have hsum : (∑ i : Fin 2, Pi.single i (x i)) = x := by
        funext i
        rw [Finset.sum_apply, Finset.sum_eq_single i]
        · simp
        · intro k _ hk
          exact Pi.single_eq_of_ne (Ne.symm hk) _
        · simp
      rw [← hsum]
      apply Submodule.sum_mem
      intro i _
      by_cases hi : Pi.single i (1 : K) ∈ W
      · apply Submodule.mem_sup_left
        simpa only [ax_smul, mul_one] using W.smul_mem (x i) hi
      · apply Submodule.mem_sup_right
        apply (memW' _).mpr
        intro k hk
        have hki : k ≠ i := fun e => hi (by simpa only [e] using hk)
        exact Pi.single_eq_of_ne hki _
  · intro g y hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply (memW' _).mpr
    intro i hi
    simp [normalizedRep_matrix, Matrix.toLin'_apply, Matrix.mulVec_diagonal, (memW' x).mp hx i hi]

private theorem continuous_dirichlet {m : ℕ} [NeZero m] [TopologicalSpace K]
    [IsTopologicalRing K] (χ : DirichletCharacter K m) :
    Continuous fun g : GalQ => (dirichletGalois χ g : K) := by
  let f : GalQ →* K := (Units.coeHom K).comp (dirichletGalois χ)
  apply continuous_of_continuousAt_one f
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar m
  let E := IntermediateField.adjoin ℚ ({ζ} : Set Qbar)
  have hfix : ∀ᶠ g : GalQ in nhds 1, g ∈ E.fixingSubgroup :=
    (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  have heq : ∀ᶠ g in nhds (1 : GalQ), f 1 = f g := hfix.mono fun g hg => by
    have h : g ζ = ζ := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hg
      exact hg ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    have he := (cycChar_spec m g ζ hζ.pow_eq_one).symm.trans
      (h.trans (cycChar_spec m (1 : GalQ) ζ hζ.pow_eq_one))
    have hv := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) he
    have hc : cycChar m g = cycChar m 1 := Units.ext (ZMod.val_injective m hv)
    simp [f, dirichletGalois, hc]
  exact tendsto_const_nhds.congr' heq

private theorem continuous_normalizedTrace [TopologicalSpace K] [IsTopologicalRing K]
    (E : CharacterPair K p) (j : ℤ_[2] →+* K) (hj : Continuous j) :
    Continuous fun g => (↑(normalizedRep E j g) : Matrix (Fin 2) (Fin 2) K).trace := by
  have ht : Continuous fun g : GalQ => (weightTwist j g : K) :=
    hj.comp (Units.continuous_val.comp (cyclotomicCharacter.continuous 2 ℚ Qbar))
  have hu := continuous_dirichlet E.unram
  have hr := continuous_dirichlet E.ramified
  by_cases he : E.twistUnramified = true
  · have h : Continuous fun g =>
        (dirichletGalois E.unram g : K) * (weightTwist j g : K) +
          (dirichletGalois E.ramified g : K) := (hu.mul ht).add hr
    simpa [normalizedRep_matrix, CharacterPair.unramLine, CharacterPair.ramLine, he,
      Fin.sum_univ_two] using h
  · have h : Continuous fun g =>
        (dirichletGalois E.unram g : K) +
          (dirichletGalois E.ramified g : K) * (weightTwist j g : K) := hu.add (hr.mul ht)
    simpa [normalizedRep_matrix, CharacterPair.unramLine, CharacterPair.ramLine, he,
      Fin.sum_univ_two] using h

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L} {X : GaloisConstituentModel T R ap B chiType}

/-- ELLIOT (tex 9649–9654, 9762–9771): the existing representation is a
continuous semisimple attachment to this Eisenstein constituent. The test
is at the **underlying** series' good Hecke eigenvalue, even for an old copy
whose coefficient at the test prime can vanish. -/
structure RepInput [TopologicalSpace X.K] (E : CharacterPair X.K p)
    (i : X.I) (avoid : Finset ℕ) : Prop where
  semisimple : MatrixSemisimple (X.ρ i)
  continuous_trace : Continuous fun g => (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K).trace
  unramified : ∀ q, T.Good q → q ∉ avoid → ∀ Q : Ideal Zbar, Q.IsMaximal →
    ((q : ℤ) : Zbar) ∈ Q → ∀ σ ∈ Q.inertia GalQ, X.ρ i σ = 1
  trace_at_test : ∀ q, T.Good q → q ∉ avoid →
    (↑(X.ρ i (X.frob q)) : Matrix (Fin 2) (Fin 2) X.K).trace = E.coeff q

/-- The model representation is the normalized character sum in a single
basis over the actual coefficient field. -/
theorem RepInput.split [CharZero X.K] [TopologicalSpace X.K] [IsTopologicalRing X.K]
    [T2Space X.K] {E : CharacterPair X.K p} {i : X.I} {avoid : Finset ℕ}
    (ρ : RepInput (X := X) E i avoid) (j : ℤ_[2] →+* X.K) (hj : Continuous j)
    (hp₂ : p ≠ 2) (P : LocalPair p) :
    ∃ b : GL (Fin 2) X.K, ∀ g : GalQ,
      (↑(b * X.ρ i g * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) =
        diagonal ![(E.unramLine j g : X.K), (E.ramLine j g : X.K)] := by
  let avoid' := avoid ∪ (pairLevel E).primeFactors
  have hn : pairLevel E ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne E.awayLevel))
      (NeZero.ne E.unramLevel)
  have htr := ρ.continuous_trace.ext_on (dense_frobeniusTests T avoid')
    (continuous_normalizedTrace E j hj) (by
    rintro g ⟨q, hq, hq', hg⟩
    have hqa : q ∉ avoid := fun e => hq' (Finset.mem_union_left _ e)
    have hqM : ¬ q ∣ pairLevel E := fun e => hq' (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hq.1, e, hn⟩))
    obtain ⟨τ, Q, hQ, hqQ, hι⟩ := IsFrobAt.exists_mul_inv_mem_inertia hq.1 hg (X.frob_spec q hq)
    have hρ := ρ.unramified q hq hqa Q hQ hqQ _ hι
    rw [map_mul, map_inv, mul_inv_eq_one] at hρ
    change (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K).trace = _
    rw [hρ, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      Matrix.trace_units_conj, ρ.trace_at_test q hq hqa]
    symm
    refine (normalizedRep_good E j hq.1 hq.ne_two ?_ ?_ hg).1
    · exact hq.1.coprime_iff_not_dvd.mpr fun h => hqM (h.trans (dvd_mul_left _ _))
    · exact hq.1.coprime_iff_not_dvd.mpr fun h => hqM (h.trans (dvd_mul_right _ _)))
  obtain ⟨b, hb⟩ := TSkolemKW.hsynBrauerNesbitt GalQ X.K 2 (X.ρ i) (normalizedRep E j)
    ρ.semisimple (normalizedRep_semisimple E j hp₂ P) (congrFun htr)
  exact ⟨b, fun g => by rw [← hb g, normalizedRep_matrix]⟩

#print axioms divisorCoeff_prime
#print axioms dirichlet_at_frob
#print axioms weightTwist_at_frob
#print axioms normalizedRep_matrix
#print axioms normalizedRep_good
#print axioms normalizedRep_semisimple
#print axioms continuous_dirichlet
#print axioms continuous_normalizedTrace
#print axioms RepInput.split

end ZInQ.Manuscript.RC.O12EisConst
