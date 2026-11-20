import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-! Assemble alternating pairings on the primary components of a torsion
abelian group. Both the pairing and its radical are determined one prime
at a time because every element has finite support. -/

noncomputable section

namespace ZInQ.Manuscript.CasselsTateGlobal

open SelmerTwoPower DirectSum IsDedekindDomain
open scoped DirectSum

private theorem map_mem_divisiblePart {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) {x : A} (hx : x ∈ divisiblePart A) : f x ∈ divisiblePart B := by
  apply le_divisiblePart (H := (divisiblePart A).map f) _ ⟨x, hx, rfl⟩
  rintro _ ⟨y, hy, rfl⟩ n hn
  obtain ⟨z, hz, hzy⟩ := divisiblePart_divisible hy hn
  exact ⟨f z, ⟨z, hz, rfl⟩, (map_nsmul f n z).symm.trans (congrArg f hzy)⟩

private abbrev HasPairing (A : Type*) [AddCommGroup A] : Prop :=
  ∃ b : A →+ A →+ QZ, (∀ x, b x x = 0) ∧
    ∀ x, (∀ y, b x y = 0) ↔ x ∈ divisiblePart A

private theorem hasPairing_of_equiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (h : HasPairing B) : HasPairing A := by
  obtain ⟨b, hAlt, hRad⟩ := h
  refine ⟨(b.compl₂ e.toAddMonoidHom).comp e.toAddMonoidHom, fun x => hAlt (e x), ?_⟩
  intro x
  change (∀ y, b (e x) (e y) = 0) ↔ x ∈ divisiblePart A
  constructor
  · intro hx
    have h := (hRad (e x)).mp (e.surjective.forall.mpr hx)
    simpa using map_mem_divisiblePart e.symm.toAddMonoidHom h
  · intro hx y
    exact (hRad (e x)).mpr (map_mem_divisiblePart e.toAddMonoidHom hx) (e y)

private theorem hasPairing_directSum {ι : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)]
    (h : ∀ i, HasPairing (P i)) : HasPairing (⨁ i, P i) := by
  classical
  choose b alt rad using h
  let β : (⨁ i, P i) →+ (⨁ i, P i) →+ QZ :=
    DirectSum.toAddMonoid fun i => (b i).compl₂ (DFinsupp.evalAddMonoidHom i)
  have left (i) (z : P i) (y : ⨁ i, P i) : β (DirectSum.of P i z) y = b i z (y i) := by
    simp only [β, DirectSum.toAddMonoid_of]
    rfl
  have right (x : ⨁ i, P i) (i) (z : P i) : β x (DirectSum.of P i z) = b i (x i) z := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j w =>
      rw [left]
      by_cases hij : j = i
      · subst j; simp
      · simp [DirectSum.of_eq_of_ne, hij, Ne.symm hij]
    | add x y hx hy => simp [hx, hy]
  refine ⟨β, ?_, ?_⟩
  · intro x
    induction x using DirectSum.induction_on' with
    | h0 => simp
    | hadd i z y hy _ ih =>
      rw [map_add β, AddMonoidHom.add_apply, map_add, map_add, left, left, right, ih]
      simp [hy, alt]
  · intro x
    constructor
    · intro hx
      have hcoord (i) : x i ∈ divisiblePart (P i) :=
        (rad i (x i)).mp fun z => (right x i z).symm.trans (hx _)
      clear hx
      induction x using DirectSum.induction_on' with
      | h0 => exact zero_mem _
      | hadd i z y hy _ ih =>
        apply add_mem
        · apply map_mem_divisiblePart (DirectSum.of P i)
          simpa [hy] using hcoord i
        · apply ih
          intro j
          by_cases hij : j = i
          · subst j; simp [hy]
          · simpa [DirectSum.of_eq_of_ne, hij, Ne.symm hij] using hcoord j
    · intro hx y
      induction y using DirectSum.induction_on with
      | zero => exact map_zero _
      | of i z =>
        rw [right]
        exact (rad i (x i)).mpr (map_mem_divisiblePart (DFinsupp.evalAddMonoidHom i) hx) z
      | add y z hy hz => simp [hy, hz]

/-- A torsion abelian group has an alternating pairing with maximal divisible
radical as soon as each primary component does. -/
theorem pairing_of_primary_pairings (A : Type*) [AddCommGroup A]
    (ht : ∀ x : A, ∃ n : ℕ, 0 < n ∧ n • x = 0)
    (h : ∀ (p : ℕ), p.Prime →
      ∃ b : AddCommGroup.primaryComponent A p →+ AddCommGroup.primaryComponent A p →+ QZ,
        (∀ x, b x x = 0) ∧ ∀ x, (∀ y, b x y = 0) ↔
          x ∈ divisiblePart (AddCommGroup.primaryComponent A p)) :
    ∃ b : A →+ A →+ QZ, (∀ x, b x x = 0) ∧
      ∀ x, (∀ y, b x y = 0) ↔ x ∈ divisiblePart A := by
  classical
  have hT : Module.IsTorsion ℤ A := by
    intro x
    obtain ⟨n, hn, hx⟩ := ht x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    simpa only [Submonoid.smul_def, natCast_zsmul] using hx
  let M (v : HeightOneSpectrum ℤ) := Ideal.primaryComponent A v.asIdeal
  have hI : DirectSum.IsInternal M := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (Ideal.iSupIndep_primaryComponent ℤ A) (Ideal.iSup_primaryComponent_eq_top hT)
  apply hasPairing_of_equiv (AddEquiv.ofBijective (DirectSum.coeAddMonoidHom M) hI).symm
  apply hasPairing_directSum
  intro v
  let p := (Submodule.IsPrincipal.generator v.asIdeal).natAbs
  have hp : p.Prime := Int.prime_iff_natAbs_prime.mp
    (Submodule.IsPrincipal.prime_generator_of_isPrime _ v.ne_bot)
  have hspan : Ideal.span {(p : ℤ)} = v.asIdeal := by simp [p]
  have he : (M v).toAddSubgroup = AddCommGroup.primaryComponent A p := by
    ext x
    change x ∈ Ideal.primaryComponent A v.asIdeal ↔ _
    rw [Ideal.primaryComponent_mem, AddCommGroup.mem_primaryComponent, ← hspan]
    simp only [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq,
      Submodule.mem_torsionBy_iff, ← Nat.cast_pow, natCast_zsmul]
  exact hasPairing_of_equiv (AddEquiv.addSubgroupCongr he) (h p hp)

end ZInQ.Manuscript.CasselsTateGlobal
