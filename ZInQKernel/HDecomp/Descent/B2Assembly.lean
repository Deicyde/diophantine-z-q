import ZInQKernel.HDecomp.Descent.Chi
import ZInQKernel.HDecomp.Descent.B2Glue

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-descent/B2Assembly.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-descent: B2 over `G_ℚ` from the four leaves L-B2a..d (N5 L665-700)

`b2_of_leaves`: for a finite Galois `L ⊂ ℚ̄` unramified outside a finite set `T` of primes, and
a continuous sign 2-cocycle `ε` of `G_ℚ` inflated from `Gal(L/ℚ)`, the four leaves give a set
`T₋ ⊆ T`, the Dirichlet character `χ = ∏_{p ∈ T₋} χ_p` of `Chi.lean` (level supported in `T`,
order `≤ 2 ∏_{p∈T, p≠2}(p-1)`), and a continuous `β : G_ℚ → ℂ^×` with `β² = χ` and
`dβ = ε`. Everything is over Mathlib's genuine objects (`Field.absoluteGaloisGroup`, `ℚ_[p]`,
`modularCyclotomicCharacter`, `DirichletCharacter`, `𝓞 L`).

Built in the project as `ZInQKernel.HDecomp.Descent.B2Assembly`.
-/

namespace GlueDescent.B2Q

open GlueDescent GlueDescent.B2 NumberField

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem chiLevel_pos (Tm : Finset ℕ) (h : ∀ p ∈ Tm, p.Prime) : 0 < chiLevel Tm :=
  Finset.prod_pos (fun p hp => by have := two_lt_lev (h p hp); omega)

/-- The unit `u ∈ (ℤ/N)^×` with `u ≡ -1 mod p^k`, `u ≡ 1 mod N'` (`N = p^k N'`). -/
theorem exists_crt_unit (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) :
    ∃ u : (ZMod N)ˣ, ((u : ZMod N).cast : ZMod (p ^ N.factorization p)) = -1 ∧
      ((u : ZMod N).cast : ZMod (N / p ^ N.factorization p)) = 1 := by
  have hN : p ^ N.factorization p * (N / p ^ N.factorization p) = N :=
    Nat.ordProj_mul_ordCompl_eq_self N p
  have hcop : Nat.Coprime (p ^ N.factorization p) (N / p ^ N.factorization p) :=
    (Nat.coprime_ordCompl hp (NeZero.ne N)).pow_left _
  generalize N.factorization p = k at hN hcop ⊢
  generalize N / p ^ k = N' at hN hcop ⊢
  let e := ZMod.chineseRemainder hcop
  let φ : ZMod (p ^ k * N') →+* ZMod N := ZMod.castHom (dvd_of_eq hN.symm) (ZMod N)
  have h1 : ∀ z, (((φ z : ZMod N)).cast : ZMod (p ^ k)) = (e z).1 := by
    intro z
    have : (ZMod.castHom (Dvd.intro N' hN) (ZMod (p ^ k))).comp φ =
        (RingHom.fst _ _).comp e.toRingHom := Subsingleton.elim _ _
    simpa [ZMod.castHom_apply] using congrArg (fun f => f z) this
  have h2 : ∀ z, (((φ z : ZMod N)).cast : ZMod N') = (e z).2 := by
    intro z
    have : (ZMod.castHom (Dvd.intro_left _ hN) (ZMod N')).comp φ =
        (RingHom.snd _ _).comp e.toRingHom := Subsingleton.elim _ _
    simpa [ZMod.castHom_apply] using congrArg (fun f => f z) this
  let y := e.symm (-1, 1)
  have hyy : y * y = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    simp [y]
  refine ⟨⟨φ y, φ y, by rw [← map_mul, hyy, map_one], by rw [← map_mul, hyy, map_one]⟩, ?_, ?_⟩
  · show ((φ y : ZMod N).cast : ZMod (p ^ k)) = -1
    rw [h1]; simp [y]
  · show ((φ y : ZMod N).cast : ZMod N') = 1
    rw [h2]; simp [y]

theorem lev_eq_pow (p : ℕ) : ∃ j, 0 < j ∧ lev p = p ^ j := by
  unfold lev
  split_ifs with h
  · exact ⟨2, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨1, by norm_num, (pow_one p).symm⟩

/-- Casting through an intermediate level. -/
theorem cast_cast_of_dvd {a b c : ℕ} (hab : b ∣ a) (hbc : c ∣ b) (x : ZMod a) :
    (((x.cast : ZMod b)).cast : ZMod c) = (x.cast : ZMod c) := by
  have : (ZMod.castHom hbc (ZMod c)).comp (ZMod.castHom hab (ZMod b)) =
      ZMod.castHom (hbc.trans hab) (ZMod c) := Subsingleton.elim _ _
  have h := congrArg (fun f => f x) this
  simp only [RingHom.comp_apply, ZMod.castHom_apply] at h
  exact h

/-- **The value of `χ` at the CRT unit**: `χ(u_p) = -1` if `p ∈ T₋` and `1` otherwise. -/
theorem chi_toUnitHom_crt (Tm : Finset ℕ) (hTm : ∀ q ∈ Tm, q.Prime) (p : ℕ) (hp : p.Prime)
    (u : (ZMod (chiLevel Tm))ˣ)
    (hu1 : ((u : ZMod (chiLevel Tm)).cast :
      ZMod (p ^ (chiLevel Tm).factorization p)) = -1)
    (hu2 : ((u : ZMod (chiLevel Tm)).cast :
      ZMod (chiLevel Tm / p ^ (chiLevel Tm).factorization p)) = 1) :
    (chi Tm).toUnitHom u = if p ∈ Tm then -1 else 1 := by
  have hN0 : chiLevel Tm ≠ 0 := (chiLevel_pos Tm hTm).ne'
  have factor : ∀ q (hq : q ∈ Tm),
      (DirichletCharacter.changeLevel (lev_dvd_chiLevel hq) (oddChar q)).toUnitHom u =
        if q = p then -1 else 1 := by
    intro q hq
    rw [DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_apply]
    split_ifs with hqp
    · subst hqp
      -- lev q ∣ q^k
      obtain ⟨j, hj, hlev⟩ := lev_eq_pow q
      have hdvdN : q ^ j ∣ chiLevel Tm := hlev ▸ lev_dvd_chiLevel hq
      have hjk : j ≤ (chiLevel Tm).factorization q :=
        (hp.pow_dvd_iff_le_factorization hN0).mp hdvdN
      have hlevk : lev q ∣ q ^ (chiLevel Tm).factorization q := hlev ▸ pow_dvd_pow q hjk
      have hval : (ZMod.unitsMap (lev_dvd_chiLevel hq) u : ZMod (lev q)) = -1 := by
        rw [ZMod.unitsMap_val, ← cast_cast_of_dvd (Nat.ordProj_dvd _ _) hlevk, hu1,
          ← ZMod.castHom_apply (h := hlevk) (R := ZMod (lev q)), map_neg, map_one]
      have hu : ZMod.unitsMap (lev_dvd_chiLevel hq) u = -1 := Units.ext (by rw [hval]; rfl)
      rw [hu]
      apply Units.ext
      rw [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one]
      exact oddChar_neg_one hp
    · obtain ⟨j, hj, hlev⟩ := lev_eq_pow q
      have hq' := hTm q hq
      have hnd : ¬ p ∣ lev q := by
        rw [hlev]
        intro h
        exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq').mp (hp.dvd_of_dvd_pow h)).symm
      have hlevN' : lev q ∣ chiLevel Tm / p ^ (chiLevel Tm).factorization p :=
        Nat.dvd_ordCompl_of_dvd_not_dvd (lev_dvd_chiLevel hq) hnd
      have hval : (ZMod.unitsMap (lev_dvd_chiLevel hq) u : ZMod (lev q)) = 1 := by
        rw [ZMod.unitsMap_val, ← cast_cast_of_dvd (Nat.ordCompl_dvd _ _) hlevN', hu2,
          ← ZMod.castHom_apply (h := hlevN') (R := ZMod (lev q)), map_one]
      have hu : ZMod.unitsMap (lev_dvd_chiLevel hq) u = 1 := Units.ext hval
      rw [hu, map_one]
  have hprod : (chi Tm).toUnitHom =
      ∏ q ∈ Tm.attach,
        (DirichletCharacter.changeLevel (lev_dvd_chiLevel q.2) (oddChar q.1)).toUnitHom := by
    have := map_prod (MulChar.mulEquivToUnitHom (R := ZMod (chiLevel Tm)) (R' := ℂ))
      (fun q : Tm => DirichletCharacter.changeLevel (lev_dvd_chiLevel q.2) (oddChar q.1))
      Tm.attach
    exact this
  rw [hprod, MonoidHom.finsetProd_apply]
  rw [Finset.prod_congr rfl (fun q _ => factor q.1 q.2)]
  rw [Finset.prod_attach Tm (fun q => if q = p then (-1 : ℂˣ) else 1)]
  rw [Finset.prod_ite_eq']

/-- **B2 over `G_ℚ`, from the four leaves** (N5 L665-700). -/
theorem b2_of_leaves (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ),
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  classical
  let Tm := T.filter (fun p => ∃ hp : p.Prime, ¬ SignCob (pull (resp ⟨p, hp⟩) ε))
  have hloc : ∀ p : Nat.Primes, ¬ SignCob (pull (resp p) ε) ↔ (p : ℕ) ∈ Tm := by
    intro p
    constructor
    · intro h
      refine Finset.mem_filter.2 ⟨?_, p.2, h⟩
      by_contra hpT
      exact h (hUnr L ε hε hinf p (hram p hpT))
    · intro h
      obtain ⟨_, hp, h'⟩ := Finset.mem_filter.1 h
      exact h'
  have hTmP : ∀ q ∈ Tm, q.Prime := fun q hq => hT q (Finset.filter_subset _ _ hq)
  haveI hN : NeZero (chiLevel Tm) := ⟨(chiLevel_pos Tm hTmP).ne'⟩
  obtain ⟨_, hsupp, hord⟩ := exists_chi T Tm hT (Finset.filter_subset _ _)
  let χ := chi Tm
  let β₀ : GQ → ℂˣ := fun x => sqrtU (galChar χ x)
  have hβ₀ : ∀ x, β₀ x ^ 2 = galChar χ x := fun x => sqrtU_sq _
  have hl : IsLocallyConstant β₀ := (galChar_isLocallyConstant χ).comp sqrtU
  have agree : ∀ p : Nat.Primes,
      SignCob (pull (resp p) ε) ↔ SignCob (pull (resp p) (dB β₀)) := by
    intro p
    rw [pull_dB, signCob_dB_iff ((galChar χ).comp (resp p)) (β₀ ∘ resp p) (fun x => hβ₀ _)
      (hl.comp_continuous (resp_continuous p))]
    obtain ⟨u, hu1, hu2⟩ := exists_crt_unit (chiLevel Tm) p p.2
    have hsq := hSq p (chiLevel Tm) χ u hu1 hu2
    have hsq' : (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
        ∀ x, φ x ^ 2 = ((galChar χ).comp (resp p)) x) ↔ χ.toUnitHom u = 1 := hsq
    rw [hsq', chi_toUnitHom_crt Tm hTmP p p.2 u hu1 hu2]
    by_cases h : (p : ℕ) ∈ Tm
    · rw [if_pos h]
      have hne : (-1 : ℂˣ) ≠ 1 := by
        intro h1
        have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
        norm_num at this
      constructor
      · intro hc; exact absurd hc ((hloc p).mpr h)
      · intro h1; exact absurd h1 hne
    · rw [if_neg h]
      simp only [iff_true]
      by_contra hc
      exact h ((hloc p).mp hc)
  obtain ⟨β, hβl, hβs, hβe⟩ := exists_beta (G := GQ) GQp resp resp_continuous hHasse hTwo ε hε
    (galChar χ) β₀ hβ₀ hl agree
  exact ⟨chiLevel Tm, hN, χ, β, hsupp, hord, hβl, hβs, hβe⟩

end GlueDescent.B2Q

