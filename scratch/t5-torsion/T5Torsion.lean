import ZInQKernel.Contrib.TauCeti.GroupTheory.FiniteAbelian.RankTwo
import ZInQKernel.Contrib.TauCeti.Algebra.Module.Torsion.Decomposition
import ZInQKernel.Contrib.TauCeti.Algebra.Group.Equiv.Pi
import ZInQKernel.Contrib.TauCeti.Data.ZMod.Torsion
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Data.ZMod.Basic
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.HDecomp.LeafPush2.T

/-!
# t5-torsion: the textbook leaf T5 (`PkgI2.TorsionStructure`, Mumford §4) reduced

Parts 1-3 are concatenated from `GroupGlue.lean`, `Torus.lean`, `Descent.lean` of this directory
(scratch files cannot import each other); part 4 is the assembly. Main results:
* `T5Torsion.torsionStructure_of_torsionCard : TorsionCard.{u} → PkgI2.TorsionStructure.{u}`;
* `T5Torsion.torsionStructureC_of_uniformization : ZInQ.LeafPush2.UniformizationExists →
  TorsionStructureC` (T5 for every field with an embedding into `ℂ`, from T35 alone);
* `T5Torsion.torsionCard_of_uniformization` (the count for subfields of `ℂ`, from T35).
No `sorry`, no `axiom`.
-/

/-!
# t5-torsion, part 1: the group-theoretic glue (rank `r` structure from torsion counts)

Generalizes Tau Ceti's rank-two lemmas (vendored in `ZInQKernel/Contrib/TauCeti/`, Apache-2.0,
`GroupTheory/FiniteAbelian/RankTwo.lean` and
`AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Torsion/Structure.lean`) from rank `2` to rank
`r`; the proofs follow theirs.
-/

set_option linter.style.haveILetI false

namespace T5Torsion

open scoped DirectSum

/-- **Rank-`r` prime-power characterisation.** An abelian group killed by `p ^ k`, with
order `p ^ (r * k)` and `p ^ r` elements killed by `p`, is `(ZMod (p ^ k))^r`. -/
theorem nonempty_addEquiv_pi_zmod_primePow {G : Type*} [AddCommGroup G] {p k r : ℕ}
    (hp : p.Prime)
    (hpow : ∀ x : G, p ^ k • x = 0)
    (hcard : Nat.card G = p ^ (r * k))
    (hcardp : Nat.card (AddSubgroup.torsionBy G (p : ℤ)) = p ^ r) :
    Nonempty (G ≃+ (Fin r → ZMod (p ^ k))) := by
  classical
  have : Finite G := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ hp.ne_zero)
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let E : G ≃+ (∀ i : ι, ZMod (n i)) := e.trans (DirectSum.addEquivProd _)
  have hn_dvd (i : ι) : n i ∣ p ^ k := by
    let x : (j : ι) → ZMod (n j) := Function.update 0 i 1
    have hx : p ^ k • x = 0 := by
      simpa using congrArg E (hpow (E.symm x))
    have hxi := congrFun hx i
    have hxi' : ((p ^ k : ℕ) : ZMod (n i)) = 0 := by
      simpa [x, nsmul_eq_mul] using hxi
    exact (ZMod.natCast_eq_zero_iff (p ^ k) (n i)).mp hxi'
  choose a ha_le ha using fun i ↦ (Nat.dvd_prime_pow hp).mp (hn_dvd i)
  have ha_pos (i : ι) : 0 < a i := by
    rw [Nat.pos_iff_ne_zero]
    intro hai
    simpa [ha i, hai] using hn i
  have hcard_prod : ∏ i, n i = p ^ (r * k) := by
    rw [← hcard, Nat.card_congr E.toEquiv, Nat.card_pi]
    simp only [Nat.card_zmod]
  have hcard_torsion_pi :
      Nat.card (AddSubgroup.torsionBy (∀ i : ι, ZMod (n i)) (p : ℤ)) = p ^ Fintype.card ι := by
    rw [Nat.card_congr (TauCeti.AddSubgroup.torsionByPiEquiv (fun i ↦ ZMod (n i)) (p : ℤ)).toEquiv,
      Nat.card_pi]
    let : NeZero p := ⟨hp.ne_zero⟩
    calc
      ∏ i, Nat.card (AddSubgroup.torsionBy (ZMod (n i)) (p : ℤ)) = ∏ _i : ι, p := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [ha i]
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ha_pos i).ne'
        rw [hj]
        simpa only [Nat.card_zmod] using
          Nat.card_congr (TauCeti.zmodTorsionByEquiv p j).symm.toEquiv
      _ = p ^ Fintype.card ι := by simp
  have hιcard : Fintype.card ι = r := by
    have ht : p ^ Fintype.card ι = p ^ r := by
      rw [← hcard_torsion_pi, ← hcardp]
      exact Nat.card_congr (AddEquiv.torsionByCongr E (p : ℤ)).symm.toEquiv
    exact Nat.pow_right_injective hp.two_le ht
  have hsum : ∑ i, a i = r * k := by
    apply Nat.pow_right_injective hp.two_le
    dsimp only
    rw [← Finset.prod_pow_eq_pow_sum Finset.univ a p]
    simp only [← ha, hcard_prod]
  have ha_eq (i : ι) : a i = k := by
    apply le_antisymm (ha_le i)
    by_contra hki
    have hai : a i < k := Nat.lt_of_not_ge hki
    have hlt : ∑ j, a j < ∑ _j : ι, k :=
      Finset.sum_lt_sum (fun j _ ↦ ha_le j) ⟨i, Finset.mem_univ i, hai⟩
    simp only [Finset.sum_const, Finset.card_univ, hιcard, smul_eq_mul] at hlt
    omega
  let rι : ι ≃ Fin r := Fintype.equivFinOfCardEq hιcard
  exact ⟨E |>.trans (AddEquiv.piCongrRight fun i ↦
      (ZMod.ringEquivCongr (by rw [ha i, ha_eq i])).toAddEquiv) |>.trans
      (AddEquiv.arrowCongr rι (AddEquiv.refl (ZMod (p ^ k))))⟩

open scoped Classical in
/-- A primary component of `A[N]` is `(ZMod q)^r`, given the counts `#A[m] = m^r` for `m ∣ N`. -/
noncomputable def primePowerComponentEquiv {A : Type*} [AddCommGroup A] (N r : ℕ) [NeZero N]
    (hcount : ∀ m : ℕ, m ∣ N → Nat.card (AddSubgroup.torsionBy A (m : ℤ)) = m ^ r)
    (p : N.primeFactors) :
    let q := (p : ℕ) ^ N.factorization p
    Submodule.torsionBy ℤ (AddSubgroup.torsionBy A (N : ℤ)) (q : ℤ) ≃+
      (Fin r → ZMod q) := by
  let G := AddSubgroup.torsionBy A (N : ℤ)
  let q := (p : ℕ) ^ N.factorization p
  have hN0 : N ≠ 0 := NeZero.ne N
  have hq_dvd : q ∣ N :=
    (Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hN0 |>.2 le_rfl
  have hp_dvd_q : (p : ℕ) ∣ q := by
    apply dvd_pow_self
    exact (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors p.2) hN0
      (Nat.dvd_of_mem_primeFactors p.2)).ne'
  let e : Submodule.torsionBy ℤ G (q : ℤ) ≃+
      AddSubgroup.torsionBy A (q : ℤ) :=
        TauCeti.AddSubgroup.torsionByTorsionByEquiv (by exact_mod_cast hq_dvd)
  have hpow (x : Submodule.torsionBy ℤ G (q : ℤ)) : q • x = 0 :=
    AddSubgroup.torsionBy.nsmul x
  have hcardq : Nat.card (Submodule.torsionBy ℤ G (q : ℤ)) = q ^ r := by
    rw [Nat.card_congr e.toEquiv]
    exact hcount q hq_dvd
  have hcardp : Nat.card
      (AddSubgroup.torsionBy (Submodule.torsionBy ℤ G (q : ℤ)) (p : ℤ)) = p ^ r := by
    let ep := (AddEquiv.torsionByCongr e p).trans
      (TauCeti.AddSubgroup.torsionByTorsionByEquiv (by exact_mod_cast hp_dvd_q))
    rw [Nat.card_congr ep.toEquiv]
    exact hcount p (dvd_trans hp_dvd_q hq_dvd)
  have hcardq' : Nat.card (Submodule.torsionBy ℤ G (q : ℤ)) =
      p ^ (r * N.factorization p) := by
    rw [hcardq]
    dsimp only [q]
    rw [← pow_mul, mul_comm]
  exact (nonempty_addEquiv_pi_zmod_primePow
    (Nat.prime_of_mem_primeFactors p.2) hpow hcardq' hcardp).some

/-- **Structure from counts.** If `#A[m] = m^r` for every `m ∣ N` (`N ≥ 1`), then
`A[N] ≃+ (ZMod N)^r`. -/
theorem nonempty_torsionBy_addEquiv_pi {A : Type*} [AddCommGroup A] (N r : ℕ) (hN0 : N ≠ 0)
    (hcount : ∀ m : ℕ, m ∣ N → Nat.card (AddSubgroup.torsionBy A (m : ℤ)) = m ^ r) :
    Nonempty (AddSubgroup.torsionBy A (N : ℤ) ≃+ (Fin r → ZMod N)) := by
  classical
  haveI : NeZero N := ⟨hN0⟩
  let G := AddSubgroup.torsionBy A (N : ℤ)
  let q : ℕ → ℕ := fun p ↦ p ^ N.factorization p
  let componentEquiv (p : N.primeFactors) :
      Submodule.torsionBy ℤ G (q p : ℤ) ≃+ (Fin r → ZMod (q p)) :=
    primePowerComponentEquiv N r hcount p
  have hinternal : DirectSum.IsInternal fun p : N.primeFactors ↦
      Submodule.torsionBy ℤ G (q p : ℤ) :=
    TauCeti.AddSubgroup.torsionBy_primeFactors_isInternal N hN0
  letI := hinternal.chooseDecomposition
  let primary : G ≃+ (∀ p : N.primeFactors, Fin r → ZMod (q p)) :=
    (DirectSum.decomposeAddEquiv fun p : N.primeFactors ↦
      Submodule.torsionBy ℤ G (q p : ℤ)).trans <|
      (DFinsupp.mapRange.addEquiv componentEquiv).trans (DirectSum.addEquivProd _)
  let comm : (∀ p : N.primeFactors, Fin r → ZMod (q p)) ≃+
      (Fin r → ∀ p : N.primeFactors, ZMod (q p)) :=
    { Equiv.piComm _ with map_add' := fun _ _ ↦ rfl }
  let crt : (∀ p : N.primeFactors, ZMod (q p)) ≃+ ZMod N :=
    (ZMod.equivPi (n := N) hN0).symm.toAddEquiv
  exact ⟨primary.trans (comm.trans (AddEquiv.piCongrRight fun _ ↦ crt))⟩

end T5Torsion



/-!
# t5-torsion, part 2: `n`-torsion of a group uniformized by `E / Λ`

If `Φ : E → P` is a surjective homomorphism (written multiplicatively on `P`) with kernel a full
lattice `Λ` of the real space `E`, then `P` has exactly `n ^ dim_ℝ E` elements `x` with `xⁿ = 1`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace T5Torsion

open Module

section Torus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {P : Type*} [Group P] (Φ : E → P)

theorem map_nsmul_of_add (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (n : ℕ) (z : E) :
    Φ (n • z) = Φ z ^ n := by
  have h0 : Φ 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem eq_iff_sub_mem (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (z w : E) : Φ z = Φ w ↔ z - w ∈ Λ := by
  rw [← hker]
  have h := hadd (z - w) w
  rw [sub_add_cancel] at h
  constructor
  · intro hzw
    rw [hzw] at h
    exact (mul_eq_right.mp h.symm)
  · intro h1
    rw [h, h1, one_mul]

/-- Membership in `Λ` through the coordinates in a `ℤ`-basis of `Λ`. -/
theorem mem_iff_repr {ι : Type*} (b : Basis ι ℤ Λ) (z : E) :
    z ∈ Λ ↔ ∀ i, (b.ofZLatticeBasis ℝ Λ).repr z i ∈ Set.range (algebraMap ℤ ℝ) := by
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ]
  exact (b.ofZLatticeBasis ℝ Λ).mem_span_iff_repr_mem ℤ z

/-- **Torsion of a uniformized group.** -/
theorem natCard_pow_eq_one (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w)
    (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ) (hsurj : Function.Surjective Φ) (n : ℕ) (hn : 0 < n) :
    Nat.card {x : P // x ^ n = 1} = n ^ finrank ℝ E := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let ι := Module.Free.ChooseBasisIndex ℤ Λ
  let B := b.ofZLatticeBasis ℝ Λ
  have hBi (i : ι) : B i ∈ Λ := by
    rw [show B i = b i from b.ofZLatticeBasis_apply ℝ Λ i]
    exact (b i).2
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let zc : (ι → ZMod n) → E := fun c => ∑ i, (((c i).val : ℝ) / n) • B i
  have hrepr (c : ι → ZMod n) (i : ι) : B.repr (zc c) i = ((c i).val : ℝ) / n := by
    simp [zc, Finsupp.single_apply]
  let f : (ι → ZMod n) → {x : P // x ^ n = 1} := fun c => ⟨Φ (zc c), by
    rw [← map_nsmul_of_add Φ hadd, hker, mem_iff_repr Λ b]
    intro i
    refine ⟨((c i).val : ℤ), ?_⟩
    rw [map_nsmul, Finsupp.smul_apply, hrepr, nsmul_eq_mul]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    field_simp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      have h1 : Φ (zc c) = Φ (zc c') := congrArg Subtype.val h
      rw [eq_iff_sub_mem Λ Φ hadd hker, mem_iff_repr Λ b] at h1
      funext i
      obtain ⟨m, hm⟩ := h1 i
      rw [map_sub, Finsupp.sub_apply, hrepr, hrepr] at hm
      simp only [algebraMap_int_eq, eq_intCast] at hm
      have hlt := ZMod.val_lt (c i)
      have hlt' := ZMod.val_lt (c' i)
      have hm' : (m : ℝ) * n = (c i).val - (c' i).val := by
        rw [hm]; field_simp
      have hmZ : m * (n : ℤ) = ((c i).val : ℤ) - (c' i).val := by exact_mod_cast hm'
      have hm0 : m = 0 := by
        rcases lt_trichotomy m 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      rw [hm0, zero_mul] at hmZ
      exact ZMod.val_injective n (by omega)
    · rintro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := hsurj x
      have h1 : Φ (n • z) = 1 := by rw [map_nsmul_of_add Φ hadd, hx]
      rw [hker, mem_iff_repr Λ b] at h1
      choose m hm using h1
      refine ⟨fun i => (m i : ZMod n), Subtype.ext ?_⟩
      change Φ (zc _) = Φ z
      rw [eq_iff_sub_mem Λ Φ hadd hker, mem_iff_repr Λ b]
      intro i
      refine ⟨-(m i / n), ?_⟩
      have hmi := hm i
      rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at hmi
      simp only [algebraMap_int_eq, eq_intCast] at hmi ⊢
      rw [map_sub, Finsupp.sub_apply, hrepr]
      have hv : (((m i : ZMod n)).val : ℤ) = m i % n := ZMod.val_intCast (m i)
      have hv' : ((((m i : ZMod n)).val : ℕ) : ℝ) = ((m i % n : ℤ) : ℝ) := by exact_mod_cast hv
      rw [hv']
      have hdiv : ((m i % n : ℤ) : ℝ) = (m i : ℝ) - n * ((m i / n : ℤ) : ℝ) := by
        have := Int.emod_def (m i) n
        rw [this]; push_cast; ring
      rw [hdiv, hmi]
      field_simp
      push_cast
      ring
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis B]

end Torus

theorem finrank_real_fin_complex (g : ℕ) : finrank ℝ (Fin g → ℂ) = 2 * g := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

end T5Torsion



/-!
# t5-torsion, part 3: torsion points along `K̄ → Ω₂` (characteristic 0)
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace T5Torsion

open ZInQ.Contrib.AbVarBC

section Desc

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- **Lifting `N`-torsion points along `κ : Ω → Ω₂`** when `[N]` is finite (adapted from
`ZInQ.Contrib.AbVarBC.torsionDescends_of_isFinite`). -/
theorem exists_extPt_eq (κ : Ω →ₐ[K] Ω₂) (N : ℕ)
    (hfin : IsFinite ((((N : ℤ)) : PkgI3.AbVar.End A).hom.left))
    (q : A.Pt Ω₂) (hq : q ^ N = 1) : ∃ p : A.Pt Ω, extPt A κ p = q := by
  have h1 : q ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom = 1 := by rw [comp_natCast_hom, hq]
  let fN : A.X.left ⟶ A.X.left := ((N : ℤ) : PkgI3.AbVar.End A).hom.left
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have hq0 : q.left ≫ fN = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂)) ≫ e := by
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  have hfN : IsFinite fN := hfin
  let z : Spec (CommRingCat.of Ω₂) ⟶ pullback fN e :=
    pullback.lift q.left (Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) hq0
  obtain ⟨p0, hp0, hp0g⟩ :=
    exists_lift_of_isFinite κ (pullback.snd fN e) z (pullback.lift_snd _ _ _)
  have hfst : pullback.fst fN e ≫ A.X.hom = pullback.snd fN e := by
    have hw : fN ≫ A.X.hom = A.X.hom := Over.w ((N : ℤ) : PkgI3.AbVar.End A).hom
    have he : e ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
    rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  let p : A.Pt Ω := Over.homMk (p0 ≫ pullback.fst fN e) (by
    change (p0 ≫ pullback.fst fN e) ≫ A.X.hom = _
    rw [Category.assoc, hfst, hp0g]
    rfl)
  refine ⟨p, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ p0 ≫ pullback.fst fN e = q.left
  rw [← Category.assoc, hp0]
  exact pullback.lift_fst _ _ _

/-- **`#A(Ω)[n] = #A(Ω₂)[n]`** in characteristic `0`, for `Ω` algebraically closed. -/
theorem natCard_torsion_eq_of_ext [CharZero K] (κ : Ω →ₐ[K] Ω₂) (n : ℕ) (hn : 0 < n) :
    Nat.card {p : A.Pt Ω // p ^ n = 1} = Nat.card {q : A.Pt Ω₂ // q ^ n = 1} := by
  have hfin : IsFinite ((((n : ℤ)) : PkgI3.AbVar.End A).hom.left) :=
    (mulIsogeny K A (n : ℤ) (by exact_mod_cast hn.ne')).1
  let f : {p : A.Pt Ω // p ^ n = 1} → {q : A.Pt Ω₂ // q ^ n = 1} := fun p =>
    ⟨extPt A κ p.1, by rw [← map_pow, p.2, map_one]⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p p' h => Subtype.ext (extPt_injective A κ (congrArg Subtype.val h)), ?_⟩
    rintro ⟨q, hq⟩
    obtain ⟨p, hp⟩ := exists_extPt_eq A κ n hfin q hq
    refine ⟨⟨p, extPt_injective A κ ?_⟩, Subtype.ext hp⟩
    rw [map_pow, hp, hq, map_one]
  exact Nat.card_congr (Equiv.ofBijective f hf)

end Desc

end T5Torsion


/-! ## Part 4: assembly over the kernel's objects -/

namespace T5Torsion

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety torsion Pts)

universe u

/-- **Leaf candidate T5-card (number of `n`-torsion points).** For an abelian variety `A` of
dimension `g` over a field `K` and `n ≥ 1` invertible in `K`, `A(K̄)` has exactly `n^{2g}`
points killed by `n`. Mumford, *Abelian varieties* (1970), §4, after the theorem of the cube:
`deg [n] = n^{2g}` and `[n]` separable when `char K ∤ n`, whence `#A[n] = n^{2g}` (locators
UNVERIFIED: the degree is §6 Application 2 in the 2nd edition, the corollary `X_n ≅ (ℤ/n)^{2g}`
follows it). A consequence of the published statement `X_n ≅ (ℤ/n)^{2g}` (take cardinalities). -/
def TorsionCard : Prop :=
  ∀ (K : Type u) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (g n : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : K) ≠ 0 →
      Nat.card (torsion A (AlgebraicClosure K) n) = n ^ (2 * g)

section Glue

variable {K : Type u} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
  (L : Type u) [CommRing L] [Algebra K L]

instance isCommMonObjU : IsCommMonObj A.X :=
  haveI := PkgI2.IsAbelianVariety.proper (A := A)
  haveI := PkgI2.IsAbelianVariety.geomIntegral (A := A)
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The points as an additive commutative group. -/
noncomputable instance ptsAddCommGroup : AddCommGroup (Additive (Pts A L)) :=
  @Additive.addCommGroup _ (Hom.commGroup (G := A.X))

/-- `torsion A L m` is the `m`-torsion subgroup of `Additive (A(L))`. -/
def torsionEquiv (m : ℕ) :
    torsion A L m ≃ AddSubgroup.torsionBy (Additive (Pts A L)) (m : ℤ) where
  toFun x := ⟨Additive.ofMul x.1, by
    refine (Submodule.mem_torsionBy_iff _ _).2 ?_
    rw [natCast_zsmul]
    exact congrArg Additive.ofMul x.2⟩
  invFun y := ⟨Additive.toMul y.1, by
    have h := (Submodule.mem_torsionBy_iff _ _).1 y.2
    rw [natCast_zsmul] at h
    exact congrArg Additive.toMul h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The structure of `A[n]` from the counts `#A[m] = m^{2g}`, `m ∣ n`** (pure algebra). -/
theorem exists_torsion_equiv_of_counts (g n : ℕ) (hn : 0 < n)
    (hc : ∀ m : ℕ, m ∣ n → Nat.card (torsion A L m) = m ^ (2 * g)) :
    ∃ e : torsion A L n ≃ (Fin (2 * g) → ZMod n),
      ∀ x y : torsion A L n, ∀ h : x.1 * y.1 ∈ torsion A L n, e ⟨x.1 * y.1, h⟩ = e x + e y := by
  obtain ⟨E⟩ := nonempty_torsionBy_addEquiv_pi (A := Additive (Pts A L)) n (2 * g) hn.ne'
    (fun m hm => by rw [← Nat.card_congr (torsionEquiv A L m)]; exact hc m hm)
  refine ⟨(torsionEquiv A L n).trans E.toEquiv, fun x y h => ?_⟩
  change E (torsionEquiv A L n ⟨x.1 * y.1, h⟩) = E (torsionEquiv A L n x) + E (torsionEquiv A L n y)
  rw [← map_add]
  rfl

end Glue

/-- **T5 from the count `TorsionCard`** (glue, proved). -/
theorem torsionStructure_of_torsionCard (h : TorsionCard.{u}) : PkgI2.TorsionStructure.{u} := by
  intro K _ A _ g n hg hn hnK
  refine exists_torsion_equiv_of_counts A (AlgebraicClosure K) g n hn (fun m hm => ?_)
  obtain ⟨k, rfl⟩ := hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hn
  refine h K A g m hg hm0 ?_
  push_cast at hnK
  exact left_ne_zero_of_mul hnK

/-- **T5 restricted to subfields of `ℂ`**: `PkgI2.TorsionStructure` for fields `K` with a ring
embedding `σ : K → ℂ` (so characteristic `0`). -/
def TorsionStructureC : Prop :=
  ∀ (K : Type) [Field K] (_ : K →+* ℂ) (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (g n : ℕ), topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n →
      ∃ e : torsion A (AlgebraicClosure K) n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A (AlgebraicClosure K) n,
          ∀ h : x.1 * y.1 ∈ torsion A (AlgebraicClosure K) n, e ⟨x.1 * y.1, h⟩ = e x + e y

/-- **`#A(K̄)[n] = n^{2g}` for `K ⊆ ℂ`, from the textbook leaf T35** (`UniformizationExists`,
already `TextbookLeaves.t35`) and Mathlib (`MulIsogeny` is proved in `Contrib/AbVarBC`). -/
theorem natCard_torsion_of_uniformization (hU : ZInQ.LeafPush2.UniformizationExists)
    {K : Type} [Field K] (σ : K →+* ℂ) (A : PkgI3.AbVar K) (g n : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) (hn : 0 < n) :
    Nat.card {p : A.Pt (AlgebraicClosure K) // p ^ n = 1} = n ^ (2 * g) := by
  haveI : CharZero K := RingHom.charZero σ
  letI : Algebra K ℂ := σ.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  rw [natCard_torsion_eq_of_ext A κ n hn]
  obtain ⟨Λ, Φ, hdisc, hlat, hadd, hker, hsurj, -, -⟩ := hU K A σ g hg
  have h := natCard_pow_eq_one Λ Φ hadd hker hsurj n hn
  rw [finrank_real_fin_complex] at h
  exact h

/-- **T5 for subfields of `ℂ` from T35** (no other leaf). -/
theorem torsionStructureC_of_uniformization (hU : ZInQ.LeafPush2.UniformizationExists) :
    TorsionStructureC := by
  intro K _ σ A _ g n hg hn
  refine exists_torsion_equiv_of_counts A (AlgebraicClosure K) g n hn (fun m hm => ?_)
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hn
  exact natCard_torsion_of_uniformization hU σ (ObjBridge.ofGrp A) g m hg hm0

/-- **`TorsionCard` for subfields of `ℂ` from T35.** -/
theorem torsionCard_of_uniformization (hU : ZInQ.LeafPush2.UniformizationExists)
    {K : Type} [Field K] (σ : K →+* ℂ) (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (g n : ℕ) (hg : topologicalKrullDim A.X.left = (g : WithBot ℕ∞)) (hn : 0 < n) :
    Nat.card (torsion A (AlgebraicClosure K) n) = n ^ (2 * g) :=
  natCard_torsion_of_uniformization hU σ (ObjBridge.ofGrp A) g n hg hn

end T5Torsion

#print axioms T5Torsion.torsionStructure_of_torsionCard
#print axioms T5Torsion.torsionStructureC_of_uniformization
#print axioms T5Torsion.torsionCard_of_uniformization
