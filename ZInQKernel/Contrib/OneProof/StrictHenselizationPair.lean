import ZInQKernel.Contrib.OneProof.H.TailZ14
import Mathlib

/-!
# `ReductGlue.StrictHenselizationPair` from one Néron leaf (task gt-shpair)

The hypothesis `ReductGlue.StrictHenselizationPair` (`ZInQKernel/Contrib/OneProof/H/TailZ14.lean`, a GLUE
field rated composite) combines (i) strict henselization along a finite extension of DVRs with
(ii) Néron models commuting with strict henselization. This file proves (i) in Lean from Mathlib,
for every field (any characteristic) and every residue field (perfect or not), and isolates (ii) as
the single printed-form leaf `GapSHPair.NeronBaseChangeStrictHenselization` (BLR, *Néron models*,
§1.2 Prop. 2; a specialization of the chain's `ReductGlue.NeronBaseChangeUnramifiedDVR`).

Main results:
* `GapSHPair.strictHenselizationPair_of_neron :
    NeronBaseChangeStrictHenselization → ReductGlue.StrictHenselizationPair`;
* `GapSHPair.strictHenselizationPair_of_unramified :
    ReductGlue.NeronBaseChangeUnramifiedDVR → ReductGlue.StrictHenselizationPair`;
* `GapSHPair.shPair` (the commutative algebra, no hypotheses).

Construction: for `w` a valuation ring of `Ω = K̄'` over `O'`, the inertia field of `w` over `K`
(the union of the inertia fields of the finite Galois subextensions) and over `K'`. The finite
level (`key_finite`) uses Mathlib's fundamental identity and `Stab/Inertia ≃ Aut(κ(P)/κ(p))` with a
separable-degree count in place of `card_inertia_eq_ramificationIdxIn` (which needs separable
residue fields); the nesting `E_{K'} ⊆ E_K(K')` in characteristic `p` uses a `p`-power argument.
Adapted from task sh-route's characteristic-0 proof (`scratch/sh-route/CA*.lean`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


-- ===== part GTCA1 =====

open IsLocalRing Polynomial
open scoped Pointwise

set_option linter.style.haveILetI false

namespace GapSHPair


section Count

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

attribute [local instance] Ideal.Quotient.field in
/-- `|D_P| = |I_P| · |Aut(κ(P)/κ(p))|` with no separability hypothesis. -/
theorem card_stabilizer_eq_card_inertia_mul_card_gal (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (P.inertia G) * Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) := by
  have : Subgroup.index _ = _ := Nat.card_congr
    (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [← this, ← ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

theorem card_stabilizer_eq_ram_mul_inertiaDeg [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  have h2 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  rw [Nat.card_prod, Nat.card_coe_set_eq, Algebra.IsInvariant.orbit_eq_primesOver R S G p P] at h2
  have h0 : (p.primesOver S).ncard ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact (Nat.card_pos (α := G)).ne' h1.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) (h2.trans h1.symm)


attribute [local instance] Ideal.Quotient.field in
/-- `|I_P| · |Aut(κ(P)/κ(p))| = e · f` with no separability hypothesis. -/
theorem card_inertia_mul_card_gal [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsMaximal] [P.LiesOver p] :
    Nat.card (P.inertia G) * Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) =
      p.ramificationIdxIn S * p.inertiaDegIn S := by
  rw [← card_stabilizer_eq_card_inertia_mul_card_gal p P, card_stabilizer_eq_ram_mul_inertiaDeg p P]

end Count

/-- For a normal extension, the number of automorphisms is the separable degree. -/
theorem card_aut_eq_finSepDegree (F E : Type*) [Field F] [Field E] [Algebra F E] [Normal F E] :
    Nat.card (E ≃ₐ[F] E) = Field.finSepDegree F E :=
  (Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure E) E)).symm

/-- **Separable-degree count.** `F ⊆ E ⊆ L`, `L/F` finite and normal, `L/E` normal. If
`e · [E : F] · |Aut(L/E)| = |Aut(L/F)|` then `e = 1` and `E/F` is separable. -/
theorem eq_one_and_isSeparable_of_card {F E L : Type*} [Field F] [Field E] [Field L] [Algebra F E]
    [Algebra E L] [Algebra F L] [IsScalarTower F E L] [FiniteDimensional F L] [Normal F L]
    [Normal E L] (e : ℕ)
    (h : e * Module.finrank F E * Nat.card (L ≃ₐ[E] L) = Nat.card (L ≃ₐ[F] L)) :
    e = 1 ∧ Algebra.IsSeparable F E := by
  haveI : FiniteDimensional F E := FiniteDimensional.left F E L
  haveI : FiniteDimensional E L := FiniteDimensional.right F E L
  rw [card_aut_eq_finSepDegree, card_aut_eq_finSepDegree,
    ← Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F E L] at h
  have hs2 : 0 < Field.finSepDegree E L := Nat.pos_of_ne_zero (NeZero.ne _)
  have h' : e * Module.finrank F E = Field.finSepDegree F E := Nat.eq_of_mul_eq_mul_right hs2 h
  have hle := Field.finSepDegree_le_finrank F E
  have hpos : 0 < Module.finrank F E := Module.finrank_pos
  have hspos : 0 < Field.finSepDegree F E := Nat.pos_of_ne_zero (NeZero.ne _)
  have he : e = 1 := by
    rcases Nat.lt_or_ge e 1 with he | he
    · interval_cases e; omega
    · by_contra hne
      have : 2 * Module.finrank F E ≤ e * Module.finrank F E := Nat.mul_le_mul_right _ (by omega)
      omega
  refine ⟨he, ?_⟩
  rw [he, one_mul] at h'
  exact (Field.finSepDegree_eq_finrank_iff F E).mp h'.symm

attribute [local instance] Ideal.Quotient.field in
/-- **The inertia ring is unramified with separable residue extension** (no separability
hypothesis on residue fields). `A ⊆ R ⊆ S`, `S/A` Galois with group `G`, `S/R` Galois with group the
inertia group `H` of a maximal `P ⊆ S` over `p`. Then `𝔮 = P ∩ R` has ramification index `1` over
`p` and `R/𝔮` is separable over `A/p`. -/
theorem inertia_unram {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [IsDomain A]
    [IsDomain R] [IsDomain S] [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G A S]
    [Module.Finite A S] [Module.Finite R S] [Module.Flat A S] [Module.Flat R S]
    (p : Ideal A) [p.IsMaximal] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [IsGaloisGroup (P.inertia G) R S] [(P.under R).IsMaximal] [(P.under R).LiesOver p] :
    (P.under R).ramificationIdx A = 1 ∧ Algebra.IsSeparable (A ⧸ p) (R ⧸ P.under R) := by
  set 𝔮 := P.under R
  set H := P.inertia G
  haveI : IsScalarTower (A ⧸ p) (R ⧸ 𝔮) (S ⧸ P) := IsScalarTower.of_algebraMap_eq (fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [← IsScalarTower.algebraMap_apply])
  have hc1 := card_inertia_mul_card_gal (G := G) p P
  have hc3 := card_inertia_mul_card_gal (G := H) 𝔮 P
  have e4 : Nat.card (P.inertia H) = Nat.card H :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (fun h => fun s => h.2 s))
  rw [e4] at hc3
  have hHpos : 0 < Nat.card H := Nat.card_pos
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G, Ideal.inertiaDegIn_eq_inertiaDeg p P G,
    Ideal.ramificationIdx_tower (R := A) 𝔮 P, Ideal.inertiaDeg_tower (R := A) 𝔮 P] at hc1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮 P H, Ideal.inertiaDegIn_eq_inertiaDeg 𝔮 P H]
    at hc3
  haveI : Normal (A ⧸ p) (S ⧸ P) := Ideal.Quotient.normal G p P
  haveI : Normal (R ⧸ 𝔮) (S ⧸ P) := Ideal.Quotient.normal H 𝔮 P
  haveI : FiniteDimensional (A ⧸ p) (S ⧸ P) := inferInstance
  refine eq_one_and_isSeparable_of_card (L := S ⧸ P) _ ?_
  rw [← Ideal.inertiaDeg_eq_of_isMaximal p 𝔮]
  have h5 : Nat.card H * Nat.card ((S ⧸ P) ≃ₐ[A ⧸ p] (S ⧸ P)) =
      Nat.card H * (𝔮.ramificationIdx A * 𝔮.inertiaDeg A *
        Nat.card ((S ⧸ P) ≃ₐ[R ⧸ 𝔮] (S ⧸ P))) := by
    rw [hc1]
    calc _ = 𝔮.ramificationIdx A * 𝔮.inertiaDeg A * (P.ramificationIdx R * P.inertiaDeg R) := by ring
      _ = _ := by rw [← hc3]; ring
  exact (Nat.eq_of_mul_eq_mul_left hHpos h5).symm



attribute [local instance] Ideal.Quotient.field in
/-- **A separable residue polynomial.** `φ : R → M` lands in a valuation ring `W` with
`φ⁻¹(𝔪_W) = 𝔮`; if `R/𝔮` is separable over `A/p` then every `x = φ(a)/φ(s)` with `s ∉ 𝔮` is a
root modulo `𝔪_W` of a polynomial over `A` whose reduction is separable. -/
theorem exists_sep_poly {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R] [Field M]
    (φ : R →+* M) (p : Ideal A) [p.IsMaximal] (𝔮 : Ideal R) [𝔮.IsMaximal] [𝔮.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (R ⧸ 𝔮)] (W : ValuationSubring M)
    (h𝔮 : ∀ r, r ∈ 𝔮 ↔ φ r ∈ W.nonunits) (hφW : ∀ r, φ r ∈ W) (x : M) (a s : R) (hs : s ∉ 𝔮)
    (hxs : x * φ s = φ a) :
    ∃ f : A[X], (f.map (Ideal.Quotient.mk p)).Separable ∧
      (f.map (φ.comp (algebraMap A R))).eval x ∈ W.nonunits := by
  set y : R ⧸ 𝔮 := Ideal.Quotient.mk 𝔮 a * (Ideal.Quotient.mk 𝔮 s)⁻¹
  have hsy : Ideal.Quotient.mk 𝔮 s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hint : IsIntegral (A ⧸ p) y := Algebra.IsIntegral.isIntegral y
  set g := minpoly (A ⧸ p) y
  have hg : g.Separable := Algebra.IsSeparable.isSeparable (A ⧸ p) y
  obtain ⟨f, hfg, -, hfm⟩ := lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective g)
    (minpoly.monic hint)
  refine ⟨f, by rw [hfg]; exact hg, ?_⟩
  set fR := f.map (algebraMap A R)
  have hfR : fR.Monic := hfm.map _
  set F := (scaleRoots fR s).eval a
  -- `F ∈ 𝔮`
  have hF : F ∈ 𝔮 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e1 : Ideal.Quotient.mk 𝔮 F =
        (scaleRoots (fR.map (Ideal.Quotient.mk 𝔮)) (Ideal.Quotient.mk 𝔮 s)).eval
          (Ideal.Quotient.mk 𝔮 a) := by
      rw [← map_scaleRoots _ _ _ (by rw [hfR.leadingCoeff, map_one]; exact one_ne_zero),
        Polynomial.eval_map, ← Polynomial.eval₂_hom]
    have e2 : fR.map (Ideal.Quotient.mk 𝔮) = g.map (algebraMap (A ⧸ p) (R ⧸ 𝔮)) := by
      rw [← hfg, Polynomial.map_map, Polynomial.map_map]
      congr 1
    have e3 : Ideal.Quotient.mk 𝔮 a = Ideal.Quotient.mk 𝔮 s * y := by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hsy, mul_one]
    rw [e1, e2, e3, scaleRoots_eval_mul, Polynomial.eval_map, ← Polynomial.aeval_def,
      minpoly.aeval, mul_zero]
  -- transport to `M`
  have e4 : φ F = φ s ^ fR.natDegree * (f.map (φ.comp (algebraMap A R))).eval x := by
    have : φ F = eval₂ φ (φ s * x) (scaleRoots fR s) := by
      rw [mul_comm, hxs, ← Polynomial.eval₂_hom]
    rw [this, scaleRoots_eval₂_mul, ← Polynomial.map_map, Polynomial.eval_map]
  have hφF := (h𝔮 F).mp hF
  have hsu : φ s ∉ W.nonunits := fun h => hs ((h𝔮 s).mpr h)
  rw [ValuationSubring.mem_nonunits_iff] at hφF hsu ⊢
  have hv1 : W.valuation (φ s) = 1 :=
    le_antisymm ((W.valuation_le_one_iff _).mpr (hφW s)) (not_lt.mp hsu)
  rw [e4, map_mul, map_pow, hv1, one_pow, one_mul] at hφF
  exact hφF



/-! ## A. Valuation rings over a Dedekind domain are localizations -/

section Loc

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- `R → W` for a valuation subring `W` of `Frac R` containing `R`. -/
def toW (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) : R →+* W :=
  (algebraMap R F).codRestrict W.toSubring hW

/-- The center `R ∩ 𝔪_W`. -/
def ctr (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) : Ideal R :=
  (maximalIdeal W).comap (toW W hW)

theorem mem_ctr_iff (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) (r : R) :
    r ∈ ctr W hW ↔ algebraMap R F r ∈ W.nonunits := by
  change toW W hW r ∈ maximalIdeal W ↔ _
  rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]
  rfl

instance ctr_isPrime (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) :
    (ctr W hW).IsPrime := Ideal.comap_isPrime _ _

theorem isUnit_toW (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) {s : R}
    (hs : s ∉ ctr W hW) : IsUnit (toW W hW s) := by
  by_contra h
  exact hs ((mem_maximalIdeal _).mpr h)

theorem mem_of_mul_eq' (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) {x : F}
    {a s : R} (hs : s ∉ ctr W hW) (h : x * algebraMap R F s = algebraMap R F a) : x ∈ W := by
  obtain ⟨u, hu⟩ := isUnit_toW W hW hs
  have h1 : ((u : W) : F) = algebraMap R F s := by rw [hu]; rfl
  have h2 : (((u⁻¹ : Wˣ) : W) : F) * ((u : W) : F) = 1 :=
    congrArg (fun z : W => (z : F)) (Units.inv_mul u)
  have : x = algebraMap R F a * (((u⁻¹ : Wˣ) : W) : F) := by
    rw [← h, h1.symm, _root_.mul_assoc, mul_comm ((u : W) : F), h2, _root_.mul_one]
  rw [this]
  exact mul_mem (hW a) (u⁻¹ : Wˣ).1.2

/-- **A valuation subring `W ⊇ R` of `Frac R` with nonzero center is the localization of `R` at
its center**: every `x ∈ W` is `a/s` with `a, s ∈ R`, `s ∉ 𝔭`. (Generalizes reduct-glue's
`mem_iff_exists` from `𝓞_L` to any Dedekind domain; same proof.) -/
theorem exists_of_mem (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W)
    (h0 : ctr W hW ≠ ⊥) {x : F} (hx : x ∈ W) :
    ∃ a s : R, s ∉ ctr W hW ∧ x * algebraMap R F s = algebraMap R F a := by
  let 𝔭 := ctr W hW
  let B := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 B
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (algebraMap R F b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.ne_zero hb)
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R B a) (algebraMap R B b)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl c
  have hinj := IsLocalization.injective B 𝔭.primeCompl_le_nonZeroDivisors
  have hspec := IsLocalization.mk'_spec B r s
  have hs : (s : R) ∉ ctr W hW := s.2
  rcases hc with h | h
  · have h' : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    have hL : (algebraMap R F a) * (algebraMap R F r) =
        (algebraMap R F b) * (algebraMap R F s) := by
      rw [← map_mul, ← map_mul, h']
    by_cases hr : r ∈ 𝔭
    · exfalso
      apply hs
      have hX : (⟨_, hx⟩ : W) * toW W hW r = toW W hW s := by
        apply Subtype.ext
        change (algebraMap R F a / algebraMap R F b) * (algebraMap R F r) = algebraMap R F s
        rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
      change toW W hW s ∈ maximalIdeal W
      rw [← hX]
      exact Ideal.mul_mem_left _ _ hr
    · refine ⟨s, r, hr, ?_⟩
      rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
  · have h' : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    refine ⟨r, s, hs, ?_⟩
    have hL : (algebraMap R F b) * (algebraMap R F r) =
        (algebraMap R F a) * (algebraMap R F s) := by
      rw [← map_mul, ← map_mul, h']
    rw [div_mul_eq_mul_div, ← hL, mul_div_cancel_left₀ _ hb0]

end Loc

/-! ## B. The inertia field of a finite Galois extension is unramified -/

section Key

theorem nonunits_comap {E M : Type*} [Field E] [Field M] (f : E →+* M) (W : ValuationSubring M)
    (x : E) : x ∈ (W.comap f).nonunits ↔ f x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  simp only [ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem div_mem_nonunits {M : Type*} [Field M] (W : ValuationSubring M) {n d : M}
    (hn : n ∈ W.nonunits) (hd : d ∈ W) (hd' : d ∉ W.nonunits) : n / d ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hn hd' ⊢
  have h1 : W.valuation d = 1 :=
    le_antisymm ((W.valuation_le_one_iff d).mpr hd) (not_lt.mp hd')
  rw [map_div₀, h1, div_one]
  exact hn

theorem div_mem {M : Type*} [Field M] (W : ValuationSubring M) {n d : M}
    (hn : n ∈ W) (hd : d ∈ W) (hd' : d ∉ W.nonunits) : n / d ∈ W := by
  rw [← W.valuation_le_one_iff] at hn ⊢
  rw [ValuationSubring.mem_nonunits_iff] at hd'
  have h1 : W.valuation d = 1 :=
    le_antisymm ((W.valuation_le_one_iff d).mpr hd) (not_lt.mp hd')
  rw [map_div₀, h1, div_one]
  exact hn

/-- An element of `M` integral over a subring contained in `W` lies in `W`. -/
theorem mem_of_isIntegral {A M : Type*} [CommRing A] [Field M] [Algebra A M]
    (W : ValuationSubring M) (hAW : ∀ a : A, algebraMap A M a ∈ W) {x : M}
    (hx : IsIntegral A x) : x ∈ W := by
  letI : Algebra A W := ((algebraMap A M).codRestrict W.toSubring hAW).toAlgebra
  haveI : IsScalarTower A W M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h2 : IsIntegral W x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2


/-- **Uniformizer from `𝔮 · J ⊆ ϖR` with `J ⊄ 𝔮`.** `R` Dedekind, `W` a valuation subring of
`F = Frac R` over `R` with center `𝔮 ≠ 0`, `ϖ ∈ 𝔮` and `j ∉ 𝔮` with `𝔮 · j ⊆ ϖ R`. Then every nonzero
`y ∈ F` with `y = a/s`, `s ∉ 𝔮`, is `ϖⁿ` times a unit of `W`. -/
theorem unit_mul_pow_of_div {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (W : ValuationSubring F)
    (hW : ∀ r : R, algebraMap R F r ∈ W) (ϖ j : R) (hj : j ∉ ctr W hW)
    (hdiv : ∀ n ∈ ctr W hW, ∃ r : R, n * j = ϖ * r) (hϖ : ϖ ∈ ctr W hW) (hϖ0 : ϖ ≠ 0) :
    ∀ (m : ℕ) (y : F) (a s : R), y ≠ 0 → s ∉ ctr W hW →
      y * algebraMap R F s = algebraMap R F a → a ∉ (ctr W hW) ^ (m + 1) →
      ∃ n : ℕ, y / algebraMap R F ϖ ^ n ∈ W ∧ (y / algebraMap R F ϖ ^ n)⁻¹ ∈ W := by
  set 𝔮 := ctr W hW
  have hϖF : algebraMap R F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hϖ0
  have unit_case : ∀ (y : F) (a s : R), y ≠ 0 → s ∉ 𝔮 →
      y * algebraMap R F s = algebraMap R F a → a ∉ 𝔮 →
      ∃ n : ℕ, y / algebraMap R F ϖ ^ n ∈ W ∧ (y / algebraMap R F ϖ ^ n)⁻¹ ∈ W := by
    intro y a s hy hs hys ha
    refine ⟨0, ?_, ?_⟩
    · rw [pow_zero, div_one]; exact mem_of_mul_eq' W hW hs hys
    · rw [pow_zero, div_one]
      refine mem_of_mul_eq' W hW (a := s) ha ?_
      rw [← hys]; field_simp
  intro m
  induction m with
  | zero =>
    intro y a s hy hs hys ha
    exact unit_case y a s hy hs hys (by rwa [zero_add, pow_one] at ha)
  | succ m ih =>
    intro y a s hy hs hys ha
    by_cases ha𝔮 : a ∉ 𝔮
    · exact unit_case y a s hy hs hys ha𝔮
    push Not at ha𝔮
    obtain ⟨r, hr⟩ := hdiv a ha𝔮
    have hsj : s * j ∉ 𝔮 := fun h =>
      ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hs hj)
    have hr' : r ∉ 𝔮 ^ (m + 1) := by
      intro hrm
      have h1 : j * a ∈ 𝔮 ^ (m + 1 + 1) := by
        rw [mul_comm, hr, pow_succ']
        exact Ideal.mul_mem_mul hϖ hrm
      rcases Ideal.IsPrime.mul_mem_pow 𝔮 h1 with h | h
      · exact hj h
      · exact ha h
    have hy' : y / algebraMap R F ϖ ≠ 0 := div_ne_zero hy hϖF
    have hys' : y / algebraMap R F ϖ * algebraMap R F (s * j) = algebraMap R F r := by
      have h2 : algebraMap R F a * algebraMap R F j = algebraMap R F ϖ * algebraMap R F r := by
        rw [← map_mul, ← map_mul, hr]
      rw [← hys] at h2
      rw [map_mul]
      field_simp
      linear_combination h2
    obtain ⟨n, h1, h2⟩ := ih (y / algebraMap R F ϖ) r (s * j) hy' hsj hys' hr'
    refine ⟨n + 1, ?_, ?_⟩
    · rwa [pow_succ', ← div_div]
    · rwa [pow_succ', ← div_div]

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K]
  [IsFractionRing A K] [Algebra A M] [IsScalarTower A K M]

instance instSMulCommClassGal : SMulCommClass (M ≃ₐ[K] M) A M where
  smul_comm σ a x := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A K M, AlgEquiv.commutes]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Key lemma (finite level, any characteristic, any residue field).** `M/K` finite Galois, `A ⊆ K`
a DVR, `W` a valuation ring of `M` over `A`. If `x ∈ W` is fixed by every `σ ∈ Gal(M/K)` acting
trivially modulo `𝔪_W`, then (a) if `x ≠ 0`, `x = ϖⁿ · (unit of W)` for a uniformizer `ϖ` of `A`;
(b) `x` is a root modulo `𝔪_W` of a polynomial over `A` with separable reduction. -/
theorem key_finite
    (W : ValuationSubring M) (hAW : ∀ a : A, algebraMap A M a ∈ W)
    (hctr : ∀ a : A, algebraMap A M a ∈ W.nonunits ↔ a ∈ maximalIdeal A)
    (ϖ : A) (hϖ : Irreducible ϖ) (x : M)
    (hfix : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ x = x)
    (hxW : x ∈ W) :
    (x ≠ 0 → ∃ n : ℕ, x / algebraMap A M ϖ ^ n ∈ W ∧ (x / algebraMap A M ϖ ^ n)⁻¹ ∈ W) ∧
    ∃ f : A[X], (f.map (residue A)).Separable ∧ (f.map (algebraMap A M)).eval x ∈ W.nonunits := by
  classical
  -- the ring of integers `S` of `M` over `A`
  let S := integralClosure A M
  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain A K M
  haveI : Module.Finite A S := IsIntegralClosure.finite A K M S
  haveI : IsFractionRing S M := IsIntegralClosure.isFractionRing_of_finite_extension A K M S
  haveI : IsGaloisGroup (M ≃ₐ[K] M) A S := IsGaloisGroup.of_isFractionRing _ A S K M
  have hSW : ∀ s : S, algebraMap S M s ∈ W := fun s =>
    mem_of_isIntegral W hAW s.2
  let p := maximalIdeal A
  let P : Ideal S := ctr W hSW
  have hP : ∀ s : S, s ∈ P ↔ (s : M) ∈ W.nonunits := fun s => mem_ctr_iff W hSW s
  haveI : P.LiesOver p := by
    constructor
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hP]
    exact (hctr a).symm
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖp : ϖ ∈ p := (mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hAinj : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have hP0 : P ≠ ⊥ := by
    intro h
    have : algebraMap A S ϖ ∈ P := by rw [hP]; exact (hctr ϖ).mpr hϖp
    rw [h, Ideal.mem_bot] at this
    apply hϖ0
    apply hAinj
    rw [map_zero]
    exact congrArg (fun z : S => (z : M)) this
  haveI : FaithfulSMul A S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hAinj (congrArg (fun z : S => (z : M)) h)
  haveI : Module.IsTorsionFree A S := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  -- the inertia field `E` and its ring of integers `R`
  let H := P.inertia (M ≃ₐ[K] M)
  let E : IntermediateField K M := FixedPoints.intermediateField H
  haveI : IsScalarTower A E M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let R := integralClosure A E
  haveI : IsDedekindDomain R := integralClosure.isDedekindDomain A K E
  haveI : Module.Finite A R := IsIntegralClosure.finite A K E R
  haveI : IsFractionRing R E := IsIntegralClosure.isFractionRing_of_finite_extension A K E R
  have hRS : ∀ r : R, IsIntegral A (algebraMap E M (r : E)) := fun r =>
    r.2.map (IsScalarTower.toAlgHom A E M)
  let φ : R →+* S := ((algebraMap E M).comp (algebraMap R E)).codRestrict S (fun r => hRS r)
  letI : Algebra R S := φ.toAlgebra
  haveI : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    change algebraMap A M a = algebraMap E M (algebraMap A E a)
    rw [← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.tower_top A
  haveI : IsGaloisGroup H E M := IsGaloisGroup.subgroup (M ≃ₐ[K] M) K M H
  haveI : IsGaloisGroup H R S := IsGaloisGroup.of_isFractionRing H R S E M
  haveI : Module.Finite R S := Module.Finite.of_restrictScalars_finite A R S
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply Subtype.ext
    apply (algebraMap E M).injective
    exact congrArg (fun z : S => (z : M)) h
  haveI : Module.IsTorsionFree R S := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  let 𝔮 : Ideal R := P.under R
  haveI : 𝔮.LiesOver p := Ideal.LiesOver.tower_bot P 𝔮 p
  have hRinj0 : Function.Injective (algebraMap A R) := by
    intro a b h
    exact hAinj (congrArg (fun r : R => algebraMap E M (r : E)) h)
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hϖ𝔮0 : algebraMap A R ϖ ∈ 𝔮 := by
    change algebraMap R S (algebraMap A R ϖ) ∈ P
    rw [← IsScalarTower.algebraMap_apply, hP]
    exact (hctr ϖ).mpr hϖp
  have h𝔮0 : 𝔮 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hϖ𝔮0
    exact hϖ0 (hRinj0 (by rw [hϖ𝔮0, map_zero]))
  haveI : 𝔮.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔮0
  obtain ⟨he𝔮, hsep⟩ := inertia_unram (M ≃ₐ[K] M) p P (R := R)
  -- `p𝓞_E = 𝔮 · J` with `J ⊄ 𝔮`
  have hpspan : p = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hRinj : Function.Injective (algebraMap A R) := by
    intro a b h
    exact hAinj (congrArg (fun r : R => algebraMap E M (r : E)) h)
  have hpR0 : p.map (algebraMap A R) ≠ ⊥ := by
    rw [hpspan, Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hϖ0 (hRinj (by rw [h, map_zero]))
  have hmult := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p 𝔮 hpR0
  rw [he𝔮] at hmult
  have h𝔮top : 𝔮 ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hfin : FiniteMultiplicity 𝔮 (p.map (algebraMap A R)) :=
    FiniteMultiplicity.of_not_isUnit (by rwa [Ideal.isUnit_iff]) hpR0
  obtain ⟨J, hJ⟩ : 𝔮 ∣ p.map (algebraMap A R) := by
    have := pow_multiplicity_dvd 𝔮 (p.map (algebraMap A R))
    rwa [← hmult, pow_one] at this
  have hJ𝔮 : ¬ J ≤ 𝔮 := by
    intro hle
    apply hfin.not_pow_dvd_of_multiplicity_lt (m := 2) (by rw [← hmult]; norm_num)
    rw [hJ, pow_two]
    exact mul_dvd_mul_left 𝔮 (Ideal.dvd_iff_le.mpr hle)
  obtain ⟨j, hjJ, hj𝔮⟩ := IsConcreteLE.not_le_iff_exists.mp hJ𝔮
  let ϖR := algebraMap A R ϖ
  have hϖR : p.map (algebraMap A R) = Ideal.span {ϖR} := by
    rw [hpspan, Ideal.map_span, Set.image_singleton]
  have hdivide : ∀ n ∈ 𝔮, ∃ r : R, n * j = ϖR * r := by
    intro n hn
    have : n * j ∈ p.map (algebraMap A R) := by
      rw [hJ]; exact Ideal.mul_mem_mul hn hjJ
    rw [hϖR, Ideal.mem_span_singleton'] at this
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr, mul_comm]⟩
  have hϖ𝔮 : ϖR ∈ 𝔮 := by
    have : ϖR ∈ p.map (algebraMap A R) := Ideal.mem_map_of_mem _ hϖp
    rw [hJ] at this
    exact (Ideal.mul_le_right (I := J) (J := 𝔮)) (by rwa [mul_comm] at this)
  -- every element of the inertia group acts trivially modulo `𝔪_W` on all of `W`
  have hcond : ∀ σ ∈ H, ∀ y ∈ W, σ y - y ∈ W.nonunits := by
    intro σ hσ y hy
    obtain ⟨a, s, hs, hys⟩ := exists_of_mem W hSW hP0 hy
    have ha : σ (a : M) - a ∈ W.nonunits := by
      have := (hP _).mp (hσ a)
      have e1 : ((σ • a : S) : M) = σ (a : M) := rfl
      rwa [Subalgebra.coe_sub, e1] at this
    have hs' : σ (s : M) - s ∈ W.nonunits := by
      have := (hP _).mp (hσ s)
      have e1 : ((σ • s : S) : M) = σ (s : M) := rfl
      rwa [Subalgebra.coe_sub, e1] at this
    rw [hP] at hs
    have hsW : (s : M) ∈ W := hSW s
    rw [ValuationSubring.mem_nonunits_iff] at ha hs' hs ⊢
    have vs : W.valuation (s : M) = 1 :=
      le_antisymm ((W.valuation_le_one_iff _).mpr hsW) (not_lt.mp hs)
    have vσs : W.valuation (σ (s : M)) = 1 := by
      have : σ (s : M) = (s : M) + (σ (s : M) - s) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [vs]; exact hs'), vs]
    have hs0 : (s : M) ≠ 0 := fun h => by rw [h, map_zero] at vs; exact zero_ne_one vs
    have hσs0 : σ (s : M) ≠ 0 := fun h => by rw [h, map_zero] at vσs; exact zero_ne_one vσs
    have hy' : y = (a : M) / s := by rw [eq_div_iff hs0]; exact hys
    have key : σ y - y = ((σ (a : M) - a) * s - a * (σ (s : M) - s)) / (σ (s : M) * s) := by
      rw [hy', map_div₀]
      field_simp
      ring
    rw [key, map_div₀, map_mul, vσs, vs, _root_.mul_one, div_one]
    have haW : W.valuation (a : M) ≤ 1 := (W.valuation_le_one_iff _).mpr (hSW a)
    rw [sub_eq_add_neg]
    apply Valuation.map_add_lt _
    · rw [map_mul, vs, _root_.mul_one]; exact ha
    · rw [Valuation.map_neg, map_mul]
      calc W.valuation (a : M) * W.valuation (σ (s : M) - s)
          ≤ 1 * W.valuation (σ (s : M) - s) := by gcongr
        _ < 1 := by rw [_root_.one_mul]; exact hs'
  have hxE : x ∈ E := by
    intro h
    exact hfix h (hcond h h.2)
  -- the valuation ring of `E`
  let WE := W.comap (algebraMap E M)
  have hRW : ∀ r : R, algebraMap R E r ∈ WE := fun r => hSW (φ r)
  have hctrE : ctr WE hRW = 𝔮 := by
    ext r
    rw [mem_ctr_iff, nonunits_comap]
    exact (hP (φ r)).symm
  have hϖR0 : algebraMap A R ϖ ≠ 0 := fun h => hϖ0 (hRinj (by rw [h, map_zero]))
  have hctrE0 : ctr WE hRW ≠ ⊥ := by
    rw [hctrE]
    intro h
    rw [h] at hϖ𝔮
    exact hϖR0 hϖ𝔮
  obtain ⟨a, s, hs, hxs⟩ := exists_of_mem WE hRW hctrE0 (x := ⟨x, hxE⟩) hxW
  have hφ𝔮 : ∀ r : R, r ∈ 𝔮 ↔ (φ r : M) ∈ W.nonunits := fun r => hP (φ r)
  refine ⟨fun hx0 => ?_, ?_⟩
  swap
  · haveI : 𝔮.LiesOver p := inferInstance
    obtain ⟨f, hf, hfx⟩ := exists_sep_poly ((algebraMap E M).comp (algebraMap R E)) p 𝔮 W
      hφ𝔮 (fun r => hSW (φ r)) x a s (by rwa [← hctrE]) (by
        have := congrArg (algebraMap E M) hxs
        rwa [map_mul] at this)
    refine ⟨f, hf, ?_⟩
    have e : ((algebraMap E M).comp (algebraMap R E)).comp (algebraMap A R) = algebraMap A M := by
      ext c
      change algebraMap E M (algebraMap R E (algebraMap A R c)) = algebraMap A M c
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rwa [e] at hfx
  have hxE0 : (⟨x, hxE⟩ : E) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hxs
    rcases mul_eq_zero.mp hxs with h' | h'
    · exact hxE0 h'
    · apply hs
      rw [(map_eq_zero_iff _ (IsFractionRing.injective R E)).mp h']
      exact Ideal.zero_mem _
  have hfa : FiniteMultiplicity 𝔮 (Ideal.span {a}) :=
    FiniteMultiplicity.of_not_isUnit (by rwa [Ideal.isUnit_iff])
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha0)
  have ham : a ∉ 𝔮 ^ (multiplicity 𝔮 (Ideal.span {a}) + 1) := by
    intro h
    apply hfa.not_pow_dvd_of_multiplicity_lt (lt_add_one _)
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [← hctrE] at hdivide hϖ𝔮 hj𝔮 ham
  obtain ⟨n, h1, h2⟩ := unit_mul_pow_of_div WE hRW (algebraMap A R ϖ) j hj𝔮 hdivide hϖ𝔮 hϖR0
    _ _ a s hxE0 hs hxs ham
  have e : ((algebraMap A E ϖ : E) : M) = algebraMap A M ϖ := rfl
  refine ⟨n, ?_, ?_⟩
  · have := h1; simpa [WE, ValuationSubring.mem_comap, e] using this
  · have := h2; simpa [WE, ValuationSubring.mem_comap, e] using this

end Key

end GapSHPair


-- ===== part GTCA2 =====

/-!
# sh-route, part C: the inertia field inside an algebraic closure

`K` any field, `Ω` an algebraic closure, `w` a valuation ring of `Ω`. The inertia field
`inertiaField w` is the set of `x ∈ Ω` such that, for some finite Galois `M ∋ x`, every
`τ ∈ Aut(Ω/K)` acting trivially modulo `𝔪_w` on `w ∩ M` fixes `x` (the union of the inertia fields
of the finite Galois subextensions).
-/

open IsLocalRing Polynomial

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GapSHPair

section Omega

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

/-- `τ` acts trivially modulo `𝔪_w` on `w ∩ M`. -/
def CondM (M : IntermediateField K Ω) (τ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ y ∈ M, y ∈ w → τ y - y ∈ w.nonunits

theorem CondM.mono {M M' : IntermediateField K Ω} (h : M ≤ M') {τ : Ω ≃ₐ[K] Ω}
    (hτ : CondM w M' τ) : CondM w M τ := fun y hy => hτ y (h hy)

/-- `x ∈ M` is fixed by every `τ` acting trivially modulo `𝔪_w` on `w ∩ M`. -/
def FixVia (M : IntermediateField K Ω) (x : Ω) : Prop :=
  x ∈ M ∧ ∀ τ : Ω ≃ₐ[K] Ω, CondM w M τ → τ x = x

theorem FixVia.mono {M M' : IntermediateField K Ω} (h : M ≤ M') {x : Ω} (hx : FixVia w M x) :
    FixVia w M' x := ⟨h hx.1, fun τ hτ => hx.2 τ (hτ.mono w h)⟩

/-- `M` is finite Galois over `K`. -/
def IsFG (M : IntermediateField K Ω) : Prop := FiniteDimensional K M ∧ IsGalois K M

/-- An inertia automorphism acts trivially modulo `𝔪_w` on all of `w`. -/
theorem condM_of_isInertia {σ : Ω ≃ₐ[K] Ω} (hσ : PkgI2.IsInertia w σ) (M : IntermediateField K Ω) :
    CondM w M σ := by
  intro y _ hy
  obtain ⟨h, hI⟩ := hσ
  have h1 : (⟨σ, h⟩ : w.decompositionSubgroup K) • residue w ⟨y, hy⟩ = residue w ⟨y, hy⟩ := by
    have := congrArg (fun f => f (residue w ⟨y, hy⟩)) (MonoidHom.mem_ker.mp hI)
    exact this
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  have h2 := (Ideal.Quotient.eq).mp h1
  rw [ValuationSubring.valuation_lt_one_iff] at h2
  rw [ValuationSubring.mem_nonunits_iff]
  exact h2

variable [IsAlgClosure K Ω]

/-- An intermediate field all of whose elements are separable is separable. -/
theorem isSeparable_of_forall (s : IntermediateField K Ω) (h : ∀ x ∈ s, IsSeparable K x) :
    Algebra.IsSeparable K s :=
  (le_separableClosure_iff K Ω s).mp (fun x hx => mem_separableClosure_iff.mpr (h x hx))

theorem IsFG.isSeparable {M : IntermediateField K Ω} (hM : IsFG M) {x : Ω} (hx : x ∈ M) :
    IsSeparable K x := by
  haveI := hM.2
  have := Algebra.IsSeparable.isSeparable K (⟨x, hx⟩ : M)
  rwa [IsSeparable, IntermediateField.minpoly_eq] at this

theorem isFG_of (s : IntermediateField K Ω) [FiniteDimensional K s] [Algebra.IsSeparable K s] :
    ∃ M : IntermediateField K Ω, IsFG M ∧ s ≤ M := by
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  exact ⟨IntermediateField.normalClosure K s Ω, ⟨inferInstance, inferInstance⟩,
    IntermediateField.le_normalClosure s⟩

theorem isFG_bot : ∃ M : IntermediateField K Ω, IsFG M := by
  haveI : Algebra.IsSeparable K (⊥ : IntermediateField K Ω) :=
    isSeparable_of_forall _ (fun x hx => by
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hx
      exact isSeparable_algebraMap c)
  obtain ⟨M, hM, -⟩ := isFG_of (⊥ : IntermediateField K Ω)
  exact ⟨M, hM⟩

theorem exists_two {M₁ M₂ : IntermediateField K Ω} (h₁ : IsFG M₁) (h₂ : IsFG M₂) :
    ∃ M : IntermediateField K Ω, IsFG M ∧ M₁ ≤ M ∧ M₂ ≤ M := by
  haveI := h₁.1
  haveI := h₂.1
  haveI : Algebra.IsSeparable K (M₁ ⊔ M₂ : IntermediateField K Ω) := by
    haveI := h₁.2
    haveI := h₂.2
    exact (le_separableClosure_iff K Ω _).mp
      (sup_le (le_separableClosure K Ω M₁) (le_separableClosure K Ω M₂))
  obtain ⟨M, hM, hle⟩ := isFG_of (M₁ ⊔ M₂)
  exact ⟨M, hM, le_trans le_sup_left hle, le_trans le_sup_right hle⟩

/-- The inertia field of `w` (over `K`). -/
def inertiaField : IntermediateField K Ω where
  carrier := {x | ∃ M : IntermediateField K Ω, IsFG M ∧ FixVia w M x}
  mul_mem' := by
    rintro x y ⟨M₁, h₁, hx⟩ ⟨M₂, h₂, hy⟩
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    have hx := hx.mono w l₁
    have hy := hy.mono w l₂
    exact ⟨M, hM, M.mul_mem hx.1 hy.1, fun τ hτ => by rw [map_mul, hx.2 τ hτ, hy.2 τ hτ]⟩
  add_mem' := by
    rintro x y ⟨M₁, h₁, hx⟩ ⟨M₂, h₂, hy⟩
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    have hx := hx.mono w l₁
    have hy := hy.mono w l₂
    exact ⟨M, hM, M.add_mem hx.1 hy.1, fun τ hτ => by rw [map_add, hx.2 τ hτ, hy.2 τ hτ]⟩
  algebraMap_mem' c := by
    obtain ⟨M, hM⟩ := isFG_bot (K := K) (Ω := Ω)
    exact ⟨M, hM, M.algebraMap_mem c, fun τ _ => τ.commutes c⟩
  inv_mem' := by
    rintro x ⟨M, hM, hx⟩
    exact ⟨M, hM, M.inv_mem hx.1, fun τ hτ => by rw [map_inv₀, hx.2 τ hτ]⟩

theorem mem_inertiaField {x : Ω} :
    x ∈ inertiaField (K := K) w ↔ ∃ M : IntermediateField K Ω, IsFG M ∧ FixVia w M x := Iff.rfl

/-- **The inertia group fixes the inertia field.** -/
theorem inertia_fixes {σ : Ω ≃ₐ[K] Ω} (hσ : PkgI2.IsInertia w σ) {x : Ω}
    (hx : x ∈ inertiaField (K := K) w) : σ x = x := by
  obtain ⟨M, -, hM⟩ := hx
  exact hM.2 σ (condM_of_isInertia w hσ M)

/-- Finitely many elements of the inertia field are fixed via one finite Galois `M`. -/
theorem exists_common (s : Finset Ω) (hs : ∀ x ∈ s, x ∈ inertiaField (K := K) w) :
    ∃ M : IntermediateField K Ω, IsFG M ∧ ∀ x ∈ s, FixVia w M x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨M, hM⟩ := isFG_bot (K := K) (Ω := Ω)
    exact ⟨M, hM, by simp⟩
  | insert a s _ ih =>
    obtain ⟨M₁, h₁, hM₁⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨M₂, h₂, hM₂⟩ := hs a (Finset.mem_insert_self a s)
    obtain ⟨M, hM, l₁, l₂⟩ := exists_two h₁ h₂
    refine ⟨M, hM, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hM₂.mono w l₂
    · exact (hM₁ x hx).mono w l₁

end Omega

section Ring

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

theorem mem_max_iff (b : w) : b ∈ maximalIdeal w ↔ (b : Ω) ∈ w.nonunits := by
  rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]

theorem mem_max_comap_iff {E : Type} [Field E] (f : E →+* Ω) (a : w.comap f) :
    a ∈ maximalIdeal (w.comap f) ↔ f (a : E) ∈ w.nonunits := by
  rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff,
    nonunits_comap]

/-- **Roots near a point.** A monic `q ∈ w[X]` with `q(c) ∈ 𝔪_w` has a root `α ∈ w` with
`α ≡ c mod 𝔪_w` (`Ω` algebraically closed, `w` integrally closed). -/
theorem exists_root_near [IsAlgClosed Ω] (q : w[X]) (hq : q.Monic) (c : w)
    (hc : q.eval c ∈ maximalIdeal w) : ∃ α : w, q.IsRoot α ∧ α - c ∈ maximalIdeal w := by
  induction h : q.natDegree generalizing q with
  | zero =>
    exfalso
    rw [hq.natDegree_eq_zero] at h
    rw [h, eval_one] at hc
    exact (maximalIdeal.isMaximal w).ne_top ((Ideal.eq_top_iff_one _).mpr hc)
  | succ n ih =>
    have hdeg : (q.map (algebraMap w Ω)).degree ≠ 0 := by
      rw [hq.degree_map, degree_eq_natDegree hq.ne_zero, h]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (q.map (algebraMap w Ω)) hdeg
    have hβw : β ∈ w := mem_of_isIntegral w (A := w) (fun a => a.2)
      ⟨q, hq, by rwa [IsRoot, Polynomial.eval_map] at hβ⟩
    let β' : w := ⟨β, hβw⟩
    have hr : q.IsRoot β' := by
      apply Subtype.ext
      rw [IsRoot, Polynomial.eval_map] at hβ
      have : algebraMap w Ω (q.eval β') = q.eval₂ (algebraMap w Ω) β := by
        rw [← eval₂_at_apply]; rfl
      exact this.trans hβ
    have hfac := (mul_divByMonic_eq_iff_isRoot).mpr hr
    have hq2 : (q /ₘ (X - C β')).Monic :=
      Monic.of_mul_monic_left (monic_X_sub_C β') (by rw [hfac]; exact hq)
    have hdeg2 : (q /ₘ (X - C β')).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C β'), h, natDegree_X_sub_C]; rfl
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at hc
    rcases (maximalIdeal.isMaximal w).isPrime.mem_or_mem hc with h1 | h1
    · exact ⟨β', hr, by rw [← neg_sub]; exact neg_mem h1⟩
    · obtain ⟨α, hα, hαc⟩ := ih (q /ₘ (X - C β')) hq2 h1 hdeg2
      refine ⟨α, ?_, hαc⟩
      rw [IsRoot, ← hfac, eval_mul, hα.eq_zero, mul_zero]

/-- **Two distinct roots with the same residue give a double root modulo `𝔪_w`.** -/
theorem derivative_eval_eq_zero_of_two_roots (q : w[X]) {α β : w} (hα : q.IsRoot α)
    (hβ : q.IsRoot β) (hne : α ≠ β) (hres : residue w α = residue w β) :
    ((q.map (residue w)).derivative).eval (residue w α) = 0 := by
  have hfac := (mul_divByMonic_eq_iff_isRoot).mpr hα
  set q1 := q /ₘ (X - C α)
  have hβ1 : q1.IsRoot β := by
    have := hβ
    rw [IsRoot, ← hfac, eval_mul, eval_sub, eval_X, eval_C] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hfac1 := (mul_divByMonic_eq_iff_isRoot).mpr hβ1
  rw [← hfac, ← hfac1]
  simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, derivative_mul,
    derivative_sub, derivative_X, derivative_C, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    hres, sub_self, zero_mul, mul_zero, add_zero]

variable [IsAlgClosure K Ω]

/-- **A simple root of a polynomial with coefficients in a separable `M₀` is separable.** -/
theorem isSeparable_of_simple_root (M₀ : IntermediateField K Ω) [Algebra.IsSeparable K M₀]
    (G : Polynomial Ω) (hG : ∀ i, G.coeff i ∈ M₀) (α : Ω) (hα : G.eval α = 0)
    (hd : G.derivative.eval α ≠ 0) : IsSeparable K α := by
  obtain ⟨G₀, hG₀'⟩ : G ∈ Polynomial.lifts (algebraMap M₀ Ω) :=
    (lifts_iff_coeff_lifts G).mpr (fun n => ⟨⟨_, hG n⟩, rfl⟩)
  have hG₀ : G₀.map (algebraMap M₀ Ω) = G := hG₀'
  have hG0 : aeval α G₀ = 0 := by rw [aeval_def, eval₂_eq_eval_map, hG₀, hα]
  have hGne : G₀ ≠ 0 := by
    rintro rfl
    apply hd
    rw [← hG₀, Polynomial.map_zero, derivative_zero, eval_zero]
  have hint : IsIntegral M₀ α := (IsAlgebraic.isIntegral ⟨G₀, hGne, hG0⟩)
  obtain ⟨h, hh⟩ := minpoly.dvd M₀ α hG0
  have hm : (minpoly M₀ α).derivative ≠ 0 := by
    intro h0
    apply hd
    rw [← hG₀, hh, Polynomial.map_mul, derivative_mul, Polynomial.derivative_map, h0,
      Polynomial.map_zero, zero_mul, zero_add, eval_mul, eval_map, ← aeval_def, minpoly.aeval,
      zero_mul]
  have hsep : IsSeparable M₀ α :=
    (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)).mpr hm
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable K hsep

/-- The valuation ring of the inertia field. -/
abbrev wE : ValuationSubring (inertiaField (K := K) w) :=
  w.comap (algebraMap (inertiaField (K := K) w) Ω)

/-- `wE → Ω`. -/
def ιΩ : wE (K := K) w →+* Ω :=
  (algebraMap (inertiaField (K := K) w) Ω).comp (wE (K := K) w).subtype

/-- `wE → w`. -/
def ιw : wE (K := K) w →+* w :=
  (ιΩ (K := K) w).codRestrict w.toSubring (fun a => a.2)

theorem ιw_coe (a : wE (K := K) w) : ((ιw w a : w) : Ω) = ιΩ w a := rfl

theorem map_ιΩ_eq (g : (wE (K := K) w)[X]) : g.map (ιΩ w) = (g.map (ιw w)).map (algebraMap w Ω) := by
  rw [Polynomial.map_map]; rfl

/-- **Core lemma.** A root `α` of a monic `g` over the valuation ring of the inertia field whose
residue is a simple root of `g mod 𝔪_w` lies in the inertia field. -/
theorem mem_inertiaField_of_simple_root (g : (wE (K := K) w)[X]) (α : Ω)
    (hα : (g.map (ιΩ w)).eval α = 0) (hαw : α ∈ w)
    (hs : ((g.map ((residue w).comp (ιw w))).derivative).eval (residue w ⟨α, hαw⟩) ≠ 0) :
    α ∈ inertiaField (K := K) w := by
  classical
  -- the coefficients are fixed via one `M₀`
  obtain ⟨M₀, h₀, hM₀⟩ := exists_common w (g.support.image fun i => ιΩ w (g.coeff i))
    (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (g.coeff i : inertiaField (K := K) w).2)
  haveI := h₀.1
  haveI := h₀.2
  have hαint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hαint
  have hcoefM₀ : ∀ i, (g.map (ιΩ w)).coeff i ∈ M₀ := by
    intro i
    rw [coeff_map]
    by_cases hi : i ∈ g.support
    · exact (hM₀ _ (Finset.mem_image_of_mem _ hi)).1
    · rw [notMem_support_iff.mp hi, map_zero]; exact M₀.zero_mem
  have hder : (g.map (ιΩ w)).derivative.eval α ≠ 0 := by
    intro h0
    apply hs
    rw [map_ιΩ_eq, derivative_map, eval_map] at h0
    have h1 : (g.map (ιw w)).derivative.eval ⟨α, hαw⟩ = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, ← h0]
      change algebraMap w Ω _ = _
      rw [← eval₂_at_apply]
      rfl
    rw [← Polynomial.map_map, derivative_map, eval_map, eval₂_at_apply, h1, map_zero]
  have hαsep : IsSeparable K α := isSeparable_of_simple_root M₀ _ hcoefM₀ α hα hder
  haveI : Algebra.IsSeparable K (M₀ ⊔ IntermediateField.adjoin K {α} : IntermediateField K Ω) := by
    haveI : Algebra.IsSeparable K (IntermediateField.adjoin K {α}) :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K Ω).mpr hαsep
    exact (le_separableClosure_iff K Ω _).mp
      (sup_le (le_separableClosure K Ω M₀) (le_separableClosure K Ω _))
  obtain ⟨M, hM, hle⟩ := isFG_of (M₀ ⊔ IntermediateField.adjoin K {α})
  have hαM : α ∈ M := hle (le_sup_right (a := M₀) (IntermediateField.mem_adjoin_simple_self K α))
  refine ⟨M, hM, hαM, fun τ hτ => ?_⟩
  have hτ₀ : CondM w M₀ τ := hτ.mono w (le_trans le_sup_left hle)
  -- `τ α` is a root of `g`
  have hcoef : (g.map (ιΩ w)).map (τ : Ω →+* Ω) = g.map (ιΩ w) := by
    ext i
    rw [coeff_map, coeff_map]
    by_cases hi : i ∈ g.support
    · exact (hM₀ _ (Finset.mem_image_of_mem _ hi)).2 τ hτ₀
    · rw [notMem_support_iff.mp hi, map_zero, map_zero]
  have hτα : (g.map (ιΩ w)).eval (τ α) = 0 := by
    rw [← hcoef, Polynomial.eval_map]
    change eval₂ (τ : Ω →+* Ω) ((τ : Ω →+* Ω) α) _ = 0
    rw [eval₂_at_apply, hα, map_zero]
  have hτw : τ α - α ∈ w.nonunits := hτ α hαM hαw
  by_contra hne
  have hταw : τ α ∈ w := by
    have : τ α = α + (τ α - α) := by ring
    rw [this]
    exact add_mem hαw (ValuationSubring.nonunits_le hτw)
  let gw := g.map (ιw w)
  have root_of : ∀ (x : Ω) (hx : x ∈ w), (g.map (ιΩ w)).eval x = 0 → gw.IsRoot ⟨x, hx⟩ := by
    intro x hx h
    apply Subtype.ext
    have e : g.map (ιΩ w) = gw.map (algebraMap w Ω) := by
      rw [Polynomial.map_map]; rfl
    rw [e, Polynomial.eval_map] at h
    change algebraMap w Ω (gw.eval ⟨x, hx⟩) = algebraMap w Ω 0
    rw [← eval₂_at_apply, map_zero]
    exact h
  have h2 := derivative_eval_eq_zero_of_two_roots w gw (root_of α hαw hα)
    (root_of (τ α) hταw hτα) (fun h => hne (congrArg Subtype.val h).symm)
    (by
      rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_max_iff]
      exact hτw)
  apply hs
  rw [← h2, Polynomial.map_map]



instance isLocalHom_ιw : IsLocalHom (ιw (K := K) w) := by
  constructor
  intro a ha
  by_contra h
  have h1 : a ∈ maximalIdeal (wE (K := K) w) := h
  rw [mem_max_comap_iff] at h1
  have h2 : ιw w a ∈ maximalIdeal w := by rw [mem_max_iff]; exact h1
  exact h2 ha

/-- **The valuation ring of the inertia field is henselian.** -/
theorem henselian_wE : HenselianLocalRing (wE (K := K) w) where
  is_henselian f hf a₀ h₁ h₂ := by
    let q := f.map (ιw w)
    have hq : q.Monic := hf.map _
    have hc : q.eval (ιw w a₀) ∈ maximalIdeal w := by
      rw [Polynomial.eval_map, eval₂_at_apply, mem_max_iff, ιw_coe]
      exact (mem_max_comap_iff w _ _).mp h₁
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
    obtain ⟨α, hα, hαc⟩ := exists_root_near w q hq _ hc
    have hroot : (f.map (ιΩ w)).eval (α : Ω) = 0 := by
      rw [map_ιΩ_eq, Polynomial.eval_map]
      change eval₂ (algebraMap w Ω) (algebraMap w Ω α) q = 0
      rw [eval₂_at_apply, hα.eq_zero, map_zero]
    have hres : residue w α = residue w (ιw w a₀) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hαc
    have hsimple : ((f.map ((residue w).comp (ιw w))).derivative).eval
        (residue w ⟨(α : Ω), α.2⟩) ≠ 0 := by
      have e : (⟨(α : Ω), α.2⟩ : w) = α := rfl
      rw [e, hres, derivative_map, Polynomial.eval_map]
      change eval₂ ((residue w).comp (ιw w)) (((residue w).comp (ιw w)) a₀) _ ≠ 0
      rw [eval₂_at_apply, RingHom.comp_apply, residue_ne_zero_iff_isUnit]
      exact h₂.map _
    have hαE := mem_inertiaField_of_simple_root w f (α : Ω) hroot α.2 hsimple
    let a : wE (K := K) w := ⟨⟨α, hαE⟩, by exact α.2⟩
    refine ⟨a, ?_, ?_⟩
    · have h0 : ιΩ w (f.eval a) = 0 := by
        rw [← eval₂_at_apply, ← Polynomial.eval_map]; exact hroot
      apply Subtype.ext
      apply (algebraMap (inertiaField (K := K) w) Ω).injective
      change ιΩ w _ = algebraMap _ Ω 0
      rw [map_zero]
      exact h0
    · rw [mem_max_comap_iff]
      have := (mem_max_iff w _).mp hαc
      exact this

/-- **The residue field of the inertia field is separably closed.** -/
theorem isSepClosed_wE : IsSepClosed (ResidueField (wE (K := K) w)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  apply IsSepClosed.of_exists_root
  intro p hpm hpirr hpsep
  obtain ⟨g, hgp, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (residue _) residue_surjective p) hpm
  have hdeg : (g.map (ιΩ w)).degree ≠ 0 := by
    rw [hgm.degree_map, degree_eq_natDegree hgm.ne_zero, hgdeg]
    exact_mod_cast (Irreducible.natDegree_pos hpirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (g.map (ιΩ w)) hdeg
  have hαw : α ∈ w := by
    letI : Algebra (wE (K := K) w) Ω := (ιΩ w).toAlgebra
    exact mem_of_isIntegral w (A := wE (K := K) w) (fun a => a.2)
      ⟨g, hgm, by rwa [IsRoot, Polynomial.eval_map] at hα⟩
  -- the residue polynomial
  let κm := ResidueField.map (ιw (K := K) w)
  have hgw : g.map ((residue w).comp (ιw w)) = p.map κm := by
    rw [← hgp, Polynomial.map_map, ResidueField.map_comp_residue]
  have hgw0 : (g.map (ιw w)).eval ⟨α, hαw⟩ = 0 := by
    apply Subtype.ext
    change algebraMap w Ω _ = algebraMap w Ω 0
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, ← map_ιΩ_eq]
    exact hα
  have hroot' : (p.map κm).eval (residue w ⟨α, hαw⟩) = 0 := by
    rw [← hgw, ← Polynomial.map_map, Polynomial.eval_map, eval₂_at_apply, hgw0, map_zero]
  have hsimple : ((g.map ((residue w).comp (ιw w))).derivative).eval
      (residue w ⟨α, hαw⟩) ≠ 0 := by
    rw [hgw]
    have := (hpsep.map (f := κm)).eval₂_derivative_ne_zero (RingHom.id _) (x := residue w ⟨α, hαw⟩)
      (by rw [← Polynomial.eval]; exact hroot')
    exact this
  have hαE := mem_inertiaField_of_simple_root w g α hα hαw hsimple
  let a : wE (K := K) w := ⟨⟨α, hαE⟩, by exact hαw⟩
  refine ⟨residue _ a, ?_⟩
  have h0 : ιΩ w (g.eval a) = 0 := by
    rw [← eval₂_at_apply, ← Polynomial.eval_map]; exact hα
  have h1 : g.eval a = 0 := by
    apply Subtype.ext
    apply (algebraMap (inertiaField (K := K) w) Ω).injective
    change ιΩ w _ = algebraMap _ Ω 0
    rw [map_zero]
    exact h0
  rw [← hgp, Polynomial.eval_map, eval₂_at_apply, h1, map_zero]

end Ring

section DVR

open ReductSplit ReductGlue

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
  [IsAlgClosure K Ω] {O : ValuationSubring K} [IsDiscreteValuationRing O]

theorem mem_w_of_mem (hw : w.comap (algebraMap K Ω) = O) (a : O) : algebraMap K Ω a ∈ w := by
  have : (a : K) ∈ w.comap (algebraMap K Ω) := hw ▸ a.2
  exact this

theorem nonunits_iff_of (hw : w.comap (algebraMap K Ω) = O) (a : O) :
    algebraMap K Ω a ∈ w.nonunits ↔ a ∈ maximalIdeal O := by
  rw [← nonunits_comap (algebraMap K Ω) w (a : K), hw, ValuationSubring.mem_nonunits_iff,
    ← ValuationSubring.valuation_lt_one_iff]

/-- **Elements of the inertia field are uniformizer powers times units** (from `key_finite`). -/
theorem unit_pow (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ) (x : Ω)
    (hxE : x ∈ inertiaField (K := K) w) (hxw : x ∈ w) (hx0 : x ≠ 0) :
    ∃ n : ℕ, x / algebraMap K Ω ϖ ^ n ∈ w ∧ (x / algebraMap K Ω ϖ ^ n)⁻¹ ∈ w := by
  obtain ⟨M, ⟨hfd, hgal⟩, hxM, hfix⟩ := hxE
  haveI := hfd
  haveI := hgal
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  letI : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := w.comap (algebraMap M Ω)
  have hAW : ∀ a : O, algebraMap O M a ∈ W := fun a => mem_w_of_mem w hw a
  have hctr : ∀ a : O, algebraMap O M a ∈ W.nonunits ↔ a ∈ maximalIdeal O := by
    intro a
    rw [nonunits_comap]
    exact nonunits_iff_of w hw a
  have hfix' : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
    intro σ hσ
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hcond : CondM w M τ := by
      intro y hyM hyw
      have h1 := hσ ⟨y, hyM⟩ hyw
      rw [nonunits_comap, map_sub, ← hτ] at h1
      exact h1
    have := hfix τ hcond
    apply (algebraMap M Ω).injective
    rw [← hτ]
    exact this
  have hx0' : (⟨x, hxM⟩ : M) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨n, h1, h2⟩ := (key_finite (K := K) O W hAW hctr ϖ hϖ ⟨x, hxM⟩ hfix' hxw).1 hx0'
  have e : ((algebraMap O M ϖ : M) : Ω) = algebraMap K Ω ϖ := rfl
  refine ⟨n, ?_, ?_⟩
  · have := h1; simpa [W, ValuationSubring.mem_comap, e] using this
  · have := h2; simpa [W, ValuationSubring.mem_comap, e] using this

theorem hE_eq (hw : w.comap (algebraMap K Ω) = O) :
    (wE (K := K) w).comap (algebraMap K (inertiaField (K := K) w)) = O := by
  rw [ValuationSubring.comap_comap]
  exact hw

theorem ιΩ_injective : Function.Injective (ιΩ (K := K) w) := fun a b h =>
  Subtype.ext (Subtype.ext h)

theorem ιΩ_comapHom (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) :
    ιΩ w (comapHom (hE_eq w hw) ϖ) = algebraMap K Ω ϖ := rfl

theorem assoc_pow (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ)
    {a : wE (K := K) w} (ha : a ≠ 0) : ∃ n : ℕ, Associated (comapHom (hE_eq w hw) ϖ ^ n) a := by
  have hx0 : ιΩ w a ≠ 0 := fun h => ha (ιΩ_injective w (by rw [h, map_zero]))
  obtain ⟨n, h1, h2⟩ := unit_pow w hw ϖ hϖ (ιΩ w a) a.1.2 a.2 hx0
  have hϖ0 : algebraMap K Ω ϖ ≠ 0 := by
    rw [_root_.map_ne_zero]; exact fun h => hϖ.ne_zero (Subtype.ext h)
  have hyE : ιΩ w a / algebraMap K Ω ϖ ^ n ∈ inertiaField (K := K) w :=
    (inertiaField w).div_mem a.1.2 (pow_mem ((inertiaField w).algebraMap_mem _) n)
  have hyE' : (ιΩ w a / algebraMap K Ω ϖ ^ n)⁻¹ ∈ inertiaField (K := K) w :=
    (inertiaField w).inv_mem hyE
  let u : wE (K := K) w := ⟨⟨_, hyE⟩, by exact h1⟩
  let v : wE (K := K) w := ⟨⟨_, hyE'⟩, by exact h2⟩
  have hy0 : ιΩ w a / algebraMap K Ω ϖ ^ n ≠ 0 := div_ne_zero hx0 (pow_ne_zero _ hϖ0)
  have huv : u * v = 1 := ιΩ_injective w (by
    rw [map_mul, map_one]; exact mul_inv_cancel₀ hy0)
  refine ⟨n, Units.mk u v huv (by rw [mul_comm]; exact huv), ιΩ_injective w ?_⟩
  rw [map_mul, map_pow, ιΩ_comapHom w hw]
  change algebraMap K Ω ϖ ^ n * (ιΩ w a / algebraMap K Ω ϖ ^ n) = ιΩ w a
  field_simp

theorem irreducible_comapHom (hw : w.comap (algebraMap K Ω) = O) (ϖ : O) (hϖ : Irreducible ϖ) :
    Irreducible (comapHom (hE_eq w hw) ϖ) := by
  set π := comapHom (hE_eq w hw) ϖ
  have hπ0 : π ≠ 0 := fun h => by
    have := congrArg (ιΩ w) h
    rw [ιΩ_comapHom w hw, map_zero, map_eq_zero] at this
    exact hϖ.ne_zero (Subtype.ext this)
  have hπnu : ¬ IsUnit π := by
    intro h
    have h1 : π ∉ maximalIdeal (wE (K := K) w) := fun hm => hm h
    apply h1
    rw [mem_max_comap_iff]
    exact (nonunits_iff_of w hw ϖ).mpr ((mem_maximalIdeal _).mpr hϖ.not_isUnit)
  refine ⟨hπnu, fun a b hab => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hau, hbu⟩ := hcon
  have ha0 : a ≠ 0 := fun h => hπ0 (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hπ0 (by rw [hab, h, mul_zero])
  obtain ⟨n, u, hu⟩ := assoc_pow w hw ϖ hϖ ha0
  obtain ⟨m, u', hu'⟩ := assoc_pow w hw ϖ hϖ hb0
  rcases n with _ | n
  · exact hau (by rw [← hu, pow_zero, _root_.one_mul]; exact u.isUnit)
  rcases m with _ | m
  · exact hbu (by rw [← hu', pow_zero, _root_.one_mul]; exact u'.isUnit)
  have key : π * 1 = π * (π * (π ^ (n + m) * ((u : wE (K := K) w) * u'))) := by
    rw [_root_.mul_one]
    conv_lhs => rw [hab, ← hu, ← hu']
    ring
  have := mul_left_cancel₀ hπ0 key
  exact hπnu (isUnit_iff_exists_inv.mpr ⟨_, this.symm⟩)

theorem isDVR_wE (hw : w.comap (algebraMap K Ω) = O) :
    IsDiscreteValuationRing (wE (K := K) w) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_comapHom w hw ϖ hϖ, fun hx => assoc_pow w hw ϖ hϖ hx⟩

end DVR

end GapSHPair


-- ===== part GTCA3 =====

/-!
# gt-shpair, part E: separable residue fields, and strict henselizations along a finite extension
(any characteristic, any residue field)
-/

open IsLocalRing Polynomial IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GapSHPair

open ReductSplit ReductGlue

section ResSep

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
  [IsAlgClosure K Ω] {O : ValuationSubring K} [IsDiscreteValuationRing O]

/-- **Elements of the inertia field have separable residues** (from `key_finite`, part (b)). -/
theorem sep_poly (hw : w.comap (algebraMap K Ω) = O) (x : Ω)
    (hxE : x ∈ inertiaField (K := K) w) (hxw : x ∈ w) :
    ∃ f : O[X], (f.map (residue O)).Separable ∧
      (f.map ((algebraMap K Ω).comp O.subtype)).eval x ∈ w.nonunits := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨M, ⟨hfd, hgal⟩, hxM, hfix⟩ := hxE
  haveI := hfd
  haveI := hgal
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  letI : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := w.comap (algebraMap M Ω)
  have hAW : ∀ a : O, algebraMap O M a ∈ W := fun a => mem_w_of_mem w hw a
  have hctr : ∀ a : O, algebraMap O M a ∈ W.nonunits ↔ a ∈ maximalIdeal O := by
    intro a
    rw [nonunits_comap]
    exact nonunits_iff_of w hw a
  have hfix' : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
    intro σ hσ
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hcond : CondM w M τ := by
      intro y hyM hyw
      have h1 := hσ ⟨y, hyM⟩ hyw
      rw [nonunits_comap, map_sub, ← hτ] at h1
      exact h1
    have := hfix τ hcond
    apply (algebraMap M Ω).injective
    rw [← hτ]
    exact this
  obtain ⟨f, hf, hfx⟩ := (key_finite (K := K) O W hAW hctr ϖ hϖ ⟨x, hxM⟩ hfix' hxw).2
  refine ⟨f, hf, ?_⟩
  rw [nonunits_comap] at hfx
  convert hfx using 1
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  rfl

/-- **The residue extension of the inertia field is separable.** -/
theorem res_isSeparable (hw : w.comap (algebraMap K Ω) = O) :
    letI := (resMap (hE_eq w hw)).toAlgebra
    Algebra.IsSeparable (ResidueField O) (ResidueField (wE (K := K) w)) := by
  letI := (resMap (hE_eq w hw)).toAlgebra
  constructor
  intro r
  obtain ⟨a, rfl⟩ := residue_surjective r
  obtain ⟨f, hf, hfx⟩ := sep_poly w hw (ιΩ w a) a.1.2 a.2
  have h0 : aeval (residue _ a) (f.map (residue O)) = 0 := by
    rw [aeval_def, eval₂_map]
    have e1 : (algebraMap (ResidueField O) (ResidueField (wE (K := K) w))).comp (residue O) =
        (residue _).comp (comapHom (hE_eq w hw)) := by
      ext b; exact resMap_residue (hE_eq w hw) b
    rw [e1, ← hom_eval₂, residue_eq_zero_iff, mem_max_comap_iff]
    convert hfx using 1
    rw [Polynomial.eval_map]
    change ιΩ w _ = _
    rw [hom_eval₂]
    rfl
  exact hf.of_dvd (minpoly.dvd _ _ h0)

/-- The inertia field is separable over `K`. -/
theorem inertiaField_isSeparable : Algebra.IsSeparable K (inertiaField (K := K) w) :=
  isSeparable_of_forall _ (fun x hx => by
    obtain ⟨M, hM, hxM, -⟩ := hx
    exact hM.isSeparable hxM)

end ResSep

section Pair

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

/-- The elements of `Gal(M/K)` acting trivially modulo `𝔪_w` on `w ∩ M`, as a submonoid. -/
def inertSub (M : IntermediateField K Ω) : Submonoid (M ≃ₐ[K] M) where
  carrier := {σ | ∀ y : M, (y : Ω) ∈ w → ((σ y : M) : Ω) - y ∈ w.nonunits}
  one_mem' := by
    intro y _
    simp only [AlgEquiv.one_apply, sub_self]
    exact zero_mem _
  mul_mem' := by
    intro σ ρ hσ hρ y hy
    have h1 := hρ y hy
    have hρy : ((ρ y : M) : Ω) ∈ w := by
      have : ((ρ y : M) : Ω) = (y : Ω) + (((ρ y : M) : Ω) - y) := by ring
      rw [this]; exact add_mem hy (ValuationSubring.nonunits_le h1)
    have h2 := hσ (ρ y) hρy
    have : (((σ * ρ) y : M) : Ω) - y = (((σ (ρ y)) : M) : Ω) - (ρ y : M) +
        (((ρ y : M) : Ω) - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [this]
    exact add_mem h2 h1

/-- The inertia subgroup of `Gal(M/K)` (a submonoid of a finite group is a subgroup). -/
def inertM (M : IntermediateField K Ω) [FiniteDimensional K M] : Subgroup (M ≃ₐ[K] M) :=
  { inertSub w M with
    inv_mem' := by
      intro σ hσ
      have hn := orderOf_pos σ
      have h : σ⁻¹ = σ ^ (orderOf σ - 1) := by
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
      change σ⁻¹ ∈ inertSub w M
      rw [h]
      exact (inertSub w M).pow_mem hσ _ }

theorem mem_inertM {M : IntermediateField K Ω} [FiniteDimensional K M] {σ : M ≃ₐ[K] M} :
    σ ∈ inertM w M ↔ ∀ y : M, (y : Ω) ∈ w → ((σ y : M) : Ω) - y ∈ w.nonunits := Iff.rfl

/-- **`x^(q^n) ∈ F` and `x` separable over `F` imply `x ∈ F`.** -/
theorem mem_range_of_pow_mem {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
    {x : E} (hsep : IsSeparable F x) (n : ℕ) (h : x ^ q ^ n ∈ (algebraMap F E).range) :
    x ∈ (algebraMap F E).range := by
  haveI : Algebra.IsSeparable F F⟮x⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).2 hsep
  haveI : IsPurelyInseparable F F⟮x⟯ :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F E q).2 ⟨n, h⟩
  have hx' := IntermediateField.mem_adjoin_simple_self F x
  rw [IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable F⟮x⟯,
    IntermediateField.mem_bot] at hx'
  obtain ⟨y, hy⟩ := hx'
  exact ⟨y, hy⟩

variable [IsAlgClosure K Ω]
variable {K' : Type} [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra K' Ω]
  [IsScalarTower K K' Ω] [IsAlgClosure K' Ω]

/-- The inertia field over `K` lies in the inertia field over `K'`. -/
theorem inertiaField_le {x : Ω} (hx : x ∈ inertiaField (K := K) w) :
    x ∈ inertiaField (K := K') w := by
  obtain ⟨M, hMfg, hxM, hfix⟩ := hx
  haveI := hMfg.1
  obtain ⟨t, ht⟩ : M.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  haveI : FiniteDimensional K' (IntermediateField.adjoin K' (t : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => Algebra.IsIntegral.isIntegral z)
  have htM : ∀ z ∈ (t : Set Ω), z ∈ M := fun z hz => by
    rw [← ht]; exact IntermediateField.subset_adjoin K _ hz
  haveI : Algebra.IsSeparable K' (IntermediateField.adjoin K' (t : Set Ω)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K' Ω).mpr
      (fun z hz => (hMfg.isSeparable (htM z hz)).tower_top K')
  obtain ⟨M', hM', hNM'⟩ := isFG_of (K := K') (IntermediateField.adjoin K' (t : Set Ω))
  have hMM' : ∀ y ∈ M, y ∈ M' := by
    intro y hy
    rw [← ht] at hy
    have hle : IntermediateField.adjoin K (t : Set Ω) ≤ M'.restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr
        (fun z hz => hNM' (IntermediateField.subset_adjoin K' _ hz))
    exact hle hy
  exact ⟨M', hM', hMM' x hxM, fun τ hτ =>
    hfix (τ.restrictScalars K) (fun y hy hyw => hτ y (hMM' y hy) hyw)⟩

/-- **The inertia field over `K'` lies in `E(t')`** for `E` the inertia field over `K` and `t'` a
finite set generating `K'` over `K` (any characteristic: for `x` in the inertia field over `K'`, a
power `x^(p^n)` lies in a finite Galois extension of `K`, is fixed by the inertia subgroup fixing
`K' ∩ N`, hence lies in `E(t')`; and `x` is separable over `E(t') ⊇ K'`). -/
theorem inertiaField_le_adjoin (t' : Finset Ω)
    (ht' : IntermediateField.adjoin K (t' : Set Ω) = (IsScalarTower.toAlgHom K K' Ω).fieldRange)
    {x : Ω} (hx : x ∈ inertiaField (K := K') w) :
    x ∈ IntermediateField.adjoin (inertiaField (K := K) w) (t' : Set Ω) := by
  classical
  set E := inertiaField (K := K) w
  set L := IntermediateField.adjoin E (t' : Set Ω)
  obtain ⟨M', hM'fg, hxM', hfix'⟩ := hx
  haveI := hM'fg.1
  haveI := hM'fg.2
  haveI : FiniteDimensional K M' := FiniteDimensional.trans K K' M'
  haveI : FiniteDimensional K (M'.restrictScalars K) := inferInstanceAs (FiniteDimensional K M')
  set p := ringExpChar K
  haveI : ExpChar Ω p := expChar_of_injective_algebraMap (algebraMap K Ω).injective p
  -- the separable part of `M'` over `K`, and a finite Galois `N ⊇ S`
  let S : IntermediateField K Ω := M'.restrictScalars K ⊓ separableClosure K Ω
  haveI : FiniteDimensional K S :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : S ≤ _)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : S ≤ _)).injective
  haveI : Algebra.IsSeparable K S := (le_separableClosure_iff K Ω S).mp inf_le_right
  obtain ⟨N, hNfg, hSN⟩ := isFG_of S
  haveI := hNfg.1
  haveI := hNfg.2
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  haveI : ExpChar (separableClosure K Ω) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  have hpow : ∀ y ∈ M', ∃ n : ℕ, y ^ p ^ n ∈ N := by
    intro y hy
    obtain ⟨n, hn⟩ := (isPurelyInseparable_iff_pow_mem (separableClosure K Ω) p).mp
      inferInstance y
    refine ⟨n, hSN ⟨?_, ?_⟩⟩
    · exact pow_mem (show y ∈ M'.restrictScalars K from hy) _
    · obtain ⟨z, hz⟩ := hn
      rw [← hz]; exact z.2
  have frob_inj : ∀ (n : ℕ) (a b : Ω), a ^ p ^ n = b ^ p ^ n → a = b := fun n a b h =>
    iterateFrobenius_inj Ω p n (by rw [iterateFrobenius_def, iterateFrobenius_def]; exact h)
  let I := inertM w N
  let F := IntermediateField.fixedField I
  let K'Ω : IntermediateField K Ω := (IsScalarTower.toAlgHom K K' Ω).fieldRange
  let K'N : IntermediateField K N := K'Ω.comap N.val
  obtain ⟨n₀, hn₀⟩ := hpow x hxM'
  let x' : N := ⟨x ^ p ^ n₀, hn₀⟩
  have hx' : x' ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup (F ⊔ K'N)) := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField]
    rintro ⟨σ, hσI, hσK'⟩
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : N, τ (algebraMap N Ω m) = algebraMap N Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hτK' : ∀ c : K', τ (algebraMap K' Ω c) = algebraMap K' Ω c := by
      intro c
      obtain ⟨n, hn⟩ := hpow _ (M'.algebraMap_mem c)
      have hmem : (⟨_, hn⟩ : N) ∈ K'N := show algebraMap K' Ω c ^ p ^ n ∈ K'Ω from
        pow_mem (show algebraMap K' Ω c ∈ K'Ω from ⟨c, rfl⟩) (p ^ n)
      have h2 : σ ⟨_, hn⟩ = ⟨_, hn⟩ :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσK' _ hmem
      have h1 := hτ ⟨_, hn⟩
      rw [h2] at h1
      apply frob_inj n
      rw [← map_pow]; exact h1
    let τ' : Ω ≃ₐ[K'] Ω := { τ.toRingEquiv with commutes' := hτK' }
    have hcond : CondM w M' τ' := by
      intro y hy hyw
      obtain ⟨n, hn⟩ := hpow y hy
      have h1 := hσI ⟨_, hn⟩ (pow_mem hyw _)
      have h2 := hτ ⟨_, hn⟩
      change τ y - y ∈ w.nonunits
      have h3 : ((σ ⟨_, hn⟩ : N) : Ω) - y ^ p ^ n = (τ y - y) ^ p ^ n := by
        rw [sub_pow_expChar_pow, ← map_pow]
        exact congrArg (· - y ^ p ^ n) h2.symm
      rw [h3, ValuationSubring.mem_nonunits_iff, map_pow] at h1
      rw [ValuationSubring.mem_nonunits_iff]
      by_contra hc
      exact absurd h1 (not_lt.mpr (one_le_pow₀ (not_lt.mp hc)))
    have h3 : τ x = x := hfix' τ' hcond
    apply Subtype.ext
    change algebraMap N Ω (σ x') = algebraMap N Ω x'
    rw [← hτ]
    change τ (x ^ p ^ n₀) = x ^ p ^ n₀
    rw [map_pow, h3]
  rw [IsGalois.fixedField_fixingSubgroup] at hx'
  have hK'L : ∀ c : K', algebraMap K' Ω c ∈ L := fun c => by
    have h1 : algebraMap K' Ω c ∈ IntermediateField.adjoin K (t' : Set Ω) := by
      rw [ht']; exact ⟨c, rfl⟩
    have h2 : IntermediateField.adjoin K (t' : Set Ω) ≤ L.restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr (fun z hz => IntermediateField.subset_adjoin E _ hz)
    exact h2 h1
  have hle : F ⊔ K'N ≤ (L.restrictScalars K).comap N.val := by
    apply sup_le
    · intro f hf
      have hfE : (f : Ω) ∈ E := by
        refine ⟨N, hNfg, f.2, fun τ hτ => ?_⟩
        let σ : N ≃ₐ[K] N := τ.restrictNormal N
        have hσ : ∀ m : N, algebraMap N Ω (σ m) = τ (algebraMap N Ω m) := fun m =>
          AlgEquiv.restrictNormal_commutes τ N m
        have hσI : σ ∈ I := by
          intro y hyw
          change algebraMap N Ω (σ y) - y ∈ w.nonunits
          rw [hσ]
          exact hτ y y.2 hyw
        have := (IntermediateField.mem_fixedField_iff _ _).mp hf σ hσI
        change τ (algebraMap N Ω f) = algebraMap N Ω f
        rw [← hσ, this]
      exact L.algebraMap_mem ⟨_, hfE⟩
    · rintro m ⟨c, hc⟩
      change (m : Ω) ∈ L
      have : (m : Ω) = algebraMap K' Ω c := hc.symm
      rw [this]
      exact hK'L c
  have hxpow : x ^ p ^ n₀ ∈ L := hle hx'
  -- `x` is separable over `L ⊇ K'`
  have hsepK' : IsSeparable K' x := hM'fg.isSeparable hxM'
  have hsepL : IsSeparable L x := by
    obtain ⟨mL, hmL⟩ : (minpoly K' x).map (algebraMap K' Ω) ∈ Polynomial.lifts (algebraMap L Ω) :=
      (lifts_iff_coeff_lifts _).mpr (fun n => ⟨⟨((minpoly K' x).map (algebraMap K' Ω)).coeff n,
        by rw [coeff_map]; exact hK'L _⟩, rfl⟩)
    have hmL' : mL.map (algebraMap L Ω) = (minpoly K' x).map (algebraMap K' Ω) := hmL
    have hsepm : mL.Separable := by
      rw [← Polynomial.separable_map (algebraMap L Ω), hmL', Polynomial.separable_map]
      exact hsepK'
    have h0 : aeval x mL = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, hmL', eval_map, ← aeval_def, minpoly.aeval]
    exact hsepm.of_dvd (minpoly.dvd L x h0)
  haveI : ExpChar L p := (algebraMap L Ω).expChar (algebraMap L Ω).injective p
  obtain ⟨y, hy⟩ := mem_range_of_pow_mem p hsepL n₀ ⟨⟨_, hxpow⟩, rfl⟩
  rw [← hy]; exact y.2

end Pair

end GapSHPair


-- ===== part GTFinal =====

/-!
# gt-shpair, final part: `ReductGlue.StrictHenselizationPair` from one Néron leaf
-/

open IsLocalRing

set_option linter.style.haveILetI false

namespace GapSHPair

open ReductSplit ReductGlue

/-- `O₁ ⊇ O` is an unramified strictly henselian extension with `K₁/K` separable: `O₁` is a
strictly henselian DVR, `K₁/K` is separable algebraic, a uniformizer of `O` stays a uniformizer of
`O₁` (ramification index 1), and `κ(O₁)/κ(O)` is separable. In every characteristic these conditions
characterize `O → O₁` as the strict henselization of `O` up to isomorphism over `O` (report §2; no excellence
hypothesis is needed, since a finite separable extension of a henselian discretely valued field is defectless:
`O^sh` is noetherian and normal, so the integral closure is finite free and `[L : K^sh] = e f = 1`). -/
def IsSHSep {K K₁ : Type} [Field K] [Field K₁] [Algebra K K₁] (O : ValuationSubring K)
    (O₁ : ValuationSubring K₁) (hO : O₁.comap (algebraMap K K₁) = O) : Prop :=
  IsStrictlyHenselianDVR O₁ ∧ Algebra.IsSeparable K K₁ ∧
    (∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) ∧
    (letI := (resMap hO).toAlgebra
     Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O₁))

/-- **LEAF `NeronBaseChangeStrictHenselization`** (Néron models commute with strict
henselization: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 2 (and §7.2 Thm. 1);
numbers UNVERIFIED). `O ⊆ K` a DVR (any characteristic, any residue field) and `O₁ ⊇ O` an
unramified strictly henselian extension with `K₁/K` separable (`IsSHSep`, which pins `O₁` as the
strict henselization `O^sh` up to isomorphism over `O`, report §2); then the base change of a Néron
model of `A` over `O` is a Néron model of `A_{K₁}` over `O₁`. It is a specialization of the chain's
`ReductGlue.NeronBaseChangeUnramifiedDVR` (`neronBaseChangeStrictHenselization_of_unramified`). -/
def NeronBaseChangeStrictHenselization : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K₁ : Type) [Field K₁] [Algebra K K₁] (O₁ : ValuationSubring K₁)
    (hO : O₁.comap (algebraMap K K₁) = O), IsSHSep O O₁ hO →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

/-- The new leaf is a specialization of the chain's `NeronBaseChangeUnramifiedDVR`. -/
theorem neronBaseChangeStrictHenselization_of_unramified (h : NeronBaseChangeUnramifiedDVR) :
    NeronBaseChangeStrictHenselization := by
  intro K _ O _ K₁ _ _ O₁ hO hS
  haveI : IsDiscreteValuationRing O₁ := hS.1.1
  exact h K O K₁ O₁ hO hS.2.1 hS.2.2.1 hS.2.2.2

theorem isSHNeronExt_of (hN : NeronBaseChangeStrictHenselization) {K K₁ : Type} [Field K]
    [Field K₁] [Algebra K K₁] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {O₁ : ValuationSubring K₁} {hO : O₁.comap (algebraMap K K₁) = O} (h : IsSHSep O O₁ hO) :
    IsSHNeronExt O O₁ hO := by
  refine ⟨h.1, ?_, hN K O K₁ O₁ hO h⟩
  letI := (resMap hO).toAlgebra
  have := h.2.2.2
  exact Algebra.IsSeparable.isAlgebraic _ _

/-- **The valuation ring of the inertia field is an unramified strictly henselian extension.** -/
theorem isSHSep_inertia {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) : IsSHSep O (wE (K := K) w) (hE_eq w hw) :=
  ⟨⟨isDVR_wE w hw, henselian_wE w, isSepClosed_wE w⟩, inertiaField_isSeparable w,
    fun ϖ hϖ => irreducible_comapHom w hw ϖ hϖ, res_isSeparable w hw⟩

/-- **Extension of a valuation ring to an extension field** (Chevalley; via Mathlib's
`IsLocalRing.exists_factor_valuationRing`). -/
theorem exists_comap_eq {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (O : ValuationSubring K) :
    ∃ w : ValuationSubring Ω, w.comap (algebraMap K Ω) = O := by
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing ((algebraMap K Ω).comp O.subtype)
  refine ⟨B, le_antisymm ?_ (fun x hx => hB ⟨x, hx⟩)⟩
  intro x hx
  by_contra hxO
  have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
  have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
  have hunit : IsUnit (((algebraMap K Ω).comp O.subtype).codRestrict B.toSubring hB ⟨x⁻¹, hinv⟩) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K Ω x, hx⟩, Subtype.ext ?_⟩
    change algebraMap K Ω x⁻¹ * algebraMap K Ω x = 1
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨u, hu⟩ := hloc.map_nonunit _ hunit
  apply hxO
  have h1 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 :=
    congrArg (fun z : O => (z : K)) (Units.mul_inv u)
  rw [hu] at h1
  change x⁻¹ * _ = 1 at h1
  have : (((u⁻¹ : Oˣ) : O) : K) = x := by
    rw [← inv_inv x]; exact (eq_inv_of_mul_eq_one_right h1)
  rw [← this]; exact (u⁻¹ : Oˣ).1.2

/-- **Strict henselizations along a finite extension (commutative algebra, any characteristic, any
residue field).** For `O' ⊆ K'` over `O ⊆ K` with `K'/K` finite there are unramified strictly
henselian extensions `P ⊇ O`, `P' ⊇ O'` with separable fraction field extensions (`IsSHSep`), `E'/E`
finite and `P'` over `P`: the inertia fields of one valuation ring `w` of `K̄'` over `O'`, over `K`
and over `K'`. -/
theorem shPair (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) :
    ∃ (E E' : Type) (_ : Field E) (_ : Field E') (_ : Algebra K E) (_ : Algebra K' E')
      (_ : Algebra E E') (_ : Algebra K E') (_ : IsScalarTower K E E') (_ : IsScalarTower K K' E')
      (_ : FiniteDimensional E E') (P : ValuationSubring E) (P' : ValuationSubring E')
      (hP : P.comap (algebraMap K E) = O) (hP' : P'.comap (algebraMap K' E') = O'),
      IsSHSep O P hP ∧ IsSHSep O' P' hP' ∧ P'.comap (algebraMap E E') = P := by
  let Ω := AlgebraicClosure K'
  haveI : IsScalarTower K K' Ω := inferInstance
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed K', Algebra.IsAlgebraic.trans K K' Ω⟩
  obtain ⟨w, hw'⟩ := exists_comap_eq (Ω := Ω) O'
  have hw : w.comap (algebraMap K Ω) = O := by
    rw [IsScalarTower.algebraMap_eq K K' Ω, ← ValuationSubring.comap_comap, hw', hO]
  let E := inertiaField (K := K) w
  let E' := inertiaField (K := K') w
  let φ : E →+* E' :=
    { toFun := fun e => ⟨e, inertiaField_le w e.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra E E' := φ.toAlgebra
  haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq (fun c => by
    apply Subtype.ext
    change algebraMap K Ω c = algebraMap E' Ω (algebraMap K E' c)
    rw [IsScalarTower.algebraMap_apply K K' E', IsScalarTower.algebraMap_apply K K' Ω]
    rfl)
  -- finiteness of `E'/E`
  let f := IsScalarTower.toAlgHom K K' Ω
  haveI : FiniteDimensional K f.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField f).toLinearEquiv
  obtain ⟨t', ht'⟩ : f.fieldRange.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  let L := IntermediateField.adjoin E (t' : Set Ω)
  haveI : FiniteDimensional E L := IntermediateField.finiteDimensional_adjoin
    (fun z _ => (Algebra.IsIntegral.isIntegral (R := K) z).tower_top)
  let ψ : E' →ₗ[E] L :=
    { toFun := fun x => ⟨x, inertiaField_le_adjoin w t' ht' x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b h =>
    Subtype.ext (congrArg (fun z : L => (z : Ω)) h)
  haveI : FiniteDimensional E E' := Module.Finite.of_injective ψ hψ
  exact ⟨E, E', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, wE (K := K) w, wE (K := K') w,
    hE_eq w hw, hE_eq w hw', isSHSep_inertia w hw, isSHSep_inertia w hw', rfl⟩

/-- **`ReductGlue.StrictHenselizationPair` from the single Néron leaf** (the commutative algebra
is proved above, in every characteristic and for every residue field). -/
theorem strictHenselizationPair_of_neron (hN : NeronBaseChangeStrictHenselization) :
    StrictHenselizationPair := by
  intro K _ O _ K' _ _ _ O' _ hO
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', h1, h2, h3⟩ := shPair K O K' O' hO
  exact ⟨E, E', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, P, P', hP, hP',
    isSHNeronExt_of hN h1, isSHNeronExt_of hN h2, h3⟩

/-- The same from the chain's `NeronBaseChangeUnramifiedDVR`. -/
theorem strictHenselizationPair_of_unramified (hN : NeronBaseChangeUnramifiedDVR) :
    StrictHenselizationPair :=
  strictHenselizationPair_of_neron (neronBaseChangeStrictHenselization_of_unramified hN)

end GapSHPair


