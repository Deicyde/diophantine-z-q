import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.StageInputs
import ZInQKernel.Contrib.RC53Assist.ResidualFiniteness.StageResidual
import ZInQKernel.Contrib.RC53Assist.CentralUniversal.CentralComparison
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Iota
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Selmer
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso

/-!
# Finiteness of compact Kummer cohomology and of finite-level Selmer cohomology

The finiteness input `KummerCohomologyFinite` of the central comparison, and finiteness of the
cohomology of the finite-level and stage Selmer complexes.

## The printed inputs

The only inputs are the finiteness prints of the inner-limit stage inputs, used as they are
stated there (`MilneLocalFiniteness`, `MilneGlobalFiniteness`):

* `MilneLocalFiniteness` — Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorem 2.1, last
  sentence of the statement (p. 27): `H^r(K_v, M)` is finite for every finite discrete
  `G_{K_v}`-module `M` and every `r`.
* `MilneGlobalFiniteness` — Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Corollary 4.15
  (p. 62): for `S` finite and `M` a finite `G_{K,S}`-module whose order is a unit in `R_{K,S}`, the
  groups `H^r(G_{K,S}, M)` are finite for every `r`.

They appear as explicit hypotheses; nothing else is assumed.

## Two-adic finite generation

* `moduleFinite_subquot_of_residual`: for a complex of `ℤ₂`-modules with two-adically complete
  and separated terms, finiteness of its cohomology modulo every `2^k` (`TwoPowResidualFinite`)
  gives finite generation of its cohomology (Kőnig's lemma for the Mittag-Leffler step
  `exists_eq_of_forall_two_pow`, and complete Nakayama `moduleFinite_of_two_adic`).
* `IsTwoAdicLimit`, `moduleFinite_homology_of_twoAdicLimit`: the continuous cochains with values in
  a two-adic limit `T = lim L_k` of discrete modules are the inverse limit of the continuous
  cochains with values in the levels `L_k` (the reduction `red` is surjective with kernel `2^k`, and
  the cochains are two-adically complete and separated), so finiteness of every `Hⁿ(G, L_k)` gives
  finite generation of every `Hⁿ(G, T)` over `ℤ₂`.
* `moduleFinite_globalTateCohomology`, `moduleFinite_localTateCohomology`: `Hⁿ(G_{K,S}, T_2E)` and
  `Hⁿ(G_{K_v}, T_2E)` are finitely generated over `ℤ₂` (`T_2E = lim E(K_S)[2^k]`).

## Compact Kummer cohomology

* `moduleFinite_compactKummer_homology`: every cohomology group of the compact Kummer complex
  `compactKummerComplex S W hFull` is a finitely generated `ℤ₂`-module, by the exact sequences of
  the Selmer cone over the noetherian ring `ℤ₂` (`moduleFinite_homology_selCx`), with the Kummer
  condition controlled in every degree (`moduleFinite_tateKummerCondition_homology`).
* `kummerCohomologyFinite_of_prints`, `kummerCohomologyFinite_of_comparison`: the input
  `KummerCohomologyFinite` of the universal-coefficient construction, for the genuine complex;
  `centralSelmerComparisonOfPrints`, `hcentral_of_prints`: the central comparison with that input
  discharged.

## Finite-level and stage Selmer cohomology

* `finite_galoisSelmer_homology`, `moduleFinite_galoisSelmer_homology`: every cohomology group of a
  finite-level Galois Selmer complex is finite, hence finitely generated over the coefficient ring
  (the stage input `galoisSelmerCohomologyFinite_of_prints`, read degreewise);
  `moduleFinite_stageSelmer_homology` over `A_i` for the actual stage modules `M_i`.
* `finite_actualSelData_homology`, `moduleFinite_actualSelData_homology`,
  `finite_kummerSelData_homology`: the actual stage complexes and the finite-level Kummer Selmer
  complexes; `finite_cocycleCondition_homology`, `finite_kummerAt_homology`,
  `finite_urAt_homology`, `finite_zeroAt_homology`, `finite_strictConditions_homology` for the
  local conditions.
* Residual cohomology: `residualCohomologyFinite_kummerSelData`, the finite-level Kummer Selmer
  complexes, from the residual finiteness of the actual stage complexes of the stage residual
  file (`actualStageSelmer_residualCohomologyFinite`, `residualCohomologyFinite_cocycleCondition`).

All statements are proved from the two printed inputs.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Finiteness

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.ResidualFiniteness (finite_homology_of_finite_X finite_frobCx_X
  finite_cocycleCondition_X finite_subquot_one_of_homology
  actualStageSelmer_residualCohomologyFinite residualCohomologyFinite_cocycleCondition)

/-! ### Kőnig's lemma along `ℕ` -/

/-- **Kőnig's lemma along `ℕ`**: an inverse sequence of nonempty finite types has a compatible
sequence of elements. -/
theorem exists_compatible_seq.{u} {Q : ℕ → Type u} [hfin : ∀ k, Finite (Q k)]
    [hne : ∀ k, Nonempty (Q k)] (π : ∀ k, Q (k + 1) → Q k) :
    ∃ q : ∀ k, Q k, ∀ k, π k (q (k + 1)) = q k := by
  let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence (X := Q) (fun k => TypeCat.ofHom (π k))
  have h1 : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => hfin j.unop
  have h2 : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => hne j.unop
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun k => s (Opposite.op k), fun k => ?_⟩
  have h := hs (homOfLE (Nat.le_add_right k 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h

/-! ### Completeness of `ℤ₂` -/

/-- Membership in `𝔪^m ℤ₂` is divisibility by `2^m`. -/
theorem mem_maximalIdeal_pow_smul_top_iff (x : ℤ_[2]) (m : ℕ) :
    x ∈ ((IsLocalRing.maximalIdeal ℤ_[2]) ^ m • ⊤ : Submodule ℤ_[2] ℤ_[2]) ↔
      ∃ e : ℤ_[2], x = (2 : ℤ_[2]) ^ m * e := by
  rw [← Ideal.one_eq_top, smul_eq_mul, mul_one, PadicInt.maximalIdeal_eq_span_p,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by push_cast; ring⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, by push_cast; ring⟩

/-- **Two-adic limits in `ℤ₂`**: a sequence with `γ (k + 1) ≡ γ k mod 2^k` converges, with
`γ∞ ≡ γ k mod 2^k` for every `k`. -/
theorem exists_padicInt_two_limit (γ : ℕ → ℤ_[2])
    (hγ : ∀ k, ∃ e : ℤ_[2], γ (k + 1) - γ k = (2 : ℤ_[2]) ^ k * e) :
    ∃ L : ℤ_[2], ∀ k, ∃ e : ℤ_[2], L - γ k = (2 : ℤ_[2]) ^ k * e := by
  have hstep : ∀ m j, ∃ e : ℤ_[2], γ (m + j) - γ m = (2 : ℤ_[2]) ^ m * e := by
    intro m j
    induction j with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      obtain ⟨e, he⟩ := ih
      obtain ⟨e', he'⟩ := hγ (m + j)
      refine ⟨e + 2 ^ j * e', ?_⟩
      have h1 : γ (m + (j + 1)) - γ m = (γ (m + j + 1) - γ (m + j)) + (γ (m + j) - γ m) := by
        rw [show m + (j + 1) = m + j + 1 by omega]; ring
      rw [h1, he, he', pow_add]; ring
  have hprec :=
    (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[2]) ℤ_[2]).toIsPrecomplete
  obtain ⟨L, hL⟩ := hprec.prec (f := γ) (by
    intro m n hmn
    rw [SModEq.sub_mem, mem_maximalIdeal_pow_smul_top_iff]
    obtain ⟨e, he⟩ := hstep m (n - m)
    rw [show m + (n - m) = n by omega] at he
    exact ⟨-e, by rw [mul_neg, ← he]; ring⟩)
  refine ⟨L, fun k => ?_⟩
  have h := hL k
  rw [SModEq.sub_mem, mem_maximalIdeal_pow_smul_top_iff] at h
  obtain ⟨e, he⟩ := h
  exact ⟨-e, by rw [mul_neg, ← he]; ring⟩

/-! ### Finite generation from a finite residual quotient and separatedness -/

/-- **Complete Nakayama over `ℤ₂`.** A `ℤ₂`-module `M` in which every element is a combination of
finitely many fixed elements modulo `2M`, and which is `2`-adically separated, is finitely
generated. -/
theorem moduleFinite_of_two_adic {M : Type*} [AddCommGroup M] [Module ℤ_[2] M]
    {ι : Type*} [Fintype ι] (e : ι → M)
    (hgen : ∀ m : M, ∃ (c : ι → ℤ_[2]) (m' : M), m = ∑ i, c i • e i + (2 : ℤ_[2]) • m')
    (hsep : ∀ m : M, (∀ k : ℕ, ∃ m' : M, m = (2 : ℤ_[2]) ^ k • m') → m = 0) :
    Module.Finite ℤ_[2] M := by
  choose c r hcr using hgen
  have hspan : ∀ m : M, m ∈ Submodule.span ℤ_[2] (Set.range e) := by
    intro m
    -- the successive remainders
    let ms : ℕ → M := fun j => Nat.rec m (fun _ x => r x) j
    have hms0 : ms 0 = m := rfl
    have hmsS : ∀ j, ms (j + 1) = r (ms j) := fun j => rfl
    let γ : ℕ → ι → ℤ_[2] := fun k i => ∑ j ∈ Finset.range k, (2 : ℤ_[2]) ^ j * c (ms j) i
    have hexp : ∀ k, m = ∑ i, γ k i • e i + (2 : ℤ_[2]) ^ k • ms k := by
      intro k
      induction k with
      | zero => simp [γ, hms0]
      | succ k ih =>
        rw [ih]
        have h := hcr (ms k)
        conv_lhs => rw [h]
        rw [hmsS, smul_add, smul_smul, ← pow_succ, Finset.smul_sum]
        simp only [γ, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, smul_smul]
        abel
    have hlim : ∀ i, ∃ L : ℤ_[2], ∀ k, ∃ x : ℤ_[2], L - γ k i = (2 : ℤ_[2]) ^ k * x := by
      intro i
      refine exists_padicInt_two_limit (fun k => γ k i) (fun k => ⟨c (ms k) i, ?_⟩)
      simp only [γ, Finset.sum_range_succ]
      ring
    choose L x hLx using hlim
    have hzero : m - ∑ i, L i • e i = 0 := by
      refine hsep _ (fun k => ⟨ms k - ∑ i, x i k • e i, ?_⟩)
      have hL : ∀ i, L i = γ k i + (2 : ℤ_[2]) ^ k * x i k := fun i => by
        rw [← hLx i k]; ring
      conv_lhs => rw [hexp k]
      simp only [hL, add_smul, Finset.sum_add_distrib, smul_sub, Finset.smul_sum, smul_smul]
      abel
    rw [sub_eq_zero] at hzero
    rw [hzero]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Submodule.fg_def.mpr ⟨Set.range e, Set.finite_range e, ?_⟩⟩
  exact top_unique fun m _ => hspan m

/-! ### Residual finiteness and the separatedness of cohomology -/

section ResidualTwoAdic

variable {X Y Z : Type*} [AddCommGroup X] [Module ℤ_[2] X] [AddCommGroup Y] [Module ℤ_[2] Y]
  [AddCommGroup Z] [Module ℤ_[2] Z]

/-- **Residual finiteness at level `2^k`** of the middle term of `X --dIn--> Y --dOut--> Z`: the
elements `y` with `dOut y ≡ 0 mod 2^k` fall into finitely many classes modulo
`2^k Y + dIn X`. This is the finiteness of the cohomology of the complex reduced modulo `2^k`
(at the middle term), expressed without forming the reduced complex. -/
def TwoPowResidualFinite (dIn : X →ₗ[ℤ_[2]] Y) (dOut : Y →ₗ[ℤ_[2]] Z) (k : ℕ) : Prop :=
  ∃ (F : Type) (_ : Finite F) (φ : Y → F), ∀ y y' : Y,
    (∃ z : Z, dOut y = (2 : ℤ_[2]) ^ k • z) → (∃ z : Z, dOut y' = (2 : ℤ_[2]) ^ k • z) →
      φ y = φ y' → ∃ (b : Y) (a : X), y - y' = (2 : ℤ_[2]) ^ k • b + dIn a

end ResidualTwoAdic

section Separated

variable {P A B : Type*} [AddCommGroup P] [Module ℤ_[2] P] [AddCommGroup A] [Module ℤ_[2] A]
  [AddCommGroup B] [Module ℤ_[2] B]

/-- **Separatedness of cohomology (the Mittag-Leffler step).** For `P --d0--> A --d1--> B` with
`d1 ∘ d0 = 0`, `A` two-adically complete, `B` two-adically separated and every residual
quotient of `A` finite, an element of `B` that is a coboundary modulo `2^k B` for every `k` is a
coboundary. -/
theorem exists_eq_of_forall_two_pow (d0 : P →ₗ[ℤ_[2]] A) (d1 : A →ₗ[ℤ_[2]] B)
    (h01 : ∀ p, d1 (d0 p) = 0)
    (hHaus : ∀ b : B, (∀ k : ℕ, ∃ b' : B, b = (2 : ℤ_[2]) ^ k • b') → b = 0)
    (hComp : ∀ s : ℕ → A, (∀ k, ∃ a : A, s (k + 1) - s k = (2 : ℤ_[2]) ^ k • a) →
      ∃ s' : A, ∀ k, ∃ a : A, s' - s k = (2 : ℤ_[2]) ^ k • a)
    (hres : ∀ k, TwoPowResidualFinite d0 d1 k)
    (z : B) (hz : ∀ k : ℕ, ∃ (y : B) (w : A), z - d1 w = (2 : ℤ_[2]) ^ k • y) :
    ∃ w : A, d1 w = z := by
  classical
  -- the approximate primitives at level `k`
  let T : ℕ → Type _ := fun k => {w : A // ∃ y : B, z - d1 w = (2 : ℤ_[2]) ^ k • y}
  let rel : ∀ k, T k → T k → Prop := fun k w w' =>
    ∃ (a : A) (p : P), w.1 - w'.1 = (2 : ℤ_[2]) ^ k • a + d0 p
  have hequiv : ∀ k, Equivalence (rel k) := fun k =>
    { refl := fun w => ⟨0, 0, by simp⟩
      symm := fun {w w'} ⟨a, p, h⟩ => ⟨-a, -p, by
        rw [smul_neg, map_neg, ← neg_add, ← h, neg_sub]⟩
      trans := fun {w w' w''} ⟨a, p, h⟩ ⟨a', p', h'⟩ => ⟨a + a', p + p', by
        rw [smul_add, map_add, show w.1 - w''.1 = (w.1 - w'.1) + (w'.1 - w''.1) by abel, h, h']
        abel⟩ }
  let st : ∀ k, Setoid (T k) := fun k => ⟨rel k, hequiv k⟩
  let Q : ℕ → Type _ := fun k => Quotient (st k)
  have hne : ∀ k, Nonempty (Q k) := fun k => by
    obtain ⟨y, w, h⟩ := hz k
    exact ⟨Quotient.mk (st k) ⟨w, y, h⟩⟩
  have hfin : ∀ k, Finite (Q k) := by
    intro k
    obtain ⟨y₀, w₀, h₀⟩ := hz k
    obtain ⟨F, hF, φ, hφ⟩ := hres k
    let ψ : T k → F := fun w => φ (w.1 - w₀)
    have hψ : ∀ w w' : T k, ψ w = ψ w' → rel k w w' := by
      intro w w' hww'
      obtain ⟨y, hy⟩ := w.2
      obtain ⟨y', hy'⟩ := w'.2
      obtain ⟨b, a, hba⟩ := hφ (w.1 - w₀) (w'.1 - w₀)
        ⟨y₀ - y, by rw [map_sub, smul_sub, ← hy, ← h₀]; abel⟩
        ⟨y₀ - y', by rw [map_sub, smul_sub, ← hy', ← h₀]; abel⟩ hww'
      exact ⟨b, a, by rw [← hba]; abel⟩
    let g : {f : F // ∃ w : T k, ψ w = f} → Q k := fun f => Quotient.mk (st k) f.2.choose
    have hg : Function.Surjective g := by
      intro q
      induction q using Quotient.inductionOn with
      | h w =>
        refine ⟨⟨ψ w, w, rfl⟩, Quotient.sound ?_⟩
        exact hψ _ _ (⟨ψ w, w, rfl⟩ : {f : F // ∃ w : T k, ψ w = f}).2.choose_spec
    exact Finite.of_surjective g hg
  -- the transition maps
  let incl : ∀ k, T (k + 1) → T k := fun k w => ⟨w.1, by
    obtain ⟨y, hy⟩ := w.2
    exact ⟨(2 : ℤ_[2]) • y, by rw [hy, smul_smul, ← pow_succ]⟩⟩
  have hincl : ∀ k (w w' : T (k + 1)), rel (k + 1) w w' → rel k (incl k w) (incl k w') := by
    rintro k w w' ⟨a, p, h⟩
    exact ⟨(2 : ℤ_[2]) • a, p, by rw [smul_smul, ← pow_succ]; exact h⟩
  let π : ∀ k, Q (k + 1) → Q k := fun k =>
    Quotient.map (incl k) (fun w w' h => hincl k w w' h)
  obtain ⟨q, hq⟩ := @exists_compatible_seq Q hfin hne π
  -- representatives and their corrections by coboundaries
  let r : ∀ k, T k := fun k => (q k).out
  have hr : ∀ k, rel k (incl k (r (k + 1))) (r k) := by
    intro k
    have h1 : π k (q (k + 1)) = q k := hq k
    have h2 : π k (Quotient.mk (st (k + 1)) (r (k + 1))) = Quotient.mk (st k) (r k) := by
      simp only [r]
      rw [Quotient.out_eq, Quotient.out_eq]
      exact h1
    exact Quotient.exact h2
  choose a p hap using hr
  let s : ℕ → A := fun k => (r k).1 - d0 (∑ j ∈ Finset.range k, p j)
  have hs : ∀ k, ∃ a' : A, s (k + 1) - s k = (2 : ℤ_[2]) ^ k • a' := by
    intro k
    refine ⟨a k, ?_⟩
    have h := hap k
    simp only [s, Finset.sum_range_succ, map_add]
    change (r (k + 1)).1 - (r k).1 = _ at h
    rw [show (r (k + 1)).1 - (d0 (∑ j ∈ Finset.range k, p j) + d0 (p k)) -
        ((r k).1 - d0 (∑ j ∈ Finset.range k, p j)) = ((r (k + 1)).1 - (r k).1) - d0 (p k) by
      abel, h]
    abel
  obtain ⟨s', hs'⟩ := hComp s hs
  refine ⟨s', ?_⟩
  have hzero : z - d1 s' = 0 := by
    refine hHaus _ (fun k => ?_)
    obtain ⟨e, he⟩ := hs' k
    obtain ⟨y, hy⟩ := (r k).2
    refine ⟨y - d1 e, ?_⟩
    have hs'k : s' = s k + (2 : ℤ_[2]) ^ k • e := by rw [← he]; abel
    rw [hs'k, map_add, map_smul]
    simp only [s, map_sub, h01, sub_zero]
    rw [smul_sub, ← hy]
    abel
  exact (sub_eq_zero.mp hzero).symm

end Separated

/-! ### Finite generation of cohomology -/

section Main

variable {P A B C : Type} [AddCommGroup P] [Module ℤ_[2] P] [AddCommGroup A] [Module ℤ_[2] A]
  [AddCommGroup B] [Module ℤ_[2] B] [AddCommGroup C] [Module ℤ_[2] C]

/-- **Finite generation of cohomology from residual finiteness.** For
`P --d0--> A --d1--> B --d2--> C` with `d1 ∘ d0 = 0` and `d2 ∘ d1 = 0`, if `C` has no
`2`-torsion, `B` is two-adically separated, `A` is two-adically complete, the residual quotient
of `B` modulo `2` is finite and the residual quotients of `A` modulo every `2^k` are finite, then
the cohomology `ker d2 / im d1` is a finitely generated `ℤ₂`-module. -/
theorem moduleFinite_subquot_of_residual (d0 : P →ₗ[ℤ_[2]] A) (d1 : A →ₗ[ℤ_[2]] B)
    (d2 : B →ₗ[ℤ_[2]] C) (h01 : ∀ p, d1 (d0 p) = 0) (h12 : ∀ a, d2 (d1 a) = 0)
    (hT : ∀ c : C, (2 : ℤ_[2]) • c = 0 → c = 0)
    (hHaus : ∀ b : B, (∀ k : ℕ, ∃ b' : B, b = (2 : ℤ_[2]) ^ k • b') → b = 0)
    (hComp : ∀ s : ℕ → A, (∀ k, ∃ a : A, s (k + 1) - s k = (2 : ℤ_[2]) ^ k • a) →
      ∃ s' : A, ∀ k, ∃ a : A, s' - s k = (2 : ℤ_[2]) ^ k • a)
    (hres1 : TwoPowResidualFinite d1 d2 1) (hres0 : ∀ k, TwoPowResidualFinite d0 d1 k) :
    Module.Finite ℤ_[2] (subquot (LinearMap.range d1) (LinearMap.ker d2)) := by
  classical
  obtain ⟨F, hF, φ, hφ⟩ := hres1
  have : Fintype F := Fintype.ofFinite F
  let rep : F → LinearMap.ker d2 := fun f =>
    if h : ∃ z : LinearMap.ker d2, φ z = f then h.choose else 0
  have hrep : ∀ z : LinearMap.ker d2, φ (rep (φ z) : B) = φ z := by
    intro z
    have h : ∃ z' : LinearMap.ker d2, φ z' = φ z := ⟨z, rfl⟩
    simp only [rep, h, dite_true]
    exact h.choose_spec
  let e : F → subquot (LinearMap.range d1) (LinearMap.ker d2) := fun f =>
    Submodule.Quotient.mk (rep f)
  refine moduleFinite_of_two_adic e ?_ ?_
  · intro m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hz : d2 (z : B) = 0 := z.2
    have hr : d2 (rep (φ z) : B) = 0 := (rep (φ z)).2
    obtain ⟨b, a, hba⟩ := hφ (z : B) (rep (φ z) : B) ⟨0, by rw [hz, smul_zero]⟩
      ⟨0, by rw [hr, smul_zero]⟩ (hrep z).symm
    rw [pow_one] at hba
    have hb : d2 b = 0 := by
      apply hT
      rw [← map_smul, show (2 : ℤ_[2]) • b = (z : B) - (rep (φ z) : B) - d1 a by
        rw [hba]; abel, map_sub, map_sub, hz, hr, h12, sub_zero, sub_zero]
    refine ⟨Pi.single (φ z) 1, Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, e]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    refine ⟨a, ?_⟩
    change d1 a = (z : B) - ((rep (φ z) : B) + (2 : ℤ_[2]) • b)
    rw [show (z : B) - ((rep (φ z) : B) + (2 : ℤ_[2]) • b) =
      ((z : B) - (rep (φ z) : B)) - (2 : ℤ_[2]) • b by abel, hba]
    abel
  · intro m hm
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hz : ∀ k : ℕ, ∃ (y : B) (w : A), (z : B) - d1 w = (2 : ℤ_[2]) ^ k • y := by
      intro k
      obtain ⟨m', hm'⟩ := hm k
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m'
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hm'
      obtain ⟨w, hw⟩ := hm'
      refine ⟨y, w, ?_⟩
      change d1 w = (z : B) - (2 : ℤ_[2]) ^ k • (y : B) at hw
      rw [hw]
      abel
    obtain ⟨w, hw⟩ := exists_eq_of_forall_two_pow d0 d1 h01 hHaus hComp hres0 (z : B) hz
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨w, hw⟩

end Main

section Subquot

variable {R : Type} [CommRing R]

theorem moduleFinite_subquot_congr {X : Type} [AddCommGroup X] [Module R X]
    {B B' K K' : Submodule R X} (hB : B = B') (hK : K = K') :
    Module.Finite R (subquot B K) ↔ Module.Finite R (subquot B' K') := by
  subst hB hK
  rfl

/-- The homology of a short complex of modules is its cycles modulo its boundaries. -/
def shortComplexHomologyEquiv (S : ShortComplex (ModuleCat.{0} R)) :
    S.homology ≃ₗ[R] subquot (LinearMap.range S.f.hom) (LinearMap.ker S.g.hom) :=
  S.moduleCatHomologyIso.toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _))

theorem prev_up_int {i m : ℤ} (hi : i + 1 = m) : (ComplexShape.up ℤ).prev m = i :=
  (CochainComplex.prev ℤ m).trans (by omega)

theorem next_up_int {m j : ℤ} (hj : m + 1 = j) : (ComplexShape.up ℤ).next m = j :=
  (CochainComplex.next ℤ m).trans (by omega)

/-- The cohomology of a relation-indexed complex in degree `m` is its `m`-cocycles modulo
`m`-coboundaries, linearly (for any names `i`, `j` of the neighbouring degrees). -/
def gcxHomologyEquiv (C : GCx R) (i m j : ℤ) (hi : i + 1 = m) (hj : m + 1 = j) :
    C.toCC.homology m ≃ₗ[R] subquot (LinearMap.range (C.toCC.sc' i m j).f.hom)
      (LinearMap.ker (C.toCC.sc' i m j).g.hom) :=
  (C.toCC.homologyIsoSc' i m j (prev_up_int hi) (next_up_int hj)).toLinearEquiv.trans
    (shortComplexHomologyEquiv (C.toCC.sc' i m j))

theorem sc'_f_hom (C : GCx R) (i m j : ℤ) (hi : i + 1 = m) :
    (C.toCC.sc' i m j).f.hom = C.d i m hi :=
  LinearMap.ext fun x => GCx.toCC_d_hom C i m hi x

theorem sc'_g_hom (C : GCx R) (i m j : ℤ) (hj : m + 1 = j) :
    (C.toCC.sc' i m j).g.hom = C.d m j hj :=
  LinearMap.ext fun x => GCx.toCC_d_hom C m j hj x

/-- **The cohomology of a relation-indexed complex in degree `m` is finitely generated exactly
when its `m`-cocycles modulo `m`-coboundaries are.** -/
theorem moduleFinite_gcx_homology_iff' (C : GCx R) (i m j : ℤ) (hi : i + 1 = m)
    (hj : m + 1 = j) :
    Module.Finite R (C.toCC.homology m) ↔
      Module.Finite R (subquot (LinearMap.range (C.d i m hi)) (LinearMap.ker (C.d m j hj))) := by
  have h1 : Module.Finite R (C.toCC.homology m) ↔
      Module.Finite R (subquot (LinearMap.range (C.toCC.sc' i m j).f.hom)
        (LinearMap.ker (C.toCC.sc' i m j).g.hom)) :=
    ⟨fun _ => Module.Finite.equiv (gcxHomologyEquiv C i m j hi hj),
      fun _ => Module.Finite.equiv (gcxHomologyEquiv C i m j hi hj).symm⟩
  rw [h1]
  exact moduleFinite_subquot_congr (congrArg LinearMap.range (sc'_f_hom C i m j hi))
    (congrArg LinearMap.ker (sc'_g_hom C i m j hj))

/-- **The cohomology of a relation-indexed complex in degree `m` is finite exactly when its
`m`-cocycles modulo `m`-coboundaries are.** -/
theorem finite_gcx_homology_iff' (C : GCx R) (i m j : ℤ) (hi : i + 1 = m) (hj : m + 1 = j) :
    Finite (C.toCC.homology m) ↔
      Finite (subquot (LinearMap.range (C.d i m hi)) (LinearMap.ker (C.d m j hj))) := by
  have h1 : Finite (C.toCC.homology m) ↔
      Finite (subquot (LinearMap.range (C.toCC.sc' i m j).f.hom)
        (LinearMap.ker (C.toCC.sc' i m j).g.hom)) :=
    ⟨fun _ => Finite.of_equiv _ (gcxHomologyEquiv C i m j hi hj).toEquiv,
      fun _ => Finite.of_equiv _ (gcxHomologyEquiv C i m j hi hj).symm.toEquiv⟩
  rw [h1]
  exact finite_subquot_congr (congrArg LinearMap.range (sc'_f_hom C i m j hi))
    (congrArg LinearMap.ker (sc'_g_hom C i m j hj))

theorem moduleFinite_gcx_homology_iff (C : GCx R) (n : ℤ) :
    Module.Finite R (C.toCC.homology n) ↔
      Module.Finite R (subquot (LinearMap.range (C.d (n - 1) n (by omega)))
        (LinearMap.ker (C.d n (n + 1) rfl))) :=
  moduleFinite_gcx_homology_iff' C (n - 1) n (n + 1) (by omega) rfl

/-- A class of the cohomology of a relation-indexed complex, from a cocycle. -/
def gcxClass (C : GCx R) (i m j : ℤ) (hi : i + 1 = m) (hj : m + 1 = j)
    (x : LinearMap.ker (C.d m j hj)) :
    subquot (LinearMap.range (C.d i m hi)) (LinearMap.ker (C.d m j hj)) :=
  Submodule.Quotient.mk x

/-- Two cocycles have the same class exactly when they differ by a coboundary. -/
theorem gcxClass_eq_iff (C : GCx R) (i m j : ℤ) (hi : i + 1 = m) (hj : m + 1 = j)
    (x y : LinearMap.ker (C.d m j hj)) :
    gcxClass C i m j hi hj x = gcxClass C i m j hi hj y ↔
      ∃ w : C.X i, C.d i m hi w = (x : C.X m) - (y : C.X m) := by
  rw [gcxClass, gcxClass, Submodule.Quotient.eq]
  rfl

end Subquot

section Exact

variable {R : Type} [CommRing R]

/-- **The middle term of an exact sequence with finitely generated ends is finitely generated**,
over a noetherian ring. -/
theorem moduleFinite_of_exact [IsNoetherianRing R] {S : ShortComplex (ModuleCat.{0} R)}
    (hS : S.Exact) (h₁ : Module.Finite R S.X₁) (h₃ : Module.Finite R S.X₃) :
    Module.Finite R S.X₂ := by
  rw [ShortComplex.moduleCat_exact_iff] at hS
  have hker : LinearMap.ker S.g.hom = (⊤ : Submodule R S.X₁).map S.f.hom := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hS x hx
      exact ⟨y, trivial, hy⟩
    · rintro ⟨y, -, rfl⟩
      change (S.f ≫ S.g).hom y = 0
      rw [S.zero]
      rfl
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker S.g.hom ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, hker]
    exact h₁.fg_top.map _

end Exact

section Pi

variable {R : Type} [CommRing R]

/-- The cocycles modulo coboundaries of a product embed into the product of the cocycles modulo
coboundaries. -/
theorem exists_injective_subquot_piCx {ι : Type} (A : ι → GCx R) (n : ℤ) :
    ∃ Φ : subquot (LinearMap.range ((piCx A).d (n - 1) n (by omega)))
        (LinearMap.ker ((piCx A).d n (n + 1) rfl)) →ₗ[R]
      (∀ v, subquot (LinearMap.range ((A v).d (n - 1) n (by omega)))
        (LinearMap.ker ((A v).d n (n + 1) rfl))), Function.Injective Φ := by
  have hcomp : ∀ (x : LinearMap.ker ((piCx A).d n (n + 1) rfl)) (v : ι),
      (x : (piCx A).X n) v ∈ LinearMap.ker ((A v).d n (n + 1) rfl) := by
    intro x v
    have hx : (piCx A).d n (n + 1) rfl (x : (piCx A).X n) = 0 := x.2
    rw [LinearMap.mem_ker, ← piCx_d_apply A n (n + 1) rfl (x : (piCx A).X n) v, hx]
    rfl
  let c : ∀ v, LinearMap.ker ((piCx A).d n (n + 1) rfl) →ₗ[R]
      LinearMap.ker ((A v).d n (n + 1) rfl) := fun v =>
    LinearMap.codRestrict _ ((LinearMap.proj v).comp (LinearMap.ker ((piCx A).d n (n + 1)
      rfl)).subtype) (fun x => hcomp x v)
  let Φ : LinearMap.ker ((piCx A).d n (n + 1) rfl) →ₗ[R]
      (∀ v, subquot (LinearMap.range ((A v).d (n - 1) n (by omega)))
        (LinearMap.ker ((A v).d n (n + 1) rfl))) :=
    LinearMap.pi fun v => (Submodule.mkQ _).comp (c v)
  have hle : (LinearMap.range ((piCx A).d (n - 1) n (by omega))).comap
      (LinearMap.ker ((piCx A).d n (n + 1) rfl)).subtype ≤ LinearMap.ker Φ := by
    rintro x ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    funext v
    change Submodule.mkQ _ (c v x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    refine ⟨y v, ?_⟩
    change (A v).d (n - 1) n (by omega) (y v) = (x : (piCx A).X n) v
    rw [← piCx_d_apply A (n - 1) n (by omega) y v, hy]
    rfl
  have hker' : LinearMap.ker Φ ≤ (LinearMap.range ((piCx A).d (n - 1) n (by omega))).comap
      (LinearMap.ker ((piCx A).d n (n + 1) rfl)).subtype := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hv : ∀ v, ∃ y : (A v).X (n - 1), (A v).d (n - 1) n (by omega) y =
        (x : (piCx A).X n) v := by
      intro v
      have hxv := congrFun hx v
      change Submodule.mkQ _ (c v x) = 0 at hxv
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hxv
      exact hxv
    choose y hy using hv
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨y, ?_⟩
    funext v
    exact hy v
  refine ⟨Submodule.liftQ _ Φ hle, ?_⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ Φ hle hker'

/-- **The cohomology of a finite product of complexes with finitely generated cohomology is
finitely generated**, over a noetherian ring. -/
theorem moduleFinite_homology_piCx [IsNoetherianRing R] {ι : Type} [Finite ι] (A : ι → GCx R)
    (n : ℤ) (h : ∀ v, Module.Finite R ((A v).toCC.homology n)) :
    Module.Finite R ((piCx A).toCC.homology n) := by
  rw [moduleFinite_gcx_homology_iff]
  have h' : ∀ v, Module.Finite R (subquot (LinearMap.range ((A v).d (n - 1) n (by omega)))
      (LinearMap.ker ((A v).d n (n + 1) rfl))) := fun v =>
    (moduleFinite_gcx_homology_iff (A v) n).1 (h v)
  obtain ⟨Φ, hΦ⟩ := exists_injective_subquot_piCx A n
  exact Module.Finite.of_injective Φ hΦ

end Pi

section Shift

variable {R : Type} [CommRing R]

theorem range_shiftDown_d (L : GCx R) (n : ℤ) :
    LinearMap.range ((shiftDown L).d (n - 1) n (by omega)) =
      LinearMap.range (L.d (n - 1 - 1) (n - 1) (by omega)) := by
  change LinearMap.range (-(L.d (n - 1 - 1) (n - 1) (by omega))) = _
  exact LinearMap.range_neg _

theorem ker_shiftDown_d (L : GCx R) (n : ℤ) :
    LinearMap.ker ((shiftDown L).d n (n + 1) rfl) =
      LinearMap.ker (L.d (n - 1) (n - 1 + 1) rfl) := by
  change LinearMap.ker (-(L.d (n - 1) (n + 1 - 1) (by omega))) = _
  rw [LinearMap.ker_neg]
  exact ker_d_congr L _ _

/-- **Shifting down by one shifts the cohomology** (finite generation). -/
theorem moduleFinite_homology_shiftDown (L : GCx R) (n : ℤ)
    (h : Module.Finite R (L.toCC.homology (n - 1))) :
    Module.Finite R ((shiftDown L).toCC.homology n) := by
  rw [moduleFinite_gcx_homology_iff] at h ⊢
  exact (moduleFinite_subquot_congr (range_shiftDown_d L n) (ker_shiftDown_d L n)).2 h

end Shift

section Selmer

variable {R : Type} [CommRing R]

/-- **Finite generation of the cohomology of a Selmer complex** in degree `n`, over a noetherian
ring, from that of its global complex in degree `n`, its local conditions in degree `n` and its
local complexes in degree `n − 1`. -/
theorem moduleFinite_homology_selCx [IsNoetherianRing R] (D : SelData R) (n : ℤ)
    (hG : Module.Finite R (D.G.toCC.homology n)) (hU : Module.Finite R (D.U.toCC.homology n))
    (hL : Module.Finite R (D.L.toCC.homology (n - 1))) :
    Module.Finite R ((selCx D).toCC.homology n) := by
  have hC : Module.Finite R ((locCx D).toCC.homology n) :=
    moduleFinite_of_exact ((coneSES_shortExact (negι D)).homology_exact₂ n)
      (moduleFinite_homology_shiftDown _ n hL) hU
  exact moduleFinite_of_exact ((sesTop_shortExact D).homology_exact₂ n) hC hG

end Selmer

/-! ### Continuous cochains with two-adic coefficients -/

section CochainFun

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- The underlying function `Gʲ → M` of a continuous cochain. -/
abbrev cochainFun {j : ℕ} (c : (contCochains k G M).X j) : (Fin j → G) → M :=
  asFun k G M ((contSubCx k G M).el c).1

/-- The continuous cochain with a given continuous underlying function. -/
abbrev mkCochain {j : ℕ} (f : (Fin j → G) → M) (hf : Continuous f) : (contCochains k G M).X j :=
  (contSubCx k G M).ofSub ⟨(f : (groupCohomology.inhomogeneousCochains (rep k G M)).X j), hf⟩

theorem continuous_cochainFun {j : ℕ} (c : (contCochains k G M).X j) :
    Continuous (cochainFun c) :=
  ((contSubCx k G M).el c).2

theorem cochainFun_mkCochain {j : ℕ} (f : (Fin j → G) → M) (hf : Continuous f) :
    cochainFun (mkCochain (k := k) f hf) = f :=
  rfl

theorem cochain_ext {j : ℕ} {c c' : (contCochains k G M).X j}
    (h : ∀ x, cochainFun c x = cochainFun c' x) : c = c' :=
  Subtype.ext (funext h)

theorem cochainFun_add {j : ℕ} (c c' : (contCochains k G M).X j) (x : Fin j → G) :
    cochainFun (c + c') x = cochainFun c x + cochainFun c' x :=
  rfl

theorem cochainFun_sub {j : ℕ} (c c' : (contCochains k G M).X j) (x : Fin j → G) :
    cochainFun (c - c') x = cochainFun c x - cochainFun c' x :=
  rfl

theorem cochainFun_zero {j : ℕ} (x : Fin j → G) :
    cochainFun (0 : (contCochains k G M).X j) x = 0 :=
  rfl

theorem cochainFun_smul {j : ℕ} (a : k) (c : (contCochains k G M).X j) (x : Fin j → G) :
    cochainFun (a • c) x = a • cochainFun c x :=
  rfl

/-- The differential of continuous cochains, on underlying functions. -/
theorem cochainFun_d {j : ℕ} (c : (contCochains k G M).X j) (g : Fin (j + 1) → G) :
    cochainFun (((contCochains k G M).d j (j + 1)).hom c) g =
      g 0 • cochainFun c (fun i => g i.succ) +
        ∑ i : Fin (j + 1), (-1 : k) ^ ((i : ℕ) + 1) • cochainFun c (Fin.contractNth i (· * ·) g) :=
  contCochains_d_apply j c g

end CochainFun

section Levels

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {T : Type} [AddCommGroup T] [Module ℤ_[2] T] [DistribMulAction G T] [SMulCommClass G ℤ_[2] T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul ℤ_[2] T] [ContinuousSMul G T]
  {L : ℕ → Type} [∀ k, AddCommGroup (L k)] [∀ k, DistribMulAction G (L k)]
  [∀ k, TopologicalSpace (L k)] [∀ k, DiscreteTopology (L k)] [∀ k, ContinuousSMul G (L k)]

/-- **Two-adic limit data**: `T` is the inverse limit of discrete modules `L k` along the
projections `p k : T → L k`, with `ker (p k) = 2^k T`, compatibly with the topology (continuous
division by `2^k` on the kernel and continuous limits of compatible families). -/
structure IsTwoAdicLimit (p : ∀ k, T →+ L k) : Prop where
  continuous : ∀ k, Continuous (p k)
  surjective : ∀ k, Function.Surjective (p k)
  map_two_pow_smul : ∀ k (t : T), p k ((2 : ℤ_[2]) ^ k • t) = 0
  divide : ∀ (k : ℕ) {X : Type} [TopologicalSpace X] (f : X → T), Continuous f →
    (∀ x, p k (f x) = 0) → ∃ g : X → T, Continuous g ∧ ∀ x, (2 : ℤ_[2]) ^ k • g x = f x
  limit : ∀ {X : Type} [TopologicalSpace X] (f : ℕ → X → T), (∀ j, Continuous (f j)) →
    (∀ j x, p j (f (j + 1) x) = p j (f j x)) →
    ∃ g : X → T, Continuous g ∧ ∀ j x, p j (g x) = p j (f j x)
  separated : ∀ t : T, (∀ k, p k t = 0) → t = 0
  torsionFree : ∀ t : T, (2 : ℤ_[2]) • t = 0 → t = 0

variable (G) in
/-- The projections are `G`-equivariant. -/
def IsEquivariantLevels (p : ∀ k, T →+ L k) : Prop :=
  ∀ k (g : G) (t : T), p k (g • t) = g • p k t

variable (p : ∀ k, T →+ L k)

variable (G) in
/-- The reduction of a continuous cochain `c` modulo `2^k`: `p k ∘ c`. -/
def redCochain (hp : IsTwoAdicLimit p) (k j : ℕ) :
    (contCochains ℤ_[2] G T).X j →+ (contCochains ℤ G (L k)).X j where
  toFun c := mkCochain (fun x => p k (cochainFun c x)) ((hp.continuous k).comp
    (continuous_cochainFun c))
  map_zero' := cochain_ext fun _ => map_zero (p k)
  map_add' _ _ := cochain_ext fun _ => map_add (p k) _ _

theorem cochainFun_redCochain (hp : IsTwoAdicLimit p) (k j : ℕ)
    (c : (contCochains ℤ_[2] G T).X j) (x : Fin j → G) :
    cochainFun (redCochain G p hp k j c) x = p k (cochainFun c x) :=
  rfl

variable (G) in
/-- The reduction modulo `2^k` in every degree of the extended complexes. -/
def red (hp : IsTwoAdicLimit p) (k : ℕ) :
    ∀ m : ℤ, (natCx (contCochains ℤ_[2] G T)).X m →+ (natCx (contCochains ℤ G (L k))).X m
  | Int.ofNat j => redCochain G p hp k j
  | Int.negSucc _ => 0

end Levels

section Signs

variable {T : Type} [AddCommGroup T] [Module ℤ_[2] T] {L' : Type} [AddCommGroup L']

/-- Signs: `q ((−1)^m • t) = (−1)^m • q t` for an additive map `q`. -/
theorem map_neg_one_pow_smul (q : T →+ L') (m : ℕ) (t : T) :
    q ((-1 : ℤ_[2]) ^ m • t) = (-1 : ℤ) ^ m • q t := by
  have h : (-1 : ℤ_[2]) ^ m • t = ((-1 : ℤ) ^ m) • t := by
    rw [← Int.cast_smul_eq_zsmul ℤ_[2]]
    push_cast
    rfl
  rw [h, map_zsmul]

end Signs

section Reduction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {T : Type} [AddCommGroup T] [Module ℤ_[2] T] [DistribMulAction G T] [SMulCommClass G ℤ_[2] T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul ℤ_[2] T] [ContinuousSMul G T]
  {L : ℕ → Type} [∀ k, AddCommGroup (L k)] [∀ k, DistribMulAction G (L k)]
  [∀ k, TopologicalSpace (L k)] [∀ k, DiscreteTopology (L k)] [∀ k, ContinuousSMul G (L k)]
  {p : ∀ k, T →+ L k}

/-- Reduction commutes with the differential of the continuous cochains. -/
theorem redCochain_comm (hp : IsTwoAdicLimit p) (hG : IsEquivariantLevels G p) (k n : ℕ)
    (x : (contCochains ℤ_[2] G T).X n) :
    redCochain G p hp k (n + 1) (((contCochains ℤ_[2] G T).d n (n + 1)).hom x) =
      ((contCochains ℤ G (L k)).d n (n + 1)).hom (redCochain G p hp k n x) := by
  apply cochain_ext
  intro g
  rw [cochainFun_redCochain, cochainFun_d, cochainFun_d, map_add, map_sum, hG,
    cochainFun_redCochain]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_neg_one_pow_smul, cochainFun_redCochain]

/-- **Reduction commutes with the differentials.** -/
theorem red_comm (hp : IsTwoAdicLimit p) (hG : IsEquivariantLevels G p) (k : ℕ) :
    ∀ (i j : ℤ) (h : i + 1 = j) (x : (natCx (contCochains ℤ_[2] G T)).X i),
      red G p hp k j ((natCx (contCochains ℤ_[2] G T)).d i j h x) =
        (natCx (contCochains ℤ G (L k))).d i j h (red G p hp k i x) := by
  intro i j h
  subst h
  cases i with
  | ofNat n =>
    intro x
    exact redCochain_comm hp hG k n x
  | negSucc n =>
    intro x
    have h1 : (natCx (contCochains ℤ_[2] G T)).d (Int.negSucc n) (Int.negSucc n + 1) rfl x = 0 :=
      rfl
    have h2 : (natCx (contCochains ℤ G (L k))).d (Int.negSucc n) (Int.negSucc n + 1) rfl
        (red G p hp k (Int.negSucc n) x) = 0 := rfl
    rw [h1, h2, map_zero]

/-- **Reduction is surjective** (lifting through a set-theoretic section of `p k`, continuous
because the levels are discrete). -/
theorem red_surjective (hp : IsTwoAdicLimit p) (k : ℕ) :
    ∀ m : ℤ, Function.Surjective (red G p hp k m)
  | Int.ofNat j => by
    intro c
    let s := Function.surjInv (hp.surjective k)
    refine ⟨mkCochain (fun x => s (cochainFun c x))
      ((continuous_of_discreteTopology (f := s)).comp (continuous_cochainFun c)), ?_⟩
    apply cochain_ext
    intro x
    exact Function.surjInv_eq (hp.surjective k) _
  | Int.negSucc _ => fun _ => ⟨0, rfl⟩

/-- **The kernel of reduction modulo `2^k` is `2^k` times the cochains.** -/
theorem red_ker (hp : IsTwoAdicLimit p) (k : ℕ) :
    ∀ (m : ℤ) (x : (natCx (contCochains ℤ_[2] G T)).X m), red G p hp k m x = 0 →
      ∃ y, x = (2 : ℤ_[2]) ^ k • y
  | Int.ofNat j => by
    intro c hc
    have hc' : ∀ x, p k (cochainFun c x) = 0 := fun x => by
      have := congrArg (fun c' => cochainFun c' x) hc
      exact this
    obtain ⟨g, hg, hgc⟩ := hp.divide k (cochainFun c) (continuous_cochainFun c) hc'
    exact ⟨mkCochain g hg, cochain_ext fun x => (hgc x).symm⟩
  | Int.negSucc _ => fun x _ => ⟨x, rfl⟩

/-- Reduction modulo `2^k` kills `2^k` times the cochains. -/
theorem red_two_pow_smul (hp : IsTwoAdicLimit p) (k : ℕ) :
    ∀ (m : ℤ) (y : (natCx (contCochains ℤ_[2] G T)).X m), red G p hp k m ((2 : ℤ_[2]) ^ k • y) = 0
  | Int.ofNat _ => fun _ => cochain_ext fun _ => hp.map_two_pow_smul k _
  | Int.negSucc _ => fun _ => rfl

omit [∀ k, DiscreteTopology (L k)] [∀ k, ContinuousSMul G (L k)]
  [∀ k, DistribMulAction G (L k)] in
/-- The cochains have no `2`-torsion. -/
theorem cochains_torsionFree (hp : IsTwoAdicLimit p) :
    ∀ (m : ℤ) (z : (natCx (contCochains ℤ_[2] G T)).X m), (2 : ℤ_[2]) • z = 0 → z = 0
  | Int.ofNat j => fun z hz => cochain_ext fun x => hp.torsionFree _ (by
      have := congrArg (fun c => cochainFun c x) hz
      exact this)
  | Int.negSucc _ => fun _ _ => rfl

omit [∀ k, DiscreteTopology (L k)] [∀ k, ContinuousSMul G (L k)]
  [∀ k, DistribMulAction G (L k)] in
/-- The cochains are two-adically separated. -/
theorem cochains_separated (hp : IsTwoAdicLimit p) :
    ∀ (m : ℤ) (b : (natCx (contCochains ℤ_[2] G T)).X m),
      (∀ k : ℕ, ∃ b', b = (2 : ℤ_[2]) ^ k • b') → b = 0
  | Int.ofNat j => fun b hb => cochain_ext fun x => hp.separated _ fun k => by
      obtain ⟨b', hb'⟩ := hb k
      have := congrArg (fun c => cochainFun c x) hb'
      change cochainFun b x = (2 : ℤ_[2]) ^ k • cochainFun b' x at this
      rw [this]
      exact hp.map_two_pow_smul k _
  | Int.negSucc _ => fun _ _ => rfl

omit [∀ k, DiscreteTopology (L k)] [∀ k, ContinuousSMul G (L k)]
  [∀ k, DistribMulAction G (L k)] in
/-- The cochains are two-adically complete. -/
theorem cochains_complete (hp : IsTwoAdicLimit p) :
    ∀ (m : ℤ) (s : ℕ → (natCx (contCochains ℤ_[2] G T)).X m),
      (∀ k, ∃ a, s (k + 1) - s k = (2 : ℤ_[2]) ^ k • a) →
      ∃ s', ∀ k, ∃ a, s' - s k = (2 : ℤ_[2]) ^ k • a
  | Int.ofNat j => by
    intro s hs
    choose a ha using hs
    have hcompat : ∀ k x, p k (cochainFun (s (k + 1)) x) = p k (cochainFun (s k) x) := by
      intro k x
      have h1 := congrArg (fun c => p k (cochainFun c x)) (ha k)
      change p k (cochainFun (s (k + 1)) x - cochainFun (s k) x) =
        p k ((2 : ℤ_[2]) ^ k • cochainFun (a k) x) at h1
      rw [map_sub, hp.map_two_pow_smul] at h1
      exact sub_eq_zero.mp h1
    obtain ⟨g, hg, hgp⟩ := hp.limit (fun k => cochainFun (s k))
      (fun k => continuous_cochainFun _) hcompat
    refine ⟨mkCochain g hg, fun k => ?_⟩
    have hcont : Continuous (fun x => g x - cochainFun (s k) x) := by
      have h := hg.add ((continuous_cochainFun (s k)).const_smul (-1 : ℤ_[2]))
      refine h.congr fun x => ?_
      change g x + (-1 : ℤ_[2]) • cochainFun (s k) x = g x - cochainFun (s k) x
      rw [neg_one_smul, ← sub_eq_add_neg]
    obtain ⟨e, he, hee⟩ := hp.divide k (fun x => g x - cochainFun (s k) x) hcont
      (fun x => by rw [map_sub, hgp, sub_self])
    exact ⟨mkCochain e he, cochain_ext fun x => (hee x).symm⟩
  | Int.negSucc _ => fun _ _ => ⟨0, fun _ => ⟨0, rfl⟩⟩

/-- **Residual finiteness of the two-adic cochains from finiteness of the cohomology of the
levels.** -/
theorem twoPowResidualFinite_of_levels (hp : IsTwoAdicLimit p) (hG : IsEquivariantLevels G p)
    (k : ℕ)
    (i m j : ℤ) (hi : i + 1 = m) (hj : m + 1 = j)
    (hfin : Finite ((natCx (contCochains ℤ G (L k))).toCC.homology m)) :
    TwoPowResidualFinite ((natCx (contCochains ℤ_[2] G T)).d i m hi)
      ((natCx (contCochains ℤ_[2] G T)).d m j hj) k := by
  classical
  have hF := (finite_gcx_homology_iff' (natCx (contCochains ℤ G (L k))) i m j hi hj).1 hfin
  have hker : ∀ y : (natCx (contCochains ℤ_[2] G T)).X m,
      red G p hp k j ((natCx (contCochains ℤ_[2] G T)).d m j hj y) = 0 →
      red G p hp k m y ∈ LinearMap.ker ((natCx (contCochains ℤ G (L k))).d m j hj) := by
    intro y hy
    rw [LinearMap.mem_ker, ← red_comm hp hG k m j hj y]
    exact hy
  refine ⟨_, hF, fun y =>
    if h : red G p hp k j ((natCx (contCochains ℤ_[2] G T)).d m j hj y) = 0 then
      gcxClass (natCx (contCochains ℤ G (L k))) i m j hi hj ⟨red G p hp k m y, hker y h⟩
    else 0, ?_⟩
  rintro y y' ⟨z, hz⟩ ⟨z', hz'⟩ hφ
  have h1 : red G p hp k j ((natCx (contCochains ℤ_[2] G T)).d m j hj y) = 0 := by
    rw [hz, red_two_pow_smul]
  have h1' : red G p hp k j ((natCx (contCochains ℤ_[2] G T)).d m j hj y') = 0 := by
    rw [hz', red_two_pow_smul]
  simp only [h1, h1', dite_true] at hφ
  obtain ⟨w', hw'⟩ := (gcxClass_eq_iff _ i m j hi hj _ _).1 hφ
  obtain ⟨w, rfl⟩ := red_surjective hp k i w'
  rw [← red_comm hp hG k i m hi w] at hw'
  obtain ⟨b, hb⟩ := red_ker hp k m (y - y' - (natCx (contCochains ℤ_[2] G T)).d i m hi w) (by
    rw [map_sub, map_sub, hw']
    exact sub_self _)
  exact ⟨b, w, by rw [← hb]; abel⟩

/-- **Finite generation of continuous cohomology with two-adic coefficients.** If `T` is the
two-adic limit of discrete `G`-modules `L k` (with `G`-equivariant projections) and every
continuous cohomology group of every level is finite, then every continuous cohomology group of
`T` is a finitely generated `ℤ₂`-module. -/
theorem moduleFinite_homology_of_twoAdicLimit (hp : IsTwoAdicLimit p)
    (hG : IsEquivariantLevels G p)
    (hfin : ∀ (k : ℕ) (m : ℤ), Finite ((natCx (contCochains ℤ G (L k))).toCC.homology m))
    (n : ℤ) : Module.Finite ℤ_[2] ((natCx (contCochains ℤ_[2] G T)).toCC.homology n) := by
  rw [moduleFinite_gcx_homology_iff' _ (n - 1) n (n + 1) (by omega) rfl]
  exact moduleFinite_subquot_of_residual
    ((natCx (contCochains ℤ_[2] G T)).d (n - 1 - 1) (n - 1) (by omega))
    ((natCx (contCochains ℤ_[2] G T)).d (n - 1) n (by omega))
    ((natCx (contCochains ℤ_[2] G T)).d n (n + 1) rfl)
    (fun x => (natCx (contCochains ℤ_[2] G T)).d_d _ _ _ _ _ x)
    (fun x => (natCx (contCochains ℤ_[2] G T)).d_d _ _ _ _ _ x)
    (cochains_torsionFree hp (n + 1)) (cochains_separated hp n) (cochains_complete hp (n - 1))
    (twoPowResidualFinite_of_levels hp hG 1 (n - 1) n (n + 1) (by omega) rfl (hfin 1 n))
    (fun k => twoPowResidualFinite_of_levels hp hG k (n - 1 - 1) (n - 1) n (by omega) (by omega)
      (hfin k (n - 1)))

end Reduction

/-! ### The Tate module as a two-adic limit -/

section Tate

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.CoefModules

attribute [local instance] levTop continuousSMul_lev

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-- **Division by `2^k`** on the kernel of `T_2E → E(K_S)[2^k]`: the point with coordinates
`P_{n+k}`. -/
def tateShift (k : ℕ) (P : TateS K S W) (hP : P.pt k = 0) : TateS K S W :=
  ⟨fun n => ⟨P.pt (n + k), by
      rw [mem_lev_iff, P.pt_congr (Nat.add_comm n k), P.two_pow_smul_pt k n, hP]⟩,
    fun n => Subtype.ext (by
      change 2 • P.pt (n + 1 + k) = P.pt (n + k)
      rw [P.pt_congr (show n + 1 + k = n + k + 1 by omega), P.two_smul_pt])⟩

theorem two_pow_smul_tateShift (k : ℕ) (P : TateS K S W) (hP : P.pt k = 0) :
    (2 : ℤ_[2]) ^ k • tateShift k P hP = P := by
  refine TateS.ext' fun n => ?_
  have hlev : (2 ^ n : ℕ) • P.pt (n + k) = 0 := by
    rw [P.pt_congr (Nat.add_comm n k), P.two_pow_smul_pt k n, hP]
  change resN n ((2 : ℤ_[2]) ^ k) • P.pt (n + k) = P.pt n
  rw [show ((2 : ℤ_[2]) ^ k) = ((2 ^ k : ℕ) : ℤ_[2]) by push_cast; rfl, resN_natCast,
    nsmul_mod_eq hlev, P.two_pow_smul_pt n k]

theorem continuous_tateShift {X : Type} [TopologicalSpace X] (k : ℕ) (f : X → TateS K S W)
    (hf : Continuous f) (h0 : ∀ x, (f x).pt k = 0) :
    Continuous (fun x => tateShift k (f x) (h0 x)) := by
  classical
  refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
  let ρ : Lev K S W (n + k) → Lev K S W n := fun Q =>
    if h : (2 ^ n : ℕ) • (Q : Pt K S W) = 0 then ⟨Q, (mem_lev_iff _).mpr h⟩ else 0
  refine ((continuous_of_discreteTopology (f := ρ)).comp
    ((continuous_projLev (n + k)).comp hf)).congr fun x => ?_
  have h : (2 ^ n : ℕ) • ((projLev (n + k) (f x) : Lev K S W (n + k)) : Pt K S W) = 0 := by
    rw [coe_projLev, (f x).pt_congr (Nat.add_comm n k), (f x).two_pow_smul_pt k n, h0 x]
  change ρ (projLev (n + k) (f x)) = _
  simp only [ρ, h, dite_true]
  rfl

variable (K S W) in
/-- **`T_2E = lim E(K_S)[2^k]` is a two-adic limit** along the projections. -/
theorem isTwoAdicLimit_tate [W.IsElliptic] [HasFullTwoTorsion K S W] :
    IsTwoAdicLimit (T := TateS K S W) (L := fun k => Lev K S W k) (fun k => projLev k) where
  continuous k := continuous_projLev k
  surjective k := projLev_surjective k
  map_two_pow_smul k t := Subtype.ext ((mem_ker_projLev_iff k _).mpr ⟨t, rfl⟩)
  divide := fun k {X} _ f hf h0 => by
    have h0' : ∀ x, (f x).pt k = 0 := fun x => congrArg Subtype.val (h0 x)
    exact ⟨fun x => tateShift k (f x) (h0' x), continuous_tateShift k f hf h0',
      fun x => two_pow_smul_tateShift k (f x) (h0' x)⟩
  limit := fun {X} _ f hf hcompat => by
    refine ⟨fun x => ⟨fun j => projLev j (f j x), fun j => ?_⟩, ?_, fun j x => rfl⟩
    · show transLev K S W j (projLev (j + 1) (f (j + 1) x)) = projLev j (f j x)
      rw [← hcompat j x]
      exact (f (j + 1) x).2 j
    · exact continuous_induced_rng.mpr (continuous_pi fun j => (continuous_projLev j).comp (hf j))
  separated t ht := TateS.ext' fun n => congrArg Subtype.val (ht n)
  torsionFree t ht := TateS.ext' fun n => by
    have h2 : t + t = 0 := by rw [← two_smul ℤ_[2] t]; exact ht
    rw [← t.two_smul_pt n, two_nsmul, ← TateS.pt_add, h2]
    rfl

variable (K S W) in
/-- The projections of `T_2E` are `G_{K,S}`-equivariant. -/
theorem isEquivariantLevels_tate :
    IsEquivariantLevels (GKS K S) (T := TateS K S W) (L := fun k => Lev K S W k)
      (fun k => projLev k) :=
  fun k g t => projLev_smul k g t

/-- The projections, read on the restriction of `T_2E` to a local Galois group. -/
def projLevRes {H : Type} [Group H] [TopologicalSpace H] (φ : H →ₜ* GKS K S) (k : ℕ) :
    ResMod φ (TateS K S W) →+ ResMod φ (Lev K S W k) :=
  projLev k

variable (K S W) in
theorem isTwoAdicLimit_tateRes [W.IsElliptic] [HasFullTwoTorsion K S W] {H : Type} [Group H]
    [TopologicalSpace H] (φ : H →ₜ* GKS K S) :
    IsTwoAdicLimit (T := ResMod φ (TateS K S W)) (L := fun k => ResMod φ (Lev K S W k))
      (fun k => projLevRes φ k) :=
  isTwoAdicLimit_tate K S W

variable (K S W) in
theorem isEquivariantLevels_tateRes {H : Type} [Group H] [TopologicalSpace H]
    (φ : H →ₜ* GKS K S) :
    IsEquivariantLevels H (T := ResMod φ (TateS K S W)) (L := fun k => ResMod φ (Lev K S W k))
      (fun k => projLevRes φ k) :=
  fun k g t => projLev_smul k (φ g) t

omit [NumberField K] in
/-- The primes dividing `#E(K_S)[2^k] = 4^k` lie above `2`. -/
theorem natCard_lev_mem [HasFullTwoTorsion K S W]
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) (k : ℕ) :
    ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card (Lev K S W k) : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  rw [natCard_lev, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at hv
  exact h2 v (v.isPrime.mem_of_pow_mem k (v.isPrime.mem_of_pow_mem 2 hv))

variable (K S W) in
/-- **Global Tate cohomology is finitely generated**: for a finite set `S` of finite primes
containing those above `2` and full `2`-power torsion over `K_S`, every continuous cohomology group
`Hⁿ(G_{K,S}, T_2E)` is a finitely generated `ℤ₂`-module (from Milne I.4.15 at every level
`E(K_S)[2^k]`). -/
theorem moduleFinite_globalTateCohomology (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) [W.IsElliptic]
    [HasFullTwoTorsion K S W] (n : ℤ) :
    Module.Finite ℤ_[2] ((natCx (contCochains ℤ_[2] (GKS K S) (TateS K S W))).toCC.homology n) :=
  moduleFinite_homology_of_twoAdicLimit (isTwoAdicLimit_tate K S W) (isEquivariantLevels_tate K S W)
    (fun k m => hglob K S hS ℤ (Lev K S W k) inferInstance (natCard_lev_mem h2 k) m) n

variable (K S W) in
/-- **Local Tate cohomology is finitely generated**: for every finite place `v`, every continuous
cohomology group `Hⁿ(G_{K_v}, T_2E)` is a finitely generated `ℤ₂`-module (from Milne I.2.1 at every
level `E(K_S)[2^k]`). -/
theorem moduleFinite_localTateCohomology (hloc : MilneLocalFiniteness) [W.IsElliptic]
    [HasFullTwoTorsion K S W] (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    Module.Finite ℤ_[2] ((natCx (contCochains ℤ_[2] (Gloc K v)
      (ResMod (locMap K S v) (TateS K S W)))).toCC.homology n) :=
  moduleFinite_homology_of_twoAdicLimit (isTwoAdicLimit_tateRes K S W (locMap K S v))
    (isEquivariantLevels_tateRes K S W (locMap K S v))
    (fun k m => hloc K v ℤ (ResMod (locMap K S v) (Lev K S W k))
      (inferInstanceAs (Finite (Lev K S W k))) m) n

end Tate

/-! ### The compact Kummer complex -/

section Kummer

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC53Assist.CentralKummer

attribute [local instance] levTop continuousSMul_lev

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

/-- **The cohomology of the `2`-adic Kummer condition is finitely generated** in every degree:
`H⁰(U_v) = H⁰(G_{K_v}, T_2E)`, `H¹(U_v) ⊆ H¹(G_{K_v}, T_2E)`, and `Uⁿ_v = 0` otherwise. -/
theorem moduleFinite_tateKummerCondition_homology (hloc : MilneLocalFiniteness)
    (v : HeightOneSpectrum (𝓞 K)) {dec : DecidableEq (v.adicCompletion K)} (n : ℤ) :
    Module.Finite ℤ_[2] ((@tateKummerCondition K _ _ S W _ hFull v dec).toCC.homology n) := by
  have : HasFullTwoTorsion K S W := ⟨hFull⟩
  match n with
  | Int.negSucc j =>
    have : Subsingleton ((@tateKummerCondition K _ _ S W _ hFull v dec).X (Int.negSucc j)) :=
      inferInstanceAs (Subsingleton PUnit)
    have := finite_homology_of_finite_X (@tateKummerCondition K _ _ S W _ hFull v dec)
      (Int.negSucc j) Finite.of_subsingleton
    exact Module.Finite.of_finite
  | Int.ofNat 0 =>
    have hiso := @tateKummerCondition_isIso_homologyMap_zero K _ _ S W _ hFull v dec
    have hinj : Function.Injective (HomologicalComplex.homologyMap
        (GHom.toCC (@tateKummerConditionι K _ _ S W _ hFull v dec)) 0).hom :=
      ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1
    have := moduleFinite_localTateCohomology K S W hloc v 0
    exact Module.Finite.of_injective _ hinj
  | Int.ofNat 1 =>
    have hmono := @tateKummerCondition_mono_homologyMap_one K _ _ S W _ hFull v dec
    have hinj := (ModuleCat.mono_iff_injective _).1 hmono
    have := moduleFinite_localTateCohomology K S W hloc v 1
    exact Module.Finite.of_injective _ hinj
  | Int.ofNat (j + 2) =>
    have : Subsingleton ((@tateKummerCondition K _ _ S W _ hFull v dec).X (Int.ofNat (j + 2))) :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℤ_[2]
        (contCochain ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) (j + 2))))
    have := finite_homology_of_finite_X (@tateKummerCondition K _ _ S W _ hFull v dec)
      (Int.ofNat (j + 2)) Finite.of_subsingleton
    exact Module.Finite.of_finite

variable (S) in
/-- **Finite generation of compact Kummer cohomology** (all degrees). For a number field `K`, a
finite set `S` of finite primes containing those above `2`, and an elliptic curve with full
`2`-power torsion over `K_S`, every cohomology group of the compact Kummer complex
`compactKummerComplex S W hFull` (the Selmer complex over `ℤ₂` with `T_2E` coefficients and the
`2`-adic Kummer condition at every place of `S`) is a finitely generated `ℤ₂`-module. Inputs:
the printed finiteness theorems Milne I.2.1 and I.4.15. -/
theorem moduleFinite_compactKummer_homology (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) (n : ℤ) :
    Module.Finite ℤ_[2] ((compactKummerComplex S W hFull).homology n) := by
  have : HasFullTwoTorsion K S W := ⟨hFull⟩
  have : Finite (Places K S) := hS.to_subtype
  refine moduleFinite_homology_selCx (tateKummerSelData S W hFull) n ?_ ?_ ?_
  · exact moduleFinite_globalTateCohomology K S W hglob hS h2 n
  · exact moduleFinite_homology_piCx _ n fun v =>
      moduleFinite_tateKummerCondition_homology W hFull hloc v.1 n
  · exact moduleFinite_homology_piCx _ (n - 1) fun v =>
      moduleFinite_localTateCohomology K S W hloc v.1 (n - 1)

end Kummer

/-! ### The input `KummerCohomologyFinite` of the universal-coefficient construction -/

section Universal

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC53Assist.CentralUniversal

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic]
  (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))

/-- **`KummerCohomologyFinite` for the genuine compact Kummer complex**, from the printed
finiteness theorems (Milne I.2.1 and I.4.15), for a finite support `S` containing the primes
above `2`. -/
theorem kummerCohomologyFinite_of_prints (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ S) :
    KummerCohomologyFinite ℓ k S hFull :=
  ⟨moduleFinite_compactKummer_homology S _ hFull hloc hglob hS h2 1,
    moduleFinite_compactKummer_homology S _ hFull hloc hglob hS h2 2⟩

/-- **`KummerCohomologyFinite` from the coefficient comparison**: the finiteness of the support is
the field `finite_support` of `KummerCoefficientComparison`. -/
theorem kummerCohomologyFinite_of_comparison (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (I : KummerCoefficientComparison ℓ k S hFull)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ S) :
    KummerCohomologyFinite ℓ k S hFull :=
  kummerCohomologyFinite_of_prints ℓ k S hFull hloc hglob I.finite_support h2

end Universal

/-! ### Finiteness of the finite-level Selmer cohomology -/

section Stage

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules

/-- **Cocycle conditions with finite coefficients have finite cohomology** (from Milne I.2.1):
their terms are finite, since `H¹(G_{K_v}, M)` is finite (`finite_cocycleCondition_X`). This
covers the finite-level Kummer conditions. -/
theorem finite_cocycleCondition_homology (hloc : MilneLocalFiniteness) {K : Type} [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {R : Type} [CommRing R] {M : Type}
    [AddCommGroup M] [Module R M] [DistribMulAction (Gloc K v) M] [SMulCommClass (Gloc K v) R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Gloc K v) M] [Finite M]
    (Z : Submodule R (contCochain R (Gloc K v) M 1))
    (hZ : ∀ z ∈ Z, contD R (Gloc K v) M 1 z = 0) (n : ℤ) :
    Finite ((cocycleCondition Z hZ).toCC.homology n) :=
  finite_homology_of_finite_X _ n
    (finite_cocycleCondition_X Z hZ
      (finite_subquot_one_of_homology (hloc K v R M inferInstance 1)) n)

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (R : Type)
  [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) R M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **Finiteness of finite-level Selmer cohomology**, degreewise: for a finite set `S` of finite
primes containing those dividing `#M`, a finite discrete `G_{K,S}`-module `M` over any coefficient
ring `R`, and local conditions with finite cohomology, every cohomology group of the Galois Selmer
complex `selCx (galoisSelData K S R M Δ)` is finite (the stage input
`galoisSelmerCohomologyFinite_of_prints`, from Milne I.2.1 and I.4.15). -/
theorem finite_galoisSelmer_homology (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hS : S.Finite) [Finite M]
    (hM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Δ : GaloisLocalConditions K S R M) (hΔ : ∀ v n, Finite ((Δ.U v).toCC.homology n))
    (n : ℤ) : Finite ((selCx (galoisSelData K S R M Δ)).toCC.homology n) :=
  galoisSelmerCohomologyFinite_of_prints K S R M hloc hglob hS hM Δ hΔ n

/-- **Finite generation of finite-level Selmer cohomology over the coefficient ring**: the form in
which the finite free models use the finiteness of the stage cohomology. -/
theorem moduleFinite_galoisSelmer_homology (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hS : S.Finite) [Finite M]
    (hM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Δ : GaloisLocalConditions K S R M) (hΔ : ∀ v n, Finite ((Δ.U v).toCC.homology n))
    (n : ℤ) : Module.Finite R ((selCx (galoisSelData K S R M Δ)).toCC.homology n) :=
  have := finite_galoisSelmer_homology K S R M hloc hglob hS hM Δ hΔ n
  Module.Finite.of_finite

/-- The strict local conditions have finite cohomology. -/
theorem finite_strictConditions_homology (v : Places K S) (n : ℤ) :
    Finite (((strictConditions R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M).U v).toCC.homology n) := by
  have : Subsingleton (((strictConditions R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M).U v).X n) := inferInstanceAs (Subsingleton PUnit)
  exact finite_homology_of_finite_X _ n Finite.of_subsingleton

end Stage

section TwoPower

open NumberField IsDedekindDomain

/-- The two-power-order case: the primes dividing `#M` are those above `2`. -/
theorem natCard_mem_of_two_pow {K : Type} [Field K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) {M : Type} {e : ℕ}
    (he : Nat.card M = 2 ^ e) :
    ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  rw [he, Nat.cast_pow, Nat.cast_ofNat] at hv
  exact h2 v (v.isPrime.mem_of_pow_mem e hv)

end TwoPower

section StageCoefficients

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ)

variable [IsOpenKer α]

/-- **Finite generation over `A_i` of the cohomology of the actual stage Selmer complexes**, for
the actual stage coefficient module `M_i = (E[2^i] ⊗ A_i)(α)`, a finite `S` containing the primes
above `2`, and local conditions with finite cohomology (the stage input
`stageSelmerCohomologyFinite`, as finite generation over `A_i`). -/
theorem moduleFinite_stageSelmer_homology (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Δ : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i α))
    (hΔ : ∀ v n, Finite ((Δ.U v).toCC.homology n)) (n : ℤ) :
    Module.Finite (Acoef i)
      ((selCx (galoisSelData K S (Acoef i) (Mcoef K S W i α) Δ)).toCC.homology n) :=
  have := stageSelmerCohomologyFinite W i α hloc hglob hS h2 Δ hΔ n
  Module.Finite.of_finite

end StageCoefficients

/-! ### The actual finite-level Kummer Selmer complexes -/

section ActualStage

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (frob eUr)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The unramified conditions have finite cohomology** (finite coefficients): they are the
two-term complexes `[M --(Φ − 1)--> M]`. -/
theorem finite_urAt_homology {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (k : Type)
    [CommRing k] [TopologicalSpace k] [DiscreteTopology k] (M₀ : Type) [AddCommGroup M₀]
    [Module k M₀] [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) k M₀]
    [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
    (w : Places K S) (hw : w.1 ∉ S₀) (n : ℤ) :
    Finite ((urAt hS k M₀ w hw).U.toCC.homology n) :=
  finite_homology_of_finite_X _ n
    (finite_frobCx_X (frob (eUr K w.1) (urRep k M₀ (newPlace w hw))) n)

/-- **The actual local conditions have finite cohomology** when the given ones at `S₀` do (the
unramified conditions at `S − S₀` have finite cohomology). -/
theorem finite_actualConditions_homology {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h n, Finite ((c v h).U.toCC.homology n)) (v : Places K S) (n : ℤ) :
    Finite (((actualConditions hS W i α c).U v).toCC.homology n) := by
  change Finite ((urOutside hS (Acoef i) (Mcoef K S₀ W i α) c v).U.toCC.homology n)
  unfold urOutside
  split_ifs with h
  · exact hc v h n
  · exact finite_urAt_homology hS (Acoef i) (Mcoef K S₀ W i α) v h n

/-- **Finiteness of the cohomology of the actual stage Selmer complexes** `actualSelData`
(coefficients `M_i` built over `G_{K,S₀}` and inflated to `S ⊇ S₀`, the given conditions at `S₀`
and the unramified conditions at `S − S₀`), for a finite `S` containing the primes above `2` and
given conditions with finite cohomology. -/
theorem finite_actualSelData_homology (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (hSfin : S.Finite) (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h n, Finite ((c v h).U.toCC.homology n)) (n : ℤ) :
    Finite ((selCx (actualSelData hS W i α c)).toCC.homology n) := by
  let := acoefTop i
  have := acoefTop_discrete i
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  obtain ⟨e, he⟩ := card_mcoef_eq_two_pow (S := S₀) W i α
  exact finite_galoisSelmer_homology K S (Acoef i) (MinS hS W i α) hloc hglob hSfin
    (natCard_mem_of_two_pow h2 he) (actualConditions hS W i α c)
    (finite_actualConditions_homology hS W i α c hc) n

/-- The same, as finite generation over `A_i`. -/
theorem moduleFinite_actualSelData_homology (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (hSfin : S.Finite) (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h n, Finite ((c v h).U.toCC.homology n)) (n : ℤ) :
    Module.Finite (Acoef i) ((selCx (actualSelData hS W i α c)).toCC.homology n) :=
  have := finite_actualSelData_homology hloc hglob hS hSfin h2 W i α c hc n
  Module.Finite.of_finite

/-- **Finiteness of the cohomology of the finite-level Kummer Selmer complexes** `kummerSelData`
(the genuine Kummer conditions at the places of `P`, the given conditions at the other places
of `S₀`, the unramified conditions at `S − S₀`): the Kummer conditions are cocycle conditions
and have finite cohomology. -/
theorem finite_kummerSelData_homology (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (hSfin : S.Finite) (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (α : GKS K S₀ →* (Acoef i)ˣ)
    (hFull : FullTorsion K S₀ W (2 ^ i)) [IsOpenKer α] (P : Set (HeightOneSpectrum (𝓞 K)))
    (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v hv hP n, Finite ((c v hv hP).U.toCC.homology n)) (n : ℤ) :
    Finite ((selCx (kummerSelData hS W i s hs hs0 α hFull P hα c)).toCC.homology n) := by
  classical
  refine finite_actualSelData_homology hloc hglob hS hSfin h2 W i α _ (fun v hv m => ?_) n
  have : Finite (ResMod (locMap K S v.1) (MinS hS W i α)) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i α))
  split
  · exact finite_cocycleCondition_homology hloc v.1 _ _ m
  · exact hc v hv ‹_› m

end ActualStage

section StandardConditions

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {A : Type}
  [CommRing A] {M : Type} [AddCommGroup M] [Module A M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) A M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- The zero condition has finite cohomology. -/
theorem finite_zeroAt_homology (v : Places K S) (n : ℤ) :
    Finite ((zeroAt K S A M v).U.toCC.homology n) :=
  finite_homology_of_finite_X _ n (inferInstanceAs (Finite PUnit))

/-- The Kummer condition with finite coefficients has finite cohomology (Milne I.2.1). -/
theorem finite_kummerAt_homology (hloc : MilneLocalFiniteness) [Finite M] (v : Places K S)
    [DecidableEq (v.1.adicCompletion K)] (B : WeierstrassCurve (v.1.adicCompletion K))
    [B.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t)
    (n : ℤ) : Finite ((kummerAt (k := A) v B m ι hι).U.toCC.homology n) := by
  have : Finite (ResMod (locMap K S v.1) M) := inferInstanceAs (Finite M)
  exact finite_cocycleCondition_homology hloc v.1 _ _ n

end StandardConditions

/-! ### Residual cohomology of the finite-level Kummer Selmer complexes -/

section ResidualKummer

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Manuscript.RC.KummerMaps

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The finite-level Kummer Selmer complexes have finite residual cohomology**
(`ResidualCohomologyFinite`, the hypothesis of the finite free models), for given conditions at
the other places of `S₀` with finite residual cohomology: `kummerSelData` is the actual stage
Selmer complex with the Kummer conditions at the places of `P`, which are cocycle conditions with
finite terms since `H¹(G_{K_v}, M_i)` is finite (Milne I.2.1). -/
theorem residualCohomologyFinite_kummerSelData (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (hSfin : S.Finite) (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (s : KS K S₀) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (α : GKS K S₀ →* (Acoef i)ˣ)
    (hFull : FullTorsion K S₀ W (2 ^ i)) [IsOpenKer α] (P : Set (HeightOneSpectrum (𝓞 K)))
    (hα : ∀ v ∈ P, IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → v.1 ∉ P → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v hv hP, ResidualCohomologyFinite (c v hv hP).U) :
    ResidualCohomologyFinite (selCx (kummerSelData hS W i s hs hs0 α hFull P hα c)) := by
  classical
  refine actualStageSelmer_residualCohomologyFinite hS W i α hloc hglob hSfin h2 _
    (fun v hv => ?_)
  have : Finite (ResMod (locMap K S v.1) (MinS hS W i α)) :=
    inferInstanceAs (Finite (Mcoef K S₀ W i α))
  by_cases hP : v.1 ∈ P
  · rw [dite_eq_left hP]
    exact residualCohomologyFinite_cocycleCondition _ _
      (hloc K v.1 (Acoef i) (ResMod (locMap K S v.1) (MinS hS W i α)) inferInstance 1)
  · rw [dite_eq_right hP]
    exact hc v hv hP

end ResidualKummer

/-! ### The central comparison with the finiteness input discharged -/

section CentralPlug

open Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.BaseZeroLimit
open ZInQ.Manuscript.RC53Assist.CentralUniversal

/-- **The central Selmer comparison with `KummerCohomologyFinite` discharged** by the printed
finiteness theorems: the remaining inputs are the coefficient comparison `I`, the support
condition `h2` and the retained model comparison `i`. -/
def centralSelmerComparisonOfPrints (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] (hk : ¬ IsSquare (k : ℚ))
    (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
    (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))
    (I : KummerCoefficientComparison ℓ k S hFull)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ S)
    {m : ℕ} (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (i : arithmeticRationalComplex ℓ k S hFull ⟶ scalarChangedComplex Rings.rhoT CU)
    [QuasiIsoAt i 1] :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm :=
  centralSelmerComparisonOfCompactKummer ℓ k hk S hFull I
    (kummerCohomologyFinite_of_comparison ℓ k S hFull hloc hglob I h2) Dm CU e1 e2 hzero hd i

/-- **The base-zero matrix rank with `KummerCohomologyFinite` discharged** by the printed
finiteness theorems. -/
theorem hcentral_of_prints (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] (hk : ¬ IsSquare (k : ℚ))
    (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
    (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))
    (I : KummerCoefficientComparison ℓ k S hFull)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ S)
    {m : ℕ} (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (i : arithmeticRationalComplex ℓ k S hFull ⟶ scalarChangedComplex Rings.rhoT CU)
    [QuasiIsoAt i 1] (hSel : SelmerCorankOneOverK ℓ k) :
    (Dm.map Rings.rhoT).rank = m :=
  hcentral_of_compactKummer ℓ k hk S hFull I
    (kummerCohomologyFinite_of_comparison ℓ k S hFull hloc hglob I h2) Dm CU e1 e2 hzero hd i hSel

end CentralPlug

end ZInQ.Contrib.RC53Assist.Finiteness
