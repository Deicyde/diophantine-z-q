import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Realization
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncPrints
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Selmer

/-!
# Arithmetic inputs of the retained inner-limit duality at the coefficient stages

The retained stage data of the inner limit (manuscript lines 4385–4451) need, at every finite
coefficient stage `A_i = (ℤ/2^i)[t]/t^i`, the following arithmetic inputs about the actual Galois
Selmer complexes. This file states them with exact types and proves those that follow from
results of the tree and from printed theorems cited by the manuscript.

* Finiteness of Galois cohomology with finite coefficients: `MilneLocalFiniteness` (PRINT,
  Milne, *Arithmetic duality theorems*, I, Theorem 2.1, p. 27; the manuscript cites I.2.3 at lines
  3442 and 4547) and `MilneGlobalFiniteness` (PRINT, Milne I, Corollary 4.15, p. 62; the manuscript
  cites I.4.10 at line 4526). From them, by the exact
  sequences of the Selmer cone, a shift and finite products, the cohomology of the actual Selmer
  complex with finite coefficients is finite (`galoisSelmerCohomologyFinite_of_prints`), in
  particular at every coefficient stage for the actual module `M_i`, which has two-power order
  (`card_mcoef_eq_two_pow`, `stageSelmerCohomologyFinite`). The shape in which the finite free
  models use finiteness is `ResidualCohomologyFinite`, the residual cohomology of a complex under
  the base change `gcxBaseChange` to the residue field.
* Chain-level reciprocity from the trace on the compact cone (`trace_reciprocity`): for global
  cochains of total degree two, the trace of the global cup product of their coboundaries equals
  minus the trace of the local cup product of their localizations; and the trace vanishes on the
  localization of a global two-cocycle (`trace_localization_of_cocycle`, the sum of the local
  invariants of a global class). These are the stage forms of the retained reciprocity of the
  limit pairing data.
* Nekovář's global duality at the stage `A_i` for the actual coefficient module `M_i`, its twist
  `M_i(α⁻¹)` and the Weil pairing into `A_i(1)`: existence of the trace (`exists_stageTrace`),
  the global duality quasi-isomorphism (`stageGlobalDuality`) and the Selmer duality
  quasi-isomorphism for orthogonal local conditions (`stageSelmerDuality`), from the prints
  `NekovarProp541T` and `NekovarProp543T` with every other hypothesis discharged for the actual
  data.
* The degree-two coordinate at a stage prime (`LocalDegreeTwoCoordinate`), which is the same as an
  isomorphism `H²(G, M) ≅ M` (`LocalDegreeTwoCoordinate.exists_equiv`), and its normalization by
  the cup product of the unramified and tame characters (`LocalDegreeTwoNormalized`).

Sources: the retained inner limit, manuscript lines 4385–4451; the local and global duality
inputs, lines 2761–2830, 3442–3463, 4526–4547; the derivative conditions, lines 4834–4907.
-/

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimitArith

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open scoped TensorProduct

/-! ### Finiteness of Galois cohomology with finite coefficients -/

section Finiteness

/-- **PRINT — Milne, *Arithmetic duality theorems*, 2nd ed., Chapter I, Theorem 2.1, last sentence
(p. 27)** (the manuscript cites Corollary 2.3, local duality, at lines 3442 and 4547): for a finite
place `v` of a number field and a finite discrete `G_{K_v}`-module `M`, the continuous cohomology
groups `H^n(K_v, M)` are finite. Stated for the continuous cochain complexes used by the Selmer
data. -/
def MilneLocalFiniteness : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (R : Type) [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] [DistribMulAction (Gloc K v) M]
    [SMulCommClass (Gloc K v) R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (Gloc K v) M], Finite M →
    ∀ n : ℤ, Finite ((natCx (contCochains R (Gloc K v) M)).toCC.homology n)

/-- **PRINT — Milne, *Arithmetic duality theorems*, 2nd ed., Chapter I, Corollary 4.15 (p. 62)**
(the manuscript cites Theorem 4.10, Poitou-Tate, at line 4526 with I.5.1): for a finite set `S` of
finite primes of a number field containing the primes dividing `#M`, and a finite discrete
`G_{K,S}`-module `M`, the continuous cohomology groups `H^n(G_{K,S}, M)` are finite. -/
def MilneGlobalFiniteness : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
      [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M] [TopologicalSpace M]
      [DiscreteTopology M] [ContinuousSMul (GKS K S) M], Finite M →
      (∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
      ∀ n : ℤ, Finite ((natCx (contCochains R (GKS K S) M)).toCC.homology n)

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (R : Type)
  [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) R M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The finiteness of the actual Selmer cohomology**: every cohomology group of the actual Galois
Selmer complex with local conditions `Δ` is finite. -/
def GaloisSelmerCohomologyFinite (Δ : GaloisLocalConditions K S R M) : Prop :=
  ∀ n : ℤ, Finite ((selCx (galoisSelData K S R M Δ)).toCC.homology n)

/-- The global cohomology of the actual Selmer data is finite under the global print. -/
theorem globalCohomology_finite (h : MilneGlobalFiniteness) (hS : S.Finite) [Finite M]
    (hM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) (n : ℤ) :
    Finite ((globalCx R (GKS K S) M).toCC.homology n) :=
  h K S hS R M inferInstance hM n

/-- The local cohomology of the actual Selmer data at every place is finite under the local
print. -/
theorem localCohomology_finite (h : MilneLocalFiniteness) [Finite M] (v : Places K S) (n : ℤ) :
    Finite ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M
      v).toCC.homology n) := by
  have : Finite (ResMod (locMap K S v.1) M) := inferInstanceAs (Finite M)
  exact h K v.1 R (ResMod (locMap K S v.1) M) inferInstance n

end Finiteness

/-! ### Residual complexes -/

section Residual

variable {A : Type} [CommRing A]

/-- **Base change of a relation-indexed complex** along `A → B`. -/
def gcxBaseChange (B : Type) [CommRing B] [Algebra A B] (C : GCx A) : GCx B where
  X n := ModuleCat.of B (B ⊗[A] C.X n)
  d i j h := (C.d i j h).baseChange B
  d_d i j k hij hjk x := by
    have h0 : C.d j k hjk ∘ₗ C.d i j hij = 0 := LinearMap.ext (C.d_d i j k hij hjk)
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h0, LinearMap.baseChange_zero,
      LinearMap.zero_apply]

variable [IsLocalRing A]

/-- **The residual cohomology of a complex is finite in every degree**: the hypothesis of the
finite free model of the retained inner-limit lemma for the stage complexes. -/
def ResidualCohomologyFinite (C : GCx A) : Prop :=
  ∀ n : ℤ, Module.Finite (IsLocalRing.ResidueField A)
    ((gcxBaseChange (IsLocalRing.ResidueField A) C).toCC.homology n)

end Residual

/-! ### Finiteness of cohomology along exact sequences, shifts and finite products -/

section FiniteHomology

variable {R : Type} [CommRing R]

/-- The subquotient `K / (B ∩ K)` of a module by two submodules. -/
abbrev subquot {X : Type} [AddCommGroup X] [Module R X] (B K : Submodule R X) : Type :=
  K ⧸ B.comap K.subtype

theorem finite_subquot_congr {X : Type} [AddCommGroup X] [Module R X] {B B' K K' : Submodule R X}
    (hB : B = B') (hK : K = K') : Finite (subquot B K) ↔ Finite (subquot B' K') := by
  subst hB hK
  rfl

/-- **The middle term of an exact sequence of modules with finite ends is finite.** -/
theorem finite_of_exact {S : ShortComplex (ModuleCat.{0} R)} (hS : S.Exact)
    (h₁ : Finite S.X₁) (h₃ : Finite S.X₃) : Finite S.X₂ := by
  rw [ShortComplex.moduleCat_exact_iff] at hS
  let s : S.X₃ → S.X₂ := fun z => Classical.epsilon fun x => S.g x = z
  have hs : ∀ x : S.X₂, S.g (s (S.g x)) = S.g x := fun x =>
    Classical.epsilon_spec (p := fun x' => S.g x' = S.g x) ⟨x, rfl⟩
  have hker : ∀ x : S.X₂, S.g (x - s (S.g x)) = 0 := by
    intro x
    rw [map_sub, hs, sub_self]
  choose y hy using fun x : S.X₂ => hS (x - s (S.g x)) (hker x)
  have := h₁
  have := h₃
  refine Finite.of_injective (fun x : S.X₂ => (S.g x, y x)) ?_
  intro x x' hxx'
  obtain ⟨hg, hyy⟩ := Prod.mk.inj hxx'
  have e : x - s (S.g x) = x' - s (S.g x') := by rw [← hy x, ← hy x', hyy]
  rw [hg] at e
  exact sub_left_injective e

/-- The homology of a short complex of modules is finite exactly when the cycles modulo the
boundaries are. -/
theorem finite_homology_iff_subquot (S : ShortComplex (ModuleCat.{0} R)) :
    Finite S.homology ↔ Finite (subquot (LinearMap.range S.f.hom) (LinearMap.ker S.g.hom)) := by
  have hr : LinearMap.range S.moduleCatToCycles =
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  constructor
  · intro h
    have : Finite (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
      Finite.of_equiv _ S.moduleCatHomologyIso.toLinearEquiv.toEquiv
    exact Finite.of_equiv _ (Submodule.quotEquivOfEq _ _ hr).toEquiv
  · intro h
    have h' : Finite (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
      Finite.of_equiv _ (Submodule.quotEquivOfEq _ _ hr).symm.toEquiv
    exact @Finite.of_equiv _ _ h' S.moduleCatHomologyIso.toLinearEquiv.symm.toEquiv

/-- **The cohomology of a relation-indexed complex in degree `n` is finite exactly when its
`n`-cocycles modulo `n`-coboundaries are.** -/
theorem finite_gcx_homology_iff (C : GCx R) (n : ℤ) :
    Finite (C.toCC.homology n) ↔
      Finite (subquot (LinearMap.range (C.d (n - 1) n (by omega)))
        (LinearMap.ker (C.d n (n + 1) rfl))) := by
  have e := C.toCC.homologyIsoSc' (n - 1) n (n + 1) (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n)
  have h1 : Finite (C.toCC.homology n) ↔ Finite ((C.toCC.sc' (n - 1) n (n + 1)).homology) :=
    ⟨fun h => Finite.of_equiv _ e.toLinearEquiv.toEquiv,
      fun h => Finite.of_equiv _ e.toLinearEquiv.symm.toEquiv⟩
  rw [h1, finite_homology_iff_subquot]
  have hf : (C.toCC.sc' (n - 1) n (n + 1)).f.hom = C.d (n - 1) n (by omega) :=
    LinearMap.ext fun x => GCx.toCC_d_hom C (n - 1) n (by omega) x
  have hg : (C.toCC.sc' (n - 1) n (n + 1)).g.hom = C.d n (n + 1) rfl :=
    LinearMap.ext fun x => GCx.toCC_d_hom C n (n + 1) rfl x
  exact finite_subquot_congr (by rw [hf]; rfl) (by rw [hg]; rfl)

/-- The kernel of a differential does not depend on the name of its target index. -/
theorem ker_d_congr (C : GCx R) {i j j' : ℤ} (h : i + 1 = j) (h' : i + 1 = j') :
    LinearMap.ker (C.d i j h) = LinearMap.ker (C.d i j' h') := by
  subst h
  subst h'
  rfl

/-- **Shifting down by one shifts the cohomology**: finiteness of `H^{n−1}(L)` gives finiteness
of `H^n(L[−1])`. -/
theorem finite_homology_shiftDown (L : GCx R) (n : ℤ) (h : Finite (L.toCC.homology (n - 1))) :
    Finite ((shiftDown L).toCC.homology n) := by
  rw [finite_gcx_homology_iff] at h ⊢
  have hB : LinearMap.range ((shiftDown L).d (n - 1) n (by omega)) =
      LinearMap.range (L.d (n - 1 - 1) (n - 1) (by omega)) := by
    change LinearMap.range (-(L.d (n - 1 - 1) (n - 1) (by omega))) = _
    exact LinearMap.range_neg _
  have hK : LinearMap.ker ((shiftDown L).d n (n + 1) rfl) =
      LinearMap.ker (L.d (n - 1) (n - 1 + 1) rfl) := by
    change LinearMap.ker (-(L.d (n - 1) (n + 1 - 1) (by omega))) = _
    rw [LinearMap.ker_neg]
    exact ker_d_congr L _ _
  exact (finite_subquot_congr hB hK).2 h

/-- **The cohomology of a finite product of complexes with finite cohomology is finite.** -/
theorem finite_homology_piCx {ι : Type} [Finite ι] (A : ι → GCx R) (n : ℤ)
    (h : ∀ v, Finite ((A v).toCC.homology n)) : Finite ((piCx A).toCC.homology n) := by
  rw [finite_gcx_homology_iff]
  have h' : ∀ v, Finite (subquot (LinearMap.range ((A v).d (n - 1) n (by omega)))
      (LinearMap.ker ((A v).d n (n + 1) rfl))) := fun v => (finite_gcx_homology_iff (A v) n).1 (h v)
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
  have hinj : Function.Injective (Submodule.liftQ _ Φ hle) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ Φ hle hker'
  have := h'
  exact Finite.of_injective _ hinj

end FiniteHomology

/-! ### Finiteness of the cohomology of the actual Selmer complexes -/

section SelmerFiniteness

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (R : Type)
  [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) R M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

/-- **The cohomology of the actual Selmer complex with finite coefficients is finite**, from the
local and global finiteness prints, for a finite `S` containing the primes dividing `#M` and local
conditions with finite cohomology: by the exact sequences
`H^n(Cone(U → L)[−1]) → H^n(C_U) → H^n(G_{K,S}, M)` and
`H^{n−1}(L) → H^n(Cone(U → L)[−1]) → H^n(U)`. -/
theorem galoisSelmerCohomologyFinite_of_prints (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hS : S.Finite) [Finite M]
    (hM : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Δ : GaloisLocalConditions K S R M) (hΔ : ∀ v n, Finite ((Δ.U v).toCC.homology n)) :
    GaloisSelmerCohomologyFinite K S R M Δ := by
  have : Finite (Places K S) := hS.to_subtype
  intro n
  have hG : Finite ((galoisSelData K S R M Δ).G.toCC.homology n) :=
    globalCohomology_finite K S R M hglob hS hM n
  have hL : Finite ((galoisSelData K S R M Δ).L.toCC.homology (n - 1)) :=
    finite_homology_piCx _ (n - 1) fun v => localCohomology_finite K S R M hloc v (n - 1)
  have hU : Finite ((galoisSelData K S R M Δ).U.toCC.homology n) :=
    finite_homology_piCx _ n fun v => hΔ v n
  have hC : Finite ((locCx (galoisSelData K S R M Δ)).toCC.homology n) :=
    finite_of_exact ((coneSES_shortExact (negι (galoisSelData K S R M Δ))).homology_exact₂ n)
      (finite_homology_shiftDown _ n hL) hU
  exact finite_of_exact ((sesTop_shortExact (galoisSelData K S R M Δ)).homology_exact₂ n) hC hG

end SelmerFiniteness

/-! ### Chain-level reciprocity from the trace on the compact cone -/

section Reciprocity

variable {R : Type} [CommRing R] {D D' : SelData R} (Q : SelPairData D D')
  (tr : (coneCx Q.resE).X 3 →ₗ[R] R) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)

include htr in
/-- **The trace vanishes on the localization of a global two-cocycle**: for a global two-cocycle of
the cup-product target, the trace of its localization is zero (the sum of the local invariants of
a global class). -/
theorem trace_localization_of_cocycle (z : Q.E.X 2) (hz : Q.E.d 2 3 rfl z = 0) :
    tr ((0, Q.resE.f 2 (3 - 1) (by omega) z) : coneT Q.resE 3) = 0 := by
  have h := htr ((z, 0) : coneT Q.resE 2)
  have e : (coneCx Q.resE).d 2 3 rfl ((z, 0) : coneT Q.resE 2) =
      ((0, Q.resE.f 2 (3 - 1) (by omega) z) : coneT Q.resE 3) := by
    change ((Q.E.d 2 3 rfl z, Q.resE.f 2 (3 - 1) (by omega) z -
      Q.EL.d (2 - 1) (3 - 1) (by omega) 0) : coneT Q.resE 3) = _
    rw [hz, map_zero, sub_zero]
  rw [e] at h
  exact h

include htr in
/-- **Chain-level reciprocity**: for global cochains `x` of degree `a` and `y` of degree `b` with
`a + b = 2`, the trace of the global cup products of their coboundaries and the trace of the local
cup product of their localizations satisfy
`tr(dx ∪ y) + (−1)^a tr(x ∪ dy) = −tr(res x ∪ res y)`. -/
theorem trace_reciprocity (a b : ℤ) (h : a + b = 2) (x : D.G.X a) (y : D'.G.X b) :
    tr ((Q.cupG.P (a + 1) b 3 (by omega) (D.G.d a (a + 1) rfl x) y, 0) : coneT Q.resE 3) +
        sgn a • tr ((Q.cupG.P a (b + 1) 3 (by omega) x (D'.G.d b (b + 1) rfl y), 0) :
          coneT Q.resE 3) =
      -tr ((0, Q.cupL.P a b (3 - 1) (by omega) (D.res.f a a rfl x) (D'.res.f b b rfl y)) :
        coneT Q.resE 3) := by
  have hd := htr ((Q.cupG.P a b 2 h x y, 0) : coneT Q.resE 2)
  have hleib := Q.cupG.leib a (a + 1) b (b + 1) 2 3 h rfl rfl rfl x y
  have hcomp := Q.compat a b 2 a b (3 - 1) h (by omega) rfl rfl (by omega) x y
  have e : (coneCx Q.resE).d 2 3 rfl ((Q.cupG.P a b 2 h x y, 0) : coneT Q.resE 2) =
      ((Q.cupG.P (a + 1) b 3 (by omega) (D.G.d a (a + 1) rfl x) y +
          sgn a • Q.cupG.P a (b + 1) 3 (by omega) x (D'.G.d b (b + 1) rfl y),
        Q.cupL.P a b (3 - 1) (by omega) (D.res.f a a rfl x) (D'.res.f b b rfl y)) :
          coneT Q.resE 3) := by
    change ((Q.E.d 2 3 rfl (Q.cupG.P a b 2 h x y),
      Q.resE.f 2 (3 - 1) (by omega) (Q.cupG.P a b 2 h x y) -
        Q.EL.d (2 - 1) (3 - 1) (by omega) 0) : coneT Q.resE 3) = _
    rw [map_zero, sub_zero, hleib, hcomp]
  rw [e] at hd
  let trP : (Q.E.X 3 × Q.EL.X (3 - 1)) →ₗ[R] R := tr
  have hsplit : ((Q.cupG.P (a + 1) b 3 (by omega) (D.G.d a (a + 1) rfl x) y +
        sgn a • Q.cupG.P a (b + 1) 3 (by omega) x (D'.G.d b (b + 1) rfl y),
      Q.cupL.P a b (3 - 1) (by omega) (D.res.f a a rfl x) (D'.res.f b b rfl y)) :
        Q.E.X 3 × Q.EL.X (3 - 1)) =
      ((Q.cupG.P (a + 1) b 3 (by omega) (D.G.d a (a + 1) rfl x) y, 0) +
        sgn a • ((Q.cupG.P a (b + 1) 3 (by omega) x (D'.G.d b (b + 1) rfl y), 0) :
          Q.E.X 3 × Q.EL.X (3 - 1)) +
        ((0, Q.cupL.P a b (3 - 1) (by omega) (D.res.f a a rfl x) (D'.res.f b b rfl y)) :
          Q.E.X 3 × Q.EL.X (3 - 1))) := by
    refine Prod.ext ?_ ?_
    · simp
    · simp
  change trP _ = 0 at hd
  rw [hsplit, map_add, map_add, map_zsmul] at hd
  change trP _ + sgn a • trP _ = -trP _
  rw [eq_neg_iff_add_eq_zero]
  exact hd

end Reciprocity

/-! ### Nekovář's global duality at the coefficient stages for the actual coefficients -/

section StageDuality

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S →* (Acoef i)ˣ)
  [IsOpenKer α] (hμ : HasRootsOfUnity K S (2 ^ i))

/-- **The trace on the compact cone exists at every stage** (Nekovář 5.4.1): for the actual
coefficient module `M_i`, its twist `M_i(α⁻¹)`, the Weil pairing into `A_i(1)` and any truncated
isotropy data of local conditions, there is a trace on the truncated compact cone killing
coboundaries and inducing `H³ ≅ A_i`. -/
theorem exists_stageTrace (h541 : NekovarProp541T K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (ΔA : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i α))
    (ΔB : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i (charInv α)))
    (I : GaloisTruncIsotropyData K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB) :
    ∃ (tr : (galoisCompactTT K S (Acoef i) (weilPairingData W i α hμ)
        (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I).X 3 →ₗ[Acoef i] Acoef i)
      (_ : ∀ z, tr ((galoisCompactTT K S (Acoef i) (weilPairingData W i α hμ)
        (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I).d 2 3 rfl z) = 0), InducesIsoH3 tr :=
  h541 S 2 (Acoef i) (nekovarFiniteSetting_acoef K hK S hSfin h2 i) (Mcoef K S W i α)
    (Mcoef K S W i (charInv α)) (Tate1 (Acoef i) hμ) (weilPairingData W i α hμ)
    (weilPairingM_smul W hμ (Acoef i) α) (isCyclotomicTwist_tate1 (Acoef i) hμ) ΔA ΔB I

/-- **Nekovář's global duality at the stage `A_i` for the actual coefficients** (5.4.3): the global
duality map `C(G_{K,S}, M_i) → Hom(C_c(G_{K,S}, M_i(α⁻¹)), A_i)[−3]` of the truncated pairing data
is a quasi-isomorphism, for a finite `S` containing the primes above `2` over which `E[2^i]` is
defined. -/
theorem stageGlobalDuality (h543 : NekovarProp543T K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hW : FullTorsion K S W (2 ^ i))
    (ΔA : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i α))
    (ΔB : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i (charInv α)))
    (I : GaloisTruncIsotropyData K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB)
    (tr : (galoisCompactTT K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (globalDualityMap (galoisPairDataT K S (Acoef i)
      (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I) tr htr)) :=
  h543 S 2 (Acoef i) (nekovarFiniteSetting_acoef K hK S hSfin h2 i) (Mcoef K S W i α)
    (Mcoef K S W i (charInv α)) (Tate1 (Acoef i) hμ) (weilPairingData W i α hμ)
    (weilPairingM_smul W hμ (Acoef i) α) (weilPairingM_bijective W hμ (Acoef i) α hW)
    (weilPairingM_flip_bijective W hμ (Acoef i) α hW) (isCyclotomicTwist_tate1 (Acoef i) hμ) ΔA
    ΔB I tr htr htr3

/-- **The Selmer duality at the stage `A_i` for the actual coefficients** (Nekovář 6.3.4): for
local conditions that are orthogonal complements with respect to the truncated isotropy data, the
Selmer duality map `C_U(M_i) → Hom(C_{U'}(M_i(α⁻¹)), A_i)[−3]` is a quasi-isomorphism. -/
theorem stageSelmerDuality (h543 : NekovarProp543T K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hW : FullTorsion K S W (2 ^ i))
    (ΔA : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i α))
    (ΔB : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i (charInv α)))
    (I : GaloisTruncIsotropyData K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB)
    (tr : (galoisCompactTT K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr)
    (horth : OrthogonalComplementsT K (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I tr htr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I) tr htr)) :=
  genuineSelmerDualityT K (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α) ΔA ΔB I
    tr htr h543 2 (nekovarFiniteSetting_acoef K hK S hSfin h2 i)
    (weilPairingM_bijective W hμ (Acoef i) α hW) (weilPairingM_flip_bijective W hμ (Acoef i) α hW)
    (isCyclotomicTwist_tate1 (Acoef i) hμ) htr3 horth

end StageDuality

/-! ### Finiteness of the cohomology of the actual stage Selmer complexes -/

section StageFiniteness

open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ)

omit [NumberField K] in
/-- **The actual stage coefficient module `M_i` has two-power order.** -/
theorem card_mcoef_eq_two_pow : ∃ k : ℕ, Nat.card (Mcoef K S W i α) = 2 ^ k := by
  have h0 : ((2 ^ i : ℕ) : Acoef i) = 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact acoef_two_pow_eq_zero i
  have hp : IsPGroup 2 (Multiplicative (Mcoef K S W i α)) := by
    intro g
    refine ⟨i, ?_⟩
    change Multiplicative.ofAdd ((2 ^ i) • Multiplicative.toAdd g) = Multiplicative.ofAdd 0
    congr 1
    rw [← Nat.cast_smul_eq_nsmul (Acoef i), h0]
    exact zero_smul (Acoef i) (Multiplicative.toAdd g : Mcoef K S W i α)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  exact ⟨n, hn⟩

variable [IsOpenKer α]

/-- **The cohomology of the actual stage Selmer complexes is finite** (from the finiteness prints):
for the actual coefficient module `M_i`, a finite `S` containing the primes above `2`, and local
conditions with finite cohomology, every cohomology group of the Selmer complex is finite. -/
theorem stageSelmerCohomologyFinite (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hSfin : S.Finite) (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (Δ : GaloisLocalConditions K S (Acoef i) (Mcoef K S W i α))
    (hΔ : ∀ v n, Finite ((Δ.U v).toCC.homology n)) :
    GaloisSelmerCohomologyFinite K S (Acoef i) (Mcoef K S W i α) Δ := by
  obtain ⟨k, hk⟩ := card_mcoef_eq_two_pow W i α
  refine galoisSelmerCohomologyFinite_of_prints K S (Acoef i) (Mcoef K S W i α) hloc hglob hSfin
    ?_ Δ hΔ
  intro v hv
  rw [hk, Nat.cast_pow, Nat.cast_ofNat] at hv
  exact h2 v (v.isPrime.mem_of_pow_mem k hv)

end StageFiniteness

/-! ### The degree-two coordinate at a stage prime -/

section DegreeTwo

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

/-- **The degree-two coordinate of the local complex at a stage prime**: an `R`-linear map
`c₂ : C²_cont(G, M) → M` killing coboundaries, whose kernel on two-cocycles consists of
coboundaries, and which is onto on two-cocycles; that is, `c₂` induces `H²(G, M) ≅ M`. This is the
`D²` coordinate of the split local model (manuscript lines 4860–4868). -/
def LocalDegreeTwoCoordinate (c₂ : (contCochains R G M).X 2 →ₗ[R] M) : Prop :=
  (∀ a, c₂ (((contCochains R G M).d 1 2).hom a) = 0) ∧
    (∀ z, ((contCochains R G M).d 2 3).hom z = 0 → c₂ z = 0 →
      ∃ a, ((contCochains R G M).d 1 2).hom a = z) ∧
    ∀ m : M, ∃ z, ((contCochains R G M).d 2 3).hom z = 0 ∧ c₂ z = m

/-- **The normalization of the degree-two coordinate by the tame cup product**: for additive
characters `u, κ : G → R` (the unramified and the tame Kummer characters) and every `m : M`, the
cup-product cocycle `(g, h) ↦ u(g) κ(h) m` has coordinate `m`. This orients the `D²` coordinate
against the tame coordinates of degree one. -/
def LocalDegreeTwoNormalized (c₂ : (contCochains R G M).X 2 →ₗ[R] M) (u κ : G → R) : Prop :=
  ∀ (m : M) (z : (contCochains R G M).X 2),
    (∀ g h : G, evalTwo R M g h z = (u g * κ h) • m) → c₂ z = m

/-- **A degree-two coordinate is an isomorphism `H²(G, M) ≅ M`**: it descends to a linear
equivalence from two-cocycles modulo two-coboundaries onto `M`. -/
theorem LocalDegreeTwoCoordinate.exists_equiv {c₂ : (contCochains R G M).X 2 →ₗ[R] M}
    (hc : LocalDegreeTwoCoordinate c₂) :
    ∃ e : subquot (LinearMap.range ((contCochains R G M).d 1 2).hom)
        (LinearMap.ker ((contCochains R G M).d 2 3).hom) ≃ₗ[R] M,
      ∀ z : LinearMap.ker ((contCochains R G M).d 2 3).hom,
        e (Submodule.Quotient.mk z) = c₂ (z : (contCochains R G M).X 2) := by
  obtain ⟨h1, h2, h3⟩ := hc
  let f : LinearMap.ker ((contCochains R G M).d 2 3).hom →ₗ[R] M :=
    c₂ ∘ₗ (LinearMap.ker ((contCochains R G M).d 2 3).hom).subtype
  have hle : (LinearMap.range ((contCochains R G M).d 1 2).hom).comap
      (LinearMap.ker ((contCochains R G M).d 2 3).hom).subtype ≤ LinearMap.ker f := by
    rintro z ⟨a, ha⟩
    rw [LinearMap.mem_ker]
    change c₂ (z : (contCochains R G M).X 2) = 0
    have ha' : ((contCochains R G M).d 1 2).hom a = (z : (contCochains R G M).X 2) := ha
    rw [← ha']
    exact h1 a
  have hker : LinearMap.ker f ≤ (LinearMap.range ((contCochains R G M).d 1 2).hom).comap
      (LinearMap.ker ((contCochains R G M).d 2 3).hom).subtype := by
    intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨a, ha⟩ := h2 (z : (contCochains R G M).X 2) z.2 hz
    exact ⟨a, ha⟩
  have hinj : Function.Injective (Submodule.liftQ _ f hle) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ f hle hker
  have hsurj : Function.Surjective (Submodule.liftQ _ f hle) := by
    intro m
    obtain ⟨z, hz, hzm⟩ := h3 m
    exact ⟨Submodule.Quotient.mk ⟨z, hz⟩, hzm⟩
  exact ⟨LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩, fun z => rfl⟩

end DegreeTwo

end ZInQ.Contrib.RC53Assist.InnerLimitArith
