import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.ActualZero
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionFamily

/-!
# An actual instance of `Identification3` with no new places (`Q = ∅`)

The fields of `Identification3` are filled with the genuine Galois objects of lane RC26
(`galoisSelData`, `galoisFullData`, `galoisFullSES` over the genuine groups `G_{K,S}`,
`G_{K_v}`), for

* `K = ℚ(ζ₄)` (totally complex, as Nekovář's finite setting requires for `p = 2`), the support
  `S` = the places over `2` together with one chosen place `v₀`, `S' = S` (no new places);
* `R₀ = 𝔽₂` with `ρ : Λ → 𝔽₂` (constant coefficient, then reduction), `p = 2`: Nekovář's finite
  setting holds (`hsetA`: `S` finite and containing the places over `2`, `K` totally complex,
  `𝔽₂` finite and self-injective, `2 = 0`);
* the cancellation core `fullCoreEx b (NewPlaces K S S)` (the old part `H₁ --0--> H₂`, no
  singular summands);
* the ZERO coefficient modules `M₀ = M_f = 0`: their global and local continuous cochains vanish,
  and the local conditions are the model complexes placed at `v₀` with the zero condition map
  (`atPlace`); then the genuine Selmer complexes are isomorphic to the models
  (`selModelMap`), which gives `ψf`, `ψ0`, `ψold` (isomorphisms) and the square.

`identification3Actual b : Identification3 K S S hS b 0 0 0 0` (PROVED, no hypotheses), and
`identification3QActual F hF : Identification3Q K S S hS F 0 0 0 0` for every family with `F.Q = ∅`
(the auxiliary one-place-per-prime variant `Identification3Q`, which is not the text's two-place
setting; at `Q = ∅` there are no new places, so the one- and two-place conditions are both empty).

CAVEAT. This witnesses the consistency of the interface with the genuine data types (genuine
groups, genuine cochain complexes, genuine full and unramified conditions, Nekovář's finite
setting), with zero coefficients and engineered local conditions; it carries no Galois-cohomological
content, and the tame field is vacuous (no new places).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (restrictData)
open ZInQ.Manuscript.RC.SelmerComplex (prodLift)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup)
open ZInQ.Manuscript.RC.SelmerComplex (GKS galoisSelData NewPlaces GaloisLocalConditions
  NekovarFiniteSetting Places natCx contCochains ResMod)

/-! ### Old inclusion of a complex without singular summands -/

namespace FullPreComplex

variable {R : Type} [CommRing R] {C : FullPreComplex R} [IsEmpty C.N]

theorem oinc_bijective (hY : C.Y = 0) (hT : C.T = 0) (n : ℤ) :
    Function.Bijective ((oldIncl hY hT).f n n rfl) := by
  change Function.Bijective (oinc hY hT n)
  match n with
  | 0 => exact Function.bijective_id
  | 1 =>
    refine ⟨fun a b h => inj_fromRows_one (m := C.D1) (0 : Matrix C.N C.D1 R) a b h, fun c => ?_⟩
    refine ⟨c ∘ Sum.inl, ?_⟩
    have h := exact_fromCols_one (0 : Matrix C.N C.D1 R) c (funext fun x => isEmptyElim x)
    rwa [neg_zero] at h
  | 2 =>
    refine ⟨fun a b h => inj_fromRows_one (m := C.D2) (0 : Matrix C.N C.D2 R) a b h, fun c => ?_⟩
    refine ⟨c ∘ Sum.inl, ?_⟩
    have h := exact_fromCols_one (0 : Matrix C.N C.D2 R) c (funext fun x => isEmptyElim x)
    rwa [neg_zero] at h
  | 3 => exact Function.bijective_id
  | Int.ofNat (k + 4) =>
    exact ⟨fun a b _ => Subsingleton.elim (α := Empty → R) a b,
      fun c => ⟨0, Subsingleton.elim (α := Empty → R) _ _⟩⟩
  | Int.negSucc k =>
    exact ⟨fun a b _ => Subsingleton.elim (α := Empty → R) a b,
      fun c => ⟨0, Subsingleton.elim (α := Empty → R) _ _⟩⟩

theorem isIso_oldIncl (hY : C.Y = 0) (hT : C.T = 0) :
    IsIso (SelmerDuality.GHom.toCC (oldIncl hY hT)) := by
  have : ∀ n, IsIso ((SelmerDuality.GHom.toCC (oldIncl hY hT)).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2 (oinc_bijective hY hT n)
  exact HomologicalComplex.Hom.isIso_of_components _

end FullPreComplex

/-! ### The number field and the support -/

namespace ActualQEmpty

/-- `K = ℚ(ζ₄)`. -/
abbrev KA : Type := CyclotomicField 4 ℚ

instance isCycKA : IsCyclotomicExtension {4} ℚ KA := CyclotomicField.isCyclotomicExtension 4 ℚ

instance numberFieldKA : NumberField KA := IsCyclotomicExtension.numberField {4} ℚ KA

theorem isTotallyComplexKA : IsTotallyComplex KA :=
  IsCyclotomicExtension.Rat.isTotallyComplex KA (n := 4) (by norm_num)

theorem exists_place : Nonempty (HeightOneSpectrum (𝓞 KA)) := by
  obtain ⟨p, hp, hpr⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField KA)
  exact ⟨⟨p, hpr, hp⟩⟩

/-- The chosen place `v₀`. -/
def v₀ : HeightOneSpectrum (𝓞 KA) := Classical.choice exists_place

/-- The support: the places over `2` and `v₀`. -/
def SA : Set (HeightOneSpectrum (𝓞 KA)) := {v | (2 : 𝓞 KA) ∈ v.asIdeal} ∪ {v₀}

theorem SA_finite : SA.Finite := by
  refine Set.Finite.union ?_ (Set.finite_singleton _)
  have h2 : Ideal.span {(2 : 𝓞 KA)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors h2).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

/-- `v₀` as a place of `S`. -/
def w₀ : Places KA SA := ⟨v₀, Or.inr rfl⟩

instance isEmptyNew : IsEmpty (NewPlaces KA SA SA) := ⟨fun x => x.2.2 x.2.1⟩

instance fintypeNew : Fintype (NewPlaces KA SA SA) := Fintype.ofIsEmpty

instance decEqNew : DecidableEq (NewPlaces KA SA SA) := fun a => isEmptyElim a

/-- `ρ : Λ → 𝔽₂`: constant coefficient, then reduction modulo `2`. -/
def ρA : Lam →+* ZMod 2 := PadicInt.toZMod.comp (PowerSeries.constantCoeff (R := ℤ_[2]))

/-- **Nekovář's finite setting holds** for `K = ℚ(ζ₄)`, `S`, `p = 2`, `R = 𝔽₂`. -/
theorem hsetA : NekovarFiniteSetting KA SA 2 (ZMod 2) where
  prime := Nat.prime_two
  finite_S := SA_finite
  above_p v hv := Or.inl (by simpa using hv)
  condP _ := isTotallyComplexKA
  finite_R := inferInstance
  nilpotent_p := ⟨1, by decide⟩
  selfInjective := Module.injective_of_isSemisimpleRing _ _

/-! ### The genuine Selmer data of the zero module with the model at `v₀` -/

variable (b : ℕ)

/-- The cancellation core (no singular summands). -/
abbrev coreA : FullCore (NewPlaces KA SA SA) b 0 0 0 0 := fullCoreEx b (NewPlaces KA SA SA)

/-- The family model `C ⊗ 𝒪[G]`. -/
abbrev famA : GCx (MonoidAlgebra OO (SignGroup b)) := ((coreA b).C.map (φO b)).toGCx

/-- The family local conditions: the family model at `v₀`, zero condition map. -/
def ΔfA : GaloisLocalConditions KA SA (MonoidAlgebra OO (SignGroup b)) PUnit :=
  ⟨fun v => atPlace w₀ (famA b) v, fun _ => zeroGHom _ _⟩

theorem subsingleton_G {k : Type} [CommRing k] (Δ : GaloisLocalConditions KA SA k PUnit) (n : ℤ) :
    Subsingleton ((galoisSelData KA SA k PUnit Δ).G.X n) :=
  subsingleton_natCx_contCochains (k := k) (G := GKS KA SA) (M := PUnit) n

theorem subsingleton_L {k : Type} [CommRing k] (Δ : GaloisLocalConditions KA SA k PUnit) (n : ℤ) :
    Subsingleton ((galoisSelData KA SA k PUnit Δ).L.X n) := by
  refine subsingleton_piCx _ (fun v m => ?_) n
  haveI : Subsingleton (ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap KA SA v.1) PUnit) :=
    inferInstanceAs (Subsingleton PUnit)
  exact subsingleton_natCx_contCochains m

/-- **`ψf`**: the family model into the genuine family Selmer complex (an isomorphism). -/
def ψfA : GHom (famA b) (selCx (galoisSelData KA SA _ PUnit (ΔfA b))) :=
  selModelMap (galoisSelData KA SA _ PUnit (ΔfA b)) (atPlaceMap w₀ (famA b))
    (subsingleton_G _) (subsingleton_L _)

theorem ψfA_quasiIso : QuasiIso (SelmerDuality.GHom.toCC (ψfA b)) :=
  bijGHom_quasiIso _ (selModelMap_bijective _ _ _ _ (atPlaceMap_bijective w₀ (famA b)))

/-! ### The augmented side over `𝔽₂` -/

theorem hSA : SA ⊆ SA := subset_refl _

/-- The augmented model modulo `ρ`. -/
abbrev CρA : FullPreComplex (ZMod 2) := ((coreA b).C.map (augR b)).map ρA

theorem hYρA : (CρA b).Y = 0 := FullPreComplex.map_Y_zero _ ρA (coreA b).hY0
theorem hTρA : (CρA b).T = 0 := FullPreComplex.map_T_zero _ ρA (coreA b).hT0

instance isEmptyCρN : IsEmpty (CρA b).N := inferInstanceAs (IsEmpty (Unit × NewPlaces KA SA SA))

/-- Its old part. -/
abbrev oldA : BlockComplex (ZMod 2) := (CρA b).old (hYρA b) (hTρA b)

/-- The old local conditions: the old model at `v₀`, zero condition map. -/
def Δ₀A : GaloisLocalConditions KA SA (ZMod 2) PUnit :=
  ⟨fun v => atPlace w₀ (oldA b).toGCx v, fun _ => zeroGHom _ _⟩

/-- No unramified factorizations are needed: there are no new places. -/
def ψurA : ∀ q : NewPlaces KA SA SA, ZInQ.Contrib.CloudB3RC53.RankCounts.GUr KA q.1 →ₜ* GKS KA SA :=
  fun q => isEmptyElim q

theorem hψurA : ∀ (q : NewPlaces KA SA SA) g,
    ZInQ.Manuscript.RC.SelmerComplex.locMap KA SA q.1 g =
      ψurA q (ZInQ.Manuscript.RC.SelmerComplex.urRes KA q.1 g) :=
  fun q => isEmptyElim q

/-- The genuine full-condition data. -/
abbrev fullA : SelData (ZMod 2) := galoisFullData KA hSA (ZMod 2) PUnit (Δ₀A b)

/-- The genuine unramified data (the first term of the genuine sequence of (5.6)). -/
abbrev urA : SelData (ZMod 2) :=
  restrictData (fullA b) (galoisUrInFull KA hSA (ZMod 2) PUnit ψurA hψurA (Δ₀A b))

theorem subsingleton_fullG (n : ℤ) : Subsingleton ((fullA b).G.X n) := by
  haveI : Subsingleton (ResMod (ZInQ.Manuscript.RC.SelmerComplex.inflMap KA hSA) PUnit) :=
    inferInstanceAs (Subsingleton PUnit)
  exact subsingleton_natCx_contCochains n

theorem subsingleton_fullL (n : ℤ) : Subsingleton ((fullA b).L.X n) := by
  refine ⟨fun x y => Prod.ext ?_ ?_⟩
  · refine (subsingleton_piCx _ (fun v m => ?_) n).elim _ _
    haveI : Subsingleton (ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap KA SA v.1)
        (ResMod (ZInQ.Manuscript.RC.SelmerComplex.inflMap KA hSA) PUnit)) :=
      inferInstanceAs (Subsingleton PUnit)
    exact subsingleton_natCx_contCochains m
  · exact funext fun q => isEmptyElim q

/-- The model into the full-condition local conditions. -/
def φfullA : GHom (oldA b).toGCx (fullA b).U :=
  prodLift (atPlaceMap w₀ (oldA b).toGCx) (zeroGHom _ _)

/-- The model into the unramified local conditions. -/
def φurA : GHom (oldA b).toGCx (urA b).U :=
  prodLift (atPlaceMap w₀ (oldA b).toGCx) (zeroGHom _ _)

theorem φfullA_bijective (n : ℤ) : Function.Bijective ((φfullA b).f n n rfl) := by
  refine ⟨fun x y h => (atPlaceMap_bijective w₀ _ n).1 (congrArg Prod.fst h), fun c => ?_⟩
  obtain ⟨x, hx⟩ := (atPlaceMap_bijective w₀ (oldA b).toGCx n).2 c.1
  exact ⟨x, Prod.ext hx (funext fun q => isEmptyElim q)⟩

theorem φurA_bijective (n : ℤ) : Function.Bijective ((φurA b).f n n rfl) := by
  refine ⟨fun x y h => (atPlaceMap_bijective w₀ _ n).1 (congrArg Prod.fst h), fun c => ?_⟩
  obtain ⟨x, hx⟩ := (atPlaceMap_bijective w₀ (oldA b).toGCx n).2 c.1
  exact ⟨x, Prod.ext hx (funext fun q => isEmptyElim q)⟩

/-- The old model into the genuine full-condition Selmer complex (an isomorphism). -/
def σfullA : GHom (oldA b).toGCx (selCx (fullA b)) :=
  selModelMap (fullA b) (φfullA b) (subsingleton_fullG b) (subsingleton_fullL b)

/-- **`ψold`**: the old model into the genuine unramified Selmer complex (an isomorphism). -/
def σurA : GHom (oldA b).toGCx (selCx (urA b)) :=
  selModelMap (urA b) (φurA b) (subsingleton_fullG b) (subsingleton_fullL b)

theorem σfullA_quasiIso : QuasiIso (SelmerDuality.GHom.toCC (σfullA b)) :=
  bijGHom_quasiIso _ (selModelMap_bijective _ _ _ _ (φfullA_bijective b))

theorem σurA_quasiIso : QuasiIso (SelmerDuality.GHom.toCC (σurA b)) :=
  bijGHom_quasiIso _ (selModelMap_bijective _ _ _ _ (φurA_bijective b))

instance isIso_oldInclA :
    IsIso (SelmerDuality.GHom.toCC (FullPreComplex.oldIncl (hYρA b) (hTρA b))) :=
  FullPreComplex.isIso_oldIncl _ _

/-- **`ψ0`**: the augmented model into the genuine full-condition Selmer complex. -/
def ψ0A : (CρA b).toGCx.toCC ⟶ (selCx (fullA b)).toCC :=
  inv (SelmerDuality.GHom.toCC (FullPreComplex.oldIncl (hYρA b) (hTρA b))) ≫
    SelmerDuality.GHom.toCC (σfullA b)

theorem ψ0A_quasiIso : QuasiIso (ψ0A b) := by
  have := σfullA_quasiIso b
  unfold ψ0A
  infer_instance

/-- **The square**: `ψold ≫ (C(ur) → C(full)) = oldIncl ≫ ψ0`. -/
theorem squareA :
    SelmerDuality.GHom.toCC (σurA b) ≫
        (galoisFullSES KA hSA (ZMod 2) PUnit ψurA hψurA (Δ₀A b)).f =
      SelmerDuality.GHom.toCC (FullPreComplex.oldIncl (hYρA b) (hTρA b)) ≫ ψ0A b := by
  unfold ψ0A
  rw [IsIso.hom_inv_id_assoc]
  change SelmerDuality.GHom.toCC (σurA b) ≫ SelmerDuality.GHom.toCC
      (SelmerDuality.changeMap (fullA b) (galoisUrInFull KA hSA (ZMod 2) PUnit ψurA hψurA (Δ₀A b))) =
    _
  rw [SelmerDuality.GHom.toCC_comp]
  refine SelmerDuality.GHom.toCC_ext fun i x => ?_
  refine Prod.ext rfl (Prod.ext (Prod.ext rfl (funext fun q => isEmptyElim q)) rfl)

/-! ### The instance -/

/-- **An actual instance of `Identification3`** over the genuine Galois objects with no new
places (PROVED; no hypotheses). See the module docstring for the caveat. -/
def identification3Actual : Identification3 KA SA SA hSA b 0 0 0 0 where
  toFullCore := coreA b
  Mf := PUnit
  Δf := ΔfA b
  hfull v hv := absurd v.2 hv
  ψf := SelmerDuality.GHom.toCC (ψfA b)
  qisf := ψfA_quasiIso b
  R₀ := ZMod 2
  ρ := ρA
  p := 2
  hset := hsetA
  hS' := SA_finite
  M₀ := PUnit
  ψur := ψurA
  hψur := hψurA
  Δ₀ := Δ₀A b
  ψ0 := ψ0A b
  qis0 := ψ0A_quasiIso b
  ψold := SelmerDuality.GHom.toCC (σurA b)
  qisOld := σurA_quasiIso b
  square := squareA b
  Φq q := isEmptyElim q
  qq q := isEmptyElim q
  qq_odd q := isEmptyElim q
  bas q := isEmptyElim q
  hA q := isEmptyElim q
  tame q := isEmptyElim q

theorem identification3_nonempty : Nonempty (Identification3 KA SA SA hSA b 0 0 0 0) :=
  ⟨identification3Actual b⟩

/-- **The auxiliary one-place-per-prime variant at `Q = ∅`**: for every family with no primes, an
actual `Identification3Q` (the new places, none, identified with `F.Q`). PROVED. `Identification3Q`
is not the text's family identification (the text has two conjugate places over each split prime,
tex 5247, 5456–5457; the text-faithful structure is the integration team's `Identification3Q2`);
at `Q = ∅` both have no new places. -/
def identification3QActual (F : ZInQ.Manuscript.RC.Family) (hF : F.Q = ∅) :
    Identification3Q KA SA SA hSA F 0 0 0 0 where
  toIdentification3 := identification3Actual F.b
  eQ := @Equiv.equivOfIsEmpty _ _ _ (by rw [hF]; exact inferInstanceAs (IsEmpty (∅ : Finset ℕ)))
  lies v := isEmptyElim v
  hqq v := isEmptyElim v

end ActualQEmpty

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
