import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.ActualQEmpty
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization

/-!
# An actual instance of `Identification3` with one new place

As `ActualQEmpty.lean`, over `K = ℚ(ζ₄)`, `R₀ = 𝔽₂`, `p = 2`, with zero coefficient modules, but
with a NONEMPTY set of new places:

* `S` = the places over `2`, `S' = S ∪ {v₃}` for a place `v₃` over `3` (`v₃ ∉ S`), so
  `S' − S = {v₃}`; the places exist since `2`, `3` are not units of `𝓞 K` (norm `> 1`);
* the genuine unramified factorization at `v₃` is lane RC26's PROVED `urFactor`;
* the family local conditions are full at `v₃` (`hfull`: the zero condition map between vanishing
  complexes is bijective there);
* the cancellation core has an empty local block at `v₃` (`ι = ∅`, `det = 1 = X⁰·1 + 2·0`);
* the tame field at `v₃`: the tame model of the zero module is quasi-isomorphic to the genuine
  local and unramified complexes of the zero module (all terms vanish).

`identification3OnePlace b : Identification3 K S S' hS b 0 0 0 0` (PROVED, no hypotheses).

This instance is of the place-indexed `Identification3` only. It does not instantiate the text's
family identification: there each prime `q` of the family contributes the two conjugate places over
it (tex 5247, 5456–5457), whereas here a single place `v₃` over `3` is added (and `3` is not
claimed to be split, nor to be a prime of any family).

CAVEAT. Zero coefficients: as in `ActualQEmpty.lean`, this witnesses the consistency of the
interface with the genuine data (genuine groups, genuine cochains, genuine full and unramified
conditions, a genuine unramified factorization, Nekovář's finite setting) with one new place, not
any Galois-cohomological content.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (restrictData)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup aug)
open ZInQ.Manuscript.RC.SelmerComplex (GKS galoisSelData NewPlaces GaloisLocalConditions
  NekovarFiniteSetting Places natCx contCochains ResMod prodLift urFactor urFactor_spec locMap
  inflMap piCx natHom)
open ActualQEmpty (KA ρA)

namespace ActualOnePlace

/-! ### The places -/

theorem not_isUnit_natCast (n : ℕ) (hn : 2 ≤ n) : ¬ IsUnit (n : 𝓞 KA) := by
  rw [NumberField.isUnit_iff_norm]
  have h : ((RingOfIntegers.norm ℚ (n : 𝓞 KA) : 𝓞 ℚ) : ℚ) = (n : ℚ) ^ Module.finrank ℚ KA := by
    have e : ((n : 𝓞 KA) : KA) = algebraMap ℚ KA (n : ℚ) := by simp
    rw [RingOfIntegers.coe_norm, e, Algebra.norm_algebraMap]
  rw [h, abs_pow, Nat.abs_cast]
  have hd : 0 < Module.finrank ℚ KA := Module.finrank_pos
  have : (1 : ℚ) < (n : ℚ) ^ Module.finrank ℚ KA :=
    one_lt_pow₀ (by exact_mod_cast hn) hd.ne'
  exact this.ne'

theorem exists_place_natCast (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : HeightOneSpectrum (𝓞 KA), (n : 𝓞 KA) ∈ v.asIdeal := by
  have hne : Ideal.span {(n : 𝓞 KA)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact not_isUnit_natCast n hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hn0 : (n : 𝓞 KA) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨⟨M, hM.isPrime, fun hb => hn0 ?_⟩, hle (Ideal.mem_span_singleton_self _)⟩
  have := hle (Ideal.mem_span_singleton_self (n : 𝓞 KA))
  rwa [hb, Ideal.mem_bot] at this

/-- A place over `2`. -/
def v₂ : HeightOneSpectrum (𝓞 KA) := Classical.choose (exists_place_natCast 2 le_rfl)

/-- A place over `3`. -/
def v₃ : HeightOneSpectrum (𝓞 KA) := Classical.choose (exists_place_natCast 3 (by norm_num))

theorem two_mem_v₂ : (2 : 𝓞 KA) ∈ v₂.asIdeal := by
  have := Classical.choose_spec (exists_place_natCast 2 le_rfl)
  simp only [Nat.cast_ofNat] at this
  exact this

theorem three_mem_v₃ : (3 : 𝓞 KA) ∈ v₃.asIdeal := by
  have := Classical.choose_spec (exists_place_natCast 3 (by norm_num))
  simp only [Nat.cast_ofNat] at this
  exact this

/-- The old support: the places over `2`. -/
def S₂ : Set (HeightOneSpectrum (𝓞 KA)) := {v | (2 : 𝓞 KA) ∈ v.asIdeal}

/-- The new support `S₂ ∪ {v₃}`. -/
def S₂' : Set (HeightOneSpectrum (𝓞 KA)) := S₂ ∪ {v₃}

theorem hS₂ : S₂ ⊆ S₂' := Set.subset_union_left

theorem v₃_not_mem : v₃ ∉ S₂ := by
  intro h
  have h2 : (2 : 𝓞 KA) ∈ v₃.asIdeal := h
  have h1 : (1 : 𝓞 KA) ∈ v₃.asIdeal := by
    have := v₃.asIdeal.sub_mem three_mem_v₃ h2
    norm_num at this
    exact this
  exact v₃.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem S₂_finite : S₂.Finite := by
  have h2 : Ideal.span {(2 : 𝓞 KA)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  exact (Ideal.finite_factors h2).subset fun v hv => Ideal.dvd_span_singleton.2 hv

theorem S₂'_finite : S₂'.Finite := S₂_finite.union (Set.finite_singleton _)

instance fintypeNew : Fintype (NewPlaces KA S₂ S₂') :=
  (S₂'_finite.subset Set.sdiff_subset).fintype

instance decEqNew : DecidableEq (NewPlaces KA S₂ S₂') := Classical.decEq _

/-- The new place `v₃`. -/
def q₃ : NewPlaces KA S₂ S₂' := ⟨v₃, Or.inr rfl, v₃_not_mem⟩

theorem nonempty_new : Nonempty (NewPlaces KA S₂ S₂') := ⟨q₃⟩

/-- `v₂` as an old place. -/
def w₂ : Places KA S₂ := ⟨v₂, two_mem_v₂⟩

/-- `v₂` as a place of the new support. -/
def w₂' : Places KA S₂' := ⟨v₂, Or.inl two_mem_v₂⟩

theorem hsetB : NekovarFiniteSetting KA S₂ 2 (ZMod 2) where
  prime := Nat.prime_two
  finite_S := S₂_finite
  above_p v hv := by
    change (2 : 𝓞 KA) ∈ v.asIdeal
    simpa using hv
  condP _ := ActualQEmpty.isTotallyComplexKA
  finite_R := inferInstance
  nilpotent_p := ⟨1, by decide⟩
  selfInjective := Module.injective_of_isSemisimpleRing _ _

/-! ### The cancellation core with an empty local block -/

variable (b : ℕ)

/-- The family model: old part `H₁ --0--> H₂`, no singular summands (empty local block at `v₃`). -/
def preB : FullPreComplex (MonoidAlgebra Lam (SignGroup b)) where
  m0 := 0
  m1 := 0
  m2 := 0
  N := Empty × NewPlaces KA S₂ S₂'
  c0 := 0
  Y := 0
  P := 0
  Q := 0
  T := 0
  B := 0
  U := 0
  V := 0
  c1_c0 := by simp
  c2_c1 := by simp

theorem central_fullB :
    let D := ((preB b).map (augR b)).old (Matrix.map_zero _ (map_zero _))
      (Matrix.map_zero _ (map_zero _))
    D.d0.map PowerSeries.constantCoeff =
        (smithForm (preB b).m0 (preB b).m1 (preB b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d0 ∧
      D.d1.map PowerSeries.constantCoeff =
        (smithForm (preB b).m0 (preB b).m1 (preB b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d1 ∧
      D.d2.map PowerSeries.constantCoeff =
        (smithForm (preB b).m0 (preB b).m1 (preB b).m2 (fun _ => 1) (fun _ => 1)
          (fun _ => 1)).d2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; exact j.elim0
  · ext (i | i | i) (j | j | j)
    all_goals first | exact i.elim0 | exact j.elim0 | rfl
  · ext i j; exact i.elim0

/-- **The cancellation core with one new place and an empty local block.** -/
def coreB : FullCore (NewPlaces KA S₂ S₂') b 0 0 0 0 where
  ιn := Empty
  A := fun _ => 0
  dq := fun _ => 0
  hd := fun _ => by norm_num
  v := fun _ => 1
  w := fun _ => 0
  hdet := fun _ => by simp
  C := preB b
  eN := Equiv.refl _
  hB0 := Matrix.ext fun i => isEmptyElim i.1
  hT0 := Matrix.map_zero _ (map_zero _)
  hY0 := Matrix.map_zero _ (map_zero _)
  s := fun _ _ => 1
  s_ne := fun _ _ => one_ne_zero
  central_full := central_fullB b
  budget := budgetInputs_of_empty _ rfl fun i => by rcases i with _ | _ | _ | i <;> rfl

/-! ### Vanishing complexes -/

theorem bijective_of_subsingleton {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) (hA : Subsingleton A) (hB : Subsingleton B) :
    Function.Bijective f :=
  ⟨fun a a' _ => hA.elim a a', fun y => ⟨0, hB.elim _ _⟩⟩

theorem subsingleton_tLX {R : Type} [CommRing R] (n : ℤ) :
    Subsingleton (tLX R PUnit n) := by
  match n with
  | 0 => exact (inferInstance : Subsingleton PUnit)
  | 1 => exact (inferInstance : Subsingleton (PUnit × PUnit))
  | 2 => exact (inferInstance : Subsingleton PUnit)
  | Int.ofNat (k + 3) => exact (inferInstance : Subsingleton PUnit)
  | Int.negSucc k => exact (inferInstance : Subsingleton PUnit)

theorem subsingleton_tUX {R : Type} [CommRing R] (n : ℤ) :
    Subsingleton (tUX R PUnit n) := by
  match n with
  | 0 => exact (inferInstance : Subsingleton PUnit)
  | 1 => exact (inferInstance : Subsingleton PUnit)
  | Int.ofNat (k + 2) => exact (inferInstance : Subsingleton PUnit)
  | Int.negSucc k => exact (inferInstance : Subsingleton PUnit)

/-! ### The genuine Selmer data of the zero module -/

/-- The family model `C ⊗ 𝒪[G]`. -/
abbrev famB : GCx (MonoidAlgebra OO (SignGroup b)) := ((coreB b).C.map (φO b)).toGCx

/-- The family local conditions over `S'`: the family model at `v₂`, zero condition map. -/
def ΔfB : GaloisLocalConditions KA S₂' (MonoidAlgebra OO (SignGroup b)) PUnit :=
  ⟨fun v => atPlace w₂' (famB b) v, fun _ => zeroGHom _ _⟩

theorem subsingleton_famG (n : ℤ) :
    Subsingleton ((galoisSelData KA S₂' (MonoidAlgebra OO (SignGroup b)) PUnit (ΔfB b)).G.X n) :=
  subsingleton_natCx_contCochains (k := MonoidAlgebra OO (SignGroup b)) (G := GKS KA S₂')
    (M := PUnit) n

theorem subsingleton_famL (n : ℤ) :
    Subsingleton ((galoisSelData KA S₂' (MonoidAlgebra OO (SignGroup b)) PUnit (ΔfB b)).L.X n) := by
  refine subsingleton_piCx _ (fun v m => ?_) n
  haveI : Subsingleton (ResMod (locMap KA S₂' v.1) PUnit) := inferInstanceAs (Subsingleton PUnit)
  exact subsingleton_natCx_contCochains m

/-- The family local conditions are full at the new place. -/
theorem hfullB : ∀ v : Places KA S₂', v.1 ∉ S₂ →
    ∀ n : ℤ, Function.Bijective (((ΔfB b).i v).f n n rfl) := by
  intro v hv n
  refine bijective_of_subsingleton _ ⟨fun x y => funext fun e => ?_⟩ ?_
  · exact absurd (congrArg Subtype.val e.down ▸ two_mem_v₂) hv
  · haveI : Subsingleton (ResMod (locMap KA S₂' v.1) PUnit) := inferInstanceAs (Subsingleton PUnit)
    exact subsingleton_natCx_contCochains n

/-- **`ψf`** (an isomorphism). -/
def ψfB : GHom (famB b) (selCx (galoisSelData KA S₂' _ PUnit (ΔfB b))) :=
  selModelMap _ (atPlaceMap w₂' (famB b)) (subsingleton_famG b) (subsingleton_famL b)

theorem ψfB_quasiIso : QuasiIso (SelmerDuality.GHom.toCC (ψfB b)) :=
  bijGHom_quasiIso _ (selModelMap_bijective _ _ _ _ (atPlaceMap_bijective w₂' (famB b)))

/-! ### The augmented side over `𝔽₂` -/

/-- The augmented model modulo `ρ`. -/
abbrev CρB : FullPreComplex (ZMod 2) := ((coreB b).C.map (augR b)).map ρA

theorem hYρB : (CρB b).Y = 0 := FullPreComplex.map_Y_zero _ ρA (coreB b).hY0
theorem hTρB : (CρB b).T = 0 := FullPreComplex.map_T_zero _ ρA (coreB b).hT0

instance isEmptyCρN : IsEmpty (CρB b).N :=
  inferInstanceAs (IsEmpty (Empty × NewPlaces KA S₂ S₂'))

/-- Its old part. -/
abbrev oldB : BlockComplex (ZMod 2) := (CρB b).old (hYρB b) (hTρB b)

/-- The old local conditions: the old model at `v₂`, zero condition map. -/
def Δ₀B : GaloisLocalConditions KA S₂ (ZMod 2) PUnit :=
  ⟨fun v => atPlace w₂ (oldB b).toGCx v, fun _ => zeroGHom _ _⟩

/-- The genuine unramified factorization at the new place (lane RC26, PROVED). -/
def ψurB : ∀ q : NewPlaces KA S₂ S₂', ZInQ.Contrib.CloudB3RC53.RankCounts.GUr KA q.1 →ₜ* GKS KA S₂ :=
  fun q => urFactor KA q

theorem hψurB : ∀ (q : NewPlaces KA S₂ S₂') g,
    locMap KA S₂ q.1 g = ψurB q (ZInQ.Manuscript.RC.SelmerComplex.urRes KA q.1 g) :=
  fun q g => urFactor_spec KA q g

/-- The genuine full-condition data. -/
abbrev fullB : SelData (ZMod 2) := galoisFullData KA hS₂ (ZMod 2) PUnit (Δ₀B b)

/-- The genuine unramified data. -/
abbrev urB : SelData (ZMod 2) :=
  restrictData (fullB b) (galoisUrInFull KA hS₂ (ZMod 2) PUnit ψurB hψurB (Δ₀B b))

theorem subsingleton_fullG (n : ℤ) : Subsingleton ((fullB b).G.X n) := by
  haveI : Subsingleton (ResMod (inflMap KA hS₂) PUnit) := inferInstanceAs (Subsingleton PUnit)
  exact subsingleton_natCx_contCochains n

theorem subsingleton_newL (n : ℤ) :
    Subsingleton ((piCx fun q : NewPlaces KA S₂ S₂' =>
      natCx (contCochains (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.Gloc KA q.1)
        (ResMod (locMap KA S₂' q.1) (ResMod (inflMap KA hS₂) PUnit)))).X n) := by
  refine subsingleton_piCx _ (fun q m => ?_) n
  haveI : Subsingleton (ResMod (locMap KA S₂' q.1) (ResMod (inflMap KA hS₂) PUnit)) :=
    inferInstanceAs (Subsingleton PUnit)
  exact subsingleton_natCx_contCochains m

theorem subsingleton_newU (n : ℤ) :
    Subsingleton ((piCx fun q : NewPlaces KA S₂ S₂' =>
      natCx (contCochains (ZMod 2) (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr KA q.1)
        (ResMod (ψurB q) PUnit))).X n) := by
  refine subsingleton_piCx _ (fun q m => ?_) n
  haveI : Subsingleton (ResMod (ψurB q) PUnit) := inferInstanceAs (Subsingleton PUnit)
  exact subsingleton_natCx_contCochains m

theorem subsingleton_fullL (n : ℤ) : Subsingleton ((fullB b).L.X n) := by
  refine ⟨fun x y => Prod.ext ?_ ((subsingleton_newL n).elim _ _)⟩
  refine (subsingleton_piCx _ (fun v m => ?_) n).elim _ _
  haveI : Subsingleton (ResMod (locMap KA S₂' v.1) (ResMod (inflMap KA hS₂) PUnit)) :=
    inferInstanceAs (Subsingleton PUnit)
  exact subsingleton_natCx_contCochains m

def φfullB : GHom (oldB b).toGCx (fullB b).U :=
  prodLift (atPlaceMap w₂ (oldB b).toGCx) (zeroGHom _ _)

def φurB : GHom (oldB b).toGCx (urB b).U :=
  prodLift (atPlaceMap w₂ (oldB b).toGCx) (zeroGHom _ _)

theorem φfullB_bijective (n : ℤ) : Function.Bijective ((φfullB b).f n n rfl) := by
  refine ⟨fun x y h => (atPlaceMap_bijective w₂ _ n).1 (congrArg Prod.fst h), fun c => ?_⟩
  obtain ⟨x, hx⟩ := (atPlaceMap_bijective w₂ (oldB b).toGCx n).2 c.1
  exact ⟨x, Prod.ext hx ((subsingleton_newL n).elim _ _)⟩

theorem φurB_bijective (n : ℤ) : Function.Bijective ((φurB b).f n n rfl) := by
  refine ⟨fun x y h => (atPlaceMap_bijective w₂ _ n).1 (congrArg Prod.fst h), fun c => ?_⟩
  obtain ⟨x, hx⟩ := (atPlaceMap_bijective w₂ (oldB b).toGCx n).2 c.1
  exact ⟨x, Prod.ext hx ((subsingleton_newU n).elim _ _)⟩

def σfullB : GHom (oldB b).toGCx (selCx (fullB b)) :=
  selModelMap (fullB b) (φfullB b) (subsingleton_fullG b) (subsingleton_fullL b)

def σurB : GHom (oldB b).toGCx (selCx (urB b)) :=
  selModelMap (urB b) (φurB b) (subsingleton_fullG b) (subsingleton_fullL b)

theorem σfullB_quasiIso : QuasiIso (SelmerDuality.GHom.toCC (σfullB b)) :=
  bijGHom_quasiIso _ (selModelMap_bijective _ _ _ _ (φfullB_bijective b))

theorem σurB_quasiIso : QuasiIso (SelmerDuality.GHom.toCC (σurB b)) :=
  bijGHom_quasiIso _ (selModelMap_bijective _ _ _ _ (φurB_bijective b))

instance isIso_oldInclB :
    IsIso (SelmerDuality.GHom.toCC (FullPreComplex.oldIncl (hYρB b) (hTρB b))) :=
  FullPreComplex.isIso_oldIncl _ _

def ψ0B : (CρB b).toGCx.toCC ⟶ (selCx (fullB b)).toCC :=
  inv (SelmerDuality.GHom.toCC (FullPreComplex.oldIncl (hYρB b) (hTρB b))) ≫
    SelmerDuality.GHom.toCC (σfullB b)

theorem ψ0B_quasiIso : QuasiIso (ψ0B b) := by
  have := σfullB_quasiIso b
  unfold ψ0B
  infer_instance

theorem squareB :
    SelmerDuality.GHom.toCC (σurB b) ≫
        (galoisFullSES KA hS₂ (ZMod 2) PUnit ψurB hψurB (Δ₀B b)).f =
      SelmerDuality.GHom.toCC (FullPreComplex.oldIncl (hYρB b) (hTρB b)) ≫ ψ0B b := by
  unfold ψ0B
  rw [IsIso.hom_inv_id_assoc]
  change SelmerDuality.GHom.toCC (σurB b) ≫ SelmerDuality.GHom.toCC
      (SelmerDuality.changeMap (fullB b) (galoisUrInFull KA hS₂ (ZMod 2) PUnit ψurB hψurB (Δ₀B b))) =
    _
  rw [SelmerDuality.GHom.toCC_comp]
  refine SelmerDuality.GHom.toCC_ext fun i x => ?_
  exact Prod.ext rfl (Prod.ext (Prod.ext rfl ((subsingleton_newL i).elim _ _)) rfl)

/-! ### The tame field at the new place -/

/-- The tame model of the zero module is a quasi-isomorphic model of the genuine local and
unramified complexes of the zero module at `q` (all terms vanish). -/
def tameB (q : NewPlaces KA S₂ S₂') : TameModelQIso PUnit (0 : PUnit →ₗ[ZMod 2] PUnit) 1
    (natCx (contCochains (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.Gloc KA q.1)
      (ResMod (locMap KA S₂' q.1) (ResMod (inflMap KA hS₂) PUnit))))
    (natCx (contCochains (ZMod 2) (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr KA q.1)
      (ResMod (ψurB q) PUnit)))
    (natHom (ZInQ.Manuscript.RC.SelmerComplex.urCond (k := ZMod 2) (GS := GKS KA S₂)
      (GS' := GKS KA S₂') (M := PUnit) (infl := inflMap KA hS₂)
      (Gq := fun q : NewPlaces KA S₂ S₂' => ZInQ.Manuscript.RC.SelmerComplex.Gloc KA q.1)
      (locq := fun q => locMap KA S₂' q.1)
      (Gur := fun q : NewPlaces KA S₂ S₂' => ZInQ.Contrib.CloudB3RC53.RankCounts.GUr KA q.1)
      (π := fun q => ZInQ.Manuscript.RC.SelmerComplex.urRes KA q.1) (ψ := ψurB)
      (fun q g => (ZInQ.Manuscript.RC.SelmerComplex.locMap_compat KA hS₂ q.1 g).trans
        (hψurB q g)) q)) where
  fL := SelmerDuality.GHom.toCC (zeroGHom _ _)
  fU := SelmerDuality.GHom.toCC (zeroGHom _ _)
  qisL := by
    refine bijGHom_quasiIso _ fun n => bijective_of_subsingleton _ (subsingleton_tLX n) ?_
    haveI : Subsingleton (ResMod (locMap KA S₂' q.1) (ResMod (inflMap KA hS₂) PUnit)) :=
      inferInstanceAs (Subsingleton PUnit)
    exact subsingleton_natCx_contCochains n
  qisU := by
    refine bijGHom_quasiIso _ fun n => bijective_of_subsingleton _ (subsingleton_tUX n) ?_
    haveI : Subsingleton (ResMod (ψurB q) PUnit) := inferInstanceAs (Subsingleton PUnit)
    exact subsingleton_natCx_contCochains n
  comm := by
    rw [SelmerDuality.GHom.toCC_comp, SelmerDuality.GHom.toCC_comp]
    refine SelmerDuality.GHom.toCC_ext fun i x => ?_
    have : Subsingleton (ResMod (locMap KA S₂' q.1) (ResMod (inflMap KA hS₂) PUnit)) :=
      inferInstanceAs (Subsingleton PUnit)
    exact (subsingleton_natCx_contCochains i).elim _ _

/-! ### The instance -/

/-- **An actual instance of `Identification3` with one new place** (PROVED; no hypotheses). -/
def identification3OnePlace : Identification3 KA S₂ S₂' hS₂ b 0 0 0 0 where
  toFullCore := coreB b
  Mf := PUnit
  Δf := ΔfB b
  hfull := hfullB b
  ψf := SelmerDuality.GHom.toCC (ψfB b)
  qisf := ψfB_quasiIso b
  R₀ := ZMod 2
  ρ := ρA
  p := 2
  hset := hsetB
  hS' := S₂'_finite
  M₀ := PUnit
  ψur := ψurB
  hψur := hψurB
  Δ₀ := Δ₀B b
  ψ0 := ψ0B b
  qis0 := ψ0B_quasiIso b
  ψold := SelmerDuality.GHom.toCC (σurB b)
  qisOld := σurB_quasiIso b
  square := squareB b
  Φq _ := 0
  qq _ := 1
  qq_odd _ := odd_one
  bas _ := @Module.Basis.empty Empty (ZMod 2) PUnit _ _ _ _ _
  hA _ := Matrix.ext fun i => isEmptyElim (α := Empty) i
  tame q := tameB q

theorem identification3OnePlace_nonempty :
    Nonempty (Identification3 KA S₂ S₂' hS₂ b 0 0 0 0) ∧ Nonempty (NewPlaces KA S₂ S₂') :=
  ⟨⟨identification3OnePlace b⟩, nonempty_new⟩

end ActualOnePlace

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
