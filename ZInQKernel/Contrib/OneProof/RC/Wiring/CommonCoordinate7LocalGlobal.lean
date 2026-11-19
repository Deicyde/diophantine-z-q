import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate7Frobenius

/-!
# Theorem 5.3, Lane RC32 round 4: the Tate-module half of the local-global comparison

`LocalGlobalFrobenius E` (`CommonCoordinate7Frobenius.lean`) has two halves: the
decomposition-group half (a global Frobenius `h` extends to a local arithmetic Frobenius `σ` along
an embedding `ι : ℚ̄ → ℚ̄_r`) and the Tate-module half (`ι` identifies `T₂(E/ℚ̄)` with `T₂(E/ℚ̄_r)`,
carrying `ρ_T(h)` to the action of `σ`). The second half is PROVED here for every elliptic `E`,
so the remaining input is `DecompositionFrobeniusQ`, a statement about Galois groups only:

* `ptCast`: transport of points along an equality of curves (coordinates unchanged);
* `ptMapIota ι`: `E(ℚ̄) → E(ℚ̄_r)` along `ι` (Mathlib's `Affine.Point.map`, then the identification
  `E⁄ℚ̄_r = (E⁄ℚ_r)⁄ℚ̄_r`); `ptMapIota_equivariant`: `ι ∘ h = σ ∘ ι` gives
  `ptMapIota ι ∘ h = σ ∘ ptMapIota ι` on points;
* `TateModule.map_bijective_of_levels`: a homomorphism bijective on every level `A[p^n]` induces a
  bijection of Tate modules; the levels of both curves have `(2^n)²` points (Tau Ceti's
  `natCard_tateModuleLevel`), and the point map is injective, so it is bijective on levels;
* `tateIota ι : T₂(E/ℚ̄) ≃ T₂(E/ℚ̄_r)` and `tateIota_equivariant`;
* `DecompositionFrobeniusQ r` (GLUE, Neukirch ANT II.8–9: the decomposition group at a prime above
  `r` is the local Galois group, and its Frobenius is the local Frobenius) and
  `localGlobalFrobenius_of_decomposition : (∀ r, r ≠ 2 → DecompositionFrobeniusQ r) →
  LocalGlobalFrobenius E` (PROVED);
* `frobeniusTrace_of_RD_decomposition : (R) → (D) → (∀ r, …) → FrobeniusTrace E` for every elliptic
  `E` (PROVED).

Kinds: definitions, PROVED; `DecompositionFrobeniusQ` is a named GLUE input (a hypothesis).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar TateMod tateRep)
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary (primeIdealQ IsArithmeticFrobeniusOnClosureQ)
open ZInQ.Contrib.CloudB3RC53.ModularWeil (TateReductionComparison DetEqDegree)
open scoped WithZero

/-! ## Tate modules of a level-wise bijective map -/

section TateBij

variable {p : ℕ} {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **A homomorphism bijective on every level `A[p^n]` induces a bijection of Tate modules**
(PROVED): injectivity componentwise; a preimage of `y` is the family of level preimages, which is
compatible because the level maps are injective and commute with multiplication by `p`. -/
theorem tateModule_map_bijective_of_levels (f : A →+ B)
    (hf : ∀ n, Function.Bijective (TauCeti.TateModule.levelMap (p := p) f n)) :
    Function.Bijective (TauCeti.TateModule.map (p := p) f) := by
  constructor
  · intro x y hxy
    refine TauCeti.TateModule.ext fun n => (hf n).1 ?_
    have := congrArg (TauCeti.TateModule.proj n) hxy
    rwa [TauCeti.TateModule.proj_map, TauCeti.TateModule.proj_map] at this
  · intro y
    choose x hx using fun n => (hf n).2 (TauCeti.TateModule.proj n y)
    have hcompat : ∀ n, TauCeti.tateModuleTransition p A n (x (n + 1)) = x n := by
      intro n
      apply (hf n).1
      apply Subtype.ext
      rw [TauCeti.TateModule.levelMap_apply, TauCeti.tateModuleTransition_apply, map_nsmul,
        ← TauCeti.TateModule.levelMap_apply f (n + 1) (x (n + 1)), hx (n + 1),
        ← TauCeti.tateModuleTransition_apply, TauCeti.TateModule.proj_succ, ← hx n,
        TauCeti.TateModule.levelMap_apply]
    refine ⟨TauCeti.TateModule.mk x hcompat, TauCeti.TateModule.ext fun n => ?_⟩
    rw [TauCeti.TateModule.proj_map, TauCeti.TateModule.proj_mk, hx n]

/-- An injective homomorphism is injective on every level (PROVED). -/
theorem levelMap_injective (f : A →+ B) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (TauCeti.TateModule.levelMap (p := p) f n) := fun a b h =>
  Subtype.ext (hf (by
    have := congrArg Subtype.val h
    rwa [TauCeti.TateModule.levelMap_apply, TauCeti.TateModule.levelMap_apply] at this))

end TateBij

/-! ## Points along an equality of curves -/

section Cast

variable {K : Type*} [Field K] [DecidableEq K]

/-- **Transport of points along an equality of curves** (definition; the coordinates are kept). -/
def ptCast {V V' : WeierstrassCurve K} (h : V = V') : V.toAffine.Point →+ V'.toAffine.Point := by
  subst h
  exact AddMonoidHom.id _

theorem ptCast_some {V V' : WeierstrassCurve K} (h : V = V') {x y : K}
    (hns : V.toAffine.Nonsingular x y) :
    ptCast h (.some x y hns) = .some x y (h ▸ hns) := by
  subst h
  rfl

theorem ptCast_injective {V V' : WeierstrassCurve K} (h : V = V') :
    Function.Injective (ptCast h) := by
  subst h
  exact Function.injective_id

end Cast

/-! ## The point map along an embedding `ℚ̄ → ℚ̄_r` -/

section Iota

open scoped Classical

variable (E : WeierstrassCurve ℚ) (r : ℕ) (hr : r.Prime)

/-- `ℚ_r`. -/
abbrev Qr : Type := (primeIdealQ r hr).adicCompletion ℚ

/-- `ℚ̄_r`. -/
abbrev Qrbar : Type := AlgebraicClosure (Qr r hr)

/-- `E⁄ℚ̄_r = (E⁄ℚ_r)⁄ℚ̄_r` (PROVED: both are `E` mapped along a ring map `ℚ → ℚ̄_r`). -/
theorem baseChange_Qrbar :
    E.baseChange (Qrbar r hr) = (E.baseChange (Qr r hr)).baseChange (Qrbar r hr) := by
  change E.map (algebraMap ℚ (Qrbar r hr)) =
    E.map ((algebraMap (Qr r hr) (Qrbar r hr)).comp (algebraMap ℚ (Qr r hr)))
  rw [RingHom.ext_rat (algebraMap ℚ (Qrbar r hr))
    ((algebraMap (Qr r hr) (Qrbar r hr)).comp (algebraMap ℚ (Qr r hr)))]

variable {E r hr}

/-- **The point map along `ι : ℚ̄ → ℚ̄_r`** (definition):
`E(ℚ̄) → E(ℚ̄_r) = ((E⁄ℚ_r)⁄ℚ̄_r)(ℚ̄_r)`. -/
def ptMapIota (ι : Qbar →ₐ[ℚ] Qrbar r hr) :
    (E.baseChange Qbar).toAffine.Point →+
      ((E.baseChange (Qr r hr)).baseChange (Qrbar r hr)).toAffine.Point :=
  (ptCast (baseChange_Qrbar E r hr)).comp (Affine.Point.map (W' := E) ι)

theorem ptMapIota_injective (ι : Qbar →ₐ[ℚ] Qrbar r hr) :
    Function.Injective (ptMapIota (E := E) ι) := by
  intro a b hab
  exact Affine.Point.map_injective (W' := E) ι (ptCast_injective (baseChange_Qrbar E r hr) hab)

/-- **The point map is equivariant** (PROVED): if `σ ∘ ι = ι ∘ h` then `ptMapIota ι` carries the
action of `h` on `E(ℚ̄)` to the action of `σ` on `E(ℚ̄_r)`. -/
theorem ptMapIota_equivariant (ι : Qbar →ₐ[ℚ] Qrbar r hr) (h : GalQ)
    (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) (hσ : ∀ x, σ (ι x) = ι (h x))
    (P : (E.baseChange Qbar).toAffine.Point) :
    ptMapIota ι (Affine.Point.map (W' := E) h.toAlgHom P) =
      Affine.Point.map (W' := E.baseChange (Qr r hr)) σ.toAlgHom (ptMapIota ι P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · simp only [ptMapIota, AddMonoidHom.comp_apply, Affine.Point.map_some, ptCast_some,
      Affine.Point.some.injEq]
    exact ⟨(hσ x).symm, (hσ y).symm⟩

end Iota

/-! ## The Tate modules -/

section TateIota

open scoped Classical

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {r : ℕ} {hr : r.Prime}

theorem two_ne_zero_Qrbar : ((2 : ℕ) : Qrbar r hr) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (Qrbar r hr))]
  exact (map_ne_zero_iff _ (algebraMap ℚ (Qrbar r hr)).injective).mpr (by norm_num)

/-- The point map is bijective on every `2^n`-torsion level (PROVED: injective, and both levels have
`(2^n)²` points). -/
theorem levelMap_ptMapIota_bijective (ι : Qbar →ₐ[ℚ] Qrbar r hr) (n : ℕ) :
    Function.Bijective (TauCeti.TateModule.levelMap (p := 2) (ptMapIota (E := E) ι) n) := by
  have h1 := (E.baseChange Qbar).natCard_tateModuleLevel (ℓ := 2)
    (Nat.cast_ne_zero.mpr two_ne_zero) n
  have h2 := ((E.baseChange (Qr r hr)).baseChange (Qrbar r hr)).natCard_tateModuleLevel
    (ℓ := 2) two_ne_zero_Qrbar n
  have : Finite (TauCeti.TateModuleLevel 2
      ((E.baseChange (Qr r hr)).baseChange (Qrbar r hr)).toAffine.Point n) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  exact (levelMap_injective _ (ptMapIota_injective ι) n).bijective_of_nat_card_le
    (by rw [h1, h2])

/-- **`T₂(E/ℚ̄) ≃ T₂(E/ℚ̄_r)` along `ι`** (definition, PROVED bijective). -/
def tateIota (ι : Qbar →ₐ[ℚ] Qrbar r hr) : TateMod E 2 ≃ₗ[ℤ_[2]] localTate E r hr :=
  LinearEquiv.ofBijective (TauCeti.TateModule.mapLinearMap (ptMapIota (E := E) ι))
    (by
      rw [show ⇑(TauCeti.TateModule.mapLinearMap (p := 2) (ptMapIota (E := E) ι)) =
        ⇑(TauCeti.TateModule.map (p := 2) (ptMapIota (E := E) ι)) from
          funext (TauCeti.TateModule.mapLinearMap_apply _)]
      exact tateModule_map_bijective_of_levels _ (levelMap_ptMapIota_bijective ι))

/-- **The comparison is equivariant** (PROVED): `σ ∘ ι = ι ∘ h` gives
`tateIota ι ∘ ρ_T(h) = ρ_{T,loc}(σ) ∘ tateIota ι`. -/
theorem tateIota_equivariant (ι : Qbar →ₐ[ℚ] Qrbar r hr) (h : GalQ)
    (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) (hσ : ∀ x, σ (ι x) = ι (h x)) (x : TateMod E 2) :
    tateIota ι (tateRep E 2 h x) =
      (E.baseChange (Qr r hr)).tateModuleGaloisRepresentation 2 σ (tateIota ι x) := by
  refine TauCeti.TateModule.ext fun n => Subtype.ext ?_
  change ((TauCeti.TateModule.proj n (TauCeti.TateModule.mapLinearMap (ptMapIota ι)
      (tateRep E 2 h x))) : ((E.baseChange (Qr r hr)).baseChange (Qrbar r hr)).toAffine.Point) =
    TauCeti.TateModule.proj n ((E.baseChange (Qr r hr)).tateModuleGaloisRepresentation 2 σ
      (TauCeti.TateModule.mapLinearMap (ptMapIota ι) x))
  rw [WeierstrassCurve.coe_proj_tateModuleGaloisRepresentation,
    TauCeti.TateModule.mapLinearMap_apply, TauCeti.TateModule.mapLinearMap_apply,
    TauCeti.TateModule.proj_map, TauCeti.TateModule.proj_map, TauCeti.TateModule.levelMap_apply,
    TauCeti.TateModule.levelMap_apply, ZInQ.Manuscript.RC.PrintsArith.coe_proj_tateRep]
  exact ptMapIota_equivariant ι h σ hσ _

end TateIota

/-! ## The decomposition-group input and the narrowed GLUE -/

section Decomposition

open scoped Classical

/-- **The decomposition group at a prime above `r` is the local Galois group** (GLUE: Neukirch,
*Algebraic Number Theory*, II.8–9; Serre, *Local Fields*, I.7): every arithmetic Frobenius
`h ∈ G_ℚ` at `r` (at a prime `P` of `ℤ̄` above `r`) extends, along an embedding `ι : ℚ̄ → ℚ̄_r`
centred at `P`, to an arithmetic Frobenius `σ ∈ Gal(ℚ̄_r/ℚ_r)` for a valuation of `ℚ̄_r` extending
`v_r`. A statement about Galois groups only, independent of the curve. -/
def DecompositionFrobeniusQ (r : ℕ) (hr : r.Prime) : Prop :=
  ∀ h : GalQ, ZInQ.Contrib.ChebFD.C10.IsFrobAt h r →
    ∃ (ι : Qbar →ₐ[ℚ] Qrbar r hr) (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
      (w : Valuation (Qrbar r hr) Γ),
      (w.comap (algebraMap (Qr r hr) (Qrbar r hr))).IsEquiv
        (Valued.v : Valuation (Qr r hr) ℤᵐ⁰) ∧
      ∃ σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr,
        IsArithmeticFrobeniusOnClosureQ (primeIdealQ r hr) Γ w σ ∧ ∀ x : Qbar, σ (ι x) = ι (h x)

/-- **The local-global comparison from the decomposition-group input** (PROVED, for every elliptic
`E`): the Tate-module half is `tateIota` with `tateIota_equivariant`. -/
theorem localGlobalFrobenius_of_decomposition (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hDec : ∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → DecompositionFrobeniusQ r hr) :
    LocalGlobalFrobenius E := by
  intro r hr hr2 _ h hF
  obtain ⟨ι, Γ, inst, w, hw, σ, hσ, hσι⟩ := hDec r hr hr2 h hF
  exact ⟨Γ, inst, w, hw, σ, hσ, tateIota ι, tateIota_equivariant ι h σ hσι⟩

/-- **`FrobeniusTrace` from (R), (D) and the decomposition-group input** (PROVED, for every
elliptic `E`). -/
theorem frobeniusTrace_of_RD_decomposition (hR : TateReductionComparison) (hD : DetEqDegree)
    (hDec : ∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → DecompositionFrobeniusQ r hr)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] : FrobeniusTrace E :=
  frobeniusTrace_of_RD E hR hD (localGlobalFrobenius_of_decomposition E hDec)

end Decomposition

end ZInQ.Manuscript.RC.Wiring
