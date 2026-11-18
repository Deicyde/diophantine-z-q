import ZInQKernel.Contrib.OneProof.SelmerTwoPower
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Tower

/-!
# The places of `ℚ`: the `v`-adic completions and the fields `ℚ_p` give the same Selmer groups

`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean` indexes the finite places of `ℚ` by the height-one
primes `v` of `ℤ` and completes at them (`v.adicCompletion ℚ`), so that Tau Ceti's comparison of the
cohomological and explicit `2`-Selmer groups applies verbatim. Earlier editions indexed them by the
primes `p` and used Mathlib's `ℚ_[p]`, with two families (finite places and the real place). This file
keeps those earlier families as local comparison data, and proves that the Shafarevich–Tate group,
the `2^n`-Selmer groups and the `2`-primary Selmer group are the same subgroups of the same
`H¹(G_ℚ, ·)` for both choices:

* `pointRes_eq_zero_iff_of_algEquiv`: a class of `H¹(G_K, E(Kˢ))` restricts to zero over a field `L`
  exactly when it restricts to zero over a `K`-isomorphic field `L'`, whatever the embeddings of
  separable closures (Tau Ceti's `WeierstrassCurve.pointRes_pointRes_eq_zero_iff`, for the towers
  `K → L → L'` and `K → L' → L` along the isomorphism);
* `algEquivPadic`: the `ℚ`-algebra isomorphism `v.adicCompletion ℚ ≃ ℚ_p`, `p = primesEquiv v`, with the
  algebra structures used here: the ring isomorphism of Mathlib's
  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`, which commutes with the (unique) maps from `ℚ`
  by `eq_ratCast` and `map_ratCast`;
* `sha_eq_shaQp`, `selmerAt_eq_selmerAtQp`, `selmerTwoPower_eq_comap_shaQp`: equality with the
  two-family definitions (`shaQp`, `selmerAtQp`), reindexing the finite places along Mathlib's
  `Rat.HeightOneSpectrum.primesEquiv`;
* `sha_eq_shaP`, `selmerAt_eq_selmerAtP`: equality with the single family over `Nat.Primes ⊕ Unit`
  (`shaP`, `selmerAtP`).
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology IsDedekindDomain

/-! ### Restriction to isomorphic fields -/

section Transport

variable {K : Type*} [Field K] (W : WeierstrassCurve K) {L L' : Type*} [Field L] [Field L']
  [Algebra K L] [Algebra K L']

/-- **Restriction to zero is invariant under a `K`-isomorphism of the local field**: for
`e : L ≃ₐ[K] L'` and any `K`-embeddings `τ : Kˢ → Lˢ`, `τ' : Kˢ → L'ˢ`, a class of `H¹(G_K, E(Kˢ))`
restricts to zero along `τ` exactly when it does along `τ'`. -/
theorem pointRes_eq_zero_iff_of_algEquiv (e : L ≃ₐ[K] L')
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    (τ' : SeparableClosure K →ₐ[K] SeparableClosure L')
    (c : H1 (AbsoluteGaloisGroup K) W.PointCoeff) :
    W.pointRes τ c = 0 ↔ W.pointRes τ' c = 0 := by
  constructor
  · intro h
    let _ : Algebra L L' := e.toRingHom.toAlgebra
    have : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
    rw [← W.pointRes_pointRes_eq_zero_iff τ IsSepClosed.lift τ', h, map_zero]
  · intro h
    let _ : Algebra L' L := e.symm.toRingHom.toAlgebra
    have : IsScalarTower K L' L := IsScalarTower.of_algebraMap_eq fun x => (e.symm.commutes x).symm
    rw [← W.pointRes_pointRes_eq_zero_iff τ' IsSepClosed.lift τ, h, map_zero]

end Transport

/-! ### The earlier families: `ℚ_p` at the primes `p`, `ℝ` at the real place -/

/-- Every `p : Nat.Primes` is prime, so `ℚ_p` is a field. -/
instance factPrimeNatPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The completion `ℚ_p` at the prime `p` (the earlier editions' finite completions). -/
abbrev QpCompletion (p : Nat.Primes) : Type := ℚ_[(p : ℕ)]

/-- The earlier editions' embeddings at the finite places. -/
def embFinQp (p : Nat.Primes) :=
  sepClosureEmb ℚ (QpCompletion p)

/-- The earlier editions' embedding at the real place. -/
def embInfR (_ : Unit) :=
  sepClosureEmb ℚ ℝ

variable (E : WeierstrassCurve ℚ)

/-- **`Sha(E/ℚ)` with the earlier two families** (finite places `ℚ_p`, real place `ℝ`). Comparison
data only. -/
def shaQp : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff) :=
  E.shafarevichTateGroup embFinQp ⊓ E.shafarevichTateGroup embInfR

/-- **`Sel_{2^n}(E/ℚ)` with the earlier two families.** Comparison data only. -/
def selmerAtQp (n : ℕ) : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))) :=
  E.selmerGroup embFinQp (2 ^ n) ⊓ E.selmerGroup embInfR (2 ^ n)

/-! ### The local fields agree -/

/-- A ring isomorphism of division rings commutes with the maps from `ℚ`, for any `ℚ`-algebra
structures: a ring homomorphism out of `ℚ` is the cast (`eq_ratCast`), and ring maps preserve casts
(`map_ratCast`). -/
theorem ringEquiv_algebraMap_rat {L L' : Type*} [DivisionRing L] [DivisionRing L'] [Algebra ℚ L]
    [Algebra ℚ L'] (f : L ≃+* L') (q : ℚ) : f (algebraMap ℚ L q) = algebraMap ℚ L' q := by
  rw [eq_ratCast (algebraMap ℚ L) q, eq_ratCast (algebraMap ℚ L') q, map_ratCast]

/-- **`ℚ_v ≅ ℚ_p` as `ℚ`-algebras**, for the algebra structures used here (the `v`-adic completion's
own, `HeightOneSpectrum.instAlgebraAdicCompletion`, and the one of `ℚ_p`): the ring isomorphism of
Mathlib's `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`; it commutes with the maps from `ℚ`
because a ring homomorphism out of `ℚ` is the cast (`eq_ratCast`) and ring maps preserve casts
(`map_ratCast`). -/
def algEquivPadic (v : HeightOneSpectrum ℤ) :
    @AlgEquiv ℚ (v.adicCompletion ℚ) (QpCompletion (Rat.HeightOneSpectrum.primesEquiv v)) _ _ _
      (HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ v) _ :=
  @AlgEquiv.ofRingEquiv ℚ (v.adicCompletion ℚ) (QpCompletion (Rat.HeightOneSpectrum.primesEquiv v))
    _ _ _ (HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ v) _
    (RingEquivClass.toRingEquiv (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v))
    (@ringEquiv_algebraMap_rat _ _ _ _ (HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ v) _
      (RingEquivClass.toRingEquiv (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)))

/-- **Restriction to zero at the finite place `v` is restriction to zero over `ℚ_p`.** -/
theorem pointRes_emb_inl_eq_zero_iff (v : HeightOneSpectrum ℤ)
    (c : H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff) :
    E.pointRes (emb (Sum.inl v)) c = 0 ↔
      E.pointRes (embFinQp (Rat.HeightOneSpectrum.primesEquiv v)) c = 0 :=
  pointRes_eq_zero_iff_of_algEquiv E (L := Completion (Sum.inl v)) (algEquivPadic v) _ _ c

/-! ### The Selmer groups agree -/

/-- **`Sha(E/ℚ)` is the same for the `v`-adic completions and for the fields `ℚ_p`.** -/
theorem sha_eq_shaQp : sha E = shaQp E := by
  ext c
  rw [sha, shaQp, AddSubgroup.mem_inf, WeierstrassCurve.mem_shafarevichTateGroup_iff,
    WeierstrassCurve.mem_shafarevichTateGroup_iff, WeierstrassCurve.mem_shafarevichTateGroup_iff]
  constructor
  · intro h
    refine ⟨fun p => ?_, fun u => h (Sum.inr u)⟩
    have := (pointRes_emb_inl_eq_zero_iff E (Rat.HeightOneSpectrum.primesEquiv.symm p) c).mp
      (h (Sum.inl _))
    rwa [Equiv.apply_symm_apply] at this
  · rintro ⟨hfin, hinf⟩ v
    match v with
    | .inl v => exact (pointRes_emb_inl_eq_zero_iff E v c).mpr (hfin _)
    | .inr u => exact hinf u

/-- **`Sel_{2^n}(E/ℚ)` is the same for the `v`-adic completions and for the fields `ℚ_p`.** -/
theorem selmerAt_eq_selmerAtQp (n : ℕ) : selmerAt E n = selmerAtQp E n := by
  ext c
  rw [selmerAt, selmerAtQp, AddSubgroup.mem_inf, WeierstrassCurve.mem_selmerGroup_iff,
    WeierstrassCurve.mem_selmerGroup_iff, WeierstrassCurve.mem_selmerGroup_iff, ← AddSubgroup.mem_inf]
  exact SetLike.ext_iff.mp (sha_eq_shaQp E) _

/-- **`Sel_{2^∞}(E/ℚ)` with the fields `ℚ_p`**: the classes whose image in `H¹(G_ℚ, E(ℚˢ))` lies in
`shaQp E`. -/
theorem selmerTwoPower_eq_comap_shaQp :
    selmerTwoPower E = (shaQp E).comap
      (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
        continuous_of_discreteTopology) := by
  rw [selmerTwoPower, sha_eq_shaQp]

/-! ### The single family over `Nat.Primes ⊕ Unit` -/

/-- The places of `ℚ` indexed by the primes and `Unit` (comparison data only). -/
abbrev PlaceP : Type := Nat.Primes ⊕ Unit

/-- The completions `ℚ_p`, `ℝ` over `PlaceP`. -/
abbrev CompletionP : PlaceP → Type :=
  Sum.elim (fun p : Nat.Primes => ℚ_[(p : ℕ)]) (fun _ : Unit => ℝ)

instance instFieldCompletionP : ∀ v, Field (CompletionP v) := fun v =>
  Sum.rec (motive := fun v => Field (CompletionP v)) (fun p => (inferInstance : Field ℚ_[(p : ℕ)]))
    (fun _ => (inferInstance : Field ℝ)) v

instance instAlgebraCompletionP : ∀ v, Algebra ℚ (CompletionP v) := fun v =>
  Sum.rec (motive := fun v => Algebra ℚ (CompletionP v))
    (fun p => (inferInstance : Algebra ℚ ℚ_[(p : ℕ)])) (fun _ => (inferInstance : Algebra ℚ ℝ)) v

/-- The embeddings over `PlaceP`. -/
def embP (v : PlaceP) :=
  sepClosureEmb ℚ (CompletionP v)

/-- `Sha(E/ℚ)` over `PlaceP` (comparison data only). -/
def shaP : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff) :=
  E.shafarevichTateGroup embP

/-- `Sel_{2^n}(E/ℚ)` over `PlaceP` (comparison data only). -/
def selmerAtP (n : ℕ) : AddSubgroup (H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))) :=
  E.selmerGroup embP (2 ^ n)

theorem shaP_eq_shaQp : shaP E = shaQp E := by
  ext c
  rw [shaP, shaQp, AddSubgroup.mem_inf, WeierstrassCurve.mem_shafarevichTateGroup_iff,
    WeierstrassCurve.mem_shafarevichTateGroup_iff, WeierstrassCurve.mem_shafarevichTateGroup_iff]
  exact ⟨fun h => ⟨fun p => h (Sum.inl p), fun u => h (Sum.inr u)⟩, fun h v =>
    match v with
    | .inl p => h.1 p
    | .inr u => h.2 u⟩

/-- **`Sha(E/ℚ)` is the same over `Place` and over `PlaceP`.** -/
theorem sha_eq_shaP : sha E = shaP E := by
  rw [sha_eq_shaQp, shaP_eq_shaQp]

/-- **`Sel_{2^n}(E/ℚ)` is the same over `Place` and over `PlaceP`.** -/
theorem selmerAt_eq_selmerAtP (n : ℕ) : selmerAt E n = selmerAtP E n := by
  ext c
  rw [selmerAt, selmerAtP, WeierstrassCurve.mem_selmerGroup_iff,
    WeierstrassCurve.mem_selmerGroup_iff]
  exact SetLike.ext_iff.mp (sha_eq_shaP E) _

end ZInQ.Manuscript.SelmerTwoPower
