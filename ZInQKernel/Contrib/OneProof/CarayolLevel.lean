import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.ModCurves.C9
import ZInQKernel.HDecomp.Textbook.C10Closed
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense

/-!
# r17-bypass: Carayol's conductor statement `CarayolR17'` from its existence form

Task r17-bypass (2026-11-15), report `docs/research/r17-bypass.md`.

The open field `r17 : LadicCond.CarayolR17'` says: for **every** semisimple `ρ` attached to a
weight-2 newform `f` of level `N` (trace form `AttachedTo`) and every `p ≠ ℓ`,
`a(ρ|G_{ℚ_p}) = v_p(N)`. Printed sources state the conductor for **the** representation they
construct (Carayol 1986, Théorème (A) with Casselman's `a(π_p) = v_p(N)`). The passage from one
representation to every semisimple one with the same traces is glue: Brauer–Nesbitt (the kernel's
`TSkolemKW.brauerNesbittChar0`), Chebotarev (the kernel's T18, `ZInQ.Contrib.frobeniusDense`) and
the invariance of the Serre–Tate conductor under isomorphism (proved below, `condExp_eq_of_intertwine`,
without `SwanIndependent`: isomorphic representations have the same adapted levels).

* `NewformRepConductor` (new leaf, existence form): there is a semisimple `ρ` attached to `f` with
  `a(ρ|G_{ℚ_p}) = v_p(N)` for every `p ≠ ℓ`.
* `carayolR17'_of_newformRepConductor : NewformRepConductor → LadicCond.CarayolR17'` (proved).
* `CarayolLevelLe`: the weakest form the route uses (the consumer `G0ModNewform.g15` needs only
  `v_p(N) ≤ a(ρ|G_{ℚ_p})`); `carayolLevelLe_of_R17'` (proved). Not used by the discharge.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace CarayolLevel

open PkgI4 LadicCond C9Rhof

/-! ## §1. Representation lemmas (copied from `ZInQKernel/OneProof/H/TailA.lean`, `G0ModNewform` §1-§2) -/

section RepLemmas

variable {k G V W : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- An isomorphism of `k[G]`-modules `ρ.asModule ≅ σ.asModule` is a `G`-equivariant
`k`-linear equivalence `V ≃ W` (copy of `G0ModNewform.equivariant_of_asModule`). -/
theorem equivariant_of_asModule (ρ : Representation k G V) (σ : Representation k G W)
    (φ : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  refine ⟨{ toFun := fun v => σ.asModuleEquiv (φ (ρ.asModuleEquiv.symm v))
            invFun := fun w => ρ.asModuleEquiv (φ.symm (σ.asModuleEquiv.symm w))
            map_add' := fun v w => by simp only [map_add]
            map_smul' := fun c v => by
              rw [ρ.asModuleEquiv_symm_map_smul, φ.map_smul,
                Representation.asModuleEquiv_map_smul, AlgHom.commutes, Module.algebraMap_end_apply]
              rfl
            left_inv := fun v => by
              dsimp only
              rw [σ.asModuleEquiv.symm_apply_apply, φ.symm_apply_apply,
                ρ.asModuleEquiv.apply_symm_apply]
            right_inv := fun w => by
              dsimp only
              rw [ρ.asModuleEquiv.symm_apply_apply, φ.apply_symm_apply,
                σ.asModuleEquiv.apply_symm_apply] }, fun g v => ?_⟩
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ρ.asModuleEquiv_symm_map_rho, φ.map_smul, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]

end RepLemmas

section CondIso

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] {n : ℕ}

theorem invariants_eq_map (ρ ρ' : GQp p →* GL (Fin n) k) (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (S : Set (GQp p)) :
    invariants ρ' S = (invariants ρ S).map (e : (Fin n → k) →ₗ[k] (Fin n → k)) := by
  ext w
  constructor
  · intro hw
    refine ⟨e.symm w, ?_, by simp⟩
    intro σ hσ
    apply e.injective
    rw [← he, e.apply_symm_apply]
    exact hw σ hσ
  · rintro ⟨v, hv, rfl⟩ σ hσ
    change (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) = e v
    rw [he]
    exact congrArg e (hv σ hσ)

theorem codimInv_eq (ρ ρ' : GQp p →* GL (Fin n) k) (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (S : Set (GQp p)) :
    codimInv ρ' S = codimInv ρ S := by
  unfold codimInv
  rw [invariants_eq_map ρ ρ' e he S, LinearEquiv.finrank_map_eq]

theorem eq_one_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (σ : GQp p) (h : ρ σ = 1) : ρ' σ = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [Matrix.toLin'_apply, he, h]
  simp

theorem isAdapted_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (L : Fld p) (hL : IsAdapted L ρ) :
    IsAdapted L ρ' :=
  ⟨hL.1, fun σ hσ => eq_one_of_intertwine ρ ρ' e he σ (hL.2 σ hσ)⟩

/-- The inverse of an intertwiner intertwines the other way. -/
theorem intertwine_symm (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) :
    ∀ σ v, (ρ σ : Matrix (Fin n) (Fin n) k).mulVec (e.symm v) =
      e.symm ((ρ' σ : Matrix (Fin n) (Fin n) k).mulVec v) := by
  intro σ v
  apply e.injective
  rw [e.apply_symm_apply, ← he, e.apply_symm_apply]

theorem swanAt_eq_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (L : Fld p) :
    swanAt L ρ' = swanAt L ρ := by
  unfold swanAt
  exact finsum_congr fun i => by rw [codimInv_eq ρ ρ' e he]

theorem choose_congr {α : Type*} {P Q : α → Prop} (hPQ : P = Q) (hP : ∃ x, P x)
    (hQ : ∃ x, Q x) : hP.choose = hQ.choose := by
  subst hPQ
  rfl

/-- **The Serre–Tate conductor `condExp` is invariant under isomorphism** (GLUE, proved; no
`SwanIndependent` needed: isomorphic representations have the same adapted levels, so `swan`
chooses the same level for both). -/
theorem condExp_eq_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) :
    condExp ρ' = condExp ρ := by
  have hiff : ∀ L : Fld p, IsAdapted L ρ' ↔ IsAdapted L ρ := fun L =>
    ⟨isAdapted_of_intertwine ρ' ρ e.symm (intertwine_symm ρ ρ' e he) L,
      isAdapted_of_intertwine ρ ρ' e he L⟩
  have hswan : swan ρ' = swan ρ := by
    unfold swan
    by_cases h : ∃ L : Fld p, IsAdapted L ρ
    · have h' : ∃ L : Fld p, IsAdapted L ρ' := by
        obtain ⟨L, hL⟩ := h
        exact ⟨L, (hiff L).2 hL⟩
      rw [dite_eq_left h, dite_eq_left h']
      have hc : h'.choose = h.choose :=
        choose_congr (funext fun L => propext (hiff L)) h' h
      rw [hc]
      exact swanAt_eq_of_intertwine ρ ρ' e he _
    · have h' : ¬ ∃ L : Fld p, IsAdapted L ρ' := by
        rintro ⟨L, hL⟩
        exact h ⟨L, (hiff L).1 hL⟩
      rw [dite_eq_right h, dite_eq_right h']
  unfold condExp
  rw [codimInv_eq ρ ρ' e he, hswan]

/-- An equivariant equivalence of `GaloisRep`s intertwines their restrictions to `G_{ℚ_p}` (copy
of `G0ModNewform.restrictLocal_intertwine`). -/
theorem restrictLocal_intertwine {ℓ : ℕ} [Fact ℓ.Prime] (r ρ : GaloisRep ℓ n)
    (e : (Fin n → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin n → PadicAlgCl ℓ))
    (he : ∀ g v, e (toRep r g v) = toRep ρ g (e v)) :
    ∀ σ v, ((ρ.restrictLocal p) σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).mulVec (e v) =
      e (((r.restrictLocal p) σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).mulVec v) := by
  intro σ v
  have h := he (PkgI4.decomp p σ) v
  rw [toRep_apply, toRep_apply, Matrix.toLin'_apply, Matrix.toLin'_apply] at h
  exact h.symm

end CondIso

/-! ## §2. Brauer–Nesbitt for representations attached to the same form -/

/-- `C9Rhof.FrobeniusDense` from the kernel's proved T18 (same body, other namespace; as
`HDec.frobeniusDense_C9`). -/
theorem frobeniusDense_C9 : C9Rhof.FrobeniusDense := by
  intro U hU σ S
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := ZInQ.Contrib.frobeniusDense U hU σ S
  exact ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩

/-- **Two semisimple representations attached to the same form are isomorphic** (GLUE, proved from
the kernel's Brauer–Nesbitt and T18): an equivariant linear equivalence `ρ ≅ ρ'`. -/
theorem iso_of_attached {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} (hN : 0 < N) {k : ℤ} (f : CF N k)
    (ρ ρ' : GaloisRep ℓ 2) (hs : ρ.IsSemisimple) (hs' : ρ'.IsSemisimple)
    (ha : ρ.AttachedTo ιC ιL f) (ha' : ρ'.AttachedTo ιC ιL f) :
    ∃ e : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ),
      ∀ g v, e (toRep ρ g v) = toRep ρ' g (e v) := by
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨φ⟩ := iso_of_arithFrob TSkolemKW.C10.brauerNesbittChar0' frobeniusDense_C9
    (N * ℓ).primeFactors (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2))
    (toRep ρ) (toRep ρ') (toRep_continuous ρ) (toRep_continuous ρ') (toRep_semisimple ρ hs)
    (toRep_semisimple ρ' hs') (by
      intro q hq hqS v τ hv hτ
      have hqN : ¬ q ∣ N * ℓ := fun h =>
        hqS (Nat.mem_primeFactors.mpr ⟨hq, h, hNℓ⟩)
      obtain ⟨-, α, hα, hρα⟩ := ha q hq hqN
      obtain ⟨-, α', hα', hρα'⟩ := ha' q hq hqN
      have : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
      rw [trace_toRep, trace_toRep, hρα v τ hv hτ, hρα' v τ hv hτ, this])
  exact equivariant_of_asModule _ _ φ

/-! ## §3. The new leaf and the discharge -/

/-- **New leaf (R17, existence form): Carayol 1986, Théorème (A), with Casselman's
`a(π_p) = v_p(N)`, for the representation attached to a weight-2 newform.** For a newform `f` of
weight 2, level `N ≥ 1` and nebentypus `χ`, a prime `ℓ` and embeddings `ιC : ℚ̄ → ℂ`,
`ιL : ℚ̄ → ℚ̄_ℓ`, there is a semisimple continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to `f`
(`AttachedTo`: Tate-module normalization, `tr ρ(Frob_p) = a_p(f)` at arithmetic Frobenius for
`p ∤ Nℓ`) whose Serre–Tate conductor exponent at every prime `p ≠ ℓ` is `v_p(N)`.
Sources: Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de Hilbert*,
Ann. Sci. ÉNS (4) 19 (1986) 409-468, Théorème (A), pp. 409-411 and §0.8 p. 411 (read by the locator
audit: all finite `p ∤ ℓ`, all `ℓ` including 2, `p ∣ N` included), for the representation
`ρ_{f,λ}` (Eichler–Shimura–Deligne; semisimple, even irreducible, Ribet 1977), with Casselman,
Math. Ann. 201 (1973), `a(π_p) = v_p(N)` for newforms (locator UNVERIFIED); the conductor is
unchanged under the dual (cohomological versus Tate normalization). The same packaging
"`ρ_{f,λ}` has prime-to-ℓ conductor `N`" is printed in surveys, e.g. Darmon–Diamond–Taylor,
*Fermat's Last Theorem* (1997), §3.1 (theorem number UNVERIFIED). Kind: consequence (not verified
as a printed statement in this form; pending reading). -/
def NewformRepConductor : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

/-- **R17 (`LadicCond.CarayolR17'`) from its existence form** (GLUE, proved: Brauer–Nesbitt, T18
and the invariance of `condExp` under isomorphism). -/
theorem carayolR17'_of_newformRepConductor (h : NewformRepConductor) :
    LadicCond.CarayolR17' := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp
  obtain ⟨ρ', hs', ha', hc⟩ := h ℓ ιC ιL N χ f hN hf
  obtain ⟨e, he⟩ := iso_of_attached ιC ιL hN f ρ ρ' hs hs' ha ha'
  rw [← hc p hp]
  exact (condExp_eq_of_intertwine _ _ e (restrictLocal_intertwine (p := p) ρ ρ' e he)).symm

/-- R17's existence form follows from R17 and R14's existence of an attached semisimple
representation (so the two are equivalent modulo the proved glue). Stated with the hypothesis
`hex` (for newforms of weight 2) to avoid importing R14's statement. -/
theorem newformRepConductor_of_R17' (h : LadicCond.CarayolR17')
    (hex : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
      (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
      ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f) :
    NewformRepConductor := by
  intro ℓ _ ιC ιL N χ f hN hf
  obtain ⟨ρ, hs, ha⟩ := hex ℓ ιC ιL N χ f hN hf
  exact ⟨ρ, hs, ha, fun p _ hp => h ℓ ιC ιL N χ f ρ p hN hf hs ha hp⟩

/-! ## §4. The weakest form the route uses -/

/-- **The form of R17 that the route uses** (the consumer `G0ModNewform.g15`, step D5 of
`docs/research/glue-conductor.md`, uses only `v_p(N) ≤ a(ρ|G_{ℚ_p})`, at `ℓ = 5`, `p ≠ 5` and at
`ℓ = 3`, `p = 5`): the level of a weight-2 newform divides the prime-to-`ℓ` conductor of its
`ℓ`-adic representation. A consequence of Carayol 1986 Théorème (A) with Casselman 1973 (its
"`≤`" half); not a printed statement as such. Not used by the discharge above. -/
def CarayolLevelLe : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ) [Fact p.Prime],
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ → p ∣ N →
      (N.factorization p : ℚ) ≤ condExp (ρ.restrictLocal p)

theorem carayolLevelLe_of_R17' (h : LadicCond.CarayolR17') : CarayolLevelLe := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp _
  exact (h ℓ ιC ιL N χ f ρ p hN hf hs ha hp).ge

end CarayolLevel

end
