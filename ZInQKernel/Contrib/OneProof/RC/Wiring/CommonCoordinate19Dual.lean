import ZInQKernel.Contrib.CloudB3E2Norm.DualPres
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Bridge
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncIsotropyGenuine

/-!
# The orthogonal side of the retention at a switch, from lane E2's dual chain

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate`, tex 4157–4175:
`j : C_S → C_{P⊥}` is the paired strict-to-primitive map (tex 4161); all old orthogonal
conditions and their homotopies are retained (tex 4162); at `q` the maps are from the
unramified condition to the full condition and from zero to the unramified condition
(tex 4163–4164); naturality of the cup pairing gives `β_R(v, i w) = β_P(j v, w)`
(tex 4164–4167); the generic paired strict lift satisfies `j z_S = e_q^c z_{P⊥}`, and
`λ_R ∘ i = e_q λ_P` (tex 4169–4174); the second factor comes from the same closed functional
(tex 4159, 3750–3752). The hypotheses of Selmer duality are a coefficient pairing and orthogonal
local diagrams with their isotropy homotopies (tex 3829–3833; Nekovář 6.2.5–6.2.8, 6.3.4), the
local products landing in Nekovář's truncated target `τ≥2` (Nekovář 6.2.1.3, 6.3.1). The paired
classes come from the orthogonal comparison (tex 3736–3753).

Everything is at one coefficient ring `k`. The relaxed and primitive sides are lane RC32's
presentation `suppDataS` on the module `M`; the orthogonal side is lane E2's dual chain
`dsuppDataS` on a module `M'` (for the text, the module of the paired character `π⁻¹`) with old
orthogonal conditions `Δ'`; the cup products come from a coefficient pairing `β : M' × M → T`.

* **The pinned cup product** (definitions, PROVED). `dualCupE`, `dualCupEL`, `dualCupResE`,
  `dualCupG`, `dualCupL`, `dualCup_compat`: the global target `C^•_cont(G_{K,S}, T)`, the local
  target `τ≥2 ⊕_v C^•_cont(G_v, T)`, the restriction, the global and the local cup products of
  `β`. **`dualCup_eq_genuinePairDataT`**: they are the targets, the restriction and the cup
  products of lane RC26's `(genuinePairDataTrunc … I).toSelPairData` for all local conditions and
  all truncated isotropy data `I` (by definition), so they depend neither on the support nor on
  the switch; `switchRetentionInputs_dual_eq_genuinePairDataT`: the same at the conditions of the
  switch, `dpresCondS T` and `presCondS (T ∪ {p})`.
* **The cup-product input** `DualCupInputs` (GLUE, owner lane U1: the genuine cup product into
  Nekovář's truncated target): the remaining fields of `SwitchRetentionInputs` that the dual chain
  does not provide: the old places (`old`, `old_avoid`), the old homotopies `hv`, the homotopy
  `hq` at `p`, and the isotropy identities `isoR`, `isoP`.
* **`switchRetentionInputs_dual`** (definition): `SwitchRetentionInputs … T p hp (dsuppDataS T)
  (dfS T p)` with `Uo' = dpresCondS T`, `Uq' = switchUq p` (on the paired module), `pS = dpS`,
  `pPp = dpPp`, `qPp = dqPp`, `ret_S = dret_S`, `q_S = dq_S` (lane E2, PROVED).
* **The paired strict lift** (PROVED from lane E2's GLUE `OrthComparisonInverse`): `dualZS`,
  `dualZP`, `dualB` and **`dual_hlift`**, `j z_S = e z_{P⊥} + d b` (lane E2's
  `hlift_stepRetention`, i.e. `hlift_of_transport`; for the classes of the actual points the
  transported norm identity is lane E2's `gxClass_step_of_global` at `π⁻¹`, as in
  `hlift_actual`); **`StepRetention.ofDual`**: the retention datum of one switch of the genuine
  chain at a coefficient stage.
* **The consecutive-step contract** (PROVED with one named compatibility). The strict side of a
  step is the orthogonal side of the next (`selRestrict_dsuppDataS`). For a class `z` of
  `C¹_{(T ∪ {p})⊥}` and one trace: **`dual_pairedFun_consecutive_iff`**: on `C²_{T ∪ {p}}`,
  `λ_P` of the step at `T ∪ {p}` and `λ_R` of the step at `T` agree at `w` iff the trace takes the
  same value on the two homotopy terms; `RetainedHomotopyStep` (the named compatibility of the cup
  data across steps: the relaxed homotopy of the step at `T` and the primitive homotopy of the
  step at `T ∪ {p}` agree on `U¹_{(T ∪ {p})⊥} × U²_{T ∪ {p}}`); **`dual_pairedFun_consecutive`**:
  under it the two linear maps are equal; **`StepRetention.ofDual_consecutive`**: the same for the
  retention data of consecutive steps with consecutive transported classes.

Kinds: definitions, PROVED, and GLUE (`DualCupInputs`; the named compatibility
`RetainedHomotopyStep`; lane E2's `OrthComparisonInverse` enters as a hypothesis).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (ghomComp changeMap restrictData)
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (truncGe2 truncSub truncPair)
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (pairedFun)
open ZInQ.Contrib.CloudB3E2.DualPres (dsuppDataS dfS dpresCondS dpPp dpS dqPp dret_S dq_S
  selRestrict_dsuppDataS OrthComparisonInverse hlift_stepRetention)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section Cup

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  {ι : Type} (place : ι × Bool → Places K S)
  (M' : Type) [AddCommGroup M'] [Module k M'] [DistribMulAction (GKS K S) M']
  [SMulCommClass (GKS K S) k M'] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousSMul (GKS K S) M']
  (Tm : Type) [AddCommGroup Tm] [Module k Tm] [DistribMulAction (GKS K S) Tm]
  [SMulCommClass (GKS K S) k Tm] [TopologicalSpace Tm] [ContinuousAdd Tm]
  [ContinuousConstSMul k Tm] [ContinuousSMul (GKS K S) Tm]
  (β : M' →ₗ[k] M →ₗ[k] Tm)
  (hβ : ∀ (g : GKS K S) (a : M') (b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M' × M => β x.1 x.2)

/-- **The global target of the pinned cup product** (tex 4164–4167, 3829–3833; Nekovář 6.3.1):
`C^•_cont(G_{K,S}, T)`. Kind: definition. -/
abbrev dualCupE : GCx k := globalCx k (GKS K S) Tm

/-- The full local target `⊕_v C^•_cont(G_v, T)` over the places of the presentation
(tex 4164–4167). Kind: definition. -/
abbrev dualCupELFull : GCx k :=
  localSumCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) Tm

/-- **The local target of the pinned cup product** (tex 4164–4167; Nekovář 6.2.1.3, 6.3.1):
Nekovář's truncation `τ≥2 ⊕_v C^•_cont(G_v, T)`. Kind: definition. -/
abbrev dualCupEL : GCx k := truncGe2 (dualCupELFull K S₀ S k place Tm)

/-- **The restriction of the pinned targets** (tex 4164–4167): `res_S` followed by the
projection to `τ≥2`. Kind: definition. -/
def dualCupResE : GHom (dualCupE K S k Tm) (dualCupEL K S₀ S k place Tm) where
  f i j h := (truncSub (dualCupELFull K S₀ S k place Tm) j).mkQ ∘ₗ
    (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) Tm).f i j h
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    change (truncSub (dualCupELFull K S₀ S k place Tm) j₁).mkQ
        ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) Tm).f i₁ j₁ hj
          ((dualCupE K S k Tm).d i i₁ h₁ x)) =
      (truncSub (dualCupELFull K S₀ S k place Tm) j₁).mkQ
        ((dualCupELFull K S₀ S k place Tm).d j j₁ h₂
          ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) Tm).f i j hij x))
    rw [(resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) Tm).comm i i₁ j j₁ hij
      h₁ h₂ hj x]

/-- **The global cup product of the pinned data** (tex 4164–4167, 3829–3833): lane RC26's
`globalPair` of the coefficient pairing `β : M' × M → T`. Kind: definition. -/
abbrev dualCupG :
    GPair (globalCx k (GKS K S) M') (globalCx k (GKS K S) M) (dualCupE K S k Tm) :=
  globalPair k (GKS K S) β hβ hβc

/-- **The local cup product of the pinned data** (tex 4164–4167; Nekovář 6.3.1): lane RC26's
`localSumPair` of `β`, followed by the projection to `τ≥2`. Kind: definition. -/
abbrev dualCupL :
    GPair (localSumCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M')
      (localSumCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M)
      (dualCupEL K S₀ S k place Tm) :=
  truncPair (localSumPair k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc)

/-- **Restriction commutes with the pinned cup products** (tex 4164–4167; Nekovář 6.4.1–6.4.3):
lane RC26's `res_cup`, projected to `τ≥2`. Kind: PROVED. -/
theorem dualCup_compat (i j l i' j' l' : ℤ) (h : i + j = l) (h' : i' + j' = l') (hi : i = i')
    (hj : j = j') (hl : l = l') (a : (globalCx k (GKS K S) M').X i)
    (b : (globalCx k (GKS K S) M).X j) :
    (dualCupResE K S₀ S k place Tm).f l l' hl ((dualCupG K S k M M' Tm β hβ hβc).P i j l h a b) =
      (dualCupL K S₀ S k M place M' Tm β hβ hβc).P i' j' l' h'
        ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M').f i i' hi a)
        ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f j j' hj b) := by
  subst hi hj hl
  have e : (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) Tm).f l l rfl
      ((globalPair k (GKS K S) β hβ hβc).P i j l h a b) =
      (localSumPair k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc).P i j l h
        ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M').f i i rfl a)
        ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f j j rfl b) := by
    funext v
    exact natF_natPairP _ _ _ _ _ (fun p q n hpq x y => res_cup k (GKS K S)
      (presGv K S₀ S place) (presLoc K S₀ S place) β hβc v p q n hpq x y) i j l h a b
  exact congrArg (truncSub (dualCupELFull K S₀ S k place Tm) l).mkQ e

/-- **The pinned data are lane RC26's truncated pairing data** (tex 4164–4167, 3829–3833;
Nekovář 6.3.1): for all local conditions `ΔA`, `ΔB` of the presentation on `M'`, `M` and all
truncated isotropy data `I`, the targets, the restriction and the cup products of
`(genuinePairDataTrunc … I).toSelPairData` are `dualCupE`, `dualCupEL`, `dualCupResE`,
`dualCupG`, `dualCupL`; so they depend neither on the support, nor on the switch, nor on `I`.
Kind: PROVED (definitional). -/
theorem dualCup_eq_genuinePairDataT
    (ΔA : LocalConditions k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M')
    (ΔB : LocalConditions k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M)
    (I : TruncIsotropyData k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc
      ΔA ΔB) :
    (genuinePairDataT k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc ΔA ΔB
        I).E = dualCupE K S k Tm ∧
      (genuinePairDataT k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc ΔA ΔB
        I).EL = dualCupEL K S₀ S k place Tm ∧
      (genuinePairDataT k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc ΔA ΔB
        I).resE = dualCupResE K S₀ S k place Tm ∧
      (genuinePairDataT k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc ΔA ΔB
        I).cupG = dualCupG K S k M M' Tm β hβ hβc ∧
      (genuinePairDataT k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc ΔA ΔB
        I).cupL = dualCupL K S₀ S k M place M' Tm β hβ hβc :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Cup

section Dual

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))
  (M' : Type) [AddCommGroup M'] [Module k M'] [DistribMulAction (GKS K S) M']
  [SMulCommClass (GKS K S) k M'] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousSMul (GKS K S) M']
  (Δ' : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M')
  (X' : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU' : ∀ j, SplitInclusion (genuineUq K S k (place j) (X' j)) (genuineLq K S k M' (place j)))
  (Tm : Type) [AddCommGroup Tm] [Module k Tm] [DistribMulAction (GKS K S) Tm]
  [SMulCommClass (GKS K S) k Tm] [TopologicalSpace Tm] [ContinuousAdd Tm]
  [ContinuousConstSMul k Tm] [ContinuousSMul (GKS K S) Tm]
  (β : M' →ₗ[k] M →ₗ[k] Tm)
  (hβ : ∀ (g : GKS K S) (a : M') (b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M' × M => β x.1 x.2)

/-- **The cup-product input of the retention at the switch `C_T ⊂ C_{T ∪ {p}}` on lane E2's dual
chain** (tex 4157–4175, 3829–3833; Nekovář 6.2.1.3, 6.3.1): the fields of
`SwitchRetentionInputs` that neither lane E2's dual chain nor the pinned cup product provide. The
targets, the restriction and the cup products are pinned (`dualCupE`, `dualCupEL`, `dualCupResE`,
`dualCupG`, `dualCupL`: those of lane RC26's `(genuinePairDataTrunc … I).toSelPairData`); the
fields are the old places, their homotopies, the homotopy at `p` and the two isotropy
identities, all into the truncated target. Kind: definition (GLUE, owner lane U1: the genuine
cup product into Nekovář's truncated target). -/
structure DualCupInputs (T : Finset ι) (p : ι) (hp : p ∉ T) where
  /-- the old places, finitely many places of the presentation (tex 4162) -/
  old : Finset (Places K S₀ ⊕ (ι × Bool))
  /-- the old places are not above `p` (tex 4162–4164) -/
  old_avoid : ∀ v ∈ old, v ≠ .inr (p, false) ∧ v ≠ .inr (p, true)
  /-- the old isotropy homotopies on the old orthogonal and the relaxed conditions, into the
  truncated target (tex 4162, 3829–3833) -/
  hv : ∀ (v : Places K S₀ ⊕ (ι × Bool)) (i j l : ℤ), i + j = l + 1 →
    ((dpresCondS K S₀ S k M' Δ' place X' EU' T).U v).X i →ₗ[k]
      ((presCondS K S₀ S k M Δ place X EU (insert p T)).U v).X j →ₗ[k]
        (dualCupEL K S₀ S k place Tm).X l
  /-- the isotropy homotopy at `p`, on the unramified conditions of the two sides
  (tex 4163–4165) -/
  hq : ∀ i j l : ℤ, i + j = l + 1 → (switchUq K S k place X' p).X i →ₗ[k]
    (switchUq K S k place X p).X j →ₗ[k] (dualCupEL K S₀ S k place Tm).X l
  /-- the isotropy identity of the relaxed homotopy `switchHR` (tex 4162–4167, 3829–3833) -/
  isoR : ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hl : l + 1 = l₁) (x : (dsuppDataS K S₀ S k M' Δ' place X' EU' (insert p T)).U.X i)
    (y : (suppDataS K S₀ S k M Δ place X EU (insert p T)).U.X j),
    (dualCupEL K S₀ S k place Tm).d l l₁ hl (switchHR K S₀ S k M Δ place X EU T p old hv
        (dpS K S₀ S k M' Δ' place X' EU' T p) i j l h x y) +
      switchHR K S₀ S k M Δ place X EU T p old hv (dpS K S₀ S k M' Δ' place X' EU' T p) i₁ j
        l₁ (by omega) ((dsuppDataS K S₀ S k M' Δ' place X' EU' (insert p T)).U.d i i₁ hi x) y +
      sgn i • switchHR K S₀ S k M Δ place X EU T p old hv (dpS K S₀ S k M' Δ' place X' EU' T p)
        i j₁ l₁ (by omega) x ((suppDataS K S₀ S k M Δ place X EU (insert p T)).U.d j j₁ hj y) =
    (dualCupL K S₀ S k M place M' Tm β hβ hβc).P i j l₁ (by omega)
      ((ghomComp (dfS K S₀ S k M' Δ' place X' EU' T p)
        (dsuppDataS K S₀ S k M' Δ' place X' EU' T).ι).f i i rfl x)
      ((suppDataS K S₀ S k M Δ place X EU (insert p T)).ι.f j j rfl y)
  /-- the isotropy identity of the primitive homotopy `switchHP` (tex 4162–4167, 3829–3833) -/
  isoP : ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hl : l + 1 = l₁) (x : (dsuppDataS K S₀ S k M' Δ' place X' EU' T).U.X i)
    (y : (suppDataS K S₀ S k M Δ place X EU T).U.X j),
    (dualCupEL K S₀ S k place Tm).d l l₁ hl (switchHP K S₀ S k M Δ place X EU T p hp
        (DPp := dsuppDataS K S₀ S k M' Δ' place X' EU' T) old hv hq
        (dpPp K S₀ S k M' Δ' place X' EU' T) (dqPp K S₀ S k M' Δ' place X' EU' T p hp)
        i j l h x y) +
      switchHP K S₀ S k M Δ place X EU T p hp (DPp := dsuppDataS K S₀ S k M' Δ' place X' EU' T)
        old hv hq (dpPp K S₀ S k M' Δ' place X' EU' T) (dqPp K S₀ S k M' Δ' place X' EU' T p hp)
        i₁ j l₁ (by omega) ((dsuppDataS K S₀ S k M' Δ' place X' EU' T).U.d i i₁ hi x) y +
      sgn i • switchHP K S₀ S k M Δ place X EU T p hp
        (DPp := dsuppDataS K S₀ S k M' Δ' place X' EU' T) old hv hq
        (dpPp K S₀ S k M' Δ' place X' EU' T) (dqPp K S₀ S k M' Δ' place X' EU' T p hp)
        i j₁ l₁ (by omega) x ((suppDataS K S₀ S k M Δ place X EU T).U.d j j₁ hj y) =
    (dualCupL K S₀ S k M place M' Tm β hβ hβc).P i j l₁ (by omega)
      ((dsuppDataS K S₀ S k M' Δ' place X' EU' T).ι.f i i rfl x)
      ((ghomComp (switchFP K S₀ S k M Δ place X EU T p)
        (suppDataS K S₀ S k M Δ place X EU (insert p T)).ι).f j j rfl y)

variable {K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc} in
/-- **Lane RC30's retention inputs at the switch on lane E2's dual chain** (tex 4157–4175,
3489–3498): `SwitchRetentionInputs` with the orthogonal data `DPp = dsuppDataS T` and
`fS = dfS T p`, the pinned cup products, `Uo' = dpresCondS T`, `Uq' = switchUq p` on the paired
module, the components `pS = dpS`, `pPp = dpPp`, `qPp = dqPp`, `ret_S := dret_S`,
`q_S := dq_S` (lane E2, PROVED), and the remaining fields from the cup-product input.
Kind: definition. -/
def switchRetentionInputs_dual {T : Finset ι} {p : ι} {hp : p ∉ T}
    (C : DualCupInputs K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc T p hp) :
    SwitchRetentionInputs K S₀ S k M Δ place X EU T p hp
      (dsuppDataS K S₀ S k M' Δ' place X' EU' T) (dfS K S₀ S k M' Δ' place X' EU' T p) where
  E := dualCupE K S k Tm
  EL := dualCupEL K S₀ S k place Tm
  resE := dualCupResE K S₀ S k place Tm
  cupG := dualCupG K S k M M' Tm β hβ hβc
  cupL := dualCupL K S₀ S k M place M' Tm β hβ hβc
  compat := dualCup_compat K S₀ S k M place M' Tm β hβ hβc
  old := C.old
  old_avoid := C.old_avoid
  Uo' := (dpresCondS K S₀ S k M' Δ' place X' EU' T).U
  hv := C.hv
  Uq' := switchUq K S k place X' p
  hq := C.hq
  pS := dpS K S₀ S k M' Δ' place X' EU' T p
  pPp := dpPp K S₀ S k M' Δ' place X' EU' T
  qPp := dqPp K S₀ S k M' Δ' place X' EU' T p hp
  isoR := C.isoR
  isoP := C.isoP
  ret_S := dret_S K S₀ S k M' Δ' place X' EU' T p
  q_S := dq_S K S₀ S k M' Δ' place X' EU' T p hp

variable {K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc} in
/-- **The types line up: the cup products of the retention inputs are those of lane RC26's
truncated pairing data at the conditions of the switch** (tex 4164–4167, 3829–3833): for every
truncated isotropy datum `I` of `dpresCondS T` against `presCondS (T ∪ {p})`, the targets, the
restriction and the cup products of `switchRetentionInputs_dual C` are those of
`genuinePairDataT … I : SelPairData (dsuppDataS T) (suppDataS (T ∪ {p}))`.
Kind: PROVED (definitional). -/
theorem switchRetentionInputs_dual_eq_genuinePairDataT {T : Finset ι} {p : ι} {hp : p ∉ T}
    (C : DualCupInputs K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc T p hp)
    (I : TruncIsotropyData k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) β hβ hβc
      (dpresCondS K S₀ S k M' Δ' place X' EU' T)
      (presCondS K S₀ S k M Δ place X EU (insert p T))) :
    (switchRetentionInputs_dual C).E = (genuinePairDataT k (GKS K S) (presGv K S₀ S place)
        (presLoc K S₀ S place) β hβ hβc _ _ I).E ∧
      (switchRetentionInputs_dual C).EL = (genuinePairDataT k (GKS K S) (presGv K S₀ S place)
        (presLoc K S₀ S place) β hβ hβc _ _ I).EL ∧
      (switchRetentionInputs_dual C).resE = (genuinePairDataT k (GKS K S) (presGv K S₀ S place)
        (presLoc K S₀ S place) β hβ hβc _ _ I).resE ∧
      (switchRetentionInputs_dual C).cupG = (genuinePairDataT k (GKS K S) (presGv K S₀ S place)
        (presLoc K S₀ S place) β hβ hβc _ _ I).cupG ∧
      (switchRetentionInputs_dual C).cupL = (genuinePairDataT k (GKS K S) (presGv K S₀ S place)
        (presLoc K S₀ S place) β hβ hβc _ _ I).cupL :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

variable {K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc} in
/-- **The compatibility of the retained homotopies across consecutive steps** (tex 4159,
4162–4167): for the step at `T` (switch `p`) and the step at `T ∪ {p}` (switch `p'`), the relaxed
homotopy of the first and the primitive homotopy of the second agree on
`U¹_{(T ∪ {p})⊥} × U²_{T ∪ {p}}`, in the truncated target (so modulo the coboundaries of the full
local target). This is the one compatibility of the cup data across steps used by
`dual_pairedFun_consecutive`; `dual_pairedFun_consecutive_iff` shows what it is needed for.
Kind: definition (a named hypothesis, GLUE with `DualCupInputs`). -/
def RetainedHomotopyStep {T : Finset ι} {p p' : ι} {hp : p ∉ T} {hp' : p' ∉ insert p T}
    (C₁ : DualCupInputs K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc T p hp)
    (C₂ : DualCupInputs K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc (insert p T) p' hp') :
    Prop :=
  ∀ (u : (dsuppDataS K S₀ S k M' Δ' place X' EU' (insert p T)).U.X 1)
    (v : (suppDataS K S₀ S k M Δ place X EU (insert p T)).U.X 2),
    switchHR K S₀ S k M Δ place X EU T p C₁.old C₁.hv (dpS K S₀ S k M' Δ' place X' EU' T p) 1 2 2
        rfl u v =
      switchHP K S₀ S k M Δ place X EU (insert p T) p' hp'
        (DPp := dsuppDataS K S₀ S k M' Δ' place X' EU' (insert p T)) C₂.old C₂.hv C₂.hq
        (dpPp K S₀ S k M' Δ' place X' EU' (insert p T))
        (dqPp K S₀ S k M' Δ' place X' EU' (insert p T) p' hp') 1 2 2 rfl u v

variable {K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc} in
/-- **The consecutive-step identity, exactly** (tex 4159, 4164–4174, 3750–3752): for the step at `T`
(switch `p`) and the step at `T ∪ {p}` (switch `p'`) with the pinned cup products and one trace,
for a class `z` of `C¹_{(T ∪ {p})⊥}` (the strict side of the first step is the orthogonal side of
the second, `selRestrict_dsuppDataS`) and `w ∈ C²_{T ∪ {p}}`,
`pairedFun QP(step T ∪ {p}) tr z w = pairedFun QR(step T) tr z w` iff the trace takes the same
value on the two homotopy terms `(0, h_P(z, w))`, `(0, h_R(z, w))`: the global part, the local
part with `ι` (`restrict_ι_eq`) and the restriction part agree identically. Kind: PROVED. -/
theorem dual_pairedFun_consecutive_iff {T : Finset ι} {p p' : ι} {hp : p ∉ T}
    {hp' : p' ∉ insert p T}
    (C₁ : DualCupInputs K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc T p hp)
    (C₂ : DualCupInputs K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc (insert p T) p' hp')
    (tr : (coneCx (dualCupResE K S₀ S k place Tm)).X 3 →ₗ[k] k)
    (z : (selCx (dsuppDataS K S₀ S k M' Δ' place X' EU' (insert p T))).X 1)
    (w : (suppCxS K S₀ S k M Δ place X EU (insert p T)).X 2) :
    pairedFun (switchRetentionInputs_dual C₂).toPlaceRetentionG.toRetainedPairing.QP tr z w =
        pairedFun (switchRetentionInputs_dual C₁).toPlaceRetentionG.toRetainedPairing.QR tr z w ↔
      tr ((0, switchHP K S₀ S k M Δ place X EU (insert p T) p' hp'
          (DPp := dsuppDataS K S₀ S k M' Δ' place X' EU' (insert p T)) C₂.old C₂.hv C₂.hq
          (dpPp K S₀ S k M' Δ' place X' EU' (insert p T))
          (dqPp K S₀ S k M' Δ' place X' EU' (insert p T) p' hp') 1 2 2 rfl z.2.1 w.2.1) :
          coneT (dualCupResE K S₀ S k place Tm) 3) =
        tr ((0, switchHR K S₀ S k M Δ place X EU T p C₁.old C₁.hv
          (dpS K S₀ S k M' Δ' place X' EU' T p) 1 2 2 rfl z.2.1 w.2.1) :
          coneT (dualCupResE K S₀ S k place Tm) 3) := by
  obtain ⟨a, u, x⟩ := z
  obtain ⟨b, v, y⟩ := w
  have hι : (ghomComp (switchFP K S₀ S k M Δ place X EU (insert p T) p')
      (suppDataS K S₀ S k M Δ place X EU (insert p' (insert p T))).ι).f 2 2 rfl v =
      (suppDataS K S₀ S k M Δ place X EU (insert p T)).ι.f 2 2 rfl v :=
    restrict_ι_eq (presCondInclS K S₀ S k M Δ place X EU (insert p T) p') 2 2 rfl v
  have key : ∀ (A : (dualCupE K S k Tm).X 3) (B B' H H' : (dualCupEL K S₀ S k place Tm).X (3 - 1)),
      B = B' →
      (tr (show (coneCx (dualCupResE K S₀ S k place Tm)).X 3 from (A, B + H)) =
          tr (show (coneCx (dualCupResE K S₀ S k place Tm)).X 3 from (A, B' + H')) ↔
        tr (show (coneCx (dualCupResE K S₀ S k place Tm)).X 3 from (0, H)) =
          tr (show (coneCx (dualCupResE K S₀ S k place Tm)).X 3 from (0, H'))) := by
    intro A B B' H H' hB
    subst hB
    have e : ∀ H₀ : (dualCupEL K S₀ S k place Tm).X (3 - 1),
        tr (show (coneCx (dualCupResE K S₀ S k place Tm)).X 3 from (A, B + H₀)) =
          tr (show (coneCx (dualCupResE K S₀ S k place Tm)).X 3 from (A, B)) +
            tr (show (coneCx (dualCupResE K S₀ S k place Tm)).X 3 from (0, H₀)) := fun H₀ => by
      rw [← map_add]
      exact congrArg tr (Prod.ext (add_zero A).symm rfl)
    rw [e, e]
    exact add_right_inj _
  exact key ((dualCupG K S k M M' Tm β hβ hβc).P 1 2 3 rfl a b)
    ((dualCupL K S₀ S k M place M' Tm β hβ hβc).P (1 - 1) 2 (3 - 1) (by omega) x
        ((ghomComp (switchFP K S₀ S k M Δ place X EU (insert p T) p')
          (suppDataS K S₀ S k M Δ place X EU (insert p' (insert p T))).ι).f 2 2 rfl v) +
      sgn 1 • (dualCupL K S₀ S k M place M' Tm β hβ hβc).P 1 (2 - 1) (3 - 1) (by omega)
        ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M').f 1 1 rfl a) y)
    ((dualCupL K S₀ S k M place M' Tm β hβ hβc).P (1 - 1) 2 (3 - 1) (by omega) x
        ((suppDataS K S₀ S k M Δ place X EU (insert p T)).ι.f 2 2 rfl v) +
      sgn 1 • (dualCupL K S₀ S k M place M' Tm β hβ hβc).P 1 (2 - 1) (3 - 1) (by omega)
        ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M').f 1 1 rfl a) y)
    (switchHP K S₀ S k M Δ place X EU (insert p T) p' hp'
      (DPp := dsuppDataS K S₀ S k M' Δ' place X' EU' (insert p T)) C₂.old C₂.hv C₂.hq
      (dpPp K S₀ S k M' Δ' place X' EU' (insert p T))
      (dqPp K S₀ S k M' Δ' place X' EU' (insert p T) p' hp') 1 2 2 rfl u v)
    (switchHR K S₀ S k M Δ place X EU T p C₁.old C₁.hv (dpS K S₀ S k M' Δ' place X' EU' T p)
      1 2 2 rfl u v)
    (by rw [hι])

variable {K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc} in
/-- **The consecutive-step contract** (tex 4159, 4164–4174, 3750–3752): under the compatibility
`RetainedHomotopyStep` of the retained homotopies, for one trace and a class `z` of
`C¹_{(T ∪ {p})⊥}`, the primitive paired functional of the step at `T ∪ {p}` and the relaxed paired
functional of the step at `T` are the same linear map on `C²_{T ∪ {p}}`. Kind: PROVED. -/
theorem dual_pairedFun_consecutive {T : Finset ι} {p p' : ι} {hp : p ∉ T}
    {hp' : p' ∉ insert p T}
    (C₁ : DualCupInputs K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc T p hp)
    (C₂ : DualCupInputs K S₀ S k M Δ place X EU M' Δ' X' EU' Tm β hβ hβc (insert p T) p' hp')
    (hC : RetainedHomotopyStep C₁ C₂)
    (tr : (coneCx (dualCupResE K S₀ S k place Tm)).X 3 →ₗ[k] k)
    (z : (selCx (dsuppDataS K S₀ S k M' Δ' place X' EU' (insert p T))).X 1) :
    pairedFun (switchRetentionInputs_dual C₂).toPlaceRetentionG.toRetainedPairing.QP tr z =
      pairedFun (switchRetentionInputs_dual C₁).toPlaceRetentionG.toRetainedPairing.QR tr z :=
  LinearMap.ext fun w => (dual_pairedFun_consecutive_iff C₁ C₂ tr z w).2 (by
    rw [hC z.2.1 w.2.1])

end Dual

section Lift

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] [TopologicalSpace k]
  {M' : Type} [AddCommGroup M'] [Module k M'] [DistribMulAction (GKS K S) M']
  [SMulCommClass (GKS K S) k M'] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousSMul (GKS K S) M']
  {Δ' Δ'' : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M'}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S}
  {X' : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1)}
  {EU' : ∀ j, SplitInclusion (genuineUq K S k (place j) (X' j)) (genuineLq K S k M' (place j))}

/-- **The paired strict class** `z_S = ψ_{T ∪ {p}}(z'_R)` (tex 4169–4171, 3740–3745): the image
of a transported class of `C'_{T ∪ {p}}` under lane E2's inverse of the orthogonal comparison, a
class of the strict side `selRestrict (dsuppDataS T) (dfS T p)`. Kind: definition. -/
def dualZS (Ψ : OrthComparisonInverse K S₀ S k M' Δ' Δ'' place X' EU') (T : Finset ι) (p : ι)
    (zR : (suppCxS K S₀ S k M' Δ'' place X' EU' (insert p T)).X 1) :
    (selCx (selRestrict (dsuppDataS K S₀ S k M' Δ' place X' EU' T)
      (dfS K S₀ S k M' Δ' place X' EU' T p))).X 1 :=
  Ψ.ψ (insert p T) 1 zR

/-- **The orthogonal class** `z_{P⊥} = ψ_T(z'_P)` (tex 4169–4171, 3740–3745). Kind: definition. -/
def dualZP (Ψ : OrthComparisonInverse K S₀ S k M' Δ' Δ'' place X' EU') (T : Finset ι)
    (zP : (suppCxS K S₀ S k M' Δ'' place X' EU' T).X 1) :
    (selCx (dsuppDataS K S₀ S k M' Δ' place X' EU' T)).X 1 :=
  Ψ.ψ T 1 zP

/-- **The retained boundary of the paired strict lift** `b = j(ψ_{T ∪ {p}}(b'))` (tex 4169–4171).
Kind: definition. -/
def dualB (Ψ : OrthComparisonInverse K S₀ S k M' Δ' Δ'' place X' EU') (T : Finset ι) (p : ι)
    (b' : (suppCxS K S₀ S k M' Δ'' place X' EU' (insert p T)).X 0) :
    (selCx (dsuppDataS K S₀ S k M' Δ' place X' EU' T)).X 0 :=
  (changeMap (dsuppDataS K S₀ S k M' Δ' place X' EU' T)
    (dfS K S₀ S k M' Δ' place X' EU' T p)).f 0 0 rfl (Ψ.ψ (insert p T) 0 b')

/-- **The paired strict lift `j z_S = e z_{P⊥} + d b`** (tex 4169–4171, 3740–3745): from the
transported norm identity `z'_R = e · i'(z'_P) + d b'` in `C'_{T ∪ {p}}` and lane E2's inverse `Ψ`
of the orthogonal comparison (GLUE, the one named input; lane E2's `hlift_stepRetention`). This
is the field `hlift` of `StepRetention`. Kind: PROVED (from `Ψ`). -/
theorem dual_hlift (Ψ : OrthComparisonInverse K S₀ S k M' Δ' Δ'' place X' EU') {T : Finset ι}
    {p : ι} (hp : p ∉ T) (zR : (suppCxS K S₀ S k M' Δ'' place X' EU' (insert p T)).X 1)
    (zP : (suppCxS K S₀ S k M' Δ'' place X' EU' T).X 1) (e : k)
    (b' : (suppCxS K S₀ S k M' Δ'' place X' EU' (insert p T)).X 0)
    (hnorm : zR = e • (suppInclS K S₀ S k M' Δ'' place X' EU' T p).f 1 1 rfl zP +
      (suppCxS K S₀ S k M' Δ'' place X' EU' (insert p T)).d 0 1 rfl b') :
    (changeMap (dsuppDataS K S₀ S k M' Δ' place X' EU' T)
        (dfS K S₀ S k M' Δ' place X' EU' T p)).f 1 1 rfl (dualZS Ψ T p zR) =
      e • dualZP Ψ T zP + (selCx (dsuppDataS K S₀ S k M' Δ' place X' EU' T)).d 0 1 rfl
        (dualB Ψ T p b') :=
  hlift_stepRetention Ψ hp zR zP e b' hnorm

/-- The strict class of the step at `T` is the orthogonal class of the step at `T ∪ {p}` for the
same transported class (tex 4159–4161; `selRestrict_dsuppDataS`). Kind: PROVED (definitional). -/
theorem dualZS_eq_dualZP (Ψ : OrthComparisonInverse K S₀ S k M' Δ' Δ'' place X' EU')
    (T : Finset ι) (p : ι) (zR : (suppCxS K S₀ S k M' Δ'' place X' EU' (insert p T)).X 1) :
    dualZP Ψ (insert p T) zR = dualZS Ψ T p zR :=
  rfl

end Lift

section Stage

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  [∀ s, TopologicalSpace (StageRing s)]
  {M : ℕ → Type} [∀ s, AddCommGroup (M s)] [∀ s, Module (StageRing s) (M s)]
  [∀ s, DistribMulAction (GKS K S) (M s)] [∀ s, SMulCommClass (GKS K S) (StageRing s) (M s)]
  [∀ s, TopologicalSpace (M s)] [∀ s, DiscreteTopology (M s)]
  [∀ s, ContinuousSMul (GKS K S) (M s)]
  {Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (M s)}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S}
  {X : ∀ s, (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1)}
  {EU : ∀ s j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X s j))
    (genuineLq K S (StageRing s) (M s) (place j))}
  {s : ℕ}
  {M' : Type} [AddCommGroup M'] [Module (StageRing s) M'] [DistribMulAction (GKS K S) M']
  [SMulCommClass (GKS K S) (StageRing s) M'] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousSMul (GKS K S) M']
  {Δ' Δ'' : LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M'}
  {X' : (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1)}
  {EU' : ∀ j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X' j))
    (genuineLq K S (StageRing s) M' (place j))}
  {Tm : Type} [AddCommGroup Tm] [Module (StageRing s) Tm] [DistribMulAction (GKS K S) Tm]
  [SMulCommClass (GKS K S) (StageRing s) Tm] [TopologicalSpace Tm] [ContinuousAdd Tm]
  [ContinuousConstSMul (StageRing s) Tm] [ContinuousSMul (GKS K S) Tm]
  {β : M' →ₗ[StageRing s] M s →ₗ[StageRing s] Tm}
  {hβ : ∀ (g : GKS K S) (a : M') (b : M s), β (g • a) (g • b) = g • β a b}
  {hβc : Continuous fun x : M' × M s => β x.1 x.2}

variable (K S₀ S M Δ place X EU) in
/-- **The retention data of one switch of the genuine chain from lane E2's dual chain**
(tex 4157–4175, 4385–4451): at a coefficient stage `s`, lane RC32's `StepRetention` with
`DPp = dsuppDataS T`, `fS = dfS T p`, the retention inputs `switchRetentionInputs_dual C`, a trace
of the pinned cone, the paired classes `dualZS`, `dualZP`, the factor `e`, the boundary `dualB` and
the paired strict lift `dual_hlift`. Kind: definition. -/
def StepRetention.ofDual {T : Finset ι} {p : ι} (hp : p ∉ T)
    (C : DualCupInputs K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) M' Δ' X' EU' Tm β
      hβ hβc T p hp)
    (tr : (coneCx (dualCupResE K S₀ S (StageRing s) place Tm)).X 3 →ₗ[StageRing s] StageRing s)
    (htr : ∀ x, tr ((coneCx (dualCupResE K S₀ S (StageRing s) place Tm)).d 2 3 rfl x) = 0)
    (Ψ : OrthComparisonInverse K S₀ S (StageRing s) M' Δ' Δ'' place X' EU')
    (zR : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p T)).X 1)
    (zP : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' T).X 1) (e : StageRing s)
    (b' : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p T)).X 0)
    (hnorm : zR = e • (suppInclS K S₀ S (StageRing s) M' Δ'' place X' EU' T p).f 1 1 rfl zP +
      (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p T)).d 0 1 rfl b') :
    StepRetention K S₀ S M Δ place X EU s T p hp where
  DPp := dsuppDataS K S₀ S (StageRing s) M' Δ' place X' EU' T
  US := (dsuppDataS K S₀ S (StageRing s) M' Δ' place X' EU' (insert p T)).U
  fS := dfS K S₀ S (StageRing s) M' Δ' place X' EU' T p
  I := switchRetentionInputs_dual C
  tr := tr
  htr := htr
  zS := dualZS Ψ T p zR
  zP := dualZP Ψ T zP
  e := e
  b := dualB Ψ T p b'
  hlift := dual_hlift Ψ hp zR zP e b' hnorm

/-- **The consecutive-step contract for the retention data** (tex 4159, 4164–4174,
3750–3752): for the retention data of the step at `T` and of the step at `T ∪ {p}` built from
lane E2's dual chain with one trace and one inverse `Ψ`, if the transported primitive class of
the second step is the transported relaxed class of the first (`z'_{P,2} = z'_{R,1}`) and the
retained homotopies are compatible (`RetainedHomotopyStep`), then `λ_P` of the second step is
`λ_R` of the first, as linear maps on `C²_{T ∪ {p}}`. Kind: PROVED. -/
theorem StepRetention.ofDual_consecutive {T : Finset ι} {p p' : ι} (hp : p ∉ T)
    (hp' : p' ∉ insert p T)
    (C₁ : DualCupInputs K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) M' Δ' X' EU' Tm β
      hβ hβc T p hp)
    (C₂ : DualCupInputs K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) M' Δ' X' EU' Tm β
      hβ hβc (insert p T) p' hp')
    (hC : RetainedHomotopyStep C₁ C₂)
    (tr : (coneCx (dualCupResE K S₀ S (StageRing s) place Tm)).X 3 →ₗ[StageRing s] StageRing s)
    (htr : ∀ x, tr ((coneCx (dualCupResE K S₀ S (StageRing s) place Tm)).d 2 3 rfl x) = 0)
    (Ψ : OrthComparisonInverse K S₀ S (StageRing s) M' Δ' Δ'' place X' EU')
    (zR₁ : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p T)).X 1)
    (zP₁ : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' T).X 1) (e₁ : StageRing s)
    (b₁ : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p T)).X 0)
    (hn₁ : zR₁ = e₁ • (suppInclS K S₀ S (StageRing s) M' Δ'' place X' EU' T p).f 1 1 rfl zP₁ +
      (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p T)).d 0 1 rfl b₁)
    (zR₂ : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p' (insert p T))).X 1)
    (zP₂ : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p T)).X 1)
    (e₂ : StageRing s)
    (b₂ : (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p' (insert p T))).X 0)
    (hn₂ : zR₂ = e₂ • (suppInclS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p T) p').f 1
        1 rfl zP₂ +
      (suppCxS K S₀ S (StageRing s) M' Δ'' place X' EU' (insert p' (insert p T))).d 0 1 rfl b₂)
    (hz : zP₂ = zR₁) :
    pairedFun (StepRetention.ofDual K S₀ S M Δ place X EU hp' C₂ tr htr Ψ zR₂ zP₂ e₂ b₂
        hn₂).I.toPlaceRetentionG.toRetainedPairing.QP
      (StepRetention.ofDual K S₀ S M Δ place X EU hp' C₂ tr htr Ψ zR₂ zP₂ e₂ b₂ hn₂).tr
      (StepRetention.ofDual K S₀ S M Δ place X EU hp' C₂ tr htr Ψ zR₂ zP₂ e₂ b₂ hn₂).zP =
    pairedFun (StepRetention.ofDual K S₀ S M Δ place X EU hp C₁ tr htr Ψ zR₁ zP₁ e₁ b₁
        hn₁).I.toPlaceRetentionG.toRetainedPairing.QR
      ((StepRetention.ofDual K S₀ S M Δ place X EU hp C₁ tr htr Ψ zR₁ zP₁ e₁ b₁ hn₁).tr :
        (coneCx (StepRetention.ofDual K S₀ S M Δ place X EU hp C₁ tr htr Ψ zR₁ zP₁ e₁ b₁
          hn₁).I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3 →ₗ[StageRing s] StageRing s)
      (StepRetention.ofDual K S₀ S M Δ place X EU hp C₁ tr htr Ψ zR₁ zP₁ e₁ b₁ hn₁).zS := by
  change pairedFun (switchRetentionInputs_dual C₂).toPlaceRetentionG.toRetainedPairing.QP tr
      (dualZP Ψ (insert p T) zP₂) =
    pairedFun (switchRetentionInputs_dual C₁).toPlaceRetentionG.toRetainedPairing.QR tr
      (dualZS Ψ T p zR₁)
  rw [hz, ← dualZS_eq_dualZP]
  exact dual_pairedFun_consecutive C₁ C₂ hC tr _

end Stage

end ZInQ.Manuscript.RC.Wiring
