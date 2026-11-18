import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer
import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.CdOne
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalConsistency

/-!
# The procyclic two-term model on genuine continuous cochains (stage (b) of the tame model)

Manuscript `diophantine_zq.tex`, tex (4.4) at L3443–3448 and the unramified complex
`[Φ − 1]` at L3478–3481. For a procyclic group `G` with a continuous isomorphism
`e : G ≃ₜ* ℤ̂` (topological generator `Frob = e⁻¹(1)`; for instance the unramified quotient
`Gal(K_q^ur/K_q)`), and a finite discrete `k`-module `M` with a continuous `G`-action, the two-term
complex `[M --(Frob − 1)--> M]` (`tU M Φ` of `NewLocalConsistency.lean`) maps to the GENUINE
continuous cochains `C^•_cont(G, M)` of lane RC26 (`contCochains`, extended by zero to `ℤ` by
`natCx`):

* degree `0`: `m ↦` the constant cochain `m`; degree `1`: `w ↦` the continuous cocycle
  `g ↦ Σ_{j < χ(g)} Frob^j • w` of the unramified-complex lane (`cocycleOf`, `χ : G → ℤ/P` the
  character with `χ(Frob) = 1`);
* `twoTermToCont` (PROVED): this is a chain map (`coc_sub`: the cocycle of `Frob • m − m` is the
  coboundary `g ↦ g • m − m`; `coc_cocycle`);
* `subsingleton_contCohomology_two` (PROVED): `H²_cont(G, M) = 0` on the genuine cochains (the
  unramified-complex lane's `H²(ℤ̂, M) = 0` through lane RC26's `contH2AddEquiv`).

Degrees `0` and `1` of the comparison are the unramified-complex lane's `h0Equiv`, `h1CoinvEquiv`
(through `contH0AddEquiv`, `contH1AddEquiv`). Degrees `≥ 3` need the identification of
`contCohomology` with Mathlib's `continuousCohomology` in all degrees (lane RC26 has it in degrees
`≤ 2`), which is open. The tame inertia `I^t ≅ ∏_{ℓ ≠ p} ℤ_ℓ(1)` is not `ℤ̂`; it is not available as
an object of the library (stages (a), (c) are not attempted; see the lane notes for the sizing).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TameModel

open CategoryTheory TauCeti TauCeti.ContCohomology ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.ClearingComplex (tU tUX tUd)

attribute [local instance] TopRep.distribMulAction

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [Finite M]
  (e : G ≃ₜ* TauCeti.zHat.{0})

/-- `M` as a topological representation (Tau Ceti), for the unramified-complex lane's results. -/
abbrev XM (G : Type) [Group G] (M : Type) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] : TopRep ℤ G :=
  TauCeti.ofDiscreteModule ℤ G M

instance instCSXM : ContinuousSMul G (XM G M).V := inferInstanceAs (ContinuousSMul G M)
instance instFinXM : Finite (XM G M).V := inferInstanceAs (Finite M)

/-! ### `H²` of the genuine continuous cochains vanishes -/

include e in
/-- **`H²_cont(G, M) = 0` on lane RC26's genuine continuous cochains** for `G ≃ₜ* ℤ̂` and finite
discrete `M` (PROVED). -/
theorem subsingleton_contCohomology_two [CompactSpace G] [TotallyDisconnectedSpace G] :
    Subsingleton (contCohomology k G M 2) := by
  refine ⟨fun a b => (contH2AddEquiv k G M).injective ?_⟩
  have h := fun x => h2_eq_zero e (XM G M) x
  exact (h _).trans (h _).symm

/-! ### The cocycle attached to an element -/

/-- A period of the Frobenius on `M`. -/
def per : ℕ := (exists_period e (XM G M)).choose

theorem per_pos : 0 < per (M := M) e := (exists_period e (XM G M)).choose_spec.1

theorem per_spec : ∀ x : (XM G M).V, frobElt e ^ per (M := M) e • x = x :=
  (exists_period e (XM G M)).choose_spec.2

theorem neZeroPeriod : NeZero (period (XM G M) (per (M := M) e)) :=
  ⟨(Nat.lt_trans Nat.zero_lt_one (one_lt_period (XM G M) (per_pos e))).ne'⟩

/-- The cocycle `g ↦ Σ_{j < χ(g)} Frob^j • w`. -/
def coc (w : M) : G → M :=
  haveI := neZeroPeriod (M := M) e
  cocycleOf e (XM G M) (per (M := M) e) w

theorem coc_mem (w : M) : coc e w ∈ Z1 G M :=
  haveI := neZeroPeriod (M := M) e
  cocycleOf_mem e (XM G M) (N := per (M := M) e) (per_spec e) w

theorem coc_cont (w : M) : Continuous (coc e w) := (mem_Z1_iff.1 (coc_mem e w)).1

theorem coc_cocycle (w : M) (g h : G) : coc e w (g * h) = g • coc e w h + coc e w g :=
  (mem_Z1_iff.1 (coc_mem e w)).2 g h

theorem coc_add (w w' : M) : coc e (w + w') = coc e w + coc e w' := by
  funext g
  change ∑ j ∈ Finset.range _, frobElt e ^ j • (w + w') =
    (∑ j ∈ Finset.range _, frobElt e ^ j • w) + ∑ j ∈ Finset.range _, frobElt e ^ j • w'
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => smul_add _ _ _

theorem coc_smul (r : k) (w : M) : coc e (r • w) = r • coc e w := by
  funext g
  change ∑ j ∈ Finset.range _, frobElt e ^ j • (r • w) = r • ∑ j ∈ Finset.range _, frobElt e ^ j • w
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ r w

/-- **The cocycle of `Frob • m − m` is the coboundary of `m`.** -/
theorem coc_sub (m : M) (g : G) : coc e (frobElt e • m - m) g = g • m - m := by
  haveI := neZeroPeriod (M := M) e
  have hg : g • m = frobElt e ^ ((chi e (period (XM G M) (per (M := M) e)) g).toAdd.val) • m :=
    smul_eq_chi e (XM G M) (N := per (M := M) e) (per_spec e) g m
  change ∑ j ∈ Finset.range ((chi e (period (XM G M) (per (M := M) e)) g).toAdd.val),
      frobElt e ^ j • (frobElt e • m - m) = g • m - m
  rw [hg]
  have : ∀ j : ℕ, frobElt e ^ j • (frobElt e • m - m) =
      frobElt e ^ (j + 1) • m - frobElt e ^ j • m := fun j => by
    rw [smul_sub, ← mul_smul, ← pow_succ]
  simp only [this]
  rw [Finset.sum_range_sub (fun j => frobElt e ^ j • m), pow_zero, one_smul]

/-! ### The chain map -/

/-- The Frobenius as a `k`-linear endomorphism of `M`. -/
def Φk : M →ₗ[k] M where
  toFun m := frobElt e • m
  map_add' := smul_add _
  map_smul' r m := smul_comm _ r m

/-- The components of the comparison `[M --(Frob − 1)--> M] → C^•_cont(G, M)`. -/
def compT : (i : ℤ) → (tU M (Φk (k := k) e)).X i →ₗ[k] (natCx (contCochains k G M)).X i
  | 0 =>
    { toFun := fun (m : M) => mkCochain0 (k := k) (G := G) m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | 1 =>
    { toFun := fun (w : M) => mkCochain1 (k := k) (coc e w) (coc_cont e w)
      map_add' := fun (w w' : M) => contCochains_ext fun v => by
        change coc e (w + w') (v 0) = coc e w (v 0) + coc e w' (v 0)
        rw [coc_add]; rfl
      map_smul' := fun r (w : M) => contCochains_ext fun v => by
        change coc e (r • w) (v 0) = r • coc e w (v 0)
        rw [coc_smul]; rfl }
  | _ => 0

theorem fin1_eq (v : Fin 1 → G) : v = fun _ => v 0 := by
  funext i; rw [Subsingleton.elim i 0]

theorem fin2_eq (v : Fin 2 → G) : v = ![v 0, v 1] := by
  funext i; fin_cases i <;> rfl

theorem comm0 (m : M) :
    mkCochain1 (k := k) (coc e (frobElt e • m - m)) (coc_cont e _) =
      ((contCochains k G M).d 0 1).hom (mkCochain0 (k := k) (G := G) m) := by
  refine contCochains_ext fun v => ?_
  rw [fin1_eq v, contFun_d01, contFun_mkCochain1, coc_sub]
  rfl

theorem comm1 (w : M) :
    ((contCochains k G M).d 1 2).hom (mkCochain1 (k := k) (coc e w) (coc_cont e w)) = 0 := by
  refine contCochains_ext fun v => ?_
  rw [fin2_eq v, contFun_d12, contFun_zero_apply]
  change v 0 • coc e w (v 1) - coc e w (v 0 * v 1) + coc e w (v 0) = 0
  rw [coc_cocycle]
  abel

theorem compT_comm (i : ℤ) (x : (tU M (Φk (k := k) e)).X i) :
    compT e (i + 1) ((tU M (Φk (k := k) e)).d i (i + 1) rfl x) =
      (natCx (contCochains k G M)).d i (i + 1) rfl (compT e i x) := by
  match i with
  | 0 => exact comm0 e (show M from x)
  | 1 => exact (comm1 e (show M from x)).symm
  | 2 => exact (map_zero _).symm
  | Int.ofNat (n + 3) => exact (map_zero _).symm
  | Int.negSucc n =>
    change compT e (Int.negSucc n + 1) 0 = (natCx (contCochains k G M)).d _ _ rfl 0
    exact (map_zero _).trans (map_zero _).symm

/-- **The procyclic two-term model maps to the genuine continuous cochains** (a chain map;
PROVED). -/
def twoTermToCont : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom (tU M (Φk (k := k) e))
    (natCx (contCochains k G M)) where
  f i j h := by subst h; exact compT e i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact compT_comm e i x

end ZInQ.Contrib.CloudB3RC53.TameModel
