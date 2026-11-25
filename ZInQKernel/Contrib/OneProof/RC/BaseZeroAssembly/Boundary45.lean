import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Transfer
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Interfaces
import ZInQKernel.Contrib.OneProof.RC.Central.BaseZero

/-!
# Lane RC25 (base zero), part 2: the retained boundary (4.5) at the base

Lemma `ex:arith-base-zero` (`diophantine_zq.tex`, 11/5 version, tex 4330–4376) uses (4.5) once
(tex 4345–4348):

> The conductor-one height formula makes the specified point torsion when `L'(E/K,1)=0`. Thus its
> rational Kummer class vanishes, and the retained boundary (4.5) makes the specialization of the
> actual cycle `z` zero.

The boundary (4.5) is proved in Lemma `ex:arith-central-specialization` (tex 3895–3986):

> The finite classes of Proposition `ex:arith-finite-heegner` satisfy the retained boundary (4.5),
> with the same fixed `L`. [...] The split norm relation gives an actual finite-stage boundary
> `z_i(0) − L m_i j_i(b_h) = d v_i`, `m_i = a_{r_i} − 2χ_h(r_i)` (4.5). The equality in global
> cohomology lifts to the Selmer cone because the local degree-zero maps are onto and the degree-one
> maps inject. Retain `v_i`. The uniform trace bound bounds `v₂(m_i)` and the local determinants by
> `c_E`; their adjugate identities multiplied by a fixed power of two survive the limit.
> [...] The boundary (4.5) gives `z_0 = i(LmP)`.

At the base `h₀ = 1` the quadratic character `χ₁` is trivial and at `t = 0` the moving character is
trivial (tex 4280–4281), so the weighted point of the class at conductor `r_i` is the plain trace
`Tr_{H_{r_i}/K} y_{r_i}`; `b₁ = Tr_{H_1/K} y_1` is the specified point `P` (the conductor-one point
of the height formula). The split norm relation (4.1) (tex 2924–2932; Cai–Chen–Liu Thm 2.15 through
`φ`, PRINT, which weights the trace by `u_1 = [𝒪_K^× : ℤ^×]`; the unweighted form here is the print
when `D_K < -4`, `cclUnitFactor_eq_one_of_discr_lt`) at the split moving prime
gives `Tr_{H_{r}/K} y_{r} = (a_r − 2) P` (lane RC10's
twisted-sum algebra `B1b_twisted_split_norm`, with `θ = 1`). For `I = ∅` the class is the Kummer
class of the `L`-multiplied weighted point (Proposition `ex:arith-finite-heegner`, tex 2867–2868,
3293–3295; lane RC10's `H11_empty`).

Contents (every theorem `PROVED`):

1. `SplitNormStage P` (the data of one finite stage at the base: the ring-class group
   `Δ = Gal(H_r/K)` acting on the points `E(H_r)`, `N = Gal(H_r/H_1)`, lifts `T` of `Gal(H_1/K)`,
   `y_1`, `y_r`, the trace `a_r`, a Frobenius `σ_r`, (4.1) at `(d, q) = (1, r)`, `E(K) ⊂ E(H_r)`,
   `P = Tr_{H_1/K} y_1` and the weighted point `W = Tr_{H_r/K} y_r ∈ E(K)`);
   `SplitNormStage.weightedPoint_eq`: `W = (a_r − 2) • P`, i.e. `m_r = a_r − 2χ₁(r)`.
2. `selmerCone_lift` (tex 3917–3918): an equality in global cohomology of two Selmer-cone cycles
   lifts to an equality in the Selmer cone, when the local degree-zero maps are onto and the
   degree-one maps inject.
3. `boundary45_finite` (tex 3912–3919, the display (4.5) at the base): at one finite stage,
   `z(0) − L m j(P) = d v` in the Selmer cone, with `v` explicit (retained).
   `classAtBase_of_construction` (tex 2867–2868, 3030–3032, 3074–3081, 3258–3262, 3293–3295): the
   class of the base is the Kummer class of the `L`-multiplied weighted point with
   `L = m₀ C_π C_bad 2^{2e}` (lane RC10's `H11_empty`, as restated by Lane RC27 over a general
   five-term sequence, and the coefficient push);
   `boundary45_finite_of_construction`: (4.5) at a finite stage "with the same fixed `L`".
4. `Boundary45Base P n z̄` (the inputs of (4.5) at the base in the central two-term model): one
   `SplitNormStage` per stage, the fixed multiplier `L ≠ 0`, the central Kummer comparison
   `κ : E(K) → ℚ₂^n`, and the limit statement `L κ(W_i) → z̄` (ELLIOT: the retained boundaries
   survive the inner limit and the central comparison `i` identifies the specialized cycle, tex
   3919–3921, 3961–3968). `Boundary45Base.central`: `z̄ = L μ κ(P)` for one `μ ∈ ℚ₂` (the limit of
   the moving multipliers `m_i` when `κ(P) ≠ 0`); `Boundary45Base.h45` is the field `h45` of the
   base model; `Boundary45Base.central_eq_zero_of_torsion` is the use at tex 4346–4348. Since
   `stage` and `kappa` are existential, `Nonempty (Boundary45Base P n z̄)` is equivalent to
   `∃ κ L, L ≠ 0 ∧ z̄ = L κ(P)`; for torsion `P` this is `z̄ = 0`. The finite-stage lemmas
   `boundary45_finite*` illustrate (4.5) and are not consumed.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly

open Finset Filter Topology

/-! ## 1. The split norm relation at the base -/

/-- **One finite stage of the class at the base** (tex 2915–2932, 3232–3233, 3281–3295, 3912–3916),
with kinds:

* `Pt` (the points `E(H_r)` over the ring class field of the moving conductor `r`), `Δ`
  (`Gal(H_r/K)`, finite abelian), `act` (the Galois action), `N` (`Gal(H_r/H_1)`), `T` (one lift
  of each element of `Gal(H_1/K)`, i.e. a transversal of `N`): definition;
* `y1 ∈ E(H_1)` (fixed by `N`) and `yr = y_r`: the CM points `π(x_1)`, `π(x_r)` (tex 2915–2917):
  definition;
* `a` (`a_r`), `σ` (a Frobenius above `r`) and `hnorm`: the split norm relation (4.1) at
  `(d, q) = (1, r)`, `Tr_{H_r/H_1} y_r = (a_r − σ_r − σ_r⁻¹) y_1` (the content of Cai–Chen–Liu,
  Trans. AMS 370 (2018), Theorem 2.15, p. 3730, split case, through `φ`, as stated by lane RC9 in
  `HeegnerPointData.NormRelations`, split clause, which is the print once the unit index
  `u_1 = [𝒪_K^× : ℤ^×]` is one, `D_K < -4`; not a constraint inside `Boundary45Base`: the
  trivial stage satisfies it);
* `incl` (`E(K) ⊂ E(H_r)`, injective), `hP` (`P = Tr_{H_1/K} y_1`, the specified point: the
  unaveraged ring-class point `b₁`), `W`, `hW` (`W = Tr_{H_r/K} y_r ∈ E(K)`, the weighted point of
  the class at the base character and `t = 0`, where `χ₁ Ψ(0) = 1`): definition. -/
structure SplitNormStage {G : Type} [AddCommGroup G] (P : G) : Type 1 where
  /-- the points `E(H_r)` -/
  Pt : Type
  [addPt : AddCommGroup Pt]
  /-- `Δ = Gal(H_r/K)` -/
  Δ : Type
  [grpΔ : CommGroup Δ]
  [finΔ : Fintype Δ]
  [decΔ : DecidableEq Δ]
  /-- the Galois action on `E(H_r)` -/
  act : Δ →* Module.End ℤ Pt
  /-- `N = Gal(H_r/H_1)` -/
  N : Subgroup Δ
  [decN : DecidablePred (· ∈ N)]
  /-- lifts of `Gal(H_1/K)` -/
  T : Finset Δ
  /-- `T` is a transversal of `N` -/
  hT : ∀ δ : Δ, ∃! t, t ∈ T ∧ t⁻¹ * δ ∈ N
  /-- `y_1 = π(x_1)` -/
  y1 : Pt
  /-- `y_1 ∈ E(H_1)` -/
  hy1 : ∀ n ∈ N, act n y1 = y1
  /-- `y_r = π(x_r)` -/
  yr : Pt
  /-- the trace `a_r` -/
  a : ℤ
  /-- a Frobenius `σ_r` above `r` -/
  σ : Δ
  /-- (4.1) at `(d, q) = (1, r)` -/
  hnorm : ∑ n ∈ Finset.univ.filter (· ∈ N), act n yr = a • y1 - act σ y1 - act σ⁻¹ y1
  /-- `E(K) ⊂ E(H_r)` -/
  incl : G →+ Pt
  /-- it is injective -/
  hincl : Function.Injective incl
  /-- `P = Tr_{H_1/K} y_1` -/
  hP : incl P = ∑ t ∈ T, act t y1
  /-- the weighted point `Tr_{H_r/K} y_r ∈ E(K)` -/
  W : G
  /-- its definition -/
  hW : incl W = ∑ δ, act δ yr

attribute [instance] SplitNormStage.addPt SplitNormStage.grpΔ SplitNormStage.finΔ
  SplitNormStage.decΔ SplitNormStage.decN

/-- **The weighted point at the base is `m_r P`, `m_r = a_r − 2`** (tex 3912–3916: "The split norm
relation gives [...] `m_i = a_{r_i} − 2χ_h(r_i)`", at `h = 1`; tex 3289–3295 for the twisted sums).
PROVED from (4.1) by lane RC10's `B1b_twisted_split_norm` with the trivial character. -/
theorem SplitNormStage.weightedPoint_eq {G : Type} [AddCommGroup G] {P : G}
    (S : SplitNormStage P) : S.W = (S.a - 2) • P := by
  have h := HeegnerAlgebra.B1b_twisted_split_norm (A := ℤ) S.act S.N S.T S.hT 1
    (fun _ _ => rfl) S.yr S.y1 S.hy1 S.a S.σ S.hnorm
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, inv_one, Int.cast_id] at h
  apply S.hincl
  rw [S.hW, h, map_zsmul, S.hP]
  congr 1
  ring

/-! ## 2. Lifting an equality in global cohomology to the Selmer cone -/

/-- **The equality in global cohomology lifts to the Selmer cone** (tex 3917–3918: "because the
local degree-zero maps are onto and the degree-one maps inject"). Degree-one Selmer-cone cochains
are triples `(p, u, q)`: a global cochain `p`, a local-condition cochain `u` and a local cochain `q`
of degree zero; `(p, u, q)` is a cycle when `d p = 0`, `d u = 0` and `loc p − ι u = d q`
((H22), batch 3's `cone_cycle`). Degree-zero cone cochains are pairs `(g, w)` with
`d(g, w) = (d g, d w, loc g − ι w)`. If two cycles `(p, u, q)`, `(p', u', q')` have cohomologous
global parts, `p − p' = d g`, then their difference is the boundary of `(g, w)` for some `w`,
provided `H⁰(U_v) → H⁰(K_v)` is onto (`honto`) and `H¹(U_v) → H¹(K_v)` injective (`hinj`).
PROVED. -/
theorem selmerCone_lift {G0 G1 U0 U1 U2 L0 L1 : Type*} [AddCommGroup G0] [AddCommGroup G1]
    [AddCommGroup U0] [AddCommGroup U1] [AddCommGroup U2] [AddCommGroup L0] [AddCommGroup L1]
    (dG0 : G0 →+ G1) (dU0 : U0 →+ U1) (dU1 : U1 →+ U2) (dL0 : L0 →+ L1)
    (loc0 : G0 →+ L0) (loc1 : G1 →+ L1) (ι0 : U0 →+ L0) (ι1 : U1 →+ L1)
    (hloc : ∀ g, loc1 (dG0 g) = dL0 (loc0 g)) (hι : ∀ u, ι1 (dU0 u) = dL0 (ι0 u))
    (honto : ∀ c : L0, dL0 c = 0 → ∃ w : U0, dU0 w = 0 ∧ ι0 w = c)
    (hinj : ∀ u : U1, dU1 u = 0 → (∃ c : L0, ι1 u = dL0 c) → ∃ w : U0, dU0 w = u)
    {p p' : G1} {u u' : U1} {q q' : L0} (hu : dU1 u = 0) (hu' : dU1 u' = 0)
    (hpq : loc1 p - ι1 u = dL0 q) (hpq' : loc1 p' - ι1 u' = dL0 q')
    {g : G0} (hg : p - p' = dG0 g) :
    ∃ w : U0, dU0 w = u - u' ∧ loc0 g - ι0 w = q - q' := by
  -- `ι(u − u')` is the local coboundary of `loc g − (q − q')`
  have h1 : ι1 (u - u') = dL0 (loc0 g - (q - q')) := by
    have e1 : ι1 u = loc1 p - dL0 q := by rw [← hpq]; abel
    have e2 : ι1 u' = loc1 p' - dL0 q' := by rw [← hpq']; abel
    have e3 : loc1 p - loc1 p' = dL0 (loc0 g) := by rw [← map_sub, hg, hloc]
    rw [map_sub, e1, e2, map_sub, map_sub, ← e3]
    abel
  -- degree one injects: `u − u'` is a local-condition coboundary
  obtain ⟨w₀, hw₀⟩ := hinj (u - u') (by rw [map_sub, hu, hu', sub_zero]) ⟨_, h1⟩
  -- the remaining local degree-zero cocycle comes from the local condition
  have hc : dL0 (loc0 g - (q - q') - ι0 w₀) = 0 := by
    rw [map_sub, ← h1, ← hι, hw₀, sub_self]
  obtain ⟨w₁, hw₁, hw₁c⟩ := honto _ hc
  refine ⟨w₀ + w₁, by rw [map_add, hw₀, hw₁, add_zero], ?_⟩
  rw [map_add, hw₁c]
  abel

/-! ## 3. The finite-stage boundary (4.5) at the base -/

/-- **The retained boundary (4.5) at the base, at one finite stage** (tex 3912–3919). Let
`(z_G, z_U, z_L)` be the Selmer-cone cycle of the finite class `z_i(0)` (the class at the base
character and `t = 0`) and `(j_G, j_U, j_L)` that of the Kummer class `j_i(b₁)` of the specified
point `P = b₁`, `cls : G¹ → H¹` the class map of the global cochains (`hexact`: a cocycle with zero
class is a coboundary) and `δ : E(K) → H¹` the global Kummer map. Inputs: the class of `z_i(0)` is
the Kummer class of the `L`-multiplied weighted point (`hzcls`; Proposition
`ex:arith-finite-heegner` for `I = ∅`, tex 2867–2868, 3293–3295, lane RC10's `H11_empty`), the class
of `j_i(b₁)` is `δ(P)` (`hjcls`, definition), the split norm relation of the stage (in `S`), and the
two local facts of `selmerCone_lift`. Then `z_i(0) − L m_i j_i(b₁) = d v_i` in the Selmer cone with
`m_i = a_{r_i} − 2` and an explicit retained `v_i = (v, w)`. PROVED. -/
theorem boundary45_finite {G : Type} [AddCommGroup G] {P : G} (S : SplitNormStage P)
    {G0 G1 G2 U0 U1 U2 L0 L1 H1 : Type*} [AddCommGroup G0] [AddCommGroup G1] [AddCommGroup G2]
    [AddCommGroup U0] [AddCommGroup U1] [AddCommGroup U2] [AddCommGroup L0] [AddCommGroup L1]
    [AddCommGroup H1]
    (dG0 : G0 →+ G1) (dG1 : G1 →+ G2) (dU0 : U0 →+ U1) (dU1 : U1 →+ U2) (dL0 : L0 →+ L1)
    (loc0 : G0 →+ L0) (loc1 : G1 →+ L1) (ι0 : U0 →+ L0) (ι1 : U1 →+ L1)
    (hloc : ∀ g, loc1 (dG0 g) = dL0 (loc0 g)) (hι : ∀ u, ι1 (dU0 u) = dL0 (ι0 u))
    (honto : ∀ c : L0, dL0 c = 0 → ∃ w : U0, dU0 w = 0 ∧ ι0 w = c)
    (hinj : ∀ u : U1, dU1 u = 0 → (∃ c : L0, ι1 u = dL0 c) → ∃ w : U0, dU0 w = u)
    (cls : G1 →+ H1) (hexact : ∀ c : G1, dG1 c = 0 → cls c = 0 → ∃ g : G0, dG0 g = c)
    (δ : G →+ H1) (L : ℤ)
    {zG jG : G1} {zU jU : U1} {zL jL : L0}
    (hzG : dG1 zG = 0) (hjG : dG1 jG = 0) (hzU : dU1 zU = 0) (hjU : dU1 jU = 0)
    (hz : loc1 zG - ι1 zU = dL0 zL) (hj : loc1 jG - ι1 jU = dL0 jL)
    (hzcls : cls zG = δ (L • S.W)) (hjcls : cls jG = δ P) :
    ∃ (v : G0) (w : U0), zG - (L * (S.a - 2)) • jG = dG0 v ∧
      zU - (L * (S.a - 2)) • jU = dU0 w ∧ loc0 v - ι0 w = zL - (L * (S.a - 2)) • jL := by
  -- the global classes agree: `[z_i(0)] = δ(L W) = δ(L m P) = L m [j_i(P)]`
  have hcls : cls (zG - (L * (S.a - 2)) • jG) = 0 := by
    rw [map_sub, map_zsmul, hzcls, hjcls, S.weightedPoint_eq, smul_smul, map_zsmul, sub_self]
  obtain ⟨v, hv⟩ := hexact _ (by rw [map_sub, map_zsmul, hzG, hjG, smul_zero, sub_zero]) hcls
  -- the multiplied Kummer cycle is a cycle of the cone
  have hj' : loc1 ((L * (S.a - 2)) • jG) - ι1 ((L * (S.a - 2)) • jU) =
      dL0 ((L * (S.a - 2)) • jL) := by
    rw [map_zsmul, map_zsmul, map_zsmul, ← smul_sub, hj]
  have hjU' : dU1 ((L * (S.a - 2)) • jU) = 0 := by rw [map_zsmul, hjU, smul_zero]
  obtain ⟨w, hw1, hw2⟩ := selmerCone_lift dG0 dU0 dU1 dL0 loc0 loc1 ι0 ι1 hloc hι honto hinj
    hzU hjU' hz hj' hv.symm
  exact ⟨v, w, hv.symm, hw1.symm, hw2⟩

/-! ## 3a. The class at the base, from its construction, with the same fixed `L` -/

/-- **The class of the base is the Kummer class of the `L`-multiplied weighted point, with
`L = m₀ C_π C_bad 2^{2e}`** (Proposition `ex:arith-finite-heegner` for `I = ∅`: tex 2867–2868,
3030–3032, 3074–3081, 3232–3234, 3258–3262, 3293–3295). The class `b_∅ = m₀ C_bad d_a(δ_a(C_π y_r))`
over `H_r` (paragraphs 4–5 of the proof), pushed to `K` by the coefficient map `Tr` ((H20)–(H21)),
is `δ(L W)`, where `W` is the weighted point. Inputs: lane RC10's `InfResInput` (PRINT/GLUE (H8),
with (H2)), over a general five-term sequence `A → B → C → D` (`B = H¹(H_r, E[2^a])`,
`C = H¹(M_∅, E[2^a])^Γ`); the Kummer maps `κ : E(H_r) → B` over the base and `δa : E(H_r) → C`
over `M_∅`, related by restriction (`hκ`: for `I = ∅`, `M_∅ = H_r`, so the class over `M_∅` is the
restriction of the class over `H_r`); the trace `Wsum : E(H_r) → E(K)` (definition); `hTr`,
"Kummer of this sum equals the cohomological transfer" (tex 3258–3262; at the cocycle level batch
3's `HeegnerCohomology.kummer_weighted_sum`, PROVED there; here on classes, GLUE), stated for the
Kummer map `κ` over `H_r`, whose classes `Tr` pushes. PROVED from lane RC10's `H11_empty`.

Restated by Lane RC27: the earlier form took `InfResInput A B B D e` with `res = id` and one map
`δa : E(H_r) → B` (the form of RC10's earlier `H11_empty`, which the genuine five-term sequence
cannot satisfy). Non-vacuity: `classAtBase_nonvacuous` (file `NonVacuity.lean`). -/
theorem classAtBase_of_construction {G : Type} [AddCommGroup G] {P : G} (S : SplitNormStage P)
    {A B C D H1 : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup H1]
    (e : ℕ) (Inp : HeegnerAlgebra.InfResInput A B C D e) (κ : S.Pt →+ B) (δa : S.Pt →+ C)
    (hκ : ∀ x, Inp.seq.res (κ x) = δa x) (m0 Cπ Cbad : ℕ) (Tr : B →+ H1) (δ : G →+ H1)
    (Wsum : S.Pt →+ G) (hWsum : ∀ x, S.incl (Wsum x) = ∑ δ', S.act δ' x)
    (hTr : ∀ x, Tr (κ x) = δ (Wsum x)) :
    Tr (((m0 * Cbad : ℕ) : ℤ) • Inp.seq.descend e Inp.killD (δa ((Cπ : ℤ) • S.yr))) =
      δ (HeegnerAlgebra.Lmult m0 Cπ Cbad e • S.W) := by
  have hW : Wsum S.yr = S.W := S.hincl (by rw [hWsum, S.hW])
  rw [HeegnerAlgebra.H11_empty e Inp κ δa hκ m0 Cπ Cbad S.yr, hTr, map_zsmul, hW]

/-- **(4.5) at the base at one finite stage, from the construction of the class** (tex 3895–3919):
`boundary45_finite` with the class of `z_i(0)` given as the pushed constructed class (`hzcls`,
definition: `z_i(0)` represents it) and `L = m₀ C_π C_bad 2^{2e}`, the fixed multiplier of (H11)
("with the same fixed `L`", tex 3897). The construction inputs are those of
`classAtBase_of_construction` (restated by Lane RC27 over a general five-term sequence, with the
Kummer maps `κ` over `H_r` and `δa` over `M_∅` related by restriction, `hκ`); they are jointly
satisfiable (`classAtBase_nonvacuous`), and the Selmer-cone inputs are those of
`boundary45_finite`. PROVED. -/
theorem boundary45_finite_of_construction {G : Type} [AddCommGroup G] {P : G}
    (S : SplitNormStage P)
    {G0 G1 G2 U0 U1 U2 L0 L1 H1 A B C D : Type*} [AddCommGroup G0] [AddCommGroup G1]
    [AddCommGroup G2] [AddCommGroup U0] [AddCommGroup U1] [AddCommGroup U2] [AddCommGroup L0]
    [AddCommGroup L1] [AddCommGroup H1] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D]
    (dG0 : G0 →+ G1) (dG1 : G1 →+ G2) (dU0 : U0 →+ U1) (dU1 : U1 →+ U2) (dL0 : L0 →+ L1)
    (loc0 : G0 →+ L0) (loc1 : G1 →+ L1) (ι0 : U0 →+ L0) (ι1 : U1 →+ L1)
    (hloc : ∀ g, loc1 (dG0 g) = dL0 (loc0 g)) (hι : ∀ u, ι1 (dU0 u) = dL0 (ι0 u))
    (honto : ∀ c : L0, dL0 c = 0 → ∃ w : U0, dU0 w = 0 ∧ ι0 w = c)
    (hinj : ∀ u : U1, dU1 u = 0 → (∃ c : L0, ι1 u = dL0 c) → ∃ w : U0, dU0 w = u)
    (cls : G1 →+ H1) (hexact : ∀ c : G1, dG1 c = 0 → cls c = 0 → ∃ g : G0, dG0 g = c)
    (δ : G →+ H1) (e : ℕ) (Inp : HeegnerAlgebra.InfResInput A B C D e) (κ : S.Pt →+ B)
    (δa : S.Pt →+ C) (hκ : ∀ x, Inp.seq.res (κ x) = δa x) (m0 Cπ Cbad : ℕ) (Tr : B →+ H1)
    (Wsum : S.Pt →+ G) (hWsum : ∀ x, S.incl (Wsum x) = ∑ δ', S.act δ' x)
    (hTr : ∀ x, Tr (κ x) = δ (Wsum x))
    {zG jG : G1} {zU jU : U1} {zL jL : L0}
    (hzG : dG1 zG = 0) (hjG : dG1 jG = 0) (hzU : dU1 zU = 0) (hjU : dU1 jU = 0)
    (hz : loc1 zG - ι1 zU = dL0 zL) (hj : loc1 jG - ι1 jU = dL0 jL)
    (hzcls : cls zG =
      Tr (((m0 * Cbad : ℕ) : ℤ) • Inp.seq.descend e Inp.killD (δa ((Cπ : ℤ) • S.yr))))
    (hjcls : cls jG = δ P) :
    ∃ (v : G0) (w : U0),
      zG - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (S.a - 2)) • jG = dG0 v ∧
      zU - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (S.a - 2)) • jU = dU0 w ∧
      loc0 v - ι0 w = zL - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (S.a - 2)) • jL :=
  boundary45_finite S dG0 dG1 dU0 dU1 dL0 loc0 loc1 ι0 ι1 hloc hι honto hinj cls hexact δ
    (HeegnerAlgebra.Lmult m0 Cπ Cbad e) hzG hjG hzU hjU hz hj
    (hzcls.trans (classAtBase_of_construction S e Inp κ δa hκ m0 Cπ Cbad Tr δ Wsum hWsum hTr))
    hjcls

/-! ## 4. (4.5) at the base in the central model -/

/-- A limit of multiples of a fixed vector of `ℚ₂ⁿ` is a multiple of it (PROVED). -/
theorem exists_smul_of_tendsto {n : ℕ} {c : ℕ → ℚ_[2]} {v zbar : Fin n → ℚ_[2]}
    (h : Tendsto (fun i => c i • v) atTop (𝓝 zbar)) : ∃ μ : ℚ_[2], zbar = μ • v := by
  by_cases hv : v = 0
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    have h0 : Tendsto (fun i => c i • v) atTop (𝓝 0) := by
      simp only [hv, smul_zero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h h0
  · obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (funext hcon)
    have hcoord : ∀ k, Tendsto (fun i => c i * v k) atTop (𝓝 (zbar k)) := fun k =>
      ((continuous_apply k).tendsto zbar).comp h
    have hc : Tendsto c atTop (𝓝 (zbar j * (v j)⁻¹)) := by
      refine ((hcoord j).mul_const (v j)⁻¹).congr fun i => ?_
      rw [mul_assoc, mul_inv_cancel₀ hj, mul_one]
    exact ⟨zbar j * (v j)⁻¹, funext fun k => tendsto_nhds_unique (hcoord k) (hc.mul_const (v k))⟩

/-- **The inputs of (4.5) at the base, in the central two-term model** (tex 3895–3921, 3952–3968,
4345–4348). For the specified point `P` and the central specialization `z̄ ∈ ℚ₂ⁿ` of the actual
cycle (in the model's central degree-one coordinates), with kinds:

* `stage i`: the data of the `i`-th finite stage (`SplitNormStage`; PRINT (4.1), unweighted, so the
  print once `u_1 = [𝒪_K^× : ℤ^×]` is one, `D_K < -4`; + definitions);
* `L`, `hL`: the fixed multiplier of Proposition `ex:arith-finite-heegner` (`L > 0` there;
  definition);
* `kappa`: the central Kummer comparison `i ∘ κ_K : E(K) → ℚ₂ⁿ` (the rational Kummer map of
  `E(K)` followed by the comparison `i : K₀ → R₀` of tex 3952–3961, in the model's coordinates;
  additive: definition);
* `hlim`: the central specialization of the actual cycle is the limit of the comparisons of the
  central classes of the finite stages, `z̄ = lim_i L κ(W_i)` (ELLIOT, tex 3919–3921 "their
  adjugate identities multiplied by a fixed power of two survive the limit", with tex 3961–3968:
  the retained boundaries (4.5) `z_i(0) − L m_i j_i(b₁) = d v_i`, proved at each stage by
  `boundary45_finite`, survive the inner limit, and the comparison `i` identifies the specialized
  cycle `z₀`).
Since `stage` and `kappa` are existential, `Nonempty (Boundary45Base P n z̄)` is equivalent to
`∃ κ L, L ≠ 0 ∧ z̄ = L κ(P)`, and for torsion `P` to `z̄ = 0`. -/
structure Boundary45Base {G : Type} [AddCommGroup G] (P : G) (n : ℕ) (zbar : Fin n → ℚ_[2]) :
    Type 1 where
  /-- the finite stages -/
  stage : ℕ → SplitNormStage P
  /-- the fixed multiplier `L` -/
  L : ℤ
  /-- `L ≠ 0` -/
  hL : L ≠ 0
  /-- the central Kummer comparison -/
  kappa : G →+ (Fin n → ℚ_[2])
  /-- the retained boundaries survive the limit at the centre -/
  hlim : Tendsto (fun i => (L : ℚ_[2]) • kappa (stage i).W) atTop (𝓝 zbar)

variable {G : Type} [AddCommGroup G] {P : G} {n : ℕ} {zbar : Fin n → ℚ_[2]}

/-- The central comparisons of the stages are `L m_i κ(P)` (PROVED, from
`SplitNormStage.weightedPoint_eq`). -/
theorem Boundary45Base.stage_eq (B : Boundary45Base P n zbar) (i : ℕ) :
    (B.L : ℚ_[2]) • B.kappa (B.stage i).W =
      (((B.L * ((B.stage i).a - 2) : ℤ)) : ℚ_[2]) • B.kappa P := by
  rw [(B.stage i).weightedPoint_eq, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ_[2], smul_smul,
    Int.cast_mul]

/-- **`z₀ = i(L m P)`** (tex 3968: "The boundary (4.5) gives `z_0 = i(LmP)`"), at the base: the
central specialization of the actual cycle is `L μ κ(P)` for one `μ ∈ ℚ₂`. PROVED. -/
theorem Boundary45Base.central (B : Boundary45Base P n zbar) :
    ∃ μ : ℚ_[2], zbar = (B.L : ℚ_[2]) • (μ • B.kappa P) := by
  have hseq : Tendsto (fun i => (((B.L * ((B.stage i).a - 2) : ℤ)) : ℚ_[2]) • B.kappa P) atTop
      (𝓝 zbar) := B.hlim.congr fun i => B.stage_eq i
  obtain ⟨ν, hν⟩ := exists_smul_of_tendsto hseq
  refine ⟨ν / B.L, ?_⟩
  rw [smul_smul, mul_div_cancel₀ _ (Int.cast_ne_zero.mpr B.hL)]
  exact hν

/-- **The moving multipliers converge** when `κ(P) ≠ 0` (PROVED): the `μ` of
`Boundary45Base.central` is then the 2-adic limit of `m_i = a_{r_i} − 2`. -/
theorem Boundary45Base.tendsto_multiplier (B : Boundary45Base P n zbar) {μ : ℚ_[2]}
    (hμ : zbar = (B.L : ℚ_[2]) • (μ • B.kappa P)) (hP : B.kappa P ≠ 0) :
    Tendsto (fun i => (((B.stage i).a - 2 : ℤ) : ℚ_[2])) atTop (𝓝 μ) := by
  obtain ⟨j, hj⟩ : ∃ j, B.kappa P j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP (funext hcon)
  have hL : (B.L : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr B.hL
  have hcoord : Tendsto (fun i => (((B.L * ((B.stage i).a - 2) : ℤ)) : ℚ_[2]) * B.kappa P j)
      atTop (𝓝 (zbar j)) :=
    ((continuous_apply j).tendsto zbar).comp (B.hlim.congr fun i => B.stage_eq i)
  have hzj : zbar j = (B.L : ℚ_[2]) * B.kappa P j * μ := by
    have h := congrFun hμ j
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    ring
  have hne : (B.L : ℚ_[2]) * B.kappa P j ≠ 0 := mul_ne_zero hL hj
  have h2 := hcoord.mul_const ((B.L : ℚ_[2]) * B.kappa P j)⁻¹
  have hval : (B.L : ℚ_[2]) * B.kappa P j * μ * ((B.L : ℚ_[2]) * B.kappa P j)⁻¹ = μ := by
    rw [mul_comm _ μ, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [hzj, hval] at h2
  refine h2.congr fun i => ?_
  rw [Int.cast_mul]
  calc (B.L : ℚ_[2]) * (((B.stage i).a - 2 : ℤ) : ℚ_[2]) * B.kappa P j *
        ((B.L : ℚ_[2]) * B.kappa P j)⁻¹ =
      (((B.stage i).a - 2 : ℤ) : ℚ_[2]) *
        ((B.L : ℚ_[2]) * B.kappa P j * ((B.L : ℚ_[2]) * B.kappa P j)⁻¹) := by ring
    _ = (((B.stage i).a - 2 : ℤ) : ℚ_[2]) := by rw [mul_inv_cancel₀ hne, mul_one]

/-- **The field `h45` of the base model** (tex 3968, 4345–4348): there is an additive map
`κ' : E(K) → ℚ₂ⁿ` (the central Kummer comparison scaled by the limit multiplier `μ`) with
`z̄ = L κ'(P)`. PROVED. -/
theorem Boundary45Base.h45 (B : Boundary45Base P n zbar) :
    ∃ kappa' : G →+ (Fin n → ℚ_[2]), zbar = (B.L : ℚ_[2]) • kappa' P := by
  obtain ⟨μ, hμ⟩ := B.central
  exact ⟨(DistribSMul.toAddMonoidHom (Fin n → ℚ_[2]) μ).comp B.kappa, by simpa using hμ⟩

/-- **The use of (4.5) in the base-zero lemma** (tex 4345–4348): if the specified point is torsion
(the conductor-one height formula when `L'(E/K,1) = 0`), its rational Kummer class vanishes and the
specialization of the actual cycle is zero. PROVED (lane RC15's
`kummer_eq_zero_of_isOfFinAddOrder`). -/
theorem Boundary45Base.central_eq_zero_of_torsion (B : Boundary45Base P n zbar)
    (hP : IsOfFinAddOrder P) : zbar = 0 := by
  obtain ⟨μ, hμ⟩ := B.central
  rw [hμ, Central.kummer_eq_zero_of_isOfFinAddOrder B.kappa hP, smul_zero, smul_zero]

end ZInQ.Manuscript.RC.BaseZeroAssembly
