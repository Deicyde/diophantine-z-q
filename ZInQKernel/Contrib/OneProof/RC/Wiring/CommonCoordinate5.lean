import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5Universal

/-!
# Theorem 5.3, Lane RC32: the common coordinate (4.7) over the text's objects

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex 4142–4328), restated over the text's
own objects, on Elliot's main path. It replaces
`CommonCoordinateInputsG` (`CommonCoordinate4.lean`), whose coefficient ring was an existential
ring `R` with `χ : R →+* ℚ₂[[t]]`: the text's ring `𝒪[G]` has no such `t`-preserving evaluation
(`t` is a unit of `𝒪`), and `e_q⁻¹`, `v_q`, `η_x` evaluated at a character may have a pole at
`t = 0` (tex 4153–4155, 4229–4231, 4318–4320), so they cannot be evaluated in `ℚ₂[[t]]`.

Here (objects in `CommonCoordinate5Objects.lean`, universal ones in
`CommonCoordinate5Universal.lean`):

* **no free ring and no free evaluation**: `g_q`, the Frobenius lift, `z`, `e_q`, `l_q`, `v_q` and
  `η_x` are definitions from the family, the address and the curve's `a_q`, evaluated in
  `F = Frac Λ` (tex 4341–4342), where `e_q(x)⁻¹` exists (`eF_ne_zero`);
* **regularity only where the text specializes**: the primitive coordinate has a `t`-expansion
  (it is regular at `t = 0`, `hprim`), and the corrected coordinate `ũ_x = η_x u_{rel,x}` — the
  product — is the one identified with the interface's power series (`htilde`); `η_x` alone and the
  relaxed coordinates are only elements of `F` (`η_x` can have a pole: `CommonCoordinate5Bridge`);
* **the step models are existential**: at each unused prime the relaxation is batch 3's
  `NaturalStep` over `F`, whose two-place block is built from the actual `z`, `a_q`, `q` and a
  Frobenius matrix over `ℤ₂` of trace `a_q` and determinant `q`; its triangular model, norm
  identity, functionals (batch 3's abstract retention data) and basis comparisons are
  existential and are met by `naturalStepF_of` for any coordinates with `δ u' = c e² u`, so the
  field asserts exactly (4.7) at the step (ELLIOT; tex 4157–4194).

PROVED (standard axioms): `CommonCoordinateTrianglesL.corrected_eq`
(`η_x u_{rel,x} = ε_x u_{prim,x}` in `F`, `ε_x ∈ Λ^×`) and
`commonCoordinateTarget_of_L : CommonCoordinateInputsL D → CommonCoordinateTarget D`, the exact
target the wiring consumes (`RCSteps.common_coordinate`).

## The leaf, field by field

Each field: text object; tex lines; kind.

* `Fr`, `hFtr`, `hFdet`: `Fr_q` on `T₂E` at a graph prime: trace `a_q` (Mathlib's coefficient),
  determinant `q`; tex 4209–4213; GLUE (Frobenius on the Tate module at a good prime; not pinned
  to `T₂E`, which is not in the tree).
* `u`: the class-functional coordinates in `F` relaxed at `T ⊆ U_x` (`U_x` the unused primes);
  tex 3877–3892, 4159–4188; existential (any coordinates; not tied to the actual complexes).
* `hprim`: `u_{prim,x} = u ∅` is regular at `t = 0`, with `t`-expansion `D.uPrim`; tex 4153,
  4334–4336, 5004–5008; definition + ELLIOT (regularity), as `RCData.uPrim`.
* `eps`: the step units of each relaxation `T → T ∪ {p}`; tex 4157–4194; existential.
* `hstep`: each relaxation `T → T ∪ {p}`: the support triangle (`NaturalStep` over `F`);
  tex 4157–4194; ELLIOT ((4.7) at one prime; `λ_R ∘ i = e_q λ_P` is PROVED only for abstract
  retention data).
* `htilde`: `ũ_x = η_x u_{rel,x}`, `η_x = etaF` the evaluated universal correction, has
  `t`-expansion `D.uTilde`; tex 4150–4151, 4224–4231; definition (the interface identification).

DEPARTURES (flagged):
* the multi-prime relaxation is done one unused prime at a time, at every intermediate `T ⊆ U_x`
  (tex 4325–4327 "Multiplying the correction factors over the finite set `Q`" leaves the order
  implicit; ELLIOT gap filled as in lane RC15's `prod_relax`), with a step unit for each `(T, p)`;
* `hprim` asks regularity of `u_{prim,x}` at every address of every final family, the scope of
  `RCData.uPrim` (the text proves it at `x ≠ 0` and at `x = 0` under full Selmer corank one,
  tex 4922–4923, 5196–5199, 4350–4351);
* `Fr` is a matrix over `ℤ₂` with the right trace and determinant, not the Frobenius of the Tate
  module (only `tr` and `det` enter `l_q`; the steps' models are existential);
* as for every post leaf, the field is also requested in Branch 1 (`RC/Skeleton/Steps.lean`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-! ## `Λ`-units in `F` and `t`-expansions -/

theorem lamUnitF_one : LamUnitF 1 := ⟨1, by simp⟩

theorem LamUnitF.mul {a b : FracLam} (ha : LamUnitF a) (hb : LamUnitF b) : LamUnitF (a * b) := by
  obtain ⟨e, rfl⟩ := ha
  obtain ⟨f, rfl⟩ := hb
  exact ⟨e * f, by rw [Units.val_mul, map_mul]⟩

theorem LamUnitF.pow {a : FracLam} (ha : LamUnitF a) (n : ℕ) : LamUnitF (a ^ n) := by
  induction n with
  | zero => simpa using lamUnitF_one
  | succ n ih => rw [pow_succ]; exact ih.mul ha

theorem LamUnitF.ring_inverse {a : FracLam} (ha : LamUnitF a) : LamUnitF (Ring.inverse a) := by
  obtain ⟨e, rfl⟩ := ha
  refine ⟨e⁻¹, ?_⟩
  have h : lamToF (e : Lambda) = ((Units.map lamToF.toMonoidHom e : FracLamˣ) : FracLam) := rfl
  rw [h, Ring.inverse_unit]
  rfl

/-- A nonzero natural number is nonzero in `F` (PROVED). -/
theorem natCast_ne_zero_F {n : ℕ} (hn : n ≠ 0) : (n : FracLam) ≠ 0 := by
  rw [← map_natCast lamToF]
  refine (map_ne_zero_iff _ (IsFractionRing.injective Lambda FracLam)).mpr fun h => hn ?_
  have := congrArg (PowerSeries.constantCoeff (R := ℤ_[2])) h
  simp only [map_natCast, map_zero] at this
  exact_mod_cast this

/-- `q` is a unit of `ℤ₂` for odd `q` (PROVED). -/
theorem isUnit_natCast_zTwo {q : ℕ} (hq : Odd q) : IsUnit (q : ℤ_[2]) :=
  PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr (Nat.coprime_two_left.mpr hq))

/-- `q⁻¹ ∈ ℤ₂` maps to `q⁻¹ ∈ F` (PROVED). -/
theorem zTwoToF_qInv {q : ℕ} (hq : Odd q) : zTwoToF (qInv q) = (q : FracLam)⁻¹ := by
  have hu := isUnit_natCast_zTwo hq
  have h1 : zTwoToF (q : ℤ_[2]) * zTwoToF (qInv q) = 1 := by
    rw [← map_mul, qInv, Ring.mul_inverse_cancel _ hu, map_one]
  rw [map_natCast] at h1
  exact (eq_inv_of_mul_eq_one_right h1)

/-- `q⁻¹` is a `Λ`-unit for odd `q` (tex 4193: "`q^{-4}` is one also"; PROVED). -/
theorem lamUnitF_qInv {q : ℕ} (hq : Odd q) : LamUnitF ((q : FracLam)⁻¹) := by
  obtain ⟨w, hw⟩ := isUnit_natCast_zTwo hq
  refine ⟨Units.map (PowerSeries.C : ℤ_[2] →+* Lambda).toMonoidHom w⁻¹, ?_⟩
  have h1 : zTwoToF (w : ℤ_[2]) * zTwoToF ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hw, map_natCast] at h1
  rw [← eq_inv_of_mul_eq_one_right h1]
  rfl

/-- `t`-expansions are multiplicative (PROVED). -/
theorem IsTExpansion.mul {u u' : FracLam} {U U' : PowerSeries ℚ_[2]} (h : IsTExpansion u U)
    (h' : IsTExpansion u' U') : IsTExpansion (u * u') (U * U') := by
  obtain ⟨a, b, hb, hu, hU⟩ := h
  obtain ⟨a', b', hb', hu', hU'⟩ := h'
  refine ⟨a * a', b * b', mul_ne_zero hb hb', ?_, ?_⟩
  · rw [map_mul, map_mul, ← hu, ← hu']; ring
  · rw [map_mul, map_mul, ← hU, ← hU']; ring

/-! ## The leaf -/

/-- **The data of Lemma `ex:arith-common-coordinate` at one address `x` of the family `Fam`**
(tex 4142–4328), over the text's objects; see the module docstring for the field table. Write
`U = unusedAt Fam x` for the unused primes, `z = zAt Fam x p` for the scalar Frobenius value and
`η_x = etaF ℓ Fam x`. -/
structure CommonCoordinateTrianglesL {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) :
    Type where
  /-- the Frobenius at each graph prime, a `2 × 2` matrix over `ℤ₂` (GLUE: the Frobenius at a good
  prime on `T₂E`; tex 4209–4213) -/
  Fr : ℕ → Matrix (Fin 2) (Fin 2) ℤ_[2]
  /-- `tr Fr_q = a_q`, Mathlib's coefficient of `L(E, s)` (GLUE; tex 4213) -/
  hFtr : ∀ q ∈ Fam.Q, (Fr q).trace = (apE ℓ q : ℤ_[2])
  /-- `det Fr_q = q` (GLUE; tex 4213) -/
  hFdet : ∀ q ∈ Fam.Q, (Fr q).det = (q : ℤ_[2])
  /-- the class-functional coordinates in `F` relaxed at `T ⊆ U` (existential: any coordinates;
  the text's are those of `[z] ⊗ [λ]`; tex 3877–3892, 4159–4188) -/
  u : Finset ℕ → FracLam
  /-- the primitive coordinate `u_{prim,x} = u ∅` is regular at `t = 0`, with `t`-expansion the
  interface's `u_{prim,x}` (definition + ELLIOT regularity; DEPARTURE of scope as `RCData.uPrim`;
  tex 4153, 4334–4336, 5004–5008) -/
  hprim : IsTExpansion (u ∅) (D.uPrim Fam x)
  /-- the step units `ε` of (4.7) (existential, determined by the step's basis comparisons;
  tex 4187–4193) -/
  eps : Finset ℕ → ℕ → FracLam
  /-- each relaxation `T → T ∪ {p}` at an unused prime is the support triangle in the original
  integral bases (batch 3's `NaturalStep` over `F`, an existential triangular model met by
  `naturalStepF_of` for any `u, u'` with `δ u' = c e² u`: (4.7) at the step, ELLIOT; DEPARTURE:
  one prime at a time at every `T ⊆ U`; tex 4157–4194, 4325–4327) -/
  hstep : ∀ T ⊆ unusedAt Fam x, ∀ p ∈ unusedAt Fam x, p ∉ T →
    NaturalStep ((Fr p).map zTwoToF) (p : FracLam) (p : FracLam)⁻¹ (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) (u T) (u (insert p T))
      (eps T p) LamUnitF LamUnitF
  /-- the corrected coordinate `ũ_x = η_x u_{rel,x}` (the product, not `η_x`) is regular, with
  `t`-expansion the interface's `ũ_x` (definition: the interface identification; tex 4150–4151,
  4224–4231) -/
  htilde : IsTExpansion (etaF ℓ Fam x * u (unusedAt Fam x)) (D.uTilde Fam x)

namespace CommonCoordinateTrianglesL

variable {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}

/-- The relaxed coordinate `u_{rel,x}` (relaxed at every unused prime of `x`). -/
def urel (M : CommonCoordinateTrianglesL D Fam x) : FracLam := M.u (unusedAt Fam x)

/-- The corrected coordinate `ũ_x = η_x u_{rel,x} ∈ F` (tex 4224). -/
def utilde (M : CommonCoordinateTrianglesL D Fam x) : FracLam := etaF ℓ Fam x * M.urel

end CommonCoordinateTrianglesL

/-- **The inputs of (4.7) over the text's objects** (tex 4142–4328): at every address of every
final family, one `CommonCoordinateTrianglesL`. -/
def CommonCoordinateInputsL {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    Nonempty (CommonCoordinateTrianglesL D F x)

/-! ## (4.7) at one unused prime -/

/-- `l_q(x)` in `F` through the Frobenius trace and determinant (PROVED). -/
theorem lF_eq_quotPoly {ℓ : ℕ} {Fam : Family} {x : Addr Fam.b} {p : ℕ} (hp : Odd p) :
    lF ℓ Fam x p = quotPoly (apE ℓ p : FracLam) (p : FracLam) (p : FracLam)⁻¹
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) := by
  rw [lF, quotFac, map_quotPoly, map_intCast, map_natCast]
  congr 1
  exact zTwoToF_qInv hp

/-- `e_q(x)` in `F` is the point factor of the evaluated data (PROVED). -/
theorem eF_eq_pointFactor {ℓ : ℕ} {Fam : Family} {x : Addr Fam.b} {p : ℕ} :
    eF ℓ Fam x p = pointFactor (apE ℓ p : FracLam) (lamToF (zAt Fam x p : Lambda))
      (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) := by
  simp only [eF, ptFac, pointFactor, map_sub, map_intCast]

/-- The trace and determinant of `Fr` survive the map to `F` (PROVED). -/
theorem trace_det_map_zTwoToF {Fr : Matrix (Fin 2) (Fin 2) ℤ_[2]} {a : ℤ} {p : ℕ}
    (htr : Fr.trace = (a : ℤ_[2])) (hdet : Fr.det = (p : ℤ_[2])) :
    (Fr.map zTwoToF).trace = (a : FracLam) ∧ (Fr.map zTwoToF).det = (p : FracLam) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.trace_fin_two, Matrix.map_apply, Matrix.map_apply, ← map_add, ← Matrix.trace_fin_two,
      htr, map_intCast]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_natCast]

/-- **(4.7) at one unused prime, in `F`** (tex 4157–4194): the support triangle of a relaxation
step gives `l_p(x) u' = e_p(x)² ε u` with `ε ∈ Λ^×` (batch 3's `ActualStep.eq47`, the functional
relation from `SelmerFunctionals.restrict`). PROVED. -/
theorem step47_of_naturalStep {ℓ : ℕ} {Fam : Family} {x : Addr Fam.b} {p : ℕ} (hp : Odd p)
    {Fr : Matrix (Fin 2) (Fin 2) ℤ_[2]} (htr : Fr.trace = (apE ℓ p : ℤ_[2]))
    (hdet : Fr.det = (p : ℤ_[2])) {u u' ε : FracLam}
    (h : NaturalStep (Fr.map zTwoToF) (p : FracLam) (p : FracLam)⁻¹ (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) u u' ε
      LamUnitF LamUnitF) :
    lF ℓ Fam x p * u' = eF ℓ Fam x p ^ 2 * ε * u ∧ LamUnitF ε := by
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hp.pos.ne'
  have hq : (p : FracLam) * (p : FracLam)⁻¹ = 1 := mul_inv_cancel₀ hp0
  obtain ⟨ha, hd⟩ := trace_det_map_zTwoToF htr hdet
  refine ⟨?_, ?_⟩
  · have h47 := ActualStep.eq47 hq ha hd h.toActualStep
    rw [quotientFactor_eq_quotPoly _ _ _ ha hd] at h47
    rw [lF_eq_quotPoly hp, eF_eq_pointFactor]
    exact h47
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hcR, hcP, hε⟩ := h
    rw [hε]
    exact ((lamUnitF_qInv hp).pow 4 |>.mul hcR).mul hcP.ring_inverse

/-- **Relaxing the unused primes one at a time** (ELLIOT gap filled, tex 4185–4188, 4325–4327): if
every step `T → T ∪ {p}` inside `U` satisfies (4.7) with a `Λ`-unit, then for every `T ⊆ U`,
`(∏_{p ∈ T} l_p) u_T = (∏_{p ∈ T} e_p²) E_T u_∅` with `E_T ∈ Λ^×`. PROVED. -/
theorem relax_chain (U : Finset ℕ) (l e : ℕ → FracLam) (u : Finset ℕ → FracLam)
    (eps : Finset ℕ → ℕ → FracLam)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      l p * u (insert p T) = e p ^ 2 * eps T p * u T ∧ LamUnitF (eps T p)) :
    ∀ T ⊆ U, ∃ E : FracLam, LamUnitF E ∧
      (∏ p ∈ T, l p) * u T = (∏ p ∈ T, e p ^ 2) * E * u ∅ := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; exact ⟨1, lamUnitF_one, by simp⟩
  | insert a T haT ih =>
    intro hT
    have hTU : T ⊆ U := (Finset.subset_insert a T).trans hT
    have haU : a ∈ U := hT (Finset.mem_insert_self a T)
    obtain ⟨E, hE, hET⟩ := ih hTU
    obtain ⟨h47, hunit⟩ := hstep T hTU a haU haT
    refine ⟨eps T a * E, hunit.mul hE, ?_⟩
    rw [Finset.prod_insert haT, Finset.prod_insert haT]
    calc l a * (∏ p ∈ T, l p) * u (insert a T)
        = (∏ p ∈ T, l p) * (l a * u (insert a T)) := by ring
      _ = (∏ p ∈ T, l p) * (e a ^ 2 * eps T a * u T) := by rw [h47]
      _ = e a ^ 2 * eps T a * ((∏ p ∈ T, l p) * u T) := by ring
      _ = e a ^ 2 * eps T a * ((∏ p ∈ T, e p ^ 2) * E * u ∅) := by rw [hET]
      _ = e a ^ 2 * (∏ p ∈ T, e p ^ 2) * (eps T a * E) * u ∅ := by ring

namespace CommonCoordinateTrianglesL

variable {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}

/-- **`ũ_x = ε_x u_{prim,x}` in `F` with `ε_x ∈ Λ^×`** (tex 4151, 4224–4227: "Formula (4.7) makes
`ũ_x = ε_x u_{prim,x}`"): the correction's poles are cancelled by the relaxed coordinate, inside
`F`. PROVED. -/
theorem corrected_eq (M : CommonCoordinateTrianglesL D Fam x) (hodd : ∀ q ∈ Fam.Q, Odd q) :
    ∃ E : FracLam, LamUnitF E ∧ M.utilde = E * M.u ∅ := by
  have hUQ : ∀ p ∈ unusedAt Fam x, p ∈ Fam.Q := fun p hp => (mem_unusedAt.mp hp).1
  obtain ⟨E, hE, hrel⟩ := relax_chain (unusedAt Fam x) (lF ℓ Fam x) (eF ℓ Fam x) M.u M.eps
    (fun T hT p hp hpT => step47_of_naturalStep (hodd p (hUQ p hp)) (M.hFtr p (hUQ p hp))
      (M.hFdet p (hUQ p hp)) (M.hstep T hT p hp hpT)) (unusedAt Fam x) subset_rfl
  refine ⟨E, hE, ?_⟩
  have hne : (∏ p ∈ unusedAt Fam x, eF ℓ Fam x p ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero 2 (eF_ne_zero ℓ Fam x p)
  rw [utilde, urel, etaF_eq, Finset.prod_div_distrib, div_mul_eq_mul_div, div_eq_iff hne, hrel]
  ring

/-- **(4.7) for the interface's power series** (PROVED): `D.uTilde Fam x = ε D.uPrim Fam x` with
`ε ∈ Λ^×`, from `corrected_eq`, the two `t`-expansions and their uniqueness. -/
theorem eq47 (M : CommonCoordinateTrianglesL D Fam x) (hodd : ∀ q ∈ Fam.Q, Odd q) :
    ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde Fam x = ε * D.uPrim Fam x := by
  obtain ⟨E, ⟨e, rfl⟩, hE⟩ := M.corrected_eq hodd
  refine ⟨lamIncl (e : Lambda), ⟨e, rfl⟩, ?_⟩
  have h1 : IsTExpansion (lamToF (e : Lambda) * M.u ∅) (lamIncl (e : Lambda) * D.uPrim Fam x) :=
    (isTExpansion_algebraMap (e : Lambda)).mul M.hprim
  have h2 : IsTExpansion (lamToF (e : Lambda) * M.u ∅) (D.uTilde Fam x) := by
    rw [← hE]; exact M.htilde
  exact h2.unique_right h1

end CommonCoordinateTrianglesL

namespace CommonCoordinateTrianglesL

variable {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}

/-- **The corrected coordinate is the universal `η` times the relaxed coordinate, at `x`**
(tex 4224, "Put `ũ = η u_rel`"): in `Frac 𝒪`, `ι(ũ_x) = x(η) · ι(u_{rel,x})`, with `η ∈ 𝒪[G]` the
universal correction (`etaU`, lift choice `0`) and `ι : Frac Λ → Frac 𝒪`. PROVED. -/
theorem iotaO_utilde (M : CommonCoordinateTrianglesL D Fam x) (hodd : ∀ q ∈ Fam.Q, Odd q) :
    Rings.iotaO M.utilde = algebraMap Determinant.OO (FractionRing Determinant.OO)
      (Determinant.signEval (Determinant.sgnChar x) (etaU ℓ Fam fun _ => 0)) *
        Rings.iotaO M.urel := by
  rw [utilde, map_mul, eval_etaU ℓ Fam hodd x]

end CommonCoordinateTrianglesL

/-- **`RCSteps.common_coordinate` from the leaf over the text's objects** ((4.7), tex 4142–4328;
PROVED): the target the wiring consumes. -/
theorem commonCoordinateTarget_of_L {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsL D) :
    CommonCoordinateTarget D := fun Co Ce F hF x => by
  obtain ⟨M⟩ := h Co Ce F hF x
  exact M.eq47 (odd_of_finalFamilyAt hF)

end ZInQ.Manuscript.RC.Wiring
