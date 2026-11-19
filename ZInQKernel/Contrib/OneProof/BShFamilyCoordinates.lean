import ZInQKernel.Contrib.OneProof.BShFamilyLocalKernels

/-! ON THE SPOT (provenance (c)): apply the same short Vélu computation
to the analytic atlas and to the algebraic marked quotient. -/

noncomputable section

namespace BShFamily

open BShTraces UpperHalfPlane PeriodPair T5Glue Filter X1Igusa.Weber
open scoped Topology MatrixGroups BigOperators

/-- The expression for the marked quotient, with a fixed finite enumeration
of the nonzero kernel elements. -/
def familyPair {F ι : Type*} [Field F] [Fintype ι] (a b x : F) (t : ι → F) : F × F :=
  shortCoordinates (a - 5 * ∑ i, shortT a (t i))
    (b - 7 * ∑ i, shortW a b (t i))
    (x + ∑ i, shortShift a b x (t i))

theorem veluPair_eq_familyPair {F ι : Type*} [Field F] [Fintype ι]
    (a b x : F) (t : ι → F) :
    veluPair a b x ((Finset.univ : Finset ι).val.map t) = familyPair a b x t := by
  simp only [veluPair, familyPair, Multiset.map_map, Function.comp_def, Finset.sum]

theorem familyPair_scale {F ι : Type*} [Field F] [Fintype ι]
    (a b x u : F) (t : ι → F) (hu : u ≠ 0) :
    familyPair (u ^ 2 * a) (u ^ 3 * b) (u * x) (fun i => u * t i) =
      familyPair a b x t := by
  have T (i : ι) := (short_weights_scale a b x (t i) u hu).1
  have W (i : ι) := (short_weights_scale a b x (t i) u hu).2.1
  have S (i : ι) := (short_weights_scale a b x (t i) u hu).2.2
  simp only [familyPair, T, W, S, ← Finset.mul_sum]
  rw [show u ^ 2 * a - 5 * (u ^ 2 * ∑ i, shortT a (t i)) =
    u ^ 2 * (a - 5 * ∑ i, shortT a (t i)) by ring,
    show u ^ 3 * b - 7 * (u ^ 3 * ∑ i, shortW a b (t i)) =
    u ^ 3 * (b - 7 * ∑ i, shortW a b (t i)) by ring, ← mul_add,
    short_coordinates_scale _ _ _ _ hu]

/-- The pointwise values of the algebraic quotient expression agree with the
short Vélu expression attached to the corresponding prime superlattice. -/
theorem normalized_familyPair_eq_lattice {p : ℕ} (hp : p.Prime) (i : Line p)
    (τ : ℍ) (N : ℕ) (h₂ : (pp τ).g₂ ≠ 0) (h₃ : (pp τ).g₃ ≠ 0) :
    let G := (pp τ).g₂ ^ 3 / (pp τ).g₃ ^ 2
    familyPair (-(G / 4)) (-(G / 4)) (normX τ (1 / (N : ℂ)))
      (fun k : Multiple p => normX τ ((k.val.val : ℂ) * generator p i τ)) =
      markedLatticeCoordinates (cosets hp.pos i τ) ⟨0, hp.pos⟩ (1 / (N : ℂ)) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : DecidableEq (Fin p) := Classical.decEq _
  let a := (pp τ).weierstrassCurve.a₄
  let b := (pp τ).weierstrassCurve.a₆
  let x := (pp τ).weierstrassP (1 / (N : ℂ))
  let D := cosets hp.pos i τ
  let t (k : Multiple p) := (pp τ).weierstrassP (D.representative k.val)
  let u := (pp τ).g₂ / (pp τ).g₃
  let G := (pp τ).g₂ ^ 3 / (pp τ).g₃ ^ 2
  have ha : u ^ 2 * a = -(G / 4) := by
    dsimp [u, a, G]
    ring
  have hb : u ^ 3 * b = -(G / 4) := by
    dsimp [u, b, G]
    field_simp
    <;> ring
  have ht (k : Multiple p) :
      u * t k = normX τ ((k.val.val : ℂ) * generator p i τ) := by
    change u * (pp τ).weierstrassP ((cosets hp.pos i τ).representative k.val) = _
    rw [representative_eq, neg_mul, weierstrassP_neg]
    rfl
  have he := familyPair_scale a b x u t (div_ne_zero h₂ h₃)
  simp only [ha, hb, ht] at he
  refine he.trans ?_
  have hs (f : Fin p → ℂ) :
      (∑ k : Multiple p, f k.val) = ∑ k ∈ Finset.univ.erase ⟨0, hp.pos⟩, f k := by
    symm
    exact Finset.sum_subtype _ (fun k => by simp [Fin.val_eq_zero_iff]) _
  simp only [familyPair, markedLatticeCoordinates, t]
  rw [hs (fun k => shortT a ((pp τ).weierstrassP (D.representative k))),
    hs (fun k => shortW a b ((pp τ).weierstrassP (D.representative k))),
    hs (fun k => shortShift a b x ((pp τ).weierstrassP (D.representative k)))]

/-- Rational operations and the three sums on the analytic multiset realize
the corresponding pointwise Vélu calculations in the germ. -/
theorem restrict_analytic_pair {p : ℕ} (hp : p.Prime) (τ : ℍ) (i : Line p)
    {a b x : MeromorphicGerm (τ : ℂ)} {A B C : ℍ → ℂ}
    (ha : restrict τ a = (A : Filter.Germ (𝓝[≠] τ) ℂ))
    (hb : restrict τ b = (B : Filter.Germ (𝓝[≠] τ) ℂ))
    (hx : restrict τ x = (C : Filter.Germ (𝓝[≠] τ) ℂ)) :
    let V := veluPair a b x (analyticCluster hp τ i)
    let f (s : ℍ) := familyPair (A s) (B s) (C s)
      (fun k : Multiple p => normX s ((k.val.val : ℂ) * generator p i s))
    restrict τ V.1 = ((fun s => (f s).1) : Filter.Germ (𝓝[≠] τ) ℂ) ∧
    restrict τ V.2 = ((fun s => (f s).2) : Filter.Germ (𝓝[≠] τ) ℂ) := by
  let T (k : Multiple p) (s : ℍ) := normX s ((k.val.val : ℂ) * generator p i s)
  have hs {f : Multiple p → MeromorphicGerm (τ : ℂ)} {g : Multiple p → ℍ → ℂ}
      (h : ∀ i, restrict τ (f i) = (g i : Filter.Germ (𝓝[≠] τ) ℂ)) :
      restrict τ (∑ i, f i) = ((fun s : ℍ => ∑ i, g i s) : Filter.Germ (𝓝[≠] τ) ℂ) := by
    rw [map_sum]
    simp_rw [h]
    change (∑ i, Germ.coeRingHom (𝓝[≠] τ) (g i)) = _
    rw [← map_sum]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun s => Finset.sum_apply _ _ _
  have hT : restrict τ (∑ k : Multiple p, shortT a (sectionAt hp τ i k)) =
      ((fun s : ℍ => ∑ k : Multiple p, shortT (A s) (T k s)) : Filter.Germ (𝓝[≠] τ) ℂ) := by
    apply hs
    intro k
    simp only [shortT, map_add, map_mul, map_pow, map_ofNat, ha, restrict_sectionAt]
    rfl
  have hW : restrict τ (∑ k : Multiple p, shortW a b (sectionAt hp τ i k)) =
      ((fun s : ℍ => ∑ k : Multiple p, shortW (A s) (B s) (T k s)) :
        Filter.Germ (𝓝[≠] τ) ℂ) := by
    apply hs
    intro k
    simp only [shortW, map_add, map_mul, map_pow, map_ofNat, ha, hb, restrict_sectionAt]
    rfl
  have hS : restrict τ (∑ k : Multiple p, shortShift a b x (sectionAt hp τ i k)) =
      ((fun s : ℍ => ∑ k : Multiple p, shortShift (A s) (B s) (C s) (T k s)) :
        Filter.Germ (𝓝[≠] τ) ℂ) := by
    apply hs
    intro k
    simp only [shortShift, shortT, restrict_div_eq, map_add, map_mul, map_pow, map_ofNat,
      map_sub, ha, hb, hx, restrict_sectionAt]
    rfl
  dsimp only
  rw [analyticCluster, veluPair_eq_familyPair]
  constructor <;>
    simp only [familyPair, shortCoordinates, restrict_div_eq, map_mul, map_neg, map_pow,
      map_sub, map_add, map_ofNat, ha, hb, hx, hT, hW, hS] <;> rfl

#print axioms veluPair_eq_familyPair
#print axioms familyPair_scale
#print axioms normalized_familyPair_eq_lattice
#print axioms restrict_analytic_pair

end BShFamily
