import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ModelColumns

/-! Merge the exact cuspidal labels of the fixed set before choosing
coordinates. The only printed input here is old/new independence. -/

noncomputable section

set_option maxHeartbeats 900000

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion
open HeckeRing.GL2 ModularForm NumberField UpperHalfPlane Wiring
open CongruenceSubgroup Matrix.SpecialLinearGroup TauCeti
open ZInQ.Contrib.CloudB3RC53
open scoped MatrixGroups

/-- The source label does not record the level or the character of a block
in which it occurs. -/
structure NormalizedCuspSource where
  level : ℕ
  level_ne : level ≠ 0
  newform : @Newform level ⟨level_ne⟩ 2

namespace NormalizedCuspSource

variable (s : NormalizedCuspSource)

def coeff (n : ℕ) : ℂ :=
  letI : NeZero s.level := ⟨s.level_ne⟩
  (qExpansion 1 s.newform.toCuspForm).coeff n

def char : (ZMod s.level)ˣ →* ℂˣ :=
  letI : NeZero s.level := ⟨s.level_ne⟩
  s.newform.χ

def field : IntermediateField ℚ ℂ :=
  letI : NeZero s.level := ⟨s.level_ne⟩
  CoefficientField s.newform

theorem coeff_zero : s.coeff 0 = 0 :=
  letI : NeZero s.level := ⟨s.level_ne⟩
  CuspFormClass.qExpansion_coeff_zero s.newform.toCuspForm one_pos
    (one_mem_strictPeriods_Gamma1_map _)

theorem coeff_mem_field (n : ℕ) : s.coeff n ∈ s.field := by
  letI : NeZero s.level := ⟨s.level_ne⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [s.coeff_zero]
    exact zero_mem _
  · exact coeff_mem_CoefficientField s.newform ⟨n, hn⟩

theorem char_mem_field (u : (ZMod s.level)ˣ) : (s.char u : ℂ) ∈ s.field :=
  letI : NeZero s.level := ⟨s.level_ne⟩
  char_mem_CoefficientField s.newform u

end NormalizedCuspSource

/-- An old column at the ambient level. The normalized newform and its
degree identify the column, including across repeated occurrences. -/
structure CuspDilation (N : ℕ) where
  source : NormalizedCuspSource
  degree : ℕ
  divides : degree * source.level ∣ N

namespace CuspDilation

variable {N : ℕ} (x : CuspDilation N)

theorem source_dvd : x.source.level ∣ N := dvd_of_mul_left_dvd x.divides

def char : (ZMod N)ˣ →* ℂˣ := x.source.char.comp (ZMod.unitsMap x.source_dvd)

def coeff : ℕ → ℂ := Odd.divCoeff x.source.coeff x.degree

def old [NeZero N] : CuspOldColumn N x.char :=
  ⟨x.source.level, x.degree, x.divides, x.source.newform, rfl⟩

def form [NeZero N] : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 := x.old.form

theorem coeff_form [NeZero N] (n : ℕ) : (qExpansion 1 x.form).coeff n = x.coeff n :=
  x.old.coeff_form n

end CuspDilation

/-- **Old/new independence in weight two** (printed-form leaf, locators
UNVERIFIED): at level `N` the distinct dilations `f(dτ)` of normalized
cuspidal newforms with `d * level(f) ∣ N` are linearly independent in
`S₂(Γ₁(N))`. Diamond–Shurman, *A First Course in Modular Forms* (GTM 228,
2005), Theorem 5.8.3 (newforms and their dilations form a basis of
`S_k(Γ₁(N))`); for trivial character, Atkin–Lehner, Math. Ann. 185 (1970),
Theorem 5, p. 151 (their `k` is classical weight `2k`). W.-C. Li, Math.
Ann. 212 (1975), uses this independence (pp. 302, 309) without proving it;
Li's Theorem 5 (p. 298) is strong multiplicity one, not this statement. -/
def OldNewIndependenceWeightTwo : Prop :=
  ∀ (N : ℕ) [NeZero N], LinearIndependent ℂ (fun x : CuspDilation N => x.form)

/-- Passing from the actual cusp forms to their Fourier series preserves
the independence asserted by the print. -/
theorem cuspDilation_coeff_independent (hLi : OldNewIndependenceWeightTwo)
    {N : ℕ} [NeZero N] : LinearIndependent ℂ (CuspDilation.coeff (N := N)) := by
  let Q : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 →ₗ[ℂ] (ℕ → ℂ) :=
    LinearMap.pi fun n => CuspForm.qExpansionCoeffₗ one_pos (one_mem_strictPeriods_Gamma1_map _) 2 n
  have hQ : Function.Injective Q := by
    intro f g h
    apply CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map _)
    ext n
    simpa only [Q, LinearMap.pi_apply, CuspForm.qExpansionCoeffₗ_apply] using congrFun h n
  have he : CuspDilation.coeff (N := N) = Q ∘ (fun x : CuspDilation N => x.form) := by
    funext x n
    simpa only [Q, Function.comp_apply, LinearMap.pi_apply, CuspForm.qExpansionCoeffₗ_apply]
      using (x.coeff_form n).symm
  rw [he]
  exact (hLi N).map' Q (LinearMap.ker_eq_bot.mpr hQ)

namespace CuspBlockExpansion

variable {m N : ℕ} {a : ℕ → ℂ} (A : CuspBlockExpansion m a)

/-- View an intrinsic column at an ambient level without changing its
source or its dilation. -/
def liftColumn (hm : m ∣ N) (c : ↥A.columns) : CuspDilation N := by
  letI : NeZero m := ⟨A.level_ne⟩
  exact ⟨⟨c.val.level, ((NeZero.of_dvd (dvd_of_mul_left_dvd c.val.divides)) :
      NeZero c.val.level).out, c.val.newform⟩, c.val.degree, c.val.divides.trans hm⟩

theorem liftColumn_level (hm : m ∣ N) (c : ↥A.columns) :
    (A.liftColumn hm c).degree * (A.liftColumn hm c).source.level ∣ m :=
  letI : NeZero m := ⟨A.level_ne⟩
  c.val.divides

theorem liftColumn_char (hm : m ∣ N) (c : ↥A.columns) :
    (A.liftColumn hm c).char = A.χ.toUnitHom.comp (ZMod.unitsMap hm) := by
  let : NeZero m := ⟨A.level_ne⟩
  have h := c.val.character
  change _ = A.χ.toUnitHom at h
  rw [← h, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  rfl

theorem liftColumn_coeff (hm : m ∣ N) (c : ↥A.columns) :
    (A.liftColumn hm c).coeff = A.colCoeff c := rfl

theorem liftColumn_field (hm : m ∣ N) (c : ↥A.columns) :
    (A.liftColumn hm c).source.field = A.colField c := rfl

end CuspBlockExpansion

section Finite

variable {D : Type} [Fintype D] {N : ℕ} {m : D → ℕ} {a : D → ℕ → ℂ}
variable (A : ∀ b, CuspBlockExpansion (m b) (a b)) (hm : ∀ b, m b ∣ N)

/-- The finite image merges occurrences without testing Fourier equality
or choosing a basis by deletion. -/
def distinctCuspColumns : Finset (CuspDilation N) := by
  classical
  exact (Finset.univ : Finset (Σ b, ↥(A b).columns)).image fun x =>
    (A x.1).liftColumn (hm x.1) x.2

theorem mem_distinctCuspColumns (x : CuspDilation N) :
    x ∈ distinctCuspColumns A hm ↔ ∃ (b : D) (c : ↥(A b).columns), (A b).liftColumn (hm b) c = x := by
  classical
  simp only [distinctCuspColumns, Finset.mem_image, Finset.mem_univ, true_and, Sigma.exists]

def distinctCuspIndex (b : D) (c : ↥(A b).columns) : ↥(distinctCuspColumns A hm) :=
  ⟨(A b).liftColumn (hm b) c, (mem_distinctCuspColumns A hm _).2 ⟨b, c, rfl⟩⟩

end Finite

end ZInQ.Manuscript.RC.EvenJoin
