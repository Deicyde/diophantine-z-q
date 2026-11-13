import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Hilbert90
import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# The Kummer bridge in degree two: `ℤ/2`-cocycles and `Br(K)[2]`, on explicit cochains

Let `K` be a field with `2 ≠ 0`, `Kˢ` its separable closure, `G = Gal(Kˢ/K)` (Tau Ceti's
`AbsoluteGaloisGroup K`) and `M = (Kˢ)ˣ` written additively (Tau Ceti's `UnitsCoeff K`, discrete).
The sign map `sgn : ℤ/2 → M`, `1 ↦ -1`, is injective and `G`-equivariant (`G` fixes `±1`).
On Tau Ceti's explicit continuous cochains (`Z2`, `B2`, `H2` of `ContCohomology.LowDegree`):

* `isCoboundary2_of_sgn_mem_B2`: if `sgn ∘ ε` is a continuous coboundary in `M`, then the
  `ℤ/2`-cocycle `ε` is a continuous coboundary (Hilbert 90, `subsingleton_H1_unitsCoeff`, plus
  square roots in `Kˢ`);
* `exists_sgn_eq_of_two_nsmul`: every class of `H²(G, M)` killed by `2` is the class of `sgn ∘ ε`
  for a continuous `ℤ/2`-cocycle `ε`.

Together these say that `H²(G, ℤ/2) → H²(G, (Kˢ)ˣ)[2]` is bijective, which is the Kummer
identification `H²(G_K, μ₂) ≅ Br(K)[2]` (Serre, *Corps locaux*, X §4-5; STANDARD), proved here
directly on cochains.  `h2TwoClasses_of_two_torsion` turns "`H²(G, M)` has exactly one nonzero
element killed by `2`" into `PkgI6.H2TwoClasses G`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

namespace ZInQ.Contrib.BrauerT14T15

open TauCeti TauCeti.ContCohomology PkgI6

variable (K : Type) [Field K]

local notation "G" => AbsoluteGaloisGroup K
local notation "M" => UnitsCoeff K

/-- The sign map `ℤ/2 → (Kˢ)ˣ`, `a ↦ (-1)^a`, written additively. -/
noncomputable def sgn : ZMod 2 →+ M :=
  ZMod.lift 2 ⟨zmultiplesHom M (Additive.ofMul (-1)), by
    rw [zmultiplesHom_apply]
    apply Additive.toMul.injective
    simp⟩

@[simp] lemma sgn_one : sgn K 1 = Additive.ofMul (-1) := by
  have h : ((1 : ℤ) : ZMod 2) = 1 := by simp
  rw [← h, sgn, ZMod.lift_coe]
  simp

lemma sgn_cases (a : ZMod 2) : sgn K a = 0 ∨ sgn K a = Additive.ofMul (-1) := by
  fin_cases a
  · left; exact map_zero _
  · right; exact sgn_one K

variable {K}

lemma neg_one_ne_one (h2 : (2 : K) ≠ 0) : ((-1 : (SeparableClosure K)ˣ)) ≠ 1 := by
  intro h
  have h' : ((-1 : (SeparableClosure K)ˣ) : SeparableClosure K) = 1 := by rw [h]; rfl
  have h2' : (2 : SeparableClosure K) ≠ 0 := by
    have h := (map_ne_zero (algebraMap K (SeparableClosure K))).mpr h2
    rwa [map_ofNat] at h
  apply h2'
  have : (-1 : SeparableClosure K) = 1 := by simpa using h'
  linear_combination -this

lemma ofMul_neg_one_ne_zero (h2 : (2 : K) ≠ 0) : (Additive.ofMul (-1) : M) ≠ 0 := by
  intro h
  exact neg_one_ne_one h2 (Additive.ofMul.injective h)

lemma sgn_injective (h2 : (2 : K) ≠ 0) : Function.Injective (sgn K) := by
  intro a b hab
  have h1 : sgn K 1 ≠ sgn K 0 := by rw [sgn_one, map_zero]; exact ofMul_neg_one_ne_zero h2
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab h1 | exact absurd hab.symm h1

lemma smul_ofMul_neg_one (g : G) : g • (Additive.ofMul (-1) : M) = Additive.ofMul (-1) := by
  apply Additive.toMul.injective
  rw [Additive.toMul_smul]
  apply Units.ext
  simp [AlgEquiv.smul_units_def]

lemma smul_sgn (g : G) (a : ZMod 2) : g • sgn K a = sgn K a := by
  rcases sgn_cases K a with h | h <;> rw [h]
  · exact smul_zero g
  · exact smul_ofMul_neg_one g

/-- The `2`-torsion of `(Kˢ)ˣ` is `{1, -1}`. -/
lemma two_torsion (m : M) (hm : 2 • m = 0) : m = 0 ∨ m = Additive.ofMul (-1) := by
  have hu : (Additive.toMul m) ^ 2 = 1 := by
    have := congrArg Additive.toMul hm
    simpa using this
  have hv : ((Additive.toMul m : (SeparableClosure K)ˣ) : SeparableClosure K) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  rcases sq_eq_one_iff.mp hv with h | h
  · left
    apply Additive.toMul.injective
    exact Units.ext (by simpa using h)
  · right
    apply Additive.toMul.injective
    exact Units.ext (by simpa using h)

/-- The `ℤ/2` value of a `2`-torsion element of `M`: `0` for `1` and `1` otherwise. -/
noncomputable def logSgn (m : M) : ZMod 2 := by
  classical exact if m = 0 then 0 else 1

lemma sgn_logSgn (h2 : (2 : K) ≠ 0) (m : M) (hm : 2 • m = 0) : sgn K (logSgn m) = m := by
  classical
  rcases two_torsion m hm with h | h
  · subst h; simp [logSgn]
  · rw [h, logSgn, ite_eq_right_iff.mpr (fun h' => absurd h' (ofMul_neg_one_ne_zero h2)), sgn_one]

/-- Every element of `M` has a square root: `Kˢ` is separably closed and `2 ≠ 0`. -/
lemma exists_two_nsmul_eq (h2 : (2 : K) ≠ 0) (m : M) : ∃ r : M, 2 • r = m := by
  have h2' : (2 : SeparableClosure K) ≠ 0 := by
    have h := (map_ne_zero (algebraMap K (SeparableClosure K))).mpr h2
    rwa [map_ofNat] at h
  have : NeZero ((2 : ℕ) : SeparableClosure K) := ⟨by exact_mod_cast h2'⟩
  obtain ⟨v, hv⟩ := IsSepClosed.exists_pow_nat_eq
    ((Additive.toMul m : (SeparableClosure K)ˣ) : SeparableClosure K) 2
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
    exact (Additive.toMul m).ne_zero hv.symm
  refine ⟨Additive.ofMul (Units.mk0 v hv0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  simp [hv]

/-- `sgn ∘ ε` is a continuous `2`-cocycle of `G` with values in `M` when `ε` is one with values in
`ℤ/2`. -/
lemma sgn_mem_Z2 {ε : G → G → ZMod 2} (hε : IsCocycle2 ε) :
    (fun q : G × G => sgn K (ε q.1 q.2)) ∈ Z2 G M := by
  rw [mem_Z2_iff]
  refine ⟨continuous_of_discreteTopology.comp hε.1, fun a b c => ?_⟩
  simp only [smul_sgn]
  have := hε.2 a b c
  rw [← map_add, ← map_add]
  congr 1
  linear_combination -this

/-- **Kummer injectivity in degree two, on cochains.** If `sgn ∘ ε` is a continuous coboundary
in `(Kˢ)ˣ`, the `ℤ/2`-cocycle `ε` is a continuous coboundary. -/
theorem isCoboundary2_of_sgn_mem_B2 (h2 : (2 : K) ≠ 0) {ε : G → G → ZMod 2}
    (hε : IsCocycle2 ε) (hB : (fun q : G × G => sgn K (ε q.1 q.2)) ∈ B2 G M) :
    IsCoboundary2 ε := by
  obtain ⟨f, hfc, hf⟩ := mem_B2_iff.mp hB
  -- `2 • f` is a continuous 1-cocycle.
  have h2f : (2 • f) ∈ Z1 G M := by
    rw [mem_Z1_iff]
    refine ⟨((continuous_of_discreteTopology (f := fun m : M => 2 • m)).comp hfc).congr
      (fun _ => rfl), ?_⟩
    rw [← d1_apply_eq_zero_iff, map_nsmul, hf]
    funext q
    simp only [Pi.smul_apply, Pi.zero_apply]
    rw [← map_nsmul]
    have : (2 • ε q.1 q.2 : ZMod 2) = 0 := by
      rw [two_nsmul]; generalize ε q.1 q.2 = x; fin_cases x <;> decide
    rw [this, map_zero]
  -- Hilbert 90: it is a coboundary.
  have hB1 : (2 • f) ∈ B1 G M := by
    have h0 : (H1pi G M ⟨2 • f, h2f⟩ : H1 G M) = 0 := Subsingleton.elim _ _
    exact (H1pi_eq_zero_iff (f := ⟨2 • f, h2f⟩)).mp h0
  obtain ⟨m, hm⟩ := hB1
  obtain ⟨r, hr⟩ := exists_two_nsmul_eq h2 m
  set f' : G → M := f - d0 G M r with hf'
  have hf'2 : ∀ g, 2 • f' g = 0 := by
    intro g
    have e := congrFun hm g
    simp only [d0_apply, Pi.smul_apply] at e
    rw [hf', Pi.sub_apply, d0_apply, nsmul_sub, nsmul_sub, smul_comm (2 : ℕ) g r, hr, e,
      sub_self]
  have hf'c : Continuous f' := by rw [hf']; exact hfc.sub (continuous_d0_apply r)
  have hd : d1 G M f' = fun q => sgn K (ε q.1 q.2) := by
    rw [hf', map_sub, hf, d1_comp_d0_apply, sub_zero]
  refine ⟨fun g => logSgn (f' g), (continuous_of_discreteTopology (f := logSgn)).comp hf'c,
    fun a b => ?_⟩
  · apply sgn_injective h2
    have := congrFun hd (a, b)
    simp only [d1_apply] at this
    rw [← this, map_add, map_sub, sgn_logSgn h2 _ (hf'2 _), sgn_logSgn h2 _ (hf'2 _),
      sgn_logSgn h2 _ (hf'2 _)]
    rcases two_torsion (f' b) (hf'2 b) with h | h <;> rw [h]
    · rw [smul_zero]
    · rw [smul_ofMul_neg_one]

/-- **Kummer surjectivity onto the `2`-torsion of `H²(G, (Kˢ)ˣ)`, on cochains.** -/
theorem exists_sgn_eq_of_two_nsmul (h2 : (2 : K) ≠ 0) (z : Z2 G M)
    (hz : 2 • (H2pi G M z : H2 G M) = 0) :
    ∃ ε : G → G → ZMod 2, ∃ hε : IsCocycle2 ε,
      H2pi G M ⟨_, sgn_mem_Z2 hε⟩ = H2pi G M z := by
  classical
  have hz2 : (H2pi G M (2 • z) : H2 G M) = 0 := by rw [map_nsmul]; exact hz
  have hz3 : ((2 • z : Z2 G M) : G × G → M) ∈ B2 G M := H2pi_eq_zero_iff.mp hz2
  rw [AddSubgroup.coe_nsmul] at hz3
  obtain ⟨c, hcc, hc⟩ := mem_B2_iff.mp hz3
  choose s hs using exists_two_nsmul_eq h2
  set c' : G → M := fun g => s (c g)
  have hc' : 2 • c' = c := funext fun g => hs (c g)
  set z' : G × G → M := (z : G × G → M) - d1 G M c' with hz'
  have hz'Z : z' ∈ Z2 G M := by
    refine (Z2 G M).sub_mem z.2 (B2_le_Z2 G M ?_)
    exact mem_B2_iff.mpr ⟨c', (continuous_of_discreteTopology (f := s)).comp hcc, rfl⟩
  have hz'2 : ∀ q, 2 • z' q = 0 := by
    intro q
    have h1 : 2 • (d1 G M c') = d1 G M c := by rw [← map_nsmul, hc']
    have h2' := congrFun h1 q
    have h3 := congrFun hc q
    simp only [Pi.smul_apply] at h2' h3
    simp only [hz', Pi.sub_apply]
    rw [nsmul_sub, h2', h3, sub_self]
  set ε : G → G → ZMod 2 := fun a b => logSgn (z' (a, b))
  have hsε : ∀ q : G × G, sgn K (ε q.1 q.2) = z' q := fun q => sgn_logSgn h2 _ (hz'2 q)
  have hε : IsCocycle2 ε := by
    refine ⟨((continuous_of_discreteTopology (f := logSgn)).comp (mem_Z2_iff.mp hz'Z).1).congr
      (fun _ => rfl), fun a b c => ?_⟩
    apply sgn_injective h2
    rw [map_zero, map_sub, map_add, map_sub]
    have := (mem_Z2_iff.mp hz'Z).2 a b c
    have e1 := hsε (b, c); have e2 := hsε (a * b, c); have e3 := hsε (a, b * c)
    have e4 := hsε (a, b)
    simp only at e1 e2 e3 e4
    rw [e1, e2, e3, e4]
    have hs : a • z' (b, c) = z' (b, c) := by
      rw [← e1, smul_sgn]
    rw [hs] at this
    calc z' (b, c) - z' (a * b, c) + z' (a, b * c) - z' (a, b)
        = -((z' (a * b, c) + z' (a, b)) - (z' (b, c) + z' (a, b * c))) := by abel
      _ = 0 := by rw [this, sub_self, neg_zero]
  refine ⟨ε, hε, ?_⟩
  have : (fun q : G × G => sgn K (ε q.1 q.2)) = z' := funext hsε
  have key : (fun q : G × G => sgn K (ε q.1 q.2)) - (z : G × G → M) ∈ B2 G M := by
    rw [this, hz', sub_sub_cancel_left]
    exact (B2 G M).neg_mem (mem_B2_iff.mpr ⟨c', (continuous_of_discreteTopology (f := s)).comp hcc,
      rfl⟩)
  exact H2pi_eq_iff.mpr key

/-- A `ℤ/2`-coboundary maps to a coboundary in `M`. -/
lemma sgn_mem_B2_of_isCoboundary2 {ε : G → G → ZMod 2} (hε : IsCoboundary2 ε) :
    (fun q : G × G => sgn K (ε q.1 q.2)) ∈ B2 G M := by
  obtain ⟨f, hfc, hf⟩ := hε
  refine mem_B2_iff'.mpr ⟨fun g => sgn K (f g), continuous_of_discreteTopology.comp hfc,
    fun a b => ?_⟩
  simp only [smul_sgn, hf, map_add, map_sub]

/-- **`H²(G, ℤ/2)` has exactly two classes** once the `2`-torsion of `H²(G, (Kˢ)ˣ)` has exactly
one nonzero element. -/
theorem h2TwoClasses_of_two_torsion (h2 : (2 : K) ≠ 0)
    (hex : ∃ x : H2 G M, x ≠ 0 ∧ 2 • x = 0)
    (huniq : ∀ x y : H2 G M, x ≠ 0 → 2 • x = 0 → y ≠ 0 → 2 • y = 0 → x = y) :
    H2TwoClasses G := by
  refine ⟨?_, fun ε₁ ε₂ c₁ c₂ n₁ n₂ => ?_⟩
  · obtain ⟨x, hx0, hx2⟩ := hex
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨ε, hε, hεz⟩ := exists_sgn_eq_of_two_nsmul h2 z hx2
    refine ⟨ε, hε, fun hcob => hx0 ?_⟩
    change H2pi G M z = 0
    rw [← hεz]
    have hB := sgn_mem_B2_of_isCoboundary2 (K := K) hcob
    exact H2pi_eq_zero_iff.mpr hB
  · have two : ∀ {ε : G → G → ZMod 2} (hε : IsCocycle2 ε),
        2 • (H2pi G M ⟨_, sgn_mem_Z2 hε⟩ : H2 G M) = 0 := by
      intro ε hε
      rw [← map_nsmul]
      refine H2pi_eq_zero_iff.mpr ?_
      have : (2 • (⟨_, sgn_mem_Z2 hε⟩ : Z2 G M) : G × G → M) = 0 := by
        funext q
        change 2 • sgn K (ε q.1 q.2) = 0
        rw [← map_nsmul, two_nsmul]
        generalize ε q.1 q.2 = x
        have : x + x = 0 := by fin_cases x <;> decide
        rw [this, map_zero]
      rw [AddSubgroup.coe_nsmul, this]; exact zero_mem _
    have ne : ∀ {ε : G → G → ZMod 2} (hε : IsCocycle2 ε), ¬ IsCoboundary2 ε →
        (H2pi G M ⟨_, sgn_mem_Z2 hε⟩ : H2 G M) ≠ 0 := by
      intro ε hε hn h0
      exact hn (isCoboundary2_of_sgn_mem_B2 h2 hε ((H2pi_eq_zero_iff).mp h0))
    have heq := huniq _ _ (ne c₁ n₁) (two c₁) (ne c₂ n₂) (two c₂)
    replace heq := H2pi_eq_iff.mp heq
    refine isCoboundary2_of_sgn_mem_B2 h2 (c₁.sub c₂) ?_
    convert heq using 1
    funext q
    simp [map_sub]

end ZInQ.Contrib.BrauerT14T15

namespace ZInQ.Contrib.BrauerT14T15

open PkgI6

/-! ### Transport of the cochain predicates along an isomorphism of topological groups -/

section Transport

variable {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]

lemma isCocycle2_comp (φ : G₁ →* G₂) (hφ : Continuous φ) {ε : G₂ → G₂ → ZMod 2}
    (h : IsCocycle2 ε) : IsCocycle2 (fun a b => ε (φ a) (φ b)) := by
  refine ⟨h.1.comp ((hφ.comp continuous_fst).prodMk (hφ.comp continuous_snd)), fun a b c => ?_⟩
  simp only [map_mul]
  exact h.2 _ _ _

lemma isCoboundary2_comp (φ : G₁ →* G₂) (hφ : Continuous φ) {ε : G₂ → G₂ → ZMod 2}
    (h : IsCoboundary2 ε) : IsCoboundary2 (fun a b => ε (φ a) (φ b)) := by
  obtain ⟨f, hf, e⟩ := h
  exact ⟨fun a => f (φ a), hf.comp hφ, fun a b => by simp only [map_mul]; exact e _ _⟩

/-- `H2TwoClasses` transports along an isomorphism of topological groups. -/
theorem h2TwoClasses_of_continuousMulEquiv (e : G₁ ≃ₜ* G₂) (h : H2TwoClasses G₂) :
    H2TwoClasses G₁ := by
  have back : ∀ ε : G₁ → G₁ → ZMod 2,
      (fun a b => (fun a b => ε (e.symm a) (e.symm b)) (e a) (e b)) = ε := by
    intro ε; funext a b; simp
  refine ⟨?_, fun ε₁ ε₂ c₁ c₂ n₁ n₂ => ?_⟩
  · obtain ⟨ε, hε, hn⟩ := h.1
    refine ⟨_, isCocycle2_comp e.toMonoidHom e.continuous hε, fun hc => hn ?_⟩
    have := isCoboundary2_comp e.symm.toMonoidHom e.symm.continuous hc
    convert this using 1
    funext a b; simp
  · have c₁' := isCocycle2_comp e.symm.toMonoidHom e.symm.continuous c₁
    have c₂' := isCocycle2_comp e.symm.toMonoidHom e.symm.continuous c₂
    have hc := h.2 _ _ c₁' c₂'
      (fun hc => n₁ (by
        have := isCoboundary2_comp e.toMonoidHom e.continuous hc
        convert this using 1; funext a b; simp))
      (fun hc => n₂ (by
        have := isCoboundary2_comp e.toMonoidHom e.continuous hc
        convert this using 1; funext a b; simp))
    have := isCoboundary2_comp e.toMonoidHom e.continuous hc
    convert this using 1
    funext a b; simp

end Transport

end ZInQ.Contrib.BrauerT14T15
