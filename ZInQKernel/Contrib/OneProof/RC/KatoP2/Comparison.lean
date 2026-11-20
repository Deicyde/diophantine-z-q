import ZInQKernel.Contrib.OneProof.RC.KatoP2.ExtendedNorm

/-! Comparing the full open of the Kodai draft with the retained dyadic
`j_*` object. The arithmetic maps and their local properties are named
separately from the formal transport of the class and length inequality. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2

open PrintsArith

/-- Degree-one coefficient and support comparison (tex 6953–6987,
7025–7034, 7243–7255, 7257–7269). Extension of a dual map is only required
after clearing a denominator outside the tested prime. An integral
isomorphism of H¹ would be too strong. -/
structure KatoH1Comparison (es : EulerSystemData ℤ_[2]) (NK : ℕ)
    (full small : IwasawaData KatoLambda2) (t : KodaiTower es NK full) where
  res : small.H1 →ₗ[KatoLambda2] full.H1
  retainedProj : ∀ n : ℕ, small.H1 →+ es.H (2 ^ n)
  proj_res : ∀ n x, 1 ≤ n → t.proj n (res x) = retainedProj n x
  retained_proj_z : ∀ n : ℕ, 1 ≤ n → retainedProj n small.zIw = es.z (2 ^ n)
  extend_local_dual :
    ∀ (𝔭 : Ideal KatoLambda2) [𝔭.IsPrime], 𝔭.height = 1 → (2 : KatoLambda2) ∉ 𝔭 →
    ∀ h : small.H1 →ₗ[KatoLambda2] KatoLambda2,
      ∃ (a : 𝔭.primeCompl) (g : full.H1 →ₗ[KatoLambda2] KatoLambda2),
        g.comp res = (a : KatoLambda2) • h

/-- The two traces in the §0.7 projection compose to the original retained
dyadic trace (tex 6994–7003 and 7025–7029). This is transitivity on classes,
not an equality inferred from local divisibility or a rescaling by degree. -/
def Kodai07Corestriction {E : WeierstrassCurve ℚ} {c ds d a : ℕ} {Y : EulerSystemData ℤ_[2]}
    {Z : RetainedZeta E c ds} (T : TwistTransfer Z d a Y) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (Y.cor (2 ^ n) (kodaiBase E d * 2 ^ n) (dvd_mul_left _ _)).comp
        (T.trace (kodaiBase E d * 2 ^ n)) =
      (T.trace (2 ^ n)).comp (Z.es.cor _ _ (Nat.mul_dvd_mul_left (primitiveD d a)
        (dvd_mul_left _ _)))

/-- In the descent to a dyadic level, both untwisted levels have the same
support after adjoining the fixed primes. Thus the base-level corestriction
has multiplier one; the extra primes of `N` were omitted already. -/
theorem retained_norm_to_dyadic {E : WeierstrassCurve ℚ} {c ds d a n : ℕ}
    (Z : RetainedZeta E c ds) (h812 : Kato812.KatoProp812Print E c ds Z.es Z.zAt)
    (hd : 0 < d) (hn : 1 ≤ n)
    (hsmooth : Nat.Coprime (kodaiBase E d) (c * ds)) :
    Z.es.cor _ _ (Nat.mul_dvd_mul_left (primitiveD d a)
        (dvd_mul_left (2 ^ n) (kodaiBase E d)))
      (Z.es.z (primitiveD d a * (kodaiBase E d * 2 ^ n))) =
      Z.es.z (primitiveD d a * 2 ^ n) := by
  have hn0 : n ≠ 0 := by omega
  have htwo : Nat.Coprime (2 : ℕ) (c * ds) :=
    Z.smooth_fixed.symm.coprime_dvd_left (dvd_mul_right _ _)
  have hd_s : Nat.Coprime d (c * ds) :=
    hsmooth.coprime_dvd_left (dvd_mul_left _ _)
  have hDo : 0 < primitiveD d a := by dsimp [primitiveD]; positivity
  have hbase : 0 < kodaiBase E d := by have := Z.level_pos; dsimp [kodaiBase]; positivity
  have hu : 0 < primitiveD d a * (kodaiBase E d * 2 ^ n) := by positivity
  have hl : 0 < primitiveD d a * 2 ^ n := by positivity
  have hnorm := retained_norm Z h812 hl hu (Nat.mul_dvd_mul_left (primitiveD d a)
    (dvd_mul_left (2 ^ n) (kodaiBase E d)))
    ((hd_s.mul_left (htwo.pow_left a)).mul_left (hsmooth.mul_left (htwo.pow_left n)))
  have hsupport : (kodaiBase E d).primeFactors ⊆
      Kato812.fixedSupport E ∪ (primitiveD d a * 2 ^ n).primeFactors := by
    rw [kodaiBase, Nat.primeFactors_mul (by have := Z.level_pos; positivity) hd.ne']
    refine Finset.union_subset Finset.subset_union_left ?_
    exact (Nat.primeFactors_mono ((dvd_mul_right d (2 ^ a)).trans
      (dvd_mul_right (primitiveD d a) (2 ^ n))) hl.ne').trans Finset.subset_union_right
  have hdiff : (primitiveD d a * (kodaiBase E d * 2 ^ n)).primeFactors \
      (Kato812.fixedSupport E ∪ (primitiveD d a * 2 ^ n).primeFactors) = ∅ := by
    rw [Finset.sdiff_eq_empty_iff_subset,
      show primitiveD d a * (kodaiBase E d * 2 ^ n) =
        kodaiBase E d * (primitiveD d a * 2 ^ n) by ac_rfl,
      Nat.primeFactors_mul hbase.ne' hl.ne']
    exact Finset.union_subset hsupport Finset.subset_union_right
  simpa only [hdiff, Finset.prod_empty, one_smul] using hnorm

/-- The §0.7 class is the image of the retained dyadic class. The proof
compares projections and uses transitivity and the empty support norm. -/
theorem kodai07_eq_retained {E : WeierstrassCurve ℚ} {c ds d a : ℕ} {Y : EulerSystemData ℤ_[2]}
    {Z : RetainedZeta E c ds} (T : TwistTransfer Z d a Y)
    (h812 : Kato812.KatoProp812Print E c ds Z.es Z.zAt)
    (hd : 0 < d) (hsmooth : Nat.Coprime (kodaiBase E d) (c * ds))
    {full small : IwasawaData KatoLambda2} {t : KodaiTower Y (kodaiBase E d) full}
    (C : KatoH1Comparison Y (kodaiBase E d) full small t)
    (ht : t.IsClass07) (htrace : Kodai07Corestriction T) :
    C.res small.zIw = full.zIw := by
  apply t.joint
  intro n hn
  rw [C.proj_res n _ hn, C.retained_proj_z n hn, ht n hn, t.corestrict_eq,
    T.z_spec (kodaiBase E d * 2 ^ n)]
  have h := DFunLike.congr_fun (htrace n hn)
    (Z.es.z (primitiveD d a * (kodaiBase E d * 2 ^ n)))
  simp only [AddMonoidHom.comp_apply] at h
  rw [h, retained_norm_to_dyadic Z h812 hd hn hsmooth, ← T.z_spec]

/-- The degree-two open restriction and local restriction commute. Its kernel
is torsion. At an away-two height-one localization the open restriction is
injective, as would follow from the local cones of (K16) with no H¹. This
condition makes no assertion about the size of either H² or about any class. -/
structure KatoSupportComparison (full small : IwasawaData KatoLambda2) where
  res : small.H2 →ₗ[KatoLambda2] full.H2
  localRes : small.H2loc →ₗ[KatoLambda2] full.H2loc
  commutes : full.loc.comp res = localRes.comp small.loc
  ker_torsion : Module.IsTorsion KatoLambda2 (LinearMap.ker res)
  inj_away : ∀ (𝔭 : Ideal KatoLambda2) [𝔭.IsPrime], 𝔭.height = 1 →
    (2 : KatoLambda2) ∉ 𝔭 → Function.Injective (LocalizedModule.map 𝔭.primeCompl res)

/-- The comparison respects the dyadic localization kernels. -/
def KatoSupportComparison.onKernel {full small : IwasawaData KatoLambda2}
    (C : KatoSupportComparison full small) : small.H2zero →ₗ[KatoLambda2] full.H2zero :=
  (C.res.comp small.H2zero.subtype).codRestrict full.H2zero fun x => by
    change full.loc (C.res x) = 0
    have h := DFunLike.congr_fun C.commutes (x : small.H2)
    simp only [LinearMap.comp_apply] at h
    rw [h, LinearMap.mem_ker.mp x.property, map_zero]

/-- (K15), in the original support on its original retained class. -/
def RetainedK15 (small : IwasawaData KatoLambda2) : Prop :=
  Module.IsTorsion KatoLambda2 small.H2 ∧
    ∀ (𝔭 : Ideal KatoLambda2) [𝔭.IsPrime], 𝔭.height = 1 → (2 : KatoLambda2) ∉ 𝔭 →
      Module.length (Localization.AtPrime 𝔭)
        (LocalizedModule 𝔭.primeCompl small.H2zero) ≤ classIndex small 𝔭

/-- Each evaluation of the retained class belongs to its index ideal. -/
theorem eval_mem_J (D : IwasawaData KatoLambda2)
    (g : D.H1 →ₗ[KatoLambda2] KatoLambda2) : g D.zIw ∈ D.J :=
  (le_iSup (fun h : D.H1 →ₗ[KatoLambda2] KatoLambda2 => D.Z.map h) g)
    ⟨D.zIw, Submodule.subset_span (Set.mem_singleton _), rfl⟩

/-- The needed orientation of the class-index comparison. Extend each
evaluation from the small open after clearing a unit at the tested prime. -/
theorem map_J_le_of_extend {es : EulerSystemData ℤ_[2]} {NK : ℕ}
    {full small : IwasawaData KatoLambda2} {t : KodaiTower es NK full}
    (C : KatoH1Comparison es NK full small t) (hz : C.res small.zIw = full.zIw)
    (𝔭 : Ideal KatoLambda2) [𝔭.IsPrime] (hh : 𝔭.height = 1) (h2 : (2 : KatoLambda2) ∉ 𝔭) :
    small.J.map (algebraMap KatoLambda2 (Localization.AtPrime 𝔭)) ≤
      full.J.map (algebraMap KatoLambda2 (Localization.AtPrime 𝔭)) := by
  let ι := algebraMap KatoLambda2 (Localization.AtPrime 𝔭)
  change small.J.map ι ≤ full.J.map ι
  apply Ideal.map_le_iff_le_comap.mpr
  apply iSup_le
  intro h
  rw [IwasawaData.Z, Submodule.map_span, Set.image_singleton]
  apply Submodule.span_le.mpr
  rintro _ rfl
  obtain ⟨a, g, hg⟩ := C.extend_local_dual 𝔭 hh h2 h
  have he := DFunLike.congr_fun hg small.zIw
  change g (C.res small.zIw) = (a : KatoLambda2) * h small.zIw at he
  rw [hz] at he
  have hmem := Ideal.mem_map_of_mem ι (eval_mem_J full g)
  rw [he, map_mul] at hmem
  change ι (h small.zIw) ∈ full.J.map ι
  obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime 𝔭) a
  rw [← hu] at hmem
  have hmul := (full.J.map ι).mul_mem_left (↑u⁻¹ : Localization.AtPrime 𝔭) hmem
  simpa [← mul_assoc] using hmul

/-- Transport the 1999 length bound to the (K15) modules. One inequality
comes from the localized injection on kernels; the other is the quotient
map induced by the inclusion of evaluation ideals. -/
theorem retainedK15_of_kodai08 {es : EulerSystemData ℤ_[2]} {NK : ℕ}
    {full small : IwasawaData KatoLambda2} {t : KodaiTower es NK full}
    (C₁ : KatoH1Comparison es NK full small t) (C₂ : KatoSupportComparison full small)
    (hz : C₁.res small.zIw = full.zIw) (h08 : Kodai08AwayTwo full) : RetainedK15 small := by
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := h08.1 (x := C₂.res x)
    have hax : C₂.res ((a : KatoLambda2) • x) = 0 := by
      rw [map_smul]
      exact ha
    obtain ⟨b, hb⟩ := C₂.ker_torsion (x := ⟨_, hax⟩)
    refine ⟨b * a, ?_⟩
    simpa [Submonoid.smul_def, mul_smul] using congrArg Subtype.val hb
  · intro 𝔭 _ hh h2
    let j := LocalizedModule.map 𝔭.primeCompl C₂.onKernel
    have hj : Function.Injective j := by
      have hc (z : LocalizedModule 𝔭.primeCompl small.H2zero) :
          LocalizedModule.map 𝔭.primeCompl full.H2zero.subtype (j z) =
            LocalizedModule.map 𝔭.primeCompl C₂.res
              (LocalizedModule.map 𝔭.primeCompl small.H2zero.subtype z) := by
        induction z using LocalizedModule.induction_on with
        | _ x a =>
          simp only [j, LocalizedModule.map_mk]
          rfl
      intro x y hxy
      apply LocalizedModule.map_injective 𝔭.primeCompl small.H2zero.subtype
        small.H2zero.subtype_injective
      apply C₂.inj_away 𝔭 hh h2
      rw [← hc, ← hc, hxy]
    have hJ := map_J_le_of_extend C₁ hz 𝔭 hh h2
    exact (Module.length_le_of_injective j hj).trans ((h08.2 𝔭 hh h2).trans
      (Module.length_le_of_surjective (Submodule.factor hJ) (Submodule.factor_surjective hJ)))

end ZInQ.Manuscript.RC.KatoP2
