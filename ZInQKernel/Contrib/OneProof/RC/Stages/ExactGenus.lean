import ZInQKernel.Contrib.OneProof.RC.Stages.GenusDescent
import ZInQKernel.Contrib.OneProof.RC.Stages.UniformBound
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ElliotClosure
import ZInQKernel.Contrib.OneProof.RC.Visibility.Genus

/-! The uniform multiplier on the native genus lattice, tex 8274–8306. -/

noncomputable section

open scoped WeierstrassCurve
open WeierstrassCurve NumberField
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
  ZInQ.Contrib.CloudB3RC53

namespace ZInQ.Manuscript.RC.Stages

section FieldLevel

variable {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]
variable [DecidableEq (ringClassField (conductorOrder K c))] {χ : Pic (conductorOrder K c) →* ℂˣ}

/-- The rational twist embedding has the native character of the genus root. -/
theorem twistEmb_mem_eigenLattice (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {d : ℚ} {s : ringClassField (conductorOrder K c)} (hs : s ≠ 0)
    (hd : s ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) d)
    (hsign : ∀ g : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
      g s = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm g) : ℤ) * s)
    (R : (qtwist E d).toAffine.Point) :
    twistEmb E d s (twistVC_smul E h₁ h₃ hs hd) R ∈ eigenLattice E χ := by
  classical
  intro g
  let i := (ringClassArtinEquiv (conductorOrder K c)).symm g
  have hg := hsign g
  change g s = (chiSign χ i : ℤ) * s at hg
  have hi : chiSign χ i = 1 ∨ chiSign χ i = -1 := by
    unfold chiSign
    split_ifs <;> simp
  change Affine.Point.map (W' := E) (g.toAlgHom.restrictScalars ℚ)
    (twistEmb E d s (twistVC_smul E h₁ h₃ hs hd) R) = chiSign χ i • _
  rcases hi with hp | hm
  · have he : g s = s := by simpa [hp] using hg
    rw [map_twistEmb_eq_ite E h₁ h₃ d _ hs hd (Or.inl he)]
    simp [hp, he]
  · have he : g s = -s := by simpa [hm] using hg
    have hne : g s ≠ s := fun h => hs (by rw [h] at he; linear_combination he / 2)
    rw [map_twistEmb_eq_ite E h₁ h₃ d _ hs hd (Or.inr he)]
    simp [hm, hne, neg_smul]

/-- The eight-count product annihilates torsion in the native character group. -/
theorem uniform_kills_native (C : WeierstrassCurve ℤ) (hK : Module.finrank ℚ K = 2)
    {s : ringClassField (conductorOrder K c)} {d : ℚ} (hs : s ≠ 0)
    (hd : s ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) d)
    (hsign : ∀ g : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
      g s = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm g) : ℤ) * s)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hp : ¬ (p : ℤ) ∣ C.Δ) (hq : ¬ (q : ℤ) ∣ C.Δ)
    {P : ((C⁄ℚ)⁄(ringClassField (conductorOrder K c))).toAffine.Point}
    (hP : P ∈ eigenLattice (C⁄ℚ) χ)
    (hPtor : IsOfFinAddOrder P) :
    (reductionBound (finiteCount C p) * reductionBound (finiteCount C q)) • P = 0 := by
  let F := IntermediateField.adjoin K ({s} : Set (ringClassField (conductorOrder K c)))
  letI := Classical.decEq F
  have hF : Module.finrank ℚ F ≤ 4 := finrank_genusField hK
    (d := algebraMap ℚ K d)
    (by rwa [IsScalarTower.algebraMap_apply ℚ K (ringClassField (conductorOrder K c))] at hd)
  obtain ⟨R, hR⟩ := eigenPoint_descends (C⁄ℚ) hs hsign hP
  let j := Affine.Point.baseChange (W' := (C⁄ℚ)) F (ringClassField (conductorOrder K c))
  have hj : Function.Injective j := Affine.Point.map_injective _
  change j R = P at hR
  have htor : IsOfFinAddOrder R := by
    obtain ⟨n, hn, h⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hPtor
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hj ?_⟩
    rwa [map_nsmul, map_zero, hR]
  have hmodel : (C⁄ℚ)⁄F = C.map (Int.castRingHom F) := by
    change (C.map (algebraMap ℤ ℚ)).map (algebraMap ℚ F) = _
    rw [WeierstrassCurve.map_map]
    congr 1
    ext m
    simp
  suffices hb : ∀ X : ((C⁄ℚ)⁄F).toAffine.Point, IsOfFinAddOrder X →
      (reductionBound (finiteCount C p) * reductionBound (finiteCount C q)) • X = 0 by
    rw [← hR, ← map_nsmul, hb R htor, map_zero]
  rw [hmodel]
  exact fun _ ht => uniform_two_prime_bound C hpq hp hq hF ht

/-- Rank zero on the other twist gives the existing comparison modulo torsion.
The bounded-degree product clears that torsion; the resulting rational point
is exactly the manuscript's multiple in the ring class field. -/
theorem exact_twist_of_genus (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic]
    (h₁ : (C⁄ℚ).a₁ = 0) (h₃ : (C⁄ℚ).a₃ = 0) (hK : Module.finrank ℚ K = 2)
    {dR dT : ℚ} {sR sT : ringClassField (conductorOrder K c)}
    (hsR : sR ≠ 0) (hR : sR ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) dR)
    (hsT : sT ≠ 0) (hT : sT ^ 2 = algebraMap ℚ (ringClassField (conductorOrder K c)) dT)
    (hneg : dR * dT < 0)
    (hσ : ∀ g : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
      g sR = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm g) : ℤ) * sR ∧
      g sT = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm g) : ℤ) * sT)
    (htorT : ∀ R : (qtwist (C⁄ℚ) dT).toAffine.Point, IsOfFinAddOrder R)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hp : ¬ (p : ℤ) ∣ C.Δ) (hq : ¬ (q : ℤ) ∣ C.Δ)
    (L₀ : ℕ) {P : ((C⁄ℚ)⁄(ringClassField (conductorOrder K c))).toAffine.Point}
    (hP : P ∈ eigenLattice (C⁄ℚ) χ) :
    let B := reductionBound (finiteCount C p) * reductionBound (finiteCount C q)
    ∃ R : (qtwist (C⁄ℚ) dR).toAffine.Point,
      twistEmb (C⁄ℚ) dR sR (twistVC_smul (C⁄ℚ) h₁ h₃ hsR hR) R = (L₀ * (4 * B)) • P ∧
      (L₀ ≠ 0 → ¬ IsOfFinAddOrder P → ¬ IsOfFinAddOrder R) := by
  intro B
  let j := twistEmb (C⁄ℚ) dR sR (twistVC_smul (C⁄ℚ) h₁ h₃ hsR hR)
  obtain ⟨R, htor⟩ := two_nsmul_mem_twist_add_torsion' (C⁄ℚ) h₁ h₃ hK
    hsR hR hsT hT hneg hσ htorT P hP
  change IsOfFinAddOrder ((2 : ℕ) • P - j R) at htor
  have hRmem : j R ∈ eigenLattice (C⁄ℚ) χ :=
    twistEmb_mem_eigenLattice (C⁄ℚ) h₁ h₃ hsR hR (fun g => (hσ g).1) R
  have hk : B • ((2 : ℕ) • P - j R) = 0 :=
    uniform_kills_native C hK hsR hR (fun g => (hσ g).1) hpq hp hq
      (AddSubgroup.sub_mem _ (AddSubgroup.nsmul_mem _ hP 2) hRmem) htor
  have he : B • ((2 : ℕ) • P) = B • j R := sub_eq_zero.mp (by simpa only [nsmul_sub] using hk)
  refine ⟨((L₀ * 2) * B) • R, ?_, ?_⟩
  · change j (((L₀ * 2) * B) • R) = _
    rw [map_nsmul, mul_nsmul', ← he]
    simp only [← mul_nsmul']
    congr 1 <;> ring
  · intro hL₀ hnt
    have hpos (r : ℕ) [Fact r.Prime] : 0 < reductionBound (finiteCount C r) := by
      unfold reductionBound
      exact Finset.prod_pos fun f _ => finiteCount_pos C r f
    have hB : B ≠ 0 := (mul_pos (hpos p) (hpos q)).ne'
    exact (exact_scaled_witness j (m := 2) (L₀ := L₀ * 2)
      (by exact Nat.mul_ne_zero (Nat.mul_ne_zero hL₀ (by decide)) (Nat.mul_ne_zero (by decide) hB))
      P R hnt hk).2

end FieldLevel

set_option maxRecDepth 2048 in
open ZInQ.Manuscript.RC.Visibility in
/-- Apply the common multiplier to the selected conductor-one genus datum.
The two roots come from the existing genus theorem; rank zero on the unwanted
twist uses the existing forward Kolyvagin theorem (cited statement, GLUE). -/
theorem exact_twist_of_genusPoint (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic]
    (h₁ : (C⁄ℚ).a₁ = 0) (h₃ : (C⁄ℚ).a₃ = 0) (P : Prints)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (C⁄ℚ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {D hstar : ℤ}
    (hD : 0 < D) (hodd : Odd (D * hstar)) (hgp : GenusPartner (C⁄ℚ) hstar)
    (dat : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hp : ¬ (p : ℤ) ∣ C.Δ) (hq : ¬ (q : ℤ) ∣ C.Δ) (L₀ : ℕ) :
    letI := dat.field
    letI := dat.nf
    letI := dat.nz
    let H := ringClassField (conductorOrder dat.K 1)
    letI := Classical.decEq H
    let B := reductionBound (finiteCount C p) * reductionBound (finiteCount C q)
    ∃ (s : H) (hs : s ≠ 0) (hd : s ^ 2 = algebraMap ℚ H (D : ℚ))
      (R : (qtwist (C⁄ℚ) (D : ℚ)).toAffine.Point),
      twistEmb (C⁄ℚ) D s (twistVC_smul (C⁄ℚ) h₁ h₃ hs hd) R =
        (L₀ * (4 * B)) • genusPoint dat ∧
      (L₀ ≠ 0 → ¬ IsOfFinAddOrder (genusPoint dat) → ¬ IsOfFinAddOrder R) := by
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  let H := ringClassField (conductorOrder dat.K 1)
  letI := Classical.decEq H
  obtain ⟨hstarNeg, hstar4, hstarSq, -, -, hRank⟩ := hgp
  have hstar0 : (hstar : ℚ) ≠ 0 := by exact_mod_cast hstarNeg.ne
  have hE := qtwist_isElliptic (C⁄ℚ) hstar0
  have htorT : ∀ R : (qtwist (C⁄ℚ) hstar).toAffine.Point, IsOfFinAddOrder R :=
    torsion_of_rank_zero (by
      exact_mod_cast (P.kolyvagin (qtwist (C⁄ℚ) hstar) hE (P.bcdt _ hE) 0
        (by norm_num) hRank).1)
  have hprod : hstar * D = discr dat.K * (1 : ℤ) ^ 2 := by rw [dat.disc]; simp [mul_comm]
  obtain ⟨sT, sR, hT, hR, hg⟩ := genusRoots_proof dat.K dat.finrank_two dat.totallyComplex
    (dat.disc.symm ▸ hodd) 1 hstar D hprod hstar4 hstarSq (by simp) (by simp) dat.χ dat.quad
  have hsR : sR ≠ 0 := by
    intro hs
    have hz : (D : H) = 0 := by simpa [hs] using hR.symm
    exact hD.ne' (by exact_mod_cast hz)
  have hsT : sT ≠ 0 := by
    intro hs
    have hz : (hstar : H) = 0 := by simpa [hs] using hT.symm
    exact hstarNeg.ne (by exact_mod_cast hz)
  have hDneg : (D : ℚ) * (hstar : ℚ) < 0 :=
    mul_neg_of_pos_of_neg (by exact_mod_cast hD) (by exact_mod_cast hstarNeg)
  have hP : genusPoint dat ∈ eigenLattice (C⁄ℚ) dat.χ :=
    heegnerSum_mem_eigenLattice (C⁄ℚ) dat.quad.1 dat.y
  have hR' : sR ^ 2 = algebraMap ℚ H (D : ℚ) := by simpa only [map_intCast] using hR
  have hT' : sT ^ 2 = algebraMap ℚ H (hstar : ℚ) := by simpa only [map_intCast] using hT
  exact ⟨sR, hsR, hR', exact_twist_of_genus C h₁ h₃ dat.finrank_two
    hsR hR' hsT hT' hDneg (fun g => ⟨(hg g).2, (hg g).1⟩) htorT hpq hp hq L₀ hP⟩

end ZInQ.Manuscript.RC.Stages
