  -- the kernel-field clause (lg-kerwild)
  intro g hgL hg1
  have hgL' : g ∈ GQL L := mem_GQL.mpr (fun x hx => hgL x hx)
  have hnormL : (L.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hcjL : cj g ∈ GQL L := hnormL.conj_mem _ hgL' h
  have haone : a (cj g) = 1 := (haL 1 (cj g) hcjL).1
  have hβC : (β (cj g) : ℂ) = 1 := by
    rw [hgamK (cj g) hg1, haone, Complex.ofReal_one]
  have hβ1 : β (cj g) = 1 := Units.ext (by rw [hβC, Units.val_one])
  have hcjL' : cj g ∈ GQL L' := (hL' (cj g)).mpr ⟨hcjL, hβ1⟩
  have hgL'' : g ∈ L'.fixingSubgroup := by
    have h4 : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ ∈ L'.fixingSubgroup := hnorm.conj_mem _ hcjL' h⁻¹
    have e : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g := by group
    rwa [e] at h4
  rw [RQ.resQ_range L']
  exact hgL''
