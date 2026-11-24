# Lean 4.35 port changes

This compares each selected source against its immutable upstream text after import relocation, excluding the added origin/change notice. Definitions and mathematical claims are preserved; coefficient notation is updated to the current API. The fixed H-67 definition and project pins are not modified.

Source revision: `6e837e75355538c7f80bab5b956861e86c4eacc2`.

## `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`

```diff
--- upstream/Definitions/Def_AlgebraicGeometry_OModulePresheafConstructions.lean
+++ ported/Definitions/Def_AlgebraicGeometry_OModulePresheafConstructions.lean
@@ -8,4 +8,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 noncomputable section
```

## `Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration`

```diff
--- upstream/Definitions/Def_AlgebraicGeometry_OModulePresheafIdealFiltration.lean
+++ ported/Definitions/Def_AlgebraicGeometry_OModulePresheafIdealFiltration.lean
@@ -5,4 +5,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option linter.unusedSectionVars false
 set_option linter.unusedVariables false
```

## `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`

```diff
--- upstream/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayBicomplex.lean
+++ ported/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayBicomplex.lean
@@ -4,4 +4,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 noncomputable section
```

## `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`

```diff
--- upstream/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex.lean
+++ ported/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex.lean
@@ -5,4 +5,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 noncomputable section
```

## `Definitions.Def_AlgebraicGeometry_ProjSpace`

```diff
--- upstream/Definitions/Def_AlgebraicGeometry_ProjSpace.lean
+++ ported/Definitions/Def_AlgebraicGeometry_ProjSpace.lean
@@ -6,4 +6,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option linter.unusedVariables false

@@ -362,10 +365,11 @@
     refine Finset.sum_eq_zero fun i _ => ?_
     rcases eq_or_ne i 0 with rfl | hi0
-    · rw [ha, coeff_zero]
+    · simp [ha]
     · exact ((mem_homogeneousSubmodule i _).mp
         (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) a i).2).coeff_eq_zero
         (by simpa [Finsupp.degree] using hi0.symm)
   obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr (Finsupp.support_eq_empty.not.mpr hd0)
-  obtain ⟨q, hq⟩ : (X j : MvPolynomial (Fin (n + 1)) A) ∣ monomial d (coeff d a) :=
+  -- Lean 4.35 port: coefficients use the polynomial-first API.
+  obtain ⟨q, hq⟩ : (X j : MvPolynomial (Fin (n + 1)) A) ∣ monomial d (a.coeff d) :=
     X_dvd_monomial.mpr (Or.inr (Finsupp.mem_support_iff.mp hj))
   rw [hq, show (X j : MvPolynomial (Fin (n + 1)) A)
```

## `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule`

```diff
--- upstream/Definitions/Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean
+++ ported/Definitions/Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean
@@ -3,4 +3,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 noncomputable section
@@ -547,5 +550,7 @@
     intro p' q' h'
     ext e
-    have := congrArg (MvPolynomial.coeff (e + ∑ j, Finsupp.single j (a j))) h'
+    -- Lean 4.35 port: the coefficient projection is polynomial-first.
+    have := congrArg (fun p : MvPolynomial (Fin (n + 1)) R =>
+      p.coeff (e + ∑ j, Finsupp.single j (a j))) h'
     simpa [MvPolynomial.coeff_monomial_mul'] using this
   exact hinj hpq
```

## `Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`

```diff
--- upstream/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCover.lean
+++ ported/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCover.lean
@@ -5,4 +5,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 noncomputable section
```

## `P2M.Sol.S_AlgebraicGeometry_ChowDatumProj_nonempty_of`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean
@@ -12,4 +12,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
@@ -247,5 +250,5 @@
             (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j))))))
       = pullback.fst _ _
-        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i)))) by rw [h]; rfl
+        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i)))) by rw [h] <;> rfl
   erw [← pullbackSpecIso_hom_fst_assoc R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
   rw [← Spec.map_comp, ← Spec.map_comp]
@@ -367,5 +370,5 @@
     chartIso_incL_assoc R n p kl.1 kl.2]
   erw [← prodCover_fst R n p ij, ← prodCover_fst R n p kl]
-  rw [← Category.assoc, pullback.condition, Category.assoc]; rfl
+  rw [← Category.assoc, pullback.condition, Category.assoc] <;> rfl

 theorem overlap_snd_condition (ij kl : Fin (n + 1) × Fin (p + 1)) :
@@ -385,5 +388,5 @@
     chartIso_incR_assoc R n p kl.1 kl.2]
   erw [← prodCover_snd R n p ij, ← prodCover_snd R n p kl]
-  rw [← Category.assoc, pullback.condition, Category.assoc]; rfl
+  rw [← Category.assoc, pullback.condition, Category.assoc] <;> rfl

 theorem chartMap_compat (ij kl : Fin (n + 1) × Fin (p + 1)) :
```

## `P2M.Sol.S_AlgebraicGeometry_ChowDatum_nonempty`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_ChowDatum_nonempty.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_ChowDatum_nonempty.lean
@@ -11,4 +11,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.lean
@@ -8,4 +8,7 @@
 set_option linter.unusedSectionVars false
 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.AlgebraicGeometry CategoryTheory"
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug.lean
@@ -5,4 +5,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 universe u
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.lean
@@ -14,4 +14,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.lean
@@ -4,4 +4,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 universe u
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow.lean
@@ -11,4 +11,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.lean
@@ -6,4 +6,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.lean
@@ -4,4 +4,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 universe u
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.lean
@@ -8,4 +8,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 universe u
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper.lean
@@ -14,4 +14,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 universe u
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff.lean
@@ -7,4 +7,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 universe u
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih.lean
@@ -9,4 +9,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 universe u
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.lean
@@ -7,4 +7,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
@@ -1055,5 +1058,6 @@
   simp only [OneMemClass.coe_one, one_mul, ProjSpaceCech.GradedModule.free_monMul_apply, mul_assoc]
   rw [← hprod]
-  exact congrArg (_ * ·) (mul_right_comm _ _ _)
+  -- Lean 4.35 port: the normalized goal also needs explicit reassociation.
+  exact congrArg (_ * ·) ((mul_right_comm _ _ _).trans (mul_assoc _ _ _))

 theorem quotSecEquiv_face {I I' : Finset (Fin (n + 1))}
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.lean
@@ -5,4 +5,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 universe u
```

## `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.lean
@@ -11,4 +11,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option linter.unusedSectionVars false

@@ -434,6 +437,5 @@
     coeffC I q K i j (z + z') = coeffC I q K i j z + coeffC I q K i j z' := by
   funext s
-  simp only [coeffC_apply, Pi.add_apply, F'_add_val, map_add, coeff_add]
-  rfl
+  simp only [coeffC_apply, Pi.add_apply, F'_add_val, map_add, coeff_add] <;> rfl

 lemma coeffC_zero (i j : ℕ) : coeffC I q K i j 0 = 0 := by
@@ -588,5 +590,7 @@
   funext s
   apply F'_ext I q
-  rw [F'val_d_zC, hdb, Pi.zero_apply, F'_zero_val]
+  rw [F'val_d_zC, hdb]
+  -- Lean 4.35 port: reduce both pointwise zeros before the section zero lemma.
+  simp only [Pi.zero_apply, F'_zero_val]
   change θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) (e_s I q K s)
     (monomial k (0 : Γ(P, K.inter s))) = 0
```

## `P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_map`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_ProjSpace_isPullback_map.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_ProjSpace_isPullback_map.lean
@@ -5,4 +5,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
@@ -126,5 +129,5 @@
   have := DFunLike.congr_fun h k.1
   simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm k.2), add_zero,
-    Finsupp.mapDomain_apply Subtype.val_injective] at this
+    Finsupp.mapDomain_apply_of_injective Subtype.val_injective] at this
   exact this

@@ -158,9 +161,9 @@

   have hterm : ∀ d ∈ p.support,
-      Localization.mk (coeff d p • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
+      Localization.mk (p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
           (⟨(X j)^(∑ k ∈ d.support, d k), _, rfl⟩
             : Submonoid.powers (X j : MvPolynomial _ S))
         * ι ((X j)^N)
-      = ι ((coeff d p • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
+      = ι ((p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial _ S) ^ d k)
           * (X j)^(N - ∑ k ∈ d.support, d k)) := by
     intro d hd
@@ -180,9 +183,9 @@

   have hform : ∀ d ∈ p.support,
-      (coeff d p • ∏ k ∈ d.support, (X k.1 : MvPolynomial (Fin (n+1)) S) ^ d k)
+      (p.coeff d • ∏ k ∈ d.support, (X k.1 : MvPolynomial (Fin (n+1)) S) ^ d k)
         * (X j)^(N - ∑ k ∈ d.support, d k)
       = (MvPolynomial.monomial
           (d.mapDomain Subtype.val + Finsupp.single j (N - ∑ k ∈ d.support, d k)))
-          (coeff d p) := by
+          (p.coeff d) := by
     intro d _
     rw [MvPolynomial.monomial_eq, Finsupp.prod_add_index (by simp)
@@ -198,13 +201,14 @@
   ext d₀
   by_cases hd₀ : d₀ ∈ p.support
-  · have hcoef := congrArg (coeff (d₀.mapDomain Subtype.val
-      + Finsupp.single j (N - ∑ k ∈ d₀.support, d₀ k))) hp'
+  · have hcoef := congrArg (fun q : MvPolynomial (Fin (n + 1)) S =>
+      q.coeff (d₀.mapDomain Subtype.val
+        + Finsupp.single j (N - ∑ k ∈ d₀.support, d₀ k))) hp'
     simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
-      MvPolynomial.coeff_zero] at hcoef
+      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoef
     rw [Finset.sum_congr rfl (fun d _ => if_congr
       ⟨fun h => exponent_inj n j N h, fun h => h ▸ rfl⟩ rfl rfl),
-      Finset.sum_ite_eq' p.support d₀ (fun d => coeff d p), if_pos hd₀] at hcoef
-    exact hcoef.trans (MvPolynomial.coeff_zero _).symm
-  · exact (MvPolynomial.notMem_support_iff.mp hd₀).trans (MvPolynomial.coeff_zero _).symm
+      Finset.sum_ite_eq' p.support d₀ (fun d => p.coeff d), if_pos hd₀] at hcoef
+    simpa using hcoef
+  · simpa using MvPolynomial.notMem_support_iff.mp hd₀

 def awayChartEquiv :
```

## `P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.lean
@@ -12,4 +12,7 @@
 set_option linter.unusedVariables false
 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"
```

## `P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.lean
@@ -5,4 +5,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry CategoryTheory TopologicalSpace AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry.Scheme"

```

## `P2M.Sol.S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.lean
@@ -10,4 +10,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option linter.unusedSectionVars false

@@ -519,6 +522,5 @@
       rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
       simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
-        OModulePresheaf.unit_res_apply, sub_eq_add_neg]
-      rfl
+        OModulePresheaf.unit_res_apply, sub_eq_add_neg] <;> rfl
     rw [hd]
     exact hmem
```

## `P2M.Sol.S_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing.lean
@@ -10,4 +10,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option linter.unusedSectionVars false

```

## `P2M.Sol.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.lean
@@ -12,4 +12,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
@@ -563,5 +566,8 @@
   haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
   refine IsLocalRing.of_unique_max_ideal ⟨𝔪, h𝔪, fun 𝔫 h𝔫 => ?_⟩
-  have h1 : (𝔫.comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
+  -- Lean 4.35 port: use the algebra-based contraction theorem.
+  have : 𝔫.IsMaximal := h𝔫
+  have h1 : (𝔫.comap (algebraMap R B)).IsMaximal :=
+    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) (S := B) 𝔫
   have h2 : 𝔫.comap (algebraMap R B) = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h1
   have h3 : 𝔪 ≤ 𝔫 := by
@@ -680,5 +686,7 @@
   haveI := preconnectedSpace_of_trivialIdem _ hk'
   have hmap : Spec.map (CommRingCat.ofHom ((algebraMap κ k).comp ψ)) = Spec.map (CommRingCat.ofHom φ) := by
-    rw [hφ]
+    -- Lean 4.35 port: expose the algebra induced by the actual residue-field map.
+    change Spec.map (CommRingCat.ofHom (ι.comp ψ)) = Spec.map (CommRingCat.ofHom φ)
+    exact congrArg (fun g : A →+* k => Spec.map (CommRingCat.ofHom g)) hφ.symm
   exact preconnectedSpace_of_iso (pullback.congrHom (rfl : πX = πX) hmap)

```

## `P2M.Sol.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.lean
@@ -10,4 +10,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option linter.unusedSectionVars false

```

## `P2M.Sol.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`

```diff
--- upstream/P2M/Sol/S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.lean
+++ ported/P2M/Sol/S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.lean
@@ -4,4 +4,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false

 open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
```

## `P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses`

```diff
--- upstream/P2M/Sol/S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.lean
+++ ported/P2M/Sol/S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.lean
@@ -7,4 +7,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
```

## `P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_ker_isFG`

```diff
--- upstream/P2M/Sol/S_ProjSpaceCech_GradedModule_Presentation_ker_isFG.lean
+++ ported/P2M/Sol/S_ProjSpaceCech_GradedModule_Presentation_ker_isFG.lean
@@ -6,4 +6,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
```

## `P2M.Sol.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD`

```diff
--- upstream/P2M/Sol/S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD.lean
+++ ported/P2M/Sol/S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD.lean
@@ -7,4 +7,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
@@ -129,5 +132,5 @@

 theorem GradedModule.coeff_Xprod (e : Fin (n + 1) → ℕ) (s : Fin (n + 1) →₀ ℕ) :
-    MvPolynomial.coeff s (GradedModule.Xprod (R := R) e)
+    (GradedModule.Xprod (R := R) e).coeff s
       = if s = ∑ j, Finsupp.single j (e j) then 1 else 0 := by
   unfold GradedModule.Xprod
@@ -234,6 +237,7 @@
           = 0 := by
     intro s
-    have hc := congrArg (MvPolynomial.coeff s) hpz
-    rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hc
+    -- Lean 4.35 port: coefficient evaluation is polynomial-first.
+    have hc := congrArg (fun p : MvPolynomial (Fin (n + 1)) R => p.coeff s) hpz
+    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, MvPolynomial.coeff_sum] at hc
     refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) hc
     rw [MvPolynomial.coeff_smul, GradedModule.coeff_Xprod, smul_eq_mul]
@@ -295,6 +299,5 @@
       refine Finset.sum_congr rfl fun e _ => ?_
       rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
-        MvPolynomial.C_mul']
-      rfl
+        MvPolynomial.C_mul'] <;> rfl
     rw [hmdecomp, map_sum]
     refine Submodule.sum_mem _ fun e _ => ?_
```

## `P2M.Sol.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi`

```diff
--- upstream/P2M/Sol/S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.lean
+++ ported/P2M/Sol/S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.lean
@@ -6,4 +6,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
```

## `P2M.Sol.S_ProjSpaceCech_Twist_finite_cohomology`

```diff
--- upstream/P2M/Sol/S_ProjSpaceCech_Twist_finite_cohomology.lean
+++ ported/P2M/Sol/S_ProjSpaceCech_Twist_finite_cohomology.lean
@@ -5,4 +5,7 @@

 set_option autoImplicit false
+-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
+set_option backward.isDefEq.respectTransparency false
+set_option backward.isDefEq.respectTransparency.types false
 set_option maxHeartbeats 6400000
 set_option synthInstance.maxHeartbeats 1600000
@@ -230,5 +233,5 @@
           = Twist.Mon.incl n d (Idx.img_face_subset n s j)
               ⟨a, hok.1, hface⟩ := rfl
-      rw [key, Finsupp.mapDomain_apply (Twist.Mon.incl_injective n d _)]
+      rw [key, Finsupp.mapDomain_apply_of_injective (Twist.Mon.incl_injective n d _)]
     · rw [Twist.coeff_of_not _ _ _ _ _ hface, smul_zero,
         Finsupp.mapDomain_notin_range, smul_zero]
@@ -719,5 +722,5 @@
   · have key : (⟨a, h1⟩ : Twist.Mon n d (Idx.img n t))
         = Twist.Mon.incl n d (Finset.empty_subset _) ⟨a, h2.1, h2.2.le⟩ := rfl
-    rw [key, Finsupp.mapDomain_apply (Twist.Mon.incl_injective n d _)]
+    rw [key, Finsupp.mapDomain_apply_of_injective (Twist.Mon.incl_injective n d _)]
   · rw [Finsupp.mapDomain_notin_range]
     rintro ⟨b, hb⟩
@@ -946,5 +949,5 @@
     · rw [if_neg (not_not.mpr hb), sub_eq_zero]
       have hkey : b = (Subtype.val : S → _) ⟨b, hb⟩ := rfl
-      rw [hkey, Finsupp.mapDomain_apply Subtype.val_injective, hg_def,
+      rw [hkey, Finsupp.mapDomain_apply_of_injective Subtype.val_injective, hg_def,
         Finsupp.comapDomain_apply]
     · rw [if_pos hb, Finsupp.mapDomain_notin_range, sub_zero]
```
