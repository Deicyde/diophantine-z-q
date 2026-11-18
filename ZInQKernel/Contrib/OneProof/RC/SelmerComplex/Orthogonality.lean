import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints

/-!
# Lane RC26: the zero condition is the orthogonal complement of the full condition

Nekovář, *Selmer complexes*, 6.2.7 (p. 140) via local duality 5.2.4 (p. 116): for the strict
condition `U_v = 0` on `M` and the relaxed (full) condition `U'_v = C^•_cont(G_v, M')` on `M'`,
the local duality map
`Cone(0 → ∏_v C(G_v, M))[−1] → Hom_R(∏_v C(G_v, M'), R)[−3]`
is the (shifted) product of the local duality maps `C(G_v, M) → Hom_R(C(G_v, M'), R)[−2]`, hence a
quasi-isomorphism as soon as every local duality map is one.

* `quasiIso_of_coneCx_acyclic`: a chain map with acyclic cone is a quasi-isomorphism (converse of
  `coneCx_acyclic_of_quasiIso`).
* `coneAdj_solve`: acyclicity of the cone of an adjoint map `adjHom P 2 tr`, in components and
  with free indices.
* `strictRelaxedIsotropyGen`, `strictRelaxedIsotropy`: zero isotropy homotopies for
  (strict, relaxed).
* `coneCx_localDualityMap_acyclic`, `quasiIso_localDualityMap_strict_relaxed`: the generic
  statement over arbitrary topological groups and finitely many places.
* `orthogonal_strict_relaxed`, `orthogonal_strict_relaxed_of_print`: the genuine Galois case.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

/-! ### Generic lemmas on cones -/

section ConeGeneric

variable {k : Type u} [CommRing k]

/-- **A chain map with acyclic cone is a quasi-isomorphism**: if `Cone(f)[−1]` is acyclic, then
`f : A → B` induces isomorphisms on all cohomology groups (compare the sequence
`B[−1] → Cone(f)[−1] → A` with the one for `id_B`, and apply the five lemma for the third term). -/
theorem quasiIso_of_coneCx_acyclic {A B : GCx k} (f : GHom A B) (hf : GAcyclic (coneCx f)) :
    QuasiIso (GHom.toCC f) := by
  have h1 : QuasiIso (coneSESHom f).τ₁ := by
    change QuasiIso (GHom.toCC (idGHom (shiftDown B)))
    rw [toCC_idGHom]
    infer_instance
  have h2 : QuasiIso (coneSESHom f).τ₂ :=
    quasiIso_of_acyclic _ ((acyclic_toCC_iff _).2 hf)
      ((acyclic_toCC_iff _).2 (coneCx_id_acyclic B))
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ (coneSESHom f) (coneSES_shortExact f)
    (coneSES_shortExact _) h1 h2

/-- **Acyclicity of the cone of an adjoint map, in components.** Let `P : A × B → T` be a pairing
and `tr : T² → k` a trace killing coboundaries such that the cone of the adjoint
`A → Hom_k(B, k)[−2]` is acyclic. If `e ∈ A^j` is a cycle and `z ∈ Hom(B^b, k)`
(`b = 3 − j`, `c = b − 1`) satisfies `tr(e ∪ y) = −(−1)^{j−1} z(dy)` for all `y ∈ B^c`, then there
are `e' ∈ A^{j−1}` and `z' ∈ Hom(B^{b+1}, k)` with `de' = e` and
`tr(e' ∪ y) + (−1)^{i−1} z'(dy) = z(y)` for all `y ∈ B^b`. -/
theorem coneAdj_solve {A B T : GCx k} (P : GPair A B T) (tr : T.X 2 →ₗ[k] k)
    (htr : ∀ z, tr (T.d (2 - 1) 2 (by omega) z) = 0) (hacyc : GAcyclic (coneCx (adjHom P 2 tr htr)))
    (i j l : ℤ) (hij : i + 1 = j) (hjl : j + 1 = l) (c b b' : ℤ) (hc : c + 1 = b) (hb : b + 1 = b')
    (hjc : j + c = 2) (e : A.X j) (z : Module.Dual k (B.X b)) (he : A.d j l hjl e = 0)
    (hz : ∀ y : B.X c, tr (P.P j c 2 hjc e y) = (-(sgn (j - 1))) • z (B.d c b hc y)) :
    ∃ (e' : A.X i) (z' : Module.Dual k (B.X b')), A.d i j hij e' = e ∧
      ∀ y : B.X b, tr (P.P i b 2 (by omega) e' y) - (-(sgn (i - 1))) • z' (B.d b b' hb y) = z y := by
  obtain rfl : b = 2 - (j - 1) := by omega
  obtain rfl : c = 2 - (l - 1) := by omega
  obtain rfl : b' = 2 - (i - 1) := by omega
  have h1 : (coneCx (adjHom P 2 tr htr)).d j l hjl ((e, z) : coneT (adjHom P 2 tr htr) j) = 0 := by
    refine Prod.ext he (dualCx_ext fun y => ?_)
    change tr (P.P j (2 - (l - 1)) 2 _ e y) -
      (-(sgn (j - 1))) • z (B.d (2 - (l - 1)) (2 - (j - 1)) _ y) = 0
    rw [hz y, sub_self]
  obtain ⟨⟨e', z'⟩, h⟩ := hacyc i j l hij hjl _ h1
  refine ⟨e', z', congrArg Prod.fst h, fun y => ?_⟩
  have h2 := congrArg (fun w : coneT (adjHom P 2 tr htr) j => asDual w.2 y) h
  exact h2

end ConeGeneric

/-! ### The generic setting: strict conditions against relaxed conditions -/

section StrictRelaxedGeneric

variable (k : Type u) [CommRing k] (GS : Type u) [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  {A B T : Type u}
  [AddCommGroup A] [Module k A] [DistribMulAction GS A] [SMulCommClass GS k A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul k A] [ContinuousSMul GS A]
  [AddCommGroup B] [Module k B] [DistribMulAction GS B] [SMulCommClass GS k B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul k B] [ContinuousSMul GS B]
  [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : A →ₗ[k] B →ₗ[k] T) (hβ : ∀ (g : GS) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : A × B => β x.1 x.2)

/-- The isotropy data of the pair (zero condition, full condition) in the generic setting: zero
homotopies (the local product `i u ∪ i' v` vanishes since `U = 0`). -/
def strictRelaxedIsotropyGen :
    IsotropyData k GS Gv loc β hβ hβc (strictConditions k GS Gv loc A)
      (relaxedConditions k GS Gv loc B) where
  h _ _ _ _ _ := 0
  isotropy v i i₁ j j₁ l l₁ hh hi hj hl x y := by
    have hx : ((strictConditions k GS Gv loc A).i v).f i i rfl x = 0 := rfl
    rw [hx, map_zero]
    simp

/-- **Evaluation of the local duality map for (zero condition, full condition)**: for
`(u, x) ∈ Cone(0 → ⊕_v C(G_v, A))[−1]` in degree `i` and `y ∈ ⊕_v C(G_v, B)` in degree `3 − j`
(`i = j`), the local duality map sends `(u, x)` to `y ↦ tr(0, x ∪ y)`. -/
theorem localDualityMap_strictRelaxed_apply
    (tr : (coneCx (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)).resE).d 2 3 rfl z) = 0)
    (i j : ℤ) (h : i = j) (u : (piCx fun _ : ι => zeroCx k).X i)
    (x : (localSumCx k GS Gv loc A).X (i - 1)) (y : (localSumCx k GS Gv loc B).X (3 - j)) :
    asDual ((localDualityMap (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)) tr htr).f i j h (u, x)) y =
      tr ((0 : (globalCx k GS T).X 3),
        (localSumPair k GS Gv loc β hβ hβc).P (i - 1) (3 - j) (3 - 1) (by omega) x y) := by
  subst h
  change tr (selCupFun (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)) i (3 - i) 3 _ (0, u, x) (0, y, 0)) = _
  congr 1
  refine Prod.ext ?_ ?_
  · change (globalPair k GS β hβ hβc).P i (3 - i) 3 _ 0 0 = 0
    simp
  · change (localSumPair k GS Gv loc β hβ hβc).P (i - 1) (3 - i) (3 - 1) _ x y +
      sgn i • (localSumPair k GS Gv loc β hβ hβc).P i (3 - i - 1) (3 - 1) _
        ((resS k GS Gv loc A).f i i rfl 0) 0 +
      (0 : (localSumCx k GS Gv loc T).X (3 - 1)) = _
    simp

/-- **The cone of the local duality map for (zero condition, full condition) is acyclic** when
the cones of all local duality maps `C(G_v, A) → Hom_k(C(G_v, B), k)[−2]` are acyclic, for finitely
many places and a global trace whose local part is the sum of the local traces,
`tr(0, z) = ∑_v tr_v(z_v)`. (A cycle of the cone splits into cycles of the local cones; their
primitives assemble into a primitive.) -/
theorem coneCx_localDualityMap_acyclic [Fintype ι]
    (trv : ∀ v, (localCx k GS Gv loc T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k GS Gv loc T v).d (2 - 1) 2 (by omega) z) = 0)
    (hv : ∀ v, GAcyclic (coneCx (adjHom (localPair k GS Gv loc β hβ hβc v) 2 (trv v) (htrv v))))
    (tr : (coneCx (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)).resE).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k GS Gv loc T).X (3 - 1),
      tr ((0 : (globalCx k GS T).X 3), z) = ∑ v, trv v (z v)) :
    GAcyclic (coneCx (localDualityMap (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)) tr htr)) := by
  classical
  intro I J L hIJ hJL c hc
  obtain ⟨⟨u, x⟩, φ⟩ := c
  -- the cycle conditions
  have hx : ∀ v, (localCx k GS Gv loc A v).d (J - 1) (L - 1) (by omega) (x v) = 0 := by
    intro v
    have h1 := congrArg (fun w : coneT (localDualityMap (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)) tr htr) L => w.1.2 v) hc
    change -(0 : (localCx k GS Gv loc A v).X (L - 1)) -
      (localCx k GS Gv loc A v).d (J - 1) (L - 1) _ (x v) = 0 at h1
    rw [neg_zero, zero_sub, neg_eq_zero] at h1
    exact h1
  have hφ : ∀ y : (localSumCx k GS Gv loc B).X (3 - (L - 1)),
      tr ((0 : (globalCx k GS T).X 3),
        (localSumPair k GS Gv loc β hβ hβc).P (J - 1) (3 - (L - 1)) (3 - 1) (by omega) x y) =
      (-(sgn (J - 1))) • asDual φ
        ((localSumCx k GS Gv loc B).d (3 - (L - 1)) (3 - (J - 1)) (by omega) y) := by
    intro y
    have h2 := congrArg (fun w : coneT (localDualityMap (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)) tr htr) L => asDual w.2 y) hc
    change asDual ((localDualityMap (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)) tr htr).f J (L - 1) _ (u, x)) y -
      (-(sgn (J - 1))) • asDual φ
        ((localSumCx k GS Gv loc B).d (3 - (L - 1)) (3 - (J - 1)) _ y) = 0 at h2
    erw [localDualityMap_strictRelaxed_apply] at h2
    rw [sub_eq_zero] at h2
    exact h2
  -- solve at every place
  have key : ∀ v, ∃ (e' : (localCx k GS Gv loc A v).X (I - 1))
      (z' : Module.Dual k ((localCx k GS Gv loc B v).X (3 - (I - 1)))),
      (localCx k GS Gv loc A v).d (I - 1) (J - 1) (by omega) e' = x v ∧
      ∀ y : (localCx k GS Gv loc B v).X (3 - (J - 1)),
        trv v ((localPair k GS Gv loc β hβ hβc v).P (I - 1) (3 - (J - 1)) 2 (by omega) e' y) -
          (-(sgn (I - 1 - 1))) •
            z' ((localCx k GS Gv loc B v).d (3 - (J - 1)) (3 - (I - 1)) (by omega) y) =
        -(asDual φ (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u))
          v y)) := by
    intro v
    refine coneAdj_solve (localPair k GS Gv loc β hβ hβc v) (trv v) (htrv v) (hv v) (I - 1) (J - 1)
      (L - 1) (by omega) (by omega) (3 - (L - 1)) (3 - (J - 1)) (3 - (I - 1)) (by omega)
      (by omega) (by omega) (x v)
      (-((asDual φ).comp (LinearMap.single k
        (fun w => ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u)) v))) (hx v) (fun y => ?_)
    have h3 := hφ (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (L - 1)) : Type u))
      v y)
    rw [hsum] at h3
    have hL : ∑ w, trv w ((localSumPair k GS Gv loc β hβ hβc).P (J - 1) (3 - (L - 1)) (3 - 1)
        (by omega) x (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (L - 1)) : Type u))
          v y) w) =
        trv v ((localPair k GS Gv loc β hβ hβc v).P (J - 1) (3 - (L - 1)) 2 (by omega) (x v) y) := by
      rw [Finset.sum_eq_single v]
      · change trv v ((localPair k GS Gv loc β hβ hβc v).P (J - 1) (3 - (L - 1)) (3 - 1) _ (x v)
          (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (L - 1)) : Type u)) v y v)) = _
        rw [Pi.single_eq_same]
        rfl
      · intro w _ hw
        change trv w ((localPair k GS Gv loc β hβ hβc w).P (J - 1) (3 - (L - 1)) (3 - 1) _ (x w)
          (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (L - 1)) : Type u)) v y w)) = 0
        rw [Pi.single_eq_of_ne hw, map_zero, map_zero]
      · intro h
        exact absurd (Finset.mem_univ v) h
    have hR : ((localSumCx k GS Gv loc B).d (3 - (L - 1)) (3 - (J - 1)) (by omega)
        (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (L - 1)) : Type u)) v y)) =
        Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u)) v
          ((localCx k GS Gv loc B v).d (3 - (L - 1)) (3 - (J - 1)) (by omega) y) := by
      refine funext fun w => ?_
      change (localCx k GS Gv loc B w).d (3 - (L - 1)) (3 - (J - 1)) _
        (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (L - 1)) : Type u)) v y w) = _
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hw, Pi.single_eq_of_ne hw, map_zero]
    rw [hL, hR] at h3
    rw [h3]
    change _ = (-(sgn (J - 1 - 1))) • -(asDual φ
      (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u)) v
        ((localCx k GS Gv loc B v).d (3 - (L - 1)) (3 - (J - 1)) _ y)))
    rw [sgn_pred (J - 1)]
    simp only [smul_neg, neg_smul, neg_neg]
  choose e' z' he' hz' using key
  -- assemble the primitive
  let x' : (localSumCx k GS Gv loc A).X (I - 1) := fun v => -e' v
  let φ' : Module.Dual k ((localSumCx k GS Gv loc B).X (3 - (I - 1))) :=
    ∑ v, (z' v).comp (LinearMap.proj (R := k)
      (φ := fun w => ((localCx k GS Gv loc B w).X (3 - (I - 1)) : Type u)) v)
  refine ⟨(((0 : (piCx fun _ : ι => zeroCx k).X I), x'), φ'), ?_⟩
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · refine funext fun v => ?_
    change -(0 : (localCx k GS Gv loc A v).X (J - 1)) -
      (localCx k GS Gv loc A v).d (I - 1) (J - 1) _ (-e' v) = x v
    rw [map_neg, he' v, neg_zero, zero_sub, neg_neg]
  · refine dualCx_ext fun y => ?_
    change asDual ((localDualityMap (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)) tr htr).f I (J - 1) _ (0, x')) y -
      (-(sgn (I - 1))) • φ'
        ((localSumCx k GS Gv loc B).d (3 - (J - 1)) (3 - (I - 1)) _ y) = asDual φ y
    erw [localDualityMap_strictRelaxed_apply]
    rw [hsum]
    have hy : asDual φ y = ∑ w, asDual φ
        (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u)) w (y w)) := by
      have e : (y : ∀ w, ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u)) =
          ∑ w, Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u))
            w (y w) :=
        (Finset.univ_sum_single (fun w => (y w : (localCx k GS Gv loc B w).X (3 - (J - 1))))).symm
      calc asDual φ y = asDual φ (∑ w, Pi.single
            (M := fun w => ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u)) w (y w)) :=
            congrArg _ e
        _ = _ := map_sum (asDual φ) _ _
    have hφ' : φ' ((localSumCx k GS Gv loc B).d (3 - (J - 1)) (3 - (I - 1)) (by omega) y) =
        ∑ w, z' w ((localCx k GS Gv loc B w).d (3 - (J - 1)) (3 - (I - 1)) (by omega) (y w)) := by
      show (∑ v, (z' v).comp (LinearMap.proj (R := k)
        (φ := fun w => ((localCx k GS Gv loc B w).X (3 - (I - 1)) : Type u)) v)) _ = _
      exact LinearMap.sum_apply Finset.univ (fun v => (z' v).comp (LinearMap.proj (R := k)
        (φ := fun w => ((localCx k GS Gv loc B w).X (3 - (I - 1)) : Type u)) v)) _
    rw [hy, hφ', Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h4 : trv w ((localPair k GS Gv loc β hβ hβc w).P (I - 1) (3 - (J - 1)) (3 - 1)
        (by omega) (e' w) (y w)) - (-(sgn (I - 1 - 1))) •
          z' w ((localCx k GS Gv loc B w).d (3 - (J - 1)) (3 - (I - 1)) (by omega) (y w)) =
        -(asDual φ (Pi.single (M := fun w => ((localCx k GS Gv loc B w).X (3 - (J - 1)) : Type u))
          w (y w))) := hz' w (y w)
    rw [sgn_pred (I - 1)] at h4
    change trv w ((localPair k GS Gv loc β hβ hβc w).P (I - 1) (3 - (J - 1)) (3 - 1) _ (-e' w)
      (y w)) - _ = _
    have h5 : trv w ((localPair k GS Gv loc β hβ hβc w).P (I - 1) (3 - (J - 1)) (3 - 1) (by omega)
        (-e' w) (y w)) =
        -trv w ((localPair k GS Gv loc β hβ hβc w).P (I - 1) (3 - (J - 1)) (3 - 1) (by omega)
          (e' w) (y w)) :=
      (congrArg (trv w) (LinearMap.map_neg₂ _ _ _)).trans (map_neg (trv w) _)
    rw [h5]
    rw [neg_neg] at h4
    simp only [zsmul_eq_mul, Int.cast_neg] at h4 ⊢
    linear_combination (-1 : k) * h4

/-- **Generic orthogonality of the zero and the full condition** (Nekovář 6.2.7 from local
duality): for finitely many places, if at every place the local duality map
`C(G_v, A) → Hom_k(C(G_v, B), k)[−2]`, `a ↦ (b ↦ tr_v(a ∪ b))`, is a quasi-isomorphism and the
global trace restricts on the local part to `∑_v tr_v`, then the local duality map
`Cone(0 → ⊕_v C(G_v, A))[−1] → Hom_k(⊕_v C(G_v, B), k)[−3]` of the pair
(zero condition on `A`, full condition on `B`) is a quasi-isomorphism. -/
theorem quasiIso_localDualityMap_strict_relaxed [Fintype ι]
    (trv : ∀ v, (localCx k GS Gv loc T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k GS Gv loc T v).d (2 - 1) 2 (by omega) z) = 0)
    (hqi : ∀ v, QuasiIso (GHom.toCC
      (adjHom (localPair k GS Gv loc β hβ hβc v) 2 (trv v) (htrv v))))
    (tr : (coneCx (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)).resE).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((coneCx (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)).resE).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k GS Gv loc T).X (3 - 1),
      tr ((0 : (globalCx k GS T).X 3), z) = ∑ v, trv v (z v)) :
    QuasiIso (GHom.toCC (localDualityMap (genuinePairData k GS Gv loc β hβ hβc _ _
      (strictRelaxedIsotropyGen k GS Gv loc β hβ hβc)) tr htr)) :=
  quasiIso_of_coneCx_acyclic _ (coneCx_localDualityMap_acyclic k GS Gv loc β hβ hβc trv htrv
    (fun v => coneCx_acyclic_of_quasiIso _ (hqi v)) tr htr hsum)

end StrictRelaxedGeneric

/-! ### The genuine Galois data -/

section Galois

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type}
  [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- The isotropy data of the pair (zero condition on `M`, full condition on `M'`) for the genuine
Galois data: zero homotopies (the local product `i u ∪ i' v` vanishes since `U = 0`). -/
def strictRelaxedIsotropy :
    GaloisIsotropyData K S R β hβ (strictConditions R _ _ _ M) (relaxedConditions R _ _ _ M') :=
  strictRelaxedIsotropyGen R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β hβ (continuous_pairing β)

/-- **The zero condition is the orthogonal complement of the full condition** (Nekovář 6.2.7,
p. 140, via local duality 5.2.4; tex 2813–2816: "A full condition is paired with the zero
condition"): for finitely many places, local traces `tr_v` on `C²_cont(G_{K_v}, T)` killing
coboundaries such that every local duality map
`C^•_cont(G_{K_v}, M) → Hom_R(C^•_cont(G_{K_v}, M'), R)[−2]` is a quasi-isomorphism, and a global
trace on `C³_c(G_{K,S}, T)` whose local part is `∑_v tr_v`, the zero condition on `M` and the full
condition on `M'` are orthogonal complements. -/
theorem orthogonal_strict_relaxed [Fintype (Places K S)]
    (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0)
    (hqi : ∀ v, QuasiIso (GHom.toCC (adjHom (localPair R (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ (continuous_pairing β) v)
        2 (trv v) (htrv v))))
    (tr : (galoisCompactT K S R β hβ _ _ (strictRelaxedIsotropy K β hβ)).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactT K S R β hβ _ _ (strictRelaxedIsotropy K β hβ)).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3), z) = ∑ v, trv v (z v)) :
    OrthogonalComplements K β hβ _ _ (strictRelaxedIsotropy K β hβ) tr htr :=
  quasiIso_localDualityMap_strict_relaxed R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β hβ (continuous_pairing β) trv htrv hqi tr htr hsum

/-- **Orthogonality of the zero and the full condition from the local duality PRINT**
(`NekovarProp524`, Nekovář 5.2.4): under the finite standing hypotheses, for finite discrete
modules with a perfect equivariant pairing `β : M × M' → T`, `T ≅ R(1)`, local traces killing
coboundaries and inducing `H²(G_{K_v}, T) ≅ R`, and a global trace whose local part is
`∑_v tr_v`, the zero condition on `M` and the full condition on `M'` are orthogonal complements
(Nekovář 6.2.7). -/
theorem orthogonal_strict_relaxed_of_print (h : NekovarProp524 K) (p : ℕ) [IsLocalRing R]
    (hset : NekovarFiniteSetting K S p R) [Finite M] [Finite M'] (hb : Function.Bijective β)
    (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S R T) [Fintype (Places K S)]
    (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R)
    (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0)
    (htrv2 : ∀ v, InducesIsoH2 (trv v))
    (tr : (galoisCompactT K S R β hβ _ _ (strictRelaxedIsotropy K β hβ)).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactT K S R β hβ _ _ (strictRelaxedIsotropy K β hβ)).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3), z) = ∑ v, trv v (z v)) :
    OrthogonalComplements K β hβ _ _ (strictRelaxedIsotropy K β hβ) tr htr :=
  orthogonal_strict_relaxed K β hβ trv htrv
    (fun v => h S p R hset M M' T β hβ hb hb' hT v (trv v) (htrv v) (htrv2 v)) tr htr hsum

end Galois

end ZInQ.Manuscript.RC.SelmerComplex
