import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.KerRing

/-! faltings5-lower, part 13: **in characteristic `0`, a tangent vector at the origin killed by a finite
homomorphism is trivial** (the kernel `G` is a finite group scheme; its tangent vectors vanish).

Proof (Cartier's argument on the Artinian ring `R = Γ(G)`): a tangent vector `v` of `G` is a ring map
`ρ = e + εD : R → K[ε]`. Multiplying the universal point `u ∈ G(R)` by `v` gives `w = u·v ∈ G(R[ε])`, i.e. a ring
map `ψ = id + εD̃ : R → R[ε]`; `D̃` is a derivation of `R` and `e ∘ D̃ = D` (specialize `w` along `e`). If `x ∈ ker e`,
`R` Artinian gives `t x^N = 0` with `e(t) ≠ 0`, and applying `D̃` to `t x^{n+1} = 0` gives
`t² (n+1) D̃(x) x^n = 0` with `e(t² (n+1) D̃ x) = e(t)² (n+1) D(x)`; descending to `n = 0`, `D(x) = 0`. -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Contrib.AbVarBC.Tangent TrivSqZeroExt

section Tsze

/-- `S[ε] → T[ε]` along a ring map `f : S → T`. -/
def liftTsze {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) :
    TrivSqZeroExt S S →+* TrivSqZeroExt T T where
  toFun x := inl (f x.fst) + inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [snd_mul]
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext
    · simp
    · simp only [snd_add, snd_inl, snd_inr, zero_add, map_add]

@[simp] theorem algebraMap_tsze (K : Type) [Field K] (c : K) :
    algebraMap K (TrivSqZeroExt K K) c = inl c := rfl

@[simp] theorem fstHom_apply' {S : Type} [CommRing S] (x : TrivSqZeroExt S S) :
    ((fstHom S S S : TrivSqZeroExt S S →ₐ[S] S) : TrivSqZeroExt S S →+* S) x = x.fst := rfl

@[simp] theorem inlHom_apply' {S : Type} [CommRing S] (r : S) : inlHom S S r = inl r := rfl

@[simp] theorem liftTsze_fst {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
    (x : TrivSqZeroExt S S) : (liftTsze f x).fst = f x.fst := by simp [liftTsze]

@[simp] theorem liftTsze_snd {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
    (x : TrivSqZeroExt S S) : (liftTsze f x).snd = f x.snd := by simp [liftTsze]

end Tsze

section Tan

variable {K : Type} [Field K] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) [IsMonHom φ] [IsFinite φ.left]

theorem ringOf_congr {Λ : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ} {P Q : pt' s ⟶ A.X}
    (hP : P ≫ φ = 1) (hQ : Q ≫ φ = 1) (h : P = Q) : ringOf φ P hP = ringOf φ Q hQ := by
  subst h; rfl

theorem sh'_congr {Λ Λ' : CommRingCat.{0}} {s : CommRingCat.of K ⟶ Λ}
    {s' : CommRingCat.of K ⟶ Λ'} {σ σ' : Λ ⟶ Λ'} (h : s ≫ σ = s') (h' : s ≫ σ' = s')
    (e : σ = σ') : sh' σ h = sh' σ' h' := by
  subst e; rfl

/-- `s₀ : K → K` (the base of `ptR K`). -/
noncomputable abbrev s0 (K : Type) [Field K] : CommRingCat.of K ⟶ CommRingCat.of K :=
  CommRingCat.ofHom (algebraMap K K)

theorem s0_comp {Λ : CommRingCat.{0}} (s : CommRingCat.of K ⟶ Λ) : s0 K ≫ s = s := by
  ext x; rfl

/-- The ring map of the trivial point (evaluation at the origin of the kernel). -/
noncomputable def eK : Γ(kerSch φ, ⊤) ⟶ CommRingCat.of K :=
  ringOf φ (1 : pt' (s0 K) ⟶ A.X) (MonObj.one_comp φ)

theorem kerAlg_eK : kerAlg φ ≫ eK φ = s0 K := ringOf_cond φ _ _

theorem eK_kerAlg (c : K) : (eK φ).hom ((kerAlg φ).hom c) = c := by
  have := congrArg (fun g => g.hom c) (kerAlg_eK φ)
  exact this

/-- The trivial point over any `Λ` has ring map `e ≫ s`. -/
theorem ringOf_one {Λ : CommRingCat.{0}} (s : CommRingCat.of K ⟶ Λ) (h1 : (1 : pt' s ⟶ A.X) ≫ φ = 1) :
    ringOf φ (1 : pt' s ⟶ A.X) h1 = eK φ ≫ s := by
  have e1 : (1 : pt' s ⟶ A.X) = sh' s (s0_comp s) ≫ (1 : pt' (s0 K) ⟶ A.X) :=
    (MonObj.comp_one _).symm
  rw [ringOf_congr φ h1 (by rw [Category.assoc, MonObj.one_comp, MonObj.comp_one]) e1,
    ringOf_sh' φ s (s0_comp s) 1 (MonObj.one_comp φ)]
  rfl

/-- **Tangent vectors of the kernel of a finite homomorphism are trivial** (characteristic `0`). -/
theorem tangent_trivial [CharZero K] (v : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X)
    (hv : AtOrigin A v) (hvφ : v ≫ φ = 1) : v = 1 := by
  -- notation
  set R := Γ(kerSch φ, ⊤)
  set j := kerAlg φ
  set e := eK φ
  let Kε := CommRingCat.of (TrivSqZeroExt K K)
  let sε : CommRingCat.of K ⟶ Kε := CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K K))
  let v0 : pt' sε ⟶ A.X := v
  have hv0 : v0 ≫ φ = 1 := hvφ
  set ρv := ringOf φ v0 hv0
  have hρvc : j ≫ ρv = sε := ringOf_cond φ v0 hv0
  -- the fst condition: `ρv ≫ fst = e`
  let σf : Kε ⟶ CommRingCat.of K :=
    CommRingCat.ofHom ((fstHom K K K : TrivSqZeroExt K K →ₐ[K] K) : TrivSqZeroExt K K →+* K)
  have hσf : sε ≫ σf = s0 K := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    rfl
  have hfst_pt : sh' σf hσf ≫ v0 = 1 := by
    have : sh' σf hσf = specHom (fstHom K K K) := Over.OverMorphism.ext rfl
    rw [this]; exact hv
  have hρf : ρv ≫ σf = e := by
    rw [← ringOf_sh' φ σf hσf v0 hv0 (by rw [hfst_pt, MonObj.one_comp])]
    rw [ringOf_congr φ _ (MonObj.one_comp φ) hfst_pt]
    rfl
  have hρfst : ∀ r, (ρv.hom r).fst = e.hom r := fun r => congrArg (fun g => g.hom r) hρf
  -- the derivation `D`
  let D : R → K := fun r => (ρv.hom r).snd
  have hDj : ∀ c, D (j.hom c) = 0 := by
    intro c
    have := congrArg (fun g => (g.hom c).snd) hρvc
    exact this.trans rfl
  -- `R[ε]` and the maps
  let Rε := CommRingCat.of (TrivSqZeroExt R R)
  let iR : R ⟶ Rε := CommRingCat.ofHom (inlHom R R)
  let sR : CommRingCat.of K ⟶ Rε := j ≫ iR
  let jr : K →+* R := j.hom
  let er : R →+* K := e.hom
  have herjr : ∀ c, er (jr c) = c := eK_kerAlg φ
  let iε : Kε ⟶ Rε := CommRingCat.ofHom (liftTsze jr)
  have hiε : sε ≫ iε = sR := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    show liftTsze jr (inl c) = inl (jr c)
    ext <;> simp
  let fR : Rε ⟶ R := CommRingCat.ofHom ((fstHom R R R : TrivSqZeroExt R R →ₐ[R] R) :
    TrivSqZeroExt R R →+* R)
  let eε : Rε ⟶ Kε := CommRingCat.ofHom (liftTsze er)
  -- the universal point and `w = u' * v'`
  let u : pt' j ⟶ A.X := ptOf φ (𝟙 R) (Category.comp_id j)
  have hu : u ≫ φ = 1 := ptOf_ker φ _ _
  let u' : pt' sR ⟶ A.X := sh' iR rfl ≫ u
  let v' : pt' sR ⟶ A.X := sh' iε hiε ≫ v0
  have hu' : u' ≫ φ = 1 := by
    show (sh' iR rfl ≫ u) ≫ φ = 1
    rw [Category.assoc, hu, MonObj.comp_one]
  have hv' : v' ≫ φ = 1 := by
    show (sh' iε hiε ≫ v0) ≫ φ = 1
    rw [Category.assoc, hv0, MonObj.comp_one]
  let w : pt' sR ⟶ A.X := u' * v'
  have hw : w ≫ φ = 1 := by
    show (u' * v') ≫ φ = 1
    rw [MonObj.mul_comp, hu', hv', _root_.mul_one]
  set ψ := ringOf φ w hw
  -- (i) `ψ ≫ fst = 𝟙`
  have hfR : sR ≫ fR = j := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    rfl
  have hi : sh' fR hfR ≫ w = u := by
    show sh' fR hfR ≫ (u' * v') = u
    rw [MonObj.comp_mul]
    have h1 : sh' fR hfR ≫ u' = u := by
      show sh' fR hfR ≫ sh' iR rfl ≫ u = u
      rw [← Category.assoc, sh'_comp, sh'_congr _ (Category.comp_id j)
        (show iR ≫ fR = 𝟙 R from CommRingCat.hom_ext (RingHom.ext fun r => rfl)), sh'_id,
        Category.id_comp]
    have h2 : sh' fR hfR ≫ v' = 1 := by
      show sh' fR hfR ≫ sh' iε hiε ≫ v0 = 1
      have hsplit : iε ≫ fR = σf ≫ j := by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        show (liftTsze jr x).fst = jr x.fst
        simp
      rw [← Category.assoc, sh'_comp, sh'_congr _ (by rw [← Category.assoc, hσf, s0_comp]) hsplit,
        ← sh'_comp σf j hσf (s0_comp j), Category.assoc, hfst_pt, MonObj.comp_one]
    rw [h1, h2, _root_.mul_one]
  have hψf : ψ ≫ fR = 𝟙 R := by
    rw [← ringOf_sh' φ fR hfR w hw (by rw [hi]; exact hu),
      ringOf_congr φ _ hu hi, ringOf_ptOf]
  have hψfst : ∀ r, (ψ.hom r).fst = r := fun r => congrArg (fun g => g.hom r) hψf
  -- (ii) `ψ ≫ eε = ρv`
  have heR : sR ≫ eε = sε := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    show liftTsze er (inl (jr c)) = inl c
    ext
    · simp [herjr]
    · simp
  have hii : sh' eε heR ≫ w = v0 := by
    show sh' eε heR ≫ (u' * v') = v0
    rw [MonObj.comp_mul]
    have h1 : sh' eε heR ≫ u' = 1 := by
      show sh' eε heR ≫ sh' iR rfl ≫ u = 1
      rw [← Category.assoc, sh'_comp]
      apply ringOf_injective φ (by rw [Category.assoc, hu, MonObj.comp_one]) (MonObj.one_comp φ)
      rw [ringOf_sh' φ _ _ u hu, ringOf_one]
      show ringOf φ (ptOf φ (𝟙 R) (Category.comp_id j)) hu ≫ (iR ≫ eε) = e ≫ sε
      rw [ringOf_ptOf, Category.id_comp]
      refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
      show liftTsze er (inl r) = inl (er r)
      ext <;> simp
    have h2 : sh' eε heR ≫ v' = v0 := by
      show sh' eε heR ≫ sh' iε hiε ≫ v0 = v0
      rw [← Category.assoc, sh'_comp, sh'_congr _ (Category.comp_id sε) (by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        show liftTsze er (liftTsze jr x) = x
        ext <;> simp [herjr]), sh'_id, Category.id_comp]
    rw [h1, h2, _root_.one_mul]
  have hψe : ψ ≫ eε = ρv := by
    rw [← ringOf_sh' φ eε heR w hw (by rw [hii]; exact hv0), ringOf_congr φ _ hv0 hii]
  -- the derivation `D̃` of `R`
  let Dt : R → R := fun r => (ψ.hom r).snd
  have hDt_mul : ∀ a b, Dt (a * b) = a * Dt b + b * Dt a := by
    intro a b
    show (ψ.hom (a * b)).snd = _
    rw [map_mul, snd_mul, hψfst, hψfst, smul_eq_mul, op_smul_eq_mul]
    ring
  have hDt_add : ∀ a b, Dt (a + b) = Dt a + Dt b := by
    intro a b
    show (ψ.hom (a + b)).snd = _
    rw [map_add, snd_add]
  have hDt0 : Dt 0 = 0 := by show (ψ.hom 0).snd = 0; rw [map_zero, snd_zero]
  have heDt : ∀ r, e.hom (Dt r) = D r := by
    intro r
    have := congrArg (fun g => (g.hom r).snd) hψe
    have h2 : (liftTsze er (ψ.hom r)).snd = er (ψ.hom r).snd := liftTsze_snd er _
    exact h2.symm.trans this
  have hDt_pow : ∀ (x : R) (n : ℕ), Dt (x ^ (n + 1)) = ((n + 1 : ℕ) : R) * x ^ n * Dt x := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hDt_mul, ih]
      push_cast
      ring
  -- `D` vanishes on `ker e`
  letI : Algebra K R := j.hom.toAlgebra
  haveI : Module.Finite K R := kerAlg_finite φ
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  have hDker : ∀ x : R, e.hom x = 0 → D x = 0 := by
    intro x hx
    by_contra hD
    obtain ⟨N, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R)
    simp only [smul_eq_mul, _root_.mul_one] at hy
    -- `t x^N = 0` with `e t ≠ 0`
    have hP : ∀ n : ℕ, ∃ t : R, e.hom t ≠ 0 ∧ t * x ^ (N - n) = 0 := by
      intro n
      induction n with
      | zero =>
        refine ⟨1 - x * y, ?_, ?_⟩
        · rw [map_sub, map_mul, hx, map_one]; simp
        · rw [Nat.sub_zero, show (1 - x * y) * x ^ N = x ^ N - x ^ (N + 1) * y by ring, hy, sub_self]
      | succ n ih =>
        obtain ⟨t, ht, htx⟩ := ih
        by_cases hn : n < N
        · obtain ⟨m, hm⟩ : ∃ m, N - n = m + 1 := ⟨N - n - 1, by omega⟩
          have hm' : N - (n + 1) = m := by omega
          rw [hm] at htx
          refine ⟨t * t * ((m + 1 : ℕ) : R) * Dt x, ?_, ?_⟩
          · rw [map_mul, map_mul, map_mul, map_natCast, heDt]
            refine mul_ne_zero (mul_ne_zero (mul_ne_zero ht ht) ?_) hD
            exact_mod_cast Nat.succ_ne_zero m
          · rw [hm']
            have h1 := congrArg Dt htx
            rw [hDt_mul, hDt0, hDt_pow] at h1
            have h2 : t * (t * (((m + 1 : ℕ) : R) * x ^ m * Dt x) + x ^ (m + 1) * Dt t) = 0 := by
              rw [h1, mul_zero]
            have h3 : t * (x ^ (m + 1) * Dt t) = 0 := by
              rw [← _root_.mul_assoc, htx, zero_mul]
            linear_combination h2 - h3
        · refine ⟨t, ht, ?_⟩
          have : N - (n + 1) = N - n := by omega
          rw [this]; exact htx
    obtain ⟨t, ht, htx⟩ := hP N
    rw [Nat.sub_self, pow_zero, _root_.mul_one] at htx
    rw [htx, map_zero] at ht
    exact ht rfl
  -- hence `D = 0`
  have hD0 : ∀ r, D r = 0 := by
    intro r
    have h1 : e.hom (r - j.hom (e.hom r)) = 0 := by
      rw [map_sub, eK_kerAlg, sub_self]
    have h2 := hDker _ h1
    have hDadd : D (r - j.hom (e.hom r)) = D r - D (j.hom (e.hom r)) := by
      show (ρv.hom _).snd = (ρv.hom _).snd - (ρv.hom _).snd
      rw [map_sub, snd_sub]
    rw [hDadd, hDj, sub_zero] at h2
    exact h2
  -- so `ρv` is the ring map of the trivial point, and `v = 1`
  have hρ1 : ρv = e ≫ sε := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show ρv.hom r = inl (er r)
    ext
    · exact hρfst r
    · exact hD0 r
  have := ringOf_injective φ hv0 (MonObj.one_comp φ) (hρ1.trans (ringOf_one φ sε _).symm)
  exact this

end Tan

end GapHeight
