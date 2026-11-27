/-
Y3ProjFiniteSets

1. Graded prime avoidance (Stacks, Algebra, Lemma 10.57.6, tag 00JS).
   Let `𝒜 : ℕ → σ` be a grading of the commutative ring `A`, let `I` be a homogeneous
   ideal contained in the irrelevant ideal, and let `s` be a finite set of homogeneous
   prime ideals, none of which contains `I`. Then `I` contains a homogeneous element of
   positive degree lying in none of the primes of `s`.
   The statement below does not assume `s` nonempty: for `s = ∅` the element `0`, viewed
   in degree `1`, is a valid witness. This removes the base case from the induction.

2. Every finite set of points of `Proj 𝒜` is contained in an affine open subscheme,
   namely a basic open `D₊(f)` with `f` homogeneous of positive degree.

Proof of 1, by induction on `s.card`. Choose `p₀ ∈ s` minimal for inclusion and put
`t = s.erase p₀`. By induction there is a homogeneous `y ∈ I` of degree `d > 0`
avoiding every prime of `t`. If `y ∉ p₀` we are done. Otherwise, by minimality no
`q ∈ t` satisfies `q ≤ p₀`. Pick homogeneous elements `b ∈ I \ p₀` and `a_q ∈ q \ p₀`
for `q ∈ t`; their product `z` is homogeneous, lies in `I` and in every `q ∈ t`, and is
not in `p₀` since `p₀` is prime. As `z ∈ I ≤ irrelevant` and `z ≠ 0`, its degree `e` is
positive. Then `x = y ^ e + z ^ d` is homogeneous of degree `d * e`, lies in `I`, and
avoids every prime of `s`.
-/
import Mathlib

open AlgebraicGeometry

namespace Y3ProjFiniteSets

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A homogeneous ideal that is not contained in an ideal `p` has a homogeneous element
outside `p`. (Only `J` needs to be homogeneous.) -/
theorem exists_homogeneous_mem_notMem_of_not_le {J p : Ideal A}
    (hJ : Ideal.IsHomogeneous 𝒜 J) (h : ¬ J ≤ p) :
    ∃ i, ∃ z ∈ 𝒜 i, z ∈ J ∧ z ∉ p := by
  classical
  by_contra! hcon
  apply h
  intro x hx
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact sum_mem fun i _ =>
    hcon i _ (SetLike.coe_mem _) ((Ideal.IsHomogeneous.mem_iff 𝒜 hJ).mp hx i)

/-- A nonzero homogeneous element of the irrelevant ideal has positive degree. -/
theorem pos_of_mem_irrelevant {i : ℕ} {z : A} (hz : z ∈ 𝒜 i)
    (hirr : z ∈ HomogeneousIdeal.irrelevant 𝒜) (hz0 : z ≠ 0) : 0 < i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · exfalso
    apply hz0
    subst h
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same 𝒜 hz] at hirr
    exact hirr
  · exact h

/-- Given a homogeneous ideal `I` and a prime `p₀` with `¬ I ≤ p₀`, and a finite set `t`
of homogeneous ideals none of which is contained in `p₀`, there is a homogeneous element
of `I`, outside `p₀`, lying in every ideal of `t`. -/
theorem exists_homogeneous_notMem_mem_forall {I p₀ : Ideal A}
    (hI : Ideal.IsHomogeneous 𝒜 I) (hp₀ : p₀.IsPrime) (hIp : ¬ I ≤ p₀)
    (t : Finset (Ideal A)) :
    (∀ q ∈ t, Ideal.IsHomogeneous 𝒜 q) → (∀ q ∈ t, ¬ q ≤ p₀) →
      ∃ e, ∃ z ∈ 𝒜 e, z ∈ I ∧ z ∉ p₀ ∧ ∀ q ∈ t, z ∈ q := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ _
    obtain ⟨e, z, hz, hzI, hzp⟩ := exists_homogeneous_mem_notMem_of_not_le 𝒜 hI hIp
    exact ⟨e, z, hz, hzI, hzp, fun q hq => absurd hq (by simp)⟩
  | @insert q t hqt ih =>
    intro ht htp
    obtain ⟨e, z, hz, hzI, hzp, hzt⟩ := ih
      (fun r hr => ht r (Finset.mem_insert_of_mem hr))
      (fun r hr => htp r (Finset.mem_insert_of_mem hr))
    obtain ⟨m, a, ha, haq, hap⟩ := exists_homogeneous_mem_notMem_of_not_le 𝒜
      (ht q (Finset.mem_insert_self q t)) (htp q (Finset.mem_insert_self q t))
    refine ⟨e + m, z * a, SetLike.mul_mem_graded hz ha, I.mul_mem_right a hzI, ?_, ?_⟩
    · intro hmem
      rcases hp₀.mem_or_mem hmem with h | h
      · exact hzp h
      · exact hap h
    · intro r hr
      rcases Finset.mem_insert.mp hr with h | h
      · rw [h]
        exact q.mul_mem_left z haq
      · exact r.mul_mem_right a (hzt r h)

/-- **Graded prime avoidance** (Stacks 00JS), ideal-level form.

Let `I` be a homogeneous ideal all of whose elements lie in the irrelevant ideal, and let
`s` be a finite set of homogeneous prime ideals, none of which contains `I`. Then there is
a homogeneous `x ∈ I` of positive degree with `x ∉ p` for every `p ∈ s`.
No nonemptiness assumption on `s` is needed. -/
theorem graded_prime_avoidance {I : Ideal A} (hI : Ideal.IsHomogeneous 𝒜 I)
    (hIirr : ∀ a ∈ I, a ∈ HomogeneousIdeal.irrelevant 𝒜) :
    ∀ s : Finset (Ideal A), (∀ p ∈ s, Ideal.IsHomogeneous 𝒜 p) → (∀ p ∈ s, p.IsPrime) →
      (∀ p ∈ s, ¬ I ≤ p) → ∃ n, 0 < n ∧ ∃ x ∈ 𝒜 n, x ∈ I ∧ ∀ p ∈ s, x ∉ p := by
  classical
  intro s
  obtain ⟨n, hn⟩ : ∃ n, s.card = n := ⟨_, rfl⟩
  induction n generalizing s with
  | zero =>
    intro _ _ _
    refine ⟨1, Nat.one_pos, 0, zero_mem _, zero_mem _, ?_⟩
    intro p hp
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨p, hp⟩
    omega
  | succ n ih =>
    intro hhom hprime hnot
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p₀, hmin⟩ := Finset.exists_minimal hne
    have hp₀s : p₀ ∈ s := hmin.prop
    have ht_sub : ∀ q ∈ s.erase p₀, q ∈ s := fun q hq => (Finset.mem_erase.mp hq).2
    have ht_card : (s.erase p₀).card = n := by
      rw [Finset.card_erase_of_mem hp₀s]
      omega
    obtain ⟨d, hd, y, hy, hyI, hyt⟩ := ih (s.erase p₀) ht_card
      (fun q hq => hhom q (ht_sub q hq)) (fun q hq => hprime q (ht_sub q hq))
      (fun q hq => hnot q (ht_sub q hq))
    by_cases hyp₀ : y ∈ p₀
    · -- By minimality of `p₀`, no other prime of `s` is contained in `p₀`.
      have htp : ∀ q ∈ s.erase p₀, ¬ q ≤ p₀ := by
        intro q hq hle
        exact (Finset.mem_erase.mp hq).1
          (le_antisymm hle (hmin.le_of_le (ht_sub q hq) hle))
      obtain ⟨e, z, hz, hzI, hzp, hzt⟩ := exists_homogeneous_notMem_mem_forall 𝒜 hI
        (hprime p₀ hp₀s) (hnot p₀ hp₀s) (s.erase p₀)
        (fun q hq => hhom q (ht_sub q hq)) htp
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact hzp (zero_mem _)
      have he : 0 < e := pos_of_mem_irrelevant 𝒜 hz (hIirr z hzI) hz0
      have h1 : y ^ e ∈ 𝒜 (d * e) := by
        have h := SetLike.pow_mem_graded e hy
        rwa [smul_eq_mul, mul_comm] at h
      have h2 : z ^ d ∈ 𝒜 (d * e) := by
        have h := SetLike.pow_mem_graded d hz
        rwa [smul_eq_mul] at h
      refine ⟨d * e, mul_pos hd he, y ^ e + z ^ d, add_mem h1 h2,
        I.add_mem (I.pow_mem_of_mem hyI e he) (I.pow_mem_of_mem hzI d hd), ?_⟩
      intro p hp hmem
      by_cases hpp : p = p₀
      · rw [hpp] at hmem
        have hye : y ^ e ∈ p₀ := p₀.pow_mem_of_mem hyp₀ e he
        have hzd : z ^ d ∈ p₀ := (p₀.add_mem_iff_right hye).mp hmem
        exact hzp ((hprime p₀ hp₀s).mem_of_pow_mem d hzd)
      · have hpt : p ∈ s.erase p₀ := Finset.mem_erase.mpr ⟨hpp, hp⟩
        have hzd : z ^ d ∈ p := p.pow_mem_of_mem (hzt p hpt) d hd
        have hye : y ^ e ∈ p := (p.add_mem_iff_left hzd).mp hmem
        exact hyt p hpt ((hprime p hp).mem_of_pow_mem e hye)
    · refine ⟨d, hd, y, hy, hyI, ?_⟩
      intro p hp
      by_cases hpp : p = p₀
      · rw [hpp]
        exact hyp₀
      · exact hyt p (Finset.mem_erase.mpr ⟨hpp, hp⟩)

/-- **Graded prime avoidance**, with `I` a bundled homogeneous ideal contained in the
irrelevant ideal. -/
theorem graded_prime_avoidance' (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ HomogeneousIdeal.irrelevant 𝒜) (s : Finset (Ideal A))
    (hhom : ∀ p ∈ s, Ideal.IsHomogeneous 𝒜 p) (hprime : ∀ p ∈ s, p.IsPrime)
    (hnot : ∀ p ∈ s, ¬ I.toIdeal ≤ p) :
    ∃ n, 0 < n ∧ ∃ x ∈ 𝒜 n, x ∈ I ∧ ∀ p ∈ s, x ∉ p := by
  obtain ⟨n, hn, x, hx, hxI, hxs⟩ := graded_prime_avoidance 𝒜 I.isHomogeneous
    (fun a ha => hI (HomogeneousIdeal.mem_iff.mp ha)) s hhom hprime hnot
  exact ⟨n, hn, x, hx, HomogeneousIdeal.mem_iff.mp hxI, hxs⟩

/-- Every finite set of points of `Proj 𝒜` is contained in an affine open subset, namely
a basic open `D₊(f)` for some homogeneous `f` of positive degree. -/
theorem exists_isAffineOpen_superset_of_finite (F : Set (Proj 𝒜)) (hF : F.Finite) :
    ∃ U : (Proj 𝒜).Opens, IsAffineOpen U ∧ F ⊆ U := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset (Ideal A),
      s = hF.toFinset.image (fun x : Proj 𝒜 => x.asHomogeneousIdeal.toIdeal) := ⟨_, rfl⟩
  have hmem : ∀ p ∈ s, ∃ x : Proj 𝒜, x ∈ F ∧ x.asHomogeneousIdeal.toIdeal = p := by
    intro p hp
    rw [hs, Finset.mem_image] at hp
    obtain ⟨x, hx, hxp⟩ := hp
    exact ⟨x, hF.mem_toFinset.mp hx, hxp⟩
  have hIirr : ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal,
      a ∈ HomogeneousIdeal.irrelevant 𝒜 := fun a ha => HomogeneousIdeal.mem_iff.mp ha
  have h1 : ∀ p ∈ s, Ideal.IsHomogeneous 𝒜 p := by
    intro p hp
    obtain ⟨x, -, rfl⟩ := hmem p hp
    exact x.asHomogeneousIdeal.isHomogeneous
  have h2 : ∀ p ∈ s, p.IsPrime := by
    intro p hp
    obtain ⟨x, -, rfl⟩ := hmem p hp
    exact x.isPrime
  have h3 : ∀ p ∈ s, ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p := by
    intro p hp
    obtain ⟨x, -, rfl⟩ := hmem p hp
    intro h
    apply x.not_irrelevant_le
    intro a ha
    exact HomogeneousIdeal.mem_iff.mp (h (HomogeneousIdeal.mem_iff.mpr ha))
  obtain ⟨n, hn, f, hf, -, hfs⟩ := graded_prime_avoidance 𝒜
    (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous hIirr s h1 h2 h3
  refine ⟨Proj.basicOpen 𝒜 f, Proj.isAffineOpen_basicOpen 𝒜 f hf hn, ?_⟩
  intro x hx
  have hxs : x.asHomogeneousIdeal.toIdeal ∈ s := by
    rw [hs, Finset.mem_image]
    exact ⟨x, hF.mem_toFinset.mpr hx, rfl⟩
  exact (Proj.mem_basicOpen 𝒜 f x).mpr fun hfx =>
    hfs _ hxs (HomogeneousIdeal.mem_iff.mpr hfx)

end Y3ProjFiniteSets
