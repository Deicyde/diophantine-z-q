import ZInQKernel.Contrib.OneProof.RC.Moving.Trace
import ZInQKernel.Contrib.OneProof.RC.Moving.Presentation

/-!
# Lane RC4 (moving character): the printed and textbook inputs, as an interface

Manuscript (11/5 version), Proposition `ex:arith-moving-character` (tex 3500–3702).

Elliot's proof combines his own finite and 2-adic algebra (proved in `SL2.lean`, `Trace.lean`,
`Presentation.lean`) with printed theorems and textbook facts about objects that do not exist in
Mathlib: the absolute Galois groups `G_{ℚ(μ_{2^∞})} ⊃ G_{F_∞} ⊃ G_{L_∞}`, the Tate representation
`ρ_T` of `E_ℓ`, Kummer theory over `F_∞ = K(μ_{2^∞})`, ring class fields `H_r` and their Artin maps,
local reciprocity and Chebotarev.  This file records them as the fields of two structures, one
field per input, each with its kind (`PRINT` or `GLUE`), the tex lines that use it and a locator.
The structures are the most faithful abstract interface we could give: every field is a
statement about the genuine objects that the manuscript uses at the cited line, and nothing else.
`MovingCharacter.lean` then proves Elliot's proposition from these fields (`PROVED` relative to
the interface).

Nothing here is assumed globally: the structures are hypotheses of the theorems that use them.
Their non-vacuity rests on the truth of the cited facts for the genuine objects; no Lean model of
the full interface is constructed (the genuine objects are not in Mathlib).

Locators (read on the public web unless marked `UNVERIFIED`):
* [Serre] J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*,
  Invent. Math. 15 (1972), 259–331 (the manuscript's `\cite{serre}`, no locator given):
  §4.4, Théorème 3, p. 299 (for non-CM `E`, `ρ(G)` is open in `∏_ℓ GL(T_ℓ)`) and Corollaire 2,
  p. 300 (the image of `Gal(K̄/K^cycl)` is open in `∏_ℓ SL(T_ℓ)`) — locators as read from the
  published scan by lane RC9 (its `ZInQ.Manuscript.RC.PrintsArith.serre_SL2_part` gives the form
  used at tex 3597–3605 over the genuine Tate module); the single-prime statement was read here in
  Serre's McGill notes, *Abelian ℓ-adic representations and elliptic curves*, Ch. IV, §2.2,
  Theorem, p. IV-11 (`G_ℓ` open in `Aut(T_ℓ)` when `E` has no complex multiplication).
* [Cox] D. A. Cox, *Primes of the form x² + ny²*: Proposition 7.22 (`C(𝒪) ≅ I_K(f)/P_{K,ℤ}(f)`),
  proof of Theorem 7.24, sequences (7.25) and (7.27) (with `𝒪_K^× = {±1}`); §9.A, (9.1) and
  the following paragraph (ring class field: primes ramified in `L` divide `f𝒪_K`; the Artin map
  gives `C(𝒪) ≅ Gal(L/K)`).  Read in a later edition with the same numbering; Version 19 of the
  manuscript cites "Proposition 7.22 and the proof of Theorem 7.24" of the 1989 edition.
* [Neukirch] J. Neukirch, *Algebraic number theory*, Grundlehren 322 (Springer 1999): Ch. V,
  Theorem (6.2), p. 354 (the norm residue symbol maps `U_K^{(n)}` onto `G^n(L|K)`; `n = 0`: the
  local units onto the inertia group); Ch. VII, Theorem (13.4) (Čebotarev's density theorem;
  quoted as such on p. 547; the statement page itself was not read: `UNVERIFIED` page).
* [Guillot] P. Guillot, *A gentle course in local class field theory* (CUP 2018), pp. 11–13,
  Lemma 1.20 and Theorem 1.22 (the perfect Kummer pairing), as cited by Version 19 of the
  manuscript (`UNVERIFIED`: not read).
* [Silverman] J. H. Silverman, *The arithmetic of elliptic curves*, 2nd ed.: Theorem V.2.3.1
  (`tr` and `det` of Frobenius on `T_ℓ`), Proposition VII.3.1(b) (reduction is injective on
  prime-to-`p` torsion), §III.8 (Weil pairing: `det ρ_T` is the cyclotomic character)
  (`UNVERIFIED`: not re-read).
-/

open Matrix
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.Moving

/-- **The fixed Tate image** (tex 3597–3605).  `G` is the absolute Galois group of
`ℚ(μ_{2^∞})` and `ρ` the 2-adic Tate representation `ρ_T` of the fixed curve `E_ℓ` restricted to
it.  Its values lie in `SL₂(ℤ₂)` because the determinant of `ρ_T` is the 2-adic cyclotomic
character (`GLUE`, [Silverman, §III.8]), trivial on `G_{ℚ(μ_{2^∞})}`; so `J = ρ(G)` is "the
determinant-one part of the fixed Tate image" (tex 3598–3599). -/
structure TateImage where
  /-- the group `G_{ℚ(μ_{2^∞})}` -/
  G : Type
  [grp : Group G]
  /-- `ρ_T` restricted to `G_{ℚ(μ_{2^∞})}` -/
  ρ : G →* SL(2, ℤ_[2])
  /-- Serre's level `d` (tex 3601) -/
  d : ℕ
  two_le_d : 2 ≤ d
  /-- `PRINT` (tex 3600–3605): **non-CM open image**, `Γ_d ⊂ J`.  [Serre, §4.4 Théorème 3 and
  Corollaire 2]: since `E_ℓ` has no CM (`j = 35152/9` is not an integer), the image of
  `G_{ℚ(μ_{2^∞})}` is open in `SL(T₂E) ≅ SL₂(ℤ₂)`, so it contains a principal congruence subgroup
  `Γ_d`, `d ≥ 2` (`GLUE`: the `Γ_d` form a basis of neighbourhoods of `1`; a basis of `T₂E` is
  fixed). -/
  serre : Γ d ≤ ρ.range

attribute [instance] TateImage.grp

/-- **The moving-character setting** for a fixed allowed `K`, a fixed finite list of oriented
active primes and a fixed `n` (tex 3530–3595, 3662–3684).

Chosen primes (tex 3530–3534): prime ideals `𝔭_1, …, 𝔭_s` of `K` in distinct conjugate pairs,
including the active orientations (`act j`, weight `w_j = 1`), one prime over each prime dividing
`2N` (`over2N j`, weight `0`), and split primes generating `Cl(K)` (weight `0`).  Relation module
`𝓡 = ker(ℤ^s → Cl(K))` with spanning vectors `m^{(a)}`, generators `(β_a) = ∏ 𝔭_j^{m_j^{(a)}}`,
radicands `α_a = β_a / β̄_a`.

Kummer layer (tex 3545–3563): `F_∞ = K(μ_{2^∞})`, `L_∞ = F_∞(α_a^{1/2^n} : a)`; `GF` and `HL`
are `G_{F_∞} ⊃ G_{L_∞}` inside `G_{ℚ(μ_{2^∞})}`; `kum σ a` is the exponent `e` with
`σ(α_a^{1/2^n}) = ζ_{2^n}^e α_a^{1/2^n}`.

Ring classes (tex 3565–3595, 3679–3684): for a good rational prime `r` (split in `K`, prime to
`2N` and to the chosen primes), `P r = Gal(H_r/K) ≅ Pic(ℤ + r𝒪_K)` (written additively),
`π r : P r → Cl(K)`, `q r j` and `qbar r j` the Frobenius classes of `𝔭_j` and `𝔭̄_j`,
`inertia r` the inertia group at `r`, `decomp r j`, `decompBar r j` the decomposition groups at
`𝔭_j`, `𝔭̄_j`; `ap r = a_r(E_ℓ)`; and, for a place `v ∈ Pl r` orienting the data at `r`,
`δ r v : 𝐅_r^× → P r` the connecting map, `x r v a = res α_a` and `κ r v` the `2^n`-th
power-residue character. -/
structure MovingSetting (T : TateImage) (n : ℕ) where
  /-- number of chosen primes -/
  s : ℕ
  /-- number of radicands (rank of `𝓡`) -/
  t : ℕ
  /-- `𝔭_j` is a prescribed active orientation (weight one) -/
  act : Fin s → Prop
  [decAct : DecidablePred act]
  /-- `𝔭_j` is the chosen prime over a prime dividing `2N` -/
  over2N : Fin s → Prop
  /-- the active primes are odd, prime to `N`, and distinct from the chosen primes over `2N` -/
  act_not_over2N : ∀ j, act j → ¬ over2N j
  /-- the class group `Cl(K)` (additively) -/
  Cl : Type
  [clGrp : AddCommGroup Cl]
  /-- the classes of the chosen primes -/
  cls : Fin s → Cl
  /-- `GLUE` (tex 3532–3534): the chosen split primes generate `Cl(K)`; they exist outside any
  finite set by Chebotarev in the Hilbert class field [Neukirch VII (13.4)]. -/
  cls_gen : ∀ c : Cl, ∃ v : Fin s → ℤ, ∑ j, v j • cls j = c
  /-- the spanning vectors `m^{(a)}` of `𝓡` (Elliot: a `ℤ`-basis; spanning is what is used) -/
  m : Fin t → Fin s → ℤ
  /-- `𝓡 = ker(ℤ^s → Cl(K))` is spanned by the `m^{(a)}` (tex 3537–3541) -/
  m_span : ∀ v : Fin s → ℤ, ∑ j, v j • cls j = 0 → ∃ b : Fin t → ℤ, v = ∑ a, b a • m a
  /-- `G_{F_∞}` -/
  GF : Subgroup T.G
  /-- `GLUE` (tex 3606): `[F_∞ : ℚ(μ_{2^∞})] ≤ [K : ℚ] = 2`, so `G_{F_∞}` has index at most two
  in `G_{ℚ(μ_{2^∞})}` (infinite Galois theory). -/
  GF_index : GF.index = 1 ∨ GF.index = 2
  /-- `G_{L_∞}` -/
  HL : Subgroup T.G
  /-- `L_∞ ⊃ F_∞` -/
  HL_le : HL ≤ GF
  /-- the Kummer multipliers on the radicals `α_a^{1/2^n}` (a homomorphism because `G_{F_∞}`
  fixes `μ_{2^∞}`) -/
  kum : GF →* Multiplicative (Fin t → ZMod (2 ^ n))
  /-- `GLUE`: `G_{L_∞}` fixes the radicals. -/
  kum_of_mem_HL : ∀ σ : GF, (σ : T.G) ∈ HL → kum σ = 1
  /-- `GLUE` (Galois correspondence): an element of `G_{F_∞}` fixing every radical fixes
  `L_∞ = F_∞(α_a^{1/2^n} : a)`. -/
  mem_HL_of_kum : ∀ σ : GF, kum σ = 1 → (σ : T.G) ∈ HL
  /-- the Kummer relations: exponent vectors `b` with `∏_a α_a^{b_a} ∈ F_∞^{×2^n}` -/
  KR : AddSubgroup (Fin t → ℤ)
  /-- `GLUE` (tex 3551–3557): if `∏ α_a^{b_a}` is a `2^n`-th power in `F_∞`, its root lies in a
  finite cyclotomic layer, unramified over `K` at the odd nonzero-weight primes; with
  `v_{𝔭_j}(α_a) = m_j^{(a)}` (disjoint conjugate pairs, tex 3542–3543) this gives
  `2^n ∣ ∑_a b_a m_j^{(a)}` at each active `j`.  (Units and dependent radicands are allowed.) -/
  KR_val : ∀ b ∈ KR, ∀ j, act j → (2 : ℤ) ^ n ∣ ∑ a, b a * m a j
  /-- `GLUE` (tex 3559–3563, the perfect Kummer pairing [Guillot, Lemma 1.20, Theorem 1.22]):
  every assignment of multipliers that respects the Kummer relations is realized by an
  automorphism of `L_∞/F_∞`, hence (restriction is onto) by some `σ₀ ∈ G_{F_∞}`. -/
  kum_surj : ∀ φ : Fin t → ZMod (2 ^ n),
    (∀ b ∈ KR, ∑ a, (b a : ZMod (2 ^ n)) * φ a = 0) → ∃ σ : GF, kum σ = Multiplicative.ofAdd φ
  /-- `r` is good: a rational prime split in `K`, prime to `2N` and to the chosen primes -/
  good : ℕ → Prop
  /-- `a_r` of the fixed curve -/
  ap : ℕ → ℤ
  /-- `Gal(H_r/K) ≅ Pic(ℤ + r𝒪_K)` -/
  P : ℕ → Type
  [pGrp : ∀ r, AddCommGroup (P r)]
  /-- the places used to orient the data at `r`: a place `v` of `K(μ_{2^n})` over `r` fixes the
  prime `𝔯 = v ∩ K` (hence the residue-ratio coordinate `𝐅_r^×` of the ring-class kernel and the
  residues `res α_a`) and the reduction of `μ_{2^n}` (hence `κ_r`).  Elliot: "Choose a place
  realizing this representative" (tex 3675–3676); "reversing the connecting-map convention
  reverses the power-residue convention as well" (tex 3594–3595). -/
  Pl : ℕ → Type
  /-- the connecting map `𝐅_r^× → Pic(ℤ + r𝒪_K)` at the place `v` (oriented as in
  tex 3576–3579) -/
  δ : ∀ r, Pl r → (Additive (ZMod r)ˣ →+ P r)
  /-- `Pic(ℤ + r𝒪_K) → Cl(K)` -/
  π : ∀ r, P r →+ Cl
  /-- `GLUE` (tex 3566–3575, [Cox, Prop. 7.22, proof of Thm 7.24, (7.25), (7.27)]): for split
  `r`, `1 → 𝐅_r^× → Pic(ℤ + r𝒪_K) → Cl(K) → 1` is exact (the kernel is the ratio of the two
  residue factors modulo diagonal rational residues; no unit quotient since `𝒪_K^× = {±1}`). -/
  δ_inj : ∀ r, good r → ∀ v, Function.Injective (δ r v)
  exact : ∀ r, good r → ∀ v, ∀ p : P r, π r p = 0 ↔ ∃ y, δ r v y = p
  /-- the Frobenius class of `𝔭_j` in `Gal(H_r/K)` -/
  q : ∀ r, Fin s → P r
  /-- the Frobenius class of `𝔭̄_j` -/
  qbar : ∀ r, Fin s → P r
  /-- `GLUE` ([Cox, (9.1)]): the Artin map sends `𝔭_j` to the class of `𝔭_j ∩ (ℤ + r𝒪_K)`,
  a lift of the class of `𝔭_j` (tex 3575–3576). -/
  π_q : ∀ r, good r → ∀ j, π r (q r j) = cls j
  /-- `GLUE` (tex 3683–3684): `𝔭_j 𝔭̄_j = (p)` is rational principal, so `qbar = −q`. -/
  qbar_eq : ∀ r, good r → ∀ j, qbar r j = -q r j
  /-- `res α_a ∈ 𝐅_r^×`: the residue of `α_a` at `𝔯 = v ∩ K`, i.e. the residue-ratio
  coordinate of the class of `β_a` (read so; see the report on tex 3579) -/
  x : ∀ r, Pl r → Fin t → Additive (ZMod r)ˣ
  /-- `GLUE` (tex 3576–3579, [Cox, (7.27)]): the principal relations
  `∑_j m_j^{(a)} q_j + δ(res α_a) = 0`. -/
  rel : ∀ r, good r → ∀ v a, ∑ j, m a j • q r j + δ r v (x r v a) = 0
  /-- the `2^n`-th power-residue character `κ_r : 𝐅_r^× → ℤ/2^n` at the place `v` -/
  κ : ∀ r, Pl r → (Additive (ZMod r)ˣ →+ ZMod (2 ^ n))
  /-- `GLUE` (tex 3585–3586): `𝐅_r^×` is cyclic of order `r − 1`, so `κ_r` is onto when
  `r ≡ 1 (mod 2^n)`. -/
  κ_surj : ∀ r, good r → ∀ v, (2 : ℤ) ^ n ∣ (r : ℤ) - 1 → Function.Surjective (κ r v)
  /-- the inertia group at `r` in `Gal(H_r/K)` -/
  inertia : ∀ r, AddSubgroup (P r)
  /-- `GLUE` (tex 3679–3681, local reciprocity [Neukirch V (6.2), p. 354] with [Cox, (9.1)]):
  each local unit factor at `r` maps onto the residue-ratio kernel, so the inertia group at `r`
  is the image of `δ_r`. -/
  inertia_eq : ∀ r, good r → ∀ v, inertia r = (δ r v).range
  /-- the decomposition groups at `𝔭_j` and `𝔭̄_j` in `Gal(H_r/K)` -/
  decomp : ∀ r, Fin s → AddSubgroup (P r)
  decompBar : ∀ r, Fin s → AddSubgroup (P r)
  /-- `GLUE` (tex 3681–3682, [Cox, §9.A]): `H_r/K` is unramified outside `r`, so the
  decomposition group of `𝔭_j` (resp. `𝔭̄_j`) is generated by its Frobenius. -/
  decomp_eq : ∀ r, good r → ∀ j, decomp r j = AddSubgroup.zmultiples (q r j)
  decompBar_eq : ∀ r, good r → ∀ j, decompBar r j = AddSubgroup.zmultiples (qbar r j)
  /-- `PRINT`/`GLUE` (tex 3670–3679): **finite Chebotarev** [Neukirch VII (13.4)] applied in a
  finite Galois extension of `ℚ` containing `K`, `μ_{2^{B'}}`, `E[2^{B'}]` and the radicals,
  at a place realizing `σ|_M` and avoiding the finite set `S`, together with the standard
  Frobenius facts: `r` splits in `K` and `r ≡ 1 (mod 2^{B'})` (since `σ` fixes `K` and
  `μ_{2^{B'}}`); `a_r ≡ tr ρ_T(σ) (mod 2^{B'})` ([Silverman, V.2.3.1, VII.3.1(b)]); and the
  Frobenius formula on `α_a^{1/2^n}` at the realizing place `v`: `κ_r(res α_a)` equals the
  Kummer multiplier of `σ`. -/
  cheb : ∀ (σ : GF) (B' : ℕ) (S : Finset ℕ), ∃ (r : ℕ) (v : Pl r), r ∉ S ∧ r.Prime ∧ good r ∧
    (2 : ℤ) ^ B' ∣ (r : ℤ) - 1 ∧
    (2 : ℤ_[2]) ^ B' ∣ (ap r : ℤ_[2]) - tr (T.ρ σ) ∧
    ∀ a, κ r v (x r v a) = Multiplicative.toAdd (kum σ) a

attribute [instance] MovingSetting.decAct MovingSetting.clGrp MovingSetting.pGrp

end ZInQ.Manuscript.RC.Moving
