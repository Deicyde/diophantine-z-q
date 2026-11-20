import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Determinant
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Seed
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Fresh

/-! Assemble the two characteristic-zero calculations and use the existing
finite-field match at the same Frobenius lift. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KsplitHpacket

open Finset AppE EvenReading AddressGenuine Wiring PrintsAnalytic PrintsArith O12Local O12Eisenstein
open ZInQ.Manuscript.RC.Even KSplit KSplitSeed
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

section Local

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B chiType}
variable {p : ℕ} {P : O12.LocalPair p} [Fact p.Prime]
variable {A : O12.FourierData X} {a η : ℕ → ℂ} {m : ℕ}

abbrev stageBlocks (s : Stage A ({p} : Finset ℕ) P (Fact.out : p.Prime).ne_zero) :
    O12.LocalBlocks X {p} P := combine s.cusp.sector s.eisenstein s.disjoint s.support

/-- Extension of the same O12 stage and operator; the three comparisons
concern the actual old action, positive Fourier shifts and determinant
characters of the singleton blocks. -/
structure Packet (A : O12.FourierData X) (P : O12.LocalPair p) (ι : X.K →+* ℂ)
    (a η : ℕ → ℂ) (m : ℕ) (O : Subring ℂ) where
  stage : Stage A {p} P (Fact.out : p.Prime).ne_zero
  old : OldBlockCubic (stageBlocks stage)
  shift : UpShift A (stageBlocks stage) (Fact.out : p.Prime).ne_zero
  zeroIndex : X.C
  blocks : BlockRealization A zeroIndex ι a η m p
  j : ℤ_[2] →+* X.K
  modulus : ℕ
  modulus_ne : NeZero modulus
  χ : DirichletCharacter X.K modulus
  det : letI : NeZero modulus := modulus_ne
    DeterminantAt P j (dirichletGalois χ) blocks.blockB blocks.blockOne blocks.blockP
  χ_mem : letI : NeZero modulus := modulus_ne
    ι (dirichletGalois χ P.φ : X.K) ∈ O

def traceFourier (A : O12.FourierData X) (zero : X.C) (ι : X.K →+* ℂ)
    (g : GalQ) (n : ℕ) : ℂ :=
  ι (X.coefK (tV X.ρ g (X.F {p})) (coeffIndex A zero n))

def detFourier (A : O12.FourierData X) (zero : X.C) (ι : X.K →+* ℂ)
    (g : GalQ) (n : ℕ) : ℂ :=
  ι (X.coefK (dV X.ρ g (X.F {p})) (coeffIndex A zero n))

/-- The five characteristic-zero conjuncts of the seed packet, with the
trace and determinant of the same actual F at the same lift. -/
theorem hpacketTrace_of_packet {ι : X.K →+* ℂ} {O : Subring ℂ}
    (Q : Packet A P ι a η m O) (hp₂ : p ≠ 2) :
    ∃ δB δ1 δp : ℂ, δB = δp ∧ δp ∈ O ∧ InTwoO O (δp - δ1) ∧
      DphiBlocks (detFourier (p := p) A Q.zeroIndex ι P.φ) a η m p δB δ1 δp ∧
      traceFourier (p := p) A Q.zeroIndex ι P.φ (p ^ 2) =
        thetaMul (Hp a η m p) (p ^ 3) + detFourier (p := p) A Q.zeroIndex ι P.φ p := by
  let : CharZero X.K := ⟨fun m n h => Nat.cast_injective (R := ℂ) (by
    simpa only [map_natCast] using congrArg ι h)⟩
  have hp : p.Prime := Fact.out
  let s := Q.stage
  let : NeZero Q.modulus := Q.modulus_ne
  obtain ⟨δB, δ1, δp, he, hO, hdiff, hdet⟩ :=
    dphiBlocks_of_characters Q.blocks O hp hp₂ Q.det Q.χ_mem
  refine ⟨δB, δ1, δp, he, hO, hdiff, hdet, ?_⟩
  have h₁ : A.UpAtOne (stageBlocks s) hp.ne_zero :=
    combine_upAtOne A _ _ s.disjoint s.support hp.ne_zero
      (cuspidal_upAtOne A _ _ s.whittaker) s.eisenstein_shift
  have ha (v : X.I → X.K) : SupportedOn (stageBlocks s).active ((stageBlocks s).Up v) :=
    combine_active_stable s.cusp.sector s.eisenstein s.disjoint s.support v
  have ht := congrArg ι (trace_coeff_p_sq A (stageBlocks s) hp.ne_zero h₁ Q.shift
    (fun v _ => ha v) Q.old)
  rw [map_add] at ht
  unfold traceFourier detFourier
  rw [← fourier_F_of_blocks Q.blocks, coeffIndex_pos _ _ (pow_ne_zero 2 hp.ne_zero),
    coeffIndex_pos _ _ (pow_ne_zero 3 hp.ne_zero), coeffIndex_pos _ _ hp.ne_zero]
  exact ht

end Local

variable {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
variable {C : CentralNormalization (Ecurve ℓ)} {hk : W.kfin < 0} {S : Finset ℕ}
variable (G : GenuineEvenSource C hk S) (O : Subring ℂ)

/-- The packet at a tested prime and the two existing inputs of
`exists_fresh_trace_match`. Models and restriction fields can be chosen
separately at each tested singleton. -/
structure MatchedPacket (B p : ℕ) [Fact p.Prime] where
  X : GaloisConstituentModel D.T₂ (RevGen S G.r) (apk W) B (typChar D.m₂)
  A : O12.FourierData X
  P : O12.LocalPair p
  ι : X.K →+* ℂ
  packet : Packet A P ι (evenCoeff G) (fun n => G.P.η n) D.m₂ O
  avoid : Finset ℕ
  E : IntermediateField ℚ PrintsArith.Qbar
  finite : FiniteDimensional ℚ E
  htr : ∀ g : GalQ, (∀ x ∈ E, g x = P.φ x) →
    InTwoO O (traceFourier (p := p) A packet.zeroIndex ι P.φ (p ^ 2) -
      traceFourier (p := p) A packet.zeroIndex ι g (p ^ 2))
  hhecke : ∀ q : ℕ, q.Prime → q.Coprime D.m₂ → q ∉ avoid → q ≠ p →
    ∀ g : GalQ, IsFrobAt g q →
      traceFourier (p := p) A packet.zeroIndex ι g (p ^ 2) =
        thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 2 * q)

/-- Exactly the hpacket argument of `kSplitSeed_of_singleton_trace`. -/
theorem hpacket_of_packets {B : ℕ}
    (hint : ∀ p : ℕ, ∀ hp : p.Prime, letI : Fact p.Prime := ⟨hp⟩
      p ∉ S → p.Coprime D.m₂ → jacobiSym W.kfin p = 1 →
      ∀ n, Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p n ∈ O)
    (packets : ∀ p : ℕ, ∀ hp : p.Prime, letI : Fact p.Prime := ⟨hp⟩
      p ∉ S → p.Coprime D.m₂ → jacobiSym W.kfin p = 1 →
      Nonempty (MatchedPacket D G O B p)) :
    ∀ p : ℕ, ∀ hp : p.Prime, letI : Fact p.Prime := ⟨hp⟩
      p ∉ S → p.Coprime D.m₂ → jacobiSym W.kfin p = 1 →
      (∀ n, Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p n ∈ O) ∧
      ∃ (p' : ℕ) (tf df : ℕ → ℂ) (δB δ1 δp : ℂ),
        p'.Prime ∧ p' ≠ p ∧ p'.Coprime D.m₂ ∧ jacobiSym W.kfin p' = 1 ∧
        δB = δp ∧ δp ∈ O ∧ InTwoO O (δp - δ1) ∧
        DphiBlocks df (evenCoeff G) (fun n => G.P.η n) D.m₂ p δB δ1 δp ∧
        tf (p ^ 2) = thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 3) + df p ∧
        InTwoO O (tf (p ^ 2) -
          thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 2 * p')) := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  intro hpS hpM hkp
  obtain ⟨Q⟩ := packets p hp hpS hpM hkp
  have hp₂ : p ≠ 2 := by
    rintro rfl
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpM) (dvd_trans (by decide : 2 ∣ 8) D.eight₂)
  obtain ⟨δB, δ1, δp, he, hO, hdiff, hd, ht⟩ := hpacketTrace_of_packet Q.packet hp₂
  have hφ : IsFrobAt Q.P.φ p := ⟨Q.P.Q, Q.P.maximal, Q.P.above, Q.P.frob⟩
  obtain ⟨q, hq, hqM, _, hqp, _, hkq, hm⟩ :=
    exists_fresh_trace_match D O hp hpM hkp hφ Q.avoid Q.E Q.finite
      (fun g => traceFourier (p := p) Q.A Q.packet.zeroIndex Q.ι g (p ^ 2))
      (thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p)) Q.htr Q.hhecke
  exact ⟨hint p hp hpS hpM hkp, q, _, _, δB, δ1, δp, hq, hqp, hqM, hkq,
    he, hO, hdiff, hd, ht, hm⟩

/-- The genuine App G seed from the characteristic-zero packets and the
existing integrality, matching and old-unit inputs. -/
theorem kSplitSeed_of_packets {B : ℕ}
    (hodd : ∀ d : ℕ, ¬ 2 ∣ d → (d : ℂ)⁻¹ ∈ O)
    (hz : ∀ n, S0Filter S 1 n → G.P.z n ∈ O)
    (hhalf : (2 : ℂ)⁻¹ ∉ O)
    (hηO : ∀ n : ℕ, G.P.η n ∈ O)
    (hlow : ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n))
    (hint : ∀ p : ℕ, ∀ hp : p.Prime, letI : Fact p.Prime := ⟨hp⟩
      p ∉ S → p.Coprime D.m₂ → jacobiSym W.kfin p = 1 →
      ∀ n, Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p n ∈ O)
    (packets : ∀ p : ℕ, ∀ hp : p.Prime, letI : Fact p.Prime := ⟨hp⟩
      p ∉ S → p.Coprime D.m₂ → jacobiSym W.kfin p = 1 →
      Nonempty (MatchedPacket D G O B p)) :
    AddressGenuine.KSplitSeed W D (RevGen S G.r) :=
  kSplitSeed_of_singleton_trace D G O hodd hz hhalf hηO hlow
    (hpacket_of_packets D G O hint packets)

end ZInQ.Manuscript.RC.KsplitHpacket
