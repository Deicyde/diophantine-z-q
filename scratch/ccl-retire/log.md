# Base consumer audit

Base `a59ea33fe90ba2b0aa39f896137097180aad5f6e`. The checked-out `wip/ccl-retire` and the
existing `origin/wip/rc-lane-batch-1121a` ref both resolve to that commit.
The fetch request returned HTTP 403.

`git grep -n -I -w` searched the exact declaration and module names across
all tracked files at that commit. The search includes `chainCond` and
`dvd_chainCond`, which are moved. The old structures and the
`E2ChainInputs` namespace were also checked for qualified references, and
for shorthand references in the files that can resolve them. Unqualified
matches in the staged modules refer to their staged counterparts. The
lists include declarations, uses, comments, and historical records.

## Retirement decision

No out-of-plan Lean declaration depends on a declaration marked for
deletion. The out-of-plan matches for retired names in Lean sources are
comments. The same-spelled `ps_getD_pos`, `ps_getD_prime`, and other
staged members belong to distinct declarations. `E2ChainActual` uses the
moved `chainCond` through the staged import. The expected imports of
retired modules are in `H20Transport`, `CommonCoordinate18LeafE2`, and
`CommonCoordinate19E2`. There is no `ALLCONTRIB.lean` on the base and no
aggregate import of a retired module.

## Direct imports on the base

```text
ZInQKernel/Contrib/CloudB3E2Norm/CentralSpec.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:1:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
ZInQKernel/Contrib/CloudB3E2Norm/H20AmbientS.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields
ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:1:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/CloudB3E2Norm/H20PairedLift.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassMatch.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClass
ZInQKernel/Contrib/CloudB3E2Norm/H20ThetaMono.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20HeegnerNorm
ZInQKernel/Contrib/CloudB3E2Norm/H20Untwisted.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20Transport
ZInQKernel/Contrib/CloudB3E2Norm/HeegnerRCBridge.lean:3:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/RingClassMono.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields
ZInQKernel/Contrib/OneProof/RC/CCLUnitIndex/Units.lean:1:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/HeegnerAnchor/Comparison.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor
ZInQKernel/Contrib/OneProof/RC/O7Actual/Reduction.lean:2:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/PrintsArith/Bundle.lean:2:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:2:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:3:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19Leaf.lean:1:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
```

## Declaration and module name matches

```text
.fleet/rc-heegner-anchor.md:9:images and their fields in the anchor of `CCLGenuine`.
.fleet/rc-heegner-anchor.md:14:stay with `CCLThm2_15Applied`; the anchor does not certify compatible
ZInQKernel/Contrib/CloudB3E2Norm/CochainNorm.lean:60:   actual classes with the classes of the Heegner points `y_T` (the anchor of `CCLThm2_15Applied`).
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:48:    ∀ j, q ∣ chainCond d ps j → q ∣ d ∨ ∃ m < j, q ∣ ps.getD m 1
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:201:      exact not_two_primes (P.ps_getD_prime hi) (P.ps_getD_prime hj) hne hmem hjmem
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:204:      have hqp := P.ps_getD_prime hi
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:228:              have hpm := P.ps_getD_prime hmi
ZInQKernel/Contrib/CloudB3E2Norm/GlobalCochain.lean:48:(`CCLThm2_15Applied`'s anchor); (5) the local components `hU`, `hL` (item 3 of the
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:12:`RC/PrintsArith/Heegner.lean` states the print as `CCLThm2_15Applied E Anchor :=
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:27:* `CCLGenuine E K p ι := CCLThm2_15Applied E (GenuineHeegnerAnchor …)` (definition): the
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:36:* **`hnorm_of_genuine_print`** (PROVED): from `CCLGenuine` and the remaining field-level dictionary
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:40:Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied` with the anchor; the analytic
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:95:def CCLGenuine (p : CSTParam E) (ι : Qbar →ₐ[ℚ] ℂ) : Prop :=
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:96:  CCLThm2_15Applied E (GenuineHeegnerAnchor E K p ι)
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:131:`CCLGenuine`): there is an anchored datum `D` (its points are the images of CM points, `D.N = N_E`,
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:136:theorem hnorm_of_genuine_print {p : CSTParam E} {ι : Qbar →ₐ[ℚ] ℂ}
ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:137:    (hprint : CCLGenuine E K p ι) :
ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:11:The print `CCLThm2_15Applied` is existential in the datum, so these descriptions must be part of the
ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:34:  Heegner points from the anchored print `CCLThm2_15Applied E (FullAnchor …)` alone, given the
ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:444:(PROVED from the PRINT `CCLThm2_15Applied E (FullAnchor …)`): there is an anchored datum `D` with
ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:452:    (hprint : CCLThm2_15Applied E (FullAnchor E K p ι κ)) :
ZInQKernel/Contrib/CloudB3E2Norm/H20Dictionary.lean:38:  `hnorm_of_print_on`) and (i)–(iv).
ZInQKernel/Contrib/CloudB3E2Norm/H20Dictionary.lean:272:(PROVED from the PRINT `CCLThm2_15Applied` and the field-level dictionary (i)–(iv), tex 2914–2936):
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:16:`t` a transversal). The tree's print is `CCLThm2_15Applied E Anchor` (`PrintsArith/Heegner.lean`):
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:20:* **`HeegnerTransportAt`** (Prop; kind GLUE — the compatibility of the ring class fields
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:25:* **`hnorm_of_normRelations`** (PROVED): `D.NormRelations`, admissibility, `q` split in `K` and
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:26:  `HeegnerTransportAt` give `hnorm` with `a = a_q = E.LFunction q`.
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:27:* **`hnorm_of_print`** (PROVED): from the print `CCLThm2_15Applied E Anchor`, if every anchored
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:31:* Non-vacuity: `nonVacuity_transport` (the zero comparison into the zero system).
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:33:Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied` and the GLUE `HeegnerTransportAt`.
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:51:def HeegnerTransportAt (D : HeegnerPointData E) (d q : ℕ) (σ : G) (yR yP : Dm) : Prop :=
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:61:`HeegnerTransportAt`, is the norm relation in the twisted-transfer form, with `a = a_q`. -/
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:62:theorem hnorm_of_normRelations (D : HeegnerPointData E) (hD : D.NormRelations) {d q : ℕ}
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:64:    (htr : HeegnerTransportAt ρ HP U t D d q σ yR yP) :
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:75:/-- **`hnorm` from the print** (PROVED from the PRINT `CCLThm2_15Applied`): if every anchored
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:78:theorem hnorm_of_print {Anchor : HeegnerPointData E → Prop} (hprint : CCLThm2_15Applied E Anchor)
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:82:    (htr : ∀ D, Anchor D → HeegnerTransportAt ρ HP U t D d q σ (yR D) (yP D)) :
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:87:  exact ⟨D, hA, hnorm_of_normRelations ρ HP U t D hD (hadm D hA) (hsplit D hA) (htr D hA)⟩
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:93:/-- **Non-vacuity of `HeegnerTransportAt`**: for the zero system (`D.y = 0`), the zero comparison
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:96:theorem nonVacuity_transport {E : WeierstrassCurve ℚ} {G : Type*} [Group G] {A : Type*}
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:101:    HeegnerTransportAt ρ HP U t (HeegnerPointData.mk (E := E) DK N H (fun _ => 0) (fun _ _ => rg)
ZInQKernel/Contrib/CloudB3E2Norm/H20PresAssembly.lean:17:* the norm relation `hnorm` (`H20HeegnerNorm.hnorm_of_print`, the Cai–Chen–Liu print), the division
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClass.lean:44:* **`gx_step_anchored`** (PROVED from the PRINT `CCLThm2_15Applied E (FullAnchor …)`): for the
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClass.lean:473:`CCLThm2_15Applied E (FullAnchor …)`; tex 2914–2936, 3915, 4157–4172): there is an anchored datum
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClass.lean:484:    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} (hprint : CCLThm2_15Applied E (FullAnchor E K cp emb κ)) :
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassMatch.lean:156:(PROVED from the PRINT `CCLThm2_15Applied E (FullAnchor …)` and the ELLIOT `ThetaOfDelta f`;
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassMatch.lean:162:    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} (hprint : CCLThm2_15Applied E (FullAnchor E K cp emb κ)) :
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:35:* **`gx_step_heegner`** (PROVED from the PRINT `CCLThm2_15Applied E (FullAnchor …)`): the step
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:534:`CCLThm2_15Applied E (FullAnchor …)`; tex 2914–2936, 3080–3084, 3915, 4157–4172): there is an
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:543:    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} (hprint : CCLThm2_15Applied E (FullAnchor E K cp emb κ)) :
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20HeegnerNorm
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:10:`H20HeegnerNorm.lean` takes the norm relation `hnorm` from the print `CCLThm2_15Applied` through the
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:11:GLUE `HeegnerTransportAt`: an additive comparison `j : E(ℚ̄) → D` into the ambient module of points,
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:18:* **`HeegnerTransportOn`** (Prop; GLUE form): as `HeegnerTransportAt`, with `j` defined on an
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:20:* **`hnorm_of_normRelations_on`**, **`hnorm_of_print_on`** (PROVED): the norm relation from
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:21:  `D.NormRelations` (resp. the print) and `HeegnerTransportOn`, as in `H20HeegnerNorm.lean`.
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:39:Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied`; the dictionary is the GLUE.
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:65:`HeegnerTransportAt`. Kind: definition (Prop). -/
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:106:`CCLThm2_15Applied`). -/
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:107:theorem hnorm_of_print_on {Anchor : HeegnerPointData E → Prop}
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:108:    (hprint : CCLThm2_15Applied E Anchor) {d q : ℕ} (σ : G) (yR yP : HeegnerPointData E → Dm)
ZInQKernel/Contrib/OneProof/RC/PrintsArith/Bundle.lean:14:statements (`KatoZetaLeaf`, `CCLThm2_15Applied`, `CJReductionData.Thm3_1KappaOne`) are not bundled:
ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean:164:def CCLThm2_15Applied (E : WeierstrassCurve ℚ) (Anchor : HeegnerPointData E → Prop) : Prop :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:16:* `chainCond` (definition): the chain conductors `d_0 = d`, `d_{j+1} = d_j · ps[j]`;
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:17:  `classSupport` (definition): the support `S₀ ∪ {v ∣ d_j}` of the division points of `y_{d_j}`;
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:18:* **`E2ChainInputs A t`** (data): the inputs of lane E2's construction that do not follow from
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:30:* **`E2ChainInputs.g`** (definition): `g_j` = lane E2's `gx` of `heegnerActual … d_j` on the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:32:* **`E2ChainInputs.hG`** (PROVED): `g_{i+1} = pointFactor a_i z_i z_i⁻¹ • g_i + d b_i` with the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:35:* **`E2ChainInputs.hloc`** (PROVED): the local lifts, lane E2's `exists_ux`;
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:36:* **`e2Provider A t I : StageClassesAt A (t + 1)`** (definition).
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:54:open ZInQ.Manuscript.RC.PrintsArith (Qbar HeegnerPointData CCLThm2_15Applied)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:66:def chainCond (d : ℕ) (ps : List ℕ) : ℕ → ℕ
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:68:  | j + 1 => chainCond d ps j * ps.getD j 1
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:71:theorem dvd_chainCond (d : ℕ) (ps : List ℕ) : ∀ j, d ∣ chainCond d ps j
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:73:  | j + 1 => (dvd_chainCond d ps j).mul_right _
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:84:def classSupport (A : ActualPresentation C D Fam x) (d j : ℕ) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:86:  A.S₀ ∪ {v | ((chainCond d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:91:theorem ActualPresentation.ps_getD_pos (A : ActualPresentation C D Fam x) (j : ℕ) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:101:theorem ActualPresentation.ps_getD_prime (A : ActualPresentation C D Fam x) {i : ℕ}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:109:structure E2ChainInputs (A : ActualPresentation C D Fam x) (t : ℕ) where
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:118:  print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:143:    6 * chainCond d A.ps i * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:156:namespace E2ChainInputs
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:158:variable {A : ActualPresentation C D Fam x} {t : ℕ} (I : E2ChainInputs A t)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:160:attribute [local instance] E2ChainInputs.hf
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:164:theorem chainCond_pos : ∀ j, 0 < chainCond I.d A.ps j
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:166:  | j + 1 => Nat.mul_pos (chainCond_pos j) (A.ps_getD_pos j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:170:theorem chainCond_coprime : ∀ j, Nat.Coprime (chainCond I.d A.ps j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:176:    · refine (Nat.Prime.coprime_iff_not_dvd (A.ps_getD_prime hj)).2 fun h => I.hq j hj ?_
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:177:      exact h.trans ⟨3 * chainCond I.d A.ps j, by ring⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:185:    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∉ (A.pl (p, c)).asIdeal
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:191:    change (((chainCond I.d A.ps j * A.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ (A.pl (p, c)).asIdeal at h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:204:    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ A.S
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:207:    change (((chainCond I.d A.ps j * A.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ v.asIdeal at h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:220:theorem classSupport_subset (j : ℕ) : classSupport A I.d j ⊆ A.S := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:228:    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupport A I.d j :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:234:    ((2 ^ (t + 1) : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupport A I.d j := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:241:theorem hgood' (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ classSupport A I.d j →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:249:    (A.place jj).1 ∉ classSupport A I.d j := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:256:theorem hfd_cond (j : ℕ) : I.f ∣ chainCond I.d A.ps j := I.hfd.trans (dvd_chainCond _ _ j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:277:theorem hcop (j : ℕ) : Nat.Coprime (chainCond I.d A.ps j) (I.datum.N * I.datum.DK.natAbs) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:284:    I.datum.Admissible (chainCond I.d A.ps i) (A.ps.getD i 1) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:285:  refine ⟨I.chainCond_pos i, ?_, A.ps_getD_prime hi, ?_⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:301:  haveI : NeZero (chainCond I.d A.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:306:      A.place I.anchor (I.classSupport_subset j) (chainCond I.d A.ps j) (I.hcop j) (I.hSd j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:330:theorem hwd {i : ℕ} (hi : i < A.ps.length) [NeZero (chainCond I.d A.ps i)] :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:333:      ((chainCond I.d A.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:335:        (CST.conductorOrder C.K (chainCond I.d A.ps i)).conductorModulus ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:337:        (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := C.K) (chainCond I.d A.ps i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:340:  have hnot : ((chainCond I.d A.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:345:  have hJ := mem_primeTo_of_not_mem (chainCond I.d A.ps i) (NeZero.ne _) w.1 hnot
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:407:  have : NeZero (chainCond I.d A.ps i) := ⟨(I.chainCond_pos i).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:408:  have : NeZero (A.ps.getD i 1) := ⟨(A.ps_getD_pos i).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:434:  have : NeZero (chainCond I.d A.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:447:      A.place I.anchor (I.classSupport_subset j) (chainCond I.d A.ps j) (I.hcop j) (I.hSd j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:452:end E2ChainInputs
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:459:def e2Provider (A : ActualPresentation C D Fam x) (t : ℕ) (I : E2ChainInputs A t) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18Leaf.lean:21:  `CommonCoordinateInputsGenuineE2` discharges it);
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18Leaf.lean:37:    included; `CommonCoordinateInputsGenuineE2` (`CommonCoordinate18LeafE2.lean`) pins it to lane
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18Leaf.lean:38:    E2's classes (`e2Provider`);
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18Leaf.lean:52:`CommonCoordinateInputsGenuineE2` the provider is lane E2's Kummer classes of the actual points
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:2:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:15:(`e2Provider`, `CommonCoordinate18E2.lean`, from lane E2's `gx`, `ux_spec`, `heegnerActual` and
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:18:* `e2ProviderOn`: the provider at the retained stages (all positive) from the inputs
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:19:  `E2ChainInputs` at each of them;
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:20:* **`CommonCoordinateInputsGenuineE2 D`**: `CommonCoordinateInputsGenuineK D` with `HC` the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:25:* **`commonCoordinateInputsGenuineK_of_E2`**, **`commonCoordinateInputsNF_of_genuineE2`**,
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:26:  **`commonCoordinateTarget_of_genuineE2`** (PROVED).
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:29:Kummer classes of the actual points (`gx_step_heegner_at`, from the PRINT `CCLThm2_15Applied`
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:31:remaining inputs of the classes are the fields of `E2ChainInputs`: the PRINT (Cai–Chen–Liu with the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:56:4385–4451): at a stage `t + 1` of `G` the provider `e2Provider` of the inputs at that stage; at
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:58:noncomputable def e2ProviderOn (A : ActualPresentation C D Fam x) {G : Set ℕ}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:59:    (I : ∀ t, t + 1 ∈ G → E2ChainInputs A t) : ∀ s, s ∈ G → StageClassesAt A s
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:61:  | t + 1, h => e2Provider A t (I t h)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:64:theorem e2ProviderOn_succ (A : ActualPresentation C D Fam x) {G : Set ℕ}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:65:    (I : ∀ t, t + 1 ∈ G → E2ChainInputs A t) (t : ℕ) (h : t + 1 ∈ G) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:66:    e2ProviderOn A I (t + 1) h = e2Provider A t (I t h) :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:71:pinned to lane E2's (`e2ProviderOn`), one base conductor per address, and the injectivity of the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:74:structure CommonCoordinateInputsGenuineE2 {ℓ : ℕ} (D : RCData ℓ) : Prop where
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:86:  conductor (PRINT, ELLIOT, definitions: `E2ChainInputs`), and the genuine stage chains with
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:94:          (I : ∀ t, t + 1 ∈ G → E2ChainInputs A t),
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:97:            (e2ProviderOn A I))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:101:theorem commonCoordinateInputsGenuineK_of_E2 {ℓ : ℕ} {D : RCData ℓ}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:102:    (h : CommonCoordinateInputsGenuineE2 D) : CommonCoordinateInputsGenuineK D := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:108:  exact ⟨A, hΦ, hPk, hdec, G, e2ProviderOn A I, hGs⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:112:theorem commonCoordinateInputsNF_of_genuineE2 {ℓ : ℕ} {D : RCData ℓ}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:113:    (h : CommonCoordinateInputsGenuineE2 D) : CommonCoordinateInputsNF D :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:114:  commonCoordinateInputsNF_of_genuineK (commonCoordinateInputsGenuineK_of_E2 h)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:118:theorem commonCoordinateTarget_of_genuineE2 {ℓ : ℕ} {D : RCData ℓ}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:119:    (h : CommonCoordinateInputsGenuineE2 D) : CommonCoordinateTarget D :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:120:  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_genuineE2 h)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:3:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:37:  `CommonCoordinate18E2.lean`, with `staged_stageFrobInput` for the junction and `P.places`,
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:193:  P.S₀ s ∪ {v | ((chainCond d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:198:theorem StagedPresentation.ps_getD_pos (P : StagedPresentation C D Fam x G.toFamily) (j : ℕ) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:208:theorem StagedPresentation.ps_getD_prime (P : StagedPresentation C D Fam x G.toFamily) {i : ℕ}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:264:    6 * chainCond d P.ps i * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:285:theorem chainCond_pos : ∀ j, 0 < chainCond I.d P.ps j
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:287:  | j + 1 => Nat.mul_pos (chainCond_pos j) (P.ps_getD_pos j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:291:theorem chainCond_coprime : ∀ j, Nat.Coprime (chainCond I.d P.ps j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:297:    · refine (Nat.Prime.coprime_iff_not_dvd (P.ps_getD_prime hj)).2 fun h => I.hq j hj ?_
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:298:      exact h.trans ⟨3 * chainCond I.d P.ps j, by ring⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:306:    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∉ (P.pl (p, c)).asIdeal
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:312:    change (((chainCond I.d P.ps j * P.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ (P.pl (p, c)).asIdeal at h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:325:    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S (t + 1)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:328:    change (((chainCond I.d P.ps j * P.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ v.asIdeal at h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:349:    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupportS P (t + 1) I.d j :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:425:theorem hcop (j : ℕ) : Nat.Coprime (chainCond I.d P.ps j) (I.datum.N * I.datum.DK.natAbs) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:432:    I.datum.Admissible (chainCond I.d P.ps i) (P.ps.getD i 1) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:433:  refine ⟨I.chainCond_pos i, ?_, P.ps_getD_prime hi, ?_⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:447:theorem hα (j : ℕ) [NeZero (chainCond I.d P.ps j)] :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:449:        (heegnerL (chainCond I.d P.ps j) (I.hSd j)) ≤
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:454:  exact h I.hθ (dvd_chainCond I.d P.ps j) (I.hSd j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:460:  haveI : NeZero (chainCond I.d P.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:465:    I.anchor (I.classSupport_subset j) (chainCond I.d P.ps j) (I.hcop j) (I.hSd j) (I.hm j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:508:theorem hwd {i : ℕ} (hi : i < P.ps.length) [NeZero (chainCond I.d P.ps i)] :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:511:      ((chainCond I.d P.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:513:        (CST.conductorOrder C.K (chainCond I.d P.ps i)).conductorModulus ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:515:        (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := C.K) (chainCond I.d P.ps i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:518:  have hnot : ((chainCond I.d P.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:523:  have hJ := mem_primeTo_of_not_mem (chainCond I.d P.ps i) (NeZero.ne _) w.1 hnot
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:590:  have : NeZero (chainCond I.d P.ps i) := ⟨(I.chainCond_pos i).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:591:  have : NeZero (P.ps.getD i 1) := ⟨(P.ps_getD_pos i).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:600:    (I.hm i) (I.hm (i + 1)) (I.hgood' i) (I.hgood' (i + 1)) I.d I.hθ (dvd_chainCond I.d P.ps i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:638:  have : NeZero (chainCond I.d P.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19Theta.lean:16:Two inputs of lane E2's class provider (`CommonCoordinate18E2.lean`) are derived here.
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19Theta.lean:209:`E2ChainInputs` (`CommonCoordinate18E2.lean`). -/
docs/research/ccl-unit-index.md:30:input, `G.r_prime`, `dvd_thetaCond_r`, `I.hfd`, `dvd_chainCond` and
docs/research/ccl-unit-index.md:40:The generic `H20HeegnerNorm` and `H20Transport` lemmas have an admissible
docs/research/ccl-unit-index.md:50:inherit the unrestricted output. The old `CommonCoordinate18E2` provider
docs/research/ccl-unit-index.md:57:`CommonCoordinate18LeafE2`, `CommonCoordinate19Leaf`, wrappers and
docs/research/ccl-unit-index2.md:96:- Delete `OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean`, including
docs/research/ccl-unit-index2.md:97:  `e2ProviderOn`, `e2ProviderOn_succ`, `CommonCoordinateInputsGenuineE2`,
docs/research/ccl-unit-index2.md:98:  `commonCoordinateInputsGenuineK_of_E2`,
docs/research/ccl-unit-index2.md:99:  `commonCoordinateInputsNF_of_genuineE2` and
docs/research/ccl-unit-index2.md:100:  `commonCoordinateTarget_of_genuineE2`.
docs/research/ccl-unit-index2.md:101:- Move `chainCond` and `dvd_chainCond` out of
docs/research/ccl-unit-index2.md:102:  `OneProof/RC/Wiring/CommonCoordinate18E2.lean` and point the staged
docs/research/ccl-unit-index2.md:104:  the transport. Then delete that old file, including `classSupport`,
docs/research/ccl-unit-index2.md:105:  `ActualPresentation.ps_getD_pos`, `ActualPresentation.ps_getD_prime`,
docs/research/ccl-unit-index2.md:106:  `E2ChainInputs` and its entire namespace, and `e2Provider`.
docs/research/ccl-unit-index2.md:107:- Delete `CloudB3E2Norm/H20HeegnerNorm.lean`, including
docs/research/ccl-unit-index2.md:108:  `HeegnerTransportAt`, `hnorm_of_normRelations`, `hnorm_of_print`
docs/research/ccl-unit-index2.md:109:  and `nonVacuity_transport`. In `H20Transport.lean`, import
docs/research/ccl-unit-index2.md:110:  `PrintsArith.Heegner` directly and delete `hnorm_of_print_on`.
docs/research/ccl-unit-index2.md:111:  In `H20Anchor.lean`, delete `CCLGenuine` and
docs/research/ccl-unit-index2.md:112:  `hnorm_of_genuine_print`. Keep the subgroup and full-anchor dictionaries
docs/research/ccl-unit-index2.md:119:  `CCLThm2_15Applied` from `PrintsArith/Heegner.lean`. The relation
docs/research/rc-cm-field.md:28:| `RC/PreparedParam/Prints.lean`, `RC/PrintsArith/Heegner.lean` and the shared CST height print | `CMFieldOfDefinition` is the **existing GLUE print (unread)**, with exactly the target quantifiers and \(\exists\iota:H_O\to_{\mathbb Q}\mathbb C,\ x\in X(H_O),\ x.\mathrm{map}(\iota)=X.\mathrm{complexPoint}(\mathrm{cmPoint}\ A\ B\ d)\). It cannot supply its own discharge. `CCLThm2_15Applied E Anchor` is the applied trace input: there exists a `HeegnerPointData E` with its inert and split norm relations **and** the supplied anchor. The zero-system theorem shows that the trace relations alone do not pin the points. The CST height input starts with an elliptic point over \(H_O\) and a complex comparison; it does not give the \(X_0(N)\)-point. |
docs/research/rc-cm-scope.md:72:The anchor quantifies over the two old Galois slots in its conclusion. It supplies no `CCLGenuine` norm-relations proof or identification of a separately chosen witness to that print with the points constructed here.
docs/research/rc-cm-scope2.md:74:The anchor quantifies over the two old Galois slots in its conclusion. It supplies no `CCLGenuine` norm-relations proof or identification of a separately chosen witness to that print with the points constructed here.
docs/research/rc-cm-scope3.md:102:The anchor quantifies over the two old Galois slots in its conclusion. It supplies no `CCLGenuine` norm-relations proof or identification of a separately chosen witness to that print with the points constructed here.
docs/research/rc-heegner-anchor.md:37:| `genuineHeegnerAnchor` | There exist `H : ℕ → IntermediateField ℚ ℚ̄` and `y : ℕ → E(ℚ̄)` such that for all `relGal, frob`, the record `⟨D_K, N, H, y, relGal, frob⟩` satisfies `GenuineHeegnerAnchor E K p ι`. At each admissible `d` the proof takes `H d = e.fieldRange` and `y d` to be the inclusion of `π(x_d) ∈ E(H d)`. These supply the coordinates and analytic comparison of `CCLGenuine`'s anchor. The fields and points outside the anchor's domain are filled with the bottom intermediate field and zero, respectively. |
docs/research/rc-heegner-anchor.md:42:`NormRelations` conjunct of `CCLGenuine`, nor does it identify an
docs/research/rc-param-at-scale.md:69:| A CCLGenuine consumer must supply the compatible oriented family over the actual class fields, the chosen embeddings and the chart equalities, the Hecke relation for `φ` and `T_q[∞]=(q+1)[∞]`, and the CCL trace-to-Galois comparisons. No declaration named `CCLGenuine` was available on this base. The theorem supplies a common π and its values, with no trace claim. | 2915–2936; sibling `rc-heegner-values` for the CCL route; geometric Hecke/cusp comparison also missing theory. |
scratch/ccl-unit-index/consumers.md:4:for the names of the direct users and the `E2ChainInputs` and `E2ChainInputsS` providers.
scratch/ccl-unit-index/consumers.md:9:| `CloudB3E2Norm/H20HeegnerNorm.lean`: `hnorm_of_normRelations`, `hnorm_of_print` | Arbitrary `d`, admissibility, split Jacobi value and additive transport. The print wrapper has an arbitrary anchor with no unit, level or split-at-two condition. |
scratch/ccl-unit-index/consumers.md:10:| `CloudB3E2Norm/H20Transport.lean`: `hnorm_of_normRelations_on`, `hnorm_of_print_on` | Same conditions, with transport on an additive subgroup. |
scratch/ccl-unit-index/consumers.md:12:| `CloudB3E2Norm/H20Anchor.lean`: `CCLGenuine`, `hnorm_of_genuine_print` | The anchor pins the discriminant, the newform level and a Heegner form at conductor one. The field, curve and level are generic; no `4 ∣ N` or split-at-two premise. |
scratch/ccl-unit-index/consumers.md:17:| `OneProof/RC/Wiring/CommonCoordinate18E2.lean`: `E2ChainInputs.print`, `datum`/anchor and `hG` calls of `gx_step_heegner_at` | The older presentation has `hd : 0 < d`, `f ∣ d` and `[NeZero f]`; none of these is a lower bound greater than one. The curve is explicit, but no `4 ∣ newformLevel (Ecurve ℓ)` theorem was found. |
scratch/ccl-unit-index/consumers.md:18:| `OneProof/RC/Wiring/CommonCoordinate19E2.lean`: `E2ChainInputsS.print`, `datum`/anchor and `hG` calls of `gx_step_heegner_at` | `G.r_prime (t+1)`, `dvd_thetaCond_r`, `I.hfd`, `dvd_chainCond`, and `I.chainCond_pos` give `1 < chainCond I.d P.ps i`. |
scratch/ccl-unit-index/consumers.md:22:| `OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean`, `OneProof/RC/Wiring/CommonCoordinate19Leaf.lean` | Downstream packages use `e2Provider` and `e2ProviderS`, respectively; they do not apply the print. |
scratch/ccl-unit-index/consumers.md:26:The two direct module importers of `Heegner.lean` are `H20HeegnerNorm.lean` and `Bundle.lean`.
scratch/ccl-unit-index/log.md:25:- L176–177: `CCLThm2_15Applied E Anchor := ∃ D : HeegnerPointData E,
scratch/ccl-unit-index2/builds.txt:36:PASS ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18LeafE2
scratch/ccl-unit-index2/closure.txt:18:   ZInQKernel.Contrib.CloudB3E2Norm.H20HeegnerNorm
scratch/ccl-unit-index2/closure.txt:25:   ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
scratch/ccl-unit-index2/closure.txt:27:   ZInQKernel.Contrib.CloudB3E2Norm.H20HeegnerNorm
scratch/ccl-unit-index2/consumer-refs.txt:1:HEAD:ZInQKernel/Contrib/CloudB3E1RingClass/SupportReq.lean:53:open ZInQ.Manuscript.RC.PrintsArith (Qbar CCLThm2_15Applied)
scratch/ccl-unit-index2/consumer-refs.txt:2:HEAD:ZInQKernel/Contrib/CloudB3E1RingClass/SupportReq.lean:127:    (print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ))
scratch/ccl-unit-index2/consumer-refs.txt:6:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/CochainNorm.lean:60:   actual classes with the classes of the Heegner points `y_T` (the anchor of `CCLThm2_15Applied`).
scratch/ccl-unit-index2/consumer-refs.txt:8:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:37:open ZInQ.Manuscript.RC.PrintsArith (Qbar CCLThm2_15Applied)
scratch/ccl-unit-index2/consumer-refs.txt:9:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:137:    (print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ))
scratch/ccl-unit-index2/consumer-refs.txt:10:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/E2ChainGood.lean:31:open ZInQ.Manuscript.RC.PrintsArith (Qbar CCLThm2_15Applied)
scratch/ccl-unit-index2/consumer-refs.txt:11:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/E2ChainGood.lean:116:    (print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ))
scratch/ccl-unit-index2/consumer-refs.txt:12:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/GlobalCochain.lean:48:(`CCLThm2_15Applied`'s anchor); (5) the local components `hU`, `hL` (item 3 of the
scratch/ccl-unit-index2/consumer-refs.txt:13:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:12:`RC/PrintsArith/Heegner.lean` states the print as `CCLThm2_15Applied E Anchor :=
scratch/ccl-unit-index2/consumer-refs.txt:15:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:27:* `CCLGenuine E K p ι := CCLThm2_15Applied E (GenuineHeegnerAnchor …)` (definition): the
scratch/ccl-unit-index2/consumer-refs.txt:16:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:36:* **`hnorm_of_genuine_print`** (PROVED): from `CCLGenuine` and the remaining field-level dictionary
scratch/ccl-unit-index2/consumer-refs.txt:17:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:40:Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied` with the anchor; the analytic
scratch/ccl-unit-index2/consumer-refs.txt:18:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:95:def CCLGenuine (p : CSTParam E) (ι : Qbar →ₐ[ℚ] ℂ) : Prop :=
scratch/ccl-unit-index2/consumer-refs.txt:19:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:96:  CCLThm2_15Applied E (GenuineHeegnerAnchor E K p ι)
scratch/ccl-unit-index2/consumer-refs.txt:20:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:131:`CCLGenuine`): there is an anchored datum `D` (its points are the images of CM points, `D.N = N_E`,
scratch/ccl-unit-index2/consumer-refs.txt:21:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean:137:    (hprint : CCLGenuine E K p ι) :
scratch/ccl-unit-index2/consumer-refs.txt:23:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:11:The print `CCLThm2_15Applied` is existential in the datum, so these descriptions must be part of the
scratch/ccl-unit-index2/consumer-refs.txt:24:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:34:  Heegner points from the anchored print `CCLThm2_15Applied E (FullAnchor …)` alone, given the
scratch/ccl-unit-index2/consumer-refs.txt:25:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:444:(PROVED from the PRINT `CCLThm2_15Applied E (FullAnchor …)`): there is an anchored datum `D` with
scratch/ccl-unit-index2/consumer-refs.txt:26:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:452:    (hprint : CCLThm2_15Applied E (FullAnchor E K p ι κ)) :
scratch/ccl-unit-index2/consumer-refs.txt:28:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Dictionary.lean:272:(PROVED from the PRINT `CCLThm2_15Applied` and the field-level dictionary (i)–(iv), tex 2914–2936):
scratch/ccl-unit-index2/consumer-refs.txt:30:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:16:`t` a transversal). The tree's print is `CCLThm2_15Applied E Anchor` (`PrintsArith/Heegner.lean`):
scratch/ccl-unit-index2/consumer-refs.txt:31:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:17:some `HeegnerPointData D` satisfying `D.NormRelations` and the anchor; the split clause of
scratch/ccl-unit-index2/consumer-refs.txt:32:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:25:* **`hnorm_of_normRelations`** (PROVED): `D.NormRelations`, admissibility, `q` split in `K` and
scratch/ccl-unit-index2/consumer-refs.txt:33:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:27:* **`hnorm_of_print`** (PROVED): from the print `CCLThm2_15Applied E Anchor`, if every anchored
scratch/ccl-unit-index2/consumer-refs.txt:34:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:33:Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied` and the GLUE `HeegnerTransportAt`.
scratch/ccl-unit-index2/consumer-refs.txt:35:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:60:clause of `D.NormRelations` at an admissible `(d, q)` with `q` split in `K`, transported by
scratch/ccl-unit-index2/consumer-refs.txt:36:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:62:theorem hnorm_of_normRelations (D : HeegnerPointData E) (hD : D.NormRelations) {d q : ℕ}
scratch/ccl-unit-index2/consumer-refs.txt:37:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:75:/-- **`hnorm` from the print** (PROVED from the PRINT `CCLThm2_15Applied`): if every anchored
scratch/ccl-unit-index2/consumer-refs.txt:38:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:78:theorem hnorm_of_print {Anchor : HeegnerPointData E → Prop} (hprint : CCLThm2_15Applied E Anchor)
scratch/ccl-unit-index2/consumer-refs.txt:40:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20PresClass.lean:44:* **`gx_step_anchored`** (PROVED from the PRINT `CCLThm2_15Applied E (FullAnchor …)`): for the
scratch/ccl-unit-index2/consumer-refs.txt:41:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20PresClass.lean:473:`CCLThm2_15Applied E (FullAnchor …)`; tex 2914–2936, 3915, 4157–4172): there is an anchored datum
scratch/ccl-unit-index2/consumer-refs.txt:42:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20PresClass.lean:484:    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} (hprint : CCLThm2_15Applied E (FullAnchor E K cp emb κ)) :
scratch/ccl-unit-index2/consumer-refs.txt:45:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassMatch.lean:156:(PROVED from the PRINT `CCLThm2_15Applied E (FullAnchor …)` and the ELLIOT `ThetaOfDelta f`;
scratch/ccl-unit-index2/consumer-refs.txt:47:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassMatch.lean:162:    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} (hprint : CCLThm2_15Applied E (FullAnchor E K cp emb κ)) :
scratch/ccl-unit-index2/consumer-refs.txt:49:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:35:* **`gx_step_heegner`** (PROVED from the PRINT `CCLThm2_15Applied E (FullAnchor …)`): the step
scratch/ccl-unit-index2/consumer-refs.txt:50:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:534:`CCLThm2_15Applied E (FullAnchor …)`; tex 2914–2936, 3080–3084, 3915, 4157–4172): there is an
scratch/ccl-unit-index2/consumer-refs.txt:51:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:543:    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} (hprint : CCLThm2_15Applied E (FullAnchor E K cp emb κ)) :
scratch/ccl-unit-index2/consumer-refs.txt:53:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:10:`H20HeegnerNorm.lean` takes the norm relation `hnorm` from the print `CCLThm2_15Applied` through the
scratch/ccl-unit-index2/consumer-refs.txt:54:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:21:  `D.NormRelations` (resp. the print) and `HeegnerTransportOn`, as in `H20HeegnerNorm.lean`.
scratch/ccl-unit-index2/consumer-refs.txt:55:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:39:Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied`; the dictionary is the GLUE.
scratch/ccl-unit-index2/consumer-refs.txt:57:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:106:`CCLThm2_15Applied`). -/
scratch/ccl-unit-index2/consumer-refs.txt:58:HEAD:ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:108:    (hprint : CCLThm2_15Applied E Anchor) {d q : ℕ} (σ : G) (yR yP : HeegnerPointData E → Dm)
scratch/ccl-unit-index2/consumer-refs.txt:60:HEAD:ZInQKernel/Contrib/OneProof/RC/PrintsArith/Bundle.lean:14:statements (`KatoZetaLeaf`, `CCLThm2_15Applied`, `CJReductionData.Thm3_1KappaOne`) are not bundled:
scratch/ccl-unit-index2/consumer-refs.txt:61:HEAD:ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean:37:(stated by the shared top layer, `CST.CSTThm11Split`), so `CCLThm2_15Applied` is parametric in an
scratch/ccl-unit-index2/consumer-refs.txt:65:HEAD:ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean:176:def CCLThm2_15Applied (E : WeierstrassCurve ℚ) (Anchor : HeegnerPointData E → Prop) : Prop :=
scratch/ccl-unit-index2/consumer-refs.txt:67:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:26:  (`hadmD`, `hsplitD`), and at every step the hypotheses of lane E2's `gx_step_heegner_at`:
scratch/ccl-unit-index2/consumer-refs.txt:68:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:33:  leaf's values at the stage, from `gx_step_heegner_at` and the junction `stepFactor_eq`
scratch/ccl-unit-index2/consumer-refs.txt:69:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:54:open ZInQ.Manuscript.RC.PrintsArith (Qbar HeegnerPointData CCLThm2_15Applied)
scratch/ccl-unit-index2/consumer-refs.txt:70:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:56:  gx_step_heegner_at exists_ux stageIsoA eK alphaStage alphaShap hα_of_theta groupRingTop)
scratch/ccl-unit-index2/consumer-refs.txt:71:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:118:  print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ)
scratch/ccl-unit-index2/consumer-refs.txt:72:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:261:`D` of `gx_step_heegner_at` for the actual presentation at the stage `t + 1`.
scratch/ccl-unit-index2/consumer-refs.txt:73:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:265:  Classical.choose (gx_step_heegner_at (Ecurve ℓ) A.hS A.hS (Set.Subset.refl A.S) (t + 1) A.sh
scratch/ccl-unit-index2/consumer-refs.txt:74:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:272:  (Classical.choose_spec (gx_step_heegner_at (Ecurve ℓ) A.hS A.hS (Set.Subset.refl A.S) (t + 1)
scratch/ccl-unit-index2/consumer-refs.txt:75:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:397:stage, from `gx_step_heegner_at` at the two places of the step (`habove` from `A.places`,
scratch/ccl-unit-index2/consumer-refs.txt:76:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:409:  obtain ⟨hA, -, hall⟩ := Classical.choose_spec (gx_step_heegner_at (Ecurve ℓ) A.hS A.hS
scratch/ccl-unit-index2/consumer-refs.txt:77:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:457:`gx_step_heegner_at` at the leaf's values and the local lifts from `exists_ux`.
scratch/ccl-unit-index2/consumer-refs.txt:78:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:16:`gx_step_heegner_at`):
scratch/ccl-unit-index2/consumer-refs.txt:79:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:29:Kummer classes of the actual points (`gx_step_heegner_at`, from the PRINT `CCLThm2_15Applied`
scratch/ccl-unit-index2/consumer-refs.txt:80:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:55:open ZInQ.Manuscript.RC.PrintsArith (Qbar HeegnerPointData CCLThm2_15Applied)
scratch/ccl-unit-index2/consumer-refs.txt:82:HEAD:ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:225:  print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ)
scratch/ccl-unit-index2/consumers.md:4:for the names of the direct users and the `E2ChainInputs` and `E2ChainInputsS` providers.
scratch/ccl-unit-index2/consumers.md:9:| `CloudB3E2Norm/H20HeegnerNorm.lean`: `hnorm_of_normRelations`, `hnorm_of_print` | Arbitrary `d`, admissibility, split Jacobi value and additive transport. The print wrapper has an arbitrary anchor with no unit, level or split-at-two condition. |
scratch/ccl-unit-index2/consumers.md:10:| `CloudB3E2Norm/H20Transport.lean`: `hnorm_of_normRelations_on`, `hnorm_of_print_on` | Same conditions, with transport on an additive subgroup. |
scratch/ccl-unit-index2/consumers.md:12:| `CloudB3E2Norm/H20Anchor.lean`: `CCLGenuine`, `hnorm_of_genuine_print` | The anchor pins the discriminant, the newform level and a Heegner form at conductor one. The field, curve and level are generic; no `4 ∣ N` or split-at-two premise. |
scratch/ccl-unit-index2/consumers.md:17:| `OneProof/RC/Wiring/CommonCoordinate18E2.lean`: `E2ChainInputs.print`, `datum`/anchor and `hG` calls of `gx_step_heegner_at` | The older presentation has `hd : 0 < d`, `f ∣ d` and `[NeZero f]`; none of these is a lower bound greater than one. The curve is explicit, but no `4 ∣ newformLevel (Ecurve ℓ)` theorem was found. |
scratch/ccl-unit-index2/consumers.md:18:| `OneProof/RC/Wiring/CommonCoordinate19E2.lean`: `E2ChainInputsS.print`, `datum`/anchor and `hG` calls of `gx_step_heegner_at` | `G.r_prime (t+1)`, `dvd_thetaCond_r`, `I.hfd`, `dvd_chainCond`, and `I.chainCond_pos` give `1 < chainCond I.d P.ps i`. |
scratch/ccl-unit-index2/consumers.md:22:| `OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean`, `OneProof/RC/Wiring/CommonCoordinate19Leaf.lean` | Downstream packages use `e2Provider` and `e2ProviderS`, respectively; they do not apply the print. |
scratch/ccl-unit-index2/consumers.md:26:The two direct module importers of `Heegner.lean` are `H20HeegnerNorm.lean` and `Bundle.lean`.
scratch/ccl-unit-index2/log.md:23:transport via `CommonCoordinate19E2.lean` importing `CommonCoordinate18E2.lean`.
scratch/ccl-unit-index2/log.md:37:- `CCLThm2_15Applied E Anchor := ∃ D : HeegnerPointData E, D.NormRelations ∧ Anchor D`.
scratch/rc-cm-field/log.md:19:| RC `CMFieldOfDefinition`, `CCLThm2_15Applied`, CST `IsHeegnerForm` and `cmPoint` | Target GLUE (unread); anchored trace input; definitions. `∃ ι : H →ₐ[ℚ] ℂ, ∃ x : FieldPoint X.overQ H, x.map ι = X.complexPoint (cmPoint A B d)`. CCL applied print gives a system satisfying norm relations and a supplied anchor. CST's height statement uses a field-valued point as input. |
scratch/rc-lane-batch-1120/targets-merged.txt:124:ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18LeafE2
scratch/rc-lane-batch-1120/targets.txt:927:ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
scratch/rc-lane-batch-1120/targets.txt:929:ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18LeafE2
```

## Qualified references to the old structures and namespace

```text
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:30:* **`E2ChainInputs.g`** (definition): `g_j` = lane E2's `gx` of `heegnerActual … d_j` on the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:32:* **`E2ChainInputs.hG`** (PROVED): `g_{i+1} = pointFactor a_i z_i z_i⁻¹ • g_i + d b_i` with the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:35:* **`E2ChainInputs.hloc`** (PROVED): the local lifts, lane E2's `exists_ux`;
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:160:attribute [local instance] E2ChainInputs.hf
```

## Members and projections in the deleted modules

```text
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:4:# The Heegner norm relation `hnorm` from the print (Cai–Chen–Liu, Theorem 2.15)
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:16:`t` a transversal). The tree's print is `CCLThm2_15Applied E Anchor` (`PrintsArith/Heegner.lean`):
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:17:some `HeegnerPointData D` satisfying `D.NormRelations` and the anchor; the split clause of
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:18:`NormRelations` is the same relation in `E(ℚ̄)`, with `D.relGal d q`, `D.frob d q`, `D.y`.
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:22:  listed as open earlier): an additive equivariant comparison `j : E(ℚ̄) → D` carrying `D.y (d q)` to
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:23:  `y_R` and `D.y d` to `y_P`, a bijection between the transversal `H_P/U` and `D.relGal d q` compatible
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:24:  with `j` on `D.y (d q)`, and `σ`, `σ⁻¹` matching `D.frob d q`, `(D.frob d q)⁻¹` on `D.y d`.
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:27:* **`hnorm_of_print`** (PROVED): from the print `CCLThm2_15Applied E Anchor`, if every anchored
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:28:  `D` admits the transport, there is a `D` (the print's) with `hnorm`. The anchor needed is the one
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:49:/-- **The transport of the Heegner point data to the ambient module of points** at `(d, q)`
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:51:def HeegnerTransportAt (D : HeegnerPointData E) (d q : ℕ) (σ : G) (yR yP : Dm) : Prop :=
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:52:  ∃ (j : (E⁄Qbar).toAffine.Point →+ Dm) (e : HP ⧸ U ≃ D.relGal d q),
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:53:    j (D.y (d * q)) = yR ∧ j (D.y d) = yP ∧
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:55:      j (WeierstrassCurve.Affine.Point.map (e τ).1.toAlgHom (D.y (d * q)))) ∧
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:56:    j (WeierstrassCurve.Affine.Point.map (D.frob d q).toAlgHom (D.y d)) = ρ σ yP ∧
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:57:    j (WeierstrassCurve.Affine.Point.map (D.frob d q)⁻¹.toAlgHom (D.y d)) = ρ σ⁻¹ yP
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:60:clause of `D.NormRelations` at an admissible `(d, q)` with `q` split in `K`, transported by
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:62:theorem hnorm_of_normRelations (D : HeegnerPointData E) (hD : D.NormRelations) {d q : ℕ}
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:63:    (hadm : D.Admissible d q) (hsplit : jacobiSym D.DK q = 1) {σ : G} {yR yP : Dm}
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:64:    (htr : HeegnerTransportAt ρ HP U t D d q σ yR yP) :
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:68:  have hrel := hD.2 d q hadm hsplit
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:70:      j (∑ τ ∈ D.relGal d q, WeierstrassCurve.Affine.Point.map τ.toAlgHom (D.y (d * q))) := by
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:71:    rw [map_sum, ← Finset.sum_coe_sort (D.relGal d q)]
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:75:/-- **`hnorm` from the print** (PROVED from the PRINT `CCLThm2_15Applied`): if every anchored
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:76:Heegner point datum admits the transport at `(d, q)` (with points `yR D`, `yP D`) and `(d, q)` is
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:77:admissible with `q` split, the print provides a datum whose transported points satisfy `hnorm`. -/
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:79:    {d q : ℕ} (σ : G) (yR yP : HeegnerPointData E → Dm)
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:80:    (hadm : ∀ D, Anchor D → D.Admissible d q) (hsplit : ∀ D : HeegnerPointData E, Anchor D →
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:82:    (htr : ∀ D, Anchor D → HeegnerTransportAt ρ HP U t D d q σ (yR D) (yP D)) :
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:87:  exact ⟨D, hA, hnorm_of_normRelations ρ HP U t D hD (hadm D hA) (hsplit D hA) (htr D hA)⟩
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:98:    (HP : Subgroup G) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP) (DK : ℤ) (N d q : ℕ)
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:102:      frob) d q σ 0 0 :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:16:* `chainCond` (definition): the chain conductors `d_0 = d`, `d_{j+1} = d_j · ps[j]`;
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:20:  (the primes of `2` and of bad reduction, the primes of `d`), the separation of the chain's
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:21:  places, the splitting of the step primes, and the ELLIOT `ThetaOfDelta f` with `f ∣ d`;
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:24:  (`classSupport_subset`, `hm`, `hgood'`, `hpl`: the chain's places off `chainT pidx j` do not
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:25:  divide `d_j`, `cond_not_mem`), the admissibility of every step for the anchored datum
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:26:  (`hadmD`, `hsplitD`), and at every step the hypotheses of lane E2's `gx_step_heegner_at`:
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:28:  (`hanti`, through `alphaStage_conj` and `frobConjugatePlaces_proved`), and the places prime
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:29:  to the conductors (`hwd`);
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:30:* **`E2ChainInputs.g`** (definition): `g_j` = lane E2's `gx` of `heegnerActual … d_j` on the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:32:* **`E2ChainInputs.hG`** (PROVED): `g_{i+1} = pointFactor a_i z_i z_i⁻¹ • g_i + d b_i` with the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:33:  leaf's values at the stage, from `gx_step_heegner_at` and the junction `stepFactor_eq`
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:35:* **`E2ChainInputs.hloc`** (PROVED): the local lifts, lane E2's `exists_ux`;
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:64:/-- **The chain conductors** `d_0 = d`, `d_{j+1} = d_j · ps[j]` (with `ps[j] = 1` past the end of
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:65:`ps`), i.e. `d_j = d ∏_{j' < j} ps[j']` (tex 2914–2921, 4142–4146). Kind: definition. -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:66:def chainCond (d : ℕ) (ps : List ℕ) : ℕ → ℕ
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:67:  | 0 => d
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:68:  | j + 1 => chainCond d ps j * ps.getD j 1
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:70:/-- `d ∣ d_j` (tex 2914–2921). Kind: PROVED. -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:71:theorem dvd_chainCond (d : ℕ) (ps : List ℕ) : ∀ j, d ∣ chainCond d ps j
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:72:  | 0 => dvd_refl d
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:73:  | j + 1 => (dvd_chainCond d ps j).mul_right _
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:84:def classSupport (A : ActualPresentation C D Fam x) (d j : ℕ) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:86:  A.S₀ ∪ {v | ((chainCond d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:111:  cp : CSTParam (Ecurve ℓ)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:113:  emb : Qbar →ₐ[ℚ] ℂ
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:115:  κ : Qbar ≃ₐ[ℚ] AlgebraicClosure C.K
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:117:  with lane E2's full anchor (tex 2914–2936) -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:118:  print : CCLThm2_15Applied (Ecurve ℓ) (FullAnchor (Ecurve ℓ) C.K cp emb κ)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:121:  hψ : Function.Injective (A.ψ (t + 1))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:123:  d : ℕ
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:125:  hd : 0 < d
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:127:  hd2 : Nat.Coprime d (2 * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:129:  hdS0 : ∀ v : HeightOneSpectrum (𝓞 C.K), (d : 𝓞 C.K) ∈ v.asIdeal → v ∈ A.S₀
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:131:  htwo : ∀ v : HeightOneSpectrum (𝓞 C.K), (2 : 𝓞 C.K) ∈ v.asIdeal → v ∈ A.S₀
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:134:  hgood : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ A.S₀ →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:138:  hsep : ∀ i < A.ps.length, ∀ (p : A.ι) (c : Bool), p ≠ A.pidx i →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:142:  hq : ∀ i < A.ps.length, ¬ A.ps.getD i 1 ∣
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:143:    6 * chainCond d A.ps i * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:145:  hsplit : ∀ i < A.ps.length, jacobiSym (discr C.K) (A.ps.getD i 1) = 1
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:147:  f : ℕ
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:149:  [hf : NeZero f]
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:152:  hθ : ThetaOfDelta A.hS (Set.Subset.refl A.S) A.sh A.hs A.hs0 (A.π (t + 1)) f
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:153:  /-- `f ∣ d` (definition; tex 2847–2855) -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:154:  hfd : f ∣ d
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:160:attribute [local instance] E2ChainInputs.hf
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:164:theorem chainCond_pos : ∀ j, 0 < chainCond I.d A.ps j
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:165:  | 0 => I.hd
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:166:  | j + 1 => Nat.mul_pos (chainCond_pos j) (A.ps_getD_pos j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:170:theorem chainCond_coprime : ∀ j, Nat.Coprime (chainCond I.d A.ps j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:172:  | 0 => I.hd2
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:174:    refine Nat.Coprime.mul_left (chainCond_coprime j) ?_
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:176:    · refine (Nat.Prime.coprime_iff_not_dvd (A.ps_getD_prime hj)).2 fun h => I.hq j hj ?_
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:177:      exact h.trans ⟨3 * chainCond I.d A.ps j, by ring⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:182:/-- **The chain's places off the support do not divide the conductor** (PROVED from `hdS0`,
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:183:`hsep` and `A.hw`; tex 3471–3487): for `p ∉ chainT pidx j`, `d_j ∉ pl (p, c)`. -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:184:theorem cond_not_mem : ∀ (j : ℕ) (p : A.ι) (c : Bool), p ∉ chainT A.pidx j →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:185:    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∉ (A.pl (p, c)).asIdeal
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:186:  | 0, p, c, _ => fun h => A.hw (p, c) (I.hdS0 _ h)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:191:    change (((chainCond I.d A.ps j * A.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ (A.pl (p, c)).asIdeal at h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:194:    · exact cond_not_mem j p c hp'.2 h1
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:196:      · exact I.hsep j hj p c hp'.1 h1
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:201:/-- The primes dividing a chain conductor lie in the Selmer support (PROVED from `hdS0` and
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:203:theorem mem_S_of_cond : ∀ (j : ℕ) (v : HeightOneSpectrum (𝓞 C.K)),
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:204:    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ A.S
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:205:  | 0, v, h => A.hS (I.hdS0 v h)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:207:    change (((chainCond I.d A.ps j * A.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ v.asIdeal at h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:210:    · exact mem_S_of_cond j v h1
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:220:theorem classSupport_subset (j : ℕ) : classSupport A I.d j ⊆ A.S := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:223:  · exact I.mem_S_of_cond j v hv
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:227:theorem hSd (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K),
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:228:    ((chainCond I.d A.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupport A I.d j :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:232:/-- The primes of `2^{t+1}` lie in the support (PROVED from `htwo`). -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:233:theorem hm (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K),
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:234:    ((2 ^ (t + 1) : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupport A I.d j := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:237:  exact Or.inl (I.htwo v (v.isPrime.mem_of_pow_mem _ hv))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:240:/-- `E` has good reduction outside the support (PROVED from `hgood`). -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:241:theorem hgood' (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ classSupport A I.d j →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:243:  fun v hv => I.hgood v fun h => hv (Or.inl h)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:246:/-- No place of the chain off `chainT pidx j` lies in the support (PROVED from `cond_not_mem`
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:248:theorem hpl (j : ℕ) : ∀ jj : A.ι × Bool, jj.1 ∉ chainT A.pidx j →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:249:    (A.place jj).1 ∉ classSupport A I.d j := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:252:  · exact I.cond_not_mem j p c hp h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:255:/-- `f ∣ d_j` (PROVED). -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:256:theorem hfd_cond (j : ℕ) : I.f ∣ chainCond I.d A.ps j := I.hfd.trans (dvd_chainCond _ _ j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:258:/-! ### The anchored datum and the classes -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:260:/-- **The anchored datum of lane E2's step identity at the stage** (tex 2914–2936): the datum
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:263:def datum : HeegnerPointData (Ecurve ℓ) :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:266:    A.hs A.hs0 (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:267:    (A.hΨ (t + 1)) (StageRing (t + 1)) A.place I.print)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:269:/-- The full anchor of the datum (tex 2914–2936). Kind: PROVED. -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:270:theorem anchor : FullAnchor (Ecurve ℓ) C.K I.cp I.emb I.κ I.datum :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:273:    A.sh A.hs A.hs0 (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:274:    (A.hΨ (t + 1)) (StageRing (t + 1)) A.place I.print)).fst
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:276:/-- The conductors are prime to `N D_K` for the datum (PROVED). -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:277:theorem hcop (j : ℕ) : Nat.Coprime (chainCond I.d A.ps j) (I.datum.N * I.datum.DK.natAbs) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:278:  rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:279:  exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) (I.chainCond_coprime j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:281:/-- **Every step is admissible for the datum** (PROVED from `hd2`, `hq` and the anchor's
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:283:theorem hadmD {i : ℕ} (hi : i < A.ps.length) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:284:    I.datum.Admissible (chainCond I.d A.ps i) (A.ps.getD i 1) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:285:  refine ⟨I.chainCond_pos i, ?_, A.ps_getD_prime hi, ?_⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:286:  · rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:287:    exact I.chainCond_coprime i
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:288:  · rw [I.anchor.anchor.1, I.anchor.anchor.2.1]
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:289:    exact I.hq i hi
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:291:/-- **Every step prime splits for the datum** (PROVED from `hsplit`; tex 2720–2722). -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:292:theorem hsplitD {i : ℕ} (hi : i < A.ps.length) : jacobiSym I.datum.DK (A.ps.getD i 1) = 1 := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:293:  rw [I.anchor.anchor.2.1]
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:294:  exact I.hsplit i hi
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:299:def g (j : ℕ) : (globalCx (StageRing (t + 1)) (GKS C.K A.S) (actualM A (t + 1))).X 1 :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:301:  haveI : NeZero (chainCond I.d A.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:305:      (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ (A.hΨ (t + 1))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:306:      A.place I.anchor (I.classSupport_subset j) (chainCond I.d A.ps j) (I.hcop j) (I.hSd j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:307:      (I.hm j) (I.hgood' j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:309:        (I.classSupport_subset j) I.f I.hθ (I.hfd_cond j) (I.hSd j)) (I.hpl j))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:316:theorem hanti {i : ℕ} (hi : i < A.ps.length) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:320:  have hκh : A.Cc.κ ((Fam.h x : ℤ) : C.K) = ((Fam.h x : ℤ) : C.K) := map_intCast _ _
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:321:  obtain ⟨g, hg⟩ := frobConjugatePlaces_proved A.S A.Cc
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:328:/-- **The places of a step are prime to the conductors** (PROVED from `cond_not_mem`, `A.hnew`
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:330:theorem hwd {i : ℕ} (hi : i < A.ps.length) [NeZero (chainCond I.d A.ps i)] :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:333:      ((chainCond I.d A.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:335:        (CST.conductorOrder C.K (chainCond I.d A.ps i)).conductorModulus ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:337:        (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := C.K) (chainCond I.d A.ps i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:340:  have hnot : ((chainCond I.d A.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:343:    · exact I.cond_not_mem i _ _ (A.hnew i hi)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:344:    · exact I.cond_not_mem i _ _ (A.hnew i hi)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:345:  have hJ := mem_primeTo_of_not_mem (chainCond I.d A.ps i) (NeZero.ne _) w.1 hnot
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:353:theorem stepFactor_eq {i : ℕ} (hi : i < A.ps.length) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:396:4157–4172): `g_{i+1} = pointFactor a_i z_i z_i⁻¹ • g_i + d b_i` with the leaf's values at the
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:398:`hanti`, `hwd`) and the junction `stepFactor_eq`. -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:399:theorem hG : ∀ i < A.ps.length,
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:401:      I.g (i + 1) = pointFactor (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).a i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:403:          (((leafFrobΛ C Fam x A.ps).map (stageMk (t + 1))).zi i) • I.g i +
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:404:        (globalCx (StageRing (t + 1)) (GKS C.K A.S) (actualM A (t + 1))).d 0 1 rfl bG := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:407:  have : NeZero (chainCond I.d A.ps i) := ⟨(I.chainCond_pos i).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:411:    (A.ψ (t + 1)) A.Pk I.hψ (A.hΨ (t + 1)) (StageRing (t + 1)) A.place I.print)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:412:  obtain ⟨bG, hbG⟩ := hall (I.hadmD hi) (I.hsplitD hi) (Tp := chainT A.pidx i) (p := A.pidx i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:413:    (I.classSupport_subset i) (I.classSupport_subset (i + 1)) (I.hSd i) (I.hSd (i + 1)) (I.hm i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:414:    (I.hm (i + 1)) (I.hgood' i) (I.hgood' (i + 1)) I.f I.hθ (I.hfd_cond i) (I.hpl i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:415:    (I.hpl (i + 1)) (newPlace (A.place (A.pidx i, false)) (A.hwp (A.pidx i, false)))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:417:    (hanti hi) (I.hwd hi)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:419:  rw [← stepFactor_eq hi]
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:424:theorem hloc (j : ℕ) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:430:        (chainT A.pidx j)).i).f 1 1 rfl u =
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:432:        (presLoc C.K A.S₀ A.S A.place) (actualM A (t + 1))).f 1 1 rfl (I.g j) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:434:  have : NeZero (chainCond I.d A.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:443:    A.hs0 (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ (A.hΨ (t + 1))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:446:      (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk I.hψ (A.hΨ (t + 1))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:447:      A.place I.anchor (I.classSupport_subset j) (chainCond I.d A.ps j) (I.hcop j) (I.hSd j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:448:      (I.hm j) (I.hgood' j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:450:        (I.classSupport_subset j) I.f I.hθ (I.hfd_cond j) (I.hSd j)) (I.hpl j))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:461:  g := I.g
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:462:  hG := I.hG
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:463:  hloc j _ := I.hloc j
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:14:classes of the actual anchored Heegner points of the chain conductors `d_j = d ∏_{j' < j} ps[j']`
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:21:  provider of lane E2's Kummer classes, one base conductor per address (the same `d` at every
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:30:with the full anchor) through `exists_stepHyps_provider`; the classes are no longer free. The
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:32:full anchor), the ELLIOT `ThetaOfDelta f` (tex 2847–2855), and definitions (the conductor, its
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:33:admissibility, the supports, the splitting of the step primes, `hψ`).
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:75:  /-- `E_ℓ` is elliptic (definition) -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:76:  elliptic : (Ecurve ℓ).IsElliptic
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:79:  milne : MilneADT_I_2_8
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:82:  iwasawa : IwasawaGenerators
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:86:  conductor (PRINT, ELLIOT, definitions: `E2ChainInputs`), and the genuine stage chains with
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:89:  chains : ∃ C : TateCoef (Ecurve ℓ), ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:95:          (∀ t (h : t + 1 ∈ G) t' (h' : t' + 1 ∈ G), (I t h).d = (I t' h').d) ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:96:          Nonempty (GenuineStageSTUK A milne iwasawa genuineCochainsInjective_proved U hU G
```

## Distinctive member-name matches elsewhere in Lean sources

```text
ZInQKernel/Contrib/CloudB3E1NoCM/Consumers.lean:133:  have hgood' : GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r := hgood
ZInQKernel/Contrib/CloudB3E1NoCM/Consumers.lean:139:  refine ⟨r, hrS, hrp, hgood', hr1, ξ, ?_, ?_, ?_, ?_, hb1, hb2, hb3, hb4, hb5⟩
ZInQKernel/Contrib/CloudB3E1NoCM/Consumers.lean:159:    have hnm := (I.not_mem hgood' j).1
ZInQKernel/Contrib/CloudB3E1NoCM/Consumers.lean:170:    have hnm := (I.not_mem hgood' j).2
ZInQKernel/Contrib/CloudB3E1RingClass/MovingGenuine.lean:81:  have hgood' : GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r := hgood
ZInQKernel/Contrib/CloudB3E1RingClass/MovingGenuine.lean:87:  refine ⟨r, hrS, hrp, hgood', hr1, ξ, ?_, ?_, ?_, ?_, hb1, hb2, hb3, hb4, hb5⟩
ZInQKernel/Contrib/CloudB3E1RingClass/MovingGenuine.lean:107:    have hnm := (I.not_mem hgood' j).1
ZInQKernel/Contrib/CloudB3E1RingClass/MovingGenuine.lean:118:    have hnm := (I.not_mem hgood' j).2
ZInQKernel/Contrib/CloudB3E1RingClass/MovingPi.lean:129:  have hgood' : GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r := hgood
ZInQKernel/Contrib/CloudB3E1RingClass/MovingPi.lean:135:  refine ⟨r, hrS, hrp, hgood', hr1, ξ, ?_, ?_, ?_, ?_, ?_, hb1, hb2, hb3, hb4, hb5⟩
ZInQKernel/Contrib/CloudB3E1RingClass/MovingPi.lean:158:    have hnm := (I.not_mem hgood' j).1
ZInQKernel/Contrib/CloudB3E1RingClass/MovingPi.lean:169:    have hnm := (I.not_mem hgood' j).2
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:285:theorem chainCond_pos : ∀ j, 0 < chainCond I.d P.ps j
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:287:  | j + 1 => Nat.mul_pos (chainCond_pos j) (P.ps_getD_pos j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:291:theorem chainCond_coprime : ∀ j, Nat.Coprime (chainCond I.d P.ps j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:295:    refine Nat.Coprime.mul_left (chainCond_coprime j) ?_
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:305:theorem cond_not_mem : ∀ (j : ℕ) (p : P.ι) (c : Bool), p ∉ chainT P.pidx j →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:315:    · exact cond_not_mem j p c hp'.2 h1
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:324:theorem mem_S_of_cond : ∀ (j : ℕ) (v : HeightOneSpectrum (𝓞 C.K)),
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:331:    · exact mem_S_of_cond j v h1
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:341:theorem classSupport_subset (j : ℕ) : classSupportS P (t + 1) I.d j ⊆ P.S (t + 1) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:344:  · exact I.mem_S_of_cond j v hv
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:362:theorem hgood' (j : ℕ) : ∀ v : HeightOneSpectrum (𝓞 C.K), v ∉ classSupportS P (t + 1) I.d j →
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:367:/-- No place of the chain off `chainT pidx j` lies in the support (PROVED from `cond_not_mem`
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:373:  · exact I.cond_not_mem j p c hp h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:427:  exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) (I.chainCond_coprime j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:433:  refine ⟨I.chainCond_pos i, ?_, P.ps_getD_prime hi, ?_⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:435:    exact I.chainCond_coprime i
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:440:theorem hsplitD {i : ℕ} (hi : i < P.ps.length) : jacobiSym I.datum.DK (P.ps.getD i 1) = 1 := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:448:    fixH ((I.classSupport_subset j).trans (Set.Subset.refl (P.S (t + 1))))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:453:    (P.sh (t + 1)) (P.hs (t + 1)) (P.hs0 (t + 1)) (P.piU (t + 1)) (I.classSupport_subset j) I.d
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:460:  haveI : NeZero (chainCond I.d P.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:465:    I.anchor (I.classSupport_subset j) (chainCond I.d P.ps j) (I.hcop j) (I.hSd j) (I.hm j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:466:    (I.hgood' j) (I.hα j) (I.hpl j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:506:/-- **The places of a step are prime to the conductors** (PROVED from `cond_not_mem`, `P.hnew`
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:521:    · exact I.cond_not_mem i _ _ (P.hnew i hi)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:522:    · exact I.cond_not_mem i _ _ (P.hnew i hi)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:531:theorem stepFactor_eq {i : ℕ} (hi : i < P.ps.length) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:580:the junction `stepFactor_eq`. -/
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:590:  have : NeZero (chainCond I.d P.ps i) := ⟨(I.chainCond_pos i).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:598:  obtain ⟨bG, hbG⟩ := hall (I.hadmD hi) (I.hsplitD hi) (Tp := chainT P.pidx i) (p := P.pidx i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:599:    (I.classSupport_subset i) (I.classSupport_subset (i + 1)) (I.hSd i) (I.hSd (i + 1))
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:600:    (I.hm i) (I.hm (i + 1)) (I.hgood' i) (I.hgood' (i + 1)) I.d I.hθ (dvd_chainCond I.d P.ps i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:606:  rw [← stepFactor_eq hi]
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:638:  have : NeZero (chainCond I.d P.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/InnerLimitFamilyPinBinding.lean:90:  have hgood' : GoodPrime (Ecurve ℓ) I.sqrtD I.Sexc r := hgood
ZInQKernel/Contrib/OneProof/RC/Wiring/InnerLimitFamilyPinBinding.lean:95:  refine ⟨r, hrS, hrp, hgood', hr1, ξ0', ?_, ?_, ?_, ?_⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/InnerLimitFamilyPinBinding.lean:115:    have hnm := (I.not_mem hgood' j).1
ZInQKernel/Contrib/OneProof/RC/Wiring/InnerLimitFamilyPinBinding.lean:126:    have hnm := (I.not_mem hgood' j).2
```
