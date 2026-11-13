# Assemble part_fix.lean = part_fix_head.lean (§0, copies from g8-tate) + part_fix_defs.lean (§1)
# + two copies of frob-trace's `tateBridge35_of_algFrobLink` (FrobTrace.lean l.2562-2755) with the
# edits below (§2) + part_fix_final.lean (§3).
src = open('../frob-trace/FrobTrace.lean').read().split('\n')
body = '\n'.join(src[2561:2753])   # l.2562 (set_option) .. l.2755 (end of the proof)
assert body.startswith('set_option maxHeartbeats 4000000 in'), body[:50]
assert body.rstrip().endswith('Ψ5 hΨ5⟩'), body[-50:]
def rep(s, a, b):
    assert s.count(a) == 1, (a, s.count(a)); return s.replace(a, b)
hdr = ("theorem tateBridge35_of_algFrobLink (hT : PkgI3.TateModuleFree) (hF : AlgFrobLink) :\n"
       "    G14Bridge.TateBridge35 := by")
cut = "  let j5 : Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift"
pre, post = body.split(cut)
# --- copy A: every ℓ, no AlgFrobLink
A = rep(pre, hdr, "theorem _root_.KWFix.tateBridgeE_of_tateModuleFree (hT : PkgI3.TateModuleFree) :\n"
        "    KWFix.TateBridgeE := by")
A = rep(A, "/-- **`TateBridge35` from the leaf I3.M0", "/-- (kerwild-fix copy A) **`TateBridge35` from the leaf I3.M0")
A += '''  -- kerwild-fix: `j := Φ ∘ ι_ℂ`, so `j ∘ βQ = Φ ∘ β` and `∂(Φ ∘ β) = Φ ∘ ε`
  intro ℓ _
  obtain ⟨Φ⟩ := G8Tate.exists_complex_equiv ℓ
  obtain ⟨c, ε', uu, hG7⟩ := key ℓ (KWFix.jOf Φ ιC)
  exact ⟨Φ, _, c, _, uu, KWFix.g7Out_eps_congr _ ℓ _ _ _ _ _ _ _
    (KWFix.g7Out_beta_congr _ ℓ _ _ _ _ _ _ _ hG7 fun g => congrArg Φ (hιβ g).symm)
    (KWFix.cocycle_map Φ β ε hβe)⟩
'''
# --- copy B: ℓ = 5, 3 with FrobTraceLink
B = rep(pre, hdr, "theorem _root_.KWFix.tateBridge35E_of_algFrobLink (hT : PkgI3.TateModuleFree)\n"
        "    (hF : AlgFrobLink) : KWFix.TateBridge35E := by")
B = rep(B, "/-- **`TateBridge35` from the leaf I3.M0", "/-- (kerwild-fix copy B) **`TateBridge35` from the leaf I3.M0")
old_end = '''  let j3 : Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, ε5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, ε3, u3, h3⟩ := key 3 j3
  refine ⟨fun g => βQ g / gamQ (h * g * h⁻¹), βQ, j5, j3, _, c5, ε5, u5, _, c3, ε3, u3, h5, h3,
    ?_, ιC, hιβ⟩'''
new_end = '''  -- kerwild-fix: `j_ℓ := Φ_ℓ ∘ ι_ℂ`
  obtain ⟨Φ5⟩ := G8Tate.exists_complex_equiv 5
  obtain ⟨Φ3⟩ := G8Tate.exists_complex_equiv 3
  obtain ⟨c5, ε5, u5, h5⟩ := key 5 (KWFix.jOf Φ5 ιC)
  obtain ⟨c3, ε3, u3, h3⟩ := key 3 (KWFix.jOf Φ3 ιC)
  refine ⟨fun g => βQ g / gamQ (h * g * h⁻¹), βQ, ιC, Φ5, Φ3, _, c5, u5, _, c3, u3, hιβ,
    KWFix.g7Out_eps_congr _ 5 _ _ _ _ _ _ _
      (KWFix.g7Out_beta_congr _ 5 _ _ _ _ _ _ _ h5 fun g => congrArg Φ5 (hιβ g).symm)
      (KWFix.cocycle_map Φ5 β ε hβe),
    KWFix.g7Out_eps_congr _ 3 _ _ _ _ _ _ _
      (KWFix.g7Out_beta_congr _ 3 _ _ _ _ _ _ _ h3 fun g => congrArg Φ3 (hιβ g).symm)
      (KWFix.cocycle_map Φ3 β ε hβe), ?_⟩'''
B = B + rep(post, old_end, new_end)
copies = '''
section KWFixCopySec

/-! ### §2. The bridges proved: two copies of frob-trace's `tateBridge35_of_algFrobLink`
(scratch/frob-trace/FrobTrace.lean l.2562-2755, verbatim except the header and the choice of the
embeddings `j_ℓ := Φ_ℓ ∘ ι_ℂ` at the end; made by mk_fix.py) -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace FrobTrace

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

''' + A.rstrip('\n') + '\n\n' + B.rstrip('\n') + '''

end FrobTrace

end

end KWFixCopySec
'''
# --- copy C: g0-mod-field's g7OutUnr_of_g4Out (FrobTrace.lean l.636-662), keeping `[L:ℚ] ≤ D`
C = '\n'.join(src[635:662])
assert C.startswith('theorem g7OutUnr_of_g4Out'), C[:40]
assert C.rstrip().endswith('_ ≤ _ := hdegR'), C[-40:]
C = rep(C, "theorem g7OutUnr_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)\n"
        "    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7OutUnr u P := by",
        "theorem _root_.KWFix.g7OutUnrD_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo)\n"
        "    (hSq : LeafSqrtCrit) (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) :\n"
        "    KWFix.G7OutUnrD u P := by")
C = rep(C, "    L', hfd', hgal', hle, hA, hD,", "    L', hfd', hgal', hle, hLD, hA, hD,")
copyC = '''
section KWFixCopyCSec

/-! ### §2b. G7 with `[L:ℚ] ≤ D` kept: a copy of g0-mod-field's `g7OutUnr_of_g4Out`
(scratch/frob-trace/FrobTrace.lean l.636-662, verbatim except the header and `hLD` inserted in the
final `refine`; made by mk_fix.py). The `open` lines are FrobTrace.lean's l.53-54. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

''' + C.rstrip('\n') + '''

end G0ModField

end

end KWFixCopyCSec
'''
head = open('part_fix_head.lean').read()
defs = open('part_fix_defs.lean').read()
final = open('part_fix_final.lean').read()
open('part_fix.lean', 'w').write(head + defs + '\nend KWFix\n\nend\n\nend KWFixSec\n' + copies + copyC + final)
