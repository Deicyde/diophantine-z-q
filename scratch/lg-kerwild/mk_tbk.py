# Assemble part_tbk.lean: part_tbk_head.lean (new: ScalarTransferK + copy of unram-tate's
# scalarTransfer proof, TateBridge.lean l.1501-1575, with one extra bullet) + a copy of
# unram-tate's tateBridge_of_pieces (TateBridge.lean l.1303-1423) with the edits listed below.
src=open('../unram-tate/TateBridge.lean').read().split('\n')
head=open('part_tbk_head.lean').read()
head=head.replace("    exact congrArg ψ (Subtype.ext (hg1 k hk))\n\n  · intro σ h1","    exact congrArg ψ (Subtype.ext (hg1 k hk))\n  · intro σ h1")
body='\n'.join(src[1302:1423])
assert body.startswith('theorem tateBridge_of_pieces'), body[:40]
assert body.rstrip().endswith('exact hc'), body[-40:]
def rep(s,a,b):
    assert s.count(a)==1,(a,s.count(a)); return s.replace(a,b)
# edit 1: name, ScalarTransferK, conclusion TateBridgeK
body=rep(body,"theorem tateBridge_of_pieces (hP : TatePoints) (hE : EndBaseChange) (hS : ScalarTransfer)\n    (hC : TateCont) (hR : ResQEmbedding) : TateBridge := by",
 "theorem tateBridgeK_of_piecesK (hP : TatePoints) (hE : EndBaseChange) (hS : ScalarTransferK)\n    (hC : TateCont) (hR : ResQEmbedding) : LGKerWild.TateBridgeK := by")
# edit 2: keep the kernel clause of ScalarTransferK
body=rep(body,"obtain ⟨gam, hgam0, hgamc, hgamcos, hgam1⟩ := hS","obtain ⟨gam, hgam0, hgamc, hgamcos, hgam1, hgamK⟩ := hS")
# edit 3: the output is G7Out ∧ KerWild
body=rep(body,"refine ⟨Tm, c', c', a', β', uu, _hdim, _hrank, hT, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,\n    fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩",
 "refine ⟨Tm, c', c', a', β', uu, ⟨_hdim, _hrank, hT, ha, hβ, hβ0,\n    fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,\n    fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩, ?_⟩")
kw=open('part_tbk_kw.lean').read()
tail=open('part_tbk_tail.lean').read()
doc='''
set_option maxHeartbeats 1000000 in
/-- **`TateBridgeK` from the five glue pieces, with `ScalarTransferK` (proved)**: unram-tate's
`tateBridge_of_pieces` (proof copied verbatim up to the final `refine`), plus the kernel-field
clause. -/
'''
open('part_tbk.lean','w').write(head.rstrip('\n')+'\n'+doc+body.rstrip('\n')+'\n'+kw+tail)
