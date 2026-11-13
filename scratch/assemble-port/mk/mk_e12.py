"""assemble-port: parts/e12_tskummer.lean = the ts-kummer appendix, scratch/ts-kummer/KummerTS.lean L3598-end verbatim minus
`#print` lines (task ts-kummer; there it follows an earlier PropTSGlue.lean, L1-2947 identical to 3d41b3d5's, without
3d41b3d5's L2948-3551, which the appendix does not use), preceded by the file-level opens that precede it in KummerTS.lean
(PropTSGlue.lean L26-27) and followed by an `end` closing its `noncomputable section`; one `simpa` made explicit (see below). Proves six of the seven Kummer pieces
(`TsKummer.kummerAbhyankarFinGlue`, …). Run from scratch/assemble-port."""
L = open('../ts-kummer/KummerTS.lean').read().split('\n')
assert L[3597].startswith('/-! # ts-kummer appendix'), L[3597]
P = open('../prop-ts-glue/PropTSGlue.lean').read().split('\n')
assert P[25].startswith('open CategoryTheory') and P[26].startswith("open LeafQM.AV"), (P[25], P[26])
body = [l for l in L[3597:] if not l.startswith('#print')]
# one proof edit (statement unchanged): in `abhyankar_core`, `simpa using h1` is closed by an unrelated simp lemma in the
# flat file's context (file-level opens of Leaves.lean); use the two rewrites it needs.
k = [i for i, l in enumerate(body) if l == '    simpa using h1']; assert len(k) == 1, k
assert 'IsUnit ((algebraMap R0 Rp).comp (algebraMap ℚ R0) (k : ℚ))' in body[k[0] - 2]
body[k[0]] = '    simpa only [RingHom.comp_apply, map_natCast] using h1'
hdr = ['/-! ## assemble-port: ts-kummer (six Kummer pieces of `KummerMeetGlue` proved). `scratch/ts-kummer/KummerTS.lean`',
       'L3598-end, verbatim minus `#print` lines (mk/mk_e12.py), after the opens of PropTSGlue.lean L26-27. -/', '',
       P[25], P[26], '']
open('parts/e12_tskummer.lean', 'w').write('\n'.join(hdr + body).rstrip() + '\n\nend  -- assemble-port: closes the appendix\'s `noncomputable section`\n')
print('ok', len(body))
