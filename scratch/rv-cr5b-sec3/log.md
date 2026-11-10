# rv-cr5b-sec3 log
- 2026-11-10T15:43:26Z start: fresh run, reading docs
- 2026-11-10T15:46:45Z load ok; started lake build ZInQKernel.RouteK.Rank5bSec3 (modules missing)
- 2026-11-10T15:49:02Z mirror.py written; d=21,5 sanity ok; running 30-value red team
- 2026-11-10T15:50:34Z red team done (out_mirror.txt): 30 d, 28 with #Sel2=8 (21 T5b=1, 7 T5b=0), 205/221 #Sel2=32; T5b=genusSum5b=detM5b everywhere; Redei = PARI on all blocks; all Selmer classes realized when #Sel2=8. No mismatch.
- findings so far: docstring GZ+Kolyvagin via Lemma 5.5 (BCDT + MPIM preprint) -> GZ + BFH/MM; cite Prop N/nt-tyz §4 not 'proof of Thm 3.5(2)' and drop '2^-rho L odd'; 𝓛 vs 𝓛₁ notation; KERNEL_PLAN not updated; build logs tracked.
