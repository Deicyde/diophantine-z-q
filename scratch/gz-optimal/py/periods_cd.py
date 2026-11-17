# Runs periods_cd.gp for the given d (ground-truth check, at most 30 inputs, one after another).
import sys, cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
pari('read("periods_cd.gp")')
maxk, amax = int(sys.argv[1]), int(sys.argv[2])
for d in sys.argv[3:]:
    pari(f'run({d}, {maxk}, {amax})')
