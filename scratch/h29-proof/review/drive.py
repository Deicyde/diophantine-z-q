import sys
sys.path.insert(0, '/home/jackmccarthy/dzq-wt/h29-proof/scratch/h29-proof')
import genus_check as g
ntau = int(sys.argv[1])
g.run([int(x) for x in sys.argv[2:]], ntau=ntau)
