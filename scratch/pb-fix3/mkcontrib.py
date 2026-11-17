"""Write ZInQKernel/Contrib/OneProof/PanBergerDict.lean = header + scratch/pb-fix3/PanDict.lean minus its 4 import lines."""
header = open('scratch/pb-fix3/contrib-header.txt').read()
body = open('scratch/pb-fix3/PanDict.lean').read().split('\n', 4)[4]
open('ZInQKernel/Contrib/OneProof/PanBergerDict.lean', 'w').write(header + body)
