"""Write ZInQKernel/Contrib/OneProof/BergerBst.lean = header + scratch/bst-construct/Bst.lean minus its two import lines."""
header = open('scratch/bst-construct/contrib-header.txt').read()
body = open('scratch/bst-construct/Bst.lean').read().split('\n', 2)[2]
open('ZInQKernel/Contrib/OneProof/BergerBst.lean', 'w').write(header + body)
