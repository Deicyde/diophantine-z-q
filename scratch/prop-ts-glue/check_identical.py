# The first part of PropTSGlue.lean must be scratch/prop-ts/PropTS.lean, byte for byte.
a=open("scratch/prop-ts/PropTS.lean").read()
b=open("scratch/prop-ts-glue/PropTSGlue.lean").read()
print("PREFIX IDENTICAL" if b.startswith(a) else "DIFFERENT", len(a))
