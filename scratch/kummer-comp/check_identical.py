# Checks that scratch/kummer-comp/KummerComp.lean begins with scratch/ts-kummer/KummerTS.lean
# byte for byte (up to its trailing newlines), so every statement it contains is verbatim.
orig = open("scratch/ts-kummer/KummerTS.lean").read().rstrip("\n")
fin = open("scratch/kummer-comp/KummerComp.lean").read()
print("PREFIX IDENTICAL" if fin.startswith(orig + "\n") else "PREFIX DIFFERS")
