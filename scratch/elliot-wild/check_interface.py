"""Emit an isolated elaboration check if the SZRaynaud import is unavailable.

Run this from the repository root after building WildPeriodCoprimeCore. The
generated Lean imports the real core and copies the defining declarations of
IsWildInertia and WildPeriodCoprime from SZRaynaud. The existing ELLIOT
reduction is represented only by a theorem parameter. Use the actual
contribution module for a full integration check.
"""

from pathlib import Path


def read(module):
    return (Path("ZInQKernel/Contrib/OneProof") / f"{module}.lean").read_text()


sz = read("SZRaynaud")
contribution = read("WildPeriodCoprime")
wild = sz[sz.index("def IsWildInertia "):sz.index("/-! ## §2")].strip()
period = sz[sz.index("def WildPeriodCoprime "):sz.index("/-- The `n`-th component")].strip()
proof = contribution[
    contribution.index("theorem wildPeriodCoprime_proof "):
    contribution.index("/-- The wild inertia consequence")
].strip()
reduction = contribution[
    contribution.index("theorem elliot_of_semistableUnipotent_of_period_proof"):
    contribution.index("#print axioms wildPeriodCoprime_proof")
].strip().replace("ReductSplit.SemistableUnipotent", "SemistableUnipotent")

print("import ZInQKernel.Contrib.OneProof.WildPeriodCoprimeCore")
print("open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj")
print("open PkgI2 (IsInertia)")
print("namespace SZRaynaud")
print(wild, period, proof, sep="\n\n")
print("#print axioms wildPeriodCoprime_proof")
print("""section
variable (SemistableUnipotent ElliotWildInertiaTrivial : Prop)
variable (elliot_of_semistableUnipotent :
  SemistableUnipotent → WildPeriodCoprime → ElliotWildInertiaTrivial)
include elliot_of_semistableUnipotent""")
print(reduction)
print("#print axioms elliot_of_semistableUnipotent_of_period_proof")
print("end\nend SZRaynaud")
