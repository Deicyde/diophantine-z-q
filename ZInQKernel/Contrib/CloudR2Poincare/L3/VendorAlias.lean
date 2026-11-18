import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

/-!
# Declaration wrapper for isolated namespace ports

This is an elaboration-only adapter. Proof and definition constants stay under
`ZInQ.Contrib.CloudR2Poincare.L3.StacksPort`. After an owned declaration is checked,
Lean's ordinary `export` command adds a namespace alias at its upstream qualified
name. That lets generalized field notation find extensions of Mathlib types without
copying or replacing their declarations. Root-name declaration collisions are refused.
No axiom, admission, native decision or theorem body is supplied by this adapter.
-/

open Lean Elab Command

namespace ZInQ.Contrib.CloudR2Poincare.L3

private def vendorPrefix : Name := `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort

private def stripVendorPrefix (n : Name) : Option Name :=
  let pfx := vendorPrefix.toString ++ "."
  let s := n.toString
  if s.startsWith pfx then
    some ((s.drop pfx.length).toString.splitOn "." |>.foldl Name.str Name.anonymous)
  else none

private def rootIdent (n : Name) : Ident := mkIdent (`_root_ ++ n)

syntax (name := cloudR2VendorDecl) "#cloudR2Vendor " ident " in " command : command

@[command_elab cloudR2VendorDecl]
def elabCloudR2VendorDecl : CommandElab := fun stx => do
  elabCommand (← `(#cloudR2LocalInstances))
  let curr ← getCurrNamespace
  let declId := stx[1].getId
  let owned := curr ++ declId
  let some upstream := stripVendorPrefix owned | throwError "Declaration is outside the owned vendor namespace: {owned}"
  let parent := upstream.getPrefix
  -- Open existing Mathlib namespaces explicitly: namespace wrapping does not
  -- otherwise expose inherited unqualified names such as IrreducibleCloseds.map.
  let rootOpens := ["AlgebraicGeometry", "TopologicalSpace", "CategoryTheory", "Topology",
    "Algebra", "Module", "IsLocalRing", "IsRegularLocalRing", "KaehlerDifferential",
    "TensorProduct", "PrimeSpectrum", "Ideal", "SheafOfModules"]
  let first := (parent.toString.splitOn ".").head!
  if rootOpens.contains first then
    let n := Name.str Name.anonymous first
    elabCommand (← `(open $(rootIdent n):ident))
  if ["TopologicalSpace.IrreducibleCloseds", "AlgebraicGeometry.Scheme.Hom",
      "AlgebraicGeometry.Scheme.Modules"].contains parent.toString then
    elabCommand (← `(open $(rootIdent parent):ident))
  elabCommand stx[3]
  -- Private declarations and anonymous instance-generated names are not exported.
  let env ← getEnv
  if !env.contains owned then return
  if env.contains upstream then
    throwError "Refusing root declaration collision while porting {owned}: {upstream} already exists"
  if parent.isAnonymous then return
  let sourceNs := owned.getPrefix
  let fn := mkIdent (Name.str Name.anonymous owned.getString!)
  withScope (fun scope => { scope with currNamespace := parent }) do
    elabCommand (← `(export $(rootIdent sourceNs):ident ($fn:ident)))
  logInfo m!"CLOUD_R2_ALIAS {upstream} := {owned}"

end ZInQ.Contrib.CloudR2Poincare.L3
