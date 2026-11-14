/-
Verification of the exact fixed H-67 proposition.
This file adds no hypotheses and checks the closed proof at an arbitrary universe.
-/

import ZInQKernel.Contrib.CloudW02Connectedness.Basic

universe u

example : ZariskiConn.ZariskiConnectedness.{u} :=
  ZariskiConn.ZariskiConnectedness_proof.{u}

#print ZariskiConn.ZariskiConnectedness_proof
#print axioms ZariskiConn.ZariskiConnectedness_proof
#print axioms P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.solution
