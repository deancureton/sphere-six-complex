/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Paper.Topology.FundamentalGroupComputation

/-!
# Geometric input for the paper's van Kampen computation

This file refines the algebraic `HasVanKampenData` interface by retaining the geometry used in
Theorem 7.17: the star-shaped cover by the regular, cusp, and two elliptic pieces, three named
meridian loops, the relations supplied by the fillings, and the assertions that these loops
generate with no additional relations.

The interface is adapted from `ComplexStructures.S6.Topology.VanKampenBridge` in Paul Lezeau's
independent formalisation.  The presentation arithmetic itself is not duplicated: the final
adapter targets `HasVanKampenData` from `FundamentalGroupComputation`.
-/

namespace SphereSixComplex.Topology

noncomputable section

/-! ## The star-shaped four-piece cover -/

/-- The source-faithful cover used by the paper's Seifert--van Kampen argument.

The three filling pieces are pairwise disjoint and meet the regular core in path-connected
mapping-torus regions.  The connector paths implement change of basepoint. -/
public structure PaperVanKampenFourPieceCover
    {Y : Type*} [TopologicalSpace Y] (base : Y) where
  core : Set Y
  cusp : Set Y
  ellipticThree : Set Y
  ellipticFour : Set Y
  core_isOpen : IsOpen core
  cusp_isOpen : IsOpen cusp
  ellipticThree_isOpen : IsOpen ellipticThree
  ellipticFour_isOpen : IsOpen ellipticFour
  covers : core ∪ cusp ∪ ellipticThree ∪ ellipticFour = Set.univ
  cusp_disjoint_ellipticThree : Disjoint cusp ellipticThree
  cusp_disjoint_ellipticFour : Disjoint cusp ellipticFour
  ellipticThree_disjoint_ellipticFour : Disjoint ellipticThree ellipticFour
  core_pathConnected : IsPathConnected core
  cusp_pathConnected : IsPathConnected cusp
  ellipticThree_pathConnected : IsPathConnected ellipticThree
  ellipticFour_pathConnected : IsPathConnected ellipticFour
  cusp_overlap_pathConnected : IsPathConnected (core ∩ cusp)
  ellipticThree_overlap_pathConnected : IsPathConnected (core ∩ ellipticThree)
  ellipticFour_overlap_pathConnected : IsPathConnected (core ∩ ellipticFour)
  base_mem_core : base ∈ core
  cuspPoint : Y
  cuspPoint_mem : cuspPoint ∈ core ∩ cusp
  cuspConnector : Path base cuspPoint
  cuspConnector_mem (t) : cuspConnector t ∈ core
  ellipticThreePoint : Y
  ellipticThreePoint_mem : ellipticThreePoint ∈ core ∩ ellipticThree
  ellipticThreeConnector : Path base ellipticThreePoint
  ellipticThreeConnector_mem (t) : ellipticThreeConnector t ∈ core
  ellipticFourPoint : Y
  ellipticFourPoint_mem : ellipticFourPoint ∈ core ∩ ellipticFour
  ellipticFourConnector : Path base ellipticFourPoint
  ellipticFourConnector_mem (t) : ellipticFourConnector t ∈ core

/-! ## Named geometric generators -/



/-! ## Relations supplied by the three fillings -/


/-! ## Complete geometric van Kampen data -/


end

end SphereSixComplex.Topology
