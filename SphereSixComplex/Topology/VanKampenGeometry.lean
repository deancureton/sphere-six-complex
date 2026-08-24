/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.FundamentalGroupComputation

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

/-- Names for the surviving central loop and the two elliptic meridians. -/
public inductive PaperMeridianName where
  | c
  | x
  | y
  deriving DecidableEq

/-- Based representatives of the loops `c`, `x`, and `y` in Theorem 7.17. -/
public structure PaperMeridianLoops {Y : Type*} [TopologicalSpace Y] (base : Y) where
  c : Path base base
  x : Path base base
  y : Path base base

namespace PaperMeridianLoops

variable {Y : Type*} [TopologicalSpace Y] {base : Y}

/-- Select the path represented by a named meridian. -/
public def path (L : PaperMeridianLoops base) : PaperMeridianName → Path base base
  | .c => L.c
  | .x => L.x
  | .y => L.y

/-- The fundamental-group class of a named geometric loop. -/
public def generator (L : PaperMeridianLoops base) (g : PaperMeridianName) :
    FundamentalGroup Y base :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (L.path g))

end PaperMeridianLoops

/-! ## Relations supplied by the three fillings -/

/-- The geometric relations before the paper eliminates the generator `y`.

The cusp filling supplies centrality and `xy = c^ℓ₀`.  The order-three and order-four
fillings supply the remaining two relations, retaining their coupled signs. -/
public structure PaperMeridianRelations
    {Y : Type*} [TopologicalSpace Y] {base : Y}
    (L : PaperMeridianLoops base) (ℓ₀ ℓ₁ ℓ₂ : ℤ) : Prop where
  central_c : ∀ g : FundamentalGroup Y base, Commute (L.generator .c) g
  cusp : L.generator .x * L.generator .y = L.generator .c ^ ℓ₀
  ellipticThree : L.generator .x ^ (3 : ℤ) = L.generator .c ^ ℓ₁
  ellipticFour : L.generator .y ^ (4 : ℤ) = L.generator .c ^ ℓ₂

namespace PaperMeridianRelations

variable {Y : Type*} [TopologicalSpace Y] {base : Y}
variable {L : PaperMeridianLoops base} {ℓ₀ ℓ₁ ℓ₂ : ℤ}

/-- Forget geometric path representatives and retain the upstream algebraic relations. -/
public def toSatisfiesPaperRelations (R : PaperMeridianRelations L ℓ₀ ℓ₁ ℓ₂) :
    SatisfiesPaperRelations (FundamentalGroup Y base) ℓ₀ ℓ₁ ℓ₂ where
  c := L.generator .c
  x := L.generator .x
  y := L.generator .y
  central_c := R.central_c
  xy := R.cusp
  x_cube := R.ellipticThree
  y_fourth := R.ellipticFour

end PaperMeridianRelations

/-! ## Complete geometric van Kampen data -/

/-- The precise geometric refinement of the upstream `HasVanKampenData` contract.

The last two fields isolate the exact output of space-level Seifert--van Kampen: the three named
loops generate, and no relation remains beyond those already encoded by the paper's relation
lattice. -/
public structure PaperVanKampenGeometryData
    {Y : Type*} [TopologicalSpace Y] (base : Y) (ℓ₀ ℓ₁ ℓ₂ : ℤ) where
  cover : PaperVanKampenFourPieceCover base
  loops : PaperMeridianLoops base
  loops_mem_core (g : PaperMeridianName) (t) : loops.path g t ∈ cover.core
  relations : PaperMeridianRelations loops ℓ₀ ℓ₁ ℓ₂
  generators_generate : PaperGeneratorsGenerate relations.toSatisfiesPaperRelations
  no_extra_relations : HasNoExtraPaperRelations relations.toSatisfiesPaperRelations

namespace PaperVanKampenGeometryData

variable {Y : Type*} [TopologicalSpace Y] {base : Y} {ℓ₀ ℓ₁ ℓ₂ : ℤ}

/-- Forget the cover and path representatives, obtaining the upstream algebraic input. -/
public theorem toHasVanKampenData (D : PaperVanKampenGeometryData base ℓ₀ ℓ₁ ℓ₂) :
    HasVanKampenData Y ℓ₀ ℓ₁ ℓ₂ :=
  ⟨base, D.relations.toSatisfiesPaperRelations, D.generators_generate,
    D.no_extra_relations⟩

/-- Geometric van Kampen data therefore give the verified presentation equivalence. -/
public theorem hasVanKampenPresentation
    (D : PaperVanKampenGeometryData base ℓ₀ ℓ₁ ℓ₂) :
    HasVanKampenPresentation Y ℓ₀ ℓ₁ ℓ₂ :=
  D.toHasVanKampenData.hasVanKampenPresentation

/-- At the paper's selected twists, the geometric data imply its fundamental-group contract. -/
public theorem hasPaperFundamentalGroup
    (D : PaperVanKampenGeometryData base 0 1 (-1)) : HasPaperFundamentalGroup Y :=
  D.hasVanKampenPresentation.hasPaperFundamentalGroup

end PaperVanKampenGeometryData

end

end SphereSixComplex.Topology
