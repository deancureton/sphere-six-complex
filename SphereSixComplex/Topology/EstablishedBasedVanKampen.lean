module

public import SphereSixComplex.Topology.ConcreteVanKampen

/-!
# Based generator extraction from groupoid van Kampen

Mathlib proves the fundamental-groupoid colimit theorem for open covers. This module isolates the
standard based-group consequence: after choosing connector paths, generators for the local
fundamental groups generate the fundamental group of the covered space.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology
namespace PaperVanKampenFourPieceCover

variable {Y : Type*} [TopologicalSpace Y] {base : Y}

/-- Inclusion of a subspace into its ambient space. -/
public def subsetInclusion (U : Set Y) : C(U, Y) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The central-piece fundamental group mapped to the ambient base point. -/
public def coreFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.core ⟨base, D.base_mem_core⟩ →* FundamentalGroup Y base :=
  FundamentalGroup.map (subsetInclusion D.core) ⟨base, D.base_mem_core⟩

/-- The cusp-piece fundamental group, transported to the ambient base along its connector. -/
public def cuspFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.cusp ⟨D.cuspPoint, D.cuspPoint_mem.2⟩ →* FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath D.cuspConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.cusp) ⟨D.cuspPoint, D.cuspPoint_mem.2⟩)

/-- The order-three filling fundamental group, transported to the ambient base. -/
public def ellipticThreeFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.ellipticThree
        ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem.2⟩ →*
      FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      D.ellipticThreeConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.ellipticThree)
      ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem.2⟩)

/-- The order-four filling fundamental group, transported to the ambient base. -/
public def ellipticFourFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.ellipticFour
        ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem.2⟩ →*
      FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      D.ellipticFourConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.ellipticFour)
      ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem.2⟩)

/-- A subgroup containing the images of the four local fundamental groups is the whole ambient
fundamental group. This is the based-group generator consequence of groupoid van Kampen. -/
public axiom localFundamentalGroupImages_generate
    (D : PaperVanKampenFourPieceCover base)
    (H : Subgroup (FundamentalGroup Y base))
    (hcore : D.coreFundamentalGroupMap.range ≤ H)
    (hcusp : D.cuspFundamentalGroupMap.range ≤ H)
    (hthree : D.ellipticThreeFundamentalGroupMap.range ≤ H)
    (hfour : D.ellipticFourFundamentalGroupMap.range ≤ H) :
    H = ⊤

end PaperVanKampenFourPieceCover
end SphereSixComplex.Topology

end
