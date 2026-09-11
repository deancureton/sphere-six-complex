module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeRelatorComparison

/-!
# The order-four actual and central relators

The explicit radial filling identifies the chosen order-four boundary loops with the physical
deck loops.  This module packages their single filling relator in the actual affine core and
reduces its normal-closure comparison to one common gauge/basepoint conjugacy.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology

variable (A : PaperAnalyticData)


/-- The order-four affine relator in the central marking transported to the actual core. -/
public noncomputable def orderFourCentralRelatorToCore
    (N : A.CuspCentralNaturality) :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (N.centralToCore A.centralAffineCorePiOneData.rhoTwo) ^ 4 *
    (Additive.toMul (A.actualCentralTranslationToCore N epsilon'))⁻¹






end SphereSixComplex.Geometry.PaperAnalyticData

end
