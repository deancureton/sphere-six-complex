module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticCanonicalFiniteMarking

/-!
# The order-three actual and central relators

The explicit radial filling identifies the chosen order-three boundary loops with the physical
deck loops.  This module packages their single filling relator in the actual affine core and
records the exact conjugacy statement sufficient for the normal-closure bridge.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Topology

/-- Conjugating a relator does not move it out of the normal closure it generates. -/
public theorem conjugate_mem_normalClosure_singleton
    {G : Type*} [Group G] (c r : G) :
    c * r * c⁻¹ ∈ Subgroup.normalClosure ({r} : Set G) := by
  exact (Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem r
    (Subgroup.subset_normalClosure (Set.mem_singleton r)) c



end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology

variable (A : AnalyticData)


/-- The order-three affine relator in the central marking transported to the actual core. -/
public noncomputable def orderThreeCentralRelatorToCore
    (N : A.CuspCentralNaturality) :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (N.centralToCore A.centralAffineCorePiOneData.rhoOne) ^ 3 *
    (Additive.toMul (A.actualCentralTranslationToCore N (-epsilon)))⁻¹






end SphereSixComplex.Geometry.AnalyticData

end
