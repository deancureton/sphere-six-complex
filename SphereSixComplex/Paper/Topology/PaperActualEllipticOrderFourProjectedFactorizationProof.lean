module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourPuncturedProductSplittingProof

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : AnalyticData)

/-- The fibre-then-base factorization after projection to the central family and the canonical
endpoint cast to the selected order-four elliptic basepoint. -/
public noncomputable def orderFourCentralFiberThenBaseLoop :
    letI := A.ellipticFourBoundaryAction
    Path A.ellipticFourCentralBase A.ellipticFourCentralBase := by
  let _ := A.ellipticFourBoundaryAction
  exact (A.orderFourRegularFiberThenBaseLoop.map
    A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
      A.orderFourCollarRegularRepresentative_base_projects.symm
      A.orderFourCollarRegularRepresentative_base_projects.symm

/-- Projecting the punctured-carrier splitting gives an endpoint-relative homotopy from the
actual order-four filling loop to its central fibre-then-base factorization. -/
public theorem orderFourProjectedRegularLoop_homotopic_fiberThenBase :
    letI := A.ellipticFourBoundaryAction
    Nonempty (Path.Homotopy
      ((A.orderFourFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderFourCollarRegularRepresentative_base_projects.symm
          A.orderFourCollarRegularRepresentative_base_projects.symm)
      A.orderFourCentralFiberThenBaseLoop) := by
  let _ := A.ellipticFourBoundaryAction
  rcases A.orderFourRegularLoop_homotopic_fiberThenBase with ⟨H⟩
  let Hmap := H.map
    ⟨A.centralQuotientProjection,
      A.centralQuotientProjection_isLocalHomeomorph.continuous⟩
  exact ⟨pathHomotopy_castEndpoints
    A.orderFourCollarRegularRepresentative_base_projects.symm Hmap⟩


end SphereSixComplex.Geometry.AnalyticData

end

end
