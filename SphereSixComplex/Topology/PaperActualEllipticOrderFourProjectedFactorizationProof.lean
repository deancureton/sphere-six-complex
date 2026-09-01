module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourPuncturedProductSplittingProof

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The fibre-then-base factorization after projection to the central family and the canonical
endpoint cast to the selected order-four elliptic basepoint. -/
public noncomputable def orderFourCentralFiberThenBaseLoop :
    letI := A.orderFourActualEllipticBoundaryAction
    Path A.orderFourActualEllipticCentralBase A.orderFourActualEllipticCentralBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact (A.orderFourRegularFiberThenBaseLoop.map
    A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
      A.orderFourCollarRegularRepresentative_base_projects.symm
      A.orderFourCollarRegularRepresentative_base_projects.symm

/-- Projecting the punctured-carrier splitting gives an endpoint-relative homotopy from the
actual order-four filling loop to its central fibre-then-base factorization. -/
public theorem orderFourProjectedRegularLoop_homotopic_fiberThenBase :
    letI := A.orderFourActualEllipticBoundaryAction
    Nonempty (Path.Homotopy
      ((A.orderFourFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderFourCollarRegularRepresentative_base_projects.symm
          A.orderFourCollarRegularRepresentative_base_projects.symm)
      A.orderFourCentralFiberThenBaseLoop) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rcases A.orderFourRegularLoop_homotopic_fiberThenBase with ⟨H⟩
  let Hmap := H.map
    ⟨A.centralQuotientProjection,
      A.centralQuotientProjection_isLocalHomeomorph.continuous⟩
  exact ⟨pathHomotopy_castEndpoints
    A.orderFourCollarRegularRepresentative_base_projects.symm Hmap⟩

/-- The projected factorization supplies exactly the free homotopy and equal endpoint traces
required by the final order-four free-loop reduction. -/
public theorem orderFourProjectedRegularLoop_freeHomotopy_fiberThenBase_with_trace :
    letI := A.orderFourActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy
        ((A.orderFourFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderFourCollarRegularRepresentative_base_projects.symm
            A.orderFourCollarRegularRepresentative_base_projects.symm).toContinuousMap
        A.orderFourCentralFiberThenBaseLoop.toContinuousMap,
      (H.evalAt 0).cast
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm).source.symm
          A.orderFourCentralFiberThenBaseLoop.source.symm =
        (H.evalAt 1).cast
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm).target.symm
          A.orderFourCentralFiberThenBaseLoop.target.symm := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rcases A.orderFourProjectedRegularLoop_homotopic_fiberThenBase with ⟨Hpath⟩
  let H := pathHomotopyToFreeHomotopy Hpath
  exact ⟨H, pathHomotopyToFreeHomotopy_trace Hpath⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
