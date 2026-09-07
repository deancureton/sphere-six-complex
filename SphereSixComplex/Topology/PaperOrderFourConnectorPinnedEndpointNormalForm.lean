module

public import SphereSixComplex.Topology.PaperActualEllipticConnectorDeckEvaluationCompletion

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- Acting on the connector point by the inverse classified order-four deck word prepends
the corresponding affine-presentation loop in the based-path universal cover. -/
public theorem orderFourClassifiedCentralProductDeck_inv_smul_productConnector :
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.orderFourActualCentralProductConnector
    orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
        A.centralAffineUniversalCoverPointOfPath beta =
      TauCeti.UniversalCover.mk A.orderFourActualEllipticCentralBase
        ((paperPuncturedGlobalFamilyAffinePresentation A
          orderFourFillingRelationClassifiedCentralProductDeck).toPath.trans
            (Path.Homotopic.Quotient.mk beta)) := by
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let beta := A.orderFourActualCentralProductConnector
  change (paperPuncturedGlobalFamilyAffinePresentation A
      orderFourFillingRelationClassifiedCentralProductDeck⁻¹) •
      TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
        (BasedPath.ofPath beta) = _
  rw [map_inv, TauCeti.UniversalCover.ofBasedPath_ofPath,
    TauCeti.UniversalCover.inv_smul_mk]

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
