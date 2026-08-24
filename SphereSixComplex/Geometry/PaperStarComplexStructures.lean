module

public import SphereSixComplex.Geometry.PaperOpenEmbeddingStar
public import SphereSixComplex.Geometry.PaperCentralFamilyTopology

/-!
# Complex structures on the four star pieces

This module packages the existing quotient complex atlases on the central family and the three
filling pieces in the dependent indexing used by the concrete open-embedding star.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

open CuspPuncturedCollarBridge

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The selected complex atlas on the central piece of the star. -/
@[instance_reducible] public noncomputable def starCentralCharts :
    ChartedSpace ComplexModel A.CentralFamily :=
  A.centralFamilyComplexCharts

/-- The quotient complex atlases on the cusp, order-three, and order-four fillings. -/
@[instance_reducible] public noncomputable def starFillingCharts :
    ∀ i, ChartedSpace ComplexModel (A.starFillingType i) :=
  Fin.cases (actualLocalCuspFillingCharts A.starCuspWitness) fun i ↦
    Fin.cases
      (A.orderThreeFillingComplexCharts A.starSeparation.orderThree.radius)
      (fun _ ↦ A.orderFourFillingComplexCharts A.starSeparation.orderFour.radius) i

/-- The central member of the concrete star is a complex three-manifold. -/
public theorem starCentral_isManifold :
    letI := A.starCentralCharts
    IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ A.CentralFamily := by
  exact A.centralFamily_isManifold

/-- Every filling member of the concrete star is a complex three-manifold. -/
public theorem starFilling_isManifold :
    letI (i : Fin 3) := A.starFillingCharts i
    ∀ i, IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starFillingType i) := by
  intro i
  fin_cases i
  · exact actualLocalCuspFilling_isManifold A.starCuspWitness
  · exact A.orderThreeFilling_isManifold A.starSeparation.orderThree.radius
  · exact A.orderFourFilling_isManifold A.starSeparation.orderFour.radius

end PaperAnalyticData

end

end SphereSixComplex.Geometry
