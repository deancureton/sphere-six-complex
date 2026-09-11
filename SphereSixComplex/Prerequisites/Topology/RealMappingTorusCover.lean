module

public import SphereSixComplex.Prerequisites.Geometry.QuotientTopology
public import SphereSixComplex.Prerequisites.Topology.CyclicPuncturedProductMappingTorus

open Set Topology
namespace SphereSixComplex.CyclicAngularFundamentalDomain
noncomputable section

variable {T : Type} [TopologicalSpace T]









/-- The same real-line cover, transported to the cylinder presentation `CircleMappingTorus`. -/
@[expose] public def circleMappingTorusRealCoverProjection (φ : T ≃ₜ T) :
    C(ℝ × T, CircleMappingTorus φ) where
  toFun p := realMappingTorusHomeomorph φ
    (Quotient.mk (realMappingTorusSetoid φ) p)
  continuous_toFun :=
    (realMappingTorusHomeomorph φ).continuous.comp continuous_quot_mk





end
end SphereSixComplex.CyclicAngularFundamentalDomain
