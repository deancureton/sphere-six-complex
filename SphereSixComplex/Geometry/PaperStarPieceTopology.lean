module

public import SphereSixComplex.Geometry.PaperStarComplexStructures

/-!
# Topology of the four concrete star pieces

This module collects countability properties in the dependent indexing of the paper's four-piece
star.
-/

namespace SphereSixComplex.Geometry

open scoped ContDiff Manifold
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open CuspPuncturedCollarBridge CuspPhaseEstimates CuspPeriodExpansion
open CuspFilling CuspLocalPhaseAction
open StandardInfiniteA2ToricModel

noncomputable section

/-- The actual local cusp quotient is second countable. -/
public theorem actualLocalCuspFilling_secondCountable
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    SecondCountableTopology (actualLocalCuspFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let hdeck : ∀ gamma : Multiplicative ParameterLattice,
      ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞
        (fun p : LocalCarrier M W.localWitness.radius ↦ gamma • p) := by
    intro gamma
    convert C.genericPsiMap_holomorphic W.localWitness.fixedPoint
      (Multiplicative.toAdd gamma) using 1
    funext p
    exact (C.toCuspActionData W.localWitness.fixedPoint).psi_smul
      (Multiplicative.toAdd gamma) p
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    ⟨fun gamma ↦ (hdeck gamma).continuous⟩
  exact ContinuousConstSMul.secondCountableTopology

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Each of the three concrete filling pieces is second countable. -/
public theorem starFilling_secondCountable (i : Fin 3) :
    SecondCountableTopology (A.starFillingType i) := by
  fin_cases i
  · exact actualLocalCuspFilling_secondCountable A.starCuspWitness
  · exact A.orderThreeFilling_secondCountable A.starSeparation.orderThree.radius
  · exact A.orderFourFilling_secondCountable A.starSeparation.orderFour.radius

/-- Every piece of the concrete star diagram is second countable. -/
public theorem starPiece_secondCountable (i : Option (Fin 3)) :
    SecondCountableTopology (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.U i) := by
  cases i with
  | none => exact A.centralFamily_secondCountable
  | some i => exact A.starFilling_secondCountable i

end PaperAnalyticData

end

end SphereSixComplex.Geometry
