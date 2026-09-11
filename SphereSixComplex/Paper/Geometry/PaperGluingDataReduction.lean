module

public import SphereSixComplex.Paper.Geometry.PaperSectionSevenHomology
public import SphereSixComplex.Paper.Topology.PaperActualAffineFillingCoverModels
public import SphereSixComplex.Paper.Topology.PaperCuspCollarFourTorusFiber

/-!
# Gluing from the positive-degree Mayer–Vietoris calculation

The van Kampen calculation and top-degree vanishing are already proved for the chosen
analytic data. The positive-degree Mayer–Vietoris calculation supplies the remaining homology
input to the four-piece gluing.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry

/-- The positive-degree calculation completes the gluing data for the chosen analytic family. -/
public theorem exists_paperGluingData_of_positiveDegreeAssembly
    (H : chosenPaperAnalyticData.PositiveDegreeHomologyAssembly) :
    Nonempty PaperGluingData :=
  ⟨chosenPaperAnalyticData.toPaperGluingData_of_positiveDegree
      establishedPaperStarHasVanKampenData H
      chosenPaperAnalyticData.stageTopDegreeVanishing⟩

end SphereSixComplex.Geometry

end

end
