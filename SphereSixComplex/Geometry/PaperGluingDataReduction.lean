module

public import SphereSixComplex.Geometry.PaperSectionSevenHomology
public import SphereSixComplex.Topology.PaperActualAffineFillingCoverModels
public import SphereSixComplex.Topology.PaperCuspCollarFourTorusFibre

/-!
# What the paper's gluing data still needs

`toPaperGluingData_of_positiveDegree` asks for three things: the van Kampen datum for the glued
star, the positive-degree homology assembly, and the Section 7 top-degree vanishing.  Two of the
three are available for the production analytic package, so the gluing data rests on the
positive-degree assembly alone.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry

/-- The production gluing data, given the one Section 7 obligation that is still open. -/
public theorem exists_paperGluingData_of_positiveDegreeAssembly
    (H : establishedPaperAnalyticData.SectionSevenPositiveDegreeHomologyAssembly) :
    Nonempty PaperGluingData :=
  ⟨establishedPaperAnalyticData.toPaperGluingData_of_positiveDegree
      establishedPaperStarHasVanKampenData H
      establishedPaperAnalyticData.sectionSevenStageTopDegreeVanishing_actual⟩

end SphereSixComplex.Geometry

end

end
