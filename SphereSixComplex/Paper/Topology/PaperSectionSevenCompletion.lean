module

public import SphereSixComplex.Paper.Geometry.PaperGluingDataReduction
public import SphereSixComplex.Paper.Topology.EstablishedPaperSectionSevenAffineCompletion
public import SphereSixComplex.Paper.Topology.EstablishedPaperSectionSevenCuspCompletion

/-!
# Completion of the Section 7 construction

The established radial topology and cusp comparison feed the exact reduction to the positive
degree Mayer--Vietoris calculation and hence to the paper's gluing data.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-- The paper's affine radial and cusp comparison theorems produce the complete gluing datum. -/
public theorem exists_paperGluingData_from_sectionSeven : Nonempty PaperGluingData := by
  let A := Geometry.chosenPaperAnalyticData
  let R := A.affineRadialCompletionInput
  exact Geometry.exists_paperGluingData_of_positiveDegreeAssembly
    (Geometry.PaperAnalyticData.EstablishedSectionSevenCuspTopology.correctedPositiveDegreeAssembly R)

end SphereSixComplex
