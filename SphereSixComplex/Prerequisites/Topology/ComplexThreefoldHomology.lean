module

public import SphereSixComplex.Prerequisites.Topology.EstablishedCompactSmoothOrientedManifoldHomology
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory
open scoped ContDiff Manifold
namespace SphereSixComplex

/-- Classical compact oriented-manifold homology specialized to a complex threefold.

The complex atlas is converted to a real smooth atlas on the same model carrier. Its orientation
is constructed from the complex transition maps, whose real determinants are positive. -/
public noncomputable def establishedCompactComplexThreefoldHomologyTheory
    (X : Type) [TopologicalSpace X] [ChartedSpace ComplexModel X]
    [T2Space X] [SecondCountableTopology X]
    (hManifold : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ X)
    (hCompact : CompactSpace X) :
    ClosedOrientedSixManifoldHomologyTheory X := by
  letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ X := hManifold
  let hComplexOne : IsManifold (modelWithCornersSelf ℂ ComplexModel) 1 X := inferInstance
  let hRealOne : IsManifold (modelWithCornersSelf ℝ ComplexModel) 1 X :=
    isManifoldRealOfComplex hComplexOne
  have hdim : Module.finrank ℝ ComplexModel = 6 := by
    rw [finrank_real_of_complex]
    norm_num [ComplexModel]
  let hOrientation : SmoothAtlasOrientation 6 ComplexModel X :=
    hdim ▸ smoothAtlasOrientationOfComplex hComplexOne
  exact establishedCompactSmoothOrientedManifoldHomologyTheory
    6 ComplexModel X hRealOne hOrientation hCompact

/-- Degree-zero homology of a connected complex manifold is infinite cyclic. -/
public noncomputable def connectedComplexManifoldHomologyZeroEquivInteger
    (X : Type) [TopologicalSpace X] [ChartedSpace ComplexModel X]
    (hConnected : ConnectedSpace X) : IntegralSingularHomology 0 X ≃+ ℤ := by
  let _ : ConnectedSpace X := hConnected
  let _ : LocallyPathConnectedSpace X :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel X
  let _ : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  exact (asIso ((TopCat.of X).singularHomology₀ε (AddCommGrpCat.of ℤ)))
    |>.addCommGroupIsoToAddEquiv

end SphereSixComplex
