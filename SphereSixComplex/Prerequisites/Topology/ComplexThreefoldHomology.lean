module

public import SphereSixComplex.Prerequisites.Topology.EstablishedCompactSmoothOrientedManifoldHomology
public import SphereSixComplex.Prerequisites.Topology.SixSphereHomology
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory
open scoped ContDiff Manifold
namespace SphereSixComplex

/-- Classical compact oriented-manifold homology specialized to a complex threefold.

The complex atlas is converted to a real smooth atlas on the same model carrier. Its orientation
is constructed from the complex transition maps, whose real determinants are positive. -/
public noncomputable def ComplexThreefold.integralPoincareUCT
    (X : Type) [TopologicalSpace X] [ChartedSpace ComplexModel X]
    [T2Space X] [SecondCountableTopology X]
    (hManifold : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ X)
    (hCompact : CompactSpace X) :
    IntegralPoincareUCTData.Six X := by
  letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ X := hManifold
  let hComplexOne : IsManifold (modelWithCornersSelf ℂ ComplexModel) 1 X := inferInstance
  let hRealOne : IsManifold (modelWithCornersSelf ℝ ComplexModel) 1 X :=
    isManifoldRealOfComplex hComplexOne
  have hdim : Module.finrank ℝ ComplexModel = 6 := by
    rw [finrank_real_of_complex]
    norm_num [ComplexModel]
  let hOrientation : SmoothAtlasOrientation 6 ComplexModel X :=
    hdim ▸ smoothAtlasOrientationOfComplex hComplexOne
  exact SmoothAtlasOrientation.integralPoincareUCT
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

/-- A compact connected complex threefold with vanishing first and second integral homology
and Euler characteristic two has the integral homology of the six-sphere. -/
public theorem ComplexThreefold.nonempty_homologyEquiv_sixSphere
    (X : Type) [TopologicalSpace X] [ChartedSpace ComplexModel X]
    [T2Space X] [SecondCountableTopology X]
    [IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ X]
    [CompactSpace X] [ConnectedSpace X]
    (hOne : Subsingleton (IntegralSingularHomology 1 X))
    (hTwo : Subsingleton (IntegralSingularHomology 2 X))
    (hEuler : integralHomologyEulerCharacteristicSix X = 2) :
    ∀ k, Nonempty (IntegralSingularHomology k X ≃+ IntegralSingularHomology k SixSphere) := by
  let T := ComplexThreefold.integralPoincareUCT X inferInstance inferInstance
  let hZero := connectedComplexManifoldHomologyZeroEquivInteger X inferInstance
  let hThree :=
    IntegralPoincareUCTData.Six.subsingleton_homology_three_of_eulerCharacteristic T
      hZero hOne hTwo hEuler
  let hFour := IntegralPoincareUCTData.Six.subsingleton_homology_four T hOne hTwo
  let hFive := IntegralPoincareUCTData.Six.subsingleton_homology_five T hZero hOne
  let hSix := IntegralPoincareUCTData.Six.homologySixEquivInt T hZero
  intro k
  by_cases hk0 : k = 0
  · subst k
    exact ⟨hZero.trans sixSphere_integralSingularHomology_zero_equiv_integer.symm⟩
  by_cases hk6 : k = 6
  · subst k
    exact ⟨hSix.trans (Classical.choice sixSpherePositiveHomologyInputs.degreeSix).symm⟩
  have hActual : Subsingleton (IntegralSingularHomology k X) := by
    rcases Nat.lt_trichotomy k 3 with hk | rfl | hk
    · interval_cases k
      · exact False.elim (hk0 rfl)
      · exact hOne
      · exact hTwo
    · exact hThree
    · rcases lt_or_ge k 7 with hk7 | hk7
      · interval_cases k
        · exact hFour
        · exact hFive
        · exact False.elim (hk6 rfl)
      · exact T.subsingleton_homology_of_lt k (by omega)
  let := hActual
  let := sixSpherePositiveHomologyInputs.otherDegrees k hk0 hk6
  let : Unique (IntegralSingularHomology k X) := uniqueOfSubsingleton 0
  let : Unique (IntegralSingularHomology k SixSphere) := uniqueOfSubsingleton 0
  exact ⟨AddEquiv.ofUnique⟩

end SphereSixComplex
