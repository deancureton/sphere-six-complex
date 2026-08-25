module

public import SphereSixComplex.Topology.EstablishedCompactSmoothOrientedManifoldHomology
public import SphereSixComplex.Topology.EstablishedSphereHomology
public import SphereSixComplex.Topology.IntegralHomologyEuler
public import SphereSixComplex.Topology.SectionSevenMayerVietorisHomologyAssembly
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Completing the Section 7 homology calculation by six-manifold duality

The Mayer--Vietoris calculation supplies the vanishing of `H₁` and `H₂`. General compact
oriented-manifold topology then supplies finite generation, the dimension bound, and the integral
Poincare-duality/UCT pairings needed to finish the calculation. The complex atlas orientation is
proved from its transition derivatives; only the dimension-generic classical manifold homology
theorem remains behind the reusable established-theorem boundary.

The final Section 7 theorem additionally requires the numerical Euler characteristic `2`; that
geometric calculation remains an explicit hypothesis here.
-/

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

private noncomputable def addEquivOfSubsingleton
    {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (hG : Subsingleton G) (hH : Subsingleton H) : G ≃+ H where
  toFun := 0
  invFun := 0
  left_inv x := @Subsingleton.elim G hG _ _
  right_inv x := @Subsingleton.elim H hH _ _
  map_add' _ _ := by simp

namespace OpenEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly

variable {A : OpenEmbeddingStarData}

/-- The source-faithful H₁/H₂ Mayer--Vietoris computation, together with standard closed oriented
six-manifold topology and Euler characteristic `2`, gives the complete integral homology of the
six-sphere. -/
public theorem hasIntegralHomologyOfSixSphere_of_closedComplexThreefold
    (H : A.SectionSevenMayerVietorisHomologyAssembly)
    [ChartedSpace ComplexModel (A.SectionSevenMayerVietorisSpace)]
    [T2Space (A.SectionSevenMayerVietorisSpace)]
    [SecondCountableTopology (A.SectionSevenMayerVietorisSpace)]
    (hManifold : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.SectionSevenMayerVietorisSpace))
    (hCompact : CompactSpace (A.SectionSevenMayerVietorisSpace))
    (hConnected : ConnectedSpace (A.SectionSevenMayerVietorisSpace))
    (hEuler : integralHomologyEulerCharacteristicSix
      (A.SectionSevenMayerVietorisSpace) = 2) :
    HasIntegralHomologyOfSixSphere (A.SectionSevenMayerVietorisSpace) := by
  let T := establishedCompactComplexThreefoldHomologyTheory
    (A.SectionSevenMayerVietorisSpace) hManifold hCompact
  let hZero := connectedComplexManifoldHomologyZeroEquivInteger
    (A.SectionSevenMayerVietorisSpace) hConnected
  let hOne := H.homologyOne_subsingleton
  let hTwo := H.homologyTwo_subsingleton
  let hThree := T.homologyThree_subsingleton_of_eulerCharacteristic
    hZero hOne hTwo hEuler
  let hFour := T.homologyFour_subsingleton hOne hTwo
  let hFive := T.homologyFive_subsingleton hZero hOne
  let hSix := T.homologySixEquivInteger hZero
  have hRealization : SectionSevenHomologyRealization
      (A.SectionSevenMayerVietorisSpace) := by
    intro k
    by_cases hk0 : k = 0
    · subst k
      exact ⟨hZero.trans sectionSevenComputedHomologyZeroEquivInteger.symm⟩
    by_cases hk6 : k = 6
    · subst k
      exact ⟨hSix.trans sectionSevenComputedHomologySixEquivInteger.symm⟩
    have hComputed : Subsingleton (SectionSevenComputedHomology k) :=
      sectionSevenComputedHomology_middle_subsingleton k hk0 hk6
    have hActual : Subsingleton (IntegralSingularHomology k
        (A.SectionSevenMayerVietorisSpace)) := by
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
        · exact T.homologyAboveDimension k (by omega)
    exact ⟨addEquivOfSubsingleton hActual hComputed⟩
  exact hasIntegralHomologyOfSixSphere_of_sectionSevenRealizations
    hRealization establishedSixSphereSectionSevenHomology

end OpenEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly

end SphereSixComplex
