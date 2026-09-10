module

public import SphereSixComplex.Prerequisites.Topology.ComplexThreefoldHomology
public import SphereSixComplex.Paper.Topology.EstablishedSphereHomology
public import SphereSixComplex.Prerequisites.Topology.IntegralHomologyEuler
public import SphereSixComplex.Paper.Topology.SectionSevenMayerVietorisHomologyAssembly
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
  let T := ComplexThreefold.integralPoincareUCT
    (A.SectionSevenMayerVietorisSpace) hManifold hCompact
  let hZero := connectedComplexManifoldHomologyZeroEquivInteger
    (A.SectionSevenMayerVietorisSpace) hConnected
  let hOne := H.homologyOne_subsingleton
  let hTwo := H.homologyTwo_subsingleton
  let hThree :=
    IntegralPoincareUCTData.Six.subsingleton_homology_three_of_eulerCharacteristic T
    hZero hOne hTwo hEuler
  let hFour := IntegralPoincareUCTData.Six.subsingleton_homology_four T hOne hTwo
  let hFive := IntegralPoincareUCTData.Six.subsingleton_homology_five T hZero hOne
  let hSix := IntegralPoincareUCTData.Six.homologySixEquivInt T hZero
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
        · exact T.subsingleton_homology_of_lt k (by omega)
    exact ⟨addEquivOfSubsingleton hActual hComputed⟩
  exact hasIntegralHomologyOfSixSphere_of_sectionSevenRealizations
    hRealization establishedSixSphereSectionSevenHomology

end OpenEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly

end SphereSixComplex
