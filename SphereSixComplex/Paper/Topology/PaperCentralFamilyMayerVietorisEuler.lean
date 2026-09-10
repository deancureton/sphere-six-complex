module

public import SphereSixComplex.Prerequisites.Topology.HomeomorphHomotopyEquivalence
public import SphereSixComplex.Paper.Topology.PaperActualCollarMappingTorusEuler
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOverlapInterleaving
public import SphereSixComplex.Paper.Topology.SectionSevenLocalEulerModels
public import SphereSixComplex.Paper.Topology.SectionSevenStageTopDegree

/-!
# The central family from its affine two-region cover

The two affine half-plane regions cover the regular central image.  Each region is homotopy
equivalent to the corresponding elliptic collar, while their intersection is the trivial
four-torus bundle over the convex central band.  Mayer--Vietoris therefore gives finite homology
and Euler characteristic zero without a finite-CW bundle realization of the full central family.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex

private theorem subsingleton_homology_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (e : X ≃ₕ Y)
    (hY : Subsingleton (IntegralSingularHomology k Y)) :
    Subsingleton (IntegralSingularHomology k X) := by
  let eH := integralSingularHomologyEquivOfHomotopyEquiv k e
  exact ⟨fun x y ↦ eH.injective (@Subsingleton.elim _ hY _ _)⟩

namespace Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization

variable (A : PaperAnalyticData)

/-- The order-three affine half-plane region has the homotopy type of the actual order-three
collar. -/
public noncomputable def centralOrderThreeRegionHomotopyEquiv :
    A.affineOrderThreeCentralRegion ≃ₕ
      A.openEmbeddingStarData.collarSource 1 :=
  A.orderThreeOverlapIsHomotopyEquivalence.homotopyEquiv.symm.trans
    A.orderThreeOverlapCollarHomeomorph.toHomotopyEquiv

/-- The order-four affine half-plane region has the homotopy type of the actual order-four
collar. -/
public noncomputable def centralOrderFourRegionHomotopyEquiv :
    A.affineOrderFourCentralRegion ≃ₕ
      A.openEmbeddingStarData.collarSource 2 :=
  A.orderFourOverlapIsHomotopyEquivalence.homotopyEquiv.symm.trans
    A.orderFourOverlapCollarHomeomorph.toHomotopyEquiv

public theorem centralOrderThreeRegion_integralHomologyFiniteSix :
    IntegralHomologyFiniteSix A.affineOrderThreeCentralRegion :=
  A.actualOrderThreeCollar_integralHomologyFiniteSix.homotopyEquiv
    A.centralOrderThreeRegionHomotopyEquiv.symm

public theorem centralOrderFourRegion_integralHomologyFiniteSix :
    IntegralHomologyFiniteSix A.affineOrderFourCentralRegion :=
  A.actualOrderFourCollar_integralHomologyFiniteSix.homotopyEquiv
    A.centralOrderFourRegionHomotopyEquiv.symm

public theorem centralOrderThreeRegion_euler_eq_zero :
    integralHomologyEulerCharacteristicSix
      A.affineOrderThreeCentralRegion = 0 :=
  (integralHomologyEulerCharacteristicSix_homotopyEquiv
    A.centralOrderThreeRegionHomotopyEquiv).trans
      A.actualOrderThreeCollar_euler_eq_zero

public theorem centralOrderFourRegion_euler_eq_zero :
    integralHomologyEulerCharacteristicSix
      A.affineOrderFourCentralRegion = 0 :=
  (integralHomologyEulerCharacteristicSix_homotopyEquiv
    A.centralOrderFourRegionHomotopyEquiv).trans
      A.actualOrderFourCollar_euler_eq_zero

/-- The intersection of the two affine regions is the four-torus central band. -/
public noncomputable def centralAffineRegionsIntersectionHomotopyEquiv :
    (A.affineOrderThreeCentralRegion ∩
        A.affineOrderFourCentralRegion :
      Set A.ellipticInterior) ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter :=
  (Homeomorph.setCongr
    A.actualAffineHeightSplit.centralRegions_intersection).toHomotopyEquiv.trans
      (A.affineCentralBandHomotopyEquiv
        A.affineCentralSeparation)

public theorem centralAffineRegionsIntersection_integralHomologyFiniteSix :
    IntegralHomologyFiniteSix
      (A.affineOrderThreeCentralRegion ∩
        A.affineOrderFourCentralRegion :
          Set A.ellipticInterior) :=
  (EstablishedFiniteCWTopology.additiveTorus_integralHomologyFiniteSix
    A.duplicatedSectionSevenBandParameter A.duplicatedSectionSevenBandFullRank).homotopyEquiv
      A.centralAffineRegionsIntersectionHomotopyEquiv.symm

public theorem centralAffineRegionsIntersection_euler_eq_zero :
    integralHomologyEulerCharacteristicSix
      (A.affineOrderThreeCentralRegion ∩
        A.affineOrderFourCentralRegion :
          Set A.ellipticInterior) = 0 :=
  (integralHomologyEulerCharacteristicSix_homotopyEquiv
    A.centralAffineRegionsIntersectionHomotopyEquiv).trans
      (EstablishedFiniteCWTopology.additiveTorus_euler_eq_zero
        A.duplicatedSectionSevenBandParameter A.duplicatedSectionSevenBandFullRank)

public theorem centralAffineRegionsIntersection_subsingleton_homology_six :
    Subsingleton (IntegralSingularHomology 6
      (A.affineOrderThreeCentralRegion ∩
        A.affineOrderFourCentralRegion :
          Set A.ellipticInterior)) :=
  subsingleton_homology_of_homotopyEquiv 6
    A.centralAffineRegionsIntersectionHomotopyEquiv
      (EstablishedFiniteCWTopology.additiveTorus_subsingleton_homology_six
        A.duplicatedSectionSevenBandParameter A.duplicatedSectionSevenBandFullRank)

/-- The two affine half-plane regions are exactly the regular central image. -/
public theorem centralAffineRegions_union :
    A.affineOrderThreeCentralRegion ∪
        A.affineOrderFourCentralRegion =
      A.ellipticCentralImage := by
  ext x
  constructor
  · rintro (hx | hx)
    · obtain ⟨y, _, rfl⟩ := hx
      exact y.2
    · obtain ⟨y, _, rfl⟩ := hx
      exact y.2
  · intro hx
    exact A.actualAffineHeightSplit.allocation.central_cover hx

/-- The affine union is the actual central family. -/
public noncomputable def centralAffineRegionsUnionHomeomorph :
    (A.affineOrderThreeCentralRegion ∪
        A.affineOrderFourCentralRegion :
      Set A.ellipticInterior) ≃ₜ A.openEmbeddingStarData.central :=
  (Homeomorph.setCongr A.centralAffineRegions_union).trans
    A.ellipticCentralImageHomeomorph

private theorem centralAffineRegionsUnion_subsingleton_homology_seven :
    Subsingleton (IntegralSingularHomology 7
      (A.affineOrderThreeCentralRegion ∪
        A.affineOrderFourCentralRegion :
          Set A.ellipticInterior)) := by
  apply subsingleton_homology_seven_union
  · exact A.actualAffineHeightSplit.centralHeightLowerRegion_isOpen
  · exact A.actualAffineHeightSplit.centralHeightUpperRegion_isOpen
  · exact A.centralOrderThreeRegion_integralHomologyFiniteSix.subsingleton_homology_of_six_lt
      7 (by omega)
  · exact A.centralOrderFourRegion_integralHomologyFiniteSix.subsingleton_homology_of_six_lt
      7 (by omega)
  · exact A.centralAffineRegionsIntersection_subsingleton_homology_six

private theorem centralAffineRegionsUnion_finite_and_euler :
    IntegralHomologyFiniteSix
        (A.affineOrderThreeCentralRegion ∪
          A.affineOrderFourCentralRegion :
            Set A.ellipticInterior) ∧
      integralHomologyEulerCharacteristicSix
        (A.affineOrderThreeCentralRegion ∪
          A.affineOrderFourCentralRegion :
            Set A.ellipticInterior) = 0 := by
  obtain ⟨hfinite, heuler⟩ :=
    integralMayerVietorisEulerAdditivitySix_of_topDegreeVanishing
      A.affineOrderThreeCentralRegion
      A.affineOrderFourCentralRegion
      A.actualAffineHeightSplit.centralHeightLowerRegion_isOpen
      A.actualAffineHeightSplit.centralHeightUpperRegion_isOpen
      A.centralOrderThreeRegion_integralHomologyFiniteSix
      A.centralOrderFourRegion_integralHomologyFiniteSix
      A.centralAffineRegionsIntersection_integralHomologyFiniteSix
      A.centralAffineRegionsUnion_subsingleton_homology_seven
  refine ⟨hfinite, ?_⟩
  rw [heuler, A.centralOrderThreeRegion_euler_eq_zero,
    A.centralOrderFourRegion_euler_eq_zero,
    A.centralAffineRegionsIntersection_euler_eq_zero]
  norm_num

/-- The actual regular central family has finite integral homology through dimension six. -/
public theorem centralFamily_integralHomologyFiniteSix :
    IntegralHomologyFiniteSix A.openEmbeddingStarData.central :=
  A.centralAffineRegionsUnion_finite_and_euler.1.homotopyEquiv
    A.centralAffineRegionsUnionHomeomorph.toHomotopyEquiv

/-- The actual regular central family has Euler characteristic zero. -/
public theorem centralFamily_euler_eq_zero :
    integralHomologyEulerCharacteristicSix A.openEmbeddingStarData.central = 0 := by
  exact (integralHomologyEulerCharacteristicSix_homotopyEquiv
    A.centralAffineRegionsUnionHomeomorph.toHomotopyEquiv).symm.trans
      A.centralAffineRegionsUnion_finite_and_euler.2

/-- Direct central model used by the local Section 7 assembly. -/
public theorem centralHomologyEulerModel :
    CentralHomologyEulerModel A.openEmbeddingStarData.central where
  integralHomologyFiniteSix := A.centralFamily_integralHomologyFiniteSix
  euler_eq_zero := A.centralFamily_euler_eq_zero

end Geometry.PaperAnalyticData

end SphereSixComplex

end
