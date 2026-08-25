module

public import SphereSixComplex.Topology.BoundarySevenFaceNeighborhoodLocalComparison
public import SphereSixComplex.Topology.BoundarySevenRealizationInjective
public import SphereSixComplex.Topology.DiskSevenCoverRangeGeometryChains

/-!
# Low integral homology of the standard six-sphere: the exact remaining comparison

The simplicial boundary of the seven-simplex has already been proved to have zero integral
homology in degrees two and three, and its realization has already been identified with the
standard six-sphere.  Consequently the desired singular-homology calculation needs only the
degree-two and degree-three pieces of the canonical simplicial-to-singular comparison; a full
quasi-isomorphism in every degree is unnecessary.

This file records that sharp equivalence and connects it to the completed local relative
Mayer--Vietoris calculation for the seven-disk.  It also isolates a degreewise Čech-total input
which is strictly weaker than the earlier all-degree Čech comparison structure.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- The canonical integral comparison for the boundary of the seven-simplex. -/
public noncomputable abbrev boundarySevenIntegralComparisonMap :=
  simplicialToRealizationSingularChainMap
    (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)

/-- Only the two degrees actually needed in the six-sphere argument. -/
public def BoundarySevenLowIntegralComparison : Prop :=
  QuasiIsoAt boundarySevenIntegralComparisonMap 2 ∧
    QuasiIsoAt boundarySevenIntegralComparisonMap 3

/-- A full canonical comparison immediately supplies its two low-degree components. -/
public theorem boundarySevenLowIntegralComparison_of_quasiIso
    (h : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) :
    BoundarySevenLowIntegralComparison := by
  change QuasiIso boundarySevenIntegralComparisonMap at h
  exact ⟨(quasiIso_iff boundarySevenIntegralComparisonMap).mp h 2,
    (quasiIso_iff boundarySevenIntegralComparisonMap).mp h 3⟩

/-- The low comparison is exactly equivalent to low singular-homology vanishing on the
realization.  The reverse implication uses the already computed vanishing of simplicial
homology, so any map between the two zero homology objects is an isomorphism. -/
public theorem boundarySevenLowIntegralComparison_iff_realization_low_isZero :
    BoundarySevenLowIntegralComparison ↔
      IsZero (((TopCat.toSSet.obj (SSet.toTop.obj (∂Δ[7] : SSet.{0}))).chainComplex
        (AddCommGrpCat.of ℤ)).homology 2) ∧
      IsZero (((TopCat.toSSet.obj (SSet.toTop.obj (∂Δ[7] : SSet.{0}))).chainComplex
        (AddCommGrpCat.of ℤ)).homology 3) := by
  constructor
  · rintro ⟨h₂, h₃⟩
    let _ : QuasiIsoAt boundarySevenIntegralComparisonMap 2 := h₂
    let _ : QuasiIsoAt boundarySevenIntegralComparisonMap 3 := h₃
    exact
      ⟨(boundarySeven_simplicialHomology_two_isZero (AddCommGrpCat.of ℤ)).of_iso
          (isoOfQuasiIsoAt boundarySevenIntegralComparisonMap 2).symm,
        (boundarySeven_simplicialHomology_three_isZero (AddCommGrpCat.of ℤ)).of_iso
          (isoOfQuasiIsoAt boundarySevenIntegralComparisonMap 3).symm⟩
  · rintro ⟨h₂, h₃⟩
    constructor
    · rw [quasiIsoAt_iff_isIso_homologyMap]
      exact (boundarySeven_simplicialHomology_two_isZero
        (AddCommGrpCat.of ℤ)).isIso h₂ _
    · rw [quasiIsoAt_iff_isIso_homologyMap]
      exact (boundarySeven_simplicialHomology_three_isZero
        (AddCommGrpCat.of ℤ)).isIso h₃ _

/-- The completed realization homeomorphism, followed by the project's identification of its
metric sphere with `TopCat.sphere 6`. -/
public noncomputable def boundarySevenRealizationHomeomorphTopCatSphereSix :
    (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ
      (TopCat.sphere.{0} 6 : Type) :=
  Classical.choice boundarySevenRealizationHomeomorphSixSphere |>.trans
    sixSphereHomeomorphTopCatSphereSix

/-- Degreewise integral singular homology is transported by the preceding homeomorphism. -/
public noncomputable def boundarySevenRealizationHomologyIsoTopCatSphereSix (k : ℕ) :
    ((IntegralSingularChainComplexObj
      (SSet.toTop.obj (∂Δ[7] : SSet.{0}))).homology k) ≅
      ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology k) :=
  ((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).mapIso
      (TopCat.isoOfHomeo boundarySevenRealizationHomeomorphTopCatSphereSix)

/-- Thus the two desired standard-sphere vanishings are equivalent to the two degreewise
components of the canonical boundary comparison. -/
public theorem boundarySevenLowIntegralComparison_iff_standardSphereSix_low_isZero :
    BoundarySevenLowIntegralComparison ↔
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology 3) := by
  rw [boundarySevenLowIntegralComparison_iff_realization_low_isZero]
  constructor
  · rintro ⟨h₂, h₃⟩
    exact
      ⟨h₂.of_iso (boundarySevenRealizationHomologyIsoTopCatSphereSix 2).symm,
        h₃.of_iso (boundarySevenRealizationHomologyIsoTopCatSphereSix 3).symm⟩
  · rintro ⟨h₂, h₃⟩
    exact
      ⟨h₂.of_iso (boundarySevenRealizationHomologyIsoTopCatSphereSix 2),
        h₃.of_iso (boundarySevenRealizationHomologyIsoTopCatSphereSix 3)⟩

/-- The disk-cover local acyclicity obligation is neither stronger nor weaker than the missing
low-degree boundary comparison: they are exactly equivalent. -/
public theorem diskSevenCoverLocalRelativeLowAcyclic_iff_boundarySevenLowIntegralComparison :
    DiskSevenCoverLocalRelativeLowAcyclic ↔ BoundarySevenLowIntegralComparison := by
  rw [diskSevenCoverLocalRelativeLowAcyclic_iff_sphereSix_low_isZero,
    boundarySevenLowIntegralComparison_iff_standardSphereSix_low_isZero]

/-- A direct endpoint producing both standard-sphere homology vanishings from the minimal
degreewise comparison input. -/
public theorem standardSphereSix_integralSingularHomology_low_isZero_of_boundaryLowComparison
    (h : BoundarySevenLowIntegralComparison) :
    IsZero ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology 3) :=
  boundarySevenLowIntegralComparison_iff_standardSphereSix_low_isZero.mp h

/-- The same minimal comparison input discharges all four fields of the local relative
Mayer--Vietoris acyclicity package. -/
public theorem diskSevenCoverLocalRelativeLowAcyclic_of_boundaryLowComparison
    (h : BoundarySevenLowIntegralComparison) :
    DiskSevenCoverLocalRelativeLowAcyclic :=
  diskSevenCoverLocalRelativeLowAcyclic_iff_boundarySevenLowIntegralComparison.mpr h

/-! ## A degreewise Čech-total endpoint -/

/-- The remaining global Čech construction can be restricted to degrees two and three.  Unlike
`BoundarySevenFaceNeighborhoodCechTotalComparison`, this structure asks for no quasi-isomorphism
outside those two degrees. -/
public structure BoundarySevenFaceNeighborhoodCechLowComparison where
  boundaryToCech :
    (∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ) ⟶
      boundarySevenFaceNeighborhoodCechTotal
  augmentation :
    boundarySevenFaceNeighborhoodCechTotal ⟶
      CoverSmallIntegralSingularChainComplex
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood
  fac : boundaryToCech ≫ augmentation =
    simplicialToCoverSmallSingularChainMap
      (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
      boundarySevenComparisonUnitLandsInFaceNeighborhoods
  boundaryToCech_quasiIsoAt_two : QuasiIsoAt boundaryToCech 2
  boundaryToCech_quasiIsoAt_three : QuasiIsoAt boundaryToCech 3
  augmentation_quasiIsoAt_two : QuasiIsoAt augmentation 2
  augmentation_quasiIsoAt_three : QuasiIsoAt augmentation 3

/-- A full Čech-total comparison restricts to the low-degree one. -/
public noncomputable def BoundarySevenFaceNeighborhoodCechTotalComparison.toLow
    (h : BoundarySevenFaceNeighborhoodCechTotalComparison) :
    BoundarySevenFaceNeighborhoodCechLowComparison where
  boundaryToCech := h.boundaryToCech
  augmentation := h.augmentation
  fac := h.fac
  boundaryToCech_quasiIsoAt_two := h.boundaryToCech_quasiIso.quasiIsoAt 2
  boundaryToCech_quasiIsoAt_three := h.boundaryToCech_quasiIso.quasiIsoAt 3
  augmentation_quasiIsoAt_two := h.augmentation_quasiIso.quasiIsoAt 2
  augmentation_quasiIsoAt_three := h.augmentation_quasiIso.quasiIsoAt 3

/-- A low Čech-total comparison gives the two degreewise quasi-isomorphisms for the cover-small
lift. -/
public theorem boundarySevenFaceNeighborhoodLift_lowComparison_of_cechLow
    (h : BoundarySevenFaceNeighborhoodCechLowComparison) :
    QuasiIsoAt
        (simplicialToCoverSmallSingularChainMap
          (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
          boundarySevenComparisonUnitLandsInFaceNeighborhoods) 2 ∧
      QuasiIsoAt
        (simplicialToCoverSmallSingularChainMap
          (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
          boundarySevenComparisonUnitLandsInFaceNeighborhoods) 3 := by
  constructor
  · rw [← h.fac]
    exact quasiIsoAt_comp h.boundaryToCech h.augmentation 2
      (hφ := h.boundaryToCech_quasiIsoAt_two)
      (hφ' := h.augmentation_quasiIsoAt_two)
  · rw [← h.fac]
    exact quasiIsoAt_comp h.boundaryToCech h.augmentation 3
      (hφ := h.boundaryToCech_quasiIsoAt_three)
      (hφ' := h.augmentation_quasiIsoAt_three)

/-- Since inclusion of cover-small chains is already a quasi-isomorphism by affine
subdivision, the low Čech-total package suffices for the desired low canonical comparison. -/
public theorem boundarySevenLowIntegralComparison_of_cechLow
    (h : BoundarySevenFaceNeighborhoodCechLowComparison) :
    BoundarySevenLowIntegralComparison := by
  have hlift := boundarySevenFaceNeighborhoodLift_lowComparison_of_cechLow h
  have hinclusion : QuasiIso
      (coverSmallIntegralSingularChainInclusion
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
        boundarySevenComparisonFaceNeighborhood) :=
    coverSmallChainQuasiIsomorphism_of_openCover
      (SSet.toTop.obj (∂Δ[7] : SSet.{0}))
      boundarySevenComparisonFaceNeighborhood
      boundarySevenComparisonFaceNeighborhood_isOpen
      boundarySevenComparisonFaceNeighborhood_iUnion_unconditional
  constructor
  · change QuasiIsoAt
      (simplicialToRealizationSingularChainMap
        (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) 2
    rw [← simplicialToCoverSmallSingularChainMap_comp_inclusion
      (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
      boundarySevenComparisonUnitLandsInFaceNeighborhoods]
    exact quasiIsoAt_comp _ _ 2
      (hφ := hlift.1) (hφ' := hinclusion.quasiIsoAt 2)
  · change QuasiIsoAt
      (simplicialToRealizationSingularChainMap
        (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) 3
    rw [← simplicialToCoverSmallSingularChainMap_comp_inclusion
      (∂Δ[7] : SSet.{0}) boundarySevenComparisonFaceNeighborhood
      boundarySevenComparisonUnitLandsInFaceNeighborhoods]
    exact quasiIsoAt_comp _ _ 3
      (hφ := hlift.2) (hφ' := hinclusion.quasiIsoAt 3)

/-- Consequently a degreewise Čech-total comparison proves the local relative acyclicity and
the two low standard-sphere homology vanishings simultaneously. -/
public theorem sixSphere_lowHomology_and_diskLocalAcyclic_of_cechLow
    (h : BoundarySevenFaceNeighborhoodCechLowComparison) :
    (IsZero ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology 2) ∧
      IsZero ((IntegralSingularChainComplexObj (TopCat.sphere.{0} 6)).homology 3)) ∧
      DiskSevenCoverLocalRelativeLowAcyclic := by
  have hc := boundarySevenLowIntegralComparison_of_cechLow h
  exact ⟨standardSphereSix_integralSingularHomology_low_isZero_of_boundaryLowComparison hc,
    diskSevenCoverLocalRelativeLowAcyclic_of_boundaryLowComparison hc⟩

end SphereSixComplex
