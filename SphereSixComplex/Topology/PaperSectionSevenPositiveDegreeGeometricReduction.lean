module

public import SphereSixComplex.Topology.PaperSectionSevenPositiveDegreeRealization
public import SphereSixComplex.Topology.EstablishedStrongDeformationRetracts

/-!
# Geometric reduction of the Section 7 positive-degree input

The regular central image can be assigned to both elliptic sides, so the allocation itself is
canonical.  The remaining radial input is the contraction and band-trivialization package.  Once
any two-disc cover and its marked cycles have been realized, they directly supply the production
positive-degree homology assembly.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set Topology
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Assign the whole regular central image to both elliptic sides. -/
public def duplicatedSectionSevenEllipticCentralAllocation :
    A.SectionSevenEllipticCentralAllocation where
  orderThreeCentral := A.sectionSevenEllipticCentralImage
  orderFourCentral := A.sectionSevenEllipticCentralImage
  orderThreeCentral_isOpen := A.sectionSevenEllipticCentralImage_isOpen
  orderFourCentral_isOpen := A.sectionSevenEllipticCentralImage_isOpen
  central_cover := fun _ hx ↦ Or.inl hx

/-- A nested subspace is canonically homeomorphic to the same set in the original ambient
space. -/
public def nestedSubtypeHomeomorph {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hVU : V ⊆ U) :
    (Subtype.val ⁻¹' V : Set U) ≃ₜ V where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, hVU x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The order-three filling regarded as a subspace of its duplicated-central side. -/
public def duplicatedOrderThreeFillingSubspace :
    Set A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide :=
  Subtype.val ⁻¹' A.sectionSevenOrderThreeFillingImage

/-- The order-four filling regarded as a subspace of its duplicated-central side. -/
public def duplicatedOrderFourFillingSubspace :
    Set A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide :=
  Subtype.val ⁻¹' A.sectionSevenOrderFourFillingImage

public theorem sectionSevenOrderThreeFillingImage_subset_duplicatedSide :
    A.sectionSevenOrderThreeFillingImage ⊆
      A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide :=
  fun _ hx ↦ Or.inl hx

public theorem sectionSevenOrderFourFillingImage_subset_duplicatedSide :
    A.sectionSevenOrderFourFillingImage ⊆
      A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide :=
  fun _ hx ↦ Or.inl hx

/-- The two concrete filling inclusions are homotopy equivalences.  This is precisely the input
needed for the lifted contractions required by the radial realization. -/
public structure DuplicatedSectionSevenLiftedContractionInput where
  orderThreeHomotopyEquivalence :
    IsHomotopyEquivalenceInclusion A.duplicatedOrderThreeFillingSubspace
  orderFourHomotopyEquivalence :
    IsHomotopyEquivalenceInclusion A.duplicatedOrderFourFillingSubspace

namespace DuplicatedSectionSevenLiftedContractionInput

variable {A : PaperAnalyticData}

/-- Upgrade the order-three filling inclusion to the required lifted contraction. -/
public noncomputable def orderThreeLiftedContraction
    (L : A.DuplicatedSectionSevenLiftedContractionInput) :
    A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide ≃ₕ
      A.sectionSevenOrderThreeFillingImage :=
  L.orderThreeHomotopyEquivalence.toHomotopyEquiv.trans
    (nestedSubtypeHomeomorph
      A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide
      A.sectionSevenOrderThreeFillingImage
      A.sectionSevenOrderThreeFillingImage_subset_duplicatedSide).toHomotopyEquiv

/-- Upgrade the order-four filling inclusion to the required lifted contraction. -/
public noncomputable def orderFourLiftedContraction
    (L : A.DuplicatedSectionSevenLiftedContractionInput) :
    A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide ≃ₕ
      A.sectionSevenOrderFourFillingImage :=
  L.orderFourHomotopyEquivalence.toHomotopyEquiv.trans
    (nestedSubtypeHomeomorph
      A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide
      A.sectionSevenOrderFourFillingImage
      A.sectionSevenOrderFourFillingImage_subset_duplicatedSide).toHomotopyEquiv

end DuplicatedSectionSevenLiftedContractionInput

/-- After the two filling inclusions have been upgraded to lifted contractions, these are exactly
the remaining band and inclusion-compatibility fields of the duplicated-central radial
realization. -/
public structure DuplicatedSectionSevenRadialBandInput
    (L : A.DuplicatedSectionSevenLiftedContractionInput) where
  bandParameter : SphereSixComplex.Periods.Parameters
  bandFullRank : FullRank bandParameter
  bandHomotopyEquiv :
    (A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide ∩
      A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide :
        Set A.SectionSevenEllipticInterior) ≃ₕ AdditiveTorus bandParameter
  bandToOrderThreeCoverSource :
    AdditiveTorus bandParameter ≃ₜ
      RadialEllipticActionData.centralFiberCoverSource
        (orderThreeRadialActionData A.periods)
  bandToOrderFourCoverSource :
    AdditiveTorus bandParameter ≃ₜ
      RadialEllipticActionData.centralFiberCoverSource
        (orderFourRadialActionData A.periods)
  orderThree_inclusion_compatibility :
    (((A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
      L.orderThreeLiftedContraction.toFun).comp
        (IntegralMayerVietoris.interToLeft
          A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide
          A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)).comp
        ⟨bandToOrderThreeCoverSource,
          bandToOrderThreeCoverSource.continuous⟩ |>.comp bandHomotopyEquiv.toFun)
  orderFour_inclusion_compatibility :
    (((A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
      L.orderFourLiftedContraction.toFun).comp
        (IntegralMayerVietoris.interToRight
          A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide
          A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)).comp
        ⟨bandToOrderFourCoverSource,
          bandToOrderFourCoverSource.continuous⟩ |>.comp bandHomotopyEquiv.toFun)

namespace DuplicatedSectionSevenRadialBandInput

variable {A : PaperAnalyticData} {L : A.DuplicatedSectionSevenLiftedContractionInput}

/-- Assemble the duplicated-central radial realization from the four concrete inclusion
properties and the remaining band data. -/
public noncomputable def toRadialRealization
    (B : A.DuplicatedSectionSevenRadialBandInput L) :
    A.duplicatedSectionSevenEllipticCentralAllocation.RadialRealization where
  orderThreeLiftedContraction := L.orderThreeLiftedContraction
  orderFourLiftedContraction := L.orderFourLiftedContraction
  bandParameter := B.bandParameter
  bandFullRank := B.bandFullRank
  bandHomotopyEquiv := B.bandHomotopyEquiv
  bandToOrderThreeCoverSource := B.bandToOrderThreeCoverSource
  bandToOrderFourCoverSource := B.bandToOrderFourCoverSource
  orderThree_inclusion_compatibility := B.orderThree_inclusion_compatibility
  orderFour_inclusion_compatibility := B.orderFour_inclusion_compatibility

end DuplicatedSectionSevenRadialBandInput

/-- The canonical central allocation and a radial realization extend by exactly the dependent
marked-cycle package to the complete geometric realization. -/
public def SectionSevenPositiveDegreeGeometricRealization.ofDuplicatedCentralAllocation
    (R : A.duplicatedSectionSevenEllipticCentralAllocation.RadialRealization)
    (M : A.SectionSevenEllipticInteriorMarkedCycleData
      R.toSectionSevenEllipticTwoDiscCoverData) :
    A.SectionSevenPositiveDegreeGeometricRealization where
  allocation := A.duplicatedSectionSevenEllipticCentralAllocation
  radial := R
  markedCycles := M

/-- A realized two-disc cover with its marked cycles is sufficient for the production
positive-degree homology assembly; no further central-allocation data enters the calculation. -/
public theorem exists_positiveDegreeHomologyAssembly_of_exists_markedCycles
    (h : ∃ D : A.SectionSevenEllipticTwoDiscCoverData,
      Nonempty (A.SectionSevenEllipticInteriorMarkedCycleData D)) :
    Nonempty A.SectionSevenPositiveDegreeHomologyAssembly := by
  obtain ⟨D, ⟨M⟩⟩ := h
  exact ⟨M.positiveDegreeHomologyAssembly⟩

/-- Every complete geometric realization determines the weaker dependent marked-cycle witness
that is sufficient for the production homology assembly. -/
public theorem SectionSevenPositiveDegreeGeometricRealization.exists_markedCycles
    (R : A.SectionSevenPositiveDegreeGeometricRealization) :
    ∃ D : A.SectionSevenEllipticTwoDiscCoverData,
      Nonempty (A.SectionSevenEllipticInteriorMarkedCycleData D) :=
  ⟨R.radial.toSectionSevenEllipticTwoDiscCoverData, ⟨R.markedCycles⟩⟩

end SphereSixComplex.Geometry.PaperAnalyticData
