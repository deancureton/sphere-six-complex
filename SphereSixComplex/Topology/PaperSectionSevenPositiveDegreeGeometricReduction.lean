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

/-- Full-rank period bases canonically identify their additive four-tori. -/
public noncomputable def fullRankAdditiveTorusHomeomorph
    (x y : Parameters) (hx : FullRank x) (hy : FullRank y) :
    AdditiveTorus x ≃ₜ AdditiveTorus y :=
  let e : ComplexTwoSpace ≃L[ℝ] ComplexTwoSpace :=
    hx.realEquiv.symm.trans hy.realEquiv
  Homeomorph.Quotient.congr e.toHomeomorph fun z w => by
    apply SphereSixComplex.Geometry.FamilyEquivariance.orbitRel_iff_of_period_equivariant
      x y (AddEquiv.refl IntegerPeriods) e.toLinearEquiv.toAddEquiv
    intro n
    change e (periodVector x n) = periodVector y n
    rw [← hx.map_integer, ← hy.map_integer]
    simp [e]

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

/-- The two distinct filling images in the star are disjoint. -/
public theorem sectionSevenEllipticFillingImages_disjoint :
    A.sectionSevenOrderThreeFillingImage ∩
      A.sectionSevenOrderFourFillingImage = ∅ := by
  ext x
  constructor
  · rintro ⟨h₃, h₄⟩
    change x.1 ∈ A.SectionSevenEllipticCover.piece 1 at h₃
    change x.1 ∈ A.SectionSevenEllipticCover.piece 2 at h₄
    have h :
        x.1 ∈ A.SectionSevenEllipticCover.piece 1 ∩
          A.SectionSevenEllipticCover.piece 2 :=
      ⟨h₃, h₄⟩
    have hdisjoint :
        A.SectionSevenEllipticCover.piece 1 ∩
          A.SectionSevenEllipticCover.piece 2 = ∅ := by
      simpa [SectionSevenEllipticCover,
        OpenEmbeddingStarData.SectionSevenMayerVietorisCover,
        sectionSevenMayerVietorisOpenCover, sectionSevenMayerVietorisOrder] using
        A.openEmbeddingStarData.fillingPiece_inter_fillingPiece
          (i := 1) (j := 2) (by decide)
    rw [hdisjoint] at h
    exact h.elim
  · simp

/-- Duplicating the whole central image makes it exactly the intersection of the two sides. -/
public theorem duplicatedSectionSevenSides_intersection :
    A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide ∩
        A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide =
      A.sectionSevenEllipticCentralImage := by
  ext x
  change ((x ∈ A.sectionSevenOrderThreeFillingImage ∨
      x ∈ A.sectionSevenEllipticCentralImage) ∧
    (x ∈ A.sectionSevenOrderFourFillingImage ∨
      x ∈ A.sectionSevenEllipticCentralImage)) ↔
    x ∈ A.sectionSevenEllipticCentralImage
  constructor
  · rintro ⟨h₃ | hc, h₄ | hc'⟩
    · have h : x ∈ A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenOrderFourFillingImage := ⟨h₃, h₄⟩
      rw [A.sectionSevenEllipticFillingImages_disjoint] at h
      exact h.elim
    · exact hc'
    · exact hc
    · exact hc
  · exact fun hc ↦ ⟨Or.inr hc, Or.inr hc⟩

/-- The duplicated-side intersection is canonically the regular central image. -/
public def duplicatedSectionSevenSidesIntersectionHomeomorph :
    (A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide ∩
      A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide :
        Set A.SectionSevenEllipticInterior) ≃ₜ
      A.sectionSevenEllipticCentralImage :=
  Homeomorph.setCongr A.duplicatedSectionSevenSides_intersection

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

/-- Use the order-three fixed period lattice as the common band parameter. -/
public def duplicatedSectionSevenBandParameter : Parameters :=
  (SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne).1

/-- The canonical band parameter has full rank. -/
public noncomputable def duplicatedSectionSevenBandFullRank :
    FullRank A.duplicatedSectionSevenBandParameter :=
  let p := SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
  FullRank.ofSetupInequalities p.1 p.2

/-- Real period coordinates identify the order-three and order-four central four-tori. -/
public noncomputable def duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph :
    AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      AdditiveTorus
        (SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 :=
  let p₄ := SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo
  fullRankAdditiveTorusHomeomorph
    A.duplicatedSectionSevenBandParameter p₄.1
    A.duplicatedSectionSevenBandFullRank
    (FullRank.ofSetupInequalities p₄.1 p₄.2)

/-- The order-three restricted covering source is the canonical band torus. -/
public noncomputable def duplicatedSectionSevenBandToOrderThreeCoverSource :
    AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      RadialEllipticActionData.centralFiberCoverSource
        (orderThreeRadialActionData A.periods) :=
  (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderThreeRadialActionData A.periods)).symm

/-- Transport the canonical band torus to the order-four restricted covering source. -/
public noncomputable def duplicatedSectionSevenBandToOrderFourCoverSource :
    AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      RadialEllipticActionData.centralFiberCoverSource
        (orderFourRadialActionData A.periods) :=
  A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.trans
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
      (orderFourRadialActionData A.periods)).symm

/-- Once the filling inclusions have been upgraded, only the band equivalence and its two
compatibility homotopies remain. -/
public structure DuplicatedSectionSevenRadialBandInput
    (L : A.DuplicatedSectionSevenLiftedContractionInput) where
  centralBandHomotopyEquiv :
    A.sectionSevenEllipticCentralImage ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter
  orderThree_inclusion_compatibility :
    (((A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
      L.orderThreeLiftedContraction.toFun).comp
        (IntegralMayerVietoris.interToLeft
          A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide
          A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
          A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩ |>.comp
            (A.duplicatedSectionSevenSidesIntersectionHomeomorph.toHomotopyEquiv.trans
              centralBandHomotopyEquiv).toFun)
  orderFour_inclusion_compatibility :
    (((A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
      L.orderFourLiftedContraction.toFun).comp
        (IntegralMayerVietoris.interToRight
          A.duplicatedSectionSevenEllipticCentralAllocation.orderThreeSide
          A.duplicatedSectionSevenEllipticCentralAllocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
          A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩ |>.comp
            (A.duplicatedSectionSevenSidesIntersectionHomeomorph.toHomotopyEquiv.trans
              centralBandHomotopyEquiv).toFun)

namespace DuplicatedSectionSevenRadialBandInput

variable {A : PaperAnalyticData} {L : A.DuplicatedSectionSevenLiftedContractionInput}

/-- Assemble the duplicated-central radial realization from the two inclusion properties and the
remaining band equivalence and compatibility homotopies. -/
public noncomputable def toRadialRealization
    (B : A.DuplicatedSectionSevenRadialBandInput L) :
    A.duplicatedSectionSevenEllipticCentralAllocation.RadialRealization where
  orderThreeLiftedContraction := L.orderThreeLiftedContraction
  orderFourLiftedContraction := L.orderFourLiftedContraction
  bandParameter := A.duplicatedSectionSevenBandParameter
  bandFullRank := A.duplicatedSectionSevenBandFullRank
  bandHomotopyEquiv :=
    A.duplicatedSectionSevenSidesIntersectionHomeomorph.toHomotopyEquiv.trans
      B.centralBandHomotopyEquiv
  bandToOrderThreeCoverSource := A.duplicatedSectionSevenBandToOrderThreeCoverSource
  bandToOrderFourCoverSource := A.duplicatedSectionSevenBandToOrderFourCoverSource
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
