module

public import SphereSixComplex.Topology.PaperSectionSevenPositiveDegreeGeometricReduction

/-!
# A genuine central-band split for the Section 7 elliptic cover

A continuous height on the regular central image cuts it into two overlapping open regions.  If
the opposite filling collars avoid these regions, the two enlarged sides intersect in exactly the
open height band.  This replaces the duplicated-central allocation, whose intersection is the
whole regular central family, by the geometric shape used in the radial Mayer--Vietoris argument.
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

variable {A : PaperAnalyticData}

/-- The part of the regular central image below an upper height. -/
public def centralHeightLowerRegion
    (height : A.sectionSevenEllipticCentralImage → ℝ) (upper : ℝ) :
    Set A.SectionSevenEllipticInterior :=
  Subtype.val '' {x | height x < upper}

/-- The part of the regular central image above a lower height. -/
public def centralHeightUpperRegion
    (height : A.sectionSevenEllipticCentralImage → ℝ) (lower : ℝ) :
    Set A.SectionSevenEllipticInterior :=
  Subtype.val '' {x | lower < height x}

/-- The open central band between two height levels. -/
public def centralHeightBand
    (height : A.sectionSevenEllipticCentralImage → ℝ) (lower upper : ℝ) :
    Set A.SectionSevenEllipticInterior :=
  Subtype.val '' {x | lower < height x ∧ height x < upper}

/-- A height split whose opposite filling collars do not enter the allocated central regions. -/
public structure SectionSevenCentralHeightSplit where
  height : A.sectionSevenEllipticCentralImage → ℝ
  height_continuous : Continuous height
  lower : ℝ
  upper : ℝ
  lower_lt_upper : lower < upper
  orderThreeFilling_disjoint_upper :
    Disjoint A.sectionSevenOrderThreeFillingImage
      (centralHeightUpperRegion height lower)
  orderFourFilling_disjoint_lower :
    Disjoint A.sectionSevenOrderFourFillingImage
      (centralHeightLowerRegion height upper)

namespace SectionSevenCentralHeightSplit

variable (S : A.SectionSevenCentralHeightSplit)

public theorem centralHeightLowerRegion_isOpen :
    IsOpen (centralHeightLowerRegion S.height S.upper) :=
  A.sectionSevenEllipticCentralImage_isOpen.isOpenMap_subtype_val _
    (isOpen_lt S.height_continuous continuous_const)

public theorem centralHeightUpperRegion_isOpen :
    IsOpen (centralHeightUpperRegion S.height S.lower) :=
  A.sectionSevenEllipticCentralImage_isOpen.isOpenMap_subtype_val _
    (isOpen_lt continuous_const S.height_continuous)

/-- The genuine central allocation obtained from the overlapping height cut. -/
public def allocation : A.SectionSevenEllipticCentralAllocation where
  orderThreeCentral := centralHeightLowerRegion S.height S.upper
  orderFourCentral := centralHeightUpperRegion S.height S.lower
  orderThreeCentral_isOpen := S.centralHeightLowerRegion_isOpen
  orderFourCentral_isOpen := S.centralHeightUpperRegion_isOpen
  central_cover := by
    intro x hx
    let y : A.sectionSevenEllipticCentralImage := ⟨x, hx⟩
    by_cases hy : S.height y < S.upper
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, S.lower_lt_upper.trans_le (le_of_not_gt hy), rfl⟩

/-- The intersection of the allocated central regions is exactly the height band. -/
public theorem centralRegions_intersection :
    centralHeightLowerRegion S.height S.upper ∩
        centralHeightUpperRegion S.height S.lower =
      centralHeightBand S.height S.lower S.upper := by
  ext x
  constructor
  · rintro ⟨⟨y, hyUpper, rfl⟩, ⟨z, hzLower, hz⟩⟩
    have hyz : y = z := Subtype.ext hz.symm
    subst z
    exact ⟨y, ⟨hzLower, hyUpper⟩, rfl⟩
  · rintro ⟨y, ⟨hyLower, hyUpper⟩, rfl⟩
    exact ⟨⟨y, hyUpper, rfl⟩, ⟨y, hyLower, rfl⟩⟩

/-- The two enlarged sides meet in the genuine height band, not in the whole central family. -/
public theorem sides_intersection :
    S.allocation.orderThreeSide ∩ S.allocation.orderFourSide =
      centralHeightBand S.height S.lower S.upper := by
  ext x
  change ((x ∈ A.sectionSevenOrderThreeFillingImage ∨
      x ∈ centralHeightLowerRegion S.height S.upper) ∧
    (x ∈ A.sectionSevenOrderFourFillingImage ∨
      x ∈ centralHeightUpperRegion S.height S.lower)) ↔ _
  constructor
  · rintro ⟨h₃ | hLower, h₄ | hUpper⟩
    · have h : x ∈ A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenOrderFourFillingImage := ⟨h₃, h₄⟩
      rw [A.sectionSevenEllipticFillingImages_disjoint] at h
      exact h.elim
    · exact (Set.disjoint_left.mp S.orderThreeFilling_disjoint_upper h₃ hUpper).elim
    · exact (Set.disjoint_left.mp S.orderFourFilling_disjoint_lower h₄ hLower).elim
    · rw [← S.centralRegions_intersection]
      exact ⟨hLower, hUpper⟩
  · intro hBand
    have h : x ∈ centralHeightLowerRegion S.height S.upper ∩
        centralHeightUpperRegion S.height S.lower := by
      rw [S.centralRegions_intersection]
      exact hBand
    exact ⟨Or.inr h.1, Or.inr h.2⟩

/-- Identify the actual side intersection with the central height band. -/
public def sidesIntersectionHomeomorph :
    (S.allocation.orderThreeSide ∩ S.allocation.orderFourSide :
      Set A.SectionSevenEllipticInterior) ≃ₜ
      centralHeightBand S.height S.lower S.upper :=
  Homeomorph.setCongr S.sides_intersection

/-- The order-three filling as a subspace of the height-split side. -/
public def orderThreeFillingSubspace : Set S.allocation.orderThreeSide :=
  Subtype.val ⁻¹' A.sectionSevenOrderThreeFillingImage

/-- The order-four filling as a subspace of the height-split side. -/
public def orderFourFillingSubspace : Set S.allocation.orderFourSide :=
  Subtype.val ⁻¹' A.sectionSevenOrderFourFillingImage

public theorem orderThreeFillingImage_subset_side :
    A.sectionSevenOrderThreeFillingImage ⊆ S.allocation.orderThreeSide :=
  fun _ hx ↦ Or.inl hx

public theorem orderFourFillingImage_subset_side :
    A.sectionSevenOrderFourFillingImage ⊆ S.allocation.orderFourSide :=
  fun _ hx ↦ Or.inl hx

/-- The remaining geometric input after replacing the duplicated allocation by a genuine band
split.  The band parameter and its two cover-source identifications are canonical. -/
public structure RadialInput where
  orderThreeHomotopyEquivalence :
    IsHomotopyEquivalenceInclusion S.orderThreeFillingSubspace
  orderFourHomotopyEquivalence :
    IsHomotopyEquivalenceInclusion S.orderFourFillingSubspace
  bandHomotopyEquiv :
    centralHeightBand S.height S.lower S.upper ≃ₕ
      AdditiveTorus A.duplicatedSectionSevenBandParameter
  orderThree_inclusion_compatibility :
    (((A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
      (orderThreeHomotopyEquivalence.toHomotopyEquiv.trans
        (nestedSubtypeHomeomorph S.allocation.orderThreeSide
          A.sectionSevenOrderThreeFillingImage
          S.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun).comp
        (IntegralMayerVietoris.interToLeft
          S.allocation.orderThreeSide S.allocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
          A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩ |>.comp
            (S.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
              bandHomotopyEquiv).toFun)
  orderFour_inclusion_compatibility :
    (((A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
      (orderFourHomotopyEquivalence.toHomotopyEquiv.trans
        (nestedSubtypeHomeomorph S.allocation.orderFourSide
          A.sectionSevenOrderFourFillingImage
          S.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun).comp
        (IntegralMayerVietoris.interToRight
          S.allocation.orderThreeSide S.allocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
          A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩ |>.comp
            (S.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
              bandHomotopyEquiv).toFun)

namespace RadialInput

variable {S : A.SectionSevenCentralHeightSplit}

/-- Assemble all fields of the radial realization from the genuine central-band input. -/
public noncomputable def toRadialRealization (R : S.RadialInput) :
    S.allocation.RadialRealization where
  orderThreeLiftedContraction :=
    R.orderThreeHomotopyEquivalence.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph S.allocation.orderThreeSide
        A.sectionSevenOrderThreeFillingImage
        S.orderThreeFillingImage_subset_side).toHomotopyEquiv
  orderFourLiftedContraction :=
    R.orderFourHomotopyEquivalence.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph S.allocation.orderFourSide
        A.sectionSevenOrderFourFillingImage
        S.orderFourFillingImage_subset_side).toHomotopyEquiv
  bandParameter := A.duplicatedSectionSevenBandParameter
  bandFullRank := A.duplicatedSectionSevenBandFullRank
  bandHomotopyEquiv :=
    S.sidesIntersectionHomeomorph.toHomotopyEquiv.trans R.bandHomotopyEquiv
  bandToOrderThreeCoverSource := A.duplicatedSectionSevenBandToOrderThreeCoverSource
  bandToOrderFourCoverSource := A.duplicatedSectionSevenBandToOrderFourCoverSource
  orderThree_inclusion_compatibility := R.orderThree_inclusion_compatibility
  orderFour_inclusion_compatibility := R.orderFour_inclusion_compatibility

end RadialInput

end SectionSevenCentralHeightSplit

end SphereSixComplex.Geometry.PaperAnalyticData
