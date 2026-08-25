module

public import SphereSixComplex.Topology.PaperEllipticTwoDiscCover
public import SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial

/-!
# Concrete pieces of the Section 7 elliptic two-disc cover

This file identifies the two elliptic filling images inside the cusp-free Mayer--Vietoris stage
and transports the radial deformation retractions to those images.  It also records a reusable
trivial-product lemma for removing a contractible base.  The remaining two-disc construction is
the decomposition and trivialization of the regular central family between the two filling
collars.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods

/-- A product trivialization over a contractible base is homotopy equivalent to its fibre. -/
public noncomputable def trivialProductHomotopyEquivFiber
    {E B F : Type} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    (totalTrivialization : E ≃ₜ B × F) (baseContraction : B ≃ₕ Unit) : E ≃ₕ F :=
  totalTrivialization.toHomotopyEquiv.trans
    ((baseContraction.prodCongr (ContinuousMap.HomotopyEquiv.refl F)).trans
      (Homeomorph.uniqueProd Unit F).toHomotopyEquiv)

namespace Geometry.PaperAnalyticData

open Topology.PaperEllipticFillingRealPeriodRadial
open Topology.PaperEllipticFillingRadialRetraction
open Topology.PaperEllipticReducedCentralFiberCoverModels

variable (A : PaperAnalyticData)

public abbrev SectionSevenEllipticCover :=
  A.openEmbeddingStarData.SectionSevenMayerVietorisCover

/-- The open image of the order-three filling, regarded as a subset of the elliptic interior. -/
public def sectionSevenOrderThreeFillingImage :
    Set A.SectionSevenEllipticInterior :=
  Subtype.val ⁻¹' A.SectionSevenEllipticCover.piece 1

/-- The open image of the order-four filling, regarded as a subset of the elliptic interior. -/
public def sectionSevenOrderFourFillingImage :
    Set A.SectionSevenEllipticInterior :=
  Subtype.val ⁻¹' A.SectionSevenEllipticCover.piece 2

public theorem sectionSevenOrderThreeFillingImage_isOpen :
    IsOpen A.sectionSevenOrderThreeFillingImage :=
  (A.SectionSevenEllipticCover.isOpen_piece 1).preimage continuous_subtype_val

public theorem sectionSevenOrderFourFillingImage_isOpen :
    IsOpen A.sectionSevenOrderFourFillingImage :=
  (A.SectionSevenEllipticCover.isOpen_piece 2).preimage continuous_subtype_val

/-- The open image of the regular central family inside the elliptic interior. -/
public def sectionSevenEllipticCentralImage : Set A.SectionSevenEllipticInterior :=
  Subtype.val ⁻¹' A.SectionSevenEllipticCover.piece 0

public theorem sectionSevenEllipticCentralImage_isOpen :
    IsOpen A.sectionSevenEllipticCentralImage :=
  (A.SectionSevenEllipticCover.isOpen_piece 0).preimage continuous_subtype_val

/-- The elliptic interior is exactly the union of the regular central image and the two elliptic
filling images. -/
public theorem sectionSevenEllipticCentral_union_fillings :
    A.sectionSevenEllipticCentralImage ∪
        A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenOrderFourFillingImage = Set.univ := by
  ext x
  simp only [sectionSevenEllipticCentralImage,
    sectionSevenOrderThreeFillingImage, sectionSevenOrderFourFillingImage,
    mem_union, mem_preimage, mem_univ, iff_true]
  have hx := x.2
  change x.1 ∈ A.SectionSevenEllipticCover.stage (2 : Fin 4) at hx
  rw [FourPieceOpenCover.stage] at hx
  simp only [mem_iUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  fin_cases i
  · exact Or.inl (Or.inl (by simpa using hxi))
  · exact Or.inl (Or.inr (by simpa using hxi))
  · exact Or.inr (by simpa using hxi)
  · have hnot : ¬ ((3 : Fin 4) ≤ (2 : Fin 4)) := by decide
    exact (hnot hi).elim

/-- The only set-theoretic input needed to enlarge the two actual filling images to an open
two-set cover is an open allocation of the regular central image between the two sides. -/
public structure SectionSevenEllipticCentralAllocation where
  orderThreeCentral : Set A.SectionSevenEllipticInterior
  orderFourCentral : Set A.SectionSevenEllipticInterior
  orderThreeCentral_isOpen : IsOpen orderThreeCentral
  orderFourCentral_isOpen : IsOpen orderFourCentral
  central_cover : A.sectionSevenEllipticCentralImage ⊆
    orderThreeCentral ∪ orderFourCentral

namespace SectionSevenEllipticCentralAllocation

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticCentralAllocation)

/-- The order-three side obtained by adjoining its allocated central region to the actual
order-three filling image. -/
public def orderThreeSide : Set A.SectionSevenEllipticInterior :=
  A.sectionSevenOrderThreeFillingImage ∪ D.orderThreeCentral

/-- The order-four side obtained by adjoining its allocated central region to the actual
order-four filling image. -/
public def orderFourSide : Set A.SectionSevenEllipticInterior :=
  A.sectionSevenOrderFourFillingImage ∪ D.orderFourCentral

public theorem orderThreeSide_isOpen : IsOpen D.orderThreeSide :=
  A.sectionSevenOrderThreeFillingImage_isOpen.union D.orderThreeCentral_isOpen

public theorem orderFourSide_isOpen : IsOpen D.orderFourSide :=
  A.sectionSevenOrderFourFillingImage_isOpen.union D.orderFourCentral_isOpen

public theorem sides_cover : D.orderThreeSide ∪ D.orderFourSide = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ A.sectionSevenEllipticCentralImage ∪
      A.sectionSevenOrderThreeFillingImage ∪
        A.sectionSevenOrderFourFillingImage := by
    rw [A.sectionSevenEllipticCentral_union_fillings]
    exact Set.mem_univ x
  rcases hx with (hx | hx) | hx
  · rcases D.central_cover hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)
  · exact Or.inl (Or.inl hx)
  · exact Or.inr (Or.inl hx)

end SectionSevenEllipticCentralAllocation

public theorem sectionSevenOrderThreePiece_subset_ellipticInterior :
    A.SectionSevenEllipticCover.piece 1 ⊆
      A.SectionSevenEllipticCover.stage (2 : Fin 4) := by
  intro x hx
  rw [FourPieceOpenCover.stage]
  exact mem_iUnion.mpr ⟨1, mem_iUnion.mpr ⟨by decide, hx⟩⟩

public theorem sectionSevenOrderFourPiece_subset_ellipticInterior :
    A.SectionSevenEllipticCover.piece 2 ⊆
      A.SectionSevenEllipticCover.stage (2 : Fin 4) := by
  intro x hx
  rw [FourPieceOpenCover.stage]
  exact mem_iUnion.mpr ⟨2, mem_iUnion.mpr ⟨by decide, hx⟩⟩

/-- Forgetting the ambient elliptic-interior subtype identifies its order-three filling image
with the corresponding member of the reordered star cover. -/
public def sectionSevenOrderThreeFillingImageToPiece :
    A.sectionSevenOrderThreeFillingImage ≃ₜ A.SectionSevenEllipticCover.piece 1 where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x :=
    ⟨⟨x.1, A.sectionSevenOrderThreePiece_subset_ellipticInterior x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Forgetting the ambient elliptic-interior subtype identifies its order-four filling image
with the corresponding member of the reordered star cover. -/
public def sectionSevenOrderFourFillingImageToPiece :
    A.sectionSevenOrderFourFillingImage ≃ₜ A.SectionSevenEllipticCover.piece 2 where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x :=
    ⟨⟨x.1, A.sectionSevenOrderFourPiece_subset_ellipticInterior x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The order-three member of the reordered cover is the canonical open image of the actual
order-three varying filling. -/
public def sectionSevenOrderThreePieceHomeomorph :
    A.openEmbeddingStarData.filling 1 ≃ₜ A.SectionSevenEllipticCover.piece 1 := by
  change A.openEmbeddingStarData.filling 1 ≃ₜ
    Set.range
      (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some (1 : Fin 3)))
  exact
    (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding
      (some (1 : Fin 3))).isEmbedding.toHomeomorph

/-- The order-four member of the reordered cover is the canonical open image of the actual
order-four varying filling. -/
public def sectionSevenOrderFourPieceHomeomorph :
    A.openEmbeddingStarData.filling 2 ≃ₜ A.SectionSevenEllipticCover.piece 2 := by
  change A.openEmbeddingStarData.filling 2 ≃ₜ
    Set.range
      (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some (2 : Fin 3)))
  exact
    (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding
      (some (2 : Fin 3))).isEmbedding.toHomeomorph

/-- The actual order-three filling image in the elliptic interior retracts to the reduced central
order-three fibre. -/
public def sectionSevenOrderThreeFillingImageHomotopyEquiv :
    A.sectionSevenOrderThreeFillingImage ≃ₕ
      OrderThreeReducedCentralFiber A.periods :=
  A.sectionSevenOrderThreeFillingImageToPiece.toHomotopyEquiv |>.trans
    A.sectionSevenOrderThreePieceHomeomorph.symm.toHomotopyEquiv |>.trans
      (orderThreeSelectedFillingHomotopyEquivCentralFiber A)

/-- The actual order-four filling image in the elliptic interior retracts to the reduced central
order-four fibre. -/
public def sectionSevenOrderFourFillingImageHomotopyEquiv :
    A.sectionSevenOrderFourFillingImage ≃ₕ
      OrderFourReducedCentralFiber A.periods :=
  A.sectionSevenOrderFourFillingImageToPiece.toHomotopyEquiv |>.trans
    A.sectionSevenOrderFourPieceHomeomorph.symm.toHomotopyEquiv |>.trans
      (orderFourSelectedFillingHomotopyEquivCentralFiber A)

/-- The remaining geometric realization after the actual open filling images and their radial
retractions have been constructed.  The two side equivalences only ask for lifted contractions
back to those concrete filling images; the radial contraction to the reduced fibres is supplied
by this file. -/
public structure SectionSevenEllipticCentralAllocation.RadialRealization
    (D : A.SectionSevenEllipticCentralAllocation) where
  orderThreeLiftedContraction :
    D.orderThreeSide ≃ₕ A.sectionSevenOrderThreeFillingImage
  orderFourLiftedContraction :
    D.orderFourSide ≃ₕ A.sectionSevenOrderFourFillingImage
  bandParameter : SphereSixComplex.Periods.Parameters
  bandFullRank : FullRank bandParameter
  bandHomotopyEquiv :
    (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) ≃ₕ
      AdditiveTorus bandParameter
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
      orderThreeLiftedContraction.toFun).comp
        (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)).comp
        ⟨bandToOrderThreeCoverSource,
          bandToOrderThreeCoverSource.continuous⟩ |>.comp bandHomotopyEquiv.toFun)
  orderFour_inclusion_compatibility :
    (((A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
      orderFourLiftedContraction.toFun).comp
        (IntegralMayerVietoris.interToRight D.orderThreeSide D.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)).comp
        ⟨bandToOrderFourCoverSource,
          bandToOrderFourCoverSource.continuous⟩ |>.comp bandHomotopyEquiv.toFun)

namespace SectionSevenEllipticCentralAllocation.RadialRealization

variable {D : A.SectionSevenEllipticCentralAllocation} (R : D.RadialRealization)

/-- Completing only the central allocation, lifted contractions, and band trivialization produces
the exact two-disc datum consumed by the Section 7 homology calculation. -/
public def toSectionSevenEllipticTwoDiscCoverData :
    A.SectionSevenEllipticTwoDiscCoverData where
  orderThreeSide := D.orderThreeSide
  orderFourSide := D.orderFourSide
  orderThreeSide_isOpen := D.orderThreeSide_isOpen
  orderFourSide_isOpen := D.orderFourSide_isOpen
  sides_cover := D.sides_cover
  bandParameter := R.bandParameter
  bandFullRank := R.bandFullRank
  bandHomotopyEquiv := R.bandHomotopyEquiv
  orderThreeSideHomotopyEquiv :=
    R.orderThreeLiftedContraction.trans
      A.sectionSevenOrderThreeFillingImageHomotopyEquiv
  orderFourSideHomotopyEquiv :=
    R.orderFourLiftedContraction.trans
      A.sectionSevenOrderFourFillingImageHomotopyEquiv
  bandToOrderThreeCoverSource := R.bandToOrderThreeCoverSource
  bandToOrderFourCoverSource := R.bandToOrderFourCoverSource
  orderThree_inclusion_compatibility := R.orderThree_inclusion_compatibility
  orderFour_inclusion_compatibility := R.orderFour_inclusion_compatibility

end SectionSevenEllipticCentralAllocation.RadialRealization

end Geometry.PaperAnalyticData

end SphereSixComplex
