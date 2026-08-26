module

public import SphereSixComplex.Topology.EstablishedNumeratedOpenCoverHomotopyExcision
public import SphereSixComplex.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Topology.ProductTrivializationHomotopyEquivalence
public import SphereSixComplex.Topology.PuncturedAffineHalfPlaneRadial

/-!
# Homotopy equivalences for the affine elliptic sides

Each affine side is the union of a filling image and an open part of the regular central family.
The product-coordinate argument applies to the overlap with the central region, not to the filled
side itself.  Dold's open-union theorem then transports that overlap equivalence to the literal
inclusion of the filling image into the whole side.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

open OpenUnionHomotopy

universe u v w

/-- The literal inclusion of a punctured disc into a containing punctured left half-plane. -/
public def puncturedComplexDiscToLeftHalfPlane {r c : ℝ} (hrc : r ≤ c) :
    puncturedComplexDisc r → puncturedComplexLeftHalfPlane c :=
  fun z ↦ ⟨z.1, z.2.1, (Complex.re_le_norm z.1).trans_lt (z.2.2.trans_le hrc)⟩

/-- Radial normalization proves that the literal left-half-plane inclusion is a homotopy
equivalence. -/
public theorem puncturedComplexDiscToLeftHalfPlane_isHomotopyEquivalence
    {s r c : ℝ} (hs : 0 < s) (hsr : s < r) (hrc : r ≤ c) :
    IsHomotopyEquivalence (puncturedComplexDiscToLeftHalfPlane hrc) := by
  refine ⟨(puncturedComplexDiscHomotopyEquivLeftHalfPlane hs hsr hrc).symm, ?_⟩
  funext x
  rfl

/-- The literal inclusion of a punctured disc at one into a containing punctured right
half-plane. -/
public def puncturedComplexDiscAtOneToRightHalfPlane {r c : ℝ} (hrc : r ≤ 1 - c) :
    puncturedComplexDiscAtOne r → puncturedComplexRightHalfPlane c :=
  fun z ↦ ⟨z.1, z.2.1, by
    have hre := Complex.abs_re_le_norm (z.1 - 1)
    simp only [Complex.sub_re, Complex.one_re] at hre
    have hlower : -‖z.1 - 1‖ ≤ z.1.re - 1 := (abs_le.mp hre).1
    linarith [z.2.2, hrc]⟩

/-- Radial normalization proves that the literal right-half-plane inclusion is a homotopy
equivalence. -/
public theorem puncturedComplexDiscAtOneToRightHalfPlane_isHomotopyEquivalence
    {s r c : ℝ} (hs : 0 < s) (hsr : s < r) (hrc : r ≤ 1 - c) :
    IsHomotopyEquivalence (puncturedComplexDiscAtOneToRightHalfPlane hrc) := by
  refine ⟨(puncturedComplexDiscAtOneHomotopyEquivRightHalfPlane hs hsr hrc).symm, ?_⟩
  funext x
  apply Subtype.ext
  change 1 - (1 - x.1) = x.1
  ring

variable {X : Type u} [TopologicalSpace X]

/-- The nested model of the left member of a union is homeomorphic to that member. -/
private def leftMemberNestedHomeomorph (U V : Set X) :
    (Subtype.val ⁻¹' U : Set ↥(U ∪ V)) ≃ₜ U where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, Or.inl x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- A homotopy equivalence carried by the literal left-to-union map gives the inclusion form used
by the affine completion input. -/
public theorem isHomotopyEquivalenceInclusion_of_leftToUnion
    (U V : Set X) (h : IsHomotopyEquivalence (leftToUnion U V).hom) :
    IsHomotopyEquivalenceInclusion (Subtype.val ⁻¹' U : Set ↥(U ∪ V)) := by
  obtain ⟨e, he⟩ := h
  let e' : ↥(U ∪ V) ≃ₕ (Subtype.val ⁻¹' U : Set ↥(U ∪ V)) :=
    e.symm.trans (leftMemberNestedHomeomorph U V).symm.toHomotopyEquiv
  refine ⟨e', ?_⟩
  ext x
  simp only [e', ContinuousMap.HomotopyEquiv.trans, ContinuousMap.HomotopyEquiv.symm,
    Homeomorph.toHomotopyEquiv, leftMemberNestedHomeomorph, ContinuousMap.comp_apply,
    topologicalSubsetInclusionMap]
  change (e ⟨x.1.1, x.2⟩ : ↥(U ∪ V)).1 = x.1.1
  rw [he]
  rfl

variable {B₁ : Type v} {B₂ : Type w}
variable [TopologicalSpace B₁] [TopologicalSpace B₂]

/-- Product coordinates on the overlap and the right member reduce an open-union inclusion to a
base homotopy equivalence.  The homotopy-excision input is kept explicit in this axiom-free
version. -/
public theorem isHomotopyEquivalenceInclusion_of_open_union_product
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (baseMap : B₁ → B₂) (fiber : Type*) [TopologicalSpace fiber]
    (overlapTrivialization : ↥(U ∩ V) ≃ₜ B₁ × fiber)
    (rightTrivialization : V ≃ₜ B₂ × fiber)
    (commutes : rightTrivialization ∘ (interToRight U V).hom =
      Prod.map baseMap id ∘ overlapTrivialization)
    (hBase : IsHomotopyEquivalence baseMap)
    (hexc : TopCat.IsHomotopyExcisiveSpan (interToRight U V) (interToLeft U V)) :
    IsHomotopyEquivalenceInclusion (Subtype.val ⁻¹' U : Set ↥(U ∪ V)) := by
  have hinter : IsHomotopyEquivalence (interToRight U V).hom :=
    isHomotopyEquivalence_of_product_trivializations_right_id baseMap
      (interToRight U V).hom overlapTrivialization rightTrivialization commutes hBase
  exact isHomotopyEquivalenceInclusion_of_leftToUnion U V
    (leftToUnion_isHomotopyEquivalence U V hU hV hinter hexc)

/-- For normal paracompact open unions, Dold's numerated-cover theorem supplies the homotopy
excision input automatically. -/
public theorem isHomotopyEquivalenceInclusion_of_normal_paracompact_open_union_product
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [NormalSpace ↥(U ∪ V)] [ParacompactSpace ↥(U ∪ V)]
    (baseMap : B₁ → B₂) (fiber : Type*) [TopologicalSpace fiber]
    (overlapTrivialization : ↥(U ∩ V) ≃ₜ B₁ × fiber)
    (rightTrivialization : V ≃ₜ B₂ × fiber)
    (commutes : rightTrivialization ∘ (interToRight U V).hom =
      Prod.map baseMap id ∘ overlapTrivialization)
    (hBase : IsHomotopyEquivalence baseMap) :
    IsHomotopyEquivalenceInclusion (Subtype.val ⁻¹' U : Set ↥(U ∪ V)) := by
  have hinter : IsHomotopyEquivalence (interToRight U V).hom :=
    isHomotopyEquivalence_of_product_trivializations_right_id baseMap
      (interToRight U V).hom overlapTrivialization rightTrivialization commutes hBase
  exact isHomotopyEquivalenceInclusion_of_leftToUnion U V
    (leftToUnion_isHomotopyEquivalence_of_normal_paracompact U V hU hV hinter)

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.OpenUnionHomotopy

variable (A : PaperAnalyticData)

/-- The regular central region on the order-three side of the affine split. -/
public abbrev sectionSevenAffineOrderThreeCentralRegion :
    Set A.SectionSevenEllipticInterior :=
  centralHeightLowerRegion A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ)

/-- The regular central region on the order-four side of the affine split. -/
public abbrev sectionSevenAffineOrderFourCentralRegion :
    Set A.SectionSevenEllipticInterior :=
  centralHeightUpperRegion A.sectionSevenEllipticCentralHeight (1 / 3 : ℝ)

variable {A : PaperAnalyticData}

/-- Exact product-coordinate input for the order-three overlap-to-central-region map.  The radius
is an affine-coordinate radius; it is not identified with a Cayley collar radius. -/
public structure SectionSevenAffineOrderThreeSideProductInput
    (fiber : Type*) [TopologicalSpace fiber] where
  normalizationRadius : ℝ
  affineDiscRadius : ℝ
  normalizationRadius_pos : 0 < normalizationRadius
  normalizationRadius_lt_disc : normalizationRadius < affineDiscRadius
  affineDiscRadius_le_halfPlane : affineDiscRadius ≤ 2 / 3
  overlapTrivialization :
    ↥(A.sectionSevenOrderThreeFillingImage ∩ A.sectionSevenAffineOrderThreeCentralRegion) ≃ₜ
      puncturedComplexDisc affineDiscRadius × fiber
  centralTrivialization :
    A.sectionSevenAffineOrderThreeCentralRegion ≃ₜ
      puncturedComplexLeftHalfPlane (2 / 3) × fiber
  commutes : centralTrivialization ∘
      (interToRight A.sectionSevenOrderThreeFillingImage
        A.sectionSevenAffineOrderThreeCentralRegion).hom =
    Prod.map (puncturedComplexDiscToLeftHalfPlane affineDiscRadius_le_halfPlane) id ∘
      overlapTrivialization

/-- Exact product-coordinate input for the order-four overlap-to-central-region map. -/
public structure SectionSevenAffineOrderFourSideProductInput
    (fiber : Type*) [TopologicalSpace fiber] where
  normalizationRadius : ℝ
  affineDiscRadius : ℝ
  normalizationRadius_pos : 0 < normalizationRadius
  normalizationRadius_lt_disc : normalizationRadius < affineDiscRadius
  affineDiscRadius_le_halfPlane : affineDiscRadius ≤ 1 - 1 / 3
  overlapTrivialization :
    ↥(A.sectionSevenOrderFourFillingImage ∩ A.sectionSevenAffineOrderFourCentralRegion) ≃ₜ
      puncturedComplexDiscAtOne affineDiscRadius × fiber
  centralTrivialization :
    A.sectionSevenAffineOrderFourCentralRegion ≃ₜ
      puncturedComplexRightHalfPlane (1 / 3) × fiber
  commutes : centralTrivialization ∘
      (interToRight A.sectionSevenOrderFourFillingImage
        A.sectionSevenAffineOrderFourCentralRegion).hom =
    Prod.map (puncturedComplexDiscAtOneToRightHalfPlane
      affineDiscRadius_le_halfPlane) id ∘ overlapTrivialization

namespace SectionSevenAffineOrderThreeSideProductInput

variable {fiber : Type*} [TopologicalSpace fiber]

/-- Product coordinates and radial normalization prove the order-three overlap map is a
homotopy equivalence. -/
public theorem overlapIsHomotopyEquivalence
    (P : A.SectionSevenAffineOrderThreeSideProductInput fiber) :
    IsHomotopyEquivalence
      (interToRight A.sectionSevenOrderThreeFillingImage
        A.sectionSevenAffineOrderThreeCentralRegion).hom :=
  isHomotopyEquivalence_of_product_trivializations_right_id
    (puncturedComplexDiscToLeftHalfPlane P.affineDiscRadius_le_halfPlane)
    (interToRight A.sectionSevenOrderThreeFillingImage
      A.sectionSevenAffineOrderThreeCentralRegion).hom
    P.overlapTrivialization P.centralTrivialization P.commutes
    (puncturedComplexDiscToLeftHalfPlane_isHomotopyEquivalence
      P.normalizationRadius_pos P.normalizationRadius_lt_disc
      P.affineDiscRadius_le_halfPlane)

/-- Dold's theorem upgrades the order-three overlap equivalence to the literal filling-to-side
inclusion. -/
public theorem homotopyEquivalenceInclusion
    (P : A.SectionSevenAffineOrderThreeSideProductInput fiber)
    [NormalSpace ↥(A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenAffineOrderThreeCentralRegion)]
    [ParacompactSpace ↥(A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenAffineOrderThreeCentralRegion)] :
    IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderThreeFillingSubspace := by
  change IsHomotopyEquivalenceInclusion
    (Subtype.val ⁻¹' A.sectionSevenOrderThreeFillingImage :
      Set ↥(A.sectionSevenOrderThreeFillingImage ∪
        A.sectionSevenAffineOrderThreeCentralRegion))
  exact isHomotopyEquivalenceInclusion_of_leftToUnion _ _
    (leftToUnion_isHomotopyEquivalence_of_normal_paracompact _ _
      A.sectionSevenOrderThreeFillingImage_isOpen
      A.sectionSevenActualAffineSplit.centralHeightLowerRegion_isOpen
      P.overlapIsHomotopyEquivalence)

end SectionSevenAffineOrderThreeSideProductInput

namespace SectionSevenAffineOrderFourSideProductInput

variable {fiber : Type*} [TopologicalSpace fiber]

/-- Product coordinates and radial normalization prove the order-four overlap map is a homotopy
equivalence. -/
public theorem overlapIsHomotopyEquivalence
    (P : A.SectionSevenAffineOrderFourSideProductInput fiber) :
    IsHomotopyEquivalence
      (interToRight A.sectionSevenOrderFourFillingImage
        A.sectionSevenAffineOrderFourCentralRegion).hom :=
  isHomotopyEquivalence_of_product_trivializations_right_id
    (puncturedComplexDiscAtOneToRightHalfPlane P.affineDiscRadius_le_halfPlane)
    (interToRight A.sectionSevenOrderFourFillingImage
      A.sectionSevenAffineOrderFourCentralRegion).hom
    P.overlapTrivialization P.centralTrivialization P.commutes
    (puncturedComplexDiscAtOneToRightHalfPlane_isHomotopyEquivalence
      P.normalizationRadius_pos P.normalizationRadius_lt_disc
      P.affineDiscRadius_le_halfPlane)

/-- Dold's theorem upgrades the order-four overlap equivalence to the literal filling-to-side
inclusion. -/
public theorem homotopyEquivalenceInclusion
    (P : A.SectionSevenAffineOrderFourSideProductInput fiber)
    [NormalSpace ↥(A.sectionSevenOrderFourFillingImage ∪
      A.sectionSevenAffineOrderFourCentralRegion)]
    [ParacompactSpace ↥(A.sectionSevenOrderFourFillingImage ∪
      A.sectionSevenAffineOrderFourCentralRegion)] :
    IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderFourFillingSubspace := by
  change IsHomotopyEquivalenceInclusion
    (Subtype.val ⁻¹' A.sectionSevenOrderFourFillingImage :
      Set ↥(A.sectionSevenOrderFourFillingImage ∪
        A.sectionSevenAffineOrderFourCentralRegion))
  exact isHomotopyEquivalenceInclusion_of_leftToUnion _ _
    (leftToUnion_isHomotopyEquivalence_of_normal_paracompact _ _
      A.sectionSevenOrderFourFillingImage_isOpen
      A.sectionSevenActualAffineSplit.centralHeightUpperRegion_isOpen
      P.overlapIsHomotopyEquivalence)

end SectionSevenAffineOrderFourSideProductInput

end SphereSixComplex.Geometry.PaperAnalyticData

end
