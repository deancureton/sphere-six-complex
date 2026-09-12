module

public import SphereSixComplex.Prerequisites.Topology.EstablishedNumeratedOpenCoverHomotopyExcision
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Prerequisites.Topology.MapHomotopyEquivalence

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

end SphereSixComplex

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.OpenUnionHomotopy

variable (A : AnalyticData)

/-- The regular central region on the order-three side of the affine split. -/
public abbrev affineOrderThreeCentralRegion :
    Set A.ellipticInterior :=
  centralHeightLowerRegion A.ellipticCentralHeight (2 / 3 : ℝ)

/-- The regular central region on the order-four side of the affine split. -/
public abbrev affineOrderFourCentralRegion :
    Set A.ellipticInterior :=
  centralHeightUpperRegion A.ellipticCentralHeight (1 / 3 : ℝ)

end SphereSixComplex.Geometry.AnalyticData

end
