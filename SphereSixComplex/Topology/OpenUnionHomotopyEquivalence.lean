module

public import SphereSixComplex.Topology.MappingCylinderGluing
public import SphereSixComplex.Topology.RelativeHomotopy
public import Mathlib.Topology.ContinuousOn

/-!
# Homotopy equivalences from homotopy-excisive open unions

Two open subsets present their union as the topological pushout of their intersection.  For a
homotopy-excisive span, replacing the span by its double mapping cylinder does not change its
homotopy type.  Hence, if the intersection-to-right map is a homotopy equivalence and the free
end of its mapping cylinder has the homotopy-extension property, the left subset includes into
the union by a homotopy equivalence.

The cofibration hypothesis is imposed on the closed free end of the mapping cylinder, not on the
literal open intersection inside either member of the cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ContinuousMap Set Topology TopologicalSpace

namespace SphereSixComplex

universe u

namespace TopCat

variable {A X Y : TopCat.{u}}

/-- A span is homotopy-excisive when collapsing its double mapping cylinder to its ordinary
topological pushout is a homotopy equivalence.  This is the comparison-map formulation of the
homotopy-pushout condition. -/
public def IsHomotopyExcisiveSpan (f : A ⟶ X) (g : A ⟶ Y) : Prop :=
  IsHomotopyEquivalence (doubleMappingCylinderCollapse f g).hom

/-- Homotopy excision and cofibrancy of the mapping-cylinder free end let a homotopy equivalence
on one attaching leg pass to the opposite coprojection of the ordinary pushout. -/
public theorem pushoutInr_isHomotopyEquivalence_of_cofibrant_homotopyExcisive
    (f : A ⟶ X) (g : A ⟶ Y)
    (hf : IsHomotopyEquivalence f.hom)
    (hcof : HomotopyExtensionProperty (mappingCylinderFree f).hom)
    (hexc : IsHomotopyExcisiveSpan f g) :
    IsHomotopyEquivalence (pushout.inr f g).hom := by
  obtain ⟨D⟩ := hcof.exists_strongDeformationRetractData
    (mappingCylinderFree_isHomotopyEquivalence f hf)
  exact pushoutInr_isHomotopyEquivalence_of_mappingCylinder f g D hexc

end TopCat

namespace OpenUnionHomotopy

variable {X : Type u} [TopologicalSpace X]

/-- Inclusion of the intersection into the right open set. -/
public def interToRight (U V : Set X) : TopCat.of ↥(U ∩ V) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.2⟩, by fun_prop⟩

/-- Inclusion of the intersection into the left open set. -/
public def interToLeft (U V : Set X) : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.1⟩, by fun_prop⟩

/-- Inclusion of the right open set into the union. -/
public def rightToUnion (U V : Set X) : TopCat.of V ⟶ TopCat.of ↥(U ∪ V) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, Or.inr x.2⟩, by fun_prop⟩

/-- Inclusion of the left open set into the union. -/
public def leftToUnion (U V : Set X) : TopCat.of U ⟶ TopCat.of ↥(U ∪ V) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, Or.inl x.2⟩, by fun_prop⟩

public theorem inter_condition (U V : Set X) :
    interToRight U V ≫ rightToUnion U V = interToLeft U V ≫ leftToUnion U V := by
  ext x
  rfl

/-- The canonical map from the intersection pushout to the literal union. -/
public def pushoutToUnion (U V : Set X) :
    pushout (interToRight U V) (interToLeft U V) ⟶ TopCat.of ↥(U ∪ V) :=
  pushout.desc (rightToUnion U V) (leftToUnion U V) (inter_condition U V)

@[simp]
public theorem pushoutToUnion_inl (U V : Set X) (x : V) :
    pushoutToUnion U V (pushout.inl (interToRight U V) (interToLeft U V) x) =
      rightToUnion U V x :=
  CategoryTheory.congr_fun
    (pushout.inl_desc (rightToUnion U V) (leftToUnion U V) (inter_condition U V)) x

@[simp]
public theorem pushoutToUnion_inr (U V : Set X) (x : U) :
    pushoutToUnion U V (pushout.inr (interToRight U V) (interToLeft U V) x) =
      leftToUnion U V x :=
  CategoryTheory.congr_fun
    (pushout.inr_desc (rightToUnion U V) (leftToUnion U V) (inter_condition U V)) x

/-- The two open members, pulled back to their union and indexed by `Bool`. -/
public def unionCoverSet (U V : Set X) : Bool → Set ↥(U ∪ V)
  | false => Subtype.val ⁻¹' U
  | true => Subtype.val ⁻¹' V

/-- The two local maps from the union to its intersection pushout. -/
public def unionCoverMap (U V : Set X) :
    (i : Bool) → C(unionCoverSet U V i,
      (pushout (interToRight U V) (interToLeft U V) : TopCat))
  | false =>
      ⟨fun x ↦ pushout.inr (interToRight U V) (interToLeft U V) ⟨x.1.1, x.2⟩,
        by fun_prop⟩
  | true =>
      ⟨fun x ↦ pushout.inl (interToRight U V) (interToLeft U V) ⟨x.1.1, x.2⟩,
        by fun_prop⟩

public theorem unionCoverMap_compatible (U V : Set X) :
    ∀ (i j : Bool) (x : ↥(U ∪ V))
      (hxi : x ∈ unionCoverSet U V i) (hxj : x ∈ unionCoverSet U V j),
      unionCoverMap U V i ⟨x, hxi⟩ = unionCoverMap U V j ⟨x, hxj⟩ := by
  intro i j x hxi hxj
  cases i <;> cases j
  · rfl
  · let z : ↥(U ∩ V) := ⟨x.1, hxi, hxj⟩
    calc
      pushout.inr (interToRight U V) (interToLeft U V) ⟨x.1, hxi⟩ =
          pushout.inr (interToRight U V) (interToLeft U V) (interToLeft U V z) := by
            congr 1
      _ = pushout.inl (interToRight U V) (interToLeft U V) (interToRight U V z) :=
        (CategoryTheory.congr_fun
          (pushout.condition (f := interToRight U V) (g := interToLeft U V)) z).symm
      _ = pushout.inl (interToRight U V) (interToLeft U V) ⟨x.1, hxj⟩ := by
        congr 1
  · let z : ↥(U ∩ V) := ⟨x.1, hxj, hxi⟩
    calc
      pushout.inl (interToRight U V) (interToLeft U V) ⟨x.1, hxi⟩ =
          pushout.inl (interToRight U V) (interToLeft U V) (interToRight U V z) := by
            congr 1
      _ = pushout.inr (interToRight U V) (interToLeft U V) (interToLeft U V z) :=
        CategoryTheory.congr_fun
          (pushout.condition (f := interToRight U V) (g := interToLeft U V)) z
      _ = pushout.inr (interToRight U V) (interToLeft U V) ⟨x.1, hxj⟩ := by
        congr 1
  · rfl

public theorem unionCover_nhds (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    ∀ x : ↥(U ∪ V), ∃ i, unionCoverSet U V i ∈ 𝓝 x := by
  intro x
  rcases x.2 with hxU | hxV
  · exact ⟨false, (hU.preimage continuous_subtype_val).mem_nhds hxU⟩
  · exact ⟨true, (hV.preimage continuous_subtype_val).mem_nhds hxV⟩

/-- The inverse map is obtained by gluing the two coprojections over the open cover of the
literal union. -/
public def unionToPushout (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    C(↥(U ∪ V), (pushout (interToRight U V) (interToLeft U V) : TopCat)) :=
  ContinuousMap.liftCover (unionCoverSet U V) (unionCoverMap U V)
    (unionCoverMap_compatible U V) (unionCover_nhds U V hU hV)

public theorem unionToPushout_of_mem_left
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (x : ↥(U ∪ V)) (hx : x.1 ∈ U) :
    unionToPushout U V hU hV x =
      pushout.inr (interToRight U V) (interToLeft U V) ⟨x.1, hx⟩ := by
  let y : unionCoverSet U V false := ⟨x, hx⟩
  exact ContinuousMap.liftCover_coe y

public theorem unionToPushout_of_mem_right
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (x : ↥(U ∪ V)) (hx : x.1 ∈ V) :
    unionToPushout U V hU hV x =
      pushout.inl (interToRight U V) (interToLeft U V) ⟨x.1, hx⟩ := by
  let y : unionCoverSet U V true := ⟨x, hx⟩
  exact ContinuousMap.liftCover_coe y

public theorem pushoutToUnion_unionToPushout
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (x : ↥(U ∪ V)) :
    pushoutToUnion U V (unionToPushout U V hU hV x) = x := by
  rcases x.2 with hxU | hxV
  · rw [unionToPushout_of_mem_left U V hU hV x hxU, pushoutToUnion_inr]
    rfl
  · rw [unionToPushout_of_mem_right U V hU hV x hxV, pushoutToUnion_inl]
    rfl

public theorem unionToPushout_pushoutToUnion
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (p : (pushout (interToRight U V) (interToLeft U V) : TopCat)) :
    unionToPushout U V hU hV (pushoutToUnion U V p) = p := by
  have h :
      pushoutToUnion U V ≫ TopCat.ofHom (unionToPushout U V hU hV) =
        𝟙 (pushout (interToRight U V) (interToLeft U V)) := by
    apply pushout.hom_ext
    · rw [← Category.assoc, pushoutToUnion, pushout.inl_desc, Category.comp_id]
      ext x
      change unionToPushout U V hU hV (rightToUnion U V x) =
        pushout.inl (interToRight U V) (interToLeft U V) x
      apply unionToPushout_of_mem_right U V hU hV
    · rw [← Category.assoc, pushoutToUnion, pushout.inr_desc, Category.comp_id]
      ext x
      change unionToPushout U V hU hV (leftToUnion U V x) =
        pushout.inr (interToRight U V) (interToLeft U V) x
      apply unionToPushout_of_mem_left U V hU hV
  exact CategoryTheory.congr_fun h p

/-- Two open sets present their literal union as the categorical topological pushout of their
intersection. -/
public def pushoutHomeomorphUnion
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    (pushout (interToRight U V) (interToLeft U V) : TopCat) ≃ₜ ↥(U ∪ V) where
  toFun := pushoutToUnion U V
  invFun := unionToPushout U V hU hV
  left_inv := unionToPushout_pushoutToUnion U V hU hV
  right_inv := pushoutToUnion_unionToPushout U V hU hV
  continuous_toFun := (pushoutToUnion U V).hom.continuous
  continuous_invFun := (unionToPushout U V hU hV).continuous

/-- Under the mapping-cylinder cofibration and homotopy-excision hypotheses, a homotopy
equivalence from the overlap to the right open set makes the left open set homotopy equivalent
to the whole union by its literal inclusion. -/
public theorem leftToUnion_isHomotopyEquivalence
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hinter : IsHomotopyEquivalence (interToRight U V).hom)
    (hcof : HomotopyExtensionProperty
      (TopCat.mappingCylinderFree (interToRight U V)).hom)
    (hexc : TopCat.IsHomotopyExcisiveSpan (interToRight U V) (interToLeft U V)) :
    IsHomotopyEquivalence (leftToUnion U V).hom := by
  have hpush : IsHomotopyEquivalence
      (pushout.inr (interToRight U V) (interToLeft U V)).hom :=
    TopCat.pushoutInr_isHomotopyEquivalence_of_cofibrant_homotopyExcisive
      (interToRight U V) (interToLeft U V) hinter hcof hexc
  obtain ⟨e, he⟩ := hpush
  refine ⟨e.trans (pushoutHomeomorphUnion U V hU hV).toHomotopyEquiv, ?_⟩
  funext x
  change pushoutToUnion U V (e x) = leftToUnion U V x
  rw [he]
  exact pushoutToUnion_inr U V x

end OpenUnionHomotopy

end SphereSixComplex
