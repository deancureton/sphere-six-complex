module

public import SphereSixComplex.Topology.MappingCylinderGluing
public import SphereSixComplex.Topology.MappingCylinderHomotopyExtension
public import SphereSixComplex.Topology.RelativeHomotopy
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.PartitionOfUnity

/-!
# Homotopy equivalences from homotopy-excisive open unions

Two open subsets present their union as the topological pushout of their intersection.  For a
homotopy-excisive span, replacing the span by its double mapping cylinder does not change its
homotopy type.  Hence, if the intersection-to-right map is a homotopy equivalence, the left
subset includes into the union by a homotopy equivalence.

The required homotopy-extension property is automatic for the closed free end of a mapping
cylinder; it is not imposed on the literal open intersection inside either member of the cover.

Mathlib has the partition-of-unity theorem needed to numerate a finite open cover, but currently
has no Dold homotopy-pushout theorem saying that a numerated open cover makes the double mapping
cylinder collapse a homotopy equivalence.  The last section isolates its exact constructive
output as `TwoSetNumeration.HomotopyExcisionData`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ContinuousMap Set Topology TopologicalSpace
open scoped BigOperators

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

/-- Homotopy excision lets a homotopy equivalence on one attaching leg pass to the opposite
coprojection of the ordinary pushout. -/
public theorem pushoutInr_isHomotopyEquivalence_of_homotopyExcisive
    (f : A ⟶ X) (g : A ⟶ Y)
    (hf : IsHomotopyEquivalence f.hom)
    (hexc : IsHomotopyExcisiveSpan f g) :
    IsHomotopyEquivalence (pushout.inr f g).hom :=
  pushoutInr_isHomotopyEquivalence_of_cofibrant_homotopyExcisive f g hf
    (mappingCylinderFree_homotopyExtensionProperty f) hexc

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

/-! ## Numerations and the remaining Dold comparison -/

/-- A numeration of a two-set cover.  Weight zero belongs to the right-hand side and weight one
to the left-hand side; away from the endpoints the point lies in the intersection. -/
public structure TwoSetNumeration (U V : Set X) where
  weight : C(↥(U ∪ V), unitInterval)
  weight_ne_zero_mem_left : ∀ x, weight x ≠ 0 → x.1 ∈ U
  weight_ne_one_mem_right : ∀ x, weight x ≠ 1 → x.1 ∈ V

/-- A normal paracompact union admits a numeration subordinate to its two open members. -/
public theorem exists_twoSetNumeration
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [NormalSpace ↥(U ∪ V)] [ParacompactSpace ↥(U ∪ V)] :
    Nonempty (TwoSetNumeration U V) := by
  have hopen : ∀ i, IsOpen (unionCoverSet U V i) := by
    intro i
    cases i
    · exact hU.preimage continuous_subtype_val
    · exact hV.preimage continuous_subtype_val
  have hcover : (Set.univ : Set ↥(U ∪ V)) ⊆ ⋃ i, unionCoverSet U V i := by
    intro x _
    rcases x.2 with hxU | hxV
    · exact Set.mem_iUnion.2 ⟨false, hxU⟩
    · exact Set.mem_iUnion.2 ⟨true, hxV⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate
    (X := ↥(U ∪ V)) isClosed_univ (unionCoverSet U V) hopen hcover
  let w : C(↥(U ∪ V), unitInterval) :=
    ⟨fun x ↦ ⟨ρ false x, ρ.nonneg false x, ρ.le_one false x⟩, by fun_prop⟩
  refine ⟨⟨w, ?_, ?_⟩⟩
  · intro x hx
    apply hρ false
    apply subset_closure
    change ρ false x ≠ 0
    intro hzero
    apply hx
    apply Subtype.ext
    exact hzero
  · intro x hx
    have hsum := ρ.sum_eq_one (x := x) (Set.mem_univ x)
    rw [finsum_eq_sum_of_fintype, Fintype.sum_bool] at hsum
    have hright : ρ true x ≠ 0 := by
      intro hzero
      apply hx
      apply Subtype.ext
      dsimp [w]
      rw [hzero, zero_add] at hsum
      exact hsum
    apply hρ true
    apply subset_closure
    exact hright

/-- Collapse the double mapping cylinder directly to the literal open union. -/
public def doubleMappingCylinderToUnion (U V : Set X) :
    TopCat.DoubleMappingCylinder (interToRight U V) (interToLeft U V) ⟶
      TopCat.of ↥(U ∪ V) :=
  TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V) ≫
    pushoutToUnion U V

namespace TwoSetNumeration

variable {U V : Set X} (N : TwoSetNumeration U V)

/-- The constructive output of the missing numerated-open-cover homotopy-pushout theorem: a
section of the double-mapping-cylinder collapse, its required pointwise formula, and a homotopy
from section after collapse to the identity.  The opposite composite is then literally the
identity.  The standard Dold theorem should construct this data from `N`; all subsequent
deductions are proved here. -/
public structure HomotopyExcisionData where
  inverse : C(↥(U ∪ V),
    TopCat.DoubleMappingCylinder (interToRight U V) (interToLeft U V))
  inverse_zero : ∀ (x : ↥(U ∪ V)) (hx : N.weight x = 0), inverse x =
    TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
      (TopCat.mappingCylinderBase (interToRight U V)
        ⟨x.1, N.weight_ne_one_mem_right x (by rw [hx]; exact zero_ne_one)⟩)
  inverse_one : ∀ (x : ↥(U ∪ V)) (hx : N.weight x = 1), inverse x =
    TopCat.doubleMappingCylinderRight (interToRight U V) (interToLeft U V)
      ⟨x.1, N.weight_ne_zero_mem_left x (by rw [hx]; exact one_ne_zero)⟩
  inverse_interior : ∀ (x : ↥(U ∪ V))
      (hzero : N.weight x ≠ 0) (hone : N.weight x ≠ 1), inverse x =
    TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
      (TopCat.mappingCylinderCylinder (interToRight U V)
        (⟨x.1, N.weight_ne_zero_mem_left x hzero,
          N.weight_ne_one_mem_right x hone⟩, N.weight x))
  sourceHomotopy : ContinuousMap.Homotopy
    (inverse.comp (doubleMappingCylinderToUnion U V).hom)
    (ContinuousMap.id
      (TopCat.DoubleMappingCylinder (interToRight U V) (interToLeft U V)))

/-- The numeration formula makes the chosen inverse a strict right inverse of the collapse. -/
public theorem HomotopyExcisionData.collapse_inverse
    (D : N.HomotopyExcisionData) :
    (doubleMappingCylinderToUnion U V).hom.comp D.inverse =
      ContinuousMap.id ↥(U ∪ V) := by
  apply ContinuousMap.ext
  intro x
  change doubleMappingCylinderToUnion U V (D.inverse x) = x
  by_cases hzero : N.weight x = 0
  · let v : V := ⟨x.1, N.weight_ne_one_mem_right x (by rw [hzero]; exact zero_ne_one)⟩
    rw [D.inverse_zero x hzero]
    change doubleMappingCylinderToUnion U V
      (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
        (TopCat.mappingCylinderBase (interToRight U V) v)) = x
    change pushoutToUnion U V
      (TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
        (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
          (TopCat.mappingCylinderBase (interToRight U V) v))) = x
    rw [show TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
        (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
          (TopCat.mappingCylinderBase (interToRight U V) v)) =
          TopCat.mappingCylinderToPushout (interToRight U V) (interToLeft U V)
            (TopCat.mappingCylinderBase (interToRight U V) v) from
      CategoryTheory.congr_fun
        (TopCat.doubleMappingCylinderLeft_comp_collapse
          (interToRight U V) (interToLeft U V)) _]
    change pushoutToUnion U V
      (pushout.inl (interToRight U V) (interToLeft U V)
        (TopCat.mappingCylinderCollapse (interToRight U V)
          (TopCat.mappingCylinderBase (interToRight U V) v))) = x
    rw [show TopCat.mappingCylinderCollapse (interToRight U V)
        (TopCat.mappingCylinderBase (interToRight U V) v) = v from
      CategoryTheory.congr_fun
        (TopCat.mappingCylinderBase_comp_collapse (interToRight U V)) v,
      pushoutToUnion_inl]
    rfl
  · by_cases hone : N.weight x = 1
    · let u : U := ⟨x.1, N.weight_ne_zero_mem_left x (by rw [hone]; exact one_ne_zero)⟩
      rw [D.inverse_one x hone]
      change doubleMappingCylinderToUnion U V
        (TopCat.doubleMappingCylinderRight (interToRight U V) (interToLeft U V) u) = x
      change pushoutToUnion U V
        (TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
          (TopCat.doubleMappingCylinderRight (interToRight U V) (interToLeft U V) u)) = x
      rw [show TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
          (TopCat.doubleMappingCylinderRight (interToRight U V) (interToLeft U V) u) =
          pushout.inr (interToRight U V) (interToLeft U V) u from
        CategoryTheory.congr_fun
          (TopCat.doubleMappingCylinderRight_comp_collapse
            (interToRight U V) (interToLeft U V)) u,
        pushoutToUnion_inr]
      rfl
    · let z : ↥(U ∩ V) :=
        ⟨x.1, N.weight_ne_zero_mem_left x hzero, N.weight_ne_one_mem_right x hone⟩
      rw [D.inverse_interior x hzero hone]
      change doubleMappingCylinderToUnion U V
        (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
          (TopCat.mappingCylinderCylinder (interToRight U V) (z, N.weight x))) = x
      change pushoutToUnion U V
        (TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
          (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
            (TopCat.mappingCylinderCylinder (interToRight U V) (z, N.weight x)))) = x
      rw [show TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
          (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
            (TopCat.mappingCylinderCylinder (interToRight U V) (z, N.weight x))) =
          TopCat.mappingCylinderToPushout (interToRight U V) (interToLeft U V)
            (TopCat.mappingCylinderCylinder (interToRight U V) (z, N.weight x)) from
        CategoryTheory.congr_fun
          (TopCat.doubleMappingCylinderLeft_comp_collapse
            (interToRight U V) (interToLeft U V)) _]
      change pushoutToUnion U V
        (pushout.inl (interToRight U V) (interToLeft U V)
          (TopCat.mappingCylinderCollapse (interToRight U V)
            (TopCat.mappingCylinderCylinder (interToRight U V) (z, N.weight x)))) = x
      rw [show TopCat.mappingCylinderCollapse (interToRight U V)
          (TopCat.mappingCylinderCylinder (interToRight U V) (z, N.weight x)) =
          interToRight U V z from
        CategoryTheory.congr_fun
          (TopCat.mappingCylinderCylinder_comp_collapse (interToRight U V)) _,
        pushoutToUnion_inl]
      rfl

namespace HomotopyExcisionData

/-- Explicit Dold comparison data makes the open-cover span homotopy-excisive. -/
public theorem isHomotopyExcisiveSpan
    (D : N.HomotopyExcisionData) (hU : IsOpen U) (hV : IsOpen V) :
    TopCat.IsHomotopyExcisiveSpan (interToRight U V) (interToLeft U V) := by
  let eUnion :
      (TopCat.DoubleMappingCylinder (interToRight U V) (interToLeft U V) : Type u) ≃ₕ
        ↥(U ∪ V) :=
    { toFun := (doubleMappingCylinderToUnion U V).hom
      invFun := D.inverse
      left_inv := ⟨D.sourceHomotopy⟩
      right_inv := by rw [D.collapse_inverse] }
  let ePushout := eUnion.trans (pushoutHomeomorphUnion U V hU hV).symm.toHomotopyEquiv
  refine ⟨ePushout, ?_⟩
  funext p
  change unionToPushout U V hU hV
      (pushoutToUnion U V
        (TopCat.doubleMappingCylinderCollapse
          (interToRight U V) (interToLeft U V) p)) =
    TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V) p
  exact unionToPushout_pushoutToUnion U V hU hV _

end HomotopyExcisionData

end TwoSetNumeration

/-- Under the homotopy-excision hypothesis, a homotopy equivalence from the overlap to the right
open set makes the left open set homotopy equivalent to the whole union by its literal
inclusion. -/
public theorem leftToUnion_isHomotopyEquivalence
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hinter : IsHomotopyEquivalence (interToRight U V).hom)
    (hexc : TopCat.IsHomotopyExcisiveSpan (interToRight U V) (interToLeft U V)) :
    IsHomotopyEquivalence (leftToUnion U V).hom := by
  have hpush : IsHomotopyEquivalence
      (pushout.inr (interToRight U V) (interToLeft U V)).hom :=
    TopCat.pushoutInr_isHomotopyEquivalence_of_homotopyExcisive
      (interToRight U V) (interToLeft U V) hinter hexc
  obtain ⟨e, he⟩ := hpush
  refine ⟨e.trans (pushoutHomeomorphUnion U V hU hV).toHomotopyEquiv, ?_⟩
  funext x
  change pushoutToUnion U V (e x) = leftToUnion U V x
  rw [he]
  exact pushoutToUnion_inr U V x

end OpenUnionHomotopy

end SphereSixComplex
