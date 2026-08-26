module

public import SphereSixComplex.Topology.BinaryOpenCoverAssembly
public import SphereSixComplex.Topology.MayerVietoris
public import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Degree-zero endpoint for the Set-based Mayer--Vietoris map

The binary-open-cover chain model proves surjectivity of its degree-zero map without invoking full
subdivision.  This file transports that result to the Set/subtype presentation used by the
project's long exact sequence.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set TopologicalSpace

namespace SphereSixComplex.IntegralMayerVietoris

private def leftOpenInUnion
    {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) :
    Opens (A ∪ B : Set X) :=
  ⟨Subtype.val ⁻¹' A, hA.preimage continuous_subtype_val⟩

private def rightOpenInUnion
    {X : Type} [TopologicalSpace X] (A B : Set X) (hB : IsOpen B) :
    Opens (A ∪ B : Set X) :=
  ⟨Subtype.val ⁻¹' B, hB.preimage continuous_subtype_val⟩

private theorem leftOpenInUnion_sup_rightOpenInUnion
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    leftOpenInUnion A B hA ⊔ rightOpenInUnion A B hB = ⊤ := by
  apply Opens.ext
  ext x
  change (x.1 ∈ A ∨ x.1 ∈ B) ↔ True
  exact iff_true_intro x.2

private def leftOpenInUnionToLeft
    {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) :
    (Opens.toTopCat (TopCat.of (A ∪ B : Set X))).obj
        (leftOpenInUnion A B hA) ⟶ TopCat.of A :=
  TopCat.ofHom
    { toFun x := ⟨x.1.1, x.2⟩
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }

private def rightOpenInUnionToRight
    {X : Type} [TopologicalSpace X] (A B : Set X) (hB : IsOpen B) :
    (Opens.toTopCat (TopCat.of (A ∪ B : Set X))).obj
        (rightOpenInUnion A B hB) ⟶ TopCat.of B :=
  TopCat.ofHom
    { toFun x := ⟨x.1.1, x.2⟩
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }

private theorem leftOpenInUnion_inclusion_fac
    {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) :
    leftOpenInUnionToLeft A B hA ≫
        TopCat.ofHom (leftToUnion A B) =
      @Opens.inclusion' (TopCat.of (A ∪ B : Set X))
        (leftOpenInUnion A B hA) := by
  ext x
  rfl

private theorem rightOpenInUnion_inclusion_fac
    {X : Type} [TopologicalSpace X] (A B : Set X) (hB : IsOpen B) :
    rightOpenInUnionToRight A B hB ≫
        TopCat.ofHom (rightToUnion A B) =
      @Opens.inclusion' (TopCat.of (A ∪ B : Set X))
        (rightOpenInUnion A B hB) := by
  ext x
  rfl

private theorem leftOpenInUnion_homology_fac
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (n : ℕ) :
    (BinaryOpenCover.integralHomologyFunctor n).map
          (leftOpenInUnionToLeft A B hA) ≫
        (BinaryOpenCover.integralHomologyFunctor n).map
          (TopCat.ofHom (leftToUnion A B)) =
      (BinaryOpenCover.integralHomologyFunctor n).map
        (@Opens.inclusion' (TopCat.of (A ∪ B : Set X))
          (leftOpenInUnion A B hA)) := by
  rw [← (BinaryOpenCover.integralHomologyFunctor n).map_comp]
  exact congrArg (BinaryOpenCover.integralHomologyFunctor n).map
    (leftOpenInUnion_inclusion_fac A B hA)

private theorem rightOpenInUnion_homology_fac
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hB : IsOpen B) (n : ℕ) :
    (BinaryOpenCover.integralHomologyFunctor n).map
          (rightOpenInUnionToRight A B hB) ≫
        (BinaryOpenCover.integralHomologyFunctor n).map
          (TopCat.ofHom (rightToUnion A B)) =
      (BinaryOpenCover.integralHomologyFunctor n).map
        (@Opens.inclusion' (TopCat.of (A ∪ B : Set X))
          (rightOpenInUnion A B hB)) := by
  rw [← (BinaryOpenCover.integralHomologyFunctor n).map_comp]
  exact congrArg (BinaryOpenCover.integralHomologyFunctor n).map
    (rightOpenInUnion_inclusion_fac A B hB)

private noncomputable def pairToBiprod
    {Y : TopCat} (U V : Opens Y) (n : ℕ)
    (uv :
      (BinaryOpenCover.integralHomologyFunctor n).obj
          ((Opens.toTopCat Y).obj U) ×
        (BinaryOpenCover.integralHomologyFunctor n).obj
          ((Opens.toTopCat Y).obj V)) :
    ((BinaryOpenCover.integralHomologyFunctor n).obj
          ((Opens.toTopCat Y).obj U) ⊞
        (BinaryOpenCover.integralHomologyFunctor n).obj
          ((Opens.toTopCat Y).obj V) : AddCommGrpCat) :=
  (AddCommGrpCat.biprodIsoProd _ _).inv uv

private noncomputable def biprodToPair
    {Y : TopCat} (U V : Opens Y) (n : ℕ)
    (z :
      ((BinaryOpenCover.integralHomologyFunctor n).obj
            ((Opens.toTopCat Y).obj U) ⊞
          (BinaryOpenCover.integralHomologyFunctor n).obj
            ((Opens.toTopCat Y).obj V) : AddCommGrpCat)) :
    (BinaryOpenCover.integralHomologyFunctor n).obj
          ((Opens.toTopCat Y).obj U) ×
        (BinaryOpenCover.integralHomologyFunctor n).obj
          ((Opens.toTopCat Y).obj V) :=
  (AddCommGrpCat.biprodIsoProd _ _).hom z

private theorem pairToBiprod_biprodToPair
    {Y : TopCat} (U V : Opens Y) (n : ℕ)
    (z :
      ((BinaryOpenCover.integralHomologyFunctor n).obj
            ((Opens.toTopCat Y).obj U) ⊞
          (BinaryOpenCover.integralHomologyFunctor n).obj
            ((Opens.toTopCat Y).obj V) : AddCommGrpCat)) :
    pairToBiprod U V n (biprodToPair U V n z) = z := by
  exact (AddCommGrpCat.biprodIsoProd
    ((BinaryOpenCover.integralHomologyFunctor n).obj
      ((Opens.toTopCat Y).obj U))
    ((BinaryOpenCover.integralHomologyFunctor n).obj
      ((Opens.toTopCat Y).obj V))).hom_inv_id_apply z

private theorem pairToBiprod_surjective
    {Y : TopCat} (U V : Opens Y) (n : ℕ) :
    Function.Surjective (pairToBiprod U V n) := by
  intro z
  exact ⟨biprodToPair U V n z, pairToBiprod_biprodToPair U V n z⟩

private noncomputable def integralMVFromProduct
    {Y : TopCat} (U V : Opens Y)
    (uv :
      (BinaryOpenCover.integralHomologyFunctor 0).obj
            ((Opens.toTopCat Y).obj U) ×
          (BinaryOpenCover.integralHomologyFunctor 0).obj
            ((Opens.toTopCat Y).obj V)) :
    (BinaryOpenCover.integralHomologyFunctor 0).obj Y :=
  BinaryOpenCover.integralMVFromBiprod U V 0 (pairToBiprod U V 0 uv)

private theorem integralMV_comp_pairToBiprod_zero_surjective
    {Y : TopCat} (U V : Opens Y) (hcover : U ⊔ V = ⊤) :
    Function.Surjective
      (integralMVFromProduct U V) :=
  (BinaryOpenCover.integralMVFromBiprod_zero_surjective U V hcover).comp
    (pairToBiprod_surjective U V 0)

private theorem integralMVFromBiprod_biprodIsoProd_inv_apply
    {Y : TopCat} (U V : Opens Y) (n : ℕ)
    (u : (BinaryOpenCover.integralHomologyFunctor n).obj
      ((Opens.toTopCat Y).obj U))
    (v : (BinaryOpenCover.integralHomologyFunctor n).obj
      ((Opens.toTopCat Y).obj V)) :
    BinaryOpenCover.integralMVFromBiprod U V n
        (pairToBiprod U V n ⟨u, v⟩) =
      (BinaryOpenCover.integralHomologyFunctor n).map
          (Opens.inclusion' U) u +
        (BinaryOpenCover.integralHomologyFunctor n).map
          (Opens.inclusion' V) v := by
  dsimp [pairToBiprod, BinaryOpenCover.integralMVFromBiprod]
  rw [← ConcreteCategory.comp_apply]
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc]

private theorem integralMVFromProduct_pair_apply
    {Y : TopCat} (U V : Opens Y)
    (u : (BinaryOpenCover.integralHomologyFunctor 0).obj
      ((Opens.toTopCat Y).obj U))
    (v : (BinaryOpenCover.integralHomologyFunctor 0).obj
      ((Opens.toTopCat Y).obj V)) :
    integralMVFromProduct U V ⟨u, v⟩ =
      (BinaryOpenCover.integralHomologyFunctor 0).map
          (Opens.inclusion' U) u +
        (BinaryOpenCover.integralHomologyFunctor 0).map
          (Opens.inclusion' V) v := by
  change BinaryOpenCover.integralMVFromBiprod U V 0
      (pairToBiprod U V 0 ⟨u, v⟩) = _
  exact integralMVFromBiprod_biprodIsoProd_inv_apply U V 0 u v

private theorem sumMap_flattenPair_zero
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B)
    (u : (BinaryOpenCover.integralHomologyFunctor 0).obj
      ((Opens.toTopCat (TopCat.of (A ∪ B : Set X))).obj
        (leftOpenInUnion A B hA)))
    (v : (BinaryOpenCover.integralHomologyFunctor 0).obj
      ((Opens.toTopCat (TopCat.of (A ∪ B : Set X))).obj
        (rightOpenInUnion A B hB))) :
    sumMap A B 0
        ((BinaryOpenCover.integralHomologyFunctor 0).map
            (leftOpenInUnionToLeft A B hA) u,
          (BinaryOpenCover.integralHomologyFunctor 0).map
            (rightOpenInUnionToRight A B hB) v) =
      (BinaryOpenCover.integralHomologyFunctor 0).map
          (@Opens.inclusion' (TopCat.of (A ∪ B : Set X))
            (leftOpenInUnion A B hA)) u +
        (BinaryOpenCover.integralHomologyFunctor 0).map
          (@Opens.inclusion' (TopCat.of (A ∪ B : Set X))
            (rightOpenInUnion A B hB)) v := by
  have hLeft := ConcreteCategory.congr_hom
    (leftOpenInUnion_homology_fac A B hA 0) u
  have hRight := ConcreteCategory.congr_hom
    (rightOpenInUnion_homology_fac A B hB 0) v
  have hLeft' :
      (BinaryOpenCover.integralHomologyFunctor 0).map
          (TopCat.ofHom (leftToUnion A B))
          ((BinaryOpenCover.integralHomologyFunctor 0).map
            (leftOpenInUnionToLeft A B hA) u) =
        (BinaryOpenCover.integralHomologyFunctor 0).map
          (@Opens.inclusion' (TopCat.of (A ∪ B : Set X))
            (leftOpenInUnion A B hA)) u := by
    rw [← ConcreteCategory.comp_apply]
    exact hLeft
  have hRight' :
      (BinaryOpenCover.integralHomologyFunctor 0).map
          (TopCat.ofHom (rightToUnion A B))
          ((BinaryOpenCover.integralHomologyFunctor 0).map
            (rightOpenInUnionToRight A B hB) v) =
        (BinaryOpenCover.integralHomologyFunctor 0).map
          (@Opens.inclusion' (TopCat.of (A ∪ B : Set X))
            (rightOpenInUnion A B hB)) v := by
    rw [← ConcreteCategory.comp_apply]
    exact hRight
  change
    (BinaryOpenCover.integralHomologyFunctor 0).map
          (TopCat.ofHom (leftToUnion A B))
          ((BinaryOpenCover.integralHomologyFunctor 0).map
            (leftOpenInUnionToLeft A B hA) u) +
        (BinaryOpenCover.integralHomologyFunctor 0).map
          (TopCat.ofHom (rightToUnion A B))
          ((BinaryOpenCover.integralHomologyFunctor 0).map
            (rightOpenInUnionToRight A B hB) v) = _
  rw [hLeft', hRight']

private theorem sumMap_flattenPair_eq_integralMVFromProduct
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B)
    (u : (BinaryOpenCover.integralHomologyFunctor 0).obj
      ((Opens.toTopCat (TopCat.of (A ∪ B : Set X))).obj
        (leftOpenInUnion A B hA)))
    (v : (BinaryOpenCover.integralHomologyFunctor 0).obj
      ((Opens.toTopCat (TopCat.of (A ∪ B : Set X))).obj
        (rightOpenInUnion A B hB))) :
    sumMap A B 0
        ((BinaryOpenCover.integralHomologyFunctor 0).map
            (leftOpenInUnionToLeft A B hA) u,
          (BinaryOpenCover.integralHomologyFunctor 0).map
            (rightOpenInUnionToRight A B hB) v) =
      integralMVFromProduct (Y := TopCat.of (A ∪ B : Set X))
        (leftOpenInUnion A B hA)
        (rightOpenInUnion A B hB) ⟨u, v⟩ := by
  exact (sumMap_flattenPair_zero A B hA hB u v).trans
    (integralMVFromProduct_pair_apply (Y := TopCat.of (A ∪ B : Set X))
      (leftOpenInUnion A B hA) (rightOpenInUnion A B hB) u v).symm

private theorem sumMap_zero_has_preimage
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B)
    (y : IntegralSingularHomology 0 (A ∪ B : Set X)) :
    ∃ x : IntegralSingularHomology 0 A × IntegralSingularHomology 0 B,
      sumMap A B 0 x = y := by
  have hcover :
      leftOpenInUnion A B hA ⊔ rightOpenInUnion A B hB = ⊤ :=
    leftOpenInUnion_sup_rightOpenInUnion A B hA hB
  obtain ⟨uv, huv⟩ := integralMV_comp_pairToBiprod_zero_surjective
    (Y := TopCat.of (A ∪ B : Set X))
    (leftOpenInUnion A B hA) (rightOpenInUnion A B hB) hcover y
  obtain ⟨u, v⟩ := uv
  exact ⟨
    ((BinaryOpenCover.integralHomologyFunctor 0).map
        (leftOpenInUnionToLeft A B hA) u,
      (BinaryOpenCover.integralHomologyFunctor 0).map
        (rightOpenInUnionToRight A B hB) v),
    (sumMap_flattenPair_eq_integralMVFromProduct A B hA hB u v).trans huv⟩

/-- The degree-zero sum of the two inclusion maps in the Set-based Mayer--Vietoris sequence is
surjective for open subsets. -/
public theorem sumMap_zero_surjective
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    Function.Surjective (sumMap A B 0) :=
  sumMap_zero_has_preimage A B hA hB

end SphereSixComplex.IntegralMayerVietoris
