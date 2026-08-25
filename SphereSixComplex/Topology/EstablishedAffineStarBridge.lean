module

public import SphereSixComplex.Topology.AffineVanKampenTransport
public import SphereSixComplex.Topology.EstablishedBasedVanKampen

/-!
# Based van Kampen bridge for affine star fillings

This source-independent bridge records the based fundamental-group squares relating three collar
inclusions to a four-piece star.  The local filling kernels then impose the affine relations in
the ambient fundamental group, while groupoid van Kampen supplies surjectivity of the core map.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Topology
namespace PaperVanKampenFourPieceCover

/-- Exact based fundamental-group compatibility data for two cyclic affine fillings and one toric
filling attached to an affine core. -/
public structure AffineTorusStarFillingBridge
    {Y Λ : Type*} [TopologicalSpace Y] [AddCommGroup Λ]
    {base : Y} {monodromyOne monodromyTwo : Λ →+ Λ}
    (D : PaperVanKampenFourPieceCover base)
    (C : AffineTorusCorePiOneData
      (FundamentalGroup D.core ⟨base, D.base_mem_core⟩) Λ
      monodromyOne monodromyTwo)
    (orderOne orderTwo : ℕ) (twistOne twistTwo cuspTwist : Λ)
    (toricSubgroup : AddSubgroup Λ) where
  cuspSurjective : Function.Surjective D.cuspOverlapFundamentalGroupMap
  oneSurjective : Function.Surjective D.ellipticThreeOverlapFundamentalGroupMap
  twoSurjective : Function.Surjective D.ellipticFourOverlapFundamentalGroupMap
  cuspToCore :
    FundamentalGroup (D.core ∩ D.cusp : Set Y) ⟨D.cuspPoint, D.cuspPoint_mem⟩ →*
      FundamentalGroup D.core ⟨base, D.base_mem_core⟩
  oneToCore :
    FundamentalGroup (D.core ∩ D.ellipticThree : Set Y)
        ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩ →*
      FundamentalGroup D.core ⟨base, D.base_mem_core⟩
  twoToCore :
    FundamentalGroup (D.core ∩ D.ellipticFour : Set Y)
        ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩ →*
      FundamentalGroup D.core ⟨base, D.base_mem_core⟩
  cuspSquare : D.coreFundamentalGroupMap.comp cuspToCore =
    D.cuspFundamentalGroupMap.comp D.cuspOverlapFundamentalGroupMap
  oneSquare : D.coreFundamentalGroupMap.comp oneToCore =
    D.ellipticThreeFundamentalGroupMap.comp D.ellipticThreeOverlapFundamentalGroupMap
  twoSquare : D.coreFundamentalGroupMap.comp twoToCore =
    D.ellipticFourFundamentalGroupMap.comp D.ellipticFourOverlapFundamentalGroupMap
  cuspTranslation : Λ →+
    Additive (FundamentalGroup (D.core ∩ D.cusp : Set Y)
      ⟨D.cuspPoint, D.cuspPoint_mem⟩)
  cuspMeridian : FundamentalGroup (D.core ∩ D.cusp : Set Y)
    ⟨D.cuspPoint, D.cuspPoint_mem⟩
  cuspTranslation_core : ∀ a,
    cuspToCore (Additive.toMul (cuspTranslation a)) =
      Additive.toMul (C.translation a)
  cuspMeridian_core : cuspToCore cuspMeridian =
    C.rhoOne * C.rhoTwo * (Additive.toMul (C.translation cuspTwist))⁻¹
  cuspMeridian_killed : D.cuspOverlapFundamentalGroupMap cuspMeridian = 1
  cuspToric_killed : ∀ a ∈ toricSubgroup,
    D.cuspOverlapFundamentalGroupMap
      (Additive.toMul (cuspTranslation a)) = 1
  oneTranslation : Λ →+
    Additive (FundamentalGroup (D.core ∩ D.ellipticThree : Set Y)
      ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩)
  oneMeridian : FundamentalGroup (D.core ∩ D.ellipticThree : Set Y)
    ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩
  oneTranslation_core : ∀ a,
    oneToCore (Additive.toMul (oneTranslation a)) =
      Additive.toMul (C.translation a)
  oneMeridian_core : oneToCore oneMeridian = C.rhoOne
  oneRelation_killed : D.ellipticThreeOverlapFundamentalGroupMap
    (oneMeridian ^ orderOne *
      (Additive.toMul (oneTranslation twistOne))⁻¹) = 1
  twoTranslation : Λ →+
    Additive (FundamentalGroup (D.core ∩ D.ellipticFour : Set Y)
      ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩)
  twoMeridian : FundamentalGroup (D.core ∩ D.ellipticFour : Set Y)
    ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩
  twoTranslation_core : ∀ a,
    twoToCore (Additive.toMul (twoTranslation a)) =
      Additive.toMul (C.translation a)
  twoMeridian_core : twoToCore twoMeridian = C.rhoTwo
  twoRelation_killed : D.ellipticFourOverlapFundamentalGroupMap
    (twoMeridian ^ orderTwo *
      (Additive.toMul (twoTranslation twistTwo))⁻¹) = 1

namespace AffineTorusStarFillingBridge

variable {Y Λ : Type*} [TopologicalSpace Y] [AddCommGroup Λ]
variable {base : Y} {monodromyOne monodromyTwo : Λ →+ Λ}
variable {D : PaperVanKampenFourPieceCover base}
variable {C : AffineTorusCorePiOneData
  (FundamentalGroup D.core ⟨base, D.base_mem_core⟩) Λ monodromyOne monodromyTwo}
variable {orderOne orderTwo : ℕ} {twistOne twistTwo cuspTwist : Λ}
variable {toricSubgroup : AddSubgroup Λ}

/-- The bridge supplies a surjective core map and all affine relations in the ambient group.

The three niceness hypotheses are what the covering-space form of van Kampen needs of the ambient
space; the glued star satisfies them because it is a complex manifold, and it is connected. -/
public theorem relationsAndCoreSurjective
    [LocallyPathConnectedSpace Y] [PathConnectedSpace Y]
    [TauCeti.SemilocallySimplyConnectedSpace Y]
    (S : AffineTorusStarFillingBridge D C orderOne orderTwo
      twistOne twistTwo cuspTwist toricSubgroup) :
    ∃ hcore : Function.Surjective D.coreFundamentalGroupMap,
      AffineTorusStarFillingRelations
        (C.mapSurjective D.coreFundamentalGroupMap hcore)
        orderOne orderTwo twistOne twistTwo cuspTwist toricSubgroup := by
  let hcore := D.coreFundamentalGroupMap_surjective_of_overlap_surjective
    S.cuspSurjective S.oneSurjective S.twoSurjective
  refine ⟨hcore, ?_⟩
  refine
    { elliptic_one := ?_
      elliptic_two := ?_
      cusp := ?_
      toric_vanishes := ?_ }
  · have h := congrArg D.ellipticThreeFundamentalGroupMap S.oneRelation_killed
    rw [map_one, ← MonoidHom.comp_apply, ← S.oneSquare,
      MonoidHom.comp_apply, map_mul, map_pow, map_inv,
      S.oneMeridian_core, S.oneTranslation_core, map_mul, map_pow, map_inv] at h
    exact mul_inv_eq_one.mp h
  · have h := congrArg D.ellipticFourFundamentalGroupMap S.twoRelation_killed
    rw [map_one, ← MonoidHom.comp_apply, ← S.twoSquare,
      MonoidHom.comp_apply, map_mul, map_pow, map_inv,
      S.twoMeridian_core, S.twoTranslation_core, map_mul, map_pow, map_inv] at h
    exact mul_inv_eq_one.mp h
  · have h := congrArg D.cuspFundamentalGroupMap S.cuspMeridian_killed
    rw [map_one, ← MonoidHom.comp_apply, ← S.cuspSquare,
      MonoidHom.comp_apply, S.cuspMeridian_core, map_mul, map_inv, map_mul] at h
    exact mul_inv_eq_one.mp h
  · intro a ha
    have h := congrArg D.cuspFundamentalGroupMap (S.cuspToric_killed a ha)
    rw [map_one, ← MonoidHom.comp_apply, ← S.cuspSquare,
      MonoidHom.comp_apply, S.cuspTranslation_core] at h
    exact h

end AffineTorusStarFillingBridge
end PaperVanKampenFourPieceCover
end SphereSixComplex.Topology

end
