module

public import SphereSixComplex.Topology.EstablishedAffineStarBridge

/-!
# Connector-invariant affine star filling bridge

The based image of a peripheral relator depends on the chosen connector by conjugation.  This
bridge records precisely the connector-invariant datum needed by van Kampen: the expected core
relator belongs to the normal closure of the chosen local relator's image.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Topology
namespace PaperVanKampenFourPieceCover

/-- Based van Kampen compatibility in which each elliptic filling is compared with the expected
core relator only up to normal closure. -/
public structure AffineTorusStarRelatorNormalClosureBridge
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
  oneRelator : FundamentalGroup (D.core ∩ D.ellipticThree : Set Y)
    ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩
  oneRelator_killed : D.ellipticThreeOverlapFundamentalGroupMap oneRelator = 1
  oneExpected_mem_normalClosure :
    C.rhoOne ^ orderOne * (Additive.toMul (C.translation twistOne))⁻¹ ∈
      Subgroup.normalClosure {oneToCore oneRelator}
  twoRelator : FundamentalGroup (D.core ∩ D.ellipticFour : Set Y)
    ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩
  twoRelator_killed : D.ellipticFourOverlapFundamentalGroupMap twoRelator = 1
  twoExpected_mem_normalClosure :
    C.rhoTwo ^ orderTwo * (Additive.toMul (C.translation twistTwo))⁻¹ ∈
      Subgroup.normalClosure {twoToCore twoRelator}

namespace AffineTorusStarRelatorNormalClosureBridge

variable {Y Λ : Type*} [TopologicalSpace Y] [AddCommGroup Λ]
variable {base : Y} {monodromyOne monodromyTwo : Λ →+ Λ}
variable {D : PaperVanKampenFourPieceCover base}
variable {C : AffineTorusCorePiOneData
  (FundamentalGroup D.core ⟨base, D.base_mem_core⟩) Λ monodromyOne monodromyTwo}
variable {orderOne orderTwo : ℕ} {twistOne twistTwo cuspTwist : Λ}
variable {toricSubgroup : AddSubgroup Λ}

/-- The connector-invariant bridge supplies a surjective core map and all affine relations in the
ambient group. -/
public theorem relationsAndCoreSurjective
    [LocallyPathConnectedSpace Y] [PathConnectedSpace Y]
    [TauCeti.SemilocallySimplyConnectedSpace Y]
    (S : AffineTorusStarRelatorNormalClosureBridge D C orderOne orderTwo
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
  · have hlocal : S.oneToCore S.oneRelator ∈ D.coreFundamentalGroupMap.ker := by
      rw [MonoidHom.mem_ker]
      have h := congrArg D.ellipticThreeFundamentalGroupMap S.oneRelator_killed
      rw [map_one, ← MonoidHom.comp_apply, ← S.oneSquare,
        MonoidHom.comp_apply] at h
      exact h
    have hnormal : Subgroup.normalClosure {S.oneToCore S.oneRelator} ≤
        D.coreFundamentalGroupMap.ker := by
      apply Subgroup.normalClosure_le_normal
      simpa using hlocal
    have h := hnormal S.oneExpected_mem_normalClosure
    rw [MonoidHom.mem_ker, map_mul, map_pow, map_inv] at h
    exact mul_inv_eq_one.mp h
  · have hlocal : S.twoToCore S.twoRelator ∈ D.coreFundamentalGroupMap.ker := by
      rw [MonoidHom.mem_ker]
      have h := congrArg D.ellipticFourFundamentalGroupMap S.twoRelator_killed
      rw [map_one, ← MonoidHom.comp_apply, ← S.twoSquare,
        MonoidHom.comp_apply] at h
      exact h
    have hnormal : Subgroup.normalClosure {S.twoToCore S.twoRelator} ≤
        D.coreFundamentalGroupMap.ker := by
      apply Subgroup.normalClosure_le_normal
      simpa using hlocal
    have h := hnormal S.twoExpected_mem_normalClosure
    rw [MonoidHom.mem_ker, map_mul, map_pow, map_inv] at h
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

end AffineTorusStarRelatorNormalClosureBridge
end PaperVanKampenFourPieceCover
end SphereSixComplex.Topology

end

end
