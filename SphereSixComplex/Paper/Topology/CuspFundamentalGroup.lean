module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorNormalClosureTypes
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczSimplyConnected

@[expose] public section
noncomputable section

namespace SphereSixComplex.Topology
open LatticeData
open scoped IsMulCommutative

public theorem cuspOnly_mul_comm {G : Type} [Group G]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo)
    (hcusp : C.rhoOne * C.rhoTwo = 1)
    (htoric : ∀ a ∈ paperToricSubgroup, Additive.toMul (C.translation a) = 1)
    (x y : G) : x * y = y * x := by
  let e (i : Fin 4) : Lattice := Pi.single i 1
  have h2 : C.translation (e 2) = 0 := by
    apply Additive.toMul.injective
    exact htoric _ (by change (e 2) 0 = 0 ∧ (e 2) 1 = 0; simp [e])
  have hA : paperMonodromyOne (e 2) = e 1 - e 2 := by
    ext i
    fin_cases i <;>
      norm_num [paperMonodromyOne, A₁, e, Pi.single_apply, Fin.ext_iff, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  have h1 : C.translation (e 1) = 0 := by
    have h := C.conjugate_one (e 2)
    rw [h2, hA, map_sub, h2, sub_zero] at h
    simpa using h.symm
  have hk (a : Lattice) (ha : a 0 = 0) : C.translation a = 0 := by
    have ht : C.translation (a - a 1 • e 1) = 0 := by
      apply Additive.toMul.injective
      apply htoric
      change (a - a 1 • e 1) 0 = 0 ∧ (a - a 1 • e 1) 1 = 0
      simp [e, ha]
    simpa only [map_sub, map_zsmul, h1, zsmul_zero, sub_zero] using ht
  have hinv₁ (a : Lattice) : C.translation (paperMonodromyOne a) = C.translation a := by
    have h := hk (paperMonodromyOne a - a) (by
      simp [paperMonodromyOne, A₁, dotProduct, Fin.sum_univ_succ])
    exact sub_eq_zero.mp (by simpa only [map_sub] using h)
  have hinv₂ (a : Lattice) : C.translation (paperMonodromyTwo a) = C.translation a := by
    have h := hk (paperMonodromyTwo a - a) (by
      simp [paperMonodromyTwo, A₂, dotProduct, Fin.sum_univ_succ])
    exact sub_eq_zero.mp (by simpa only [map_sub] using h)
  have hcomm₁ (a : Lattice) : Commute C.rhoOne (Additive.toMul (C.translation a)) := by
    rw [commute_iff_eq, ← mul_inv_eq_iff_eq_mul]
    exact (C.conjugate_one a).trans (congrArg Additive.toMul (hinv₁ a))
  have hcomm₂ (a : Lattice) : Commute C.rhoTwo (Additive.toMul (C.translation a)) := by
    rw [commute_iff_eq, ← mul_inv_eq_iff_eq_mul]
    exact (C.conjugate_two a).trans (congrArg Additive.toMul (hinv₂ a))
  have hrho : Commute C.rhoOne C.rhoTwo := by
    have h : C.rhoTwo = C.rhoOne⁻¹ := eq_inv_of_mul_eq_one_right hcusp
    rw [h]
    exact Commute.inv_right (Commute.refl _)
  have htrans (a b : Lattice) :
      Additive.toMul (C.translation a) * Additive.toMul (C.translation b) =
        Additive.toMul (C.translation b) * Additive.toMul (C.translation a) := by
    exact congrArg Additive.toMul ((map_add C.translation a b).symm.trans
      ((congrArg C.translation (add_comm a b)).trans (map_add C.translation b a)))
  have hgen :
      ∀ u ∈ Set.range (fun a ↦ Additive.toMul (C.translation a)) ∪ {C.rhoOne, C.rhoTwo},
      ∀ v ∈ Set.range (fun a ↦ Additive.toMul (C.translation a)) ∪ {C.rhoOne, C.rhoTwo},
        u * v = v * u := by
    rintro u (⟨a, rfl⟩ | hu) v (⟨b, rfl⟩ | hv)
    · exact htrans a b
    · rcases hv with rfl | rfl
      · exact (hcomm₁ a).symm.eq
      · exact (hcomm₂ a).symm.eq
    · rcases hu with rfl | rfl
      · exact (hcomm₁ b).eq
      · exact (hcomm₂ b).eq
    · rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hrho.eq
      · exact hrho.symm.eq
      · rfl
  have hi := Subgroup.isMulCommutative_closure hgen
  rw [C.generators_generate] at hi
  let := hi
  exact congrArg Subtype.val (mul_comm (⟨x, trivial⟩ : (⊤ : Subgroup G)) ⟨y, trivial⟩)

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology

public theorem starPiOne_mul_comm (A : AnalyticData) (N : A.CuspCentralNaturality)
    (x y : FundamentalGroup A.VanKampenSpace A.vanKampenBase) : x * y = y * x := by
  let _ := A.vanKampenCharts
  have _ : StronglyLocallyContractibleSpace A.VanKampenSpace := A.vanKampen_locallyNice
  have _ : PathConnectedSpace A.VanKampenSpace := A.vanKampen_pathConnected
  have _ : TauCeti.SemilocallySimplyConnectedSpace A.VanKampenSpace :=
    A.vanKampen_semilocallySimplyConnected
  let D := A.actualVanKampenFourPieceCover
  have hs := D.coreFundamentalGroupMap_surjective_of_overlap_surjective
    A.cuspOverlapFundamentalGroupMap_surjective
    A.ellipticThreeOverlapFundamentalGroupMap_surjective
    A.ellipticFourOverlapFundamentalGroupMap_surjective
  let C := (A.coreDataOf N).mapSurjective D.coreFundamentalGroupMap hs
  apply cuspOnly_mul_comm C ?_ ?_ x y
  · have hm := A.cuspBridge_meridian_core N
    have hz : Additive.toMul ((A.coreDataOf N).translation 0) = 1 := by
      rw [map_zero]; rfl
    rw [hz, inv_one, mul_one] at hm
    change D.coreFundamentalGroupMap (A.coreDataOf N).rhoOne *
      D.coreFundamentalGroupMap (A.coreDataOf N).rhoTwo = 1
    calc
      _ = D.coreFundamentalGroupMap
          ((A.coreDataOf N).rhoOne * (A.coreDataOf N).rhoTwo) :=
        (map_mul D.coreFundamentalGroupMap _ _).symm
      _ = D.coreFundamentalGroupMap (A.cuspOverlapToCore A.cuspAffineBridgeMeridian) :=
        congrArg D.coreFundamentalGroupMap hm.symm
      _ = D.cuspFundamentalGroupMap
          (D.cuspOverlapFundamentalGroupMap A.cuspAffineBridgeMeridian) :=
        DFunLike.congr_fun A.cuspAffineBridge_cuspSquare _
      _ = 1 := (congrArg D.cuspFundamentalGroupMap A.cuspAffineBridge_meridian_killed).trans
        (map_one D.cuspFundamentalGroupMap)
  · intro a ha
    change D.coreFundamentalGroupMap (Additive.toMul ((A.coreDataOf N).translation a)) = 1
    calc
      _ = D.coreFundamentalGroupMap
          (A.cuspOverlapToCore (Additive.toMul (A.cuspAffineBridgeTranslation a))) :=
        congrArg D.coreFundamentalGroupMap (A.cuspBridge_translation_core N a).symm
      _ = D.cuspFundamentalGroupMap (D.cuspOverlapFundamentalGroupMap
          (Additive.toMul (A.cuspAffineBridgeTranslation a))) :=
        DFunLike.congr_fun A.cuspAffineBridge_cuspSquare _
      _ = 1 := (congrArg D.cuspFundamentalGroupMap
          (A.cuspAffineBridge_toric_killed a ha)).trans (map_one D.cuspFundamentalGroupMap)

end SphereSixComplex.Geometry.AnalyticData


namespace SphereSixComplex.Geometry.AnalyticData

public theorem star_simplyConnectedSpace_of_homologyOne_subsingleton
    (A : AnalyticData) (N : A.CuspCentralNaturality)
    [Subsingleton (IntegralSingularHomology 1 A.VanKampenSpace)] :
    SimplyConnectedSpace A.VanKampenSpace := by
  have := A.vanKampen_pathConnected
  exact Topology.simplyConnectedSpace_of_mul_comm_of_homologyOne_subsingleton
    A.vanKampenBase (A.starPiOne_mul_comm N)

end SphereSixComplex.Geometry.AnalyticData
