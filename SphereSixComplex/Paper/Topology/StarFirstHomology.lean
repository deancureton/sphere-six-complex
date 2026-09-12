module

public import SphereSixComplex.Paper.Topology.CuspFundamentalGroup
public import SphereSixComplex.Paper.Topology.EllipticFillingHomology
public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczSurjective

/-! # Vanishing first homology from the local filling relations

The core generators map onto first homology. The cusp and elliptic filling relations kill their
images directly, without choosing homology bases for the pieces or the Mayer–Vietoris maps.
-/

@[expose] public section
noncomputable section
open AlgebraicTopology SphereSixComplex SphereSixComplex.Topology SphereSixComplex.LatticeData

namespace SphereSixComplex.Topology

public theorem cuspElliptic_abelian_generators_eq_zero
    {H : Type} [AddCommGroup H] (t : Lattice →+ H) (r₁ r₂ : H)
    (hmon : ∀ a, t (paperMonodromyOne a) = t a)
    (htoric : ∀ a ∈ paperToricSubgroup, t a = 0)
    (hthree : (3 : ℕ) • r₁ = t (-epsilon))
    (hfour : (4 : ℕ) • r₂ = t epsilon')
    (hcusp : r₁ + r₂ = 0) :
    (∀ a, t a = 0) ∧ r₁ = 0 ∧ r₂ = 0 := by
  let e (i : Fin 4) : Lattice := Pi.single i 1
  have h2 : t (e 2) = 0 := htoric _ (by
    change (e 2) 0 = 0 ∧ (e 2) 1 = 0; simp [e])
  have hA : paperMonodromyOne (e 2) = e 1 - e 2 := by
    ext i
    fin_cases i <;>
      norm_num [paperMonodromyOne, A₁, e, Pi.single_apply, Fin.ext_iff,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have h1 : t (e 1) = 0 := by
    have h := hmon (e 2)
    simpa only [hA, map_sub, h2, sub_zero] using h
  have hk (a : Lattice) (ha : a 0 = 0) : t a = 0 := by
    have h := htoric (a - a 1 • e 1) (by
      change (a - a 1 • e 1) 0 = 0 ∧ (a - a 1 • e 1) 1 = 0
      simp [e, ha])
    simpa only [map_sub, map_zsmul, h1, zsmul_zero, sub_zero] using h
  have ht (a : Lattice) : t a = a 0 • t (e 0) := by
    have h := hk (a - a 0 • e 0) (by simp [e])
    exact sub_eq_zero.mp (by simpa only [map_sub, map_zsmul] using h)
  have he : t epsilon = t (e 0) := by simpa [epsilon] using ht epsilon
  have he' : t epsilon' = t (e 0) := by simpa [epsilon'] using ht epsilon'
  have hr : r₂ = -r₁ := eq_neg_of_add_eq_zero_right hcusp
  rw [map_neg, he] at hthree
  rw [hr, smul_neg, he'] at hfour
  have h34 : (3 : ℕ) • r₁ = (4 : ℕ) • r₁ := by
    rw [hthree, ← hfour, neg_neg]
  have hr₁ : r₁ = 0 := by
    have h := congrArg (fun z ↦ z - (3 : ℕ) • r₁) h34
    simpa only [show 4 = 3 + 1 from rfl, add_nsmul, one_nsmul,
      sub_self, add_sub_cancel_left] using h.symm
  have ht0 : t (e 0) = 0 := by simpa [hr₁] using hfour.symm
  exact ⟨fun a ↦ by rw [ht, ht0, zsmul_zero], hr₁, by rw [hr, hr₁, neg_zero]⟩

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.AnalyticData
open Hurewicz.Chains

public def ellipticInteriorInclusion (A : AnalyticData) : C(A.ellipticInterior, A.VanKampenSpace) :=
  ⟨Subtype.val, continuous_subtype_val⟩

public theorem coreToStar_hurewicz_via_interior (A : AnalyticData)
    (g : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) :
    hurewiczFunction A.vanKampenBase (A.actualVanKampenFourPieceCover.coreFundamentalGroupMap g) =
      integralSingularHomologyMap 1 (ellipticInteriorInclusion A)
        (hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne g)) := by
  rw [← hurewiczFunction_map]
  congr 1
  exact (CoveringSpace.map_map A.actualCoreToEllipticInterior
    (ellipticInteriorInclusion A) _ g).symm


public noncomputable def starHurewiczCoreHom (A : AnalyticData) :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ →*
      Multiplicative (IntegralSingularHomology 1 A.VanKampenSpace) :=
  (hurewiczPi1 A.vanKampenBase).comp A.actualVanKampenFourPieceCover.coreFundamentalGroupMap

public theorem starHurewiczCoreHom_central (A : AnalyticData)
    (g : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    (integralSingularHomologyMap 1 (ellipticInteriorInclusion A)).toMultiplicative
        (A.centralToInteriorAbelian g) =
      starHurewiczCoreHom A (A.cuspCentralNaturality.centralToCore g) := by
  apply Multiplicative.toAdd.injective
  exact (congrArg (integralSingularHomologyMap 1 (ellipticInteriorInclusion A))
    (A.geometricMarkedCentralToCoreEquiv_hurewicz g).symm).trans
      (A.coreToStar_hurewicz_via_interior (A.cuspCentralNaturality.centralToCore g)).symm

public theorem starHurewiczCoreHom_orderThree (A : AnalyticData) :
    starHurewiczCoreHom A (A.coreDataOf A.cuspCentralNaturality).rhoOne ^ 3 =
      starHurewiczCoreHom A
        (Additive.toMul ((A.coreDataOf A.cuspCentralNaturality).translation (-epsilon))) := by
  have h := congrArg
    (integralSingularHomologyMap 1 (ellipticInteriorInclusion A)).toMultiplicative
    A.centralToInteriorAbelian_orderThree
  rw [map_pow, A.starHurewiczCoreHom_central, A.starHurewiczCoreHom_central] at h
  exact h

public theorem starHurewiczCoreHom_orderFour (A : AnalyticData) :
    starHurewiczCoreHom A (A.coreDataOf A.cuspCentralNaturality).rhoTwo ^ 4 =
      starHurewiczCoreHom A
        (Additive.toMul ((A.coreDataOf A.cuspCentralNaturality).translation epsilon')) := by
  have h := congrArg
    (integralSingularHomologyMap 1 (ellipticInteriorInclusion A)).toMultiplicative
    A.centralToInteriorAbelian_orderFour
  rw [map_pow, A.starHurewiczCoreHom_central, A.starHurewiczCoreHom_central] at h
  exact h


public theorem star_homologyOne_subsingleton (A : AnalyticData) :
    Subsingleton (IntegralSingularHomology 1 A.VanKampenSpace) := by
  let _ := A.vanKampenCharts
  have _ : StronglyLocallyContractibleSpace A.VanKampenSpace := A.vanKampen_locallyNice
  have _ : PathConnectedSpace A.VanKampenSpace := A.vanKampen_pathConnected
  have _ : TauCeti.SemilocallySimplyConnectedSpace A.VanKampenSpace :=
    A.vanKampen_semilocallySimplyConnected
  let D := A.actualVanKampenFourPieceCover
  let N := A.cuspCentralNaturality
  let f := starHurewiczCoreHom A
  let k := (hurewiczPi1 A.vanKampenBase).comp D.cuspFundamentalGroupMap
  have hs := D.coreFundamentalGroupMap_surjective_of_overlap_surjective
    A.cuspOverlapFundamentalGroupMap_surjective
    A.ellipticThreeOverlapFundamentalGroupMap_surjective
    A.ellipticFourOverlapFundamentalGroupMap_surjective
  have hf : Function.Surjective f := (hurewiczPi1_surjective A.vanKampenBase).comp hs
  let C := (A.coreDataOf N).mapSurjective f hf
  have hsq (g) : f (A.cuspOverlapToCore g) = k (D.cuspOverlapFundamentalGroupMap g) :=
    congrArg (hurewiczPi1 A.vanKampenBase) (DFunLike.congr_fun A.cuspAffineBridge_cuspSquare g)
  have hcusp : C.rhoOne * C.rhoTwo = 1 := by
    have hm := A.cuspBridge_meridian_core N
    have hz : Additive.toMul ((A.coreDataOf N).translation 0) = 1 := by
      rw [map_zero]; rfl
    rw [hz, inv_one, mul_one] at hm
    change f (A.coreDataOf N).rhoOne * f (A.coreDataOf N).rhoTwo = 1
    calc
      _ = f ((A.coreDataOf N).rhoOne * (A.coreDataOf N).rhoTwo) := (map_mul f _ _).symm
      _ = f (A.cuspOverlapToCore A.cuspAffineBridgeMeridian) := congrArg f hm.symm
      _ = k (D.cuspOverlapFundamentalGroupMap A.cuspAffineBridgeMeridian) := hsq _
      _ = 1 := (congrArg k A.cuspAffineBridge_meridian_killed).trans (map_one k)
  have htoric (a : Lattice) (ha : a ∈ paperToricSubgroup) :
      Additive.toMul (C.translation a) = 1 := by
    change f (Additive.toMul ((A.coreDataOf N).translation a)) = 1
    calc
      _ = f (A.cuspOverlapToCore (Additive.toMul (A.cuspAffineBridgeTranslation a))) :=
        congrArg f (A.cuspBridge_translation_core N a).symm
      _ = k (D.cuspOverlapFundamentalGroupMap
          (Additive.toMul (A.cuspAffineBridgeTranslation a))) := hsq _
      _ = 1 := (congrArg k (A.cuspAffineBridge_toric_killed a ha)).trans (map_one k)
  have hmon (a : Lattice) : C.translation (paperMonodromyOne a) = C.translation a := by
    have h := congrArg Multiplicative.toAdd (C.conjugate_one a)
    simpa using h.symm
  have hthree : (3 : ℕ) • C.rhoOne.toAdd = C.translation (-epsilon) :=
    congrArg Multiplicative.toAdd (A.starHurewiczCoreHom_orderThree)
  have hfour : (4 : ℕ) • C.rhoTwo.toAdd = C.translation epsilon' :=
    congrArg Multiplicative.toAdd (A.starHurewiczCoreHom_orderFour)
  obtain ⟨ht, h1, h2⟩ := cuspElliptic_abelian_generators_eq_zero C.translation
    C.rhoOne.toAdd C.rhoTwo.toAdd hmon
    (fun a ha ↦ congrArg Multiplicative.toAdd (htoric a ha)) hthree hfour
    (congrArg Multiplicative.toAdd hcusp)
  have hg : Subgroup.closure
      (Set.range (fun a ↦ Additive.toMul (C.translation a)) ∪
        {C.rhoOne, C.rhoTwo}) ≤ ⊥ := by
    apply (Subgroup.closure_le _).mpr
    rintro z (⟨a, rfl⟩ | hz)
    · exact Subgroup.mem_bot.mpr (congrArg Additive.toMul (ht a))
    · rcases hz with rfl | rfl
      · exact Subgroup.mem_bot.mpr (Multiplicative.toAdd.injective h1)
      · exact Subgroup.mem_bot.mpr (Multiplicative.toAdd.injective h2)
  rw [C.generators_generate] at hg
  have hz (z : Multiplicative (IntegralSingularHomology 1 A.VanKampenSpace)) : z = 1 :=
    Subgroup.mem_bot.mp (hg trivial)
  exact ⟨fun x y ↦ Multiplicative.ofAdd.injective ((hz _).trans (hz _).symm)⟩

end SphereSixComplex.Geometry.AnalyticData
