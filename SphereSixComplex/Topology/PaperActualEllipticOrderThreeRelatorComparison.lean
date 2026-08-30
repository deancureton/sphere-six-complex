module

public import SphereSixComplex.Topology.PaperActualEllipticCanonicalFiniteMarking

/-!
# The order-three actual and central relators

The explicit radial filling identifies the chosen order-three boundary loops with the physical
deck loops.  This module packages their single filling relator in the actual affine core and
records the exact conjugacy statement sufficient for the normal-closure bridge.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Topology

/-- Conjugating a relator does not move it out of the normal closure it generates. -/
public theorem conjugate_mem_normalClosure_singleton
    {G : Type*} [Group G] (c r : G) :
    c * r * c⁻¹ ∈ Subgroup.normalClosure ({r} : Set G) := by
  exact (Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem r
    (Subgroup.subset_normalClosure (Set.mem_singleton r)) c

/-- Simultaneously conjugating the meridian and translation conjugates their affine relator. -/
public theorem affineRelator_eq_conjugate_of_simultaneous_conjugacy
    {G : Type*} [Group G] (c m t m' t' : G) (n : ℕ)
    (hm : m' = c * m * c⁻¹) (ht : t' = c * t * c⁻¹) :
    m' ^ n * t'⁻¹ = c * (m ^ n * t⁻¹) * c⁻¹ := by
  rw [hm, ht]
  change (MulAut.conj c m) ^ n * (MulAut.conj c t)⁻¹ =
    MulAut.conj c (m ^ n * t⁻¹)
  rw [map_mul, map_pow, map_inv]

/-- Simultaneous conjugacy of the marked generators gives the required one-sided
normal-closure membership of their affine relators. -/
public theorem affineRelator_mem_normalClosure_of_simultaneous_conjugacy
    {G : Type*} [Group G] (c m t m' t' : G) (n : ℕ)
    (hm : m' = c * m * c⁻¹) (ht : t' = c * t * c⁻¹) :
    m' ^ n * t'⁻¹ ∈ Subgroup.normalClosure ({m ^ n * t⁻¹} : Set G) := by
  rw [affineRelator_eq_conjugate_of_simultaneous_conjugacy c m t m' t' n hm ht]
  exact conjugate_mem_normalClosure_singleton c (m ^ n * t⁻¹)

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- The physical order-three filling relator after transporting the marked overlap loops into
the actual affine core. -/
public noncomputable def orderThreeActualPhysicalRelatorToCore :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  A.orderThreeActualEllipticPhysicalMeridianToCore ^ 3 *
    (Additive.toMul
      (A.orderThreeActualEllipticPhysicalTranslationToCore (-epsilon)))⁻¹

/-- The order-three affine relator in the central marking transported to the actual core. -/
public noncomputable def orderThreeCentralRelatorToCore
    (N : A.ActualCuspCentralNaturality) :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (N.centralToCore A.centralAffineCorePiOneData.rhoOne) ^ 3 *
    (Additive.toMul (A.actualCentralTranslationToCore N (-epsilon)))⁻¹

/-- The relator of the canonical chosen order-three cover maps to the physical core relator. -/
public theorem orderThreeActualCanonicalRelatorToCore_eq_physical :
    A.actualEllipticThreeOverlapToCore
        ((fundamentalGroupElementOfBaseEq
            A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
            A.orderThreeActualEllipticCanonicalChosenCover.meridian) ^ 3 *
          (Additive.toMul
            (fundamentalGroupAddHomOfBaseEq
              A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
              A.orderThreeActualEllipticCanonicalChosenCover.translation
              (-epsilon)))⁻¹) =
      A.orderThreeActualPhysicalRelatorToCore := by
  rw [map_mul, map_pow, map_inv,
    A.orderThreeActualEllipticCanonicalMeridianToCore_eq_physical]
  change A.orderThreeActualEllipticPhysicalMeridianToCore ^ 3 *
      (Additive.toMul
        (A.actualEllipticThreeTranslationToCore
          A.orderThreeActualEllipticCanonicalChosenCover
          A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
          (-epsilon)))⁻¹ = _
  rw [A.orderThreeActualEllipticCanonicalTranslationToCore_eq_physical]
  rfl

/-- A single relator conjugacy is sufficient for the order-three normal-closure bridge. -/
public theorem orderThreeCentralRelator_mem_normalClosure_of_conjugacy
    (N : A.ActualCuspCentralNaturality)
    (c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
    (h : A.orderThreeCentralRelatorToCore N =
      c * A.orderThreeActualPhysicalRelatorToCore * c⁻¹) :
    A.orderThreeCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.orderThreeActualPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  rw [h]
  exact conjugate_mem_normalClosure_singleton c A.orderThreeActualPhysicalRelatorToCore

/-- The exact remaining order-three geometric comparison: one connector carries both the
physical meridian and the physical `-epsilon` translation to the central marking. -/
public def OrderThreeCommonGaugeComparison
    (N : A.ActualCuspCentralNaturality) : Prop :=
  ∃ c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩,
    N.centralToCore A.centralAffineCorePiOneData.rhoOne =
        c * A.orderThreeActualEllipticPhysicalMeridianToCore * c⁻¹ ∧
      Additive.toMul (A.actualCentralTranslationToCore N (-epsilon)) =
        c * Additive.toMul
          (A.orderThreeActualEllipticPhysicalTranslationToCore (-epsilon)) * c⁻¹

/-- A common gauge/basepoint path for the physical meridian and translation implies the single
order-three normal-closure membership needed downstream. -/
public theorem orderThreeCentralRelator_mem_normalClosure_of_simultaneous_conjugacy
    (N : A.ActualCuspCentralNaturality)
    (c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
    (hmeridian : N.centralToCore A.centralAffineCorePiOneData.rhoOne =
      c * A.orderThreeActualEllipticPhysicalMeridianToCore * c⁻¹)
    (htranslation :
      Additive.toMul (A.actualCentralTranslationToCore N (-epsilon)) =
        c * Additive.toMul
          (A.orderThreeActualEllipticPhysicalTranslationToCore (-epsilon)) * c⁻¹) :
    A.orderThreeCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.orderThreeActualPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  exact affineRelator_mem_normalClosure_of_simultaneous_conjugacy c
    A.orderThreeActualEllipticPhysicalMeridianToCore
    (Additive.toMul (A.orderThreeActualEllipticPhysicalTranslationToCore (-epsilon)))
    (N.centralToCore A.centralAffineCorePiOneData.rhoOne)
    (Additive.toMul (A.actualCentralTranslationToCore N (-epsilon))) 3
    hmeridian htranslation

/-- Package the exact common-gauge residual as the required order-three normal-closure
membership. -/
public theorem OrderThreeCommonGaugeComparison.relator_mem_normalClosure
    {N : A.ActualCuspCentralNaturality} (H : A.OrderThreeCommonGaugeComparison N) :
    A.orderThreeCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.orderThreeActualPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  obtain ⟨c, hmeridian, htranslation⟩ := H
  exact A.orderThreeCentralRelator_mem_normalClosure_of_simultaneous_conjugacy N c
    hmeridian htranslation

end SphereSixComplex.Geometry.PaperAnalyticData

end
