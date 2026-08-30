module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeRelatorComparison

/-!
# The order-four actual and central relators

The explicit radial filling identifies the chosen order-four boundary loops with the physical
deck loops.  This module packages their single filling relator in the actual affine core and
reduces its normal-closure comparison to one common gauge/basepoint conjugacy.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- The physical order-four filling relator after transporting the marked overlap loops into
the actual affine core. -/
public noncomputable def orderFourActualPhysicalRelatorToCore :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  A.orderFourActualEllipticPhysicalMeridianToCore ^ 4 *
    (Additive.toMul
      (A.orderFourActualEllipticPhysicalTranslationToCore epsilon'))⁻¹

/-- The order-four affine relator in the central marking transported to the actual core. -/
public noncomputable def orderFourCentralRelatorToCore
    (N : A.ActualCuspCentralNaturality) :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (N.centralToCore A.centralAffineCorePiOneData.rhoTwo) ^ 4 *
    (Additive.toMul (A.actualCentralTranslationToCore N epsilon'))⁻¹

/-- The relator of the canonical chosen order-four cover maps to the physical core relator. -/
public theorem orderFourActualCanonicalRelatorToCore_eq_physical :
    A.actualEllipticFourOverlapToCore
        ((fundamentalGroupElementOfBaseEq
            A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
            A.orderFourActualEllipticCanonicalChosenCover.meridian) ^ 4 *
          (Additive.toMul
            (fundamentalGroupAddHomOfBaseEq
              A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
              A.orderFourActualEllipticCanonicalChosenCover.translation
              epsilon'))⁻¹) =
      A.orderFourActualPhysicalRelatorToCore := by
  rw [map_mul, map_pow, map_inv,
    A.orderFourActualEllipticCanonicalMeridianToCore_eq_physical]
  change A.orderFourActualEllipticPhysicalMeridianToCore ^ 4 *
      (Additive.toMul
        (A.actualEllipticFourTranslationToCore
          A.orderFourActualEllipticCanonicalChosenCover
          A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
          epsilon'))⁻¹ = _
  rw [A.orderFourActualEllipticCanonicalTranslationToCore_eq_physical]
  rfl

/-- A single relator conjugacy is sufficient for the order-four normal-closure bridge. -/
public theorem orderFourCentralRelator_mem_normalClosure_of_conjugacy
    (N : A.ActualCuspCentralNaturality)
    (c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
    (h : A.orderFourCentralRelatorToCore N =
      c * A.orderFourActualPhysicalRelatorToCore * c⁻¹) :
    A.orderFourCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.orderFourActualPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  rw [h]
  exact conjugate_mem_normalClosure_singleton c A.orderFourActualPhysicalRelatorToCore

/-- The exact remaining order-four geometric comparison: one connector carries both the
physical meridian and the physical `epsilon'` translation to the central marking. -/
public def OrderFourCommonGaugeComparison
    (N : A.ActualCuspCentralNaturality) : Prop :=
  ∃ c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩,
    N.centralToCore A.centralAffineCorePiOneData.rhoTwo =
        c * A.orderFourActualEllipticPhysicalMeridianToCore * c⁻¹ ∧
      Additive.toMul (A.actualCentralTranslationToCore N epsilon') =
        c * Additive.toMul
          (A.orderFourActualEllipticPhysicalTranslationToCore epsilon') * c⁻¹

/-- A common gauge/basepoint path for the physical meridian and translation implies the single
order-four normal-closure membership needed downstream. -/
public theorem orderFourCentralRelator_mem_normalClosure_of_simultaneous_conjugacy
    (N : A.ActualCuspCentralNaturality)
    (c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
    (hmeridian : N.centralToCore A.centralAffineCorePiOneData.rhoTwo =
      c * A.orderFourActualEllipticPhysicalMeridianToCore * c⁻¹)
    (htranslation : Additive.toMul (A.actualCentralTranslationToCore N epsilon') =
      c * Additive.toMul
        (A.orderFourActualEllipticPhysicalTranslationToCore epsilon') * c⁻¹) :
    A.orderFourCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.orderFourActualPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  exact affineRelator_mem_normalClosure_of_simultaneous_conjugacy c
    A.orderFourActualEllipticPhysicalMeridianToCore
    (Additive.toMul (A.orderFourActualEllipticPhysicalTranslationToCore epsilon'))
    (N.centralToCore A.centralAffineCorePiOneData.rhoTwo)
    (Additive.toMul (A.actualCentralTranslationToCore N epsilon')) 4
    hmeridian htranslation

/-- Package the exact common-gauge residual as the required order-four normal-closure
membership. -/
public theorem OrderFourCommonGaugeComparison.relator_mem_normalClosure
    {N : A.ActualCuspCentralNaturality} (H : A.OrderFourCommonGaugeComparison N) :
    A.orderFourCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.orderFourActualPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  rcases H with ⟨c, hmeridian, htranslation⟩
  exact A.orderFourCentralRelator_mem_normalClosure_of_simultaneous_conjugacy N c
    hmeridian htranslation

end SphereSixComplex.Geometry.PaperAnalyticData

end
