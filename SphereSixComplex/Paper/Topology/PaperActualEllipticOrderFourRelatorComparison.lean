module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeRelatorComparison

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
public noncomputable def ellipticFourPhysicalRelatorToCore :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  A.ellipticFourPhysicalMeridianToCore ^ 4 *
    (Additive.toMul
      (A.ellipticFourPhysicalTranslationToCore epsilon'))⁻¹

/-- The order-four affine relator in the central marking transported to the actual core. -/
public noncomputable def orderFourCentralRelatorToCore
    (N : A.CuspCentralNaturality) :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (N.centralToCore A.centralAffineCorePiOneData.rhoTwo) ^ 4 *
    (Additive.toMul (A.actualCentralTranslationToCore N epsilon'))⁻¹

/-- The relator of the canonical chosen order-four cover maps to the physical core relator. -/
public theorem ellipticFourCanonicalRelatorToCore_eq_physical :
    A.ellipticFourOverlapToCore
        ((fundamentalGroupElementOfBaseEq
            A.ellipticFourCanonicalChosenCover_boundaryBase_eq
            A.ellipticFourCanonicalChosenCover.meridian) ^ 4 *
          (Additive.toMul
            (fundamentalGroupAddHomOfBaseEq
              A.ellipticFourCanonicalChosenCover_boundaryBase_eq
              A.ellipticFourCanonicalChosenCover.translation
              epsilon'))⁻¹) =
      A.ellipticFourPhysicalRelatorToCore := by
  rw [map_mul, map_pow, map_inv,
    A.ellipticFourCanonicalMeridianToCore_eq_physical]
  change A.ellipticFourPhysicalMeridianToCore ^ 4 *
      (Additive.toMul
        (A.ellipticFourTranslationToCore
          A.ellipticFourCanonicalChosenCover
          A.ellipticFourCanonicalChosenCover_boundaryBase_eq
          epsilon'))⁻¹ = _
  rw [A.ellipticFourCanonicalTranslationToCore_eq_physical]
  rfl

/-- A single relator conjugacy is sufficient for the order-four normal-closure bridge. -/
public theorem orderFourCentralRelator_mem_normalClosure_of_conjugacy
    (N : A.CuspCentralNaturality)
    (c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
    (h : A.orderFourCentralRelatorToCore N =
      c * A.ellipticFourPhysicalRelatorToCore * c⁻¹) :
    A.orderFourCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.ellipticFourPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  rw [h]
  exact conjugate_mem_normalClosure_singleton c A.ellipticFourPhysicalRelatorToCore

/-- The exact remaining order-four geometric comparison: one connector carries both the
physical meridian and the physical `epsilon'` translation to the central marking. -/
public def OrderFourCommonGaugeComparison
    (N : A.CuspCentralNaturality) : Prop :=
  ∃ c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩,
    N.centralToCore A.centralAffineCorePiOneData.rhoTwo =
        c * A.ellipticFourPhysicalMeridianToCore * c⁻¹ ∧
      Additive.toMul (A.actualCentralTranslationToCore N epsilon') =
        c * Additive.toMul
          (A.ellipticFourPhysicalTranslationToCore epsilon') * c⁻¹

/-- A common gauge/basepoint path for the physical meridian and translation implies the single
order-four normal-closure membership needed downstream. -/
public theorem orderFourCentralRelator_mem_normalClosure_of_simultaneous_conjugacy
    (N : A.CuspCentralNaturality)
    (c : FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
    (hmeridian : N.centralToCore A.centralAffineCorePiOneData.rhoTwo =
      c * A.ellipticFourPhysicalMeridianToCore * c⁻¹)
    (htranslation : Additive.toMul (A.actualCentralTranslationToCore N epsilon') =
      c * Additive.toMul
        (A.ellipticFourPhysicalTranslationToCore epsilon') * c⁻¹) :
    A.orderFourCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.ellipticFourPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  exact affineRelator_mem_normalClosure_of_simultaneous_conjugacy c
    A.ellipticFourPhysicalMeridianToCore
    (Additive.toMul (A.ellipticFourPhysicalTranslationToCore epsilon'))
    (N.centralToCore A.centralAffineCorePiOneData.rhoTwo)
    (Additive.toMul (A.actualCentralTranslationToCore N epsilon')) 4
    hmeridian htranslation

/-- Package the exact common-gauge residual as the required order-four normal-closure
membership. -/
public theorem OrderFourCommonGaugeComparison.relator_mem_normalClosure
    {N : A.CuspCentralNaturality} (H : A.OrderFourCommonGaugeComparison N) :
    A.orderFourCentralRelatorToCore N ∈
      Subgroup.normalClosure ({A.ellipticFourPhysicalRelatorToCore} :
        Set (FundamentalGroup A.actualVanKampenFourPieceCover.core
          ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)) := by
  rcases H with ⟨c, hmeridian, htranslation⟩
  exact A.orderFourCentralRelator_mem_normalClosure_of_simultaneous_conjugacy N c
    hmeridian htranslation

end SphereSixComplex.Geometry.PaperAnalyticData

end
