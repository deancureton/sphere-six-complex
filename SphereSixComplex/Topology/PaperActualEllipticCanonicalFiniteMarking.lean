module

public import SphereSixComplex.Topology.PaperActualEllipticMarkedRadialFillingExtension

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain

variable (A : PaperAnalyticData)

/-- The canonical chosen order-three filling cover produced by the explicit radial action and
lift. -/
public noncomputable def orderThreeActualEllipticCanonicalChosenCover :=
  A.orderThreeActualEllipticFillingMarkedDeckData.toExtensionAtBase.toFillingExtension.toChosenCover

/-- The canonical chosen order-four filling cover produced by the explicit radial action and
lift. -/
public noncomputable def orderFourActualEllipticCanonicalChosenCover :=
  A.orderFourActualEllipticFillingExtensionAtBase.toFillingExtension.toChosenCover

public theorem orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq :
    A.orderThreeActualEllipticCanonicalChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  A.orderThreeActualEllipticFillingMarkedDeckData.toExtensionAtBase.toFillingExtension
    |>.toChosenCover_boundaryBase_eq

public theorem orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq :
    A.orderFourActualEllipticCanonicalChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  A.orderFourActualEllipticFillingExtensionAtBase.toFillingExtension
    |>.toChosenCover_boundaryBase_eq

/-- The canonical order-three translation loop is exactly the loop attached to the physical
real-period deck translation. -/
public theorem orderThreeActualEllipticCanonicalChosenCover_translation_eq_ofDeck
    (a : Lattice) :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    let hp := A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
    fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        (Additive.toMul (A.orderThreeActualEllipticCanonicalChosenCover.translation a)) =
      fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        (ofDeck hp A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul (A.orderThreeActualEllipticBoundaryDeckData.translation a))) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let hp := A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
  let C := A.orderThreeActualEllipticCanonicalChosenCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : Additive.toMul (C.translation a) =
      ofDeck hp A.orderThreeActualEllipticBoundaryBase
        (Additive.toMul (A.orderThreeActualEllipticBoundaryDeckData.translation a)) := by
    apply (hp.fundamentalGroupEquiv
      ⟨A.orderThreeActualEllipticBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact C.fundamentalGroupData.translation_deck a
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq) hraw

/-- The canonical order-three meridian loop is exactly the loop attached to the physical inverse
mapping-torus meridian. -/
public theorem orderThreeActualEllipticCanonicalChosenCover_meridian_eq_ofDeck :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    let hp := A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
    fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        A.orderThreeActualEllipticCanonicalChosenCover.meridian =
      fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        (ofDeck hp A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let hp := A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
  let C := A.orderThreeActualEllipticCanonicalChosenCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : C.meridian = ofDeck hp A.orderThreeActualEllipticBoundaryBase
      A.orderThreeActualEllipticBoundaryDeckData.meridian := by
    apply (hp.fundamentalGroupEquiv
      ⟨A.orderThreeActualEllipticBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact C.fundamentalGroupData.meridian_deck
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq) hraw

/-- The canonical order-four translation loop is exactly the loop attached to the physical
real-period deck translation. -/
public theorem orderFourActualEllipticCanonicalChosenCover_translation_eq_ofDeck
    (a : Lattice) :
    letI := A.orderFourActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    let hp := A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
    fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        (Additive.toMul (A.orderFourActualEllipticCanonicalChosenCover.translation a)) =
      fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        (ofDeck hp A.orderFourActualEllipticBoundaryBase
          (Additive.toMul (A.orderFourActualEllipticBoundaryDeckData.translation a))) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let hp := A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
  let C := A.orderFourActualEllipticCanonicalChosenCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : Additive.toMul (C.translation a) =
      ofDeck hp A.orderFourActualEllipticBoundaryBase
        (Additive.toMul (A.orderFourActualEllipticBoundaryDeckData.translation a)) := by
    apply (hp.fundamentalGroupEquiv
      ⟨A.orderFourActualEllipticBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact C.fundamentalGroupData.translation_deck a
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq) hraw

/-- The canonical order-four meridian loop is exactly the loop attached to the physical inverse
mapping-torus meridian. -/
public theorem orderFourActualEllipticCanonicalChosenCover_meridian_eq_ofDeck :
    letI := A.orderFourActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    let hp := A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
    fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        A.orderFourActualEllipticCanonicalChosenCover.meridian =
      fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        (ofDeck hp A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.meridian) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let hp := A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
  let C := A.orderFourActualEllipticCanonicalChosenCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : C.meridian = ofDeck hp A.orderFourActualEllipticBoundaryBase
      A.orderFourActualEllipticBoundaryDeckData.meridian := by
    apply (hp.fundamentalGroupEquiv
      ⟨A.orderFourActualEllipticBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact C.fundamentalGroupData.meridian_deck
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq) hraw

/-- The physical order-three deck translation, transported from the marked overlap to the
central core. -/
public noncomputable def orderThreeActualEllipticPhysicalTranslationToCore
    (a : Lattice) :
    Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) := by
  letI := A.orderThreeActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  exact Additive.ofMul
    (A.actualEllipticThreeOverlapToCore
      (fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul (A.orderThreeActualEllipticBoundaryDeckData.translation a)))))

/-- The physical order-three inverse-meridian deck loop, transported to the central core. -/
public noncomputable def orderThreeActualEllipticPhysicalMeridianToCore :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ := by
  letI := A.orderThreeActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  exact A.actualEllipticThreeOverlapToCore
    (fundamentalGroupElementOfBaseEq
      A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
      (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase
        A.orderThreeActualEllipticBoundaryDeckData.meridian))

/-- The physical order-four deck translation, transported from the marked overlap to the
central core. -/
public noncomputable def orderFourActualEllipticPhysicalTranslationToCore
    (a : Lattice) :
    Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) := by
  letI := A.orderFourActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  exact Additive.ofMul
    (A.actualEllipticFourOverlapToCore
      (fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          (Additive.toMul (A.orderFourActualEllipticBoundaryDeckData.translation a)))))

/-- The physical order-four inverse-meridian deck loop, transported to the central core. -/
public noncomputable def orderFourActualEllipticPhysicalMeridianToCore :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ := by
  letI := A.orderFourActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  exact A.actualEllipticFourOverlapToCore
    (fundamentalGroupElementOfBaseEq
      A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
      (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase
        A.orderFourActualEllipticBoundaryDeckData.meridian))

public theorem orderThreeActualEllipticCanonicalTranslationToCore_eq_physical
    (a : Lattice) :
    A.actualEllipticThreeTranslationToCore
        A.orderThreeActualEllipticCanonicalChosenCover
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq a =
      A.orderThreeActualEllipticPhysicalTranslationToCore a := by
  simp only [actualEllipticThreeTranslationToCore, AddMonoidHom.comp_apply,
    MonoidHom.coe_toAdditive, Function.comp_apply, fundamentalGroupAddHomOfBaseEq_apply]
  rw [A.orderThreeActualEllipticCanonicalChosenCover_translation_eq_ofDeck a]
  simp only [toMul_ofMul]
  unfold orderThreeActualEllipticPhysicalTranslationToCore
  rfl

public theorem orderThreeActualEllipticCanonicalMeridianToCore_eq_physical :
    A.actualEllipticThreeOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
          A.orderThreeActualEllipticCanonicalChosenCover.meridian) =
      A.orderThreeActualEllipticPhysicalMeridianToCore := by
  rw [A.orderThreeActualEllipticCanonicalChosenCover_meridian_eq_ofDeck]
  rfl

public theorem orderFourActualEllipticCanonicalTranslationToCore_eq_physical
    (a : Lattice) :
    A.actualEllipticFourTranslationToCore
        A.orderFourActualEllipticCanonicalChosenCover
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq a =
      A.orderFourActualEllipticPhysicalTranslationToCore a := by
  simp only [actualEllipticFourTranslationToCore, AddMonoidHom.comp_apply,
    MonoidHom.coe_toAdditive, Function.comp_apply, fundamentalGroupAddHomOfBaseEq_apply]
  rw [A.orderFourActualEllipticCanonicalChosenCover_translation_eq_ofDeck a]
  simp only [toMul_ofMul]
  unfold orderFourActualEllipticPhysicalTranslationToCore
  rfl

public theorem orderFourActualEllipticCanonicalMeridianToCore_eq_physical :
    A.actualEllipticFourOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
          A.orderFourActualEllipticCanonicalChosenCover.meridian) =
      A.orderFourActualEllipticPhysicalMeridianToCore := by
  rw [A.orderFourActualEllipticCanonicalChosenCover_meridian_eq_ofDeck]
  rfl

/-- The seven finite marked-star comparisons after replacing chosen filling-cover loops by the
canonical physical deck loops. -/
public structure ActualEllipticCanonicalDeckLoopNaturality
    (N : A.ActualCuspCentralNaturality) where
  orderThreeTranslation_zero :
    A.orderThreeActualEllipticPhysicalTranslationToCore
        (integralBasisVector 0) =
      A.actualCentralTranslationToCore N (integralBasisVector 0)
  orderThreeTranslation_one :
    A.orderThreeActualEllipticPhysicalTranslationToCore
        (integralBasisVector 1) =
      A.actualCentralTranslationToCore N (integralBasisVector 1)
  orderThreeTranslation_three :
    A.orderThreeActualEllipticPhysicalTranslationToCore
        (integralBasisVector 3) =
      A.actualCentralTranslationToCore N (integralBasisVector 3)
  orderThreeMeridian_naturality :
    A.orderThreeActualEllipticPhysicalMeridianToCore =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne
  orderFourTranslation_zero :
    A.orderFourActualEllipticPhysicalTranslationToCore
        (integralBasisVector 0) =
      A.actualCentralTranslationToCore N (integralBasisVector 0)
  orderFourTranslation_one :
    A.orderFourActualEllipticPhysicalTranslationToCore
        (integralBasisVector 1) =
      A.actualCentralTranslationToCore N (integralBasisVector 1)
  orderFourMeridian_naturality :
    A.orderFourActualEllipticPhysicalMeridianToCore =
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo

namespace ActualEllipticCanonicalDeckLoopNaturality

variable {A} {N : A.ActualCuspCentralNaturality}

/-- Assemble the former residual from the explicit radial filling extensions and the seven
physical deck-loop comparisons. -/
public noncomputable def toMarkedFillingExtensionAtBaseResidual
    (E : ActualEllipticCanonicalDeckLoopNaturality A N) :
    ActualEllipticMarkedFillingExtensionAtBaseResidual A N where
  orderThreeData := A.orderThreeActualEllipticFillingMarkedDeckData
  orderThreeTranslation_zero :=
    (A.orderThreeActualEllipticCanonicalTranslationToCore_eq_physical
      (integralBasisVector 0)).trans E.orderThreeTranslation_zero
  orderThreeTranslation_one :=
    (A.orderThreeActualEllipticCanonicalTranslationToCore_eq_physical
      (integralBasisVector 1)).trans E.orderThreeTranslation_one
  orderThreeTranslation_three :=
    (A.orderThreeActualEllipticCanonicalTranslationToCore_eq_physical
      (integralBasisVector 3)).trans E.orderThreeTranslation_three
  orderThreeMeridian_naturality :=
    A.orderThreeActualEllipticCanonicalMeridianToCore_eq_physical.trans
      E.orderThreeMeridian_naturality
  orderFourExtension := A.orderFourActualEllipticFillingExtensionAtBase
  orderFourTranslation_zero :=
    (A.orderFourActualEllipticCanonicalTranslationToCore_eq_physical
      (integralBasisVector 0)).trans E.orderFourTranslation_zero
  orderFourTranslation_one :=
    (A.orderFourActualEllipticCanonicalTranslationToCore_eq_physical
      (integralBasisVector 1)).trans E.orderFourTranslation_one
  orderFourMeridian_naturality :=
    A.orderFourActualEllipticCanonicalMeridianToCore_eq_physical.trans
      E.orderFourMeridian_naturality

end ActualEllipticCanonicalDeckLoopNaturality

end SphereSixComplex.Geometry.PaperAnalyticData
