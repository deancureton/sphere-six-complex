module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticMarkedRadialFillingExtension

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
public noncomputable def ellipticThreeCanonicalChosenCover :=
  A.ellipticThreeFillingMarkedDeckData.toExtensionAtBase.toFillingExtension.toChosenCover

/-- The canonical chosen order-four filling cover produced by the explicit radial action and
lift. -/
public noncomputable def ellipticFourCanonicalChosenCover :=
  A.ellipticFourFillingExtensionAtBase.toFillingExtension.toChosenCover

public theorem ellipticThreeCanonicalChosenCover_boundaryBase_eq :
    A.ellipticThreeCanonicalChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  A.ellipticThreeFillingMarkedDeckData.toExtensionAtBase.toFillingExtension
    |>.toChosenCover_boundaryBase_eq

public theorem ellipticFourCanonicalChosenCover_boundaryBase_eq :
    A.ellipticFourCanonicalChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  A.ellipticFourFillingExtensionAtBase.toFillingExtension
    |>.toChosenCover_boundaryBase_eq

/-- The canonical order-three translation loop is exactly the loop attached to the physical
real-period deck translation. -/
public theorem ellipticThreeCanonicalChosenCover_translation_eq_ofDeck
    (a : Lattice) :
    letI := A.ellipticThreeBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticThreeBoundaryCover_simplyConnected
    let hp := A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
    fundamentalGroupElementOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        (Additive.toMul (A.ellipticThreeCanonicalChosenCover.translation a)) =
      fundamentalGroupElementOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        (ofDeck hp A.ellipticThreeBoundaryBase
          (Additive.toMul (A.ellipticThreeBoundaryDeckData.translation a))) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let hp := A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
  let C := A.ellipticThreeCanonicalChosenCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : Additive.toMul (C.translation a) =
      ofDeck hp A.ellipticThreeBoundaryBase
        (Additive.toMul (A.ellipticThreeBoundaryDeckData.translation a)) := by
    apply (hp.fundamentalGroupEquiv
      ⟨A.ellipticThreeBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact C.fundamentalGroupData.translation_deck a
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.ellipticThreeCanonicalChosenCover_boundaryBase_eq) hraw

/-- The canonical order-three meridian loop is exactly the loop attached to the physical inverse
mapping-torus meridian. -/
public theorem ellipticThreeCanonicalChosenCover_meridian_eq_ofDeck :
    letI := A.ellipticThreeBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticThreeBoundaryCover_simplyConnected
    let hp := A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
    fundamentalGroupElementOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        A.ellipticThreeCanonicalChosenCover.meridian =
      fundamentalGroupElementOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        (ofDeck hp A.ellipticThreeBoundaryBase
          A.ellipticThreeBoundaryDeckData.meridian) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let hp := A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
  let C := A.ellipticThreeCanonicalChosenCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : C.meridian = ofDeck hp A.ellipticThreeBoundaryBase
      A.ellipticThreeBoundaryDeckData.meridian := by
    apply (hp.fundamentalGroupEquiv
      ⟨A.ellipticThreeBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact C.fundamentalGroupData.meridian_deck
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.ellipticThreeCanonicalChosenCover_boundaryBase_eq) hraw

/-- The canonical order-four translation loop is exactly the loop attached to the physical
real-period deck translation. -/
public theorem ellipticFourCanonicalChosenCover_translation_eq_ofDeck
    (a : Lattice) :
    letI := A.ellipticFourBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    let hp := A.ellipticFourBoundaryProjection_isQuotientCoveringMap
    fundamentalGroupElementOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        (Additive.toMul (A.ellipticFourCanonicalChosenCover.translation a)) =
      fundamentalGroupElementOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        (ofDeck hp A.ellipticFourBoundaryBase
          (Additive.toMul (A.ellipticFourBoundaryDeckData.translation a))) := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let hp := A.ellipticFourBoundaryProjection_isQuotientCoveringMap
  let C := A.ellipticFourCanonicalChosenCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : Additive.toMul (C.translation a) =
      ofDeck hp A.ellipticFourBoundaryBase
        (Additive.toMul (A.ellipticFourBoundaryDeckData.translation a)) := by
    apply (hp.fundamentalGroupEquiv
      ⟨A.ellipticFourBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact C.fundamentalGroupData.translation_deck a
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.ellipticFourCanonicalChosenCover_boundaryBase_eq) hraw

/-- The canonical order-four meridian loop is exactly the loop attached to the physical inverse
mapping-torus meridian. -/
public theorem ellipticFourCanonicalChosenCover_meridian_eq_ofDeck :
    letI := A.ellipticFourBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    let hp := A.ellipticFourBoundaryProjection_isQuotientCoveringMap
    fundamentalGroupElementOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        A.ellipticFourCanonicalChosenCover.meridian =
      fundamentalGroupElementOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        (ofDeck hp A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.meridian) := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let hp := A.ellipticFourBoundaryProjection_isQuotientCoveringMap
  let C := A.ellipticFourCanonicalChosenCover
  let _ := C.boundaryDeckGroup
  let _ := C.fillingDeckGroup
  let _ := C.boundaryCoverTopology
  let _ := C.fillingCoverTopology
  let _ := C.boundaryAction
  let _ := C.fillingAction
  have hraw : C.meridian = ofDeck hp A.ellipticFourBoundaryBase
      A.ellipticFourBoundaryDeckData.meridian := by
    apply (hp.fundamentalGroupEquiv
      ⟨A.ellipticFourBoundaryBase, rfl⟩).injective
    rw [fundamentalGroupEquiv_ofDeck]
    exact C.fundamentalGroupData.meridian_deck
  exact congrArg
    (fundamentalGroupElementOfBaseEq
      A.ellipticFourCanonicalChosenCover_boundaryBase_eq) hraw

/-- The physical order-three deck translation, transported from the marked overlap to the
central core. -/
public noncomputable def ellipticThreePhysicalTranslationToCore
    (a : Lattice) :
    Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) := by
  letI := A.ellipticThreeBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  exact Additive.ofMul
    (A.ellipticThreeOverlapToCore
      (fundamentalGroupElementOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
          A.ellipticThreeBoundaryBase
          (Additive.toMul (A.ellipticThreeBoundaryDeckData.translation a)))))

/-- The physical order-three inverse-meridian deck loop, transported to the central core. -/
public noncomputable def ellipticThreePhysicalMeridianToCore :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ := by
  letI := A.ellipticThreeBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  exact A.ellipticThreeOverlapToCore
    (fundamentalGroupElementOfBaseEq
      A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
      (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
        A.ellipticThreeBoundaryBase
        A.ellipticThreeBoundaryDeckData.meridian))

/-- The physical order-four deck translation, transported from the marked overlap to the
central core. -/
public noncomputable def ellipticFourPhysicalTranslationToCore
    (a : Lattice) :
    Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) := by
  letI := A.ellipticFourBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  exact Additive.ofMul
    (A.ellipticFourOverlapToCore
      (fundamentalGroupElementOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          (Additive.toMul (A.ellipticFourBoundaryDeckData.translation a)))))

/-- The physical order-four inverse-meridian deck loop, transported to the central core. -/
public noncomputable def ellipticFourPhysicalMeridianToCore :
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ := by
  letI := A.ellipticFourBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  exact A.ellipticFourOverlapToCore
    (fundamentalGroupElementOfBaseEq
      A.ellipticFourCanonicalChosenCover_boundaryBase_eq
      (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase
        A.ellipticFourBoundaryDeckData.meridian))

public theorem ellipticThreeCanonicalTranslationToCore_eq_physical
    (a : Lattice) :
    A.ellipticThreeTranslationToCore
        A.ellipticThreeCanonicalChosenCover
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq a =
      A.ellipticThreePhysicalTranslationToCore a := by
  simp only [ellipticThreeTranslationToCore, AddMonoidHom.comp_apply,
    MonoidHom.coe_toAdditive, Function.comp_apply, fundamentalGroupAddHomOfBaseEq_apply]
  rw [A.ellipticThreeCanonicalChosenCover_translation_eq_ofDeck a]
  simp only [toMul_ofMul]
  unfold ellipticThreePhysicalTranslationToCore
  rfl

public theorem ellipticThreeCanonicalMeridianToCore_eq_physical :
    A.ellipticThreeOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
          A.ellipticThreeCanonicalChosenCover.meridian) =
      A.ellipticThreePhysicalMeridianToCore := by
  rw [A.ellipticThreeCanonicalChosenCover_meridian_eq_ofDeck]
  rfl

public theorem ellipticFourCanonicalTranslationToCore_eq_physical
    (a : Lattice) :
    A.ellipticFourTranslationToCore
        A.ellipticFourCanonicalChosenCover
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq a =
      A.ellipticFourPhysicalTranslationToCore a := by
  simp only [ellipticFourTranslationToCore, AddMonoidHom.comp_apply,
    MonoidHom.coe_toAdditive, Function.comp_apply, fundamentalGroupAddHomOfBaseEq_apply]
  rw [A.ellipticFourCanonicalChosenCover_translation_eq_ofDeck a]
  simp only [toMul_ofMul]
  unfold ellipticFourPhysicalTranslationToCore
  rfl

public theorem ellipticFourCanonicalMeridianToCore_eq_physical :
    A.ellipticFourOverlapToCore
        (fundamentalGroupElementOfBaseEq
          A.ellipticFourCanonicalChosenCover_boundaryBase_eq
          A.ellipticFourCanonicalChosenCover.meridian) =
      A.ellipticFourPhysicalMeridianToCore := by
  rw [A.ellipticFourCanonicalChosenCover_meridian_eq_ofDeck]
  rfl

/-- The seven finite marked-star comparisons after replacing chosen filling-cover loops by the
canonical physical deck loops. -/
public structure EllipticCanonicalDeckLoopNaturality
    (N : A.CuspCentralNaturality) where
  orderThreeTranslation_zero :
    A.ellipticThreePhysicalTranslationToCore
        (integralBasisVector 0) =
      A.actualCentralTranslationToCore N (integralBasisVector 0)
  orderThreeTranslation_one :
    A.ellipticThreePhysicalTranslationToCore
        (integralBasisVector 1) =
      A.actualCentralTranslationToCore N (integralBasisVector 1)
  orderThreeTranslation_three :
    A.ellipticThreePhysicalTranslationToCore
        (integralBasisVector 3) =
      A.actualCentralTranslationToCore N (integralBasisVector 3)
  orderThreeMeridian_naturality :
    A.ellipticThreePhysicalMeridianToCore =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne
  orderFourTranslation_zero :
    A.ellipticFourPhysicalTranslationToCore
        (integralBasisVector 0) =
      A.actualCentralTranslationToCore N (integralBasisVector 0)
  orderFourTranslation_one :
    A.ellipticFourPhysicalTranslationToCore
        (integralBasisVector 1) =
      A.actualCentralTranslationToCore N (integralBasisVector 1)
  orderFourMeridian_naturality :
    A.ellipticFourPhysicalMeridianToCore =
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo

namespace EllipticCanonicalDeckLoopNaturality

variable {A} {N : A.CuspCentralNaturality}

/-- Assemble the former residual from the explicit radial filling extensions and the seven
physical deck-loop comparisons. -/
public noncomputable def toMarkedFillingExtensionAtBaseResidual
    (E : EllipticCanonicalDeckLoopNaturality A N) :
    EllipticMarkedFillingExtensionAtBaseResidual A N where
  orderThreeData := A.ellipticThreeFillingMarkedDeckData
  orderThreeTranslation_zero :=
    (A.ellipticThreeCanonicalTranslationToCore_eq_physical
      (integralBasisVector 0)).trans E.orderThreeTranslation_zero
  orderThreeTranslation_one :=
    (A.ellipticThreeCanonicalTranslationToCore_eq_physical
      (integralBasisVector 1)).trans E.orderThreeTranslation_one
  orderThreeTranslation_three :=
    (A.ellipticThreeCanonicalTranslationToCore_eq_physical
      (integralBasisVector 3)).trans E.orderThreeTranslation_three
  orderThreeMeridian_naturality :=
    A.ellipticThreeCanonicalMeridianToCore_eq_physical.trans
      E.orderThreeMeridian_naturality
  orderFourExtension := A.ellipticFourFillingExtensionAtBase
  orderFourTranslation_zero :=
    (A.ellipticFourCanonicalTranslationToCore_eq_physical
      (integralBasisVector 0)).trans E.orderFourTranslation_zero
  orderFourTranslation_one :=
    (A.ellipticFourCanonicalTranslationToCore_eq_physical
      (integralBasisVector 1)).trans E.orderFourTranslation_one
  orderFourMeridian_naturality :=
    A.ellipticFourCanonicalMeridianToCore_eq_physical.trans
      E.orderFourMeridian_naturality

end EllipticCanonicalDeckLoopNaturality

end SphereSixComplex.Geometry.PaperAnalyticData
