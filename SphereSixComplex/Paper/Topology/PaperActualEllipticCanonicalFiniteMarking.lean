module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticMarkedRadialFillingExtension

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain

variable (A : AnalyticData)

/-- The canonical chosen order-three filling cover produced by the explicit radial action and
lift. -/
public noncomputable def ellipticThreeCanonicalChosenCover :=
  A.ellipticThreeFillingMarkedDeckData.toExtensionAtBase.toChosenCover

/-- The canonical chosen order-four filling cover produced by the explicit radial action and
lift. -/
public noncomputable def ellipticFourCanonicalChosenCover :=
  A.ellipticFourFillingExtensionAtBase.toChosenCover

public theorem ellipticThreeCanonicalChosenCover_boundaryBase_eq :
    A.ellipticThreeCanonicalChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  A.ellipticThreeFillingMarkedDeckData.toExtensionAtBase
    |>.toChosenCover_boundaryBase_eq

public theorem ellipticFourCanonicalChosenCover_boundaryBase_eq :
    A.ellipticFourCanonicalChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  A.ellipticFourFillingExtensionAtBase
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










end SphereSixComplex.Geometry.AnalyticData
