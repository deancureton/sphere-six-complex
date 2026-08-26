module

public import SphereSixComplex.Geometry.PaperAnalyticFillingPieces

/-!
# Elliptic filling loop powers

The explicit angular-affine paths on the two punctured Cayley covers project to loops in the
finite elliptic filling quotients.  This file identifies their third and fourth powers with
successive lifted paths and then contracts the angular parts through the filled discs, leaving
the exact `epsilon` and `-epsilon'` period loops.
-/

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup

noncomputable section

variable (A : PaperAnalyticData)

/-- On the punctured order-three cover, the full filling-cover map intertwines the explicit
affine lift with the finite cyclic generator. -/
public theorem orderThreeFillingCoverMap_punctured_generator {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderThreeFillingAction r
    A.orderThreeFillingCoverMap r
        (complexDiscPuncturedCoverToBallCover
          (orderThreeAffinePuncturedCoverGenerator A p)) =
      cyclicGenerator 3 •
        A.orderThreeFillingCoverMap r (complexDiscPuncturedCoverToBallCover p) := by
  let _ := A.orderThreeFillingAction r
  let _ := restrictedMulAction
    (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  apply Subtype.ext
  change (A.orderThreePuncturedCoverMap r
      (orderThreeAffinePuncturedCoverGenerator A p)).1 =
    (cyclicGenerator 3 • A.orderThreePuncturedCoverMap r p).1
  exact congrArg Subtype.val (A.orderThreePuncturedCoverMap_generator p)

/-- The analogous intertwining identity for the order-four full filling cover. -/
public theorem orderFourFillingCoverMap_punctured_generator {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderFourFillingAction r
    A.orderFourFillingCoverMap r
        (complexDiscPuncturedCoverToBallCover
          (orderFourAffinePuncturedCoverGenerator A p)) =
      cyclicGenerator 4 •
        A.orderFourFillingCoverMap r (complexDiscPuncturedCoverToBallCover p) := by
  let _ := A.orderFourFillingAction r
  let _ := restrictedMulAction
    (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  apply Subtype.ext
  change (A.orderFourPuncturedCoverMap r
      (orderFourAffinePuncturedCoverGenerator A p)).1 =
    (cyclicGenerator 4 • A.orderFourPuncturedCoverMap r p).1
  exact congrArg Subtype.val (A.orderFourPuncturedCoverMap_generator p)

/-- Projection of the punctured order-three affine cover all the way to the finite filling
quotient. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverToFillingQuotient
    (r : ℝ) : let _ := A.orderThreeFillingAction r
    ComplexDiscPuncturedBall r × ComplexTwoSpace →
      OrbitQuotient (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3) := by
  let _ := A.orderThreeFillingAction r
  exact fun p => Quotient.mk _
    (A.orderThreeFillingCoverMap r (complexDiscPuncturedCoverToBallCover p))

public theorem orderThreeAffinePuncturedCoverToFillingQuotient_continuous (r : ℝ) :
    let _ := A.orderThreeFillingAction r
    Continuous (A.orderThreeAffinePuncturedCoverToFillingQuotient r) := by
  let _ := A.orderThreeFillingAction r
  exact continuous_quot_mk.comp ((A.orderThreeFillingCoverMap_continuous r).comp
    complexDiscPuncturedCoverToBallCover.continuous)

/-- The outer finite quotient makes one application of the explicit order-three cover generator
invisible. -/
public theorem orderThreeAffinePuncturedCoverToFillingQuotient_generator {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderThreeFillingAction r
    A.orderThreeAffinePuncturedCoverToFillingQuotient r
        (orderThreeAffinePuncturedCoverGenerator A p) =
      A.orderThreeAffinePuncturedCoverToFillingQuotient r p := by
  let _ := A.orderThreeFillingAction r
  apply Quotient.sound
  change MulAction.orbitRel (FiniteCyclic 3) (A.orderThreeFillingOpen r)
    (A.orderThreeFillingCoverMap r
      (complexDiscPuncturedCoverToBallCover
        (orderThreeAffinePuncturedCoverGenerator A p)))
    (A.orderThreeFillingCoverMap r (complexDiscPuncturedCoverToBallCover p))
  rw [A.orderThreeFillingCoverMap_punctured_generator p]
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨cyclicGenerator 3, rfl⟩

/-- The explicit one-step order-three angular-affine loop in the finite filling quotient. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverFillingLoop {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderThreeFillingAction r
    Path (A.orderThreeAffinePuncturedCoverToFillingQuotient r p)
      (A.orderThreeAffinePuncturedCoverToFillingQuotient r p) := by
  let _ := A.orderThreeFillingAction r
  exact projectedForwardLoop
    (orderThreeAffinePuncturedCoverGenerator A)
    (A.orderThreeAffinePuncturedCoverToFillingQuotient r)
    (A.orderThreeAffinePuncturedCoverToFillingQuotient_generator (r := r))
    (orderThreeAffinePuncturedCoverLiftPath A p)
    (A.orderThreeAffinePuncturedCoverToFillingQuotient_continuous r)

/-- The successive-image lift represents the cube of the explicit order-three filling loop. -/
public theorem orderThreeAffinePuncturedCoverFillingLoop_pow_three {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderThreeFillingAction r
    pathLoopClass
        (projectedIteratedMappedLoop
          (orderThreeAffinePuncturedCoverGenerator A)
          A.orderThreeAffinePuncturedCoverGenerator_continuous
          (A.orderThreeAffinePuncturedCoverToFillingQuotient r)
          (A.orderThreeAffinePuncturedCoverToFillingQuotient_generator (r := r))
          (orderThreeAffinePuncturedCoverLiftPath A p)
          (A.orderThreeAffinePuncturedCoverToFillingQuotient_continuous r) 3) =
      pathLoopClass (A.orderThreeAffinePuncturedCoverFillingLoop p) ^ 3 := by
  let _ := A.orderThreeFillingAction r
  exact pathLoopClass_projectedIteratedMappedLoop_eq_pow _ _ _ _ _ _ 3

/-- The actual successive-image lift of the order-three one-step path. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverMappedLiftPathThree {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path p ((orderThreeAffinePuncturedCoverGenerator A)^[3] p) :=
  iteratedMappedPath (orderThreeAffinePuncturedCoverGenerator A)
    A.orderThreeAffinePuncturedCoverGenerator_continuous
    (orderThreeAffinePuncturedCoverLiftPath A p) 3

/-- Include the actual order-three power lift in the full disc cover and display its exact
period endpoint. -/
@[expose] public noncomputable def
    orderThreeAffinePuncturedCoverMappedLiftPathThreeToFull {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path (complexDiscPuncturedCoverToBallCover p)
      (complexDiscPuncturedCoverToBallCover
        (orderThreeAffinePuncturedCoverPeriodTranslate A p)) :=
  ((A.orderThreeAffinePuncturedCoverMappedLiftPathThree p).map
    complexDiscPuncturedCoverToBallCover.continuous).cast rfl
      (congrArg complexDiscPuncturedCoverToBallCover
        (orderThreeAffinePuncturedCoverGenerator_iterate_three A p)).symm

/-- Contractibility of the full filling cover changes the actual successive-image power lift to
the straight `epsilon` period path relative to its endpoints. -/
public theorem orderThreeAffinePuncturedCoverMappedLiftPathThree_homotopic_periodPath
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path.Homotopic
      (A.orderThreeAffinePuncturedCoverMappedLiftPathThreeToFull p)
      (orderThreeFullCoverPeriodPath A p) := by
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  exact SimplyConnectedSpace.paths_homotopic _ _

/-- Projection of the full order-three disc cover to the finite filling quotient. -/
@[expose] public noncomputable def orderThreeFullCoverToFillingQuotient (r : ℝ) :
    let _ := A.orderThreeFillingAction r
    ComplexDiscBall r × ComplexTwoSpace →
      OrbitQuotient (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3) := by
  let _ := A.orderThreeFillingAction r
  exact fun p => Quotient.mk _ (A.orderThreeFillingCoverMap r p)

public theorem orderThreeFullCoverToFillingQuotient_continuous (r : ℝ) :
    let _ := A.orderThreeFillingAction r
    Continuous (A.orderThreeFullCoverToFillingQuotient r) := by
  let _ := A.orderThreeFillingAction r
  exact continuous_quot_mk.comp (A.orderThreeFillingCoverMap_continuous r)

public theorem orderThreeFullCoverToFillingQuotient_punctured {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderThreeFillingAction r
    A.orderThreeFullCoverToFillingQuotient r
        (complexDiscPuncturedCoverToBallCover p) =
      A.orderThreeAffinePuncturedCoverToFillingQuotient r p := by
  let _ := A.orderThreeFillingAction r
  rfl

/-- The exact order-three period endpoint projects back to the initial filling-quotient point. -/
public theorem orderThreeAffinePuncturedCoverPeriod_fillingQuotient_eq {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderThreeFillingAction r
    A.orderThreeFullCoverToFillingQuotient r
        (complexDiscPuncturedCoverToBallCover
          (orderThreeAffinePuncturedCoverPeriodTranslate A p)) =
      A.orderThreeAffinePuncturedCoverToFillingQuotient r p := by
  let _ := A.orderThreeFillingAction r
  rw [A.orderThreeFullCoverToFillingQuotient_punctured]
  rw [← orderThreeAffinePuncturedCoverGenerator_iterate_three A p]
  exact map_iterate_eq_of_map_comp_eq
    (orderThreeAffinePuncturedCoverGenerator A)
    (A.orderThreeAffinePuncturedCoverToFillingQuotient r)
    (A.orderThreeAffinePuncturedCoverToFillingQuotient_generator (r := r)) 3 p

/-- The straight `epsilon` period loop in the actual finite order-three filling quotient. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverFillingPeriodLoop {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderThreeFillingAction r
    Path (A.orderThreeAffinePuncturedCoverToFillingQuotient r p)
      (A.orderThreeAffinePuncturedCoverToFillingQuotient r p) := by
  let _ := A.orderThreeFillingAction r
  exact ((orderThreeFullCoverPeriodPath A p).map
    (A.orderThreeFullCoverToFillingQuotient_continuous r)).cast
      (A.orderThreeFullCoverToFillingQuotient_punctured p).symm
      (A.orderThreeAffinePuncturedCoverPeriod_fillingQuotient_eq p).symm

/-- The path representing the cube of the order-three affine filling loop is homotopic in the
actual finite filling quotient to the straight `epsilon` period loop. -/
public theorem orderThreeAffinePuncturedCoverFillingPowerLoop_homotopic_periodLoop
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderThreeFillingAction r
    Path.Homotopic
      (projectedIteratedMappedLoop
        (orderThreeAffinePuncturedCoverGenerator A)
        A.orderThreeAffinePuncturedCoverGenerator_continuous
        (A.orderThreeAffinePuncturedCoverToFillingQuotient r)
        (A.orderThreeAffinePuncturedCoverToFillingQuotient_generator (r := r))
        (orderThreeAffinePuncturedCoverLiftPath A p)
        (A.orderThreeAffinePuncturedCoverToFillingQuotient_continuous r) 3)
      (A.orderThreeAffinePuncturedCoverFillingPeriodLoop p) := by
  let _ := A.orderThreeFillingAction r
  let qfull : C(ComplexDiscBall r × ComplexTwoSpace,
      OrbitQuotient (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3)) :=
    ⟨A.orderThreeFullCoverToFillingQuotient r,
      A.orderThreeFullCoverToFillingQuotient_continuous r⟩
  have h := (A.orderThreeAffinePuncturedCoverMappedLiftPathThree_homotopic_periodPath
    hr hr1 p).map qfull
  have hcast := h.pathCast
    (A.orderThreeFullCoverToFillingQuotient_punctured p).symm
    (A.orderThreeAffinePuncturedCoverPeriod_fillingQuotient_eq p).symm
  apply Path.Homotopic.trans ?_ hcast
  apply Path.Homotopic.refl

/-- Projection of the punctured order-four affine cover all the way to the finite filling
quotient. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverToFillingQuotient
    (r : ℝ) : let _ := A.orderFourFillingAction r
    ComplexDiscPuncturedBall r × ComplexTwoSpace →
      OrbitQuotient (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4) := by
  let _ := A.orderFourFillingAction r
  exact fun p => Quotient.mk _
    (A.orderFourFillingCoverMap r (complexDiscPuncturedCoverToBallCover p))

public theorem orderFourAffinePuncturedCoverToFillingQuotient_continuous (r : ℝ) :
    let _ := A.orderFourFillingAction r
    Continuous (A.orderFourAffinePuncturedCoverToFillingQuotient r) := by
  let _ := A.orderFourFillingAction r
  exact continuous_quot_mk.comp ((A.orderFourFillingCoverMap_continuous r).comp
    complexDiscPuncturedCoverToBallCover.continuous)

/-- The outer finite quotient makes one application of the explicit order-four cover generator
invisible. -/
public theorem orderFourAffinePuncturedCoverToFillingQuotient_generator {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderFourFillingAction r
    A.orderFourAffinePuncturedCoverToFillingQuotient r
        (orderFourAffinePuncturedCoverGenerator A p) =
      A.orderFourAffinePuncturedCoverToFillingQuotient r p := by
  let _ := A.orderFourFillingAction r
  apply Quotient.sound
  change MulAction.orbitRel (FiniteCyclic 4) (A.orderFourFillingOpen r)
    (A.orderFourFillingCoverMap r
      (complexDiscPuncturedCoverToBallCover
        (orderFourAffinePuncturedCoverGenerator A p)))
    (A.orderFourFillingCoverMap r (complexDiscPuncturedCoverToBallCover p))
  rw [A.orderFourFillingCoverMap_punctured_generator p]
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨cyclicGenerator 4, rfl⟩

/-- The explicit one-step order-four angular-affine loop in the finite filling quotient. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverFillingLoop {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderFourFillingAction r
    Path (A.orderFourAffinePuncturedCoverToFillingQuotient r p)
      (A.orderFourAffinePuncturedCoverToFillingQuotient r p) := by
  let _ := A.orderFourFillingAction r
  exact projectedForwardLoop
    (orderFourAffinePuncturedCoverGenerator A)
    (A.orderFourAffinePuncturedCoverToFillingQuotient r)
    (A.orderFourAffinePuncturedCoverToFillingQuotient_generator (r := r))
    (orderFourAffinePuncturedCoverLiftPath A p)
    (A.orderFourAffinePuncturedCoverToFillingQuotient_continuous r)

/-- The successive-image lift represents the fourth power of the explicit order-four loop. -/
public theorem orderFourAffinePuncturedCoverFillingLoop_pow_four {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderFourFillingAction r
    pathLoopClass
        (projectedIteratedMappedLoop
          (orderFourAffinePuncturedCoverGenerator A)
          A.orderFourAffinePuncturedCoverGenerator_continuous
          (A.orderFourAffinePuncturedCoverToFillingQuotient r)
          (A.orderFourAffinePuncturedCoverToFillingQuotient_generator (r := r))
          (orderFourAffinePuncturedCoverLiftPath A p)
          (A.orderFourAffinePuncturedCoverToFillingQuotient_continuous r) 4) =
      pathLoopClass (A.orderFourAffinePuncturedCoverFillingLoop p) ^ 4 := by
  let _ := A.orderFourFillingAction r
  exact pathLoopClass_projectedIteratedMappedLoop_eq_pow _ _ _ _ _ _ 4

/-- The actual successive-image lift of the order-four one-step path. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverMappedLiftPathFour {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path p ((orderFourAffinePuncturedCoverGenerator A)^[4] p) :=
  iteratedMappedPath (orderFourAffinePuncturedCoverGenerator A)
    A.orderFourAffinePuncturedCoverGenerator_continuous
    (orderFourAffinePuncturedCoverLiftPath A p) 4

/-- Include the actual order-four power lift in the full disc cover and display its exact period
endpoint. -/
@[expose] public noncomputable def
    orderFourAffinePuncturedCoverMappedLiftPathFourToFull {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path (complexDiscPuncturedCoverToBallCover p)
      (complexDiscPuncturedCoverToBallCover
        (orderFourAffinePuncturedCoverPeriodTranslate A p)) :=
  ((A.orderFourAffinePuncturedCoverMappedLiftPathFour p).map
    complexDiscPuncturedCoverToBallCover.continuous).cast rfl
      (congrArg complexDiscPuncturedCoverToBallCover
        (orderFourAffinePuncturedCoverGenerator_iterate_four A p)).symm

/-- Contractibility changes the actual order-four power lift to the straight `-epsilon'` period
path relative to its endpoints. -/
public theorem orderFourAffinePuncturedCoverMappedLiftPathFour_homotopic_periodPath
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path.Homotopic
      (A.orderFourAffinePuncturedCoverMappedLiftPathFourToFull p)
      (orderFourFullCoverPeriodPath A p) := by
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  exact SimplyConnectedSpace.paths_homotopic _ _

/-- Projection of the full order-four disc cover to the finite filling quotient. -/
@[expose] public noncomputable def orderFourFullCoverToFillingQuotient (r : ℝ) :
    let _ := A.orderFourFillingAction r
    ComplexDiscBall r × ComplexTwoSpace →
      OrbitQuotient (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4) := by
  let _ := A.orderFourFillingAction r
  exact fun p => Quotient.mk _ (A.orderFourFillingCoverMap r p)

public theorem orderFourFullCoverToFillingQuotient_continuous (r : ℝ) :
    let _ := A.orderFourFillingAction r
    Continuous (A.orderFourFullCoverToFillingQuotient r) := by
  let _ := A.orderFourFillingAction r
  exact continuous_quot_mk.comp (A.orderFourFillingCoverMap_continuous r)

public theorem orderFourFullCoverToFillingQuotient_punctured {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderFourFillingAction r
    A.orderFourFullCoverToFillingQuotient r
        (complexDiscPuncturedCoverToBallCover p) =
      A.orderFourAffinePuncturedCoverToFillingQuotient r p := by
  let _ := A.orderFourFillingAction r
  rfl

/-- The exact order-four period endpoint projects back to the initial filling-quotient point. -/
public theorem orderFourAffinePuncturedCoverPeriod_fillingQuotient_eq {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderFourFillingAction r
    A.orderFourFullCoverToFillingQuotient r
        (complexDiscPuncturedCoverToBallCover
          (orderFourAffinePuncturedCoverPeriodTranslate A p)) =
      A.orderFourAffinePuncturedCoverToFillingQuotient r p := by
  let _ := A.orderFourFillingAction r
  rw [A.orderFourFullCoverToFillingQuotient_punctured]
  rw [← orderFourAffinePuncturedCoverGenerator_iterate_four A p]
  exact map_iterate_eq_of_map_comp_eq
    (orderFourAffinePuncturedCoverGenerator A)
    (A.orderFourAffinePuncturedCoverToFillingQuotient r)
    (A.orderFourAffinePuncturedCoverToFillingQuotient_generator (r := r)) 4 p

/-- The straight `-epsilon'` period loop in the actual finite order-four filling quotient. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverFillingPeriodLoop {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderFourFillingAction r
    Path (A.orderFourAffinePuncturedCoverToFillingQuotient r p)
      (A.orderFourAffinePuncturedCoverToFillingQuotient r p) := by
  let _ := A.orderFourFillingAction r
  exact ((orderFourFullCoverPeriodPath A p).map
    (A.orderFourFullCoverToFillingQuotient_continuous r)).cast
      (A.orderFourFullCoverToFillingQuotient_punctured p).symm
      (A.orderFourAffinePuncturedCoverPeriod_fillingQuotient_eq p).symm

/-- The path representing the fourth power of the order-four affine filling loop is homotopic in
the actual finite filling quotient to the straight `-epsilon'` period loop. -/
public theorem orderFourAffinePuncturedCoverFillingPowerLoop_homotopic_periodLoop
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := A.orderFourFillingAction r
    Path.Homotopic
      (projectedIteratedMappedLoop
        (orderFourAffinePuncturedCoverGenerator A)
        A.orderFourAffinePuncturedCoverGenerator_continuous
        (A.orderFourAffinePuncturedCoverToFillingQuotient r)
        (A.orderFourAffinePuncturedCoverToFillingQuotient_generator (r := r))
        (orderFourAffinePuncturedCoverLiftPath A p)
        (A.orderFourAffinePuncturedCoverToFillingQuotient_continuous r) 4)
      (A.orderFourAffinePuncturedCoverFillingPeriodLoop p) := by
  let _ := A.orderFourFillingAction r
  let qfull : C(ComplexDiscBall r × ComplexTwoSpace,
      OrbitQuotient (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4)) :=
    ⟨A.orderFourFullCoverToFillingQuotient r,
      A.orderFourFullCoverToFillingQuotient_continuous r⟩
  have h := (A.orderFourAffinePuncturedCoverMappedLiftPathFour_homotopic_periodPath
    hr hr1 p).map qfull
  have hcast := h.pathCast
    (A.orderFourFullCoverToFillingQuotient_punctured p).symm
    (A.orderFourAffinePuncturedCoverPeriod_fillingQuotient_eq p).symm
  apply Path.Homotopic.trans ?_ hcast
  apply Path.Homotopic.refl

/-! ## Independence of the chosen one-step lift -/

/-- Project any path from an order-three cover point to its affine-generator translate.  The
finite quotient closes the path to a loop just as it does for the straight angular-affine path. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverFillingLoopOfPath {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace)
    (P : Path p (orderThreeAffinePuncturedCoverGenerator A p)) :
    let _ := A.orderThreeFillingAction r
    Path (A.orderThreeAffinePuncturedCoverToFillingQuotient r p)
      (A.orderThreeAffinePuncturedCoverToFillingQuotient r p) := by
  let _ := A.orderThreeFillingAction r
  exact projectedForwardLoop
    (orderThreeAffinePuncturedCoverGenerator A)
    (A.orderThreeAffinePuncturedCoverToFillingQuotient r)
    (A.orderThreeAffinePuncturedCoverToFillingQuotient_generator (r := r))
    P
    (A.orderThreeAffinePuncturedCoverToFillingQuotient_continuous r)

/-- In the full contractible filling cover, every such one-step path is homotopic relative
endpoints to the explicit angular-affine path.  Hence both project to the same filling-meridian
class. -/
public theorem orderThreeAffinePuncturedCoverFillingLoopOfPath_class_eq
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace)
    (P : Path p (orderThreeAffinePuncturedCoverGenerator A p)) :
    let _ := A.orderThreeFillingAction r
    pathLoopClass (A.orderThreeAffinePuncturedCoverFillingLoopOfPath p P) =
      pathLoopClass (A.orderThreeAffinePuncturedCoverFillingLoop p) := by
  let _ := A.orderThreeFillingAction r
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  let inc : C(ComplexDiscPuncturedBall r × ComplexTwoSpace,
      ComplexDiscBall r × ComplexTwoSpace) :=
    complexDiscPuncturedCoverToBallCover
  let qfull : C(ComplexDiscBall r × ComplexTwoSpace,
      OrbitQuotient (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3)) :=
    ⟨A.orderThreeFullCoverToFillingQuotient r,
      A.orderThreeFullCoverToFillingQuotient_continuous r⟩
  have hfull : Path.Homotopic
      (P.map inc.continuous)
      ((orderThreeAffinePuncturedCoverLiftPath A p).map inc.continuous) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hmapped := hfull.map qfull
  have hcast := hmapped.pathCast rfl
    (A.orderThreeAffinePuncturedCoverToFillingQuotient_generator p).symm
  exact Path.Homotopic.Quotient.eq.mpr hcast

/-- The analogous loop obtained from an arbitrary order-four one-step lift. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverFillingLoopOfPath {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace)
    (P : Path p (orderFourAffinePuncturedCoverGenerator A p)) :
    let _ := A.orderFourFillingAction r
    Path (A.orderFourAffinePuncturedCoverToFillingQuotient r p)
      (A.orderFourAffinePuncturedCoverToFillingQuotient r p) := by
  let _ := A.orderFourFillingAction r
  exact projectedForwardLoop
    (orderFourAffinePuncturedCoverGenerator A)
    (A.orderFourAffinePuncturedCoverToFillingQuotient r)
    (A.orderFourAffinePuncturedCoverToFillingQuotient_generator (r := r))
    P
    (A.orderFourAffinePuncturedCoverToFillingQuotient_continuous r)

/-- Every order-four one-step lift likewise gives the same filling-meridian class as the explicit
angular-affine path. -/
public theorem orderFourAffinePuncturedCoverFillingLoopOfPath_class_eq
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace)
    (P : Path p (orderFourAffinePuncturedCoverGenerator A p)) :
    let _ := A.orderFourFillingAction r
    pathLoopClass (A.orderFourAffinePuncturedCoverFillingLoopOfPath p P) =
      pathLoopClass (A.orderFourAffinePuncturedCoverFillingLoop p) := by
  let _ := A.orderFourFillingAction r
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  let inc : C(ComplexDiscPuncturedBall r × ComplexTwoSpace,
      ComplexDiscBall r × ComplexTwoSpace) :=
    complexDiscPuncturedCoverToBallCover
  let qfull : C(ComplexDiscBall r × ComplexTwoSpace,
      OrbitQuotient (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4)) :=
    ⟨A.orderFourFullCoverToFillingQuotient r,
      A.orderFourFullCoverToFillingQuotient_continuous r⟩
  have hfull : Path.Homotopic
      (P.map inc.continuous)
      ((orderFourAffinePuncturedCoverLiftPath A p).map inc.continuous) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hmapped := hfull.map qfull
  have hcast := hmapped.pathCast rfl
    (A.orderFourAffinePuncturedCoverToFillingQuotient_generator p).symm
  exact Path.Homotopic.Quotient.eq.mpr hcast

end

end SphereSixComplex.Geometry.PaperAnalyticData
