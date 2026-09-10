module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeBaseFactorHomotopyProof
public import SphereSixComplex.Prerequisites.TriangleGroup.FreeProductCentralizers
import all SphereSixComplex.Paper.TriangleGroup.Representation

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.TriangleGroup

open LatticeData

public theorem rhoLambda_inl_epsilon (a : CyclicThree) :
    rhoLambda (Monoid.Coprod.inl a) epsilon = epsilon := by
  have ha : a = Multiplicative.ofAdd (1 : ZMod 3) ^ a.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp
  rw [ha, map_pow]
  change rhoLambda (g₁ ^ a.toAdd.val) epsilon = epsilon
  generalize a.toAdd.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul]
    change rhoLambda (g₁ ^ n) (rhoLambda g₁ epsilon) = epsilon
    rw [rhoLambda_g₁_apply, A₁_epsilon, ih]

public theorem rhoLambda_epsilon_eq_of_commute_g₁ (g : Delta) (h : Commute g g₁) :
    rhoLambda g epsilon = epsilon := by
  obtain ⟨a, rfl⟩ := eq_inl_of_commute_g₁ g h
  exact rhoLambda_inl_epsilon a

end SphereSixComplex.TriangleGroup

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- The first-power meridian determines the corrected twist label without choosing a unique
sheet inside the finite elliptic stabilizer. -/
public theorem orderThree_enteringSheet_inverse_transports_epsilon
    (g : Delta)
    (hmeridian : g⁻¹ * g₁ * g = A.geometricCentralClockwiseOneDeck) :
    rhoLambda g⁻¹ epsilon =
      rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon := by
  let q := (g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent
  have hconj : g⁻¹ * g₁ * g = q * g₁ * q⁻¹ :=
    hmeridian.trans A.geometricCentralClockwiseOneDeck_eq_cuspConjugate
  have hcomm : Commute (g * q) g₁ := by
    rw [commute_iff_eq]
    calc
      (g * q) * g₁ = g * (q * g₁ * q⁻¹) * q := by group
      _ = g * (g⁻¹ * g₁ * g) * q := by rw [hconj]
      _ = g₁ * (g * q) := by group
  apply (rhoLambda g).injective
  rw [map_inv]
  change (rhoLambda g) ((rhoLambda g).symm epsilon) = _
  rw [LinearEquiv.apply_symm_apply]
  simpa only [map_mul, LinearEquiv.mul_apply] using
    (rhoLambda_epsilon_eq_of_commute_g₁ (g * q) hcomm).symm

/-- The local fixed-base fibre loop after removing the constant collar offset. -/
public noncomputable def orderThreeCentralPrincipalGaugeFiberPath :
    letI := A.ellipticThreeBoundaryAction
    Path
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreeFillingRelationPrincipalGaugeLoop 0))
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreeFillingRelationPrincipalGaugeLoop 0)) := by
  let _ := A.ellipticThreeBoundaryAction
  exact ((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod
    A.orderThreeFillingRelationPrincipalGaugeLoop).map
      A.orderThreePuncturedProductToCentralMap.continuous

/-- Contracting the collar offset gives a free homotopy to the principal-gauge fibre loop. -/
public def orderThreeLocalOffsetFiberCentralPath_offsetHomotopy :
    letI := A.ellipticThreeBoundaryAction
    ContinuousMap.Homotopy A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
      A.orderThreeCentralPrincipalGaugeFiberPath.toContinuousMap := by
  let _ := A.ellipticThreeBoundaryAction
  let x := A.orderThreeCayleyPuncturedBasepoint
  let f := A.orderThreePuncturedProductToCentralMap
  let Hoffset := A.orderThreePrincipalGaugeOffsetHomotopy
  exact
    { toFun := fun st ↦ f (x, Hoffset st)
      continuous_toFun := f.continuous.comp
        (continuous_const.prodMk Hoffset.continuous)
      map_zero_left := by
        intro t
        change f (x, Hoffset (0, t)) = f (x, A.orderThreePrincipalGaugeWithOffsetPath t)
        exact congrArg (fun q ↦ f (x, q)) (Hoffset.map_zero_left t)
      map_one_left := by
        intro t
        change f (x, Hoffset (1, t)) =
          f (x, A.orderThreeFillingRelationPrincipalGaugeLoop t)
        exact congrArg (fun q ↦ f (x, q)) (Hoffset.map_one_left t) }

public theorem orderThreeLocalOffsetFiberCentralPath_offsetHomotopy_trace
    (s : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    let H := A.orderThreeLocalOffsetFiberCentralPath_offsetHomotopy
    H (s, 0) = H (s, 1) := by
  let _ := A.ellipticThreeBoundaryAction
  change A.orderThreePuncturedProductToCentralMap
      (A.orderThreeCayleyPuncturedBasepoint,
        A.orderThreePrincipalGaugeOffsetHomotopy (s, 0)) =
    A.orderThreePuncturedProductToCentralMap
      (A.orderThreeCayleyPuncturedBasepoint,
        A.orderThreePrincipalGaugeOffsetHomotopy (s, 1))
  apply congrArg (fun q ↦ A.orderThreePuncturedProductToCentralMap
    (A.orderThreeCayleyPuncturedBasepoint, q))
  change A.orderThreeFillingRelationPrincipalGaugeLoop 0 + _ =
    A.orderThreeFillingRelationPrincipalGaugeLoop 1 + _
  rw [A.orderThreeFillingRelationPrincipalGaugeLoop.source,
    A.orderThreeFillingRelationPrincipalGaugeLoop.target]

/-- The fixed-base local realization of the classified straight period segment. -/
public noncomputable def orderThreeCentralPrincipalGaugeStraightFiberPath :
    letI := A.ellipticThreeBoundaryAction
    Path
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreeFillingRelationPrincipalGaugeLoop 0))
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreeFillingRelationPrincipalGaugeLoop 0)) := by
  let _ := A.ellipticThreeBoundaryAction
  let q := A.orderThreePrincipalGaugeStraightLoop
  have hbase :
      torusProjection
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1
          (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) =
        A.orderThreeFillingRelationPrincipalGaugeLoop 0 := by
    rfl
  exact (((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod q).map
    A.orderThreePuncturedProductToCentralMap.continuous).cast
      (congrArg
        (fun z ↦ A.orderThreePuncturedProductToCentralMap
          (A.orderThreeCayleyPuncturedBasepoint, z)) hbase)
      (congrArg
        (fun z ↦ A.orderThreePuncturedProductToCentralMap
          (A.orderThreeCayleyPuncturedBasepoint, z)) hbase)

public theorem orderThreeCentralPrincipalGaugeFiberPath_homotopic_straight :
    letI := A.ellipticThreeBoundaryAction
    Nonempty (Path.Homotopy A.orderThreeCentralPrincipalGaugeFiberPath
      A.orderThreeCentralPrincipalGaugeStraightFiberPath) := by
  let _ := A.ellipticThreeBoundaryAction
  have hclass := A.orderThreeFillingRelationPrincipalGaugeLoop_class_eq_straight
  change Path.Homotopic.Quotient.mk A.orderThreeFillingRelationPrincipalGaugeLoop =
    Path.Homotopic.Quotient.mk A.orderThreePrincipalGaugeStraightLoop at hclass
  have htorus : Path.Homotopic A.orderThreeFillingRelationPrincipalGaugeLoop
      A.orderThreePrincipalGaugeStraightLoop := Quotient.exact hclass
  rcases htorus with ⟨Htorus⟩
  let f : C(A.OrderThreeTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint, q)
      continuous_toFun := A.orderThreePuncturedProductToCentralMap.continuous.comp
        (continuous_const.prodMk continuous_id) }
  let Hmapped := Htorus.map f
  have hsource :
      A.orderThreeFillingRelationPrincipalGaugeLoop.map f.continuous =
        A.orderThreeCentralPrincipalGaugeFiberPath := by
    apply Path.ext
    funext t
    rfl
  have htarget :
      A.orderThreePrincipalGaugeStraightLoop.map f.continuous =
        A.orderThreeCentralPrincipalGaugeStraightFiberPath := by
    apply Path.ext
    funext t
    rfl
  exact ⟨Hmapped.cast hsource htarget⟩

public theorem orderThreeLocalOffsetFiberCentralPath_homotopy_localStraight_with_trace :
    letI := A.ellipticThreeBoundaryAction
    ∃ H : ContinuousMap.Homotopy A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
        A.orderThreeCentralPrincipalGaugeStraightFiberPath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.ellipticThreeBoundaryAction
  let Hoffset := A.orderThreeLocalOffsetFiberCentralPath_offsetHomotopy
  rcases A.orderThreeCentralPrincipalGaugeFiberPath_homotopic_straight with ⟨Hpath⟩
  let Hstraight := pathHomotopyToFreeHomotopy Hpath
  let H := Hoffset.trans Hstraight
  refine ⟨H, fun s ↦ ?_⟩
  apply freeLoopHomotopyTrans_trace
  · intro r
    exact A.orderThreeLocalOffsetFiberCentralPath_offsetHomotopy_trace r
  · intro r
    exact (Hpath.source r).trans (Hpath.target r).symm

/-- The regular point underlying the local straight fibre loop. -/
public noncomputable def orderThreeLocalStraightRegularPoint : RegularTotalSpace A.periods :=
  A.orderThreePuncturedProductToRegularMap
    (A.orderThreePuncturedProductCarrierMap
      (A.orderThreeCayleyPuncturedBasepoint,
        A.orderThreePrincipalGaugeStraightLoop 0))

/-- A vector-bundle-cover representative whose fixed real-period coordinate is the chosen
principal-gauge lift. -/
public noncomputable def orderThreeLocalStraightCoverPoint :
    RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace :=
  let b := regularTotalSpaceBase A.periods A.orderThreeLocalStraightRegularPoint
  (b, (fixedToMovingCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
    (b.1, A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2)

public theorem orderThreeLocalStraightCoverPoint_projects :
    letI := A.ellipticThreeBoundaryAction
    regularFamilyCoverProjection A.periods A.orderThreeLocalStraightCoverPoint =
      A.orderThreeLocalStraightRegularPoint := by
  let _ := A.ellipticThreeBoundaryAction
  let x := A.orderThreeLocalStraightRegularPoint
  let b := regularTotalSpaceBase A.periods x
  let v := (fixedToMovingCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
    (b.1, A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2
  change regularFamilyCoverProjection A.periods (b, v) = x
  apply regularFamilyInclusion_injective A.periods
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  have hlocal := A.orderThreePuncturedProductToRegularMap_productCoordinate
    (A.orderThreeCayleyPuncturedBasepoint,
      A.orderThreePrincipalGaugeStraightLoop 0)
  change (orderThreeRealPeriodProductHomeomorph A.periods)
      (Quotient.mk _ (b.1, v)) =
    (orderThreeRealPeriodProductHomeomorph A.periods)
      (regularFamilyInclusion A.periods x)
  dsimp only [x]
  unfold orderThreeLocalStraightRegularPoint at ⊢
  rw [hlocal]
  rw [orderThreeRealPeriodProductHomeomorph_mk]
  have hvpair : (b.1, v) = fixedToMovingCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne
      (b.1, A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) := by
    rfl
  rw [hvpair, movingToFixedCover_fixedToMovingCover]
  simp only [fixedToMovingCover]
  apply Prod.ext
  · have hbase := congrArg Prod.fst hlocal
    rw [orderThreeRealPeriodProductHomeomorph_fst,
      familyTotalSpaceBase_regularFamilyInclusion] at hbase
    simpa only [b, x, orderThreeLocalStraightRegularPoint] using hbase
  · change Quotient.mk _ (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) =
      A.orderThreePrincipalGaugeStraightLoop 0
    rw [show A.orderThreePrincipalGaugeStraightLoop 0 =
      Quotient.mk _ (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) by
        exact A.orderThreePrincipalGaugeStraightLoop.source]

public theorem orderThreeLocalStraightCoverPoint_period_projects
    (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    regularFamilyCoverProjection A.periods
        (regularFamilyPeriodLiftPath A.periods
          A.orderThreeLocalStraightCoverPoint epsilon t) =
      A.orderThreePuncturedProductToRegularMap
        (A.orderThreePuncturedProductCarrierMap
          (A.orderThreeCayleyPuncturedBasepoint,
            A.orderThreePrincipalGaugeStraightLoop t)) := by
  let _ := A.ellipticThreeBoundaryAction
  apply regularFamilyInclusion_injective A.periods
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  have hlocal := A.orderThreePuncturedProductToRegularMap_productCoordinate
    (A.orderThreeCayleyPuncturedBasepoint,
      A.orderThreePrincipalGaugeStraightLoop t)
  rw [hlocal]
  unfold orderThreeLocalStraightCoverPoint regularFamilyPeriodLiftPath
  change (orderThreeRealPeriodProductHomeomorph A.periods)
      (Quotient.mk _
        ((regularTotalSpaceBase A.periods A.orderThreeLocalStraightRegularPoint).1,
          (t : ℝ) • periodVector
              (parameterMap A.periods
                (regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1).1 epsilon +
            (fixedToMovingCover A.periods
              A.modular.modularParameter.toTriangleUniformization.zOne
              ((regularTotalSpaceBase A.periods
                A.orderThreeLocalStraightRegularPoint).1,
                A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2)) = _
  rw [orderThreeRealPeriodProductHomeomorph_mk]
  have hscaled :
      movingToFixedCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne
          ((regularTotalSpaceBase A.periods A.orderThreeLocalStraightRegularPoint).1,
            (t : ℝ) • periodVector
                (parameterMap A.periods
                  (regularTotalSpaceBase A.periods
                    A.orderThreeLocalStraightRegularPoint).1).1 epsilon +
              (fixedToMovingCover A.periods
                A.modular.modularParameter.toTriangleUniformization.zOne
                ((regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1,
                  A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2) =
        ((regularTotalSpaceBase A.periods A.orderThreeLocalStraightRegularPoint).1,
          (t : ℝ) • periodVector
              (parameterMap A.periods
                A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon +
            (movingToFixedCover A.periods
              A.modular.modularParameter.toTriangleUniformization.zOne
              ((regularTotalSpaceBase A.periods
                A.orderThreeLocalStraightRegularPoint).1,
                (fixedToMovingCover A.periods
                  A.modular.modularParameter.toTriangleUniformization.zOne
                  ((regularTotalSpaceBase A.periods
                    A.orderThreeLocalStraightRegularPoint).1,
                    A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2)).2) := by
    apply Prod.ext
    · rfl
    · change (fullRankDomain
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne)).realEquiv
          (EllipticFixedPointCriterion.periodCoordinates
            (parameterMap A.periods
              (regularTotalSpaceBase A.periods
                A.orderThreeLocalStraightRegularPoint).1)
            ((t : ℝ) • periodVector
                (parameterMap A.periods
                  (regularTotalSpaceBase A.periods
                    A.orderThreeLocalStraightRegularPoint).1).1 epsilon +
              (fixedToMovingCover A.periods
                A.modular.modularParameter.toTriangleUniformization.zOne
                ((regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1,
                  A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2)) =
        (t : ℝ) • periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon +
          (fullRankDomain
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zOne)).realEquiv
            (EllipticFixedPointCriterion.periodCoordinates
              (parameterMap A.periods
                (regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1)
              (fixedToMovingCover A.periods
                A.modular.modularParameter.toTriangleUniformization.zOne
                ((regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1,
                  A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2)
      rw [show EllipticFixedPointCriterion.periodCoordinates
            (parameterMap A.periods
              (regularTotalSpaceBase A.periods
                A.orderThreeLocalStraightRegularPoint).1)
            ((t : ℝ) • periodVector
                (parameterMap A.periods
                  (regularTotalSpaceBase A.periods
                    A.orderThreeLocalStraightRegularPoint).1).1 epsilon +
              (fixedToMovingCover A.periods
                A.modular.modularParameter.toTriangleUniformization.zOne
                ((regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1,
                  A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2) =
          EllipticFixedPointCriterion.periodCoordinates
              (parameterMap A.periods
                (regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1)
              ((t : ℝ) • periodVector
                (parameterMap A.periods
                  (regularTotalSpaceBase A.periods
                    A.orderThreeLocalStraightRegularPoint).1).1 epsilon) +
            EllipticFixedPointCriterion.periodCoordinates
              (parameterMap A.periods
                (regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1)
              (fixedToMovingCover A.periods
                A.modular.modularParameter.toTriangleUniformization.zOne
                ((regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1,
                  A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2 by
          exact map_add
            (fullRankDomain
              (parameterMap A.periods
                (regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1)).realEquiv.symm _ _,
        show EllipticFixedPointCriterion.periodCoordinates
              (parameterMap A.periods
                (regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1)
              ((t : ℝ) • periodVector
                (parameterMap A.periods
                  (regularTotalSpaceBase A.periods
                    A.orderThreeLocalStraightRegularPoint).1).1 epsilon) =
            (t : ℝ) • EllipticFixedPointCriterion.periodCoordinates
              (parameterMap A.periods
                (regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1)
              (periodVector
                (parameterMap A.periods
                  (regularTotalSpaceBase A.periods
                    A.orderThreeLocalStraightRegularPoint).1).1 epsilon) by
          exact map_smul
            (fullRankDomain
              (parameterMap A.periods
                (regularTotalSpaceBase A.periods
                  A.orderThreeLocalStraightRegularPoint).1)).realEquiv.symm _ _,
        EllipticFixedPointCriterion.periodCoordinates_periodVector, map_add, map_smul,
        (fullRankDomain
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne)).map_integer]
  rw [hscaled]
  have hvpair :
      ((regularTotalSpaceBase A.periods A.orderThreeLocalStraightRegularPoint).1,
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne
          ((regularTotalSpaceBase A.periods A.orderThreeLocalStraightRegularPoint).1,
            A.orderThreeFillingRelationPrincipalGaugeCoverLift 0)).2) =
        fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne
          ((regularTotalSpaceBase A.periods A.orderThreeLocalStraightRegularPoint).1,
            A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) := by
    rfl
  rw [hvpair, movingToFixedCover_fixedToMovingCover]
  apply Prod.ext
  · have hbase := congrArg Prod.fst
      (A.orderThreePuncturedProductToRegularMap_productCoordinate
        (A.orderThreeCayleyPuncturedBasepoint,
          A.orderThreePrincipalGaugeStraightLoop 0))
    rw [orderThreeRealPeriodProductHomeomorph_fst,
      familyTotalSpaceBase_regularFamilyInclusion] at hbase
    simpa only [orderThreeLocalStraightRegularPoint] using hbase
  · apply congrArg (Quotient.mk _)
    change (t : ℝ) • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon +
        A.orderThreeFillingRelationPrincipalGaugeCoverLift 0 =
      A.orderThreePrincipalGaugeStraightLiftPath t
    unfold orderThreePrincipalGaugeStraightLiftPath
    rw [Path.segment_apply, AffineMap.lineMap_apply_module,
      orderThreeFillingRelationPrincipalGaugeDeck_smul]
    module

/-- A cover path from the local straight representative to the inverse deck translate of the
actual cusp representative.  The inverse translate is what makes the transported `epsilon`
label become the corrected global label. -/
public noncomputable def orderThreeLocalStraightToCorrectedCuspCoverPath :
    Path A.orderThreeLocalStraightCoverPoint
      (regularDeckMap A.periods
        (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
        A.cuspRegularCoverPoint) := by
  letI : PathConnectedSpace
      (RegularBase (U := A.paperTriangleUniformization)) :=
    regularBase_pathConnected A.paperTriangleUniformization
  exact PathConnectedSpace.somePath _ _

/-- Sweep the globally labelled `epsilon` period from the local straight cover point to the
inverse deck translate of the actual cusp cover point. -/
public noncomputable def orderThreeLocalStraightToCorrectedCuspRegularHomotopy :
    ContinuousMap.Homotopy
      (regularFamilyPeriodLoop A.periods A.orderThreeLocalStraightCoverPoint epsilon).toContinuousMap
      (regularFamilyPeriodLoop A.periods
        (regularDeckMap A.periods
          (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
          A.cuspRegularCoverPoint) epsilon).toContinuousMap :=
  regularFamilyPeriodLoopHomotopyAlong A.periods
    A.orderThreeLocalStraightToCorrectedCuspCoverPath epsilon

/-- The same sweep after passing to the central triangle-group quotient. -/
public noncomputable def orderThreeLocalStraightToCorrectedCuspCentralHomotopy :
    ContinuousMap.Homotopy
      (((regularFamilyPeriodLoop A.periods A.orderThreeLocalStraightCoverPoint epsilon).map
        (regularFamilyQuotientMap A.periods).continuous).toContinuousMap)
      (((regularFamilyPeriodLoop A.periods
        (regularDeckMap A.periods
          (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
          A.cuspRegularCoverPoint) epsilon).map
        (regularFamilyQuotientMap A.periods).continuous).toContinuousMap) :=
  (ContinuousMap.Homotopy.refl (regularFamilyQuotientMap A.periods)).comp
    A.orderThreeLocalStraightToCorrectedCuspRegularHomotopy

public theorem orderThreeLocalStraightToCorrectedCuspCentralHomotopy_trace
    (s : unitInterval) :
    A.orderThreeLocalStraightToCorrectedCuspCentralHomotopy (s, 0) =
      A.orderThreeLocalStraightToCorrectedCuspCentralHomotopy (s, 1) := by
  have hraw :
      A.orderThreeLocalStraightToCorrectedCuspRegularHomotopy (s, 0) =
        A.orderThreeLocalStraightToCorrectedCuspRegularHomotopy (s, 1) := by
    have hzero := congrArg (fun L ↦ L s)
      (regularFamilyPeriodLoopHomotopyAlong_evalAt_zero A.periods
        A.orderThreeLocalStraightToCorrectedCuspCoverPath epsilon)
    have hone := congrArg (fun L ↦ L s)
      (regularFamilyPeriodLoopHomotopyAlong_evalAt_one A.periods
        A.orderThreeLocalStraightToCorrectedCuspCoverPath epsilon)
    have hzero' :
        A.orderThreeLocalStraightToCorrectedCuspRegularHomotopy (s, 0) =
          regularFamilyCoverWhisker A.periods
            A.orderThreeLocalStraightToCorrectedCuspCoverPath s := by
      simpa only [orderThreeLocalStraightToCorrectedCuspRegularHomotopy,
        Path.cast_coe, ContinuousMap.Homotopy.evalAt_apply] using hzero
    have hone' :
        A.orderThreeLocalStraightToCorrectedCuspRegularHomotopy (s, 1) =
          regularFamilyCoverWhisker A.periods
            A.orderThreeLocalStraightToCorrectedCuspCoverPath s := by
      simpa only [orderThreeLocalStraightToCorrectedCuspRegularHomotopy,
        Path.cast_coe, ContinuousMap.Homotopy.evalAt_apply] using hone
    exact hzero'.trans hone'.symm
  exact congrArg (regularFamilyQuotientMap A.periods) hraw

public theorem orderThreeMappedLocalStraightPeriod_eq_principalGaugeStraightFiberPath :
    letI := A.ellipticThreeBoundaryAction
    ((regularFamilyPeriodLoop A.periods A.orderThreeLocalStraightCoverPoint epsilon).map
        (regularFamilyQuotientMap A.periods).continuous).toContinuousMap =
      A.orderThreeCentralPrincipalGaugeStraightFiberPath.toContinuousMap := by
  let _ := A.ellipticThreeBoundaryAction
  ext t
  change regularFamilyQuotientMap A.periods
      (regularFamilyCoverProjection A.periods
        (regularFamilyPeriodLiftPath A.periods
          A.orderThreeLocalStraightCoverPoint epsilon t)) = _
  rw [A.orderThreeLocalStraightCoverPoint_period_projects t]
  rfl

public theorem orderThreeMappedCorrectedCuspPeriod_eq_centralAffineCorrectedPeriod :
    ((regularFamilyPeriodLoop A.periods
        (regularDeckMap A.periods
          (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
          A.cuspRegularCoverPoint) epsilon).map
        (regularFamilyQuotientMap A.periods).continuous).toContinuousMap =
      A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.toContinuousMap := by
  ext t
  unfold orderThreeCentralAffineCorrectedEpsilonPeriodPath
    ellipticThreeCuspCorrectedEpsilonPeriodPath cuspCentralPeriodLoop
  have hlabel :
      rhoLambda (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
          (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon) =
        epsilon := by
    rw [map_inv]
    exact (rhoLambda
      ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)).symm_apply_apply epsilon
  have hdeck := regularFamilyPeriodLoop_deck A.periods
    (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
    A.cuspRegularCoverPoint
    (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon)
  have ht := congrArg (fun L ↦ L t) hdeck
  have haffine :
      (A.orderThreeCentralAffineCorrectedEpsilonPeriodPath : unitInterval → _) =
        (A.ellipticThreeCuspCorrectedEpsilonPeriodPath : unitInterval → _) := by
    unfold orderThreeCentralAffineCorrectedEpsilonPeriodPath
    exact Path.cast_coe _ _ _
  have hcusp :
      (A.ellipticThreeCuspCorrectedEpsilonPeriodPath : unitInterval → _) =
        (((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint
          (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon)).map
            (regularFamilyQuotientMap A.periods).continuous) : unitInterval → _) := by
    unfold ellipticThreeCuspCorrectedEpsilonPeriodPath cuspCentralPeriodLoop
    exact Path.cast_coe _ _ _
  have ht' :
      ((regularFamilyPeriodLoop A.periods
        (regularDeckMap A.periods
          (((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent)⁻¹)
          A.cuspRegularCoverPoint) epsilon).map
        (regularFamilyQuotientMap A.periods).continuous) t =
      ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint
        (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon)).map
        (regularFamilyQuotientMap A.periods).continuous) t := by
    simpa only [hlabel, Path.cast_coe] using ht
  exact ht'.trans (congrFun (haffine.trans hcusp) t).symm

/-- The local principal-gauge straight fibre loop sweeps to the exact globally corrected
affine-period representative, and every intermediate path remains a free loop. -/
public theorem
    orderThreeCentralPrincipalGaugeStraightFiberPath_homotopy_globalCorrectedPeriod_with_trace :
    letI := A.ellipticThreeBoundaryAction
    ∃ H : ContinuousMap.Homotopy
        A.orderThreeCentralPrincipalGaugeStraightFiberPath.toContinuousMap
        A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.ellipticThreeBoundaryAction
  let H := A.orderThreeLocalStraightToCorrectedCuspCentralHomotopy.cast
    A.orderThreeMappedLocalStraightPeriod_eq_principalGaugeStraightFiberPath
    A.orderThreeMappedCorrectedCuspPeriod_eq_centralAffineCorrectedPeriod
  refine ⟨H, fun s ↦ ?_⟩
  exact A.orderThreeLocalStraightToCorrectedCuspCentralHomotopy_trace s

/-- Complete order-three fibre comparison: the local offset fibre factor is freely homotopic,
with its endpoint trace retained, to the exact global affine-period representative used by the
relator classification. -/
public theorem orderThreeLocalOffsetFiberCentralPath_homotopy_globalCorrectedPeriod_with_trace :
    letI := A.ellipticThreeBoundaryAction
    ∃ H : ContinuousMap.Homotopy
        A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
        A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.ellipticThreeBoundaryAction
  rcases A.orderThreeLocalOffsetFiberCentralPath_homotopy_localStraight_with_trace with
    ⟨Hlocal, hlocal⟩
  rcases A.orderThreeCentralPrincipalGaugeStraightFiberPath_homotopy_globalCorrectedPeriod_with_trace
    with ⟨Hglobal, hglobal⟩
  let H := Hlocal.trans Hglobal
  refine ⟨H, fun s ↦ ?_⟩
  apply freeLoopHomotopyTrans_trace
  · exact hlocal
  · exact hglobal

/-- Remove the whole initial fibre coordinate, including its principal-gauge component. -/
public noncomputable def orderThreeLocalZeroBasedFiberCentralPath :
    letI := A.ellipticThreeBoundaryAction
    Path (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint, 0))
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint, 0)) := by
  let _ := A.ellipticThreeBoundaryAction
  let q := A.orderThreePrincipalGaugeWithOffsetPath
  exact
    { toFun := fun t ↦ A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint, q t - q 0)
      continuous_toFun := A.orderThreePuncturedProductToCentralMap.continuous.comp
        (continuous_const.prodMk (q.continuous.sub continuous_const))
      source' := by rw [sub_self]
      target' := by rw [q.target, q.source, sub_self] }

/-- This fibre contraction uses exactly the vector contraction of the base factor. -/
public def orderThreeLocalSynchronizedFiberContractionHomotopy :
    letI := A.ellipticThreeBoundaryAction
    ContinuousMap.Homotopy A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
      A.orderThreeLocalZeroBasedFiberCentralPath.toContinuousMap := by
  let _ := A.ellipticThreeBoundaryAction
  let p := (parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne).1
  let q := A.orderThreePrincipalGaugeWithOffsetPath
  exact
    { toFun := fun st ↦ A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          q st.2 - q 0 + (Quotient.mk _
            (((1 - (st.1 : ℝ) : ℝ) : ℂ) • A.orderThreeLocalOffsetBaseVector) :
              AdditiveTorus p))
      continuous_toFun := A.orderThreePuncturedProductToCentralMap.continuous.comp
        (continuous_const.prodMk
          (((q.continuous.comp continuous_snd).sub continuous_const).add
            ((continuous_quot_mk : Continuous (torusProjection p)).comp (by fun_prop))))
      map_zero_left := by
        intro t
        change A.orderThreePuncturedProductToCentralMap
            (A.orderThreeCayleyPuncturedBasepoint,
              q t - q 0 + Quotient.mk _ (((1 - (0 : ℝ) : ℝ) : ℂ) •
                A.orderThreeLocalOffsetBaseVector)) =
          A.orderThreePuncturedProductToCentralMap (A.orderThreeCayleyPuncturedBasepoint, q t)
        simp only [sub_zero, Complex.ofReal_one, one_smul]
        rw [← A.orderThreePrincipalGaugeWithOffsetPath_zero_eq_mk]
        simp only [q, sub_add_cancel]
      map_one_left := by
        intro t
        change A.orderThreePuncturedProductToCentralMap
            (A.orderThreeCayleyPuncturedBasepoint,
              q t - q 0 + Quotient.mk _ (((1 - (1 : ℝ) : ℝ) : ℂ) •
                A.orderThreeLocalOffsetBaseVector)) =
          A.orderThreePuncturedProductToCentralMap
            (A.orderThreeCayleyPuncturedBasepoint, q t - q 0)
        simp only [sub_self, Complex.ofReal_zero, zero_smul, additiveTorus_mk_zero, add_zero] }

public theorem orderThreeLocalSynchronizedFiberContractionHomotopy_endpoints
    (s : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    let Hfiber := A.orderThreeLocalSynchronizedFiberContractionHomotopy
    let Hbase := A.orderThreeLocalBaseFiberContractionHomotopy
    Hfiber (s, 1) = Hbase (s, 0) ∧ Hfiber (s, 0) = Hbase (s, 1) := by
  let _ := A.ellipticThreeBoundaryAction
  change A.orderThreePuncturedProductToCentralMap (_, _ - _ + _) =
      A.orderThreePuncturedProductToCentralMap (_, _) ∧
    A.orderThreePuncturedProductToCentralMap (_, _ - _ + _) =
      A.orderThreePuncturedProductToCentralMap (_, _)
  simp only [A.orderThreePrincipalGaugeWithOffsetPath.target,
    A.orderThreePrincipalGaugeWithOffsetPath.source,
    A.orderThreeFillingRelationCayleyPuncturedLoop.source,
    A.orderThreeFillingRelationCayleyPuncturedLoop.target, sub_self, zero_add]
  trivial

/-- The zero-fibre base factor has the same basepoint as the normalized fibre factor. -/
public noncomputable def orderThreeLocalZeroBaseCentralPath :
    letI := A.ellipticThreeBoundaryAction
    Path (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint, 0))
      (A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint, 0)) := by
  let _ := A.ellipticThreeBoundaryAction
  exact
    { toContinuousMap := A.orderThreeLocalZeroBaseCentralMap
      source' := congrArg (fun x ↦ A.orderThreePuncturedProductToCentralMap (x, 0))
        A.orderThreeFillingRelationCayleyPuncturedLoop.source
      target' := congrArg (fun x ↦ A.orderThreePuncturedProductToCentralMap (x, 0))
        A.orderThreeFillingRelationCayleyPuncturedLoop.target }

/-- Both factors can be normalized simultaneously, retaining a single moving basepoint for
the complete local relator. -/
public theorem orderThreeLocalFiberThenBaseCentralPath_homotopy_zeroBased_with_trace :
    letI := A.ellipticThreeBoundaryAction
    ∃ H : ContinuousMap.Homotopy A.orderThreeLocalFiberThenBaseCentralPath.toContinuousMap
        (A.orderThreeLocalZeroBasedFiberCentralPath.trans
          A.orderThreeLocalZeroBaseCentralPath).toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.ellipticThreeBoundaryAction
  let F := A.orderThreeLocalSynchronizedFiberContractionHomotopy
  let G : ContinuousMap.Homotopy A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeLocalZeroBaseCentralPath.toContinuousMap :=
    A.orderThreeLocalBaseFiberContractionHomotopy
  have hjoin (s : unitInterval) : F (s, 1) = G (s, 0) :=
    (A.orderThreeLocalSynchronizedFiberContractionHomotopy_endpoints s).1
  have htrace (s : unitInterval) : F (s, 0) = G (s, 1) :=
    (A.orderThreeLocalSynchronizedFiberContractionHomotopy_endpoints s).2
  let H := freeLoopHomotopyHcomp F G hjoin
  refine ⟨H.cast (congrArg Path.toContinuousMap
    A.orderThreeLocalFiberThenBaseCentralPath_eq_trans.symm) rfl, ?_⟩
  exact freeLoopHomotopyHcomp_trace F G hjoin htrace

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
