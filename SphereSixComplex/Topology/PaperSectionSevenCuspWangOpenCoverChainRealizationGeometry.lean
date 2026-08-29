module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealization
public import SphereSixComplex.Topology.PaperActualCuspCoordinateWinding
public import SphereSixComplex.Topology.PaperSectionSevenAffineOverlapInterleaving

/-!
# Geometric position of the actual cusp meridian

The logarithmic lift of the actual cusp meridian gains exactly `2πi`.  Hence its normalized
central coordinate crosses the affine vertical strip used by the Section 7 two-open cover.
-/

@[expose] public section

noncomputable section

open Set Metric Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge

/-- A loop with a logarithmic lift gaining `2πi` has a point on the imaginary axis. -/
public theorem exists_exp_re_eq_zero_of_log_turn
    (γ : C(unitInterval, ℂ))
    (hturn : γ 1 = γ 0 + 2 * Real.pi * Complex.I) :
    ∃ t : unitInterval, (Complex.exp (γ t)).re = 0 := by
  let a : ℝ := (γ 0).im
  let k : ℤ := ⌊(a - Real.pi / 2) / Real.pi⌋ + 1
  let target : ℝ := Real.pi / 2 + (k : ℝ) * Real.pi
  have hpi : 0 < Real.pi := Real.pi_pos
  have hkLower : (a - Real.pi / 2) / Real.pi < (k : ℝ) := by
    dsimp [k]
    push_cast
    exact Int.lt_floor_add_one (R := ℝ) _
  have hkUpper : (k : ℝ) ≤ (a - Real.pi / 2) / Real.pi + 1 := by
    dsimp [k]
    have hfloor := Int.floor_le (α := ℝ) ((a - Real.pi / 2) / Real.pi)
    push_cast
    linarith
  have hmulLower := mul_lt_mul_of_pos_right hkLower hpi
  have hmulUpper := mul_le_mul_of_nonneg_right hkUpper hpi.le
  have htargetLower : a ≤ target := by
    dsimp [target]
    rw [div_mul_cancel₀ _ hpi.ne'] at hmulLower
    linarith
  have htargetUpper : target ≤ a + 2 * Real.pi := by
    dsimp [target]
    rw [add_mul, div_mul_cancel₀ _ hpi.ne'] at hmulUpper
    linarith
  have himOne : (γ 1).im = a + 2 * Real.pi := by
    rw [hturn]
    simp [a]
  have hcont : Continuous (fun t : unitInterval ↦ (γ t).im) :=
    Complex.continuous_im.comp γ.continuous
  have hmem : target ∈ Set.Icc ((γ 0).im) ((γ 1).im) := by
    change a ≤ target ∧ target ≤ (γ 1).im
    rw [himOne]
    exact ⟨htargetLower, htargetUpper⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1 hcont hmem
  change (γ t).im = target at ht
  refine ⟨t, ?_⟩
  rw [Complex.exp_re, ht]
  have hcos : Real.cos target = 0 := by
    dsimp [target]
    rw [Real.cos_add_int_mul_pi]
    simp
  rw [hcos, mul_zero]

/-- During one positive logarithmic turn the exponential reaches the positive real axis. -/
public theorem exists_exp_re_eq_norm_of_log_turn
    (γ : C(unitInterval, ℂ))
    (hturn : γ 1 = γ 0 + 2 * Real.pi * Complex.I) :
    ∃ t : unitInterval, (Complex.exp (γ t)).re = ‖Complex.exp (γ t)‖ := by
  let a : ℝ := (γ 0).im
  let k : ℤ := ⌊a / (2 * Real.pi)⌋ + 1
  let target : ℝ := (k : ℝ) * (2 * Real.pi)
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have hkLower : a / (2 * Real.pi) < (k : ℝ) := by
    dsimp [k]
    push_cast
    exact Int.lt_floor_add_one (R := ℝ) _
  have hkUpper : (k : ℝ) ≤ a / (2 * Real.pi) + 1 := by
    dsimp [k]
    have hfloor := Int.floor_le (α := ℝ) (a / (2 * Real.pi))
    push_cast
    linarith
  have hmulLower := mul_lt_mul_of_pos_right hkLower htwoPi
  have hmulUpper := mul_le_mul_of_nonneg_right hkUpper htwoPi.le
  have htargetLower : a ≤ target := by
    dsimp [target]
    rw [div_mul_cancel₀ _ htwoPi.ne'] at hmulLower
    exact hmulLower.le
  have htargetUpper : target ≤ a + 2 * Real.pi := by
    dsimp [target]
    rw [add_mul, div_mul_cancel₀ _ htwoPi.ne'] at hmulUpper
    linarith
  have himOne : (γ 1).im = a + 2 * Real.pi := by
    rw [hturn]
    simp [a]
  have hcont : Continuous (fun t : unitInterval ↦ (γ t).im) :=
    Complex.continuous_im.comp γ.continuous
  have hmem : target ∈ Set.Icc ((γ 0).im) ((γ 1).im) := by
    change a ≤ target ∧ target ≤ (γ 1).im
    rw [himOne]
    exact ⟨htargetLower, htargetUpper⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1 hcont hmem
  change (γ t).im = target at ht
  refine ⟨t, ?_⟩
  rw [Complex.exp_re, Complex.norm_exp, ht]
  have hcos : Real.cos target = 1 := by
    dsimp [target]
    exact Real.cos_int_mul_two_pi k
  rw [hcos, mul_one]

variable (A : PaperAnalyticData)

/-- The actual marked cusp meridian reaches the middle height of the affine strip. -/
public theorem exists_actualCuspAngularCoordinateLoop_re_eq_half :
    ∃ t : unitInterval, ((A.actualCuspAngularCoordinateLoop t).1).re = 1 / 2 := by
  let γ : C(unitInterval, ℂ) :=
    ⟨A.actualCuspAngularZeroRawLog, A.continuous_actualCuspAngularZeroRawLog⟩
  obtain ⟨tzero, hzero⟩ :=
    exists_exp_re_eq_zero_of_log_turn γ A.actualCuspAngularZeroRawLog_one
  obtain ⟨tpositive, hpositive⟩ :=
    exists_exp_re_eq_norm_of_log_turn γ A.actualCuspAngularZeroRawLog_one
  have hgt : 2 < (Complex.exp (γ tpositive)).re := by
    rw [hpositive]
    change 2 < ‖Complex.exp (A.actualCuspAngularZeroRawLog tpositive)‖
    rw [A.actualCuspAngularZeroRawLog_exp]
    exact A.actualCuspAngularCoordinateLoop_norm_gt_two tpositive
  have hcont : Continuous (fun t : unitInterval ↦ (Complex.exp (γ t)).re) :=
    Complex.continuous_re.comp (Complex.continuous_exp.comp γ.continuous)
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc
      ((Complex.exp (γ tzero)).re) ((Complex.exp (γ tpositive)).re) := by
    rw [hzero]
    constructor <;> linarith
  obtain ⟨t, ht⟩ := intermediate_value_univ tzero tpositive hcont hmem
  refine ⟨t, ?_⟩
  rw [← A.actualCuspAngularZeroRawLog_exp]
  exact ht

/-- The explicit actual cusp meridian meets the precise affine overlap strip. -/
public theorem exists_actualCuspAngularCoordinateLoop_mem_affineVerticalStrip :
    ∃ t : unitInterval,
      (A.actualCuspAngularCoordinateLoop t).1 ∈ sectionSevenAffineVerticalStrip := by
  obtain ⟨t, ht⟩ := A.exists_actualCuspAngularCoordinateLoop_re_eq_half
  refine ⟨t, ?_⟩
  rw [sectionSevenAffineVerticalStrip]
  change (1 / 3 : ℝ) < ((A.actualCuspAngularCoordinateLoop t).1).re ∧
    ((A.actualCuspAngularCoordinateLoop t).1).re < 2 / 3
  rw [ht]
  norm_num

/-- The literal point of the actual cusp collar below the marked additive angular lift. -/
public noncomputable def actualCuspAngularCollarPoint (t : unitInterval) :
    A.openEmbeddingStarData.collarSource 0 :=
  additiveCuspBoundaryProjection A.starCuspWitness (A.actualCuspAngularLiftPoint t)

namespace SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

/-- The actual angular collar point enters the elliptic interior through its central piece. -/
public theorem cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage
    (t : unitInterval) :
    D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t) ∈
      A.sectionSevenEllipticCentralImage := by
  let q := A.actualCuspAngularCollarPoint t
  let y := A.cuspCollarToSectionSevenFinalOverlapHomeomorph q
  have hy : y.1 ∈
      (A.openEmbeddingStarData.SectionSevenEulerCover).piece 0 ∩
        (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 := by
    rw [← A.sectionSevenFinalOverlap_eq_centralCuspIntersection]
    exact y.2
  change (A.cuspCollarToSectionSevenFinalOverlapHomeomorph q).1 ∈
    (A.openEmbeddingStarData.SectionSevenEulerCover).piece 0
  exact hy.1

/-- In the central chart, the literal collar point has exactly the actual cusp-loop coordinate. -/
public theorem
    sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint
    (t : unitInterval) :
    A.sectionSevenEllipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ =
      A.centralFamilyCoordinate
        (A.actualCuspOverlapToCentral
          (A.actualCuspBoundaryProjection (A.actualCuspAngularLiftPoint t))) := by
  unfold sectionSevenEllipticCentralCoordinate
  congr 1
  apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
  apply Subtype.ext
  rw [A.centralToSectionSevenEulerPiece_centralImage,
    A.actualCuspOverlapToCentral_boundaryProjection]
  have hglobal :
      additiveCuspCoverToGlobal A.starCuspWitness (A.actualCuspAngularLiftPoint t) =
        A.starToCentral 0
          (additiveCuspBoundaryProjection A.starCuspWitness
            (A.actualCuspAngularLiftPoint t)) := by
    change additiveCuspCoverToGlobal A.starCuspWitness (A.actualCuspAngularLiftPoint t) =
      puncturedLocalCuspQuotientMap A.starCuspWitness
        (additiveCuspBoundaryProjection A.starCuspWitness
          (A.actualCuspAngularLiftPoint t))
    exact (puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection
      A.starCuspWitness (A.actualCuspAngularLiftPoint t)).symm
  calc
    ↑↑(⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ :
          A.sectionSevenEllipticCentralImage) =
        A.openEmbeddingStarData.collarSourceToGlued 0
          (A.actualCuspAngularCollarPoint t) := rfl
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral 0
          (additiveCuspBoundaryProjection A.starCuspWitness
            (A.actualCuspAngularLiftPoint t)))).1 :=
      (A.centralToSectionSevenEulerPiece_starToCentral 0 _).symm
    _ = (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (additiveCuspCoverToGlobal A.starCuspWitness
          (A.actualCuspAngularLiftPoint t))).1 := by rw [hglobal]

/-- Equivalently, that central coordinate is the explicit normalized cusp-coordinate loop. -/
public theorem
    sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_eq_loop
    (t : unitInterval) :
    A.sectionSevenEllipticCentralCoordinate
      ⟨D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t),
        D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t⟩ =
      A.actualCuspAngularCoordinateLoop t := by
  rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint]
  rfl

/-- At affine height `1/2`, the literal collar point lies in both concrete sides of the
pulled-back two-open cover. -/
public theorem cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_sideIntersection
    (R : A.SectionSevenAffineRadialCompletionInput) (t : unitInterval)
    (ht : ((A.actualCuspAngularCoordinateLoop t).1).re = 1 / 2) :
    R.twoDiscCover.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t) ∈
      R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide := by
  let D := R.twoDiscCover
  let x : A.SectionSevenEllipticInterior :=
    D.cuspToEllipticInteriorMap (A.actualCuspAngularCollarPoint t)
  have hxcentral : x ∈ A.sectionSevenEllipticCentralImage :=
    D.cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_centralImage t
  have hheight : A.sectionSevenEllipticCentralHeight ⟨x, hxcentral⟩ = 1 / 2 := by
    change (A.sectionSevenEllipticCentralCoordinate ⟨x, hxcentral⟩).1.re = 1 / 2
    rw [D.sectionSevenEllipticCentralCoordinate_cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_eq_loop]
    exact ht
  change x ∈ A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
    A.sectionSevenActualAffineSplit.allocation.orderFourSide
  constructor
  · right
    exact ⟨⟨x, hxcentral⟩, by
      change A.sectionSevenEllipticCentralHeight ⟨x, hxcentral⟩ < 2 / 3
      rw [hheight]
      norm_num, rfl⟩
  · right
    exact ⟨⟨x, hxcentral⟩, by
      change 1 / 3 < A.sectionSevenEllipticCentralHeight ⟨x, hxcentral⟩
      rw [hheight]
      norm_num, rfl⟩

/-- A concrete point of the actual cusp collar lies in the pulled-back cover intersection. -/
public theorem exists_actualCuspAngularCollarPoint_mem_pulledBackIntersection
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ∃ t : unitInterval,
      A.actualCuspAngularCollarPoint t ∈
        R.twoDiscCover.cuspOrderThreeOpen ⊓ R.twoDiscCover.cuspOrderFourOpen := by
  obtain ⟨t, ht⟩ := A.exists_actualCuspAngularCoordinateLoop_re_eq_half
  refine ⟨t, ?_⟩
  exact cuspToEllipticInteriorMap_actualCuspAngularCollarPoint_mem_sideIntersection R t ht

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end
