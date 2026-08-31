module

public import SphereSixComplex.Topology.ConstructedA2GlobalMomentCoordinateProof
public import SphereSixComplex.Topology.ConstructedA2HoneycombCellDataProof

@[expose] public section

noncomputable section

open Filter Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions

private def baseApproachRawCoordinates (s a : ℝ) : RawCoordinates :=
  ![(s : ℂ), (a : ℂ), 1]

private noncomputable def baseApproachPoint {r : ℝ} (a : ℝ) (ha : 0 ≤ a)
    (s : ℝ) (hs : 0 ≤ s) (hsr : s * a < r) : constructedLocalPositivePart r := by
  let x : Carrier := inclusion baseChart (baseApproachRawCoordinates s a)
  let q : LocalCarrier constructedModel r := ⟨x, by
    change carrierHeight x ∈ Metric.ball 0 r
    rw [carrierHeight_inclusion]
    simp only [rawHeight, baseApproachRawCoordinates, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Metric.mem_ball, dist_zero_right]
    simpa [abs_of_nonneg hs, abs_of_nonneg ha] using hsr⟩
  exact ⟨q, (mem_constructedLocalPositivePart_iff r q).mpr (by
    rw [inclusion_mem_carrierPositivePart_iff]
    refine ⟨![s, a, 1], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [hs, ha]
    · funext i
      fin_cases i <;> simp [baseApproachRawCoordinates])⟩

private theorem baseApproachPoint_t {r : ℝ} (a : ℝ) (ha : 0 ≤ a)
    (s : ℝ) (hs : 0 ≤ s) (hsr : s * a < r) :
    constructedModel.t
        (baseApproachPoint a ha s hs hsr : LocalCarrier constructedModel r) =
      (s * a : ℂ) := by
  change carrierHeight (inclusion baseChart (baseApproachRawCoordinates s a)) = _
  rw [carrierHeight_inclusion]
  simp [rawHeight, baseApproachRawCoordinates]

private def baseApproachTorus (s a : ℝ) (hs : s ≠ 0) (ha : a ≠ 0) : DenseTorus :=
  ![Units.mk0 (a : ℂ) (by exact_mod_cast ha), 1,
    Units.mk0 ((s * a : ℝ) : ℂ) (by exact_mod_cast mul_ne_zero hs ha)]

private theorem torusCoordinates_baseApproachPoint {r : ℝ}
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : 0 < s) (hsr : s * a < r) :
    torusCoordinates constructedModel
        (baseApproachPoint a ha.le s hs.le hsr : LocalCarrier constructedModel r) =
      baseApproachTorus s a hs.ne' ha.ne' := by
  apply torusCoordinates_unique constructedModel
    (by
      rw [baseApproachPoint_t a ha.le s hs.le hsr]
      exact_mod_cast (mul_pos hs ha).ne')
  change carrierTorusEmbedding (baseApproachTorus s a hs.ne' ha.ne') =
    inclusion baseChart (baseApproachRawCoordinates s a)
  unfold carrierTorusEmbedding
  congr 1
  funext i
  fin_cases i <;>
    simp [baseChartCoordinates, baseTorusHomeomorph, baseTorusEquiv,
      denseRawCoordinates, baseApproachTorus, baseApproachRawCoordinates]

private theorem offCentralMomentCoordinate_baseApproachPoint {r : ℝ}
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : 0 < s) (hsr : s * a < r) :
    constructedA2OffCentralMomentCoordinate (baseApproachPoint a ha.le s hs.le hsr) =
      ![Real.log a / Real.log (s * a), 0, s * a] := by
  funext i
  fin_cases i <;>
    simp [constructedA2OffCentralMomentCoordinate, rescaledPosition,
      torusCoordinates_baseApproachPoint a ha s hs hsr,
      baseApproachPoint_t a ha.le s hs.le hsr, baseApproachTorus,
      abs_of_pos ha, abs_of_pos hs]

private def baseApproachScale (r : ℝ) (n : ℕ) : ℝ :=
  (r / 2) / ((n : ℝ) + 1)

private theorem baseApproachScale_pos {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 < baseApproachScale r n := by
  exact div_pos (half_pos hr) (Nat.cast_add_one_pos n)

private theorem baseApproachScale_mul_lt {r : ℝ} (hr : 0 < r)
    (a : ℝ) (ha : a ≤ 1) (n : ℕ) : baseApproachScale r n * a < r := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
  have hs0 : 0 ≤ baseApproachScale r n := (baseApproachScale_pos hr n).le
  have hsle : baseApproachScale r n ≤ r / 2 := div_le_self (half_pos hr).le hn
  have hsa : baseApproachScale r n * a ≤ baseApproachScale r n :=
    mul_le_of_le_one_right hs0 ha
  nlinarith

private theorem baseApproachScale_tendsto (r : ℝ) :
    Tendsto (baseApproachScale r) atTop (nhds 0) := by
  unfold baseApproachScale
  apply Filter.Tendsto.const_div_atTop
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds

private noncomputable def baseApproachSequence {r : ℝ} (hr : 0 < r)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    constructedLocalPositivePart r :=
  baseApproachPoint a ha0 (baseApproachScale r n) (baseApproachScale_pos hr n).le
    (baseApproachScale_mul_lt hr a ha1 n)

private noncomputable def baseCentralPoint {r : ℝ} (hr : 0 < r)
    (a : ℝ) (ha : 0 ≤ a) : constructedLocalPositivePart r :=
  baseApproachPoint a ha 0 le_rfl (by simpa using hr)

private theorem baseApproachSequence_tendsto {r : ℝ} (hr : 0 < r)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Tendsto (baseApproachSequence hr a ha0 ha1) atTop
      (nhds (baseCentralPoint hr a ha0)) := by
  rw [tendsto_subtype_rng, tendsto_subtype_rng]
  change Tendsto
    (fun n => inclusion baseChart (baseApproachRawCoordinates (baseApproachScale r n) a))
    atTop (nhds (inclusion baseChart (baseApproachRawCoordinates 0 a)))
  apply ((inclusion_isOpenEmbedding baseChart).continuous.tendsto
    (baseApproachRawCoordinates 0 a)).comp
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · change Tendsto (Complex.ofReal ∘ baseApproachScale r) atTop
      (nhds (Complex.ofReal 0))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (baseApproachScale_tendsto r)
  · simp [baseApproachRawCoordinates]
  · simp [baseApproachRawCoordinates]

private theorem baseApproachLogRatio_tendsto {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    Tendsto (fun n => Real.log a / Real.log (baseApproachScale r n * a))
      atTop (nhds 0) := by
  have harg : Tendsto (fun n => baseApproachScale r n * a) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using (baseApproachScale_tendsto r).mul_const a
    · exact Filter.Eventually.of_forall fun n => mul_pos (baseApproachScale_pos hr n) ha
  exact (Real.tendsto_log_nhdsGT_zero.comp harg).const_div_atBot (Real.log a)

private noncomputable def zeroMomentPoint {r : ℝ} (hr : 0 < r) :
    constructedPositiveMomentRegion r :=
  ⟨![0, 0, 0], by simp [constructedPositiveMomentRegion, hr]⟩

private theorem coordinate_baseApproachSequence_tendsto_zero {r : ℝ}
    (hr : 0 < r) {H : ConstructedHoneycombCellData r}
    (C : ConstructedA2ProperMomentCoordinate r H)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun n => C.coordinate (baseApproachSequence hr a ha0.le ha1 n))
      atTop (nhds (zeroMomentPoint hr)) := by
  have heq : (fun n => C.coordinate (baseApproachSequence hr a ha0.le ha1 n)) =
      fun n => constructedA2OffCentralMomentCoordinateTarget
        (baseApproachSequence hr a ha0.le ha1 n) := by
    funext n
    apply C.coordinate_offCentral
    unfold baseApproachSequence
    rw [baseApproachPoint_t]
    exact_mod_cast (mul_pos (baseApproachScale_pos hr n) ha0).ne'
  rw [heq, tendsto_subtype_rng]
  change Tendsto
    (fun n => constructedA2OffCentralMomentCoordinate
      (baseApproachSequence hr a ha0.le ha1 n)) atTop (nhds ![0, 0, 0])
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · convert baseApproachLogRatio_tendsto hr ha0 using 1
    funext n
    unfold baseApproachSequence
    exact congrFun (offCentralMomentCoordinate_baseApproachPoint a ha0
      (baseApproachScale r n) (baseApproachScale_pos hr n)
      (baseApproachScale_mul_lt hr a ha1 n)) 0
    · simp
  · convert tendsto_const_nhds using 1
    funext n
    unfold baseApproachSequence
    exact congrFun (offCentralMomentCoordinate_baseApproachPoint a ha0
      (baseApproachScale r n) (baseApproachScale_pos hr n)
      (baseApproachScale_mul_lt hr a ha1 n)) 1
  · convert (baseApproachScale_tendsto r).mul_const a using 1
    funext n
    unfold baseApproachSequence
    exact congrFun (offCentralMomentCoordinate_baseApproachPoint a ha0
      (baseApproachScale r n) (baseApproachScale_pos hr n)
      (baseApproachScale_mul_lt hr a ha1 n)) 2
    · simp

private theorem coordinate_baseCentralPoint_eq_zero {r : ℝ}
    (hr : 0 < r) {H : ConstructedHoneycombCellData r}
    (C : ConstructedA2ProperMomentCoordinate r H)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    C.coordinate (baseCentralPoint hr a ha0.le) = zeroMomentPoint hr := by
  apply tendsto_nhds_unique
    ((C.proper_coordinate.continuous.tendsto _).comp
      (baseApproachSequence_tendsto hr a ha0.le ha1))
    (coordinate_baseApproachSequence_tendsto_zero hr C a ha0 ha1)

private theorem baseCentralPoint_zero_ne_half {r : ℝ} (hr : 0 < r) :
    baseCentralPoint hr 1 (by norm_num) ≠
      baseCentralPoint hr (1 / 2) (by norm_num) := by
  intro h
  have hcarrier := congrArg
    (fun q : constructedLocalPositivePart r => (q.1.1 : Carrier)) h
  change inclusion baseChart (baseApproachRawCoordinates 0 1) =
    inclusion baseChart (baseApproachRawCoordinates 0 (1 / 2)) at hcarrier
  have hraw := (inclusion_isOpenEmbedding baseChart).injective hcarrier
  have hcoord := congrFun hraw 1
  norm_num [baseApproachRawCoordinates] at hcoord

/-- The raw logarithmic position collapses distinct points of a central toric component, so the
currently specified proper moment-coordinate certificate cannot exist. -/
public theorem constructedA2ProperMomentCoordinate_isEmpty {r : ℝ}
    (hr : 0 < r) (H : ConstructedHoneycombCellData r) :
    IsEmpty (ConstructedA2ProperMomentCoordinate r H) :=
  ⟨fun C => by
    have hcoord : C.coordinate (baseCentralPoint hr 1 (by norm_num)) =
        C.coordinate (baseCentralPoint hr (1 / 2) (by norm_num)) := by
      rw [coordinate_baseCentralPoint_eq_zero hr C 1 (by norm_num) (by norm_num),
        coordinate_baseCentralPoint_eq_zero hr C (1 / 2) (by norm_num) (by norm_num)]
    have hzero (a : ℝ) (ha : 0 ≤ a) :
        constructedModel.t
          (baseCentralPoint hr a ha : LocalCarrier constructedModel r) = 0 := by
      unfold baseCentralPoint
      rw [baseApproachPoint_t]
      norm_num
    have hplanar := congrArg
      (fun x : constructedPositiveMomentRegion r => fun i : Fin 2 => x.1 i.castSucc) hcoord
    rw [C.coordinate_central (baseCentralPoint hr 1 (by norm_num))
        (hzero 1 (by norm_num)),
      C.coordinate_central (baseCentralPoint hr (1 / 2) (by norm_num))
        (hzero (1 / 2) (by norm_num))] at hplanar
    have hcentral := H.honeycomb.symm.injective hplanar
    have hpoint := congrArg Subtype.val hcentral
    exact baseCentralPoint_zero_ne_half hr hpoint⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
