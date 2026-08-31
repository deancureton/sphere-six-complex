module

public import SphereSixComplex.Topology.PaperSectionSevenCuspAdaptiveCoverSelfMapConstruction

/-!
# Endpoint completion of the adaptive cusp phase

This file corrects the two height phases at the cylinder ends without moving either standard
cover threshold, then glues the corrected phases across the certified negative midpoint.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex

public noncomputable def lowerEndpointCorrectionValue (a x : ℝ) : ℝ :=
  if x ≤ 1 / 6 then
    max 0 (min (1 / 6) ((x - a) * ((1 / 6) / (1 / 6 - a))))
  else x

public theorem lowerEndpointCorrectionValue_nonneg (a x : unitInterval) :
    0 ≤ lowerEndpointCorrectionValue a x := by
  by_cases hx : (x : ℝ) ≤ 1 / 6
  · rw [lowerEndpointCorrectionValue, ite_eq_left hx]
    exact le_max_left _ _
  · rw [lowerEndpointCorrectionValue, ite_eq_right hx]
    exact x.2.1

public theorem lowerEndpointCorrectionValue_le_one (a x : unitInterval) :
    lowerEndpointCorrectionValue a x ≤ 1 := by
  by_cases hx : (x : ℝ) ≤ 1 / 6
  · rw [lowerEndpointCorrectionValue, ite_eq_left hx]
    exact (max_le (by norm_num) (min_le_left _ _)).trans (by norm_num)
  · rw [lowerEndpointCorrectionValue, ite_eq_right hx]
    exact x.2.2

public theorem continuous_lowerEndpointCorrectionValue (a : unitInterval)
    (ha : (a : ℝ) < 1 / 6) :
    Continuous (fun x : unitInterval => lowerEndpointCorrectionValue a x) := by
  unfold lowerEndpointCorrectionValue
  apply continuous_if_le continuous_subtype_val continuous_const
  · apply Continuous.continuousOn
    fun_prop
  · exact continuous_subtype_val.continuousOn
  · intro x hx
    have hd : (1 / 6 : ℝ) - a ≠ 0 := by linarith
    rw [hx, mul_div_cancel₀ (1 / 6 : ℝ) hd]
    norm_num

/-- A monotone lower-end correction sending `a < 1/6` to zero and fixing every point from
`1/6` onward. -/
public noncomputable def lowerEndpointCorrection (a : unitInterval)
    (ha : (a : ℝ) < 1 / 6) : C(unitInterval, unitInterval) where
  toFun x := ⟨lowerEndpointCorrectionValue a x,
    lowerEndpointCorrectionValue_nonneg a x,
    lowerEndpointCorrectionValue_le_one a x⟩
  continuous_toFun := (continuous_lowerEndpointCorrectionValue a ha).subtype_mk _

@[simp]
public theorem lowerEndpointCorrection_coe (a : unitInterval) (ha : (a : ℝ) < 1 / 6)
    (x : unitInterval) :
    (lowerEndpointCorrection a ha x : ℝ) = lowerEndpointCorrectionValue a x := rfl

@[simp]
public theorem lowerEndpointCorrection_self (a : unitInterval) (ha : (a : ℝ) < 1 / 6) :
    lowerEndpointCorrection a ha a = 0 := by
  apply Subtype.ext
  rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue, ite_eq_left ha.le]
  rw [sub_self]
  norm_num

public theorem lowerEndpointCorrection_eq_self_of_one_sixth_le
    (a : unitInterval) (ha : (a : ℝ) < 1 / 6) (x : unitInterval)
    (hx : (1 / 6 : ℝ) ≤ x) : lowerEndpointCorrection a ha x = x := by
  apply Subtype.ext
  by_cases hxeq : (x : ℝ) = 1 / 6
  · have hx' : (x : ℝ) ≤ 1 / 6 := hxeq.le
    rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue, ite_eq_left hx']
    change max 0 (min (1 / 6) (((x : ℝ) - a) * ((1 / 6) / (1 / 6 - a)))) = x
    rw [hxeq]
    have hd : (1 / 6 : ℝ) - a ≠ 0 := by linarith
    rw [mul_div_cancel₀ (1 / 6 : ℝ) hd]
    norm_num
  · rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue, ite_eq_right]
    exact fun h ↦ hxeq (le_antisymm h hx)

public theorem lowerEndpointCorrection_lt_one_third_iff
    (a : unitInterval) (ha : (a : ℝ) < 1 / 6) (x : unitInterval) :
    (lowerEndpointCorrection a ha x : ℝ) < 1 / 3 ↔ (x : ℝ) < 1 / 3 := by
  by_cases hx : (x : ℝ) ≤ 1 / 6
  · rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue, ite_eq_left hx]
    constructor
    · intro _
      linarith
    · intro _
      exact lt_of_le_of_lt (max_le (by norm_num) (min_le_left _ _)) (by norm_num)
  · rw [show lowerEndpointCorrection a ha x = x from
      lowerEndpointCorrection_eq_self_of_one_sixth_le a ha x (le_of_not_ge hx)]

public theorem one_sixth_lt_lowerEndpointCorrection_iff
    (a : unitInterval) (ha : (a : ℝ) < 1 / 6) (x : unitInterval) :
    1 / 6 < (lowerEndpointCorrection a ha x : ℝ) ↔ 1 / 6 < (x : ℝ) := by
  by_cases hx : (x : ℝ) ≤ 1 / 6
  · rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue, ite_eq_left hx]
    have hmax : max 0 (min (1 / 6) (((x : ℝ) - a) *
        ((1 / 6) / (1 / 6 - a)))) ≤ 1 / 6 := max_le (by norm_num) (min_le_left _ _)
    constructor <;> intro h <;> linarith
  · rw [show lowerEndpointCorrection a ha x = x from
      lowerEndpointCorrection_eq_self_of_one_sixth_le a ha x (le_of_not_ge hx)]

public noncomputable def lowerEndpointCorrectionFamily {X : Type*} [TopologicalSpace X]
    (a x : C(X, unitInterval)) (ha : ∀ z, (a z : ℝ) < 1 / 6) : C(X, unitInterval) where
  toFun z := ⟨lowerEndpointCorrectionValue (a z) (x z),
    lowerEndpointCorrectionValue_nonneg (a z) (x z),
    lowerEndpointCorrectionValue_le_one (a z) (x z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold lowerEndpointCorrectionValue
    apply continuous_if_le (continuous_subtype_val.comp x.continuous) continuous_const
    · apply Continuous.continuousOn
      have hden : Continuous (fun z => (1 / 6 : ℝ) - (a z : ℝ)) := by fun_prop
      have hden_ne : ∀ z, (1 / 6 : ℝ) - (a z : ℝ) ≠ 0 := fun z => by linarith [ha z]
      have hquot : Continuous (fun z => (1 / 6 : ℝ) / (1 / 6 - (a z : ℝ))) :=
        continuous_const.div hden hden_ne
      exact continuous_const.max (continuous_const.min
        ((continuous_subtype_val.comp x.continuous).sub
          (continuous_subtype_val.comp a.continuous) |>.mul hquot))
    · exact (continuous_subtype_val.comp x.continuous).continuousOn
    · intro z hz
      change (x z : ℝ) = 1 / 6 at hz
      have hd : (1 / 6 : ℝ) - (a z : ℝ) ≠ 0 := by linarith [ha z]
      rw [hz, mul_div_cancel₀ (1 / 6 : ℝ) hd]
      norm_num

@[simp]
public theorem lowerEndpointCorrectionFamily_apply {X : Type*} [TopologicalSpace X]
    (a x : C(X, unitInterval)) (ha : ∀ z, (a z : ℝ) < 1 / 6) (z : X) :
    lowerEndpointCorrectionFamily a x ha z = lowerEndpointCorrection (a z) (ha z) (x z) := by
  rfl

/-- The reflected endpoint correction sends a phase above `5/6` to one and fixes every point
through `5/6`. -/
public noncomputable def upperEndpointCorrection (b : unitInterval)
    (hb : 5 / 6 < (b : ℝ)) : C(unitInterval, unitInterval) where
  toFun x := ⟨1 - lowerEndpointCorrection
      ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩ (by linarith)
      ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩, by
    have h0 := (lowerEndpointCorrection
      ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩ (by linarith)
      ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩).2.1
    have h1 := (lowerEndpointCorrection
      ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩ (by linarith)
      ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩).2.2
    constructor <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_const.sub
    let a : unitInterval :=
      ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩
    have ha : (a : ℝ) < 1 / 6 := by dsimp [a]; linarith
    let reflect : unitInterval → unitInterval := fun x =>
      ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩
    have hreflect : Continuous reflect := by
      apply Continuous.subtype_mk
      fun_prop
    change Continuous (fun x : unitInterval =>
      lowerEndpointCorrectionValue (1 - (b : ℝ)) (1 - (x : ℝ)))
    convert (continuous_lowerEndpointCorrectionValue a ha).comp hreflect using 1
    funext x
    rfl

public theorem lowerEndpointCorrection_mem_vertexBand_iff_of_le_half
    (a : unitInterval) (ha : (a : ℝ) < 1 / 6) (x : unitInterval)
    (hx : (x : ℝ) ≤ 1 / 2) :
    lowerEndpointCorrection a ha x ∈ vertexBand ↔ x ∈ vertexBand := by
  have hout : (lowerEndpointCorrection a ha x : ℝ) ≤ 1 / 2 := by
    by_cases hlow : (x : ℝ) ≤ 1 / 6
    · rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue, ite_eq_left hlow]
      exact (max_le (by norm_num) (min_le_left _ _)).trans (by norm_num)
    · rw [lowerEndpointCorrection_eq_self_of_one_sixth_le a ha x (le_of_not_ge hlow)]
      exact hx
  change ((lowerEndpointCorrection a ha x : ℝ) < 1 / 3 ∨
      2 / 3 < (lowerEndpointCorrection a ha x : ℝ)) ↔
    ((x : ℝ) < 1 / 3 ∨ 2 / 3 < (x : ℝ))
  rw [or_iff_left (not_lt_of_ge (hout.trans (by norm_num))),
    or_iff_left (not_lt_of_ge (hx.trans (by norm_num))),
    lowerEndpointCorrection_lt_one_third_iff]

public theorem lowerEndpointCorrection_mem_edgeBand_iff_of_le_half
    (a : unitInterval) (ha : (a : ℝ) < 1 / 6) (x : unitInterval)
    (hx : (x : ℝ) ≤ 1 / 2) :
    lowerEndpointCorrection a ha x ∈ edgeBand ↔ x ∈ edgeBand := by
  have hout : (lowerEndpointCorrection a ha x : ℝ) ≤ 1 / 2 := by
    by_cases hlow : (x : ℝ) ≤ 1 / 6
    · rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue, ite_eq_left hlow]
      exact (max_le (by norm_num) (min_le_left _ _)).trans (by norm_num)
    · rw [lowerEndpointCorrection_eq_self_of_one_sixth_le a ha x (le_of_not_ge hlow)]
      exact hx
  change (1 / 6 < (lowerEndpointCorrection a ha x : ℝ) ∧
      (lowerEndpointCorrection a ha x : ℝ) < 5 / 6) ↔
    (1 / 6 < (x : ℝ) ∧ (x : ℝ) < 5 / 6)
  rw [and_iff_left (lt_of_le_of_lt hout (by norm_num)),
    and_iff_left (lt_of_le_of_lt hx (by norm_num)),
    one_sixth_lt_lowerEndpointCorrection_iff]

@[simp]
public theorem upperEndpointCorrection_self (b : unitInterval) (hb : 5 / 6 < (b : ℝ)) :
    upperEndpointCorrection b hb b = 1 := by
  apply Subtype.ext
  change 1 - (lowerEndpointCorrection _ _ _ : ℝ) = 1
  rw [lowerEndpointCorrection_self]
  norm_num

public theorem two_thirds_lt_upperEndpointCorrection_iff
    (b : unitInterval) (hb : 5 / 6 < (b : ℝ)) (x : unitInterval) :
    2 / 3 < (upperEndpointCorrection b hb x : ℝ) ↔ 2 / 3 < (x : ℝ) := by
  let a : unitInterval :=
    ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩
  have ha : (a : ℝ) < 1 / 6 := by dsimp [a]; linarith
  let xr : unitInterval :=
    ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩
  change 2 / 3 < 1 - (lowerEndpointCorrection a ha xr : ℝ) ↔ 2 / 3 < (x : ℝ)
  let z : ℝ := lowerEndpointCorrection a ha xr
  rw [show (2 / 3 < 1 - (lowerEndpointCorrection a ha xr : ℝ)) ↔
      ((lowerEndpointCorrection a ha xr : ℝ) < 1 / 3) by
        change 2 / 3 < 1 - z ↔ z < 1 / 3
        constructor <;> intro h <;> norm_num at h ⊢ <;> linarith]
  rw [lowerEndpointCorrection_lt_one_third_iff a ha xr]
  change 1 - (x : ℝ) < 1 / 3 ↔ 2 / 3 < (x : ℝ)
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

public theorem upperEndpointCorrection_lt_five_sixths_iff
    (b : unitInterval) (hb : 5 / 6 < (b : ℝ)) (x : unitInterval) :
    (upperEndpointCorrection b hb x : ℝ) < 5 / 6 ↔ (x : ℝ) < 5 / 6 := by
  let a : unitInterval :=
    ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩
  have ha : (a : ℝ) < 1 / 6 := by dsimp [a]; linarith
  let xr : unitInterval :=
    ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩
  change 1 - (lowerEndpointCorrection a ha xr : ℝ) < 5 / 6 ↔ (x : ℝ) < 5 / 6
  let z : ℝ := lowerEndpointCorrection a ha xr
  rw [show (1 - (lowerEndpointCorrection a ha xr : ℝ) < 5 / 6) ↔
      (1 / 6 < (lowerEndpointCorrection a ha xr : ℝ)) by
        change 1 - z < 5 / 6 ↔ 1 / 6 < z
        constructor <;> intro h <;> norm_num at h ⊢ <;> linarith]
  rw [one_sixth_lt_lowerEndpointCorrection_iff a ha xr]
  change 1 / 6 < 1 - (x : ℝ) ↔ (x : ℝ) < 5 / 6
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

public theorem upperEndpointCorrection_eq_self_of_le_five_sixths
    (b : unitInterval) (hb : 5 / 6 < (b : ℝ)) (x : unitInterval)
    (hx : (x : ℝ) ≤ 5 / 6) : upperEndpointCorrection b hb x = x := by
  let a : unitInterval :=
    ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩
  have ha : (a : ℝ) < 1 / 6 := by dsimp [a]; linarith
  let xr : unitInterval :=
    ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩
  have hxr : (1 / 6 : ℝ) ≤ xr := by dsimp [xr]; linarith
  apply Subtype.ext
  change 1 - (lowerEndpointCorrection a ha xr : ℝ) = (x : ℝ)
  rw [lowerEndpointCorrection_eq_self_of_one_sixth_le a ha xr hxr]
  dsimp [xr]
  ring

public theorem upperEndpointCorrection_mem_vertexBand_iff_of_half_le
    (b : unitInterval) (hb : 5 / 6 < (b : ℝ)) (x : unitInterval)
    (hx : (1 / 2 : ℝ) ≤ x) :
    upperEndpointCorrection b hb x ∈ vertexBand ↔ x ∈ vertexBand := by
  have hout : (1 / 2 : ℝ) ≤ upperEndpointCorrection b hb x := by
    let a : unitInterval :=
      ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩
    have ha : (a : ℝ) < 1 / 6 := by dsimp [a]; linarith
    let xr : unitInterval :=
      ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩
    change 1 / 2 ≤ 1 - (lowerEndpointCorrection a ha xr : ℝ)
    by_cases h : (1 / 6 : ℝ) ≤ 1 - (x : ℝ)
    · have hr : (1 / 6 : ℝ) ≤ xr := by exact h
      rw [lowerEndpointCorrection_eq_self_of_one_sixth_le a ha xr hr]
      change 1 / 2 ≤ 1 - (1 - (x : ℝ))
      linarith
    · have hsmall : (lowerEndpointCorrection a ha xr : ℝ) ≤ 1 / 6 := by
        rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue,
          ite_eq_left (le_of_not_ge h)]
        exact max_le (by norm_num) (min_le_left _ _)
      linarith
  change ((upperEndpointCorrection b hb x : ℝ) < 1 / 3 ∨
      2 / 3 < (upperEndpointCorrection b hb x : ℝ)) ↔
    ((x : ℝ) < 1 / 3 ∨ 2 / 3 < (x : ℝ))
  rw [or_iff_right (not_lt_of_ge ((by norm_num : (1 / 3 : ℝ) ≤ 1 / 2).trans hout)),
    or_iff_right (not_lt_of_ge ((by norm_num : (1 / 3 : ℝ) ≤ 1 / 2).trans hx)),
    two_thirds_lt_upperEndpointCorrection_iff]

public theorem upperEndpointCorrection_mem_edgeBand_iff_of_half_le
    (b : unitInterval) (hb : 5 / 6 < (b : ℝ)) (x : unitInterval)
    (hx : (1 / 2 : ℝ) ≤ x) :
    upperEndpointCorrection b hb x ∈ edgeBand ↔ x ∈ edgeBand := by
  have hout : (1 / 2 : ℝ) ≤ upperEndpointCorrection b hb x := by
    let a : unitInterval :=
      ⟨1 - (b : ℝ), by constructor <;> linarith [b.2.1, b.2.2]⟩
    have ha : (a : ℝ) < 1 / 6 := by dsimp [a]; linarith
    let xr : unitInterval :=
      ⟨1 - (x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩
    change 1 / 2 ≤ 1 - (lowerEndpointCorrection a ha xr : ℝ)
    by_cases h : (1 / 6 : ℝ) ≤ 1 - (x : ℝ)
    · have hr : (1 / 6 : ℝ) ≤ xr := by exact h
      rw [lowerEndpointCorrection_eq_self_of_one_sixth_le a ha xr hr]
      change 1 / 2 ≤ 1 - (1 - (x : ℝ))
      linarith
    · have hsmall : (lowerEndpointCorrection a ha xr : ℝ) ≤ 1 / 6 := by
        rw [lowerEndpointCorrection_coe, lowerEndpointCorrectionValue,
          ite_eq_left (le_of_not_ge h)]
        exact max_le (by norm_num) (min_le_left _ _)
      linarith
  change (1 / 6 < (upperEndpointCorrection b hb x : ℝ) ∧
      (upperEndpointCorrection b hb x : ℝ) < 5 / 6) ↔
    (1 / 6 < (x : ℝ) ∧ (x : ℝ) < 5 / 6)
  rw [and_iff_right (lt_of_lt_of_le (by norm_num) hout),
    and_iff_right (lt_of_lt_of_le (by norm_num) hx),
    upperEndpointCorrection_lt_five_sixths_iff]

public noncomputable def upperEndpointCorrectionFamily {X : Type*} [TopologicalSpace X]
    (b x : C(X, unitInterval)) (hb : ∀ z, 5 / 6 < (b z : ℝ)) : C(X, unitInterval) := by
  let rb : C(X, unitInterval) :=
    ⟨fun z => ⟨1 - (b z : ℝ), by
        constructor <;> linarith [(b z).2.1, (b z).2.2]⟩,
      by apply Continuous.subtype_mk; fun_prop⟩
  let rx : C(X, unitInterval) :=
    ⟨fun z => ⟨1 - (x z : ℝ), by
        constructor <;> linarith [(x z).2.1, (x z).2.2]⟩,
      by apply Continuous.subtype_mk; fun_prop⟩
  let lower := lowerEndpointCorrectionFamily rb rx (fun z => by dsimp [rb]; linarith [hb z])
  exact
    ⟨fun z => ⟨1 - (lower z : ℝ), by
        constructor <;> linarith [(lower z).2.1, (lower z).2.2]⟩,
      by apply Continuous.subtype_mk; fun_prop⟩

@[simp]
public theorem upperEndpointCorrectionFamily_apply {X : Type*} [TopologicalSpace X]
    (b x : C(X, unitInterval)) (hb : ∀ z, 5 / 6 < (b z : ℝ)) (z : X) :
    upperEndpointCorrectionFamily b x hb z = upperEndpointCorrection (b z) (hb z) (x z) := by
  rfl

namespace Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData

open MappingTorusDegreeOneCoverComparison

variable {A : PaperAnalyticData}

public theorem heightToLowerPhase_lt_one_sixth_iff (h : ℝ) :
    (heightToLowerPhase h : ℝ) < 1 / 6 ↔ 2 / 3 < h := by
  change max 0 (min (1 / 2) ((1 - h) / 2)) < 1 / 6 ↔ _
  rw [max_lt_iff, min_lt_iff]
  constructor
  · rintro ⟨-, hfalse | hraw⟩
    · norm_num at hfalse
    · norm_num at hraw ⊢
      linarith
  · intro hh
    constructor
    · norm_num
    · right
      norm_num at hh ⊢
      linarith

public noncomputable def actualCuspCylinderHeight
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, ℝ) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let cylinder : C(unitInterval × G.Fiber, CircleMappingTorus G.clutching) :=
    circleMappingTorusCylinderProjection G.clutching
  let collar : C(unitInterval × G.Fiber, A.openEmbeddingStarData.collarSource 0) :=
    G.totalHomotopyEquiv.invFun.comp cylinder
  let central : C(unitInterval × G.Fiber, A.sectionSevenEllipticCentralImage) :=
    ⟨fun p =>
      ⟨R.twoDiscCover.cuspToEllipticInteriorMap (collar p),
        R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage _⟩,
      (R.twoDiscCover.cuspToEllipticInteriorMap.hom.continuous.comp
        collar.continuous).subtype_mk _⟩
  exact ⟨fun p => A.sectionSevenEllipticCentralHeight (central p),
    A.sectionSevenEllipticCentralHeight_continuous.comp central.continuous⟩

@[simp]
public theorem actualCuspCylinderHeight_apply
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    actualCuspCylinderHeight R p = actualCuspCylinderHeightLoop R p.2 p.1 := by
  rfl

public noncomputable def actualCuspLowerRawPhase
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact heightToLowerPhase.comp (actualCuspCylinderHeight R)

public noncomputable def actualCuspUpperRawPhase
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact heightToUpperPhase.comp (actualCuspCylinderHeight R)

public noncomputable def actualCuspCylinderStart
    (_R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval × G.Fiber) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact ⟨fun p => (0, p.2), continuous_const.prodMk continuous_snd⟩

public noncomputable def actualCuspCylinderEnd
    (_R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval × G.Fiber) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact ⟨fun p => (1, p.2), continuous_const.prodMk continuous_snd⟩

public noncomputable def actualCuspLowerEndpointParameter
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (actualCuspLowerRawPhase R).comp (actualCuspCylinderStart R)

public noncomputable def actualCuspUpperEndpointParameter
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact (actualCuspUpperRawPhase R).comp (actualCuspCylinderEnd R)

public theorem actualCuspLowerEndpointParameter_lt_one_sixth
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    (actualCuspLowerEndpointParameter R p : ℝ) < 1 / 6 := by
  change (heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 0) : ℝ) < 1 / 6
  rw [heightToLowerPhase_lt_one_sixth_iff]
  exact two_thirds_lt_actualCuspCylinderHeightLoop_zero R p.2

public theorem five_sixths_lt_actualCuspUpperEndpointParameter
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    5 / 6 < (actualCuspUpperEndpointParameter R p : ℝ) := by
  change 5 / 6 < 1 - (heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 1) : ℝ)
  have hlow : (heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 1) : ℝ) < 1 / 6 :=
    (heightToLowerPhase_lt_one_sixth_iff _).2
      (two_thirds_lt_actualCuspCylinderHeightLoop_one R p.2)
  norm_num at hlow ⊢
  linarith

public noncomputable def actualCuspCorrectedLowerPhase
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact lowerEndpointCorrectionFamily (actualCuspLowerEndpointParameter R)
    (actualCuspLowerRawPhase R) (actualCuspLowerEndpointParameter_lt_one_sixth R)

public noncomputable def actualCuspCorrectedUpperPhase
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact upperEndpointCorrectionFamily (actualCuspUpperEndpointParameter R)
    (actualCuspUpperRawPhase R) (five_sixths_lt_actualCuspUpperEndpointParameter R)

public theorem actualCuspCorrectedPhases_agree_at_five_sixteenths
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
    actualCuspCorrectedLowerPhase R (m, y) = actualCuspCorrectedUpperPhase R (m, y) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
  change actualCuspCorrectedLowerPhase R (m, y) =
    actualCuspCorrectedUpperPhase R (m, y)
  have hmid : heightToLowerPhase (actualCuspCylinderHeightLoop R y m) =
      (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval) := by
    have hagree := actualCuspHeightPhaseCharts_agree_at_five_sixteenths R y
    change heightToLowerPhase (actualCuspCylinderHeightLoop R y m) =
      heightToUpperPhase (actualCuspCylinderHeightLoop R y m) at hagree
    apply Subtype.ext
    have hcoe := congrArg Subtype.val hagree
    change (heightToLowerPhase (actualCuspCylinderHeightLoop R y m) : ℝ) =
      1 - (heightToLowerPhase (actualCuspCylinderHeightLoop R y m) : ℝ) at hcoe
    norm_num at hcoe ⊢
    linarith
  rw [actualCuspCorrectedLowerPhase, lowerEndpointCorrectionFamily_apply,
    lowerEndpointCorrection_eq_self_of_one_sixth_le _ _ _ (by
      change (1 / 6 : ℝ) ≤ heightToLowerPhase (actualCuspCylinderHeightLoop R y m)
      rw [hmid]
      norm_num)]
  rw [actualCuspCorrectedUpperPhase, upperEndpointCorrectionFamily_apply,
    upperEndpointCorrection_eq_self_of_le_five_sixths _ _ _ (by
      change 1 - (heightToLowerPhase (actualCuspCylinderHeightLoop R y m) : ℝ) ≤ 5 / 6
      rw [hmid]
      norm_num)]
  exact actualCuspHeightPhaseCharts_agree_at_five_sixteenths R y

public noncomputable def actualCuspAdaptivePhase
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(unitInterval × G.Fiber, unitInterval) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
  exact
    ⟨fun p => if p.1 ≤ m then actualCuspCorrectedLowerPhase R p
        else actualCuspCorrectedUpperPhase R p,
      by
        apply continuous_if_le continuous_fst continuous_const
        · exact (actualCuspCorrectedLowerPhase R).continuous.continuousOn
        · exact (actualCuspCorrectedUpperPhase R).continuous.continuousOn
        · intro p hp
          rcases p with ⟨t, y⟩
          dsimp at hp ⊢
          subst t
          exact actualCuspCorrectedPhases_agree_at_five_sixteenths R y⟩

@[simp]
public theorem actualCuspAdaptivePhase_apply
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
    actualCuspAdaptivePhase R p = if p.1 ≤ m then
      actualCuspCorrectedLowerPhase R p else actualCuspCorrectedUpperPhase R p := by
  rfl

public theorem actualCuspAdaptivePhase_zero
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) : actualCuspAdaptivePhase R (0, y) = 0 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspAdaptivePhase_apply, ite_eq_left (by norm_num)]
  rw [actualCuspCorrectedLowerPhase, lowerEndpointCorrectionFamily_apply]
  apply lowerEndpointCorrection_self

public theorem actualCuspAdaptivePhase_one
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) : actualCuspAdaptivePhase R (1, y) = 1 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  have hnot : ¬ (1 : unitInterval) ≤
      (⟨5 / 16, by constructor <;> norm_num⟩ : unitInterval) := by
    intro h
    change (1 : ℝ) ≤ 5 / 16 at h
    norm_num at h
  rw [actualCuspAdaptivePhase_apply, ite_eq_right hnot]
  rw [actualCuspCorrectedUpperPhase, upperEndpointCorrectionFamily_apply]
  apply upperEndpointCorrection_self

public theorem actualCuspAdaptivePhase_mem_vertexBand_iff
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspAdaptivePhase R p ∈ vertexBand ↔
      circleMappingTorusCylinderProjection G.clutching p ∈
        actualCuspMappingTorusOrderFourOpen R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
  by_cases hp : p.1 ≤ m
  · rw [actualCuspAdaptivePhase_apply, ite_eq_left hp, actualCuspCorrectedLowerPhase,
      lowerEndpointCorrectionFamily_apply]
    change lowerEndpointCorrection _ _
        (heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 p.1)) ∈ vertexBand ↔ _
    rw [lowerEndpointCorrection_mem_vertexBand_iff_of_le_half _ _ _
      (heightToLowerPhase_le_half (actualCuspCylinderHeightLoop R p.2 p.1))]
    change heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 p.1) ∈ vertexBand ↔
      G.totalHomotopyEquiv.invFun
        (circleMappingTorusCylinderProjection G.clutching p) ∈
          R.twoDiscCover.cuspOrderFourOpen
    exact heightToLowerPhase_mem_vertexBand_iff_orderFourOpen R p.2 p.1
  · rw [actualCuspAdaptivePhase_apply, ite_eq_right hp, actualCuspCorrectedUpperPhase,
      upperEndpointCorrectionFamily_apply]
    change upperEndpointCorrection _ _
        (heightToUpperPhase (actualCuspCylinderHeightLoop R p.2 p.1)) ∈ vertexBand ↔ _
    rw [upperEndpointCorrection_mem_vertexBand_iff_of_half_le _ _ _ (by
        change (1 / 2 : ℝ) ≤ 1 -
          (heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 p.1) : ℝ)
        linarith [heightToLowerPhase_le_half (actualCuspCylinderHeightLoop R p.2 p.1)])]
    rw [heightToUpperPhase_mem_vertexBand_iff, ← heightToLowerPhase_mem_vertexBand_iff,
      ]
    change heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 p.1) ∈ vertexBand ↔
      G.totalHomotopyEquiv.invFun
        (circleMappingTorusCylinderProjection G.clutching p) ∈
          R.twoDiscCover.cuspOrderFourOpen
    exact heightToLowerPhase_mem_vertexBand_iff_orderFourOpen R p.2 p.1

public theorem actualCuspAdaptivePhase_mem_edgeBand_iff
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspAdaptivePhase R p ∈ edgeBand ↔
      circleMappingTorusCylinderProjection G.clutching p ∈
        actualCuspMappingTorusOrderThreeOpen R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
  by_cases hp : p.1 ≤ m
  · rw [actualCuspAdaptivePhase_apply, ite_eq_left hp, actualCuspCorrectedLowerPhase,
      lowerEndpointCorrectionFamily_apply]
    change lowerEndpointCorrection _ _
        (heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 p.1)) ∈ edgeBand ↔ _
    rw [lowerEndpointCorrection_mem_edgeBand_iff_of_le_half _ _ _
      (heightToLowerPhase_le_half (actualCuspCylinderHeightLoop R p.2 p.1))]
    change heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 p.1) ∈ edgeBand ↔
      G.totalHomotopyEquiv.invFun
        (circleMappingTorusCylinderProjection G.clutching p) ∈
          R.twoDiscCover.cuspOrderThreeOpen
    exact heightToLowerPhase_mem_edgeBand_iff_orderThreeOpen R p.2 p.1
  · rw [actualCuspAdaptivePhase_apply, ite_eq_right hp, actualCuspCorrectedUpperPhase,
      upperEndpointCorrectionFamily_apply]
    change upperEndpointCorrection _ _
        (heightToUpperPhase (actualCuspCylinderHeightLoop R p.2 p.1)) ∈ edgeBand ↔ _
    rw [upperEndpointCorrection_mem_edgeBand_iff_of_half_le _ _ _ (by
        change (1 / 2 : ℝ) ≤ 1 -
          (heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 p.1) : ℝ)
        linarith [heightToLowerPhase_le_half (actualCuspCylinderHeightLoop R p.2 p.1)])]
    rw [heightToUpperPhase_mem_edgeBand_iff, ← heightToLowerPhase_mem_edgeBand_iff,
      ]
    change heightToLowerPhase (actualCuspCylinderHeightLoop R p.2 p.1) ∈ edgeBand ↔
      G.totalHomotopyEquiv.invFun
        (circleMappingTorusCylinderProjection G.clutching p) ∈
          R.twoDiscCover.cuspOrderThreeOpen
    exact heightToLowerPhase_mem_edgeBand_iff_orderThreeOpen R p.2 p.1

public noncomputable def actualCuspAdaptiveCoverDegreeOneSelfMap
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspAdaptiveCoverDegreeOneSelfMap R :=
  actualCuspAdaptiveCoverDegreeOneSelfMapOfPhase R (actualCuspAdaptivePhase R)
    (actualCuspAdaptivePhase_zero R) (actualCuspAdaptivePhase_one R)
    (actualCuspAdaptivePhase_mem_vertexBand_iff R)
    (actualCuspAdaptivePhase_mem_edgeBand_iff R)

public theorem actualCuspAdaptiveCover_actual_boundary_eq_wang
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspAdaptiveCoverDegreeOneSelfMap R).actualSourceRead.comp
        ((actualCuspMappingTorusPulledBackSwappedHomologyComparison R).boundaryHom 1) =
      (circleMappingTorusWangPresentationOfCover G.clutching 1).boundary :=
  (actualCuspAdaptiveCoverDegreeOneSelfMap R).actual_boundary_eq_wang R

end Geometry.PaperAnalyticData.SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex

end

end
