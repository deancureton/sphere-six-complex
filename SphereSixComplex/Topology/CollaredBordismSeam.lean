module

public import SphereSixComplex.Topology.CollaredBordismQuotient
public import SphereSixComplex.Topology.CylinderSeam

/-!
# A signed bicollar around a glued bordism seam

For two explicitly collared bordisms, this file identifies the two half-collars at their common
end with a single open cylinder.  The midpoint of the open cylinder is the glued boundary, its
left half runs backwards through the outgoing collar of the first bordism, and its right half
runs forwards through the incoming collar of the second bordism.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SphereSixComplex
namespace SmoothCollaredBordism
namespace QuotientGluing

universe uE uH uM₀ uM₁ uM₂ uW₀₁ uW₁₂

variable {E : Type uE} {H : Type uH} {M₀ : Type uM₀} {M₁ : Type uM₁}
  {M₂ : Type uM₂}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M₀] [T2Space M₀] [SecondCountableTopology M₀]
  [ChartedSpace H M₀] [IsManifold I ∞ M₀] [CompactSpace M₀]
  [BoundarylessManifold I M₀]
  [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
  [ChartedSpace H M₁] [IsManifold I ∞ M₁] [CompactSpace M₁]
  [BoundarylessManifold I M₁]
  [TopologicalSpace M₂] [T2Space M₂] [SecondCountableTopology M₂]
  [ChartedSpace H M₂] [IsManifold I ∞ M₂] [CompactSpace M₂]
  [BoundarylessManifold I M₂]

variable
  (B₀₁ : SmoothCollaredBordism.{uE, uH, uW₀₁, uM₀, uM₁} I M₀ M₁)
  (B₁₂ : SmoothCollaredBordism.{uE, uH, uW₁₂, uM₁, uM₂} I M₁ M₂)

/-- The real coordinate of an interior collar parameter. -/
public def seamCoordinate (t : OpenCollarParameter) : ℝ :=
  (t.1 : ℝ)

@[simp]
public theorem seamCoordinate_apply (t : OpenCollarParameter) :
    seamCoordinate t = (t.1 : ℝ) :=
  rfl

public theorem continuous_seamCoordinate : Continuous seamCoordinate :=
  continuous_subtype_val.comp continuous_subtype_val

/-- The outgoing-collar radius on the left side of the signed seam.  The `max` extends the
formula continuously across the midpoint, where this auxiliary map is constant zero. -/
public def seamLeftRadius (t : OpenCollarParameter) : HalfCollarParameter :=
  ⟨⟨max 0 (1 - 2 * seamCoordinate t), by
      change 0 ≤ max 0 (1 - 2 * seamCoordinate t) ∧
        max 0 (1 - 2 * seamCoordinate t) ≤ 1
      constructor
      · exact le_max_left (0 : ℝ) _
      · exact max_le (by norm_num) (by
          have ht := t.2.1
          change 0 < seamCoordinate t at ht
          linarith)⟩, by
    change max 0 (1 - 2 * seamCoordinate t) < 1
    rw [max_lt_iff]
    constructor
    · norm_num
    · have ht := t.2.1
      change 0 < seamCoordinate t at ht
      linarith⟩

/-- The incoming-collar radius on the right side of the signed seam.  The `max` extends the
formula continuously across the midpoint, where this auxiliary map is constant zero. -/
public def seamRightRadius (t : OpenCollarParameter) : HalfCollarParameter :=
  ⟨⟨max 0 (2 * seamCoordinate t - 1), by
      change 0 ≤ max 0 (2 * seamCoordinate t - 1) ∧
        max 0 (2 * seamCoordinate t - 1) ≤ 1
      constructor
      · exact le_max_left (0 : ℝ) _
      · exact max_le (by norm_num) (by
          have ht := t.2.2
          change seamCoordinate t < 1 at ht
          linarith)⟩, by
    change max 0 (2 * seamCoordinate t - 1) < 1
    rw [max_lt_iff]
    constructor
    · norm_num
    · have ht := t.2.2
      change seamCoordinate t < 1 at ht
      linarith⟩

@[simp]
public theorem seamLeftRadius_val (t : OpenCollarParameter) :
    ((seamLeftRadius t : CollarParameter) : ℝ) = max 0 (1 - 2 * seamCoordinate t) :=
  rfl

@[simp]
public theorem seamRightRadius_val (t : OpenCollarParameter) :
    ((seamRightRadius t : CollarParameter) : ℝ) = max 0 (2 * seamCoordinate t - 1) :=
  rfl

public theorem continuous_seamLeftRadius : Continuous seamLeftRadius := by
  change Continuous (fun t : OpenCollarParameter ↦
    (⟨⟨max 0 (1 - 2 * seamCoordinate t), _⟩, _⟩ : HalfCollarParameter))
  exact ((continuous_const.max
    (continuous_const.sub (continuous_const.mul continuous_seamCoordinate))).subtype_mk _).subtype_mk _

public theorem continuous_seamRightRadius : Continuous seamRightRadius := by
  change Continuous (fun t : OpenCollarParameter ↦
    (⟨⟨max 0 (2 * seamCoordinate t - 1), _⟩, _⟩ : HalfCollarParameter))
  exact ((continuous_const.max
    ((continuous_const.mul continuous_seamCoordinate).sub continuous_const)).subtype_mk _).subtype_mk _

/-- Equality of real coordinates determines an interior collar parameter. -/
public theorem openCollarParameter_ext {s t : OpenCollarParameter}
    (h : seamCoordinate s = seamCoordinate t) : s = t := by
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- On the left half, the auxiliary radius is the expected affine expression. -/
public theorem seamLeftRadius_eq_of_le {t : OpenCollarParameter}
    (ht : seamCoordinate t ≤ 1 / 2) :
    ((seamLeftRadius t : CollarParameter) : ℝ) = 1 - 2 * seamCoordinate t := by
  rw [seamLeftRadius_val, max_eq_right]
  linarith

/-- On the right half, the auxiliary radius is the expected affine expression. -/
public theorem seamRightRadius_eq_of_ge {t : OpenCollarParameter}
    (ht : 1 / 2 ≤ seamCoordinate t) :
    ((seamRightRadius t : CollarParameter) : ℝ) = 2 * seamCoordinate t - 1 := by
  rw [seamRightRadius_val, max_eq_right]
  linarith

/-- The left radius vanishes exactly at the midpoint of the left half. -/
public theorem seamLeftRadius_eq_start_iff {t : OpenCollarParameter}
    (ht : seamCoordinate t ≤ 1 / 2) :
    seamLeftRadius t = halfCollarStart ↔ seamCoordinate t = 1 / 2 := by
  constructor
  · intro h
    have hv := congrArg (fun r : HalfCollarParameter ↦ ((r.1 : CollarParameter) : ℝ)) h
    rw [seamLeftRadius_eq_of_le ht] at hv
    change 1 - 2 * seamCoordinate t = 0 at hv
    linarith
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    rw [seamLeftRadius_eq_of_le ht]
    change 1 - 2 * seamCoordinate t = 0
    linarith

/-- The right radius vanishes exactly at the midpoint of the right half. -/
public theorem seamRightRadius_eq_start_iff {t : OpenCollarParameter}
    (ht : 1 / 2 ≤ seamCoordinate t) :
    seamRightRadius t = halfCollarStart ↔ seamCoordinate t = 1 / 2 := by
  constructor
  · intro h
    have hv := congrArg (fun r : HalfCollarParameter ↦ ((r.1 : CollarParameter) : ℝ)) h
    rw [seamRightRadius_eq_of_ge ht] at hv
    change 2 * seamCoordinate t - 1 = 0 at hv
    linarith
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    rw [seamRightRadius_eq_of_ge ht]
    change 2 * seamCoordinate t - 1 = 0
    linarith

/-- The left affine radius is injective on the closed left half. -/
public theorem seamLeftRadius_injective_on {s t : OpenCollarParameter}
    (hs : seamCoordinate s ≤ 1 / 2) (ht : seamCoordinate t ≤ 1 / 2)
    (h : seamLeftRadius s = seamLeftRadius t) : s = t := by
  apply openCollarParameter_ext
  have hv := congrArg (fun r : HalfCollarParameter ↦ ((r.1 : CollarParameter) : ℝ)) h
  rw [seamLeftRadius_eq_of_le hs, seamLeftRadius_eq_of_le ht] at hv
  linarith

/-- The right affine radius is injective on the closed right half. -/
public theorem seamRightRadius_injective_on {s t : OpenCollarParameter}
    (hs : 1 / 2 ≤ seamCoordinate s) (ht : 1 / 2 ≤ seamCoordinate t)
    (h : seamRightRadius s = seamRightRadius t) : s = t := by
  apply openCollarParameter_ext
  have hv := congrArg (fun r : HalfCollarParameter ↦ ((r.1 : CollarParameter) : ℝ)) h
  rw [seamRightRadius_eq_of_ge hs, seamRightRadius_eq_of_ge ht] at hv
  linarith

/-- The left-side collar map before the two halves are pasted at the midpoint. -/
public def seamLeftMap (p : M₁ × OpenCollarParameter) : Glue B₀₁ B₁₂ :=
  toGlueLeft B₀₁ B₁₂ (B₀₁.outgoing.chart (p.1, seamLeftRadius p.2))

/-- The right-side collar map before the two halves are pasted at the midpoint. -/
public def seamRightMap (p : M₁ × OpenCollarParameter) : Glue B₀₁ B₁₂ :=
  toGlueRight B₀₁ B₁₂ (B₁₂.incoming.chart (p.1, seamRightRadius p.2))

public theorem continuous_seamLeftMap : Continuous (seamLeftMap B₀₁ B₁₂) := by
  exact (toGlueLeft_isClosedEmbedding B₀₁ B₁₂).continuous.comp
    (B₀₁.outgoing.chart.contMDiff.continuous.comp
      (continuous_fst.prodMk (continuous_seamLeftRadius.comp continuous_snd)))

public theorem continuous_seamRightMap : Continuous (seamRightMap B₀₁ B₁₂) := by
  exact (toGlueRight_isClosedEmbedding B₀₁ B₁₂).continuous.comp
    (B₁₂.incoming.chart.contMDiff.continuous.comp
      (continuous_fst.prodMk (continuous_seamRightRadius.comp continuous_snd)))

/-- The closed left half of the signed seam cylinder. -/
public def seamLeftRegion : Set (M₁ × OpenCollarParameter) :=
  {p | seamCoordinate p.2 ≤ 1 / 2}

/-- The closed right half of the signed seam cylinder. -/
public def seamRightRegion : Set (M₁ × OpenCollarParameter) :=
  {p | 1 / 2 ≤ seamCoordinate p.2}

public theorem isClosed_seamLeftRegion : IsClosed (seamLeftRegion (M₁ := M₁)) := by
  exact isClosed_le (continuous_seamCoordinate.comp continuous_snd) continuous_const

public theorem isClosed_seamRightRegion : IsClosed (seamRightRegion (M₁ := M₁)) := by
  exact isClosed_le continuous_const (continuous_seamCoordinate.comp continuous_snd)

public theorem seamLeftRegion_union_right :
    seamLeftRegion (M₁ := M₁) ∪ seamRightRegion (M₁ := M₁) = Set.univ := by
  ext p
  simp only [seamLeftRegion, seamRightRegion, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact le_total _ _

/-- The two collar charts agree in the quotient at the seam midpoint. -/
public theorem seamLeftMap_eq_seamRightMap_of_midpoint
    (p : M₁ × OpenCollarParameter) (hp : seamCoordinate p.2 = 1 / 2) :
    seamLeftMap B₀₁ B₁₂ p = seamRightMap B₀₁ B₁₂ p := by
  have hl : seamLeftRadius p.2 = halfCollarStart :=
    (seamLeftRadius_eq_start_iff (le_of_eq hp)).2 hp
  have hr : seamRightRadius p.2 = halfCollarStart :=
    (seamRightRadius_eq_start_iff (le_of_eq hp.symm)).2 hp
  rw [seamLeftMap, seamRightMap, hl, hr]
  exact toGlue_commute B₀₁ B₁₂ p.1

/-- The signed bicollar map into the direct quotient. -/
public def signedSeamMap (p : M₁ × OpenCollarParameter) : Glue B₀₁ B₁₂ :=
  if seamCoordinate p.2 ≤ 1 / 2 then seamLeftMap B₀₁ B₁₂ p
  else seamRightMap B₀₁ B₁₂ p

public theorem signedSeamMap_eq_left {p : M₁ × OpenCollarParameter}
    (hp : seamCoordinate p.2 ≤ 1 / 2) :
    signedSeamMap B₀₁ B₁₂ p = seamLeftMap B₀₁ B₁₂ p := by
  unfold signedSeamMap
  rw [if_pos hp]

public theorem signedSeamMap_eq_right {p : M₁ × OpenCollarParameter}
    (hp : 1 / 2 < seamCoordinate p.2) :
    signedSeamMap B₀₁ B₁₂ p = seamRightMap B₀₁ B₁₂ p := by
  unfold signedSeamMap
  rw [if_neg (not_le.mpr hp)]

/-- The signed bicollar map is continuous across the identified zero sections. -/
public theorem continuous_signedSeamMap : Continuous (signedSeamMap B₀₁ B₁₂) := by
  rw [← continuousOn_univ]
  rw [← seamLeftRegion_union_right (M₁ := M₁)]
  apply ContinuousOn.union_of_isClosed
      (hs := isClosed_seamLeftRegion (M₁ := M₁))
      (ht := isClosed_seamRightRegion (M₁ := M₁))
  · exact (continuous_seamLeftMap B₀₁ B₁₂).continuousOn.congr fun p hp ↦ by
      exact signedSeamMap_eq_left B₀₁ B₁₂ hp
  · apply (continuous_seamRightMap B₀₁ B₁₂).continuousOn.congr
    intro p hp
    by_cases hleft : seamCoordinate p.2 ≤ 1 / 2
    · have hmid : seamCoordinate p.2 = 1 / 2 := le_antisymm hleft hp
      rw [signedSeamMap_eq_left B₀₁ B₁₂ hleft]
      exact seamLeftMap_eq_seamRightMap_of_midpoint B₀₁ B₁₂ p hmid
    · exact signedSeamMap_eq_right B₀₁ B₁₂ (lt_of_not_ge hleft)

/-- The signed bicollar has no self-identifications beyond the intended seam identification. -/
public theorem signedSeamMap_injective : Injective (signedSeamMap B₀₁ B₁₂) := by
  intro p q hpq
  by_cases hp : seamCoordinate p.2 ≤ 1 / 2
  · by_cases hq : seamCoordinate q.2 ≤ 1 / 2
    · rw [signedSeamMap_eq_left B₀₁ B₁₂ hp,
          signedSeamMap_eq_left B₀₁ B₁₂ hq] at hpq
      have hcharts := (toGlueLeft_isClosedEmbedding B₀₁ B₁₂).injective hpq
      have hsources := B₀₁.outgoing.chart.isOpenEmbedding.injective hcharts
      have hx : p.1 = q.1 :=
        congrArg (fun z : M₁ × HalfCollarParameter ↦ z.1) hsources
      have hr : seamLeftRadius p.2 = seamLeftRadius q.2 :=
        congrArg (fun z : M₁ × HalfCollarParameter ↦ z.2) hsources
      exact Prod.ext hx (seamLeftRadius_injective_on hp hq hr)
    · have hqr : 1 / 2 < seamCoordinate q.2 := lt_of_not_ge hq
      rw [signedSeamMap_eq_left B₀₁ B₁₂ hp,
          signedSeamMap_eq_right B₀₁ B₁₂ hqr] at hpq
      obtain ⟨z, -, hzright⟩ :=
        (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂ _ _).1 hpq
      have hsources : (z, halfCollarStart) = (q.1, seamRightRadius q.2) :=
        B₁₂.incoming.chart.isOpenEmbedding.injective hzright
      have hr : seamRightRadius q.2 = halfCollarStart := (congrArg Prod.snd hsources).symm
      have hmid := (seamRightRadius_eq_start_iff (le_of_lt hqr)).1 hr
      exact False.elim (ne_of_gt hqr hmid)
  · have hpr : 1 / 2 < seamCoordinate p.2 := lt_of_not_ge hp
    by_cases hq : seamCoordinate q.2 ≤ 1 / 2
    · rw [signedSeamMap_eq_right B₀₁ B₁₂ hpr,
          signedSeamMap_eq_left B₀₁ B₁₂ hq] at hpq
      obtain ⟨z, -, hzright⟩ :=
        (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂ _ _).1 hpq.symm
      have hsources : (z, halfCollarStart) = (p.1, seamRightRadius p.2) :=
        B₁₂.incoming.chart.isOpenEmbedding.injective hzright
      have hr : seamRightRadius p.2 = halfCollarStart := (congrArg Prod.snd hsources).symm
      have hmid := (seamRightRadius_eq_start_iff (le_of_lt hpr)).1 hr
      exact False.elim (ne_of_gt hpr hmid)
    · have hqr : 1 / 2 < seamCoordinate q.2 := lt_of_not_ge hq
      rw [signedSeamMap_eq_right B₀₁ B₁₂ hpr,
          signedSeamMap_eq_right B₀₁ B₁₂ hqr] at hpq
      have hcharts := (toGlueRight_isClosedEmbedding B₀₁ B₁₂).injective hpq
      have hsources := B₁₂.incoming.chart.isOpenEmbedding.injective hcharts
      have hx : p.1 = q.1 :=
        congrArg (fun z : M₁ × HalfCollarParameter ↦ z.1) hsources
      have hr : seamRightRadius p.2 = seamRightRadius q.2 :=
        congrArg (fun z : M₁ × HalfCollarParameter ↦ z.2) hsources
      exact Prod.ext hx (seamRightRadius_injective_on (le_of_lt hpr) (le_of_lt hqr) hr)

/-- Convert a point of a left half-collar to its signed seam coordinate. -/
public def seamFromLeftCollarSource (p : CollarSource M₁) :
    M₁ × OpenCollarParameter :=
  (p.1, ⟨⟨(1 - ((p.2.1 : CollarParameter) : ℝ)) / 2, by
      constructor
      · have hp := p.2.1.property.2
        linarith
      · have hp := p.2.1.property.1
        linarith⟩, by
    constructor
    · have hp := p.2.2
      change ((p.2.1 : CollarParameter) : ℝ) < 1 at hp
      linarith
    · have hp := p.2.1.property.1
      linarith⟩)

/-- Convert a point of a right half-collar to its signed seam coordinate. -/
public def seamFromRightCollarSource (p : CollarSource M₁) :
    M₁ × OpenCollarParameter :=
  (p.1, ⟨⟨(((p.2.1 : CollarParameter) : ℝ) + 1) / 2, by
      constructor
      · have hp := p.2.1.property.1
        linarith
      · have hp := p.2.1.property.2
        linarith⟩, by
    constructor
    · have hp := p.2.1.property.1
      linarith
    · have hp := p.2.2
      change ((p.2.1 : CollarParameter) : ℝ) < 1 at hp
      linarith⟩)

@[simp]
public theorem seamFromLeftCollarSource_fst (p : CollarSource M₁) :
    (seamFromLeftCollarSource p).1 = p.1 :=
  rfl

@[simp]
public theorem seamFromRightCollarSource_fst (p : CollarSource M₁) :
    (seamFromRightCollarSource p).1 = p.1 :=
  rfl

@[simp]
public theorem seamCoordinate_fromLeftCollarSource (p : CollarSource M₁) :
    seamCoordinate (seamFromLeftCollarSource p).2 =
      (1 - ((p.2.1 : CollarParameter) : ℝ)) / 2 :=
  rfl

@[simp]
public theorem seamCoordinate_fromRightCollarSource (p : CollarSource M₁) :
    seamCoordinate (seamFromRightCollarSource p).2 =
      (((p.2.1 : CollarParameter) : ℝ) + 1) / 2 :=
  rfl

public theorem continuous_seamFromLeftCollarSource :
    Continuous (seamFromLeftCollarSource : CollarSource M₁ →
      M₁ × OpenCollarParameter) := by
  apply continuous_fst.prodMk
  change Continuous (fun p : CollarSource M₁ ↦
    (⟨⟨(1 - ((p.2.1 : CollarParameter) : ℝ)) / 2, _⟩, _⟩ : OpenCollarParameter))
  exact ((continuous_const.sub
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).div_const 2
      |>.subtype_mk _).subtype_mk _

public theorem continuous_seamFromRightCollarSource :
    Continuous (seamFromRightCollarSource : CollarSource M₁ →
      M₁ × OpenCollarParameter) := by
  apply continuous_fst.prodMk
  change Continuous (fun p : CollarSource M₁ ↦
    (⟨⟨(((p.2.1 : CollarParameter) : ℝ) + 1) / 2, _⟩, _⟩ : OpenCollarParameter))
  exact (((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).add
    continuous_const).div_const 2 |>.subtype_mk _).subtype_mk _

public theorem seamFromLeftCollarSource_mem_left (p : CollarSource M₁) :
    seamCoordinate (seamFromLeftCollarSource p).2 ≤ 1 / 2 := by
  rw [seamCoordinate_fromLeftCollarSource]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 (by
    have hp := p.2.1.property.1
    linarith)

public theorem seamFromRightCollarSource_mem_right (p : CollarSource M₁) :
    1 / 2 ≤ seamCoordinate (seamFromRightCollarSource p).2 := by
  rw [seamCoordinate_fromRightCollarSource]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 (by
    have hp := p.2.1.property.1
    linarith)

@[simp]
public theorem seamLeftRadius_fromLeftCollarSource (p : CollarSource M₁) :
    seamLeftRadius (seamFromLeftCollarSource p).2 = p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [seamLeftRadius_eq_of_le (seamFromLeftCollarSource_mem_left p),
    seamCoordinate_fromLeftCollarSource]
  ring

@[simp]
public theorem seamRightRadius_fromRightCollarSource (p : CollarSource M₁) :
    seamRightRadius (seamFromRightCollarSource p).2 = p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [seamRightRadius_eq_of_ge (seamFromRightCollarSource_mem_right p),
    seamCoordinate_fromRightCollarSource]
  ring

public theorem seamFromLeftCollarSource_radius (x : M₁) (t : OpenCollarParameter)
    (ht : seamCoordinate t ≤ 1 / 2) :
    seamFromLeftCollarSource (x, seamLeftRadius t) = (x, t) := by
  apply Prod.ext
  · rfl
  · apply openCollarParameter_ext
    rw [seamCoordinate_fromLeftCollarSource, seamLeftRadius_eq_of_le ht]
    ring

public theorem seamFromRightCollarSource_radius (x : M₁) (t : OpenCollarParameter)
    (ht : 1 / 2 ≤ seamCoordinate t) :
    seamFromRightCollarSource (x, seamRightRadius t) = (x, t) := by
  apply Prod.ext
  · rfl
  · apply openCollarParameter_ext
    rw [seamCoordinate_fromRightCollarSource, seamRightRadius_eq_of_ge ht]
    ring

/-- On a left collar source, the signed seam map recovers the left quotient map. -/
@[simp]
public theorem signedSeamMap_fromLeftCollarSource (p : CollarSource M₁) :
    signedSeamMap B₀₁ B₁₂ (seamFromLeftCollarSource p) =
      toGlueLeft B₀₁ B₁₂ (B₀₁.outgoing.chart p) := by
  rw [signedSeamMap_eq_left B₀₁ B₁₂
    (seamFromLeftCollarSource_mem_left p)]
  simp [seamLeftMap]

/-- On a right collar source, the signed seam map recovers the right quotient map. -/
@[simp]
public theorem signedSeamMap_fromRightCollarSource (p : CollarSource M₁) :
    signedSeamMap B₀₁ B₁₂ (seamFromRightCollarSource p) =
      toGlueRight B₀₁ B₁₂ (B₁₂.incoming.chart p) := by
  have hright := seamFromRightCollarSource_mem_right p
  by_cases hleft : seamCoordinate (seamFromRightCollarSource p).2 ≤ 1 / 2
  · have hmid : seamCoordinate (seamFromRightCollarSource p).2 = 1 / 2 :=
      le_antisymm hleft hright
    rw [signedSeamMap_eq_left B₀₁ B₁₂ hleft,
      seamLeftMap_eq_seamRightMap_of_midpoint B₀₁ B₁₂ _ hmid]
    simp [seamRightMap]
  · rw [signedSeamMap_eq_right B₀₁ B₁₂ (lt_of_not_ge hleft)]
    simp [seamRightMap]

/-- The union of the two open collar targets in the quotient. -/
public def seamNeighborhood : Set (Glue B₀₁ B₁₂) :=
  toGlueLeft B₀₁ B₁₂ '' (B₀₁.outgoing.chart.target : Set B₀₁.W) ∪
    toGlueRight B₀₁ B₁₂ '' (B₁₂.incoming.chart.target : Set B₁₂.W)

/-- The range of the signed seam is exactly the union of the two collar targets. -/
public theorem range_signedSeamMap :
    Set.range (signedSeamMap B₀₁ B₁₂) = seamNeighborhood B₀₁ B₁₂ := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    by_cases hp : seamCoordinate p.2 ≤ 1 / 2
    · rw [signedSeamMap_eq_left B₀₁ B₁₂ hp]
      left
      refine ⟨B₀₁.outgoing.chart (p.1, seamLeftRadius p.2), ?_, rfl⟩
      exact (B₀₁.outgoing.chart.toDiffeomorph (p.1, seamLeftRadius p.2)).property
    · rw [signedSeamMap_eq_right B₀₁ B₁₂ (lt_of_not_ge hp)]
      right
      refine ⟨B₁₂.incoming.chart (p.1, seamRightRadius p.2), ?_, rfl⟩
      exact (B₁₂.incoming.chart.toDiffeomorph (p.1, seamRightRadius p.2)).property
  · rintro (hy | hy)
    · rcases hy with ⟨w, hw, rfl⟩
      let p : CollarSource M₁ :=
        B₀₁.outgoing.chart.toDiffeomorph.symm ⟨w, hw⟩
      refine ⟨seamFromLeftCollarSource p, ?_⟩
      rw [signedSeamMap_fromLeftCollarSource]
      change toGlueLeft B₀₁ B₁₂
        (B₀₁.outgoing.chart (B₀₁.outgoing.chart.toDiffeomorph.symm ⟨w, hw⟩)) = _
      congr 1
      exact congrArg Subtype.val
        (B₀₁.outgoing.chart.toDiffeomorph.apply_symm_apply ⟨w, hw⟩)
    · rcases hy with ⟨w, hw, rfl⟩
      let p : CollarSource M₁ :=
        B₁₂.incoming.chart.toDiffeomorph.symm ⟨w, hw⟩
      refine ⟨seamFromRightCollarSource p, ?_⟩
      rw [signedSeamMap_fromRightCollarSource]
      change toGlueRight B₀₁ B₁₂
        (B₁₂.incoming.chart (B₁₂.incoming.chart.toDiffeomorph.symm ⟨w, hw⟩)) = _
      congr 1
      exact congrArg Subtype.val
        (B₁₂.incoming.chart.toDiffeomorph.apply_symm_apply ⟨w, hw⟩)

/-- The preimage of the seam neighborhood under the quotient map is the disjoint union of the
two open collar targets. -/
public theorem preimage_quotientMk_seamNeighborhood :
    (fun w : B₀₁.W ⊕ B₁₂.W ↦ (Quotient.mk'' w : Glue B₀₁ B₁₂)) ⁻¹'
        seamNeighborhood B₀₁ B₁₂ =
      Sum.inl '' (B₀₁.outgoing.chart.target : Set B₀₁.W) ∪
        Sum.inr '' (B₁₂.incoming.chart.target : Set B₁₂.W) := by
  ext w
  rcases w with w | w
  · constructor
    · intro hw
      change toGlueLeft B₀₁ B₁₂ w ∈ seamNeighborhood B₀₁ B₁₂ at hw
      rcases hw with hw | hw
      · rcases hw with ⟨w', hw', heq⟩
        have : w' = w := (toGlueLeft_isClosedEmbedding B₀₁ B₁₂).injective heq
        subst w'
        exact Or.inl ⟨w, hw', rfl⟩
      · rcases hw with ⟨w', hw', heq⟩
        obtain ⟨z, hzleft, -⟩ :=
          (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂ w w').1 heq.symm
        have hzmem : B₀₁.outgoing.inclusion z ∈ B₀₁.outgoing.chart.target := by
          exact (B₀₁.outgoing.chart.toDiffeomorph (z, halfCollarStart)).property
        rw [← hzleft]
        exact Or.inl ⟨B₀₁.outgoing.inclusion z, hzmem, rfl⟩
    · intro hw
      rcases hw with hw | hw
      · rcases hw with ⟨w', hw', heq⟩
        have : w' = w := Sum.inl.inj heq
        subst w'
        exact Or.inl ⟨w, hw', rfl⟩
      · rcases hw with ⟨w', -, heq⟩
        exact (Sum.inr_ne_inl heq).elim
  · constructor
    · intro hw
      change toGlueRight B₀₁ B₁₂ w ∈ seamNeighborhood B₀₁ B₁₂ at hw
      rcases hw with hw | hw
      · rcases hw with ⟨w', hw', heq⟩
        obtain ⟨z, -, hzright⟩ :=
          (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂ w' w).1 heq
        have hzmem : B₁₂.incoming.inclusion z ∈ B₁₂.incoming.chart.target := by
          exact (B₁₂.incoming.chart.toDiffeomorph (z, halfCollarStart)).property
        rw [← hzright]
        exact Or.inr ⟨B₁₂.incoming.inclusion z, hzmem, rfl⟩
      · rcases hw with ⟨w', hw', heq⟩
        have : w' = w := (toGlueRight_isClosedEmbedding B₀₁ B₁₂).injective heq
        subst w'
        exact Or.inr ⟨w, hw', rfl⟩
    · intro hw
      rcases hw with hw | hw
      · rcases hw with ⟨w', -, heq⟩
        exact (Sum.inl_ne_inr heq).elim
      · rcases hw with ⟨w', hw', heq⟩
        have : w' = w := Sum.inr.inj heq
        subst w'
        exact Or.inr ⟨w, hw', rfl⟩

/-- The union of the two collar targets is an open neighborhood of the seam in the quotient. -/
public theorem isOpen_seamNeighborhood : IsOpen (seamNeighborhood B₀₁ B₁₂) := by
  have hq : IsQuotientMap
      (fun w : B₀₁.W ⊕ B₁₂.W ↦ (Quotient.mk'' w : Glue B₀₁ B₁₂)) :=
    isQuotientMap_quotient_mk'
  rw [← hq.isOpen_preimage,
    preimage_quotientMk_seamNeighborhood B₀₁ B₁₂]
  exact (isOpenMap_inl _ B₀₁.outgoing.chart.target.isOpen).union
    (isOpenMap_inr _ B₁₂.incoming.chart.target.isOpen)

/-- In particular, the range of the signed seam map is open. -/
public theorem isOpen_range_signedSeamMap :
    IsOpen (Set.range (signedSeamMap B₀₁ B₁₂)) := by
  rw [range_signedSeamMap B₀₁ B₁₂]
  exact isOpen_seamNeighborhood B₀₁ B₁₂

/-- Pulling an arbitrary subset of the seam cylinder back to the left summand is computed in the
outgoing collar chart. -/
public theorem toGlueLeft_mem_image_signedSeamMap_iff (U : Set (M₁ × OpenCollarParameter))
    (w : B₀₁.W) :
    toGlueLeft B₀₁ B₁₂ w ∈ signedSeamMap B₀₁ B₁₂ '' U ↔
      ∃ p : CollarSource M₁,
        B₀₁.outgoing.chart p = w ∧ seamFromLeftCollarSource p ∈ U := by
  constructor
  · rintro ⟨z, hzU, hz⟩
    by_cases hleft : seamCoordinate z.2 ≤ 1 / 2
    · rw [signedSeamMap_eq_left B₀₁ B₁₂ hleft] at hz
      have hchart : B₀₁.outgoing.chart (z.1, seamLeftRadius z.2) = w :=
        (toGlueLeft_isClosedEmbedding B₀₁ B₁₂).injective hz
      refine ⟨(z.1, seamLeftRadius z.2), hchart, ?_⟩
      rw [seamFromLeftCollarSource_radius z.1 z.2 hleft]
      exact hzU
    · have hright : 1 / 2 < seamCoordinate z.2 := lt_of_not_ge hleft
      rw [signedSeamMap_eq_right B₀₁ B₁₂ hright] at hz
      obtain ⟨a, -, haright⟩ :=
        (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂ w
          (B₁₂.incoming.chart (z.1, seamRightRadius z.2))).1 hz.symm
      have hsource : (a, halfCollarStart) = (z.1, seamRightRadius z.2) :=
        B₁₂.incoming.chart.isOpenEmbedding.injective haright
      have hr : seamRightRadius z.2 = halfCollarStart :=
        (congrArg (fun p : M₁ × HalfCollarParameter ↦ p.2) hsource).symm
      have hmid := (seamRightRadius_eq_start_iff (le_of_lt hright)).1 hr
      exact False.elim (ne_of_gt hright hmid)
  · rintro ⟨p, hpw, hpU⟩
    refine ⟨seamFromLeftCollarSource p, hpU, ?_⟩
    rw [signedSeamMap_fromLeftCollarSource B₀₁ B₁₂ p, hpw]

/-- Pulling an arbitrary subset of the seam cylinder back to the right summand is computed in the
incoming collar chart. -/
public theorem toGlueRight_mem_image_signedSeamMap_iff (U : Set (M₁ × OpenCollarParameter))
    (w : B₁₂.W) :
    toGlueRight B₀₁ B₁₂ w ∈ signedSeamMap B₀₁ B₁₂ '' U ↔
      ∃ p : CollarSource M₁,
        B₁₂.incoming.chart p = w ∧ seamFromRightCollarSource p ∈ U := by
  constructor
  · rintro ⟨z, hzU, hz⟩
    by_cases hleft : seamCoordinate z.2 ≤ 1 / 2
    · rw [signedSeamMap_eq_left B₀₁ B₁₂ hleft] at hz
      obtain ⟨a, haleft, haright⟩ :=
        (toGlueLeft_eq_toGlueRight_iff B₀₁ B₁₂
          (B₀₁.outgoing.chart (z.1, seamLeftRadius z.2)) w).1 hz
      have hsource : (a, halfCollarStart) = (z.1, seamLeftRadius z.2) :=
        B₀₁.outgoing.chart.isOpenEmbedding.injective haleft
      have hax : a = z.1 :=
        congrArg (fun p : M₁ × HalfCollarParameter ↦ p.1) hsource
      have hl : seamLeftRadius z.2 = halfCollarStart :=
        (congrArg (fun p : M₁ × HalfCollarParameter ↦ p.2) hsource).symm
      have hmid := (seamLeftRadius_eq_start_iff hleft).1 hl
      subst a
      refine ⟨(z.1, halfCollarStart), ?_, ?_⟩
      · exact haright
      · have hr : seamRightRadius z.2 = halfCollarStart :=
          (seamRightRadius_eq_start_iff (le_of_eq hmid.symm)).2 hmid
        rw [← hr, seamFromRightCollarSource_radius z.1 z.2 (le_of_eq hmid.symm)]
        exact hzU
    · have hright : 1 / 2 < seamCoordinate z.2 := lt_of_not_ge hleft
      rw [signedSeamMap_eq_right B₀₁ B₁₂ hright] at hz
      have hchart : B₁₂.incoming.chart (z.1, seamRightRadius z.2) = w :=
        (toGlueRight_isClosedEmbedding B₀₁ B₁₂).injective hz
      refine ⟨(z.1, seamRightRadius z.2), hchart, ?_⟩
      rw [seamFromRightCollarSource_radius z.1 z.2 (le_of_lt hright)]
      exact hzU
  · rintro ⟨p, hpw, hpU⟩
    refine ⟨seamFromRightCollarSource p, hpU, ?_⟩
    rw [signedSeamMap_fromRightCollarSource B₀₁ B₁₂ p, hpw]

/-- Pointwise description of the preimage of the image of an arbitrary seam-cylinder subset
under the quotient map. -/
public theorem preimage_quotientMk_image_signedSeamMap
    (U : Set (M₁ × OpenCollarParameter)) :
    (fun w : B₀₁.W ⊕ B₁₂.W ↦ (Quotient.mk'' w : Glue B₀₁ B₁₂)) ⁻¹'
        (signedSeamMap B₀₁ B₁₂ '' U) =
      Sum.inl '' (B₀₁.outgoing.chart '' (seamFromLeftCollarSource ⁻¹' U)) ∪
        Sum.inr '' (B₁₂.incoming.chart '' (seamFromRightCollarSource ⁻¹' U)) := by
  ext w
  rcases w with w | w
  · constructor
    · intro hw
      change toGlueLeft B₀₁ B₁₂ w ∈
        signedSeamMap B₀₁ B₁₂ '' U at hw
      obtain ⟨p, hpw, hpU⟩ :=
        (toGlueLeft_mem_image_signedSeamMap_iff B₀₁ B₁₂ U w).1 hw
      exact Or.inl ⟨B₀₁.outgoing.chart p, ⟨p, hpU, rfl⟩,
        congrArg Sum.inl hpw⟩
    · intro hw
      rcases hw with hw | hw
      · rcases hw with ⟨w', ⟨p, hpU, hpw'⟩, heq⟩
        have hww' : w' = w := Sum.inl.inj heq
        apply (toGlueLeft_mem_image_signedSeamMap_iff B₀₁ B₁₂ U w).2
        exact ⟨p, hpw'.trans hww', hpU⟩
      · rcases hw with ⟨w', -, heq⟩
        exact (Sum.inr_ne_inl heq).elim
  · constructor
    · intro hw
      change toGlueRight B₀₁ B₁₂ w ∈
        signedSeamMap B₀₁ B₁₂ '' U at hw
      obtain ⟨p, hpw, hpU⟩ :=
        (toGlueRight_mem_image_signedSeamMap_iff B₀₁ B₁₂ U w).1 hw
      exact Or.inr ⟨B₁₂.incoming.chart p, ⟨p, hpU, rfl⟩,
        congrArg Sum.inr hpw⟩
    · intro hw
      rcases hw with hw | hw
      · rcases hw with ⟨w', -, heq⟩
        exact (Sum.inl_ne_inr heq).elim
      · rcases hw with ⟨w', ⟨p, hpU, hpw'⟩, heq⟩
        have hww' : w' = w := Sum.inr.inj heq
        apply (toGlueRight_mem_image_signedSeamMap_iff B₀₁ B₁₂ U w).2
        exact ⟨p, hpw'.trans hww', hpU⟩

/-- The signed seam map sends open sets to open sets in the glued quotient. -/
public theorem isOpenMap_signedSeamMap : IsOpenMap (signedSeamMap B₀₁ B₁₂) := by
  intro U hU
  have hq : IsQuotientMap
      (fun w : B₀₁.W ⊕ B₁₂.W ↦ (Quotient.mk'' w : Glue B₀₁ B₁₂)) :=
    isQuotientMap_quotient_mk'
  rw [← hq.isOpen_preimage,
    preimage_quotientMk_image_signedSeamMap B₀₁ B₁₂ U]
  apply IsOpen.union
  · apply isOpenMap_inl
    exact B₀₁.outgoing.chart.isOpenEmbedding.isOpenMap _
      (hU.preimage continuous_seamFromLeftCollarSource)
  · apply isOpenMap_inr
    exact B₁₂.incoming.chart.isOpenEmbedding.isOpenMap _
      (hU.preimage continuous_seamFromRightCollarSource)

/-- The signed bicollar is an open embedding onto the seam neighborhood. -/
public theorem signedSeamMap_isOpenEmbedding :
    IsOpenEmbedding (signedSeamMap B₀₁ B₁₂) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_signedSeamMap B₀₁ B₁₂)
    (signedSeamMap_injective B₀₁ B₁₂)
    (isOpenMap_signedSeamMap B₀₁ B₁₂)

/-- The seam neighborhood packaged as an open subspace of the glued carrier. -/
public def seamOpenNeighborhood : Opens (Glue B₀₁ B₁₂) where
  carrier := seamNeighborhood B₀₁ B₁₂
  is_open' := isOpen_seamNeighborhood B₀₁ B₁₂

@[simp]
public theorem seamOpenNeighborhood_coe :
    (seamOpenNeighborhood B₀₁ B₁₂ : Set (Glue B₀₁ B₁₂)) =
      seamNeighborhood B₀₁ B₁₂ :=
  rfl

/-- The explicit homeomorphism from the signed open cylinder onto the seam neighborhood. -/
public def signedSeamHomeomorph :
    (M₁ × OpenCollarParameter) ≃ₜ seamOpenNeighborhood B₀₁ B₁₂ :=
  (signedSeamMap_isOpenEmbedding B₀₁ B₁₂).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (range_signedSeamMap B₀₁ B₁₂))

@[simp]
public theorem signedSeamHomeomorph_apply (p : M₁ × OpenCollarParameter) :
    (signedSeamHomeomorph B₀₁ B₁₂ p : Glue B₀₁ B₁₂) =
      signedSeamMap B₀₁ B₁₂ p :=
  rfl

/-- The open piece supplied by the first bordism away from the identified zero section. -/
public def leftAwayOpenNeighborhood : Opens (Glue B₀₁ B₁₂) where
  carrier := Set.range (toGlueLeftAway B₀₁ B₁₂)
  is_open' := (toGlueLeftAway_isOpenEmbedding B₀₁ B₁₂).isOpen_range

/-- The open piece supplied by the second bordism away from the identified zero section. -/
public def rightAwayOpenNeighborhood : Opens (Glue B₀₁ B₁₂) where
  carrier := Set.range (toGlueRightAway B₀₁ B₁₂)
  is_open' := (toGlueRightAway_isOpenEmbedding B₀₁ B₁₂).isOpen_range

@[simp]
public theorem leftAwayOpenNeighborhood_coe :
    (leftAwayOpenNeighborhood B₀₁ B₁₂ : Set (Glue B₀₁ B₁₂)) =
      Set.range (toGlueLeftAway B₀₁ B₁₂) :=
  rfl

@[simp]
public theorem rightAwayOpenNeighborhood_coe :
    (rightAwayOpenNeighborhood B₀₁ B₁₂ : Set (Glue B₀₁ B₁₂)) =
      Set.range (toGlueRightAway B₀₁ B₁₂) :=
  rfl

/-- The two away pieces and the signed bicollar form an explicit three-piece open cover of the
glued carrier. -/
public theorem threePieceSeamCover :
    Set.range (toGlueLeftAway B₀₁ B₁₂) ∪
        seamNeighborhood B₀₁ B₁₂ ∪
        Set.range (toGlueRightAway B₀₁ B₁₂) =
      Set.univ := by
  ext y
  constructor
  · intro
    trivial
  · intro
    rcases Quotient.mk_surjective y with ⟨w, rfl⟩
    rcases w with w | w
    · by_cases hw : w ∈ Set.range B₀₁.outgoing.inclusion
      · rcases hw with ⟨x, rfl⟩
        refine Or.inl (Or.inr (Or.inl ⟨B₀₁.outgoing.inclusion x, ?_, rfl⟩))
        exact (B₀₁.outgoing.chart.toDiffeomorph (x, halfCollarStart)).property
      · exact Or.inl (Or.inl ⟨⟨w, hw⟩, rfl⟩)
    · by_cases hw : w ∈ Set.range B₁₂.incoming.inclusion
      · rcases hw with ⟨x, rfl⟩
        refine Or.inl (Or.inr (Or.inr ⟨B₁₂.incoming.inclusion x, ?_, rfl⟩))
        exact (B₁₂.incoming.chart.toDiffeomorph (x, halfCollarStart)).property
      · exact Or.inr ⟨⟨w, hw⟩, rfl⟩

end QuotientGluing
end SmoothCollaredBordism
end SphereSixComplex
