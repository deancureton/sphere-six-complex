module

public import SphereSixComplex.Topology.OpenUnionHomotopyEquivalence

/-!
# Dold's homotopy excision for a numerated two-set open cover

This file contains two independent results about the double-mapping-cylinder collapse of a
two-set open cover.

## The open-support interface is unsatisfiable

`OpenUnionHomotopy.TwoSetNumeration` requires only the *open* support conditions
`weight x ≠ 0 → x ∈ U` and `weight x ≠ 1 → x ∈ V`, while
`TwoSetNumeration.HomotopyExcisionData` prescribes the value of its section `inverse`
pointwise at every point of the union.  Those prescribed values do not assemble into a
continuous map: `isEmpty_homotopyExcisionData` exhibits the cover `{Ioi 0, univ}` of `ℝ`,
numerated by the clamped identity, for which the interface is empty.  Hence
`not_forall_twoSetNumeration_homotopyExcisionData` refutes the corresponding general statement.
The obstruction is exactly the difference between open and closed supports: at the boundary
point `0`, which lies outside `Ioi 0` but is a limit of points of positive weight, the
prescribed section jumps from the base of the mapping cylinder into the interior of the
inserted cylinder.

## Dold's theorem for a closed numeration

A partition of unity subordinate to `{U, V}` provides the *closed* support conditions
`tsupport` and these do make the section continuous.  `ClosedNumeration` records that data,
`ClosedNumeration.sectionMap` glues the section from three charts, `ClosedNumeration.slideDouble`
slides the cylinder coordinate to the weight, and `ClosedNumeration.isHomotopyExcisiveSpan`
concludes that the collapse is a homotopy equivalence.  Since a subordinate partition of unity
produces a closed numeration on a normal paracompact union,
`leftToUnion_isHomotopyEquivalence_of_normal_paracompact_proved` is an axiom-free replacement of
the corresponding established statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ContinuousMap Set Topology

namespace SphereSixComplex

universe u

namespace NumeratedCoverCounterexample

open OpenUnionHomotopy

/-- The left member of the counterexample cover. -/
public def leftSet : Set ℝ := Set.Ioi 0

/-- The right member of the counterexample cover. -/
public def rightSet : Set ℝ := Set.univ

public theorem mem_union (x : ℝ) : x ∈ leftSet ∪ rightSet := Or.inr (Set.mem_univ x)

/-- A real number as a point of the union of the counterexample cover. -/
public def pt (x : ℝ) : ↥(leftSet ∪ rightSet) := ⟨x, mem_union x⟩

/-- The counterexample numeration: the clamping of the identity to the unit interval. -/
public def weightFn : C(↥(leftSet ∪ rightSet), unitInterval) :=
  ⟨fun x ↦ Set.projIcc 0 1 zero_le_one x.1,
    continuous_projIcc.comp continuous_subtype_val⟩

public theorem weightFn_apply (x : ↥(leftSet ∪ rightSet)) :
    (weightFn x : ℝ) = max 0 (min 1 x.1) := rfl

/-- The counterexample numeration of the cover `{Ioi 0, univ}` of `ℝ`. -/
public def numeration : TwoSetNumeration leftSet rightSet where
  weight := weightFn
  weight_ne_zero_mem_left := by
    intro x hx
    by_contra hmem
    apply hx
    apply Subtype.ext
    have hle : x.1 ≤ 0 := le_of_not_gt fun h ↦ hmem h
    rw [weightFn_apply]
    have : min (1 : ℝ) x.1 ≤ 0 := le_trans (min_le_right _ _) hle
    simp [max_eq_left this]
  weight_ne_one_mem_right := by
    intro x _
    exact Set.mem_univ _


/-! ## A continuous probe of the double mapping cylinder -/

/-- The overlap-to-right leg of the counterexample span. -/
public abbrev spanRight : TopCat.of ↥(leftSet ∩ rightSet) ⟶ TopCat.of ↥rightSet :=
  interToRight leftSet rightSet

/-- The overlap-to-left leg of the counterexample span. -/
public abbrev spanLeft : TopCat.of ↥(leftSet ∩ rightSet) ⟶ TopCat.of ↥leftSet :=
  interToLeft leftSet rightSet

public theorem pos_of_mem_inter (a : ↥(leftSet ∩ rightSet)) : 0 < (a : ℝ) := a.2.1

public theorem pos_of_mem_left (a : ↥leftSet) : 0 < (a : ℝ) := a.2

/-- On the cylinder branch the probe divides the cylinder coordinate by the base point. -/
public def probeCylinder :
    TopCat.of (↥(leftSet ∩ rightSet) × unitInterval) ⟶ TopCat.of ℝ :=
  TopCat.ofHom ⟨fun p ↦ (p.2 : ℝ) / (p.1 : ℝ), by
    refine Continuous.div (continuous_subtype_val.comp continuous_snd)
      (continuous_subtype_val.comp continuous_fst) ?_
    intro p
    exact ne_of_gt (pos_of_mem_inter p.1)⟩

/-- On the right branch the probe vanishes. -/
public def probeBase : TopCat.of ↥rightSet ⟶ TopCat.of ℝ :=
  TopCat.ofHom ⟨fun _ ↦ 0, continuous_const⟩

/-- On the left branch the probe is the reciprocal. -/
public def probeLeftEnd : TopCat.of ↥leftSet ⟶ TopCat.of ℝ :=
  TopCat.ofHom ⟨fun u ↦ 1 / (u : ℝ), by
    refine Continuous.div continuous_const continuous_subtype_val ?_
    intro u
    exact ne_of_gt (pos_of_mem_left u)⟩

/-- The probe on the mapping cylinder of the overlap-to-right leg. -/
public def probeMappingCylinder : TopCat.MappingCylinder spanRight ⟶ TopCat.of ℝ :=
  pushout.desc probeCylinder probeBase (by
    ext a
    change ((0 : unitInterval) : ℝ) / (a : ℝ) = 0
    simp)

public theorem probeMappingCylinder_cylinder
    (p : ↥(leftSet ∩ rightSet) × unitInterval) :
    probeMappingCylinder (TopCat.mappingCylinderCylinder spanRight p) =
      (p.2 : ℝ) / (p.1 : ℝ) := by
  have h : TopCat.mappingCylinderCylinder spanRight ≫ probeMappingCylinder = probeCylinder :=
    pushout.inl_desc _ _ _
  exact CategoryTheory.congr_fun h p

public theorem probeMappingCylinder_base (v : ↥rightSet) :
    probeMappingCylinder (TopCat.mappingCylinderBase spanRight v) = 0 := by
  have h : TopCat.mappingCylinderBase spanRight ≫ probeMappingCylinder = probeBase :=
    pushout.inr_desc _ _ _
  exact CategoryTheory.congr_fun h v

/-- The probe on the double mapping cylinder of the counterexample span. -/
public def probeDouble :
    TopCat.DoubleMappingCylinder spanRight spanLeft ⟶ TopCat.of ℝ :=
  pushout.desc probeMappingCylinder probeLeftEnd (by
    ext a
    change probeMappingCylinder
      (TopCat.mappingCylinderCylinder spanRight (a, 1)) = 1 / (a : ℝ)
    rw [probeMappingCylinder_cylinder]
    norm_num)

public theorem probeDouble_left (m : TopCat.MappingCylinder spanRight) :
    probeDouble (TopCat.doubleMappingCylinderLeft spanRight spanLeft m) =
      probeMappingCylinder m := by
  have h : TopCat.doubleMappingCylinderLeft spanRight spanLeft ≫ probeDouble =
      probeMappingCylinder := pushout.inl_desc _ _ _
  exact CategoryTheory.congr_fun h m


/-! ## The prescribed section is not continuous -/

public theorem weight_pt (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ((numeration.weight (pt t) : unitInterval) : ℝ) = t := by
  show max (0 : ℝ) (min 1 t) = t
  rw [min_eq_right h1, max_eq_right h0]

public theorem weight_pt_zero : numeration.weight (pt 0) = 0 := by
  apply Subtype.ext
  show max (0 : ℝ) (min 1 0) = 0
  norm_num

/-- At the endpoint the probe of the prescribed section vanishes. -/
public theorem probe_inverse_zero (D : numeration.HomotopyExcisionData) :
    probeDouble (D.inverse (pt 0)) = 0 := by
  rw [D.inverse_zero (pt 0) weight_pt_zero, probeDouble_left, probeMappingCylinder_base]

/-- Immediately to the right of the endpoint the probe of the prescribed section is `1`. -/
public theorem probe_inverse_interior (D : numeration.HomotopyExcisionData)
    (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    probeDouble (D.inverse (pt t)) = 1 := by
  have hval := weight_pt t h0.le h1.le
  have hz : numeration.weight (pt t) ≠ 0 := by
    intro h
    rw [h] at hval
    exact h0.ne hval
  have ho : numeration.weight (pt t) ≠ 1 := by
    intro h
    rw [h] at hval
    exact h1.ne' hval
  rw [D.inverse_interior (pt t) hz ho, probeDouble_left, probeMappingCylinder_cylinder]
  show ((numeration.weight (pt t) : unitInterval) : ℝ) / t = 1
  rw [hval, div_self h0.ne']

/-- The interface `TwoSetNumeration.HomotopyExcisionData` is unsatisfiable for the numerated
cover `{Ioi 0, univ}` of `ℝ`: the pointwise formulas prescribed for `inverse` do not define a
continuous map. -/
public theorem isEmpty_homotopyExcisionData :
    IsEmpty numeration.HomotopyExcisionData := by
  constructor
  intro D
  have hmk : Continuous fun t : ℝ ↦ pt t := continuous_id.subtype_mk _
  have hcont : Continuous fun t : ℝ ↦ probeDouble (D.inverse (pt t)) :=
    (TopCat.Hom.hom probeDouble).continuous.comp (D.inverse.continuous.comp hmk)
  have hmem : Set.Iio (1 / 2 : ℝ) ∈ 𝓝 (probeDouble (D.inverse (pt 0))) := by
    rw [probe_inverse_zero D]
    exact Iio_mem_nhds (by norm_num)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), probeDouble (D.inverse (pt t)) < 1 / 2 :=
    (hcont.continuousAt (x := (0 : ℝ))) hmem
  have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht using ht
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t := by
    filter_upwards [self_mem_nhdsWithin] with t ht using ht
  obtain ⟨t, ⟨hhalf, hone⟩, hzero⟩ :=
    (((hev.filter_mono nhdsWithin_le_nhds).and
      (hlt.filter_mono nhdsWithin_le_nhds)).and hpos).exists
  rw [probe_inverse_interior D t hzero hone] at hhalf
  norm_num at hhalf

/-- The established axiom `numeratedTwoSetCoverHomotopyExcisionData` is false: no such data
exists for the numerated cover `{Ioi 0, univ}` of `ℝ`. -/
public theorem not_forall_twoSetNumeration_homotopyExcisionData :
    ¬ ∀ (X : Type) [TopologicalSpace X] (U V : Set X)
        (N : TwoSetNumeration U V), Nonempty N.HomotopyExcisionData := by
  intro h
  exact isEmpty_homotopyExcisionData.false (h ℝ leftSet rightSet numeration).some

end NumeratedCoverCounterexample

namespace ClosedCover

open OpenUnionHomotopy

variable {X : Type u} [TopologicalSpace X]

/-- A numeration of a two-set open cover with *closed* supports.  This is what a partition of
unity subordinate to the cover `{U, V}` actually provides, and — unlike the open-support
condition — it is strong enough to make the Dold collapse section continuous. -/
public structure ClosedNumeration (U V : Set X) where
  /-- The weight function; weight one belongs to the left member, weight zero to the right. -/
  weight : C(↥(U ∪ V), unitInterval)
  isOpen_left : IsOpen U
  isOpen_right : IsOpen V
  closure_ne_zero : closure {x : ↥(U ∪ V) | weight x ≠ 0} ⊆ {x | x.1 ∈ U}
  closure_ne_one : closure {x : ↥(U ∪ V) | weight x ≠ 1} ⊆ {x | x.1 ∈ V}

namespace ClosedNumeration

variable {U V : Set X} (N : ClosedNumeration U V)

public theorem mem_left_of_ne_zero (x : ↥(U ∪ V)) (h : N.weight x ≠ 0) : x.1 ∈ U :=
  N.closure_ne_zero (subset_closure h)

public theorem mem_right_of_ne_one (x : ↥(U ∪ V)) (h : N.weight x ≠ 1) : x.1 ∈ V :=
  N.closure_ne_one (subset_closure h)

/-- The chart on which the weight vanishes identically. -/
public def chartRight : Set ↥(U ∪ V) := (closure {x : ↥(U ∪ V) | N.weight x ≠ 0})ᶜ

/-- The chart on which the weight is identically one. -/
public def chartLeft : Set ↥(U ∪ V) := (closure {x : ↥(U ∪ V) | N.weight x ≠ 1})ᶜ

/-- The chart of points lying in both members of the cover. -/
public def chartBoth (U V : Set X) : Set ↥(U ∪ V) := {x | x.1 ∈ U ∩ V}

public theorem weight_eq_zero_of_chartRight {x : ↥(U ∪ V)} (hx : x ∈ N.chartRight) :
    N.weight x = 0 := by
  by_contra h
  exact hx (subset_closure h)

public theorem weight_eq_one_of_chartLeft {x : ↥(U ∪ V)} (hx : x ∈ N.chartLeft) :
    N.weight x = 1 := by
  by_contra h
  exact hx (subset_closure h)

public theorem mem_right_of_chartRight {x : ↥(U ∪ V)} (hx : x ∈ N.chartRight) : x.1 ∈ V :=
  N.mem_right_of_ne_one x (by rw [N.weight_eq_zero_of_chartRight hx]; exact zero_ne_one)

public theorem mem_left_of_chartLeft {x : ↥(U ∪ V)} (hx : x ∈ N.chartLeft) : x.1 ∈ U :=
  N.mem_left_of_ne_zero x (by rw [N.weight_eq_one_of_chartLeft hx]; exact one_ne_zero)

public theorem isOpen_chartRight : IsOpen N.chartRight := isClosed_closure.isOpen_compl

public theorem isOpen_chartLeft : IsOpen N.chartLeft := isClosed_closure.isOpen_compl

public theorem isOpen_chartBoth (hU : IsOpen U) (hV : IsOpen V) : IsOpen (chartBoth U V) :=
  (hU.inter hV).preimage continuous_subtype_val

/-- Every point of the union lies in one of the three charts. -/
public theorem chart_nhds (x : ↥(U ∪ V)) :
    x ∈ N.chartRight ∨ x ∈ N.chartLeft ∨ x ∈ chartBoth U V := by
  by_cases hr : x ∈ N.chartRight
  · exact Or.inl hr
  · by_cases hl : x ∈ N.chartLeft
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr
        ⟨N.closure_ne_zero (not_not.1 hr), N.closure_ne_one (not_not.1 hl)⟩)

end ClosedNumeration

/-! ### Points of the double mapping cylinder of an open cover -/

/-- The double mapping cylinder of the two inclusions of the overlap. -/
public abbrev Dmc (U V : Set X) : TopCat.{u} :=
  TopCat.DoubleMappingCylinder (interToRight U V) (interToLeft U V)

/-- The point of the inserted cylinder over `a` at height `t`. -/
public def pointCyl (U V : Set X) (a : ↥(U ∩ V)) (t : unitInterval) : Dmc U V :=
  TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
    (TopCat.mappingCylinderCylinder (interToRight U V) (a, t))

/-- The point of the right member of the cover. -/
public def pointRight (U V : Set X) (v : ↥V) : Dmc U V :=
  TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
    (TopCat.mappingCylinderBase (interToRight U V) v)

/-- The point of the left member of the cover. -/
public def pointLeft (U V : Set X) (u : ↥U) : Dmc U V :=
  TopCat.doubleMappingCylinderRight (interToRight U V) (interToLeft U V) u

variable {U V : Set X}

public theorem pointCyl_zero (a : ↥(U ∩ V)) :
    pointCyl U V a 0 = pointRight U V ⟨a.1, a.2.2⟩ :=
  congrArg (fun m ↦ TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V) m)
    (CategoryTheory.congr_fun (TopCat.mappingCylinder_zero_eq_base (interToRight U V)) a)

public theorem pointCyl_one (a : ↥(U ∩ V)) :
    pointCyl U V a 1 = pointLeft U V ⟨a.1, a.2.1⟩ :=
  CategoryTheory.congr_fun
    (TopCat.doubleMappingCylinder_condition (interToRight U V) (interToLeft U V)) a

public theorem continuous_pointCyl :
    Continuous fun p : ↥(U ∩ V) × unitInterval ↦ pointCyl U V p.1 p.2 :=
  (TopCat.Hom.hom
      (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V))).continuous.comp
    (TopCat.Hom.hom (TopCat.mappingCylinderCylinder (interToRight U V))).continuous

public theorem continuous_pointRight :
    Continuous fun v : ↥V ↦ pointRight U V v :=
  (TopCat.Hom.hom
      (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V))).continuous.comp
    (TopCat.Hom.hom (TopCat.mappingCylinderBase (interToRight U V))).continuous

public theorem continuous_pointLeft :
    Continuous fun u : ↥U ↦ pointLeft U V u :=
  (TopCat.Hom.hom
    (TopCat.doubleMappingCylinderRight (interToRight U V) (interToLeft U V))).continuous

/-! ### The collapse on the three kinds of points -/

public theorem collapse_pointRight (v : ↥V) :
    doubleMappingCylinderToUnion U V (pointRight U V v) = ⟨v.1, Or.inr v.2⟩ := by
  change pushoutToUnion U V (TopCat.doubleMappingCylinderCollapse (interToRight U V)
    (interToLeft U V) (TopCat.doubleMappingCylinderLeft (interToRight U V)
      (interToLeft U V) (TopCat.mappingCylinderBase (interToRight U V) v))) = _
  rw [show TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
      (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
        (TopCat.mappingCylinderBase (interToRight U V) v)) =
      TopCat.mappingCylinderToPushout (interToRight U V) (interToLeft U V)
        (TopCat.mappingCylinderBase (interToRight U V) v) from
    CategoryTheory.congr_fun
      (TopCat.doubleMappingCylinderLeft_comp_collapse (interToRight U V) (interToLeft U V)) _]
  change pushoutToUnion U V (pushout.inl (interToRight U V) (interToLeft U V)
    (TopCat.mappingCylinderCollapse (interToRight U V)
      (TopCat.mappingCylinderBase (interToRight U V) v))) = _
  rw [show TopCat.mappingCylinderCollapse (interToRight U V)
      (TopCat.mappingCylinderBase (interToRight U V) v) = v from
    CategoryTheory.congr_fun (TopCat.mappingCylinderBase_comp_collapse (interToRight U V)) v,
    pushoutToUnion_inl]
  rfl

public theorem collapse_pointCyl (a : ↥(U ∩ V)) (t : unitInterval) :
    doubleMappingCylinderToUnion U V (pointCyl U V a t) = ⟨a.1, Or.inl a.2.1⟩ := by
  change pushoutToUnion U V (TopCat.doubleMappingCylinderCollapse (interToRight U V)
    (interToLeft U V) (TopCat.doubleMappingCylinderLeft (interToRight U V)
      (interToLeft U V) (TopCat.mappingCylinderCylinder (interToRight U V) (a, t)))) = _
  rw [show TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
      (TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V)
        (TopCat.mappingCylinderCylinder (interToRight U V) (a, t))) =
      TopCat.mappingCylinderToPushout (interToRight U V) (interToLeft U V)
        (TopCat.mappingCylinderCylinder (interToRight U V) (a, t)) from
    CategoryTheory.congr_fun
      (TopCat.doubleMappingCylinderLeft_comp_collapse (interToRight U V) (interToLeft U V)) _]
  change pushoutToUnion U V (pushout.inl (interToRight U V) (interToLeft U V)
    (TopCat.mappingCylinderCollapse (interToRight U V)
      (TopCat.mappingCylinderCylinder (interToRight U V) (a, t)))) = _
  rw [show TopCat.mappingCylinderCollapse (interToRight U V)
      (TopCat.mappingCylinderCylinder (interToRight U V) (a, t)) = interToRight U V a from
    CategoryTheory.congr_fun
      (TopCat.mappingCylinderCylinder_comp_collapse (interToRight U V)) _,
    pushoutToUnion_inl]
  rfl

public theorem collapse_pointLeft (u : ↥U) :
    doubleMappingCylinderToUnion U V (pointLeft U V u) = ⟨u.1, Or.inl u.2⟩ := by
  change pushoutToUnion U V (TopCat.doubleMappingCylinderCollapse (interToRight U V)
    (interToLeft U V) (TopCat.doubleMappingCylinderRight (interToRight U V)
      (interToLeft U V) u)) = _
  rw [show TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V)
      (TopCat.doubleMappingCylinderRight (interToRight U V) (interToLeft U V) u) =
      pushout.inr (interToRight U V) (interToLeft U V) u from
    CategoryTheory.congr_fun
      (TopCat.doubleMappingCylinderRight_comp_collapse (interToRight U V) (interToLeft U V)) u,
    pushoutToUnion_inr]
  rfl

/-! ### The Dold section of the collapse -/

namespace ClosedNumeration

variable (N : ClosedNumeration U V)

/-- The three charts of the numeration, indexed by `Option Bool`. -/
public def coverSet : Option Bool → Set ↥(U ∪ V)
  | none => chartBoth U V
  | some false => N.chartRight
  | some true => N.chartLeft

/-- The chartwise pieces of the Dold section. -/
public def coverMap : (i : Option Bool) → C(↥(N.coverSet i), Dmc U V)
  | none => ⟨fun x ↦ pointCyl U V ⟨x.1.1, x.2⟩ (N.weight x.1),
      continuous_pointCyl.comp
        (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).prodMk
          (N.weight.continuous.comp continuous_subtype_val))⟩
  | some false => ⟨fun x ↦ pointRight U V ⟨x.1.1, N.mem_right_of_chartRight x.2⟩,
      continuous_pointRight.comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  | some true => ⟨fun x ↦ pointLeft U V ⟨x.1.1, N.mem_left_of_chartLeft x.2⟩,
      continuous_pointLeft.comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩

public theorem coverMap_compatible :
    ∀ (i j : Option Bool) (x : ↥(U ∪ V)) (hxi : x ∈ N.coverSet i)
      (hxj : x ∈ N.coverSet j),
      N.coverMap i ⟨x, hxi⟩ = N.coverMap j ⟨x, hxj⟩ := by
  have key : ∀ (j : Option Bool) (x : ↥(U ∪ V)) (hxi : x ∈ N.coverSet none)
      (hxj : x ∈ N.coverSet j), N.coverMap none ⟨x, hxi⟩ = N.coverMap j ⟨x, hxj⟩ := by
    rintro (_ | b) x hxi hxj
    · rfl
    · cases b
      · show pointCyl U V ⟨x.1, hxi⟩ (N.weight x) = _
        rw [N.weight_eq_zero_of_chartRight hxj, pointCyl_zero]
        rfl
      · show pointCyl U V ⟨x.1, hxi⟩ (N.weight x) = _
        rw [N.weight_eq_one_of_chartLeft hxj, pointCyl_one]
        rfl
  rintro (_ | bi) j x hxi hxj
  · exact key j x hxi hxj
  · rcases j with _ | bj
    · exact (key (some bi) x hxj hxi).symm
    · cases bi <;> cases bj
      · rfl
      · have h0 := N.weight_eq_zero_of_chartRight hxi
        rw [N.weight_eq_one_of_chartLeft hxj] at h0
        exact absurd h0 one_ne_zero
      · have h0 := N.weight_eq_zero_of_chartRight hxj
        rw [N.weight_eq_one_of_chartLeft hxi] at h0
        exact absurd h0 one_ne_zero
      · rfl

public theorem coverSet_nhds (x : ↥(U ∪ V)) : ∃ i, N.coverSet i ∈ 𝓝 x := by
  rcases N.chart_nhds x with h | h | h
  · exact ⟨some false, N.isOpen_chartRight.mem_nhds h⟩
  · exact ⟨some true, N.isOpen_chartLeft.mem_nhds h⟩
  · exact ⟨none, (isOpen_chartBoth N.isOpen_left N.isOpen_right).mem_nhds h⟩

/-- Dold's section of the double-mapping-cylinder collapse, glued from the three charts. -/
public def sectionMap : C(↥(U ∪ V), Dmc U V) :=
  ContinuousMap.liftCover N.coverSet N.coverMap N.coverMap_compatible N.coverSet_nhds

public theorem sectionMap_of_chartBoth (x : ↥(U ∪ V)) (hx : x.1 ∈ U ∩ V) :
    N.sectionMap x = pointCyl U V ⟨x.1, hx⟩ (N.weight x) :=
  ContinuousMap.liftCover_coe (S := N.coverSet) (i := none) ⟨x, hx⟩

public theorem sectionMap_of_chartRight (x : ↥(U ∪ V)) (hx : x ∈ N.chartRight) :
    N.sectionMap x = pointRight U V ⟨x.1, N.mem_right_of_chartRight hx⟩ :=
  ContinuousMap.liftCover_coe (S := N.coverSet) (i := some false) ⟨x, hx⟩

public theorem sectionMap_of_chartLeft (x : ↥(U ∪ V)) (hx : x ∈ N.chartLeft) :
    N.sectionMap x = pointLeft U V ⟨x.1, N.mem_left_of_chartLeft hx⟩ :=
  ContinuousMap.liftCover_coe (S := N.coverSet) (i := some true) ⟨x, hx⟩

end ClosedNumeration

/-! ### The collapse retracts the section -/

namespace ClosedNumeration

variable (N : ClosedNumeration U V)

public theorem collapse_sectionMap (x : ↥(U ∪ V)) :
    doubleMappingCylinderToUnion U V (N.sectionMap x) = x := by
  rcases N.chart_nhds x with h | h | h
  · rw [N.sectionMap_of_chartRight x h, collapse_pointRight]
  · rw [N.sectionMap_of_chartLeft x h, collapse_pointLeft]
  · rw [N.sectionMap_of_chartBoth x h, collapse_pointCyl]

/-! ### The sliding homotopy -/

/-- The weight of a point of the overlap. -/
public def weightInter (a : ↥(U ∩ V)) : unitInterval := N.weight ⟨a.1, Or.inl a.2.1⟩

public theorem continuous_weightInter : Continuous N.weightInter :=
  N.weight.continuous.comp (continuous_subtype_val.subtype_mk _)

end ClosedNumeration

/-- The affine slide from `p` to `q` inside the unit interval. -/
public def slide (p q t : unitInterval) : unitInterval :=
  ⟨(1 - (t : ℝ)) * (p : ℝ) + (t : ℝ) * (q : ℝ), by
    have ht : (0 : ℝ) ≤ 1 - (t : ℝ) := by have := t.2.2; linarith
    constructor
    · have h1 := mul_nonneg ht p.2.1
      have h2 := mul_nonneg t.2.1 q.2.1
      linarith
    · have h1 : (1 - (t : ℝ)) * (p : ℝ) ≤ (1 - (t : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left p.2.2 ht
      have h2 : (t : ℝ) * (q : ℝ) ≤ (t : ℝ) * 1 := mul_le_mul_of_nonneg_left q.2.2 t.2.1
      linarith⟩

@[simp]
public theorem slide_zero (p q : unitInterval) : slide p q 0 = p := by
  apply Subtype.ext
  show (1 - (0 : ℝ)) * (p : ℝ) + (0 : ℝ) * (q : ℝ) = (p : ℝ)
  ring

@[simp]
public theorem slide_one (p q : unitInterval) : slide p q 1 = q := by
  apply Subtype.ext
  show (1 - (1 : ℝ)) * (p : ℝ) + (1 : ℝ) * (q : ℝ) = (q : ℝ)
  ring

public theorem slide_self (p t : unitInterval) : slide p p t = p := by
  apply Subtype.ext
  show (1 - (t : ℝ)) * (p : ℝ) + (t : ℝ) * (p : ℝ) = (p : ℝ)
  ring

public theorem continuous_slide :
    Continuous fun r : (unitInterval × unitInterval) × unitInterval ↦ slide r.1.1 r.1.2 r.2 :=
  Continuous.subtype_mk (by fun_prop) _

public theorem continuous_inclRight (U V : Set X) :
    Continuous fun v : ↥V ↦ (⟨v.1, Or.inr v.2⟩ : ↥(U ∪ V)) :=
  continuous_subtype_val.subtype_mk _

public theorem continuous_inclLeft (U V : Set X) :
    Continuous fun u : ↥U ↦ (⟨u.1, Or.inl u.2⟩ : ↥(U ∪ V)) :=
  continuous_subtype_val.subtype_mk _

namespace ClosedNumeration

variable (N : ClosedNumeration U V)

/-! #### The sliding homotopy on the inserted cylinder -/

/-- On the inserted cylinder the homotopy slides the cylinder coordinate to the weight. -/
public def slideCylMap : TopCat.of (↥(U ∩ V) × unitInterval) ⟶
    TopCat.of C(unitInterval, ↥(Dmc U V)) :=
  TopCat.ofHom (ContinuousMap.curry
    ⟨fun r : (↥(U ∩ V) × unitInterval) × unitInterval ↦
        pointCyl U V r.1.1 (slide (N.weightInter r.1.1) r.1.2 r.2), by
      have hb : Continuous fun r : (↥(U ∩ V) × unitInterval) × unitInterval ↦ r.1.1 :=
        continuous_fst.fst
      exact continuous_pointCyl.comp (hb.prodMk (continuous_slide.comp
        (((N.continuous_weightInter.comp hb).prodMk continuous_fst.snd).prodMk
          continuous_snd)))⟩)

public theorem slideCylMap_apply (a : ↥(U ∩ V)) (t τ : unitInterval) :
    N.slideCylMap (a, t) τ = pointCyl U V a (slide (N.weightInter a) t τ) := rfl

/-! #### The sliding homotopy on the right member -/

/-- The two charts of the right member. -/
public def baseCoverSet : Bool → Set ↥V
  | false => {v | v.1 ∈ U}
  | true => {v | (⟨v.1, Or.inr v.2⟩ : ↥(U ∪ V)) ∈ N.chartRight}

/-- The chartwise pieces of the sliding homotopy on the right member. -/
public def baseCoverMap :
    (i : Bool) → C(↥(N.baseCoverSet i), C(unitInterval, ↥(Dmc U V)))
  | false => ContinuousMap.curry
      ⟨fun r : ↥(N.baseCoverSet false) × unitInterval ↦
          pointCyl U V ⟨r.1.1.1, r.1.2, r.1.1.2⟩
            (slide (N.weightInter ⟨r.1.1.1, r.1.2, r.1.1.2⟩) 0 r.2), by
        have hb : Continuous fun r : ↥(N.baseCoverSet false) × unitInterval ↦
            (⟨r.1.1.1, r.1.2, r.1.1.2⟩ : ↥(U ∩ V)) :=
          Continuous.subtype_mk
            (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)) _
        exact continuous_pointCyl.comp (hb.prodMk (continuous_slide.comp
          (((N.continuous_weightInter.comp hb).prodMk continuous_const).prodMk
            continuous_snd)))⟩
  | true => ContinuousMap.curry
      ⟨fun r : ↥(N.baseCoverSet true) × unitInterval ↦ pointRight U V r.1.1, by
        exact continuous_pointRight.comp (continuous_subtype_val.comp continuous_fst)⟩

public theorem baseCoverMap_compatible :
    ∀ (i j : Bool) (v : ↥V) (hi : v ∈ N.baseCoverSet i) (hj : v ∈ N.baseCoverSet j),
      N.baseCoverMap i ⟨v, hi⟩ = N.baseCoverMap j ⟨v, hj⟩ := by
  have key : ∀ (v : ↥V) (hi : v ∈ N.baseCoverSet false) (hj : v ∈ N.baseCoverSet true),
      N.baseCoverMap false ⟨v, hi⟩ = N.baseCoverMap true ⟨v, hj⟩ := by
    intro v hi hj
    ext τ
    show pointCyl U V ⟨v.1, hi, v.2⟩ (slide (N.weightInter ⟨v.1, hi, v.2⟩) 0 τ) =
      pointRight U V v
    have hw : N.weightInter ⟨v.1, hi, v.2⟩ = 0 := N.weight_eq_zero_of_chartRight hj
    rw [hw, slide_self, pointCyl_zero]
  intro i j v hi hj
  cases i <;> cases j
  · rfl
  · exact key v hi hj
  · exact (key v hj hi).symm
  · rfl

public theorem baseCoverSet_nhds (v : ↥V) : ∃ i, N.baseCoverSet i ∈ 𝓝 v := by
  by_cases h : (⟨v.1, Or.inr v.2⟩ : ↥(U ∪ V)) ∈ N.chartRight
  · exact ⟨true, (N.isOpen_chartRight.preimage (continuous_inclRight U V)).mem_nhds h⟩
  · exact ⟨false, (N.isOpen_left.preimage continuous_subtype_val).mem_nhds
      (N.closure_ne_zero (not_not.1 h))⟩

/-- The sliding homotopy on the right member of the cover. -/
public def slideBase : C(↥V, C(unitInterval, ↥(Dmc U V))) :=
  ContinuousMap.liftCover N.baseCoverSet N.baseCoverMap N.baseCoverMap_compatible
    N.baseCoverSet_nhds

public theorem slideBase_of_mem_left (v : ↥V) (hv : v.1 ∈ U) (τ : unitInterval) :
    N.slideBase v τ =
      pointCyl U V ⟨v.1, hv, v.2⟩ (slide (N.weightInter ⟨v.1, hv, v.2⟩) 0 τ) :=
  DFunLike.congr_fun
    (ContinuousMap.liftCover_coe (S := N.baseCoverSet) (i := false) ⟨v, hv⟩) τ

public theorem slideBase_of_chartRight (v : ↥V)
    (hv : (⟨v.1, Or.inr v.2⟩ : ↥(U ∪ V)) ∈ N.chartRight) (τ : unitInterval) :
    N.slideBase v τ = pointRight U V v :=
  DFunLike.congr_fun
    (ContinuousMap.liftCover_coe (S := N.baseCoverSet) (i := true) ⟨v, hv⟩) τ

/-! #### The sliding homotopy on the left member -/

/-- The two charts of the left member. -/
public def leftCoverSet : Bool → Set ↥U
  | false => {u | u.1 ∈ V}
  | true => {u | (⟨u.1, Or.inl u.2⟩ : ↥(U ∪ V)) ∈ N.chartLeft}

/-- The chartwise pieces of the sliding homotopy on the left member. -/
public def leftCoverMap :
    (i : Bool) → C(↥(N.leftCoverSet i), C(unitInterval, ↥(Dmc U V)))
  | false => ContinuousMap.curry
      ⟨fun r : ↥(N.leftCoverSet false) × unitInterval ↦
          pointCyl U V ⟨r.1.1.1, r.1.1.2, r.1.2⟩
            (slide (N.weightInter ⟨r.1.1.1, r.1.1.2, r.1.2⟩) 1 r.2), by
        have hb : Continuous fun r : ↥(N.leftCoverSet false) × unitInterval ↦
            (⟨r.1.1.1, r.1.1.2, r.1.2⟩ : ↥(U ∩ V)) :=
          Continuous.subtype_mk
            (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)) _
        exact continuous_pointCyl.comp (hb.prodMk (continuous_slide.comp
          (((N.continuous_weightInter.comp hb).prodMk continuous_const).prodMk
            continuous_snd)))⟩
  | true => ContinuousMap.curry
      ⟨fun r : ↥(N.leftCoverSet true) × unitInterval ↦ pointLeft U V r.1.1, by
        exact continuous_pointLeft.comp (continuous_subtype_val.comp continuous_fst)⟩

public theorem leftCoverMap_compatible :
    ∀ (i j : Bool) (u : ↥U) (hi : u ∈ N.leftCoverSet i) (hj : u ∈ N.leftCoverSet j),
      N.leftCoverMap i ⟨u, hi⟩ = N.leftCoverMap j ⟨u, hj⟩ := by
  have key : ∀ (u : ↥U) (hi : u ∈ N.leftCoverSet false) (hj : u ∈ N.leftCoverSet true),
      N.leftCoverMap false ⟨u, hi⟩ = N.leftCoverMap true ⟨u, hj⟩ := by
    intro u hi hj
    ext τ
    show pointCyl U V ⟨u.1, u.2, hi⟩ (slide (N.weightInter ⟨u.1, u.2, hi⟩) 1 τ) =
      pointLeft U V u
    have hw : N.weightInter ⟨u.1, u.2, hi⟩ = 1 := N.weight_eq_one_of_chartLeft hj
    rw [hw, slide_self, pointCyl_one]
  intro i j u hi hj
  cases i <;> cases j
  · rfl
  · exact key u hi hj
  · exact (key u hj hi).symm
  · rfl

public theorem leftCoverSet_nhds (u : ↥U) : ∃ i, N.leftCoverSet i ∈ 𝓝 u := by
  by_cases h : (⟨u.1, Or.inl u.2⟩ : ↥(U ∪ V)) ∈ N.chartLeft
  · exact ⟨true, (N.isOpen_chartLeft.preimage (continuous_inclLeft U V)).mem_nhds h⟩
  · exact ⟨false, (N.isOpen_right.preimage continuous_subtype_val).mem_nhds
      (N.closure_ne_one (not_not.1 h))⟩

/-- The sliding homotopy on the left member of the cover. -/
public def slideLeft : C(↥U, C(unitInterval, ↥(Dmc U V))) :=
  ContinuousMap.liftCover N.leftCoverSet N.leftCoverMap N.leftCoverMap_compatible
    N.leftCoverSet_nhds

public theorem slideLeft_of_mem_right (u : ↥U) (hu : u.1 ∈ V) (τ : unitInterval) :
    N.slideLeft u τ =
      pointCyl U V ⟨u.1, u.2, hu⟩ (slide (N.weightInter ⟨u.1, u.2, hu⟩) 1 τ) :=
  DFunLike.congr_fun
    (ContinuousMap.liftCover_coe (S := N.leftCoverSet) (i := false) ⟨u, hu⟩) τ

public theorem slideLeft_of_chartLeft (u : ↥U)
    (hu : (⟨u.1, Or.inl u.2⟩ : ↥(U ∪ V)) ∈ N.chartLeft) (τ : unitInterval) :
    N.slideLeft u τ = pointLeft U V u :=
  DFunLike.congr_fun
    (ContinuousMap.liftCover_coe (S := N.leftCoverSet) (i := true) ⟨u, hu⟩) τ

end ClosedNumeration

/-! #### Assembling the sliding homotopy on the double mapping cylinder -/

namespace ClosedNumeration

variable (N : ClosedNumeration U V)

/-- The sliding homotopy on the mapping-cylinder branch. -/
public def slideCylinder : TopCat.MappingCylinder (interToRight U V) ⟶
    TopCat.of C(unitInterval, ↥(Dmc U V)) :=
  pushout.desc N.slideCylMap (TopCat.ofHom N.slideBase) (by
    ext a τ
    exact (N.slideBase_of_mem_left ⟨a.1, a.2.2⟩ a.2.1 τ).symm)

public theorem slideCylinder_cyl (a : ↥(U ∩ V)) (t τ : unitInterval) :
    N.slideCylinder (TopCat.mappingCylinderCylinder (interToRight U V) (a, t)) τ =
      pointCyl U V a (slide (N.weightInter a) t τ) := by
  have h : TopCat.mappingCylinderCylinder (interToRight U V) ≫ N.slideCylinder =
      N.slideCylMap := pushout.inl_desc _ _ _
  exact DFunLike.congr_fun (CategoryTheory.congr_fun h (a, t)) τ

public theorem slideCylinder_base (v : ↥V) (τ : unitInterval) :
    N.slideCylinder (TopCat.mappingCylinderBase (interToRight U V) v) τ = N.slideBase v τ := by
  have h : TopCat.mappingCylinderBase (interToRight U V) ≫ N.slideCylinder =
      TopCat.ofHom N.slideBase := pushout.inr_desc _ _ _
  exact DFunLike.congr_fun (CategoryTheory.congr_fun h v) τ

/-- The sliding homotopy, as a map out of the double mapping cylinder. -/
public def slideDouble : Dmc U V ⟶ TopCat.of C(unitInterval, ↥(Dmc U V)) :=
  pushout.desc N.slideCylinder (TopCat.ofHom N.slideLeft) (by
    ext a τ
    show N.slideCylinder (TopCat.mappingCylinderCylinder (interToRight U V) (a, 1)) τ =
      N.slideLeft ⟨a.1, a.2.1⟩ τ
    rw [N.slideCylinder_cyl, N.slideLeft_of_mem_right ⟨a.1, a.2.1⟩ a.2.2])

public theorem slideDouble_pointCyl (a : ↥(U ∩ V)) (t τ : unitInterval) :
    N.slideDouble (pointCyl U V a t) τ = pointCyl U V a (slide (N.weightInter a) t τ) := by
  have h : TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V) ≫
      N.slideDouble = N.slideCylinder := pushout.inl_desc _ _ _
  exact (DFunLike.congr_fun (CategoryTheory.congr_fun h
    (TopCat.mappingCylinderCylinder (interToRight U V) (a, t))) τ).trans
      (N.slideCylinder_cyl a t τ)

public theorem slideDouble_pointRight (v : ↥V) (τ : unitInterval) :
    N.slideDouble (pointRight U V v) τ = N.slideBase v τ := by
  have h : TopCat.doubleMappingCylinderLeft (interToRight U V) (interToLeft U V) ≫
      N.slideDouble = N.slideCylinder := pushout.inl_desc _ _ _
  exact (DFunLike.congr_fun (CategoryTheory.congr_fun h
    (TopCat.mappingCylinderBase (interToRight U V) v)) τ).trans (N.slideCylinder_base v τ)

public theorem slideDouble_pointLeft (u : ↥U) (τ : unitInterval) :
    N.slideDouble (pointLeft U V u) τ = N.slideLeft u τ := by
  have h : TopCat.doubleMappingCylinderRight (interToRight U V) (interToLeft U V) ≫
      N.slideDouble = TopCat.ofHom N.slideLeft := pushout.inr_desc _ _ _
  exact DFunLike.congr_fun (CategoryTheory.congr_fun h u) τ

end ClosedNumeration

/-! #### The endpoints of the sliding homotopy -/

/-- Evaluation of a path of points of the double mapping cylinder at a parameter. -/
public def evalAt (U V : Set X) (τ : unitInterval) :
    TopCat.of C(unitInterval, ↥(Dmc U V)) ⟶ Dmc U V :=
  TopCat.ofHom ⟨fun f ↦ f τ, continuous_eval_const τ⟩

namespace ClosedNumeration

variable (N : ClosedNumeration U V)

public theorem slideBase_one (v : ↥V) : N.slideBase v 1 = pointRight U V v := by
  by_cases h : (⟨v.1, Or.inr v.2⟩ : ↥(U ∪ V)) ∈ N.chartRight
  · rw [N.slideBase_of_chartRight v h]
  · have hv : v.1 ∈ U := N.closure_ne_zero (not_not.1 h)
    rw [N.slideBase_of_mem_left v hv, slide_one, pointCyl_zero]

public theorem slideLeft_one (u : ↥U) : N.slideLeft u 1 = pointLeft U V u := by
  by_cases h : (⟨u.1, Or.inl u.2⟩ : ↥(U ∪ V)) ∈ N.chartLeft
  · rw [N.slideLeft_of_chartLeft u h]
  · have hu : u.1 ∈ V := N.closure_ne_one (not_not.1 h)
    rw [N.slideLeft_of_mem_right u hu, slide_one, pointCyl_one]

public theorem slideBase_zero (v : ↥V) :
    N.slideBase v 0 = N.sectionMap ⟨v.1, Or.inr v.2⟩ := by
  by_cases h : (⟨v.1, Or.inr v.2⟩ : ↥(U ∪ V)) ∈ N.chartRight
  · rw [N.slideBase_of_chartRight v h, N.sectionMap_of_chartRight _ h]
  · have hv : v.1 ∈ U := N.closure_ne_zero (not_not.1 h)
    rw [N.slideBase_of_mem_left v hv, slide_zero,
      N.sectionMap_of_chartBoth ⟨v.1, Or.inr v.2⟩ ⟨hv, v.2⟩]
    rfl

public theorem slideLeft_zero (u : ↥U) :
    N.slideLeft u 0 = N.sectionMap ⟨u.1, Or.inl u.2⟩ := by
  by_cases h : (⟨u.1, Or.inl u.2⟩ : ↥(U ∪ V)) ∈ N.chartLeft
  · rw [N.slideLeft_of_chartLeft u h, N.sectionMap_of_chartLeft _ h]
  · have hu : u.1 ∈ V := N.closure_ne_one (not_not.1 h)
    rw [N.slideLeft_of_mem_right u hu, slide_zero,
      N.sectionMap_of_chartBoth ⟨u.1, Or.inl u.2⟩ ⟨u.2, hu⟩]
    rfl

/-- At parameter one the sliding homotopy is the identity. -/
public theorem slideDouble_one (p : ↥(Dmc U V)) : N.slideDouble p 1 = p := by
  have h : N.slideDouble ≫ evalAt U V 1 = 𝟙 (Dmc U V) := by
    apply pushout.hom_ext
    · apply pushout.hom_ext
      · ext r
        show N.slideDouble (pointCyl U V r.1 r.2) 1 = pointCyl U V r.1 r.2
        rw [N.slideDouble_pointCyl, slide_one]
      · ext v
        show N.slideDouble (pointRight U V v) 1 = pointRight U V v
        rw [N.slideDouble_pointRight, N.slideBase_one]
    · ext u
      show N.slideDouble (pointLeft U V u) 1 = pointLeft U V u
      rw [N.slideDouble_pointLeft, N.slideLeft_one]
  exact CategoryTheory.congr_fun h p

/-- At parameter zero the sliding homotopy is the section after the collapse. -/
public theorem slideDouble_zero (p : ↥(Dmc U V)) :
    N.slideDouble p 0 = N.sectionMap (doubleMappingCylinderToUnion U V p) := by
  have h : N.slideDouble ≫ evalAt U V 0 =
      doubleMappingCylinderToUnion U V ≫ TopCat.ofHom N.sectionMap := by
    apply pushout.hom_ext
    · apply pushout.hom_ext
      · ext r
        show N.slideDouble (pointCyl U V r.1 r.2) 0 =
          N.sectionMap (doubleMappingCylinderToUnion U V (pointCyl U V r.1 r.2))
        rw [N.slideDouble_pointCyl, slide_zero, collapse_pointCyl,
          N.sectionMap_of_chartBoth _ r.1.2]
        rfl
      · ext v
        show N.slideDouble (pointRight U V v) 0 =
          N.sectionMap (doubleMappingCylinderToUnion U V (pointRight U V v))
        rw [N.slideDouble_pointRight, collapse_pointRight, N.slideBase_zero]
    · ext u
      show N.slideDouble (pointLeft U V u) 0 =
        N.sectionMap (doubleMappingCylinderToUnion U V (pointLeft U V u))
      rw [N.slideDouble_pointLeft, collapse_pointLeft, N.slideLeft_zero]
  exact CategoryTheory.congr_fun h p

end ClosedNumeration

/-! ### Dold's theorem for a closed numeration -/

namespace ClosedNumeration

variable (N : ClosedNumeration U V)

public theorem collapse_comp_sectionMap :
    (doubleMappingCylinderToUnion U V).hom.comp N.sectionMap = ContinuousMap.id ↥(U ∪ V) :=
  ContinuousMap.ext N.collapse_sectionMap

/-- The sliding homotopy from the section after the collapse to the identity of the double
mapping cylinder. -/
public def sourceHomotopy : ContinuousMap.Homotopy
    (N.sectionMap.comp (doubleMappingCylinderToUnion U V).hom)
    (ContinuousMap.id ↥(Dmc U V)) :=
  ⟨⟨fun q ↦ N.slideDouble q.2 q.1,
      (ContinuousMap.uncurry (TopCat.Hom.hom N.slideDouble)).continuous.comp continuous_swap⟩,
    fun p ↦ N.slideDouble_zero p, fun p ↦ N.slideDouble_one p⟩

/-- **Dold's theorem** for a two-set open cover with a closed numeration: the collapse of the
double mapping cylinder of the two inclusions of the overlap is a homotopy equivalence. -/
public theorem isHomotopyExcisiveSpan (N : ClosedNumeration U V) :
    TopCat.IsHomotopyExcisiveSpan (interToRight U V) (interToLeft U V) := by
  let eUnion : (↥(Dmc U V)) ≃ₕ ↥(U ∪ V) :=
    { toFun := (doubleMappingCylinderToUnion U V).hom
      invFun := N.sectionMap
      left_inv := ⟨N.sourceHomotopy⟩
      right_inv := by rw [N.collapse_comp_sectionMap] }
  let ePushout := eUnion.trans
    (pushoutHomeomorphUnion U V N.isOpen_left N.isOpen_right).symm.toHomotopyEquiv
  refine ⟨ePushout, ?_⟩
  funext p
  change unionToPushout U V N.isOpen_left N.isOpen_right
      (pushoutToUnion U V
        (TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V) p)) =
    TopCat.doubleMappingCylinderCollapse (interToRight U V) (interToLeft U V) p
  exact unionToPushout_pushoutToUnion U V N.isOpen_left N.isOpen_right _

end ClosedNumeration

/-- A normal paracompact union of two open sets admits a numeration with closed supports:
this is exactly a partition of unity subordinate to the cover. -/
public theorem exists_closedNumeration (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [NormalSpace ↥(U ∪ V)] [ParacompactSpace ↥(U ∪ V)] :
    Nonempty (ClosedNumeration U V) := by
  have hopen : ∀ i, IsOpen (unionCoverSet U V i) := by
    intro i
    cases i
    · exact hU.preimage continuous_subtype_val
    · exact hV.preimage continuous_subtype_val
  have hcover : (Set.univ : Set ↥(U ∪ V)) ⊆ ⋃ i, unionCoverSet U V i := by
    intro x _
    rcases x.2 with hxU | hxV
    · exact Set.mem_iUnion.2 ⟨false, hxU⟩
    · exact Set.mem_iUnion.2 ⟨true, hxV⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate
    (X := ↥(U ∪ V)) isClosed_univ (unionCoverSet U V) hopen hcover
  let w : C(↥(U ∪ V), unitInterval) :=
    ⟨fun x ↦ ⟨ρ false x, ρ.nonneg false x, ρ.le_one false x⟩, by fun_prop⟩
  have hsum : ∀ x : ↥(U ∪ V), ρ true x + ρ false x = 1 := by
    intro x
    have h := ρ.sum_eq_one (x := x) (Set.mem_univ x)
    rw [finsum_eq_sum_of_fintype, Fintype.sum_bool] at h
    exact h
  have hzero : {x : ↥(U ∪ V) | w x ≠ 0} = Function.support (ρ false) := by
    ext x
    constructor
    · intro hx h
      exact hx (Subtype.ext h)
    · intro hx h
      exact hx (congrArg Subtype.val h)
  have hone : {x : ↥(U ∪ V) | w x ≠ 1} = Function.support (ρ true) := by
    ext x
    constructor
    · intro hx h
      refine hx (Subtype.ext ?_)
      have := hsum x
      rw [h, zero_add] at this
      exact this
    · intro hx h
      have hval : ρ false x = 1 := congrArg Subtype.val h
      have := hsum x
      rw [hval] at this
      exact hx (by linarith)
  refine ⟨⟨w, hU, hV, ?_, ?_⟩⟩
  · rw [hzero]
    exact hρ false
  · rw [hone]
    exact hρ true

/-- The axiom-free replacement of `leftToUnion_isHomotopyEquivalence_of_normal_paracompact`:
for a normal paracompact open union, a homotopy equivalence from the overlap to the right member
makes the literal inclusion of the left member into the union a homotopy equivalence. -/
public theorem leftToUnion_isHomotopyEquivalence_of_normal_paracompact_proved
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [NormalSpace ↥(U ∪ V)] [ParacompactSpace ↥(U ∪ V)]
    (hinter : IsHomotopyEquivalence (interToRight U V).hom) :
    IsHomotopyEquivalence (leftToUnion U V).hom := by
  obtain ⟨N⟩ := exists_closedNumeration U V hU hV
  exact leftToUnion_isHomotopyEquivalence U V hU hV hinter N.isHomotopyExcisiveSpan

end ClosedCover








end SphereSixComplex
