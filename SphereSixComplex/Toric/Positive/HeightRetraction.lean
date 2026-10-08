module

public import SphereSixComplex.Toric.Positive.CompactSublevels
public import SphereSixComplex.Toric.Positive.InteriorTorus
public import ForMathlib.Topology.Collar.HomotopyEquivalence
public import ForMathlib.Topology.Collar.SmallPush

@[expose] public section
noncomputable section
open Function Set Topology
open scoped ContinuousMap unitInterval
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspCollar CuspPeriodExpansion

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

theorem exists_positiveQuotientHeight_sublevel_subset
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    {U : Set (PositiveQuotient W)} (hU : IsOpen U) (hcore : positiveQuotientCore W ⊆ U) :
    ∃ ε > 0, ε < W.localWitness.radius ∧ {y | positiveQuotientHeight W y < ε} ⊆ U := by
  let a := W.localWitness.radius / 2
  have ha : 0 < a := half_pos W.localWitness.radius_pos
  have har : a < W.localWitness.radius := half_lt_self W.localWitness.radius_pos
  let K := {y | positiveQuotientHeight W y ≤ a} ∩ Uᶜ
  have hK : IsCompact K :=
    (isCompact_positiveQuotientHeight_sublevel W a ha.le har).inter_right hU.isClosed_compl
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (positiveQuotientHeight W).continuous.continuousOn
    have hxpos : 0 < positiveQuotientHeight W x := by
      refine lt_of_le_of_ne (positiveQuotientHeight_nonneg W x) ?_
      intro heq
      exact hx.2 (hcore ((positiveQuotientHeight_eq_zero_iff W x).mp heq.symm))
    refine ⟨min a (positiveQuotientHeight W x), lt_min ha hxpos,
      (min_le_left _ _).trans_lt har, ?_⟩
    intro y hy
    change positiveQuotientHeight W y < _ at hy
    by_contra hyU
    have hyK : y ∈ K := ⟨hy.le.trans (min_le_left _ _), hyU⟩
    exact (not_lt_of_ge (hmin hyK)) (hy.trans_le (min_le_right _ _))
  · refine ⟨a, ha, har, ?_⟩
    intro y hy
    change positiveQuotientHeight W y < _ at hy
    by_contra hyU
    exact hne ⟨y, hy.le, hyU⟩

theorem constructedPositiveInteriorTorusHomeomorph_height
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (y : ↥((positiveQuotientCore W)ᶜ)) :
    ((constructedPositiveInteriorTorusHomeomorph W y).2 : ℝ) =
      positiveQuotientHeight W y.1 := by
  obtain ⟨p, rfl⟩ := constructedPositiveInteriorProjection_surjective W y
  rw [constructedPositiveInteriorTorusHomeomorph_projection]
  rfl

def positiveInteriorHeightMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : Set.Ioo (0 : ℝ) W.localWitness.radius) :
    C(↥((positiveQuotientCore W)ᶜ), ↥((positiveQuotientCore W)ᶜ)) :=
  let e := constructedPositiveInteriorTorusHomeomorph W
  ⟨fun y ↦ e.symm ((e y).1, a),
    e.symm.continuous.comp ((e.continuous.fst).prodMk continuous_const)⟩

def positiveInteriorHeightHomotopy
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : Set.Ioo (0 : ℝ) W.localWitness.radius) :
    (ContinuousMap.id ↥((positiveQuotientCore W)ᶜ)).Homotopy
      (positiveInteriorHeightMap W a) := by
  let e := constructedPositiveInteriorTorusHomeomorph W
  let h (t : unitInterval) (x : Set.Ioo (0 : ℝ) W.localWitness.radius) :
      Set.Ioo (0 : ℝ) W.localWitness.radius :=
    ⟨(1 - (t : ℝ)) * x.1 + t * a.1, by
      exact (convex_Ioo (0 : ℝ) W.localWitness.radius) x.2 a.2
        (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 (t : ℝ))⟩
  refine ⟨⟨fun p ↦ e.symm ((e p.2).1, h p.1 (e p.2).2), ?_⟩, ?_, ?_⟩
  · apply e.symm.continuous.comp
    refine (e.continuous.comp continuous_snd).fst.prodMk ?_
    apply Continuous.subtype_mk
    exact ((continuous_const.sub continuous_fst.subtype_val).mul
      (e.continuous.comp continuous_snd).snd.subtype_val).add
      (continuous_fst.subtype_val.mul continuous_const)
  · intro y
    change e.symm ((e y).1, h 0 (e y).2) = y
    have hh : h 0 (e y).2 = (e y).2 := by apply Subtype.ext; simp [h]
    rw [hh, Prod.mk.eta, e.symm_apply_apply]
  · intro y
    change e.symm ((e y).1, h 1 (e y).2) = e.symm ((e y).1, a)
    have hh : h 1 (e y).2 = a := by apply Subtype.ext; simp [h]
    rw [hh]

theorem positiveInteriorHeightHomotopy_height
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : Set.Ioo (0 : ℝ) W.localWitness.radius)
    (t : unitInterval) (y : ↥((positiveQuotientCore W)ᶜ)) :
    positiveQuotientHeight W (positiveInteriorHeightHomotopy W a (t, y)).1 =
      (1 - (t : ℝ)) * positiveQuotientHeight W y.1 + t * a.1 := by
  rw [← constructedPositiveInteriorTorusHomeomorph_height]
  change ((constructedPositiveInteriorTorusHomeomorph W
    ((constructedPositiveInteriorTorusHomeomorph W).symm _)).2 : ℝ) = _
  rw [Homeomorph.apply_symm_apply]
  simp only [constructedPositiveInteriorTorusHomeomorph_height]


theorem positiveQuotientCore_isHomotopyEquivalence
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsHomotopyEquivalence (Subtype.val : positiveQuotientCore W → PositiveQuotient W) := by
  let _ := constructedPositiveQuotient_metrizable W
  let c := constructedPositiveQuotientCollar W
  obtain ⟨w⟩ := c.nonempty_pushWeight (isClosed_positiveDeck_orbitCore W)
  obtain ⟨ε, hε, hεr, hεU⟩ := exists_positiveQuotientHeight_sublevel_subset W
    c.neighborhood.2 c.boundary_subset
  let V := {y | positiveQuotientHeight W y < ε}
  have hV : IsOpen V := isOpen_lt (positiveQuotientHeight W).continuous continuous_const
  have hBV : positiveQuotientCore W ⊆ V := by
    intro b hb
    change positiveQuotientHeight W b < ε
    rw [(positiveQuotientHeight_eq_zero_iff W b).mpr hb]
    exact hε
  obtain ⟨τ, hτ, hτV⟩ := c.exists_pos_forall_push_mem w (isCompact_positiveQuotientCore W) hV hBV
  let a : Set.Ioo (0 : ℝ) W.localWitness.radius :=
    ⟨ε / 2, half_pos hε, (half_lt_self hε).trans hεr⟩
  let i : C(↥((positiveQuotientCore W)ᶜ), PositiveQuotient W) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(PositiveQuotient W, ↥((positiveQuotientCore W)ᶜ)) :=
    ⟨fun x ↦ ⟨c.push w.weight τ x, c.push_pos_notMem_boundary w τ hτ x⟩,
      ((c.continuous_push w.weight w.inner w.closure_subset w.zero_outside).comp
        (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let F : (ContinuousMap.id (PositiveQuotient W)).Homotopy (i.comp g) :=
    { toFun := fun p ↦ c.push w.weight (p.1 * τ) p.2
      continuous_toFun :=
        (c.continuous_push w.weight w.inner w.closure_subset w.zero_outside).comp
          ((continuous_fst.mul continuous_const).prodMk continuous_snd)
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp [i, g] }
  let G : (i.comp g).Homotopy (i.comp ((positiveInteriorHeightMap W a).comp g)) :=
    (ContinuousMap.Homotopy.refl i).comp
      ((positiveInteriorHeightHomotopy W a).compContinuousMap g)
  have hF (t : unitInterval) (b : positiveQuotientCore W) : F (t, b.1) ∈ c.neighborhood := by
    apply hεU
    exact hτV (t * τ) (by
      change (t : ℝ) * τ ≤ τ
      exact mul_le_of_le_one_left τ.2.1 t.2.2) b b.2
  have hG (t : unitInterval) (b : positiveQuotientCore W) : G (t, b.1) ∈ c.neighborhood := by
    apply hεU
    change positiveQuotientHeight W (positiveInteriorHeightHomotopy W a (t, g b.1)).1 < ε
    rw [positiveInteriorHeightHomotopy_height]
    have hb : positiveQuotientHeight W (g b.1).1 < ε := hτV τ le_rfl b b.2
    exact (convex_Iio ε) hb (half_lt_self hε)
      (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 (t : ℝ))
  apply c.isHomotopyEquivalence_subtypeVal_of_homotopy (F.trans G)
  · intro x
    apply hεU
    have hh := positiveInteriorHeightHomotopy_height W a 1 (g x)
    change positiveQuotientHeight W (positiveInteriorHeightMap W a (g x)).1 < ε
    simp only [ContinuousMap.Homotopy.apply_one, Set.Icc.coe_one,
      sub_self, zero_mul, one_mul, zero_add] at hh
    exact hh.trans_lt (half_lt_self hε)
  · intro t b
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hF _ b
    · exact hG _ b


end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
