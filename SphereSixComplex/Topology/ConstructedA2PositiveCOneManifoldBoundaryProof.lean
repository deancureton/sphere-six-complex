module

public import SphereSixComplex.Topology.ConstructedA2PositiveQuotientRelativeCWProof

/-!
# The global quadrant target for the constructed A₂ positive carrier

The logarithmic position-height target is identified with the open subset
`(0, ∞) × (0, ∞) × [0, r)` of the three-dimensional Euclidean quadrant.  Its
manifold boundary is exactly its zero-height locus.
-/

@[expose] public section

noncomputable section

open Function Set TopologicalSpace Topology WithLp

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The open quadrant target of the exponential log-position and height coordinates. -/
public def constructedA2PositiveQuadrantTarget (r : ℝ) : Opens (EuclideanQuadrant 3) where
  carrier := {u | 0 < u.1 0 ∧ 0 < u.1 1 ∧ u.1 2 < r}
  is_open' := by
    have h (i : Fin 3) : Continuous (fun u : EuclideanQuadrant 3 ↦ u.1 i) := by fun_prop
    have h₀ : IsOpen {u : EuclideanQuadrant 3 | (0 : ℝ) < u.1 0} :=
      isOpen_lt continuous_const (h 0)
    have h₁ : IsOpen {u : EuclideanQuadrant 3 | (0 : ℝ) < u.1 1} :=
      isOpen_lt continuous_const (h 1)
    have h₂ : IsOpen {u : EuclideanQuadrant 3 | u.1 2 < r} :=
      isOpen_lt (h 2) continuous_const
    have heq :
        {u : EuclideanQuadrant 3 | 0 < u.1 0 ∧ 0 < u.1 1 ∧ u.1 2 < r} =
          ({u : EuclideanQuadrant 3 | 0 < u.1 0} ∩
            {u : EuclideanQuadrant 3 | 0 < u.1 1}) ∩
              {u : EuclideanQuadrant 3 | u.1 2 < r} := by
      ext u
      simp only [mem_ofPred_eq, mem_inter_iff]
      tauto
    rw [heq]
    exact (h₀.inter h₁).inter h₂

public theorem constructedA2PositiveQuadrantTarget_nonempty {r : ℝ} (hr : 0 < r) :
    Nonempty (constructedA2PositiveQuadrantTarget r) := by
  let u : EuclideanQuadrant 3 :=
    ⟨toLp 2 ![1, 1, 0], by intro i; fin_cases i <;> norm_num⟩
  exact ⟨⟨u, by simp [constructedA2PositiveQuadrantTarget, u, hr]⟩⟩

/-- Exponentiating the two logarithmic coordinates identifies the moment strip with the open
quadrant target. -/
public noncomputable def constructedA2MomentQuadrantHomeomorph (r : ℝ) :
    constructedPositiveMomentRegion r ≃ₜ constructedA2PositiveQuadrantTarget r where
  toFun x := ⟨⟨toLp 2 ![Real.exp (x.1 0), Real.exp (x.1 1), x.1 2], by
    intro i
    fin_cases i
    · exact (Real.exp_pos _).le
    · exact (Real.exp_pos _).le
    · exact x.2.1⟩, by
      change 0 < Real.exp (x.1 0) ∧ 0 < Real.exp (x.1 1) ∧ x.1 2 < r
      exact ⟨Real.exp_pos _, Real.exp_pos _, x.2.2⟩⟩
  invFun u := ⟨![Real.log (u.1.1 0), Real.log (u.1.1 1), u.1.1 2], by
    have hu : 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r := by
      have hmem := u.2
      change 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r at hmem
      exact hmem
    change 0 ≤ u.1.1 2 ∧ u.1.1 2 < r
    exact ⟨u.1.2 2, hu.2.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv u := by
    have hu : 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r := by
      have hmem := u.2
      change 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r at hmem
      exact hmem
    apply Subtype.ext
    apply EuclideanQuadrant.ext
    ext i
    fin_cases i
    · exact Real.exp_log hu.1
    · exact Real.exp_log hu.2.1
    · rfl
  continuous_toFun := by
    have hcoord (i : Fin 3) :
        Continuous (fun x : constructedPositiveMomentRegion r ↦ x.1 i) :=
      (continuous_apply i).comp continuous_subtype_val
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp
    · exact Real.continuous_exp.comp (hcoord 0)
    · exact Real.continuous_exp.comp (hcoord 1)
    · exact hcoord 2
  continuous_invFun := by
    have hcoord (i : Fin 3) :
        Continuous (fun u : constructedA2PositiveQuadrantTarget r ↦ u.1.1 i) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp continuous_subtype_val).comp
        continuous_subtype_val
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · simp
      exact Continuous.log (hcoord 0) fun u ↦ (by
        have hu : 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r := by
          have hmem := u.2
          change 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r at hmem
          exact hmem
        exact hu.1.ne')
    · simp
      exact Continuous.log (hcoord 1) fun u ↦ (by
        have hu : 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r := by
          have hmem := u.2
          change 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r at hmem
          exact hmem
        exact hu.2.1.ne')
    · simpa using hcoord 2

public theorem constructedA2PositiveQuadrantTarget_boundary (r : ℝ) :
    (modelWithCornersEuclideanQuadrant 3).boundary
        (constructedA2PositiveQuadrantTarget r) =
      {u | u.1.1 2 = 0} := by
  rw [ModelWithCorners.boundary_open]
  ext u
  have hu : 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r := by
    have hmem := u.2
    change 0 < u.1.1 0 ∧ 0 < u.1.1 1 ∧ u.1.1 2 < r at hmem
    exact hmem
  change (modelWithCornersEuclideanQuadrant 3).IsBoundaryPoint
      (u.1 : EuclideanQuadrant 3) ↔ u.1.1 2 = 0
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt_self_apply, frontier]
  rw [(modelWithCornersEuclideanQuadrant 3).isClosed_range.closure_eq]
  rw [show range (modelWithCornersEuclideanQuadrant 3) =
      {y : EuclideanSpace ℝ (Fin 3) | ∀ i, 0 ≤ y i} from range_euclideanQuadrant 3]
  rw [interior_euclideanQuadrant]
  simp only [modelWithCornersEuclideanQuadrant_apply, mem_sdiff, mem_ofPred_eq]
  constructor
  · rintro ⟨_, hnot⟩
    by_contra hne
    apply hnot
    intro i
    fin_cases i
    · exact hu.1
    · exact hu.2.1
    · exact lt_of_le_of_ne (u.1.2 2) (Ne.symm hne)
  · intro hzero
    exact ⟨u.1.2, fun hpos ↦ (ne_of_gt (hpos 2)) hzero⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
