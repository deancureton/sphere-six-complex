module

public import SphereSixComplex.Geometry.StandardInfiniteA2PositiveQuadrantAtlas

@[expose] public section

noncomputable section

open Function Set Topology WithLp
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public def positiveQuadrantScale (c : Fin 3 → ℝ) (hc : ∀ i, 0 ≤ c i)
    (u : EuclideanQuadrant 3) : EuclideanQuadrant 3 :=
  ⟨toLp 2 (fun i ↦ c i * u.1 i), fun i ↦ mul_nonneg (hc i) (u.2 i)⟩

public theorem positiveQuadrantScale_contMDiff (c : Fin 3 → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ContMDiff (modelWithCornersEuclideanQuadrant 3) (modelWithCornersEuclideanQuadrant 3)
      1 (positiveQuadrantScale c hc) := by
  have hs : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) ↦
      toLp 2 (fun i ↦ c i * x i)) := by
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp (by fun_prop)
  intro u
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · apply Continuous.continuousAt
    apply Continuous.subtype_mk
    exact hs.continuous.comp continuous_subtype_val
  · apply hs.contDiffWithinAt.congr
    · rintro x ⟨v, rfl⟩
      change (positiveQuadrantScale c hc
        ((modelWithCornersEuclideanQuadrant 3).symm
          (modelWithCornersEuclideanQuadrant 3 v))).1 = _
      rw [(modelWithCornersEuclideanQuadrant 3).left_inv v]
      rfl
    · change (positiveQuadrantScale c hc
        ((modelWithCornersEuclideanQuadrant 3).symm
          (modelWithCornersEuclideanQuadrant 3 u))).1 = _
      rw [(modelWithCornersEuclideanQuadrant 3).left_inv u]
      rfl

public def positiveTorusShear (g : DenseTorus)
    (hg : ∀ i, 0 < (g i : ℂ).re ∧ (g i : ℂ).im = 0)
    (lambda : CuspFilling.ParameterLattice) (x : carrierPositivePart) : carrierPositivePart :=
  ⟨carrierTorusAction g (carrierFanShearFun lambda x.1),
    carrierPositivePart_torusAction_fanShear g hg lambda x.2⟩

public theorem positiveTorusShear_chart (g : DenseTorus)
    (hg : ∀ i, 0 < (g i : ℂ).re ∧ (g i : ℂ).im = 0)
    (lambda : CuspFilling.ParameterLattice) (a : ChartIndex) (u : EuclideanQuadrant 3) :
    positiveTorusShear g hg lambda (carrierPositiveQuadrantChart a u) =
      carrierPositiveQuadrantChart (translateChartIndex lambda a)
        (positiveQuadrantScale (fun i ↦ ‖torusChartCoordinates (translateChartIndex lambda a) g i‖)
          (fun _i ↦ norm_nonneg _) u) := by
  have hc := torusChartCoordinates_denseTorusModulus (translateChartIndex lambda a) g
  rw [denseTorusModulus_eq_self_of_positive g hg] at hc
  apply Subtype.ext
  change carrierTorusActionFun g (carrierFanShearFun lambda
    (inclusion a (fun i ↦ (u.1 i : ℂ)))) = _
  rw [carrierFanShearFun_inclusion, carrierTorusActionFun_inclusion,
    carrierPositiveQuadrantChart_coe]
  congr 1
  funext i
  have hi := congrFun hc i
  change torusChartCoordinates (translateChartIndex lambda a) g i =
    (‖torusChartCoordinates (translateChartIndex lambda a) g i‖ : ℂ) at hi
  simp only [Pi.mul_apply, positiveQuadrantScale, ofLp_toLp, Complex.ofReal_mul]
  exact congrArg (fun z : ℂ ↦ z * (u.1 i : ℂ)) hi

public theorem positiveTorusShear_contMDiff (g : DenseTorus)
    (hg : ∀ i, 0 < (g i : ℂ).re ∧ (g i : ℂ).im = 0)
    (lambda : CuspFilling.ParameterLattice) :
    letI := positiveQuadrantChartedSpace
    ContMDiff (modelWithCornersEuclideanQuadrant 3) (modelWithCornersEuclideanQuadrant 3)
      1 (positiveTorusShear g hg lambda) := by
  let _ := positiveQuadrantChartedSpace
  let _ := positiveQuadrantIsManifold
  intro x
  let a := positivePreferredChart x
  let b := translateChartIndex lambda a
  have ha : (positiveQuadrantParametrization a).symm ∈
      IsManifold.maximalAtlas (modelWithCornersEuclideanQuadrant 3) 1 carrierPositivePart :=
    IsManifold.subset_maximalAtlas (mem_range_self a)
  have hb : (positiveQuadrantParametrization b).symm ∈
      IsManifold.maximalAtlas (modelWithCornersEuclideanQuadrant 3) 1 carrierPositivePart :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  have hx : x ∈ (positiveQuadrantParametrization a).symm.source := by
    simpa [positiveQuadrantParametrization, a] using positivePreferredChart_mem x
  let scale := positiveQuadrantScale (fun i ↦ ‖torusChartCoordinates b g i‖)
    (fun i ↦ norm_nonneg _)
  have hf := (positiveQuadrantScale_contMDiff (fun i ↦ ‖torusChartCoordinates b g i‖)
    (fun i ↦ norm_nonneg _)).contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas ha hx)
  have hi := contMDiffAt_symm_of_mem_maximalAtlas hb
    (show scale ((positiveQuadrantParametrization a).symm x) ∈
      (positiveQuadrantParametrization b).symm.target by
        simp [positiveQuadrantParametrization])
  apply (hi.comp x hf).congr_of_eventuallyEq
  filter_upwards [(positiveQuadrantParametrization a).symm.open_source.mem_nhds hx] with y hy
  have he := (positiveQuadrantParametrization a).right_inv hy
  change carrierPositiveQuadrantChart a ((positiveQuadrantParametrization a).symm y) = y at he
  conv_lhs => rw [← he]
  exact positiveTorusShear_chart g hg lambda a _

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
