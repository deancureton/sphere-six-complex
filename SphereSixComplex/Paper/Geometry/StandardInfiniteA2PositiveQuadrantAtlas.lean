module

public import SphereSixComplex.Paper.Geometry.StandardInfiniteA2ToricPolarModulus
public import Mathlib.Geometry.Manifold.Instances.Real

@[expose] public section

noncomputable section

open Function Set Topology WithLp
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

public def positiveQuadrantHomeomorph : EuclideanQuadrant 3 ≃ₜ PositiveOrthant where
  toFun u := ⟨fun i ↦ u.1 i, u.2⟩
  invFun u := ⟨toLp 2 u.1, u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i ↦ (EuclideanSpace.proj i).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp continuous_subtype_val

public def carrierPositiveQuadrantChart (a : ChartIndex) :
    EuclideanQuadrant 3 → carrierPositivePart :=
  carrierPositiveChart a ∘ positiveQuadrantHomeomorph

public theorem carrierPositiveQuadrantChart_isOpenEmbedding (a : ChartIndex) :
    IsOpenEmbedding (carrierPositiveQuadrantChart a) :=
  (carrierPositiveChart_isOpenEmbedding a).comp positiveQuadrantHomeomorph.isOpenEmbedding

public theorem carrierPositiveQuadrantChart_jointly_surjective (x : carrierPositivePart) :
    ∃ a u, carrierPositiveQuadrantChart a u = x := by
  obtain ⟨a, u, hu⟩ := carrierPositiveChart_jointly_surjective x
  exact ⟨a, positiveQuadrantHomeomorph.symm u, by
    simpa [carrierPositiveQuadrantChart] using hu⟩

public def positiveQuadrantParametrization (a : ChartIndex) :
    OpenPartialHomeomorph (EuclideanQuadrant 3) carrierPositivePart :=
  (carrierPositiveQuadrantChart_isOpenEmbedding a).toOpenPartialHomeomorph
    (carrierPositiveQuadrantChart a)

public def positivePreferredChart (x : carrierPositivePart) : ChartIndex :=
  (carrierPositiveQuadrantChart_jointly_surjective x).choose

public theorem positivePreferredChart_mem (x : carrierPositivePart) :
    x ∈ range (carrierPositiveQuadrantChart (positivePreferredChart x)) :=
  (carrierPositiveQuadrantChart_jointly_surjective x).choose_spec

@[instance_reducible]
public def positiveQuadrantChartedSpace : ChartedSpace (EuclideanQuadrant 3) carrierPositivePart where
  atlas := range (fun a : ChartIndex ↦ (positiveQuadrantParametrization a).symm)
  chartAt x := (positiveQuadrantParametrization (positivePreferredChart x)).symm
  mem_chart_source x := by
    simpa [positiveQuadrantParametrization] using positivePreferredChart_mem x
  chart_mem_atlas _ := mem_range_self _

public theorem carrierPositiveQuadrantChart_coe (a : ChartIndex) (u : EuclideanQuadrant 3) :
    (carrierPositiveQuadrantChart a u : Carrier) = inclusion a (fun i ↦ (u.1 i : ℂ)) := rfl

public theorem positiveQuadrantParametrization_transition (a b : ChartIndex)
    {u : EuclideanQuadrant 3}
    (hu : carrierPositiveQuadrantChart a u ∈ range (carrierPositiveQuadrantChart b)) :
    (fun i ↦ (u.1 i : ℂ)) ∈ (chartChange a b).source ∧
      (fun i ↦ (((positiveQuadrantParametrization b).symm
        (carrierPositiveQuadrantChart a u)).1 i : ℂ)) =
        chartChange a b (fun i ↦ (u.1 i : ℂ)) := by
  obtain ⟨v, hv⟩ := hu
  have he := (inclusion_eq_iff a b (fun i ↦ (u.1 i : ℂ))
    (fun i ↦ (v.1 i : ℂ))).mp (congrArg Subtype.val hv.symm)
  refine ⟨he.1, ?_⟩
  rw [← hv]
  rw [show (positiveQuadrantParametrization b).symm (carrierPositiveQuadrantChart b v) = v
    from (carrierPositiveQuadrantChart_isOpenEmbedding b).toOpenPartialHomeomorph_left_inv]
  exact he.2.symm

public def positiveRealChartChange (a b : ChartIndex)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  toLp 2 (fun i ↦ (chartChange a b (fun j ↦ (x j : ℂ)) i).re)

public theorem positiveRealChartChange_contDiffOn (a b : ChartIndex) :
    ContDiffOn ℝ 1 (positiveRealChartChange a b)
      {x | (fun j ↦ (x j : ℂ)) ∈ (chartChange a b).source} := by
  have hin : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 3) ↦
      (fun j ↦ (x j : ℂ))) := by
    apply contDiff_pi.mpr
    intro j
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ j).comp (EuclideanSpace.equiv (Fin 3) ℝ).contDiff)
  have hout : ContDiff ℝ 1 (fun z : RawCoordinates ↦ toLp 2 (fun i ↦ (z i).re)) := by
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp (contDiff_pi.mpr fun i ↦
      Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ i))
  exact hout.comp_contDiffOn
    (((chartChange_contDiffOn a b).of_le (by simp : (1 : ℕ∞ω) ≤ ω)).restrict_scalars ℝ |>.comp
      hin.contDiffOn (fun _ h ↦ h))

public theorem positiveQuadrantIsManifold :
    letI := positiveQuadrantChartedSpace
    IsManifold (modelWithCornersEuclideanQuadrant 3) 1 carrierPositivePart := by
  let _ := positiveQuadrantChartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := he'
  have h (x : EuclideanSpace ℝ (Fin 3))
      (hx : x ∈ (modelWithCornersEuclideanQuadrant 3).symm ⁻¹'
        ((positiveQuadrantParametrization a).trans
          (positiveQuadrantParametrization b).symm).source ∩
            range (modelWithCornersEuclideanQuadrant 3)) :
      (fun j ↦ (x j : ℂ)) ∈ (chartChange a b).source ∧
      ((modelWithCornersEuclideanQuadrant 3) ∘
        (positiveQuadrantParametrization a).trans (positiveQuadrantParametrization b).symm ∘
          (modelWithCornersEuclideanQuadrant 3).symm) x = positiveRealChartChange a b x := by
    obtain ⟨u, rfl⟩ := hx.2
    have hu : (modelWithCornersEuclideanQuadrant 3).symm
        (modelWithCornersEuclideanQuadrant 3 u) = u := by
      exact (modelWithCornersEuclideanQuadrant 3).left_inv u
    have hm : carrierPositiveQuadrantChart a u ∈ range (carrierPositiveQuadrantChart b) := by
      have hh := hx.1.2
      rw [hu] at hh
      simpa [positiveQuadrantParametrization] using hh
    have ht := positiveQuadrantParametrization_transition a b hm
    refine ⟨ht.1, ?_⟩
    change (modelWithCornersEuclideanQuadrant 3)
      ((positiveQuadrantParametrization b).symm
        (carrierPositiveQuadrantChart a
          ((modelWithCornersEuclideanQuadrant 3).symm
            (modelWithCornersEuclideanQuadrant 3 u)))) = _
    rw [hu]
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    funext i
    have hi := congrArg (fun z : RawCoordinates ↦ (z i).re) ht.2
    simpa [Function.comp_def, hu, positiveRealChartChange, positiveQuadrantParametrization] using hi
  exact ((positiveRealChartChange_contDiffOn a b).mono (fun x hx ↦ (h x hx).1)).congr
    (fun x hx ↦ (h x hx).2)

public theorem positiveQuadrant_boundary :
    letI := positiveQuadrantChartedSpace
    (modelWithCornersEuclideanQuadrant 3).boundary carrierPositivePart =
      {x | carrierHeight x.1 = 0} := by
  let _ := positiveQuadrantChartedSpace
  ext x
  let a := positivePreferredChart x
  let u := (positiveQuadrantParametrization a).symm x
  have hu : carrierPositiveQuadrantChart a u = x := by
    apply (positiveQuadrantParametrization a).right_inv
    simpa [positiveQuadrantParametrization, a] using positivePreferredChart_mem x
  have hheight : carrierHeight x.1 = (u.1 0 : ℂ) * (u.1 1 : ℂ) * (u.1 2 : ℂ) := by
    rw [← hu, carrierPositiveQuadrantChart_coe, carrierHeight_inclusion]
    rfl
  change (modelWithCornersEuclideanQuadrant 3).IsBoundaryPoint x ↔ _
  rw [ModelWithCorners.isBoundaryPoint_iff]
  change u.1 ∈ frontier (range (modelWithCornersEuclideanQuadrant 3)) ↔ _
  rw [frontier, (modelWithCornersEuclideanQuadrant 3).isClosed_range.closure_eq,
    show range (modelWithCornersEuclideanQuadrant 3) =
      {y : EuclideanSpace ℝ (Fin 3) | ∀ i, 0 ≤ y i} from range_euclideanQuadrant 3,
    interior_euclideanQuadrant]
  simp only [mem_sdiff, mem_ofPred_eq]
  rw [hheight]
  simp only [mul_eq_zero, Complex.ofReal_eq_zero]
  constructor
  · rintro ⟨_, hn⟩
    by_contra he
    apply hn
    intro i
    fin_cases i <;> apply lt_of_le_of_ne (u.2 _) <;> tauto
  · intro hz
    refine ⟨u.2, ?_⟩
    intro hp
    rcases hz with (h | h) | h
    · exact (ne_of_gt (hp 0)) h
    · exact (ne_of_gt (hp 1)) h
    · exact (ne_of_gt (hp 2)) h

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
