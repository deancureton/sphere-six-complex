module

public import SphereSixComplex.Topology.BoundarySevenRealizationInjective
public import SphereSixComplex.Topology.BoundarySevenFaceNeighborhoodComparison
public import SphereSixComplex.Topology.HomotopySphereHomology

/-!
# Deformation of a boundary-face neighbourhood onto its face

For a fixed barycentric coordinate `i`, the open subset `w i < 1 / 8` of the boundary of the
standard seven-simplex deformation retracts onto the face `w i = 0`.  The retraction sets the
`i`-th coordinate to zero and divides all other coordinates by `1 - w i`.

This file develops the affine formula independently of the total-complex argument.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap Set Simplicial

namespace SphereSixComplex

/-- The ordinary barycentric version of the `i`-th open face neighbourhood. -/
public def standardBoundarySevenFaceNeighborhood (i : Fin 8) :
    Set (StandardSimplexBoundary 7) :=
  {w | w.1 i < (1 : ℝ) / 8}

/-- On the `i`-th face neighbourhood, the sum of the other coordinates is positive. -/
public theorem standardBoundarySevenFaceNeighborhood_one_sub_pos
    (i : Fin 8) (w : standardBoundarySevenFaceNeighborhood i) :
    0 < 1 - w.1.1 i := by
  have hw : w.1.1 i < (1 : ℝ) / 8 := w.2
  linarith

/-- Delete the `i`-th coordinate and renormalize the remaining seven coordinates. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodRetractionCoordinates
    (i : Fin 8) (w : standardBoundarySevenFaceNeighborhood i) :
    stdSimplex ℝ (Fin 7) := by
  let d : ℝ := 1 - w.1.1 i
  have hd : 0 < d := standardBoundarySevenFaceNeighborhood_one_sub_pos i w
  refine ⟨fun j ↦ w.1.1 (i.succAbove j) / d, ⟨?_, ?_⟩⟩
  · intro j
    exact div_nonneg (w.1.1.2.1 _) hd.le
  · have hsum := w.1.1.2.2
    change (∑ k : Fin 8, w.1.1 k) = 1 at hsum
    have hother : (∑ j : Fin 7, w.1.1 (i.succAbove j)) = d := by
      rw [Fin.sum_univ_succAbove (fun k ↦ w.1.1 k) i] at hsum
      dsimp [d]
      linarith
    rw [← Finset.sum_div, hother, div_self hd.ne']

/-- The retraction coordinates vary continuously over the open face neighbourhood. -/
public theorem continuous_standardBoundarySevenFaceNeighborhoodRetractionCoordinates
    (i : Fin 8) :
    Continuous (standardBoundarySevenFaceNeighborhoodRetractionCoordinates i) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact (((continuous_apply (i.succAbove j)).comp
      (continuous_subtype_val.comp continuous_subtype_val)).comp
        continuous_subtype_val).div
    (continuous_const.sub
      (((continuous_apply i).comp
        (continuous_subtype_val.comp continuous_subtype_val)).comp
          continuous_subtype_val))
    (fun w ↦ (standardBoundarySevenFaceNeighborhood_one_sub_pos i w).ne')

/-- The normalized point, reinserted as a point of the ordinary boundary. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodProjection
    (i : Fin 8) (w : standardBoundarySevenFaceNeighborhood i) :
    StandardSimplexBoundary 7 :=
  ⟨stdSimplex.map i.succAbove
      (standardBoundarySevenFaceNeighborhoodRetractionCoordinates i w),
    ⟨i, stdSimplex_map_succAbove_apply_self i _⟩⟩

/-- The projection varies continuously. -/
public theorem continuous_standardBoundarySevenFaceNeighborhoodProjection
    (i : Fin 8) :
    Continuous (standardBoundarySevenFaceNeighborhoodProjection i) := by
  apply Continuous.subtype_mk
  exact (stdSimplex.continuous_map i.succAbove).comp
    (continuous_standardBoundarySevenFaceNeighborhoodRetractionCoordinates i)

/-- The projected point still belongs to the same open face neighbourhood. -/
public theorem standardBoundarySevenFaceNeighborhoodProjection_mem
    (i : Fin 8) (w : standardBoundarySevenFaceNeighborhood i) :
    standardBoundarySevenFaceNeighborhoodProjection i w ∈
      standardBoundarySevenFaceNeighborhood i := by
  change (standardBoundarySevenFaceNeighborhoodProjection i w).1 i < (1 : ℝ) / 8
  rw [standardBoundarySevenFaceNeighborhoodProjection,
    stdSimplex_map_succAbove_apply_self]
  norm_num

/-- The projection, as a self-map of the open neighbourhood. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodProjectionSelf
    (i : Fin 8) :
    C(standardBoundarySevenFaceNeighborhood i,
      standardBoundarySevenFaceNeighborhood i) :=
  ⟨fun w ↦ ⟨standardBoundarySevenFaceNeighborhoodProjection i w,
      standardBoundarySevenFaceNeighborhoodProjection_mem i w⟩,
    (continuous_standardBoundarySevenFaceNeighborhoodProjection i).subtype_mk _⟩

/-- Every coordinate which vanishes before projection also vanishes after projection. -/
public theorem standardBoundarySevenFaceNeighborhoodProjection_apply_eq_zero
    (i k : Fin 8) (w : standardBoundarySevenFaceNeighborhood i)
    (hk : w.1.1 k = 0) :
    (standardBoundarySevenFaceNeighborhoodProjection i w).1 k = 0 := by
  rcases Fin.eq_self_or_eq_succAbove i k with hik | ⟨j, hj⟩
  · subst k
    exact stdSimplex_map_succAbove_apply_self i _
  · subst k
    rw [standardBoundarySevenFaceNeighborhoodProjection,
      stdSimplex_map_apply_of_injective i.succAbove
        Fin.succAbove_right_injective]
    change w.1.1 (i.succAbove j) /
      (1 - w.1.1 i) = 0
    rw [hk, zero_div]

/-- Linear interpolation from a point of the neighbourhood to its normalized face projection. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodHomotopyPoint
    (i : Fin 8) (q : unitInterval × standardBoundarySevenFaceNeighborhood i) :
    standardBoundarySevenFaceNeighborhood i := by
  let t : ℝ := q.1
  let w := q.2
  let p := standardBoundarySevenFaceNeighborhoodProjection i w
  let z : Fin 8 → ℝ := fun k ↦ (1 - t) * w.1.1 k + t * p.1 k
  have hz_nonneg : ∀ k, 0 ≤ z k := by
    intro k
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr q.1.2.2) (w.1.1.2.1 k))
      (mul_nonneg q.1.2.1 (p.1.2.1 k))
  have hz_sum : ∑ k, z k = 1 := by
    dsimp [z]
    have hw_sum : (∑ k : Fin 8, w.1.1 k) = 1 := w.1.1.2.2
    have hp_sum : (∑ k : Fin 8, p.1 k) = 1 := p.1.2.2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hw_sum, hp_sum]
    ring
  have hz_boundary : ∃ k, z k = 0 := by
    obtain ⟨k, hk⟩ := w.1.2
    refine ⟨k, ?_⟩
    dsimp [z]
    rw [hk, standardBoundarySevenFaceNeighborhoodProjection_apply_eq_zero i k w hk]
    ring
  let zs : stdSimplex ℝ (Fin 8) := ⟨z, ⟨hz_nonneg, hz_sum⟩⟩
  let zb : StandardSimplexBoundary 7 := ⟨zs, hz_boundary⟩
  refine ⟨zb, ?_⟩
  have hpi : p.1 i = 0 := stdSimplex_map_succAbove_apply_self i _
  have hwi_nonneg : 0 ≤ w.1.1 i := w.1.1.2.1 i
  have hwi_lt : w.1.1 i < (1 : ℝ) / 8 := w.2
  have ht0 : 0 ≤ t := q.1.2.1
  have ht1 : t ≤ 1 := q.1.2.2
  change z i < (1 : ℝ) / 8
  dsimp [z]
  rw [hpi, mul_zero, add_zero]
  nlinarith

/-- The affine neighbourhood deformation is continuous. -/
public theorem continuous_standardBoundarySevenFaceNeighborhoodHomotopyPoint
    (i : Fin 8) :
    Continuous (standardBoundarySevenFaceNeighborhoodHomotopyPoint i) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  change Continuous (fun q : unitInterval ×
      standardBoundarySevenFaceNeighborhood i ↦
        (1 - (q.1 : ℝ)) * q.2.1.1 k +
          (q.1 : ℝ) *
            (standardBoundarySevenFaceNeighborhoodProjection i q.2).1 k)
  have ct : Continuous (fun q : unitInterval ×
      standardBoundarySevenFaceNeighborhood i ↦ (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have cw : Continuous (fun q : unitInterval ×
      standardBoundarySevenFaceNeighborhood i ↦ q.2.1.1 k) :=
    ((((continuous_apply k).comp continuous_subtype_val).comp
      continuous_subtype_val).comp continuous_subtype_val).comp continuous_snd
  have cp : Continuous (fun q : unitInterval ×
      standardBoundarySevenFaceNeighborhood i ↦
        (standardBoundarySevenFaceNeighborhoodProjection i q.2).1 k) :=
    (((continuous_apply k).comp continuous_subtype_val).comp
      continuous_subtype_val).comp
        ((continuous_standardBoundarySevenFaceNeighborhoodProjection i).comp continuous_snd)
  exact (continuous_const.sub ct).mul cw |>.add (ct.mul cp)

/-- At time zero the affine deformation is the identity. -/
@[simp]
public theorem standardBoundarySevenFaceNeighborhoodHomotopyPoint_zero
    (i : Fin 8) (w : standardBoundarySevenFaceNeighborhood i) :
    standardBoundarySevenFaceNeighborhoodHomotopyPoint i (0, w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  change (1 - (0 : ℝ)) * w.1.1 k + 0 *
      (standardBoundarySevenFaceNeighborhoodProjection i w).1 k = w.1.1 k
  ring

/-- At time one the affine deformation is the normalized face projection. -/
@[simp]
public theorem standardBoundarySevenFaceNeighborhoodHomotopyPoint_one
    (i : Fin 8) (w : standardBoundarySevenFaceNeighborhood i) :
    standardBoundarySevenFaceNeighborhoodHomotopyPoint i (1, w) =
      standardBoundarySevenFaceNeighborhoodProjectionSelf i w := by
  apply Subtype.ext
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  change (1 - (1 : ℝ)) * w.1.1 k + 1 *
      (standardBoundarySevenFaceNeighborhoodProjection i w).1 k =
        (standardBoundarySevenFaceNeighborhoodProjection i w).1 k
  ring

/-- The explicit deformation from the identity to the face projection. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodHomotopy
    (i : Fin 8) :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      (standardBoundarySevenFaceNeighborhoodProjectionSelf i) where
  toFun := standardBoundarySevenFaceNeighborhoodHomotopyPoint i
  continuous_toFun := continuous_standardBoundarySevenFaceNeighborhoodHomotopyPoint i
  map_zero_left := standardBoundarySevenFaceNeighborhoodHomotopyPoint_zero i
  map_one_left := standardBoundarySevenFaceNeighborhoodHomotopyPoint_one i

/-! ## The face inclusion is a homotopy equivalence -/

/-- Insert a realized standard six-simplex as the `i`-th affine face, regarded as a point of the
open face neighbourhood. -/
public noncomputable def realizedStandardSixSimplexToStandardBoundaryFaceNeighborhood
    (i : Fin 8) :
    C((SSet.toTop.obj (Δ[6] : SSet.{0}) : Type),
      standardBoundarySevenFaceNeighborhood i) := by
  refine ⟨fun y ↦ ⟨⟨stdSimplex.map i.succAbove
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y),
      ⟨i, stdSimplex_map_succAbove_apply_self i _⟩⟩, ?_⟩, ?_⟩
  · change stdSimplex.map i.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y) i < (1 : ℝ) / 8
    rw [stdSimplex_map_succAbove_apply_self]
    norm_num
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map i.succAbove).comp
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).continuous

/-- Normalize away the distinguished coordinate and return to the realized standard face. -/
public noncomputable def standardBoundarySevenFaceNeighborhoodToRealizedStandardSixSimplex
    (i : Fin 8) :
    C(standardBoundarySevenFaceNeighborhood i,
      (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type)) :=
  ⟨fun w ↦ (SimplexCategory.toTopHomeo
      (SimplexCategory.mk 6)).symm
        (standardBoundarySevenFaceNeighborhoodRetractionCoordinates i w),
    (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).symm.continuous.comp
      (continuous_standardBoundarySevenFaceNeighborhoodRetractionCoordinates i)⟩

/-- Normalizing a point already on the face returns its original face coordinates. -/
public theorem standardBoundarySevenFaceNeighborhoodRetractionCoordinates_face
    (i : Fin 8) (y : SSet.toTop.obj (Δ[6] : SSet.{0})) :
    standardBoundarySevenFaceNeighborhoodRetractionCoordinates i
        (realizedStandardSixSimplexToStandardBoundaryFaceNeighborhood i y) =
      SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y := by
  apply stdSimplex.ext
  funext j
  rw [standardBoundarySevenFaceNeighborhoodRetractionCoordinates]
  change stdSimplex.map i.succAbove
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y) (i.succAbove j) /
        (1 - stdSimplex.map i.succAbove
          (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y) i) = _
  rw [stdSimplex_map_apply_of_injective i.succAbove
      Fin.succAbove_right_injective,
    stdSimplex_map_succAbove_apply_self]
  simp

/-- The retraction is a strict left inverse to the face inclusion. -/
public theorem standardBoundarySevenFaceNeighborhoodToRealized_comp_inclusion :
    (standardBoundarySevenFaceNeighborhoodToRealizedStandardSixSimplex i).comp
        (realizedStandardSixSimplexToStandardBoundaryFaceNeighborhood i) =
      ContinuousMap.id _ := by
  ext y
  apply (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).injective
  simp [standardBoundarySevenFaceNeighborhoodToRealizedStandardSixSimplex,
    standardBoundarySevenFaceNeighborhoodRetractionCoordinates_face]

/-- Inclusion after retraction is exactly the normalized affine face projection. -/
public theorem realizedStandardSixSimplexToStandardBoundary_comp_retraction :
    (realizedStandardSixSimplexToStandardBoundaryFaceNeighborhood i).comp
        (standardBoundarySevenFaceNeighborhoodToRealizedStandardSixSimplex i) =
      standardBoundarySevenFaceNeighborhoodProjectionSelf i := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  apply Subtype.ext
  apply stdSimplex.ext
  funext k
  change stdSimplex.map i.succAbove
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).symm
          (standardBoundarySevenFaceNeighborhoodRetractionCoordinates i w))) k =
    stdSimplex.map i.succAbove
      (standardBoundarySevenFaceNeighborhoodRetractionCoordinates i w) k
  rw [Homeomorph.apply_symm_apply]

/-- The affine face inclusion is a homotopy equivalence, with the explicit normalized
retraction as inverse. -/
public noncomputable def realizedStandardSixSimplexStandardBoundaryFaceNeighborhoodHomotopyEquiv
    (i : Fin 8) :
    (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type) ≃ₕ
      standardBoundarySevenFaceNeighborhood i where
  toFun := realizedStandardSixSimplexToStandardBoundaryFaceNeighborhood i
  invFun := standardBoundarySevenFaceNeighborhoodToRealizedStandardSixSimplex i
  left_inv := by
    rw [standardBoundarySevenFaceNeighborhoodToRealized_comp_inclusion]
  right_inv := by
    rw [realizedStandardSixSimplexToStandardBoundary_comp_retraction]
    exact ⟨(standardBoundarySevenFaceNeighborhoodHomotopy i).symm⟩

/-! ## Transport back to the geometric realization -/

/-- The canonical barycentric homeomorphism, now available unconditionally. -/
public noncomputable def boundarySevenRealizationHomeomorphStandardBoundary :
    (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ StandardSimplexBoundary 7 :=
  boundarySevenRealizationHomeomorphStandardBoundary_of_injective
    boundarySevenRealizationToBoundary_injective

@[simp]
public theorem boundarySevenRealizationHomeomorphStandardBoundary_apply_val
    (x : SSet.toTop.obj (∂Δ[7] : SSet.{0})) :
    (boundarySevenRealizationHomeomorphStandardBoundary x :
        stdSimplex ℝ (Fin 8)) = boundarySevenRealizationToStdSimplex x :=
  rfl

/-- The actual realization face neighbourhood is homeomorphic to its ordinary barycentric
counterpart. -/
public noncomputable def boundarySevenFaceNeighborhoodHomeomorphStandard
    (i : Fin 8) :
    boundarySevenComparisonFaceNeighborhood i ≃ₜ
      standardBoundarySevenFaceNeighborhood i :=
  boundarySevenRealizationHomeomorphStandardBoundary.subtype fun x ↦ by
    change boundarySevenRealizationToStdSimplex x i < (1 : ℝ) / 8 ↔
      (boundarySevenRealizationHomeomorphStandardBoundary x :
        stdSimplex ℝ (Fin 8)) i < (1 : ℝ) / 8
    rw [boundarySevenRealizationHomeomorphStandardBoundary_apply_val]

/-- The forward continuous map of the barycentric neighbourhood homeomorphism. -/
public noncomputable def boundarySevenFaceNeighborhoodToStandardContinuousMap
    (i : Fin 8) :
    C(boundarySevenComparisonFaceNeighborhood i,
      standardBoundarySevenFaceNeighborhood i) :=
  ⟨boundarySevenFaceNeighborhoodHomeomorphStandard i,
    (boundarySevenFaceNeighborhoodHomeomorphStandard i).continuous⟩

/-- Under barycentric coordinates, the existing realized-face map is the affine face
inclusion used above. -/
public theorem boundarySevenFaceNeighborhoodHomeomorphStandard_comp_face
    (i : Fin 8) :
    (boundarySevenFaceNeighborhoodToStandardContinuousMap i).comp
        (boundarySevenFaceToComparisonFaceNeighborhood i).hom =
      realizedStandardSixSimplexToStandardBoundaryFaceNeighborhood i := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  apply Subtype.ext
  change boundarySevenRealizationToStdSimplex
      (SSet.toTop.map (SSet.boundary.ι i) y) =
    stdSimplex.map i.succAbove
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y)
  exact boundarySevenRealizationToStdSimplex_face i y

/-- Every canonical realized face is a homotopy equivalence onto its open affine
neighbourhood. -/
public noncomputable def boundarySevenFaceNeighborhoodHomotopyEquiv
    (i : Fin 8) :
    (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type) ≃ₕ
      boundarySevenComparisonFaceNeighborhood i :=
  (realizedStandardSixSimplexStandardBoundaryFaceNeighborhoodHomotopyEquiv i).trans
    (boundarySevenFaceNeighborhoodHomeomorphStandard i).symm.toHomotopyEquiv

/-- The forward function of the preceding homotopy equivalence is the face map already used by
the comparison construction. -/
public theorem boundarySevenFaceNeighborhoodHomotopyEquiv_apply
    (i : Fin 8) (y : SSet.toTop.obj (Δ[6] : SSet.{0})) :
    boundarySevenFaceNeighborhoodHomotopyEquiv i y =
      boundarySevenFaceToComparisonFaceNeighborhood i y := by
  change (boundarySevenFaceNeighborhoodHomeomorphStandard i).symm
      (realizedStandardSixSimplexToStandardBoundaryFaceNeighborhood i y) =
    boundarySevenFaceToComparisonFaceNeighborhood i y
  apply (boundarySevenFaceNeighborhoodHomeomorphStandard i).injective
  rw [Homeomorph.apply_symm_apply]
  exact ContinuousMap.congr_fun
    (boundarySevenFaceNeighborhoodHomeomorphStandard_comp_face i).symm y

/-- The singular-chain map induced by inclusion of a realized face into its neighbourhood. -/
public noncomputable def boundarySevenFaceNeighborhoodIntegralSingularChainMap
    (i : Fin 8) :
    IntegralSingularChainComplexObj
        (SSet.toTop.obj (Δ[6] : SSet.{0})) ⟶
      IntegralSingularChainComplexObj
        (TopCat.of (boundarySevenComparisonFaceNeighborhood i)) :=
  integralSingularChainMapObj
    (boundarySevenFaceToComparisonFaceNeighborhood i)

/-- Since the face inclusion is an explicit homotopy equivalence, its integral singular-chain
map is a quasi-isomorphism. -/
public theorem boundarySevenFaceNeighborhoodIntegralSingularChainMap_quasiIso
    (i : Fin 8) :
    QuasiIso (boundarySevenFaceNeighborhoodIntegralSingularChainMap i) := by
  let e := boundarySevenFaceNeighborhoodHomotopyEquiv i
  have hmap : TopCat.ofHom e.toFun =
      boundarySevenFaceToComparisonFaceNeighborhood i := by
    ext y
    exact congrArg Subtype.val
      (boundarySevenFaceNeighborhoodHomotopyEquiv_apply i y)
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).map
      (boundarySevenFaceToComparisonFaceNeighborhood i))
  rw [← hmap]
  change IsIso (singularHomologyIsoOfHomotopyEquiv
    (AddCommGrpCat.of ℤ) k e).hom
  infer_instance

end SphereSixComplex
