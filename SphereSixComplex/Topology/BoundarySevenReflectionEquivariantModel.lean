module

public import SphereSixComplex.Topology.SixSphereCoordinateReflectionHomology
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-!
# A reflection-equivariant radial model of the seven-simplex boundary

We use seven explicit linear coordinates on the affine hyperplane of barycentric coordinates.
The first is the difference of barycentric coordinates zero and one; the remaining six are the
centered coordinates at vertices two through seven.  Thus swapping vertices zero and one becomes
literal negation of ambient coordinate zero.  Radial normalization then gives the desired map to
the unit six-sphere.
-/

@[expose] public section

noncomputable section

open ContinuousMap Metric Set

namespace SphereSixComplex

/-- Explicit linear coordinates on the centered barycentric hyperplane. -/
public noncomputable def boundarySevenReflectionCoordinates
    (w : Fin 8 → ℝ) : EuclideanSpace ℝ (Fin 7) :=
  WithLp.toLp 2 ![
    w 0 - w 1,
    w 2 - (1 / 8 : ℝ),
    w 3 - (1 / 8 : ℝ),
    w 4 - (1 / 8 : ℝ),
    w 5 - (1 / 8 : ℝ),
    w 6 - (1 / 8 : ℝ),
    w 7 - (1 / 8 : ℝ)]

/-- Reconstruct centered barycentric coordinates from the seven reflection coordinates. -/
public noncomputable def boundarySevenReflectionCoordinatesInverse
    (y : EuclideanSpace ℝ (Fin 7)) : Fin 8 → ℝ :=
  ![
    (y 0 - (y 1 + y 2 + y 3 + y 4 + y 5 + y 6)) / 2,
    (-y 0 - (y 1 + y 2 + y 3 + y 4 + y 5 + y 6)) / 2,
    y 1, y 2, y 3, y 4, y 5, y 6]

public theorem boundarySevenReflectionCoordinatesInverse_sum
    (y : EuclideanSpace ℝ (Fin 7)) :
    ∑ i, boundarySevenReflectionCoordinatesInverse y i = 0 := by
  simp [boundarySevenReflectionCoordinatesInverse, Fin.sum_univ_succ]
  ring

public theorem boundarySevenReflectionCoordinates_inverse_apply
    (y : EuclideanSpace ℝ (Fin 7)) :
    boundarySevenReflectionCoordinates
        (fun i ↦ boundarySevenReflectionCoordinatesInverse y i + (1 / 8 : ℝ)) = y := by
  apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
  funext i
  fin_cases i <;> simp [boundarySevenReflectionCoordinates,
    boundarySevenReflectionCoordinatesInverse] <;> ring

public theorem boundarySevenReflectionCoordinatesInverse_smul
    (c : ℝ) (y : EuclideanSpace ℝ (Fin 7)) (i : Fin 8) :
    boundarySevenReflectionCoordinatesInverse (c • y) i =
      c * boundarySevenReflectionCoordinatesInverse y i := by
  fin_cases i <;> simp [boundarySevenReflectionCoordinatesInverse] <;> ring

public theorem boundarySevenReflectionCoordinates_scaled_inverse
    (c : ℝ) (y : EuclideanSpace ℝ (Fin 7)) :
    boundarySevenReflectionCoordinates
        (fun i ↦ c * boundarySevenReflectionCoordinatesInverse y i + (1 / 8 : ℝ)) =
      c • y := by
  apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
  funext i
  fin_cases i <;> simp [boundarySevenReflectionCoordinates,
    boundarySevenReflectionCoordinatesInverse] <;> ring

public theorem boundarySevenReflectionCoordinatesInverse_coordinates
    (w : Fin 8 → ℝ) (hw : ∑ i, w i = 1) (i : Fin 8) :
    boundarySevenReflectionCoordinatesInverse
        (boundarySevenReflectionCoordinates w) i = w i - (1 / 8 : ℝ) := by
  norm_num [Fin.sum_univ_succ] at hw
  change w 0 + (w 1 + (w 2 + (w 3 + (w 4 + (w 5 + (w 6 + w 7)))))) = 1 at hw
  fin_cases i <;> simp [boundarySevenReflectionCoordinates,
    boundarySevenReflectionCoordinatesInverse] <;> linarith

public theorem boundarySevenReflectionCoordinates_injective_on_sum_one
    {w z : Fin 8 → ℝ} (hw : ∑ i, w i = 1) (hz : ∑ i, z i = 1)
    (h : boundarySevenReflectionCoordinates w = boundarySevenReflectionCoordinates z) :
    w = z := by
  funext i
  have hiw := boundarySevenReflectionCoordinatesInverse_coordinates w hw i
  have hiz := boundarySevenReflectionCoordinatesInverse_coordinates z hz i
  rw [h] at hiw
  linarith

public theorem continuous_boundarySevenReflectionCoordinates :
    Continuous (fun w : Fin 8 → ℝ ↦ boundarySevenReflectionCoordinates w) := by
  rw [← (EuclideanSpace.equiv (Fin 7) ℝ).toHomeomorph.comp_continuous_iff]
  apply continuous_pi
  intro i
  fin_cases i <;> simp [boundarySevenReflectionCoordinates] <;> fun_prop

/-- Reflection coordinates do not vanish on the boundary of the simplex. -/
public theorem boundarySevenReflectionCoordinates_ne_zero
    (w : StandardSimplexBoundary 7) :
    boundarySevenReflectionCoordinates (w.1 : Fin 8 → ℝ) ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := w.2
  have hsum : ∑ j, (w.1 : Fin 8 → ℝ) j = 1 := w.1.2.2
  have hi' := boundarySevenReflectionCoordinatesInverse_coordinates
    (w.1 : Fin 8 → ℝ) hsum i
  rw [hzero] at hi'
  simp [boundarySevenReflectionCoordinatesInverse] at hi'
  rw [hi] at hi'
  fin_cases i <;> norm_num [boundarySevenReflectionCoordinatesInverse] at hi'

/-- The unnormalized reflection-coordinate map, bundled with its nonvanishing proof. -/
public noncomputable def boundarySevenReflectionCoordinatesNonzero :
    StandardSimplexBoundary 7 → ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 7))) :=
  fun w ↦ ⟨boundarySevenReflectionCoordinates (w.1 : Fin 8 → ℝ), by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      boundarySevenReflectionCoordinates_ne_zero w⟩

public theorem continuous_boundarySevenReflectionCoordinatesNonzero :
    Continuous boundarySevenReflectionCoordinatesNonzero := by
  apply Continuous.subtype_mk
  exact continuous_boundarySevenReflectionCoordinates.comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- Radially normalize the explicit coordinates to the unit six-sphere. -/
public noncomputable def boundarySevenReflectionRadialMap :
    StandardSimplexBoundary 7 → SixSphere :=
  fun w ↦ (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 7))
    (boundarySevenReflectionCoordinatesNonzero w)).1

public theorem continuous_boundarySevenReflectionRadialMap :
    Continuous boundarySevenReflectionRadialMap :=
  continuous_fst.comp ((homeomorphUnitSphereProd
    (EuclideanSpace ℝ (Fin 7))).continuous.comp
      continuous_boundarySevenReflectionCoordinatesNonzero)

@[simp]
public theorem boundarySevenReflectionRadialMap_coe
    (w : StandardSimplexBoundary 7) :
    (boundarySevenReflectionRadialMap w : EuclideanSpace ℝ (Fin 7)) =
      ‖boundarySevenReflectionCoordinates (w.1 : Fin 8 → ℝ)‖⁻¹ •
        boundarySevenReflectionCoordinates (w.1 : Fin 8 → ℝ) := by
  exact homeomorphUnitSphereProd_apply_fst_coe
    (E := EuclideanSpace ℝ (Fin 7)) _

public theorem boundarySevenReflectionCoordinates_permute
    (w : Fin 8 → ℝ) :
    boundarySevenReflectionCoordinates
        (fun i ↦ w (boundarySevenReflectionPermutation.symm i)) =
      sixSphereCoordinateReflectionAmbient
        (boundarySevenReflectionCoordinates w) := by
  apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
  funext i
  fin_cases i <;> simp [boundarySevenReflectionCoordinates,
    boundarySevenReflectionPermutation, sixSphereCoordinateReflectionAmbient,
    Equiv.swap_apply_def]

public theorem boundarySevenReflectionCoordinates_permute_norm
    (w : Fin 8 → ℝ) :
    ‖boundarySevenReflectionCoordinates
        (fun i ↦ w (boundarySevenReflectionPermutation.symm i))‖ =
      ‖boundarySevenReflectionCoordinates w‖ := by
  rw [boundarySevenReflectionCoordinates_permute]
  rw [← sixSphereAntipodalReflectionRotationAmbient_one,
    sixSphereAntipodalReflectionRotationAmbient_norm]

public theorem boundarySevenReflectionBoundaryPerm_val
    (w : StandardSimplexBoundary 7) :
    ((standardSimplexBoundaryPermHomeomorph
        boundarySevenReflectionPermutation w).1 : Fin 8 → ℝ) =
      fun i ↦ (w.1 : Fin 8 → ℝ) (boundarySevenReflectionPermutation.symm i) := by
  funext i
  exact stdSimplex_map_equiv_apply boundarySevenReflectionPermutation w.1 i

public theorem boundarySevenReflectionRadialMap_equivariant
    (w : StandardSimplexBoundary 7) :
    boundarySevenReflectionRadialMap
        (standardSimplexBoundaryPermHomeomorph
          boundarySevenReflectionPermutation w) =
      sixSphereCoordinateReflectionMap (boundarySevenReflectionRadialMap w) := by
  apply Subtype.ext
  rw [boundarySevenReflectionRadialMap_coe,
    sixSphereCoordinateReflectionMap_apply,
    boundarySevenReflectionRadialMap_coe]
  rw [boundarySevenReflectionBoundaryPerm_val,
    boundarySevenReflectionCoordinates_permute_norm,
    boundarySevenReflectionCoordinates_permute]
  apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
  funext i
  fin_cases i <;> simp [sixSphereCoordinateReflectionAmbient]

public theorem boundarySevenReflectionRadialMap_injective :
    Function.Injective boundarySevenReflectionRadialMap := by
  intro w z hwz
  let vw := boundarySevenReflectionCoordinates (w.1 : Fin 8 → ℝ)
  let vz := boundarySevenReflectionCoordinates (z.1 : Fin 8 → ℝ)
  have hvw : vw ≠ 0 := boundarySevenReflectionCoordinates_ne_zero w
  have hvz : vz ≠ 0 := boundarySevenReflectionCoordinates_ne_zero z
  have hnw : 0 < ‖vw‖ := norm_pos_iff.mpr hvw
  have hnz : 0 < ‖vz‖ := norm_pos_iff.mpr hvz
  have hnormalized : ‖vw‖⁻¹ • vw = ‖vz‖⁻¹ • vz := by
    have := congrArg Subtype.val hwz
    simpa only [boundarySevenReflectionRadialMap_coe] using this
  let c : ℝ := ‖vz‖ / ‖vw‖
  have hc : 0 < c := div_pos hnz hnw
  have hscaled : vz = c • vw := by
    calc
      vz = ‖vz‖ • (‖vz‖⁻¹ • vz) := by
        rw [smul_smul]
        simp [hnz.ne']
      _ = ‖vz‖ • (‖vw‖⁻¹ • vw) := by rw [hnormalized]
      _ = c • vw := by
        rw [smul_smul]
        congr 1
  change boundarySevenReflectionCoordinates (z.1 : Fin 8 → ℝ) =
    c • boundarySevenReflectionCoordinates (w.1 : Fin 8 → ℝ) at hscaled
  have hcentered (i : Fin 8) :
      (z.1 : Fin 8 → ℝ) i - (1 / 8 : ℝ) =
        c * ((w.1 : Fin 8 → ℝ) i - (1 / 8 : ℝ)) := by
    have hzcoord := boundarySevenReflectionCoordinatesInverse_coordinates
      (z.1 : Fin 8 → ℝ) z.1.2.2 i
    have hwcoord := boundarySevenReflectionCoordinatesInverse_coordinates
      (w.1 : Fin 8 → ℝ) w.1.2.2 i
    rw [hscaled, boundarySevenReflectionCoordinatesInverse_smul] at hzcoord
    rw [hwcoord] at hzcoord
    exact hzcoord.symm
  obtain ⟨iw, hiw⟩ := w.2
  obtain ⟨iz, hiz⟩ := z.2
  have hcle : c ≤ 1 := by
    have hznonneg := z.1.2.1 iw
    change 0 ≤ (z.1 : Fin 8 → ℝ) iw at hznonneg
    have h := hcentered iw
    rw [hiw] at h
    norm_num at h
    linarith
  have hge : 1 ≤ c := by
    have hwnonneg := w.1.2.1 iz
    change 0 ≤ (w.1 : Fin 8 → ℝ) iz at hwnonneg
    have h := hcentered iz
    rw [hiz] at h
    norm_num at h
    nlinarith [hc]
  have hc_one : c = 1 := le_antisymm hcle hge
  apply Subtype.ext
  apply Subtype.ext
  change (w.1 : Fin 8 → ℝ) = (z.1 : Fin 8 → ℝ)
  exact boundarySevenReflectionCoordinates_injective_on_sum_one
    w.1.2.2 z.1.2.2 (by simpa [hc_one] using hscaled.symm)

public theorem boundarySevenReflectionRadialMap_surjective :
    Function.Surjective boundarySevenReflectionRadialMap := by
  intro y
  let x : Fin 8 → ℝ := boundarySevenReflectionCoordinatesInverse y.1
  have hxsum : ∑ j, x j = 0 :=
    boundarySevenReflectionCoordinatesInverse_sum y.1
  have hyne : y.1 ≠ 0 := by
    intro hyzero
    have hynorm : ‖y.1‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using y.2
    rw [hyzero, norm_zero] at hynorm
    norm_num at hynorm
  have hxne : x ≠ 0 := by
    intro hxzero
    have hreconstruct := boundarySevenReflectionCoordinates_inverse_apply y.1
    have hcenter : (fun i : Fin 8 ↦ x i + (1 / 8 : ℝ)) =
        fun _ ↦ (1 / 8 : ℝ) := by simp [hxzero]
    rw [hcenter] at hreconstruct
    have hcoordszero : boundarySevenReflectionCoordinates
        (fun _ : Fin 8 ↦ (1 / 8 : ℝ)) = 0 := by
      apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
      funext i
      fin_cases i <;> norm_num [boundarySevenReflectionCoordinates]
    exact hyne (hreconstruct ▸ hcoordszero)
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  have hxi : x i < 0 := by
    by_contra hnot
    have hall : ∀ j ∈ Finset.univ, 0 ≤ x j := by
      intro j hj
      exact (le_of_not_gt hnot).trans (hi j hj)
    have hallzero : ∀ j ∈ Finset.univ, x j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hall).mp hxsum
    apply hxne
    funext j
    exact hallzero j (Finset.mem_univ j)
  let c : ℝ := (1 / 8 : ℝ) / (-x i)
  have hc : 0 < c := div_pos (by norm_num) (neg_pos.mpr hxi)
  have hci : c * x i = -(1 / 8 : ℝ) := by
    dsimp [c]
    field_simp [hxi.ne]
  let wf : Fin 8 → ℝ := fun j ↦ c * x j + (1 / 8 : ℝ)
  have hw_nonneg (j : Fin 8) : 0 ≤ wf j := by
    have hmin := hi j (Finset.mem_univ j)
    dsimp [wf]
    nlinarith
  have hw_sum : ∑ j, wf j = 1 := by
    simp only [wf, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, hxsum]
    norm_num
  let ws : stdSimplex ℝ (Fin 8) := ⟨wf, hw_nonneg, hw_sum⟩
  have hwi : ws i = 0 := by
    change wf i = 0
    dsimp [wf]
    linarith
  let wb : StandardSimplexBoundary 7 := ⟨ws, ⟨i, hwi⟩⟩
  refine ⟨wb, ?_⟩
  apply Subtype.ext
  rw [boundarySevenReflectionRadialMap_coe]
  have hraw : boundarySevenReflectionCoordinates (wb.1 : Fin 8 → ℝ) = c • y.1 := by
    exact boundarySevenReflectionCoordinates_scaled_inverse c y.1
  rw [hraw]
  have hynorm : ‖y.1‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using y.2
  simp [norm_smul, abs_of_pos hc, hynorm, hc.ne']

public theorem boundarySevenReflectionRadialMap_bijective :
    Function.Bijective boundarySevenReflectionRadialMap :=
  ⟨boundarySevenReflectionRadialMap_injective,
    boundarySevenReflectionRadialMap_surjective⟩

/-- The vanishing-coordinate boundary is closed in the compact standard simplex. -/
public theorem isClosed_standardSimplexBoundarySeven :
    IsClosed {w : stdSimplex ℝ (Fin 8) | ∃ i, w i = 0} := by
  have hset : {w : stdSimplex ℝ (Fin 8) | ∃ i, w i = 0} =
      ⋃ i : Fin 8, {w : stdSimplex ℝ (Fin 8) | w i = 0} := by
    ext w
    simp
  rw [hset]
  apply isClosed_iUnion_of_finite
  intro i
  exact isClosed_eq
    ((continuous_apply i).comp continuous_subtype_val) continuous_const

/-- The explicit radial map, upgraded to a homeomorphism by compactness of the simplex boundary. -/
public noncomputable def boundarySevenReflectionEquivariantHomeomorph :
    StandardSimplexBoundary 7 ≃ₜ SixSphere := by
  letI : CompactSpace (StandardSimplexBoundary 7) :=
    isClosed_standardSimplexBoundarySeven.isClosedEmbedding_subtypeVal.compactSpace
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective boundarySevenReflectionRadialMap
      boundarySevenReflectionRadialMap_bijective)
    continuous_boundarySevenReflectionRadialMap

@[simp]
public theorem boundarySevenReflectionEquivariantHomeomorph_apply
    (w : StandardSimplexBoundary 7) :
    boundarySevenReflectionEquivariantHomeomorph w =
      boundarySevenReflectionRadialMap w :=
  rfl

/-- Swapping vertices zero and one is exactly coordinate-zero reflection under the explicit
radial homeomorphism. -/
public theorem boundarySevenReflectionEquivariantHomeomorph_equivariant :
    BoundarySevenReflectionEquivariant
      boundarySevenReflectionEquivariantHomeomorph := by
  intro w
  simp only [boundarySevenReflectionEquivariantHomeomorph_apply]
  exact boundarySevenReflectionRadialMap_equivariant w

end SphereSixComplex
