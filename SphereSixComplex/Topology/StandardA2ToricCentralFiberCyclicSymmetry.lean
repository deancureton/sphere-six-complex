module

public import SphereSixComplex.Topology.StandardA2ToricCentralFiberOneCells

/-!
# Cyclic symmetry of the standard `A₂` central fibre

The affine order-three rotation of the triangular lattice cyclically permutes the three
one-dimensional strata.  Its height-one linearization gives the corresponding fan symmetry,
while the two triangle orientations use opposite cyclic permutations of affine coordinates.
-/

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The linear part of the order-three affine rotation of the triangular lattice. -/
public def a2CyclicLinear (v : ToricLattice) : ToricLattice :=
  ![-v 0 - v 1, v 0]

@[simp]
public theorem a2CyclicLinear_zero : a2CyclicLinear 0 = 0 := by
  ext i
  fin_cases i <;> simp [a2CyclicLinear]

public theorem a2CyclicLinear_add (v w : ToricLattice) :
    a2CyclicLinear (v + w) = a2CyclicLinear v + a2CyclicLinear w := by
  ext i
  fin_cases i
  · simp [a2CyclicLinear]
    ring
  · simp [a2CyclicLinear]

@[simp]
public theorem a2CyclicLinear_apply_three (v : ToricLattice) :
    a2CyclicLinear (a2CyclicLinear (a2CyclicLinear v)) = v := by
  ext i
  fin_cases i
  · simp [a2CyclicLinear]
    ring
  · simp [a2CyclicLinear]

/-- The order-three additive equivalence underlying the affine lattice rotation. -/
public def a2CyclicLinearEquiv : ToricLattice ≃+ ToricLattice where
  toFun := a2CyclicLinear
  invFun := a2CyclicLinear ∘ a2CyclicLinear
  left_inv v := a2CyclicLinear_apply_three v
  right_inv v := a2CyclicLinear_apply_three v
  map_add' := a2CyclicLinear_add

/-- The affine rotation sending `0 → e₁ → e₂ → 0`. -/
public def a2CyclicVertex (v : ToricLattice) : ToricLattice :=
  a2CyclicLinear v + e₁

@[simp]
public theorem a2CyclicVertex_zero : a2CyclicVertex 0 = e₁ := by
  simp [a2CyclicVertex]

@[simp]
public theorem a2CyclicVertex_e₁ : a2CyclicVertex e₁ = e₂ := by
  ext i
  fin_cases i <;> simp [a2CyclicVertex, a2CyclicLinear, e₁, e₂]

@[simp]
public theorem a2CyclicVertex_e₂ : a2CyclicVertex e₂ = 0 := by
  ext i
  fin_cases i <;> simp [a2CyclicVertex, a2CyclicLinear, e₁, e₂]

@[simp]
public theorem a2CyclicVertex_apply_three (v : ToricLattice) :
    a2CyclicVertex (a2CyclicVertex (a2CyclicVertex v)) = v := by
  ext i
  fin_cases i <;> simp [a2CyclicVertex, a2CyclicLinear, e₁] <;> ring

/-- Cyclic permutation of the coordinates of a lower affine triangle. -/
public def a2CyclicRawLower (z : RawCoordinates) : RawCoordinates :=
  ![z 2, z 0, z 1]

/-- Cyclic permutation of the coordinates of an upper affine triangle. -/
public def a2CyclicRawUpper (z : RawCoordinates) : RawCoordinates :=
  ![z 1, z 2, z 0]

@[simp]
public theorem a2CyclicRawLower_apply_three (z : RawCoordinates) :
    a2CyclicRawLower (a2CyclicRawLower (a2CyclicRawLower z)) = z := by
  funext i
  fin_cases i <;> rfl

@[simp]
public theorem a2CyclicRawUpper_apply_three (z : RawCoordinates) :
    a2CyclicRawUpper (a2CyclicRawUpper (a2CyclicRawUpper z)) = z := by
  funext i
  fin_cases i <;> rfl

public def a2CyclicRaw (upper : Bool) : RawCoordinates ≃ RawCoordinates :=
  if upper then
    { toFun := a2CyclicRawUpper
      invFun := a2CyclicRawUpper ∘ a2CyclicRawUpper
      left_inv := a2CyclicRawUpper_apply_three
      right_inv := a2CyclicRawUpper_apply_three }
  else
    { toFun := a2CyclicRawLower
      invFun := a2CyclicRawLower ∘ a2CyclicRawLower
      left_inv := a2CyclicRawLower_apply_three
      right_inv := a2CyclicRawLower_apply_three }

/-- The induced permutation of lower and upper chart indices. -/
public def a2CyclicChartIndex (a : ChartIndex) : ChartIndex :=
  if a.1 then (true, a2CyclicLinear a.2 - e₁)
  else (false, a2CyclicLinear a.2)

@[simp]
public theorem a2CyclicChartIndex_apply_three (a : ChartIndex) :
    a2CyclicChartIndex (a2CyclicChartIndex (a2CyclicChartIndex a)) = a := by
  rcases a with ⟨upper, v⟩
  cases upper
  · apply Prod.ext
    · simp [a2CyclicChartIndex]
    · exact a2CyclicLinear_apply_three v
  · apply Prod.ext
    · simp [a2CyclicChartIndex]
    · ext i
      fin_cases i <;>
        simp [a2CyclicChartIndex, a2CyclicLinear, e₁] <;> ring

/-- The lower triangles are rotated with the vertex permutation `0 → 1 → 2 → 0`. -/
public theorem a2CyclicVertex_lowerTriangle (v : ToricLattice) (i : Fin 3) :
    a2CyclicVertex (a2Triangle false v i) =
      a2Triangle false (a2CyclicLinear v) (i + 1) := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  fin_cases i <;>
    ext j <;> fin_cases j <;>
      simp [a2CyclicVertex, a2CyclicLinear, a2Triangle, e₁, e₂, hv0, hv1] <;> ring

/-- The upper triangles are rotated with the opposite coordinate permutation. -/
public theorem a2CyclicVertex_upperTriangle (v : ToricLattice) (i : Fin 3) :
    a2CyclicVertex (a2Triangle true v i) =
      a2Triangle true (a2CyclicLinear v - e₁) (i + 2) := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  fin_cases i <;>
    ext j <;> fin_cases j <;>
      simp [a2CyclicVertex, a2CyclicLinear, a2Triangle, e₁, e₂, hv0, hv1] <;> ring

/-- Height-one linearization of the affine lattice rotation. -/
public def a2CyclicFan (v : FanLattice) : FanLattice :=
  ![-v 0 - v 1 + v 2, v 0, v 2]

@[simp]
public theorem a2CyclicFan_apply_three (v : FanLattice) :
    a2CyclicFan (a2CyclicFan (a2CyclicFan v)) = v := by
  ext i
  fin_cases i <;> simp [a2CyclicFan] <;> ring

public theorem a2CyclicFan_heightOneRay (v : ToricLattice) :
    a2CyclicFan (heightOneRay v) = heightOneRay (a2CyclicVertex v) := by
  ext i
  fin_cases i <;>
    simp [a2CyclicFan, heightOneRay, a2CyclicVertex, a2CyclicLinear, e₁]

public theorem a2CyclicRawLower_lowerAxisZero (z : ℂ) :
    a2CyclicRawLower (lowerAxisZero z) = singleAxis 1 z := by
  funext i
  fin_cases i <;> simp [a2CyclicRawLower, lowerAxisZero, singleAxis]

public theorem a2CyclicRawUpper_upperAxisTwo (z : ℂ) :
    a2CyclicRawUpper (upperAxisTwo z) = singleAxis 1 z := by
  funext i
  fin_cases i <;> simp [a2CyclicRawUpper, upperAxisTwo, singleAxis]

public theorem a2CyclicRawLower_sq_lowerAxisZero (z : ℂ) :
    a2CyclicRawLower (a2CyclicRawLower (lowerAxisZero z)) = singleAxis 2 z := by
  funext i
  fin_cases i <;> simp [a2CyclicRawLower, lowerAxisZero, singleAxis]

public theorem a2CyclicRawUpper_sq_upperAxisTwo (z : ℂ) :
    a2CyclicRawUpper (a2CyclicRawUpper (upperAxisTwo z)) = singleAxis 0 z := by
  funext i
  fin_cases i <;> simp [a2CyclicRawUpper, upperAxisTwo, singleAxis]

@[simp]
public theorem a2CyclicChartIndex_lower_zero :
    a2CyclicChartIndex (false, 0) = (false, 0) := by
  simp [a2CyclicChartIndex]

@[simp]
public theorem a2CyclicChartIndex_upper_zero :
    a2CyclicChartIndex (true, 0) = (true, -e₁) := by
  simp [a2CyclicChartIndex]

@[simp]
public theorem a2CyclicChartIndex_sq_upper_zero :
    a2CyclicChartIndex (a2CyclicChartIndex (true, 0)) = (true, -e₂) := by
  apply Prod.ext
  · simp [a2CyclicChartIndex]
  · ext i
    fin_cases i <;> simp [a2CyclicChartIndex, a2CyclicLinear, e₁, e₂]

public theorem a2CyclicVertex_image_support_zero :
    a2CyclicVertex '' ({e₁, e₂} : Set ToricLattice) = {0, e₂} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with (rfl | rfl)
    · simp
    · simp
  · intro hv
    rcases hv with (rfl | rfl)
    · exact ⟨e₂, by simp⟩
    · exact ⟨e₁, by simp⟩

public theorem a2CyclicVertex_image_support_one :
    a2CyclicVertex '' ({0, e₂} : Set ToricLattice) = {0, e₁} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with (rfl | rfl)
    · simp
    · simp
  · intro hv
    rcases hv with (rfl | rfl)
    · exact ⟨e₂, by simp⟩
    · exact ⟨0, by simp⟩

public theorem a2CyclicRaw_transitionMatrix
    (a b : ChartIndex) (z : RawCoordinates) :
    a2CyclicRaw b.1 (monomial (transitionMatrix a b) z) =
      monomial (transitionMatrix (a2CyclicChartIndex a)
        (a2CyclicChartIndex b)) (a2CyclicRaw a.1 z) := by
  rcases a with ⟨ua, v⟩
  rcases b with ⟨ub, w⟩
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  cases ua <;> cases ub <;> funext i <;> fin_cases i <;>
    simp [a2CyclicRaw, a2CyclicRawLower, a2CyclicRawUpper,
      a2CyclicChartIndex, a2CyclicLinear, transitionMatrix, dualMatrix,
      a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle, monomial,
      Matrix.mul_apply, Fin.sum_univ_succ, Fin.prod_univ_succ,
      e₁, e₂, hv0, hv1]
  all_goals ring_nf

public theorem a2CyclicRaw_monomialDomain_iff
    (a b : ChartIndex) (z : RawCoordinates) :
    a2CyclicRaw a.1 z ∈
        monomialDomain (transitionMatrix (a2CyclicChartIndex a)
          (a2CyclicChartIndex b)) ↔
      z ∈ monomialDomain (transitionMatrix a b) := by
  rcases a with ⟨ua, v⟩
  rcases b with ⟨ub, w⟩
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  cases ua <;> cases ub <;>
    simp [a2CyclicRaw, a2CyclicRawLower, a2CyclicRawUpper,
      monomialDomain, a2CyclicChartIndex, a2CyclicLinear, transitionMatrix,
      dualMatrix, a2DualCharacter, a2ConeMatrix, heightOneRay, a2Triangle,
      Matrix.mul_apply, Fin.sum_univ_succ, Fin.forall_fin_succ,
      e₁, e₂, hv0, hv1]
  all_goals
    by_cases hz0 : z 0 = 0 <;>
      by_cases hz1 : z 1 = 0 <;>
        by_cases hz2 : z 2 = 0 <;> simp_all <;> omega

public theorem a2CyclicRaw_chartChange_source_iff
    (a b : ChartIndex) (z : RawCoordinates) :
    a2CyclicRaw a.1 z ∈
        (chartChange (a2CyclicChartIndex a) (a2CyclicChartIndex b)).source ↔
      z ∈ (chartChange a b).source := by
  rw [chartChange_source, chartChange_source]
  exact a2CyclicRaw_monomialDomain_iff a b z

public theorem a2CyclicRaw_chartChange
    (a b : ChartIndex) (z : RawCoordinates) :
    a2CyclicRaw b.1 (chartChange a b z) =
      chartChange (a2CyclicChartIndex a) (a2CyclicChartIndex b)
        (a2CyclicRaw a.1 z) := by
  exact a2CyclicRaw_transitionMatrix a b z

public noncomputable def a2CyclicRepresentativeChart (p : Carrier) : ChartIndex :=
  Classical.choose (inclusion_jointly_surjective p)

public noncomputable def a2CyclicRepresentativeCoordinates (p : Carrier) : RawCoordinates :=
  Classical.choose (Classical.choose_spec (inclusion_jointly_surjective p))

public theorem a2CyclicRepresentative_eq (p : Carrier) :
    inclusion (a2CyclicRepresentativeChart p)
      (a2CyclicRepresentativeCoordinates p) = p :=
  Classical.choose_spec (Classical.choose_spec (inclusion_jointly_surjective p))

/-- The carrier rotation obtained by applying the cyclic chart transformation to any affine
representative.  Compatibility with `chartChange` makes this independent of that representative. -/
public noncomputable def a2CyclicCarrier (p : Carrier) : Carrier :=
  inclusion (a2CyclicChartIndex (a2CyclicRepresentativeChart p))
    (a2CyclicRaw (a2CyclicRepresentativeChart p).1
      (a2CyclicRepresentativeCoordinates p))

public theorem a2CyclicCarrier_inclusion (a : ChartIndex) (z : RawCoordinates) :
    a2CyclicCarrier (inclusion a z) =
      inclusion (a2CyclicChartIndex a) (a2CyclicRaw a.1 z) := by
  let b := a2CyclicRepresentativeChart (inclusion a z)
  let w := a2CyclicRepresentativeCoordinates (inclusion a z)
  have hba : inclusion b w = inclusion a z := by
    exact a2CyclicRepresentative_eq (inclusion a z)
  have hchange := (inclusion_eq_iff b a w z).mp hba
  unfold a2CyclicCarrier
  change inclusion (a2CyclicChartIndex b) (a2CyclicRaw b.1 w) =
    inclusion (a2CyclicChartIndex a) (a2CyclicRaw a.1 z)
  apply (inclusion_eq_iff _ _ _ _).mpr
  refine ⟨(a2CyclicRaw_chartChange_source_iff b a w).mpr hchange.1, ?_⟩
  rw [← a2CyclicRaw_chartChange b a w, hchange.2]

private theorem a2CyclicRaw_continuous (upper : Bool) :
    Continuous (a2CyclicRaw upper) := by
  cases upper
  · change Continuous a2CyclicRawLower
    apply continuous_pi
    intro i
    fin_cases i <;> simp [a2CyclicRawLower] <;> fun_prop
  · change Continuous a2CyclicRawUpper
    apply continuous_pi
    intro i
    fin_cases i <;> simp [a2CyclicRawUpper] <;> fun_prop

public theorem a2CyclicCarrier_continuous : Continuous a2CyclicCarrier := by
  rw [continuous_def]
  intro s hs
  rw [gluing.isOpen_iff]
  intro a
  let a' : ChartIndex := a
  change IsOpen (inclusion a' ⁻¹' (a2CyclicCarrier ⁻¹' s))
  have heq : inclusion a' ⁻¹' (a2CyclicCarrier ⁻¹' s) =
      (inclusion (a2CyclicChartIndex a') ∘ a2CyclicRaw a'.1) ⁻¹' s := by
    ext z
    change a2CyclicCarrier (inclusion a' z) ∈ s ↔
      inclusion (a2CyclicChartIndex a') (a2CyclicRaw a'.1 z) ∈ s
    rw [a2CyclicCarrier_inclusion]
  rw [heq]
  exact hs.preimage ((inclusion_isOpenEmbedding _).continuous.comp
    (a2CyclicRaw_continuous a'.1))

@[simp]
public theorem a2CyclicCarrier_apply_three (p : Carrier) :
    a2CyclicCarrier (a2CyclicCarrier (a2CyclicCarrier p)) = p := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
    a2CyclicCarrier_inclusion, a2CyclicChartIndex_apply_three]
  congr 1
  rcases a with ⟨upper, v⟩
  cases upper
  · exact a2CyclicRawLower_apply_three z
  · exact a2CyclicRawUpper_apply_three z

/-- The order-three homeomorphism of the glued toric carrier. -/
public noncomputable def a2CyclicCarrierHomeomorph : Carrier ≃ₜ Carrier where
  toFun := a2CyclicCarrier
  invFun := a2CyclicCarrier ∘ a2CyclicCarrier
  left_inv := a2CyclicCarrier_apply_three
  right_inv := a2CyclicCarrier_apply_three
  continuous_toFun := a2CyclicCarrier_continuous
  continuous_invFun := a2CyclicCarrier_continuous.comp a2CyclicCarrier_continuous

/-- The second phase face, obtained by rotating the explicit zero-axis face. -/
public def constructedCentralPhaseFaceOneCarrier (x : Fin 2 → ℝ) : Carrier :=
  if x 0 ≤ 0 then
    inclusion (false, 0) (singleAxis 1 (centralPhaseDiskLowerCoordinate x))
  else
    inclusion (true, -e₁) (singleAxis 1 (centralPhaseDiskUpperCoordinate x))

/-- Carrier-level cyclic equivariance of the first explicit phase face. -/
public theorem a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier
    (x : Fin 2 → ℝ) :
    a2CyclicCarrier (constructedCentralPhaseFaceZeroCarrier x) =
      constructedCentralPhaseFaceOneCarrier x := by
  by_cases hx : x 0 ≤ 0
  · simp only [constructedCentralPhaseFaceZeroCarrier, constructedCentralPhaseFaceOneCarrier,
      hx, ↓reduceIte]
    rw [a2CyclicCarrier_inclusion, a2CyclicChartIndex_lower_zero]
    exact congrArg (inclusion (false, 0))
      (a2CyclicRawLower_lowerAxisZero (centralPhaseDiskLowerCoordinate x))
  · simp only [constructedCentralPhaseFaceZeroCarrier, constructedCentralPhaseFaceOneCarrier,
      hx, ↓reduceIte]
    rw [a2CyclicCarrier_inclusion, a2CyclicChartIndex_upper_zero]
    exact congrArg (inclusion (true, -e₁))
      (a2CyclicRawUpper_upperAxisTwo (centralPhaseDiskUpperCoordinate x))

/-- The third phase face, obtained by applying the carrier rotation twice. -/
public def constructedCentralPhaseFaceTwoCarrier (x : Fin 2 → ℝ) : Carrier :=
  if x 0 ≤ 0 then
    inclusion (false, 0) (singleAxis 2 (centralPhaseDiskLowerCoordinate x))
  else
    inclusion (true, -e₂) (singleAxis 0 (centralPhaseDiskUpperCoordinate x))

/-- Applying the carrier rotation twice transports the first face to the third face. -/
public theorem a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier
    (x : Fin 2 → ℝ) :
    a2CyclicCarrier (a2CyclicCarrier (constructedCentralPhaseFaceZeroCarrier x)) =
      constructedCentralPhaseFaceTwoCarrier x := by
  by_cases hx : x 0 ≤ 0
  · simp only [constructedCentralPhaseFaceZeroCarrier, constructedCentralPhaseFaceTwoCarrier,
      hx, ↓reduceIte]
    rw [a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
      a2CyclicChartIndex_lower_zero]
    simpa [a2CyclicRaw] using congrArg (inclusion (false, 0))
      (a2CyclicRawLower_sq_lowerAxisZero (centralPhaseDiskLowerCoordinate x))
  · simp only [constructedCentralPhaseFaceZeroCarrier, constructedCentralPhaseFaceTwoCarrier,
      hx, ↓reduceIte]
    rw [a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
      a2CyclicChartIndex_sq_upper_zero]
    exact congrArg (inclusion (true, -e₂))
      (a2CyclicRawUpper_sq_upperAxisTwo (centralPhaseDiskUpperCoordinate x))

/-- Continuity of the second phase face follows by transport through the carrier homeomorphism. -/
public theorem constructedCentralPhaseFaceOneCarrier_continuousOn_closedBall :
    ContinuousOn constructedCentralPhaseFaceOneCarrier (Metric.closedBall 0 1) := by
  have heq : a2CyclicCarrier ∘ constructedCentralPhaseFaceZeroCarrier =
      constructedCentralPhaseFaceOneCarrier := by
    funext x
    exact a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier x
  have h := a2CyclicCarrier_continuous.comp_continuousOn
    constructedCentralPhaseFaceZeroCarrier_continuousOn_closedBall
  rwa [heq] at h

/-- Continuity of the third phase face follows by two cyclic transports. -/
public theorem constructedCentralPhaseFaceTwoCarrier_continuousOn_closedBall :
    ContinuousOn constructedCentralPhaseFaceTwoCarrier (Metric.closedBall 0 1) := by
  have heq : a2CyclicCarrier ∘ a2CyclicCarrier ∘
      constructedCentralPhaseFaceZeroCarrier = constructedCentralPhaseFaceTwoCarrier := by
    funext x
    exact a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier x
  have h := a2CyclicCarrier_continuous.comp_continuousOn
    (a2CyclicCarrier_continuous.comp_continuousOn
      constructedCentralPhaseFaceZeroCarrier_continuousOn_closedBall)
  rwa [heq] at h

/-- The second phase face has the same injective open-cell parametrization as the first. -/
public theorem constructedCentralPhaseFaceOneCarrier_injOn :
    Set.InjOn constructedCentralPhaseFaceOneCarrier (Metric.ball 0 1) := by
  intro x hx y hy hxy
  rw [← a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier,
    ← a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier] at hxy
  exact constructedCentralPhaseFaceZeroCarrier_injOn hx hy
    (a2CyclicCarrierHomeomorph.injective hxy)

/-- The third phase face has the same injective open-cell parametrization as the first. -/
public theorem constructedCentralPhaseFaceTwoCarrier_injOn :
    Set.InjOn constructedCentralPhaseFaceTwoCarrier (Metric.ball 0 1) := by
  intro x hx y hy hxy
  rw [← a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier,
    ← a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier] at hxy
  exact constructedCentralPhaseFaceZeroCarrier_injOn hx hy
    (a2CyclicCarrierHomeomorph.injective (a2CyclicCarrierHomeomorph.injective hxy))

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
