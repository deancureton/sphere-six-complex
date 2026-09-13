module

public import SphereSixComplex.Paper.Topology.StandardA2ToricCentralFiberOneCells

/-!
# Cyclic symmetry of the standard `A₂` central fibre

The affine order-three rotation of the triangular lattice cyclically permutes the three
one-dimensional strata.  Its height-one linearization gives the corresponding fan symmetry,
while the two triangle orientations use opposite cyclic permutations of affine coordinates.
-/

@[expose] public section

noncomputable section

open Matrix Set

namespace SphereSixComplex.Geometry.CuspCollar

open SphereSixComplex
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

/-- The linear part of the order-three affine rotation of the triangular lattice. -/
public def a2CyclicLinear (v : ToricLattice) : ToricLattice :=
  ![-v 0 - v 1, v 0]

@[simp]
public theorem a2CyclicLinear_zero : a2CyclicLinear 0 = 0 := by
  ext i
  fin_cases i <;> simp [a2CyclicLinear]

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

end SphereSixComplex.Geometry.CuspCollar

end
