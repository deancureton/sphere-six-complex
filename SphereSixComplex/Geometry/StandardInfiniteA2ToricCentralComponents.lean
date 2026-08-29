/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrierGeometry

/-!
# Central components of the standard infinite `A₂` toric carrier

This file constructs the irreducible components of the zero fibre directly from the affine
toric gluing.  A component is the image of the coordinate hyperplane belonging to its ray.
-/

@[expose] public section

noncomputable section

open Matrix Set
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

private theorem heightOneRay_injective : Function.Injective heightOneRay := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

private theorem coneMatrix_mul_transitionMatrix (a b : ChartIndex) :
    a2ConeMatrix b.1 b.2 * transitionMatrix a b = a2ConeMatrix a.1 a.2 := by
  rw [transitionMatrix, ← Matrix.mul_assoc, coneMatrix_mul_dualMatrix, Matrix.one_mul]

private theorem transitionColumn_single_of_zero
    (a b : ChartIndex) {z : RawCoordinates} (hz : z ∈ (chartChange a b).source)
    {j : Fin 3} (hj : z j = 0) :
    ∃ i : Fin 3, ∀ k, transitionMatrix a b k j = if k = i then 1 else 0 := by
  rw [chartChange_source] at hz
  have hn (k : Fin 3) : 0 ≤ transitionMatrix a b k j := by
    by_contra h
    exact hz k j (lt_of_not_ge h) hj
  have hsum := transitionMatrix_heightOne a b j
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.sum_univ_zero, add_zero] at hsum
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have hcases : transitionMatrix a b 0 j = 1 ∨
      transitionMatrix a b 1 j = 1 ∨ transitionMatrix a b 2 j = 1 := by
    omega
  rcases hcases with h | h | h
  · refine ⟨0, ?_⟩
    intro k
    fin_cases k <;> simp <;> omega
  · refine ⟨1, ?_⟩
    intro k
    fin_cases k <;> simp <;> omega
  · refine ⟨2, ?_⟩
    intro k
    fin_cases k <;> simp <;> omega

private theorem triangle_vertex_eq_of_transitionColumn_single
    (a b : ChartIndex) (j i : Fin 3)
    (hcol : ∀ k, transitionMatrix a b k j = if k = i then 1 else 0) :
    a2Triangle a.1 a.2 j = a2Triangle b.1 b.2 i := by
  apply heightOneRay_injective
  have hmatrix := coneMatrix_mul_transitionMatrix a b
  funext k
  have hentry := congrArg (fun M ↦ M k j) hmatrix
  simpa [a2ConeMatrix, Matrix.mul_apply, hcol] using hentry.symm

private theorem a2Triangle_injective (upper : Bool) (v : ToricLattice) :
    Function.Injective (a2Triangle upper v) := by
  intro i j h
  have hcone (k : Fin 3) :
      a2ConeMatrix upper v k i = a2ConeMatrix upper v k j := by
    exact congrFun (congrArg heightOneRay h) k
  have hmatrix := dualMatrix_mul_coneMatrix (upper, v)
  have hentry (k : Fin 3) :
      (1 : Matrix (Fin 3) (Fin 3) ℤ) k i = (1 : Matrix (Fin 3) (Fin 3) ℤ) k j := by
    rw [← hmatrix, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcone l]
  by_contra hij
  have hii := hentry i
  simp [hij] at hii

/-- The ray component obtained by gluing all coordinate hyperplanes labelled by `v`. -/
public def carrierCentralComponent (v : ToricLattice) : Set Carrier :=
  {p | ∃ (a : ChartIndex) (i : Fin 3) (z : RawCoordinates),
    a2Triangle a.1 a.2 i = v ∧ z i = 0 ∧ inclusion a z = p}

/-- In one affine chart, the component belonging to its `i`th ray is precisely the `i`th
coordinate hyperplane. -/
public theorem carrierCentralComponent_in_chart
    (a : ChartIndex) (i : Fin 3) (p : Carrier) :
    letI := chartedSpace
    p ∈ (toricChart a).source →
      (p ∈ carrierCentralComponent (a2Triangle a.1 a.2 i) ↔ toricChart a p i = 0) := by
  let _ := chartedSpace
  intro hp
  rw [toricChart_source] at hp
  obtain ⟨z, rfl⟩ := hp
  rw [toricChart_inclusion]
  change inclusion a z ∈ carrierCentralComponent (a2Triangle a.1 a.2 i) ↔ z i = 0
  constructor
  · rintro ⟨b, j, w, hray, hw, he⟩
    have hchange := (inclusion_eq_iff b a w z).mp he
    obtain ⟨k, hk⟩ := transitionColumn_single_of_zero b a hchange.1 hw
    have hray' := triangle_vertex_eq_of_transitionColumn_single b a j k hk
    have hki : k = i := a2Triangle_injective a.1 a.2 (hray'.symm.trans hray)
    subst k
    have hchange_apply := congrFun hchange.2 i
    change monomial (transitionMatrix b a) w i = z i at hchange_apply
    rw [← hchange_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hw, hk]
  · intro hi
    exact ⟨a, i, z, rfl, hi, rfl⟩

/-- The zero fibre of the height monomial is the union of its ray components. -/
public theorem carrierCentralFiber_eq_iUnion :
    carrierHeight ⁻¹' {0} = ⋃ v, carrierCentralComponent v := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
    change carrierHeight (inclusion a z) = 0 at hp
    rw [carrierHeight_inclusion] at hp
    change z 0 * z 1 * z 2 = 0 at hp
    rcases mul_eq_zero.mp hp with h01 | h2
    · rcases mul_eq_zero.mp h01 with h0 | h1
      · exact Set.mem_iUnion.mpr
          ⟨a2Triangle a.1 a.2 0, a, 0, z, rfl, h0, rfl⟩
      · exact Set.mem_iUnion.mpr
          ⟨a2Triangle a.1 a.2 1, a, 1, z, rfl, h1, rfl⟩
    · exact Set.mem_iUnion.mpr
        ⟨a2Triangle a.1 a.2 2, a, 2, z, rfl, h2, rfl⟩
  · intro hp
    obtain ⟨v, a, i, z, _, hi, rfl⟩ := Set.mem_iUnion.mp hp
    change carrierHeight (inclusion a z) = 0
    rw [carrierHeight_inclusion]
    rw [rawHeight, mul_eq_zero, mul_eq_zero]
    fin_cases i
    · exact Or.inl (Or.inl (by simpa using hi))
    · exact Or.inl (Or.inr (by simpa using hi))
    · exact Or.inr (by simpa using hi)

/-- Any ray component meeting an affine chart is one of the chart's three rays. -/
private theorem ray_mem_triangle_range_of_component_meets_chart
    (a : ChartIndex) (v : ToricLattice) (p : Carrier)
    (hv : p ∈ carrierCentralComponent v) (hp : p ∈ Set.range (inclusion a)) :
    v ∈ Set.range (a2Triangle a.1 a.2) := by
  obtain ⟨b, j, w, hray, hw, hwp⟩ := hv
  obtain ⟨z, hzp⟩ := hp
  have hchange := (inclusion_eq_iff b a w z).mp (hwp.trans hzp.symm)
  obtain ⟨i, hi⟩ := transitionColumn_single_of_zero b a hchange.1 hw
  refine ⟨i, ?_⟩
  exact (triangle_vertex_eq_of_transitionColumn_single b a j i hi).symm.trans hray

/-- A ray component not belonging to a maximal cone is disjoint from its affine chart. -/
public theorem otherCarrierCentralComponent_disjoint_chart
    (a : ChartIndex) (v : ToricLattice)
    (hv : v ∉ Set.range (a2Triangle a.1 a.2)) :
    letI := chartedSpace
    Disjoint (carrierCentralComponent v) (toricChart a).source := by
  let _ := chartedSpace
  rw [toricChart_source]
  rw [Set.disjoint_left]
  intro p hp hchart
  exact hv (ray_mem_triangle_range_of_component_meets_chart a v p hp hchart)

private theorem carrierTorusAction_mapsTo_centralComponent
    (g : DenseTorus) (v : ToricLattice) :
    MapsTo (carrierTorusAction g) (carrierCentralComponent v) (carrierCentralComponent v) := by
  intro p hp
  obtain ⟨a, i, z, hray, hi, rfl⟩ := hp
  change carrierTorusActionFun g (inclusion a z) ∈ carrierCentralComponent v
  rw [carrierTorusActionFun_inclusion]
  refine ⟨a, i, torusChartCoordinates a g * z, hray, ?_, rfl⟩
  simp [hi]

/-- The dense torus preserves every ray component setwise. -/
public theorem carrierTorusAction_centralComponent
    (g : DenseTorus) (v : ToricLattice) (p : Carrier) :
    carrierTorusAction g p ∈ carrierCentralComponent v ↔ p ∈ carrierCentralComponent v := by
  constructor
  · intro hp
    have hinv := carrierTorusAction_mapsTo_centralComponent g⁻¹ v hp
    have he : carrierTorusAction g⁻¹ (carrierTorusAction g p) = p := by
      change carrierTorusActionFun g⁻¹ (carrierTorusActionFun g p) = p
      rw [← carrierTorusActionFun_mul]
      simpa using carrierTorusActionFun_one p
    rwa [he] at hinv
  · intro hp
    exact carrierTorusAction_mapsTo_centralComponent g v hp

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
