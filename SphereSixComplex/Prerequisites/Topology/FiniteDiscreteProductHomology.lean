module

public import SphereSixComplex.Prerequisites.Topology.WangHomologyPresentationProof
public section
noncomputable section
open Set Topology
namespace SphereSixComplex.IntegralSingularHomology
open WangFromMayerVietoris
variable (J X : Type) [Fintype J] [TopologicalSpace J] [DiscreteTopology J] [TopologicalSpace X]
private def component (j : J) : Set (J × X) := {p | p.1 = j}
private def componentHomeomorph (j : J) : component J X j ≃ₜ X where
  toFun p := p.1.2
  invFun x := ⟨(j,x),rfl⟩
  left_inv p := by apply Subtype.ext; exact Prod.ext p.2.symm rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.snd
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _
private theorem component_sum_bijective (n : ℕ) :
    Function.Bijective (coverSumMap (component J X) n) := by
  apply coverSumMap_bijective
  · intro j
    exact (isOpen_discrete ({j} : Set J)).preimage continuous_fst
  · intro i j h
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact h (hi.symm.trans hj)
  · ext p
    simp [component]
/-- Integral homology of a product with a finite discrete space, read component by component. -/
def discreteProductEquiv (n : ℕ) :
    IntegralSingularHomology n (J × X) ≃+ (J → IntegralSingularHomology n X) :=
  (AddEquiv.ofBijective (coverSumMap (component J X) n)
    (component_sum_bijective J X n)).symm.trans
    (AddEquiv.piCongrRight (fun j => integralSingularHomologyEquiv n (componentHomeomorph J X j)))

theorem discreteProductEquiv_symm_apply (n : ℕ) (v : J → IntegralSingularHomology n X) :
    (discreteProductEquiv J X n).symm v =
      ∑ j, integralSingularHomologyMap n
        ((ContinuousMap.const X j).prodMk (ContinuousMap.id X)) (v j) := by
  change coverSumMap (component J X) n
    (fun j => (integralSingularHomologyEquiv n (componentHomeomorph J X j)).symm (v j)) = _
  rw [coverSumMap_apply]
  apply Finset.sum_congr rfl
  intro j _
  change integralSingularHomologyMap n (subsetInclusion (component J X j))
    (integralSingularHomologyMap n (componentHomeomorph J X j).symm (v j)) = _
  rw [integralSingularHomologyMap_comp_wang]
  rfl


theorem discreteProductEquiv_component [DecidableEq J] (n : ℕ) (j : J)
    (x : IntegralSingularHomology n X) :
    discreteProductEquiv J X n (integralSingularHomologyMap n
      ((ContinuousMap.const X j).prodMk (ContinuousMap.id X)) x) =
      Pi.single j x := by
  classical
  apply (discreteProductEquiv J X n).symm.injective
  rw [AddEquiv.symm_apply_apply, discreteProductEquiv_symm_apply]
  simp [Pi.single_apply, apply_ite]

end SphereSixComplex.IntegralSingularHomology
