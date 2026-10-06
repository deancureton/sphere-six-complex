module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalTop
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeZero
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TotallyDisconnectedZero
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-! # Actual local homology is concentrated in the manifold dimension -/

noncomputable section

open CategoryTheory ContinuousMap Metric Module Set

universe u

namespace DifferentialGeometry.Topology

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual point complement is path connected in dimension at least two. -/
theorem puncturedSpace_pathConnected_of_finrank (hd : 1 < finrank ℝ E) :
    PathConnectedSpace ({0}ᶜ : Set E) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← finrank_eq_rank ℝ E]
  exact_mod_cast hd

/-- The actual local group at zero vanishes in every degree other than
the dimension, including degrees zero and one. -/
theorem integralEuclideanLocalZero_subsingleton (n k : ℕ)
    (hd : finrank ℝ E = n + 2) (hk : k ≠ n + 2) :
    Subsingleton (integralLocalHomology k (0 : E)) := by
  let := puncturedSpace_pathConnected_of_finrank E (by omega)
  cases k with
  | zero => exact integralRelativeZero_subsingleton ({0}ᶜ : Set E)
  | succ k =>
      cases k with
      | zero =>
          let := integralReducedZero_subsingleton (X := ({0}ᶜ : Set E))
          let e := (integralRelativeConnectingZeroKernelEquiv ({0}ᶜ : Set E)).trans
            (integralZeroMapKernelReducedEquiv (singularSubspaceInclusion ({0}ᶜ : Set E)))
          exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
      | succ k =>
          let := integralSphereHomology_subsingleton (n + 1) (k + 1) E hd (by omega) (by omega)
          let e := (integralRelativeConnectingEquivOfContractible (k + 1) (by omega)
            ({0}ᶜ : Set E)).trans (integralPuncturedSpaceSphereHomologyEquiv E (k + 1))
          exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- The same vanishing holds at every original point, by the actual
translation of its original point-complement pair. -/
theorem integralEuclideanLocal_subsingleton (n k : ℕ)
    (hd : finrank ℝ E = n + 2) (hk : k ≠ n + 2) (x : E) :
    Subsingleton (integralLocalHomology k x) := by
  let e : E ≃ₜ E := Homeomorph.addRight (-x)
  have hx : e x = 0 := add_neg_cancel x
  have h := (integralLocalHomologyHomeomorphIso k e x).toLinearEquiv
  rw [hx] at h
  let := integralEuclideanLocalZero_subsingleton E n k hd hk
  exact ⟨fun a b => h.injective (Subsingleton.elim _ _)⟩

/-- Actual manifold local homology vanishes outside its dimension, by
the original chart and the proved Euclidean computation. -/
theorem integralManifoldLocal_subsingleton (n k : ℕ) (hd : finrank ℝ E = n + 2)
    (hk : k ≠ n + 2) (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M]
    (x : M) : Subsingleton (integralLocalHomology k x) := by
  let := integralEuclideanLocal_subsingleton E n k hd hk (chartAt E x x)
  exact ⟨fun a b => (integralLocalHomologyChartIso (Y := E) k x).toLinearEquiv.injective
    (Subsingleton.elim _ _)⟩

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousMap Metric Module Set

universe u

namespace DifferentialGeometry.Topology

private theorem integral_homology_subsingleton_of_isEmpty
    {X : Type u} [TopologicalSpace X] [IsEmpty X] (n : ℕ) :
    Subsingleton (integralSingularHomology n X) := by
  cases n with
  | zero =>
    let e := integralTotallyDisconnectedZeroEquiv (X := X)
    exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
  | succ n =>
    exact integralSingularHomology_subsingleton_of_totallyDisconnected (n + 1) (by omega) X

private theorem integral_local_zero_subsingleton_of_finrank_lt
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hn : finrank ℝ E < n) :
    Subsingleton (integralLocalHomology n (0 : E)) := by
  by_cases hlarge : 2 ≤ finrank ℝ E
  · exact integralEuclideanLocalZero_subsingleton E (finrank ℝ E - 2) n (by omega) (by omega)
  cases n with
  | zero => omega
  | succ n =>
    by_cases hd : finrank ℝ E = 0
    · let : IsEmpty ({0}ᶜ : Set E) :=
        ⟨fun x => x.property ((finrank_zero_iff_forall_zero.mp hd) x.val)⟩
      let := integral_homology_subsingleton_of_isEmpty (X := ({0}ᶜ : Set E)) n
      let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) E
      exact ModuleCat.subsingleton_of_isZero
        (((integralRelativeChainSequence_shortExact ({0}ᶜ : Set E)).homology_exact₃
          (n + 1) n (by simp)).isZero_X₂
          ((ModuleCat.isZero_of_subsingleton (integralSingularHomology (n + 1) E)).eq_of_src _ _)
          ((ModuleCat.isZero_of_subsingleton
            (integralSingularHomology n ({0}ᶜ : Set E))).eq_of_tgt _ _))
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, finrank ℝ E = m + 1 := ⟨finrank ℝ E - 1, by omega⟩
      let := integralSphereHomology_subsingleton m n E hm (by omega) (by omega)
      let e := (integralRelativeConnectingEquivOfContractible n (by omega)
        ({0}ᶜ : Set E)).trans (integralPuncturedSpaceSphereHomologyEquiv E n)
      exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

theorem integralLocalHomology_subsingleton_of_finrank_lt
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hn : finrank ℝ E < n) (c : E) :
    Subsingleton (integralLocalHomology n c) := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    b.equivFunL.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let h := (e.toHomeomorph.trans (Homeomorph.subRight (e c)))
  have hc : h c = 0 := sub_self (e c)
  have he := (integralLocalHomologyHomeomorphIso n h c).toLinearEquiv
  rw [hc] at he
  let := integral_local_zero_subsingleton_of_finrank_lt (E := EuclideanSpace ℝ ι) n
    (by rw [← e.toLinearEquiv.finrank_eq]; exact hn)
  exact ⟨fun a b => he.injective (Subsingleton.elim _ _)⟩

end DifferentialGeometry.Topology

end
