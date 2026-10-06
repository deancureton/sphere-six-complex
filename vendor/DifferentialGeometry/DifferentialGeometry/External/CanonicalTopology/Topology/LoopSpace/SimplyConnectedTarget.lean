module

public import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.BasedCircle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

/-! # Continuous circle loops in a simply connected target

The contractions use the actual path homotopies supplied by simple connectivity,
then the proved circle/path identification. No second-homotopy vanishing or
canonical class is assumed here.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q]

/-- Simple connectivity contracts every actual quotient-circle loop. -/
theorem circleLoop_nullhomotopic (γ : freeLoop Q) : γ.Nullhomotopic := by
  let q := γ 0
  let p := circleToPath (⟨γ, rfl⟩ : basedCircleLoop q)
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl q)
  have hH : Continuous H.eval := Path.continuous_uncurry_iff.mp H.continuous
  have hc : Continuous (fun t => pathToCircle (H.eval t)) := continuous_pathToCircle.comp hH
  refine ⟨q, ⟨⟨⟨fun z => pathToCircle (H.eval z.1) z.2,
    (FreeLoop.continuous_family_iff _).mp hc⟩, ?_, ?_⟩⟩⟩
  · intro θ
    change pathToCircle (H.eval 0) θ = γ θ
    rw [H.eval_zero]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    exact pathToCircle_coe p t
  · intro θ
    change pathToCircle (H.eval 1) θ = q
    rw [H.eval_one]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    exact pathToCircle_coe (Path.refl q) t

/-- The source's contractible-loop subspace is the entire continuous loop
space for a simply connected target, by an actual homeomorphism. -/
def contractibleLoopHomeomorphFreeLoop (Q : Type*) [TopologicalSpace Q] [SimplyConnectedSpace Q] :
    contractibleLoop Q ≃ₜ freeLoop Q where
  toFun := Subtype.val
  invFun γ := ⟨γ, circleLoop_nullhomotopic γ⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- In the source's specified compact-open topology, any two loops in a
simply connected target are joined by an actual continuous loop family. -/
theorem joined_freeLoops (γ η : freeLoop Q) : Joined γ η := by
  obtain ⟨q, hq⟩ := circleLoop_nullhomotopic γ
  obtain ⟨r, hr⟩ := circleLoop_nullhomotopic η
  have hqr : Joined (ContinuousMap.const loopCircle q) (ContinuousMap.const loopCircle r) :=
    (PathConnectedSpace.joined q r).map FreeLoop.constants.continuous
  exact ((FreeLoop.homotopic_iff_joined _ _).mp hq).trans
    (hqr.trans ((FreeLoop.homotopic_iff_joined _ _).mp hr).symm)

/-- Path connectedness of the actual full continuous loop space. -/
instance freeLoop_pathConnected_of_simplyConnected : PathConnectedSpace (freeLoop Q) where
  nonempty := ⟨ContinuousMap.const loopCircle (Classical.arbitrary Q)⟩
  joined := joined_freeLoops

/-- Path connectedness holds on the same actual contractible-loop subspace. -/
instance contractibleLoop_pathConnected_of_simplyConnected : PathConnectedSpace (contractibleLoop Q) :=
  (contractibleLoopHomeomorphFreeLoop Q).symm.surjective.pathConnectedSpace
    (contractibleLoopHomeomorphFreeLoop Q).symm.continuous

end DifferentialGeometry.Topology
