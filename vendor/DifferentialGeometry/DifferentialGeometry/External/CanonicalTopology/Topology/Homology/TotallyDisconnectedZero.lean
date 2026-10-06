module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ZeroHomologyMaps
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

/-! # Actual degree-zero homology of a totally disconnected space -/

noncomputable section

open CategoryTheory ContinuousMap Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [TotallyDisconnectedSpace X]

/-- Every original path in a totally disconnected space has equal endpoints. -/
theorem path_endpoints_eq_of_totallyDisconnected {x y : X} (p : Path x y) : x = y := by
  have hs := (isPreconnected_range p.continuous).subsingleton
  exact hs ⟨0, p.source⟩ ⟨1, p.target⟩

/-- The actual degree-one differential is zero on a totally disconnected
space, since every original singular edge has equal endpoints. -/
theorem integralBoundary_one_eq_zero_of_totallyDisconnected :
    ((integralSingularChains X).d 1 0).hom = 0 := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, ← integralPathChain_simplexPath,
    integralPathChain_boundary]
  change _ - _ = 0
  rw [path_endpoints_eq_of_totallyDisconnected (integralSimplexPath σ)]
  exact sub_self _

/-- The original zero-chain class map is bijective when every actual
one-boundary vanishes. -/
theorem integralZeroChainClass_bijective_of_totallyDisconnected :
    Function.Bijective (integralZeroChainClass (X := X)) := by
  refine ⟨?_, integralZeroChainClass_surjective⟩
  intro c d h
  obtain ⟨b, hb⟩ := (integralZeroChainClass_eq_iff c d).mp h
  have hz : (integralSingularChains X).d 1 0 b = 0 :=
    LinearMap.congr_fun integralBoundary_one_eq_zero_of_totallyDisconnected b
  exact sub_eq_zero.mp (hb.symm.trans hz)

/-- Original H0 is the free integral module on the actual points, with
coordinates supplied by the original singular vertex basis. -/
def integralTotallyDisconnectedZeroEquiv :
    integralSingularHomology 0 X ≃ₗ[ℤ] (X →₀ ℤ) :=
  (LinearEquiv.ofBijective integralZeroChainClass
    integralZeroChainClass_bijective_of_totallyDisconnected).symm.trans
      ((integralSingularChainRepr 0 X).trans (Finsupp.domLCongr TopCat.toSSetObj₀Equiv))

/-- The actual class of a vertex corresponds to coefficient one at that
same point, fixing the normalization of this H0 computation. -/
theorem integralTotallyDisconnectedZeroEquiv_vertex (x : X) :
    integralTotallyDisconnectedZeroEquiv (integralZeroChainClass (integralVertexChain x)) =
      Finsupp.single x 1 := by
  change Finsupp.domLCongr (R := ℤ) (M := ℤ) TopCat.toSSetObj₀Equiv (integralSingularChainRepr 0 X
    ((LinearEquiv.ofBijective integralZeroChainClass
      integralZeroChainClass_bijective_of_totallyDisconnected).symm
        (integralZeroChainClass (integralVertexChain x)))) = _
  have hi : (LinearEquiv.ofBijective integralZeroChainClass
      integralZeroChainClass_bijective_of_totallyDisconnected).symm
        (integralZeroChainClass (integralVertexChain x)) = integralVertexChain x :=
    (LinearEquiv.ofBijective integralZeroChainClass
      integralZeroChainClass_bijective_of_totallyDisconnected).symm_apply_apply _
  rw [hi]
  unfold integralVertexChain
  rw [integralSingularChainRepr_simplex]
  simp

end DifferentialGeometry.Topology
