module

public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorStandardFrameDescent

/-!
# Analytic descent for affine-line torsors

Local equivariant sections on regular, elliptic, and cusp patches are glued by the proved
normalized Cousin theorem. The infinity germ supplies the required bound on the closed cusp.
-/

namespace SphereSixComplex.Periods

/-- The two homogeneous frames used by the construction are the acyclic line bundles
`O(-1)` and `O` on the projective line. -/
@[expose] public def OrbifoldAffineDescentData.HasAcyclicProjectiveLineFrame
    (P : OrbifoldAffineDescentData) : Prop :=
  (P.frameOrderOne = 2 ∧ P.frameOrderTwo = 1 ∧
      P.frameTransition = fun q ↦ q⁻¹) ∨
    (P.frameOrderOne = 0 ∧ P.frameOrderTwo = 0 ∧
      P.frameTransition = fun _ ↦ 1)


public theorem OrbifoldAffineDescentData.hasCuspBoundedSection
    (P : OrbifoldAffineDescentData)
    (hP : P.HasAcyclicProjectiveLineFrame) :
    P.HasCuspBoundedSection := by
  apply P.hasCuspBoundedSection_of_standard_transition
  exact hP.elim (fun h ↦ Or.inl h.2.2) (fun h ↦ Or.inr h.2.2)


end SphereSixComplex.Periods
