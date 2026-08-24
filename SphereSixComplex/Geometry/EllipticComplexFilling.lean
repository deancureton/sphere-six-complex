module

public import SphereSixComplex.Geometry.CuspFilling
public import SphereSixComplex.Geometry.EllipticFilling

/-!
# Complex manifolds from the elliptic fillings

The finite logarithmic-transform actions from `EllipticFilling` are combined with the generic
analytic quotient-atlas theorem proved for covering actions.
-/

namespace SphereSixComplex.Geometry

open SphereSixComplex.LatticeData

noncomputable section

/-- A free analytic elliptic action has a complex-manifold quotient. -/
public theorem ellipticQuotient_isManifold
    {m : ℕ} [NeZero m] {Base Torus E H : Type*} [AddCommGroup Torus]
    [TopologicalSpace (Base × Torus)] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space (Base × Torus)] [LocallyCompactSpace (Base × Torus)]
    [ChartedSpace H (Base × Torus)] [IsManifold I ω (Base × Torus)]
    (D : EllipticActionData m Base Torus)
    (hfree : letI := D.diagonalAction
      IsCancelSMul (FiniteCyclic m) (Base × Torus))
    (hholomorphic : ∀ g : FiniteCyclic m,
      ContMDiff I I ω (fun p : Base × Torus ↦ D.representation g p)) :
    letI := D.diagonalAction
    let hf := quotient_isQuotientCoveringMap D hfree
      (fun g ↦ (hholomorphic g).continuous)
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (FiniteCyclic m) (Base × Torus)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω
      (MulAction.orbitRel.Quotient (FiniteCyclic m) (Base × Torus)) := by
  let _ := D.diagonalAction
  let _ : IsCancelSMul (FiniteCyclic m) (Base × Torus) := hfree
  let _ : ContinuousConstSMul (FiniteCyclic m) (Base × Torus) :=
    ⟨fun g ↦ (hholomorphic g).continuous⟩
  let hf := quotient_isQuotientCoveringMap D hfree
    (fun g ↦ (hholomorphic g).continuous)
  let _ : ChartedSpace H
      (MulAction.orbitRel.Quotient (FiniteCyclic m) (Base × Torus)) :=
    hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
  exact CuspFilling.quotient_isManifold I hf hholomorphic

/-- The order-three filling with translation vector `epsilon` is a complex manifold. -/
public theorem epsilonQuotient_isManifold
    {Base Torus E H : Type*} [AddCommGroup Torus]
    [TopologicalSpace (Base × Torus)] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space (Base × Torus)] [LocallyCompactSpace (Base × Torus)]
    [ChartedSpace H (Base × Torus)] [IsManifold I ω (Base × Torus)]
    (D : EllipticActionData 3 Base Torus) (hv : D.translationVector = epsilon)
    (hholomorphic : ∀ g : FiniteCyclic 3,
      ContMDiff I I ω (fun p : Base × Torus ↦ D.representation g p)) :
    letI := D.diagonalAction
    let hf := quotient_isQuotientCoveringMap D (epsilon_action_free D hv)
      (fun g ↦ (hholomorphic g).continuous)
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (FiniteCyclic 3) (Base × Torus)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω
      (MulAction.orbitRel.Quotient (FiniteCyclic 3) (Base × Torus)) := by
  exact ellipticQuotient_isManifold I D (epsilon_action_free D hv) hholomorphic

/-- The order-four filling with translation vector `-epsilon'` is a complex manifold. -/
public theorem negEpsilonPrimeQuotient_isManifold
    {Base Torus E H : Type*} [AddCommGroup Torus]
    [TopologicalSpace (Base × Torus)] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : ModelWithCorners ℂ E H)
    [T2Space (Base × Torus)] [LocallyCompactSpace (Base × Torus)]
    [ChartedSpace H (Base × Torus)] [IsManifold I ω (Base × Torus)]
    (D : EllipticActionData 4 Base Torus) (hv : D.translationVector = -epsilon')
    (hholomorphic : ∀ g : FiniteCyclic 4,
      ContMDiff I I ω (fun p : Base × Torus ↦ D.representation g p)) :
    letI := D.diagonalAction
    let hf := quotient_isQuotientCoveringMap D (neg_epsilonPrime_action_free D hv)
      (fun g ↦ (hholomorphic g).continuous)
    letI : ChartedSpace H
      (MulAction.orbitRel.Quotient (FiniteCyclic 4) (Base × Torus)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold I ω
      (MulAction.orbitRel.Quotient (FiniteCyclic 4) (Base × Torus)) := by
  exact ellipticQuotient_isManifold I D (neg_epsilonPrime_action_free D hv) hholomorphic

end

end SphereSixComplex.Geometry
