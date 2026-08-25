module

public import SphereSixComplex.Topology.BoundarySevenCechTotalQuasiIsoProof
public import SphereSixComplex.Topology.StandardSpherePositiveHomology

/-!
# Positive integral homology of the standard six-sphere from the boundary comparison

The completed comparison between simplicial and singular chains transports the elementary
homology calculation of the boundary of the seven-simplex to the standard six-sphere. In degrees
one through five, the zero-vertex cone contracts the simplicial chains. Above degree six,
normalization and the dimension bound make homology vanish.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- The zero-vertex cone proves exactness in every positive degree below the top dimension. -/
public theorem boundarySeven_simplicialHomology_isZero_of_pos_of_lt_six
    (R : AddCommGrpCat) (k : ℕ) (hkPos : 0 < k) (hkTop : k < 6) :
    IsZero (((∂Δ[7] : SSet.{0}).chainComplex R).homology k) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkPos)
  let K := (∂Δ[7] : SSet.{0}).chainComplex R
  rw [← K.exactAt_iff_isZero_homology]
  apply (K.exactAt_iff' (i := n + 1 + 1) (j := n + 1) (k := n) (by simp) (by simp)).2
  rw [ShortComplex.ab_exact_iff]
  change ∀ x : K.X (n + 1), K.d (n + 1) n x = 0 →
    ∃ y : K.X (n + 1 + 1), K.d (n + 1 + 1) (n + 1) y = x
  intro x hx
  let cPrev := boundarySevenZeroConeComponent R n (by omega)
  let c := boundarySevenZeroConeComponent R (n + 1) (by omega)
  refine ⟨c x, ?_⟩
  have h := boundarySevenZeroConeComponent_boundary_succ R n (by omega)
  have hx' := ConcreteCategory.congr_hom h x
  dsimp [K] at hx ⊢
  simpa [cPrev, c, hx] using hx'

/-- Simplicial homology of the boundary vanishes strictly above its dimension. -/
public theorem boundarySeven_simplicialHomology_isZero_of_six_lt
    (R : AddCommGrpCat) (k : ℕ) (hk : 6 < k) :
    IsZero (((∂Δ[7] : SSet.{0}).chainComplex R).homology k) := by
  exact (∂Δ[7] : SSet.{0}).isZero_homology_of_hasDimensionLT R k 7 (by omega)

/-- The canonical boundary comparison transports every simplicial vanishing degree to the
standard six-sphere. -/
public theorem sixSphere_integralSingularHomology_isZero_of_boundarySeven
    (k : ℕ)
    (hsimplicial : IsZero
      (((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).homology k)) :
    IsZero (((singularHomologyFunctor AddCommGrpCat k).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of SixSphere)) := by
  have hrealization := realizationSingularHomology_isZero_of_simplicial
    (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ) k
      boundarySeven_integralComparison_proof hsimplicial
  obtain ⟨e⟩ := boundarySevenRealizationHomeomorphSixSphere
  exact hrealization.of_iso
    (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).mapIso
      (TopCat.isoOfHomeo e.symm))

/-- The proved boundary comparison gives the complete positive-degree integral homology of the
standard six-sphere. -/
public theorem establishedSixSpherePositiveHomologyInputs_proof :
    SixSpherePositiveHomologyInputs where
  degreeSix := ⟨boundarySevenExplicitSphereHomologyAddEquivInt
    boundarySeven_integralComparison_proof
      standardSimplexBoundarySevenHomeomorphSixSphere⟩
  otherDegrees k hkZero hkSix := by
    apply AddCommGrpCat.subsingleton_of_isZero
    apply sixSphere_integralSingularHomology_isZero_of_boundarySeven
    by_cases hkLow : k < 6
    · exact boundarySeven_simplicialHomology_isZero_of_pos_of_lt_six
        (AddCommGrpCat.of ℤ) k (Nat.pos_of_ne_zero hkZero) hkLow
    · exact boundarySeven_simplicialHomology_isZero_of_six_lt
        (AddCommGrpCat.of ℤ) k (by omega)

end SphereSixComplex
