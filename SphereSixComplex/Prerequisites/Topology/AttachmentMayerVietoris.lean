module

public import SphereSixComplex.Prerequisites.Topology.ExactSplitting
public import SphereSixComplex.Prerequisites.Topology.IntegralMayerVietorisTheorem

@[expose] public section

namespace SphereSixComplex.IntegralMayerVietoris

/-- Split an open-cover Mayer–Vietoris sequence while retaining the actual sum and boundary maps. -/
theorem exists_homologyEquiv_coker_prod_ker
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (k : ℕ)
    [Module.Projective ℤ (LinearMap.ker (differenceMap A B k).toIntLinearMap)] :
    ∃ δ : IntegralSingularHomology (k + 1) (A ∪ B : Set X) →+
        IntegralSingularHomology k (A ∩ B : Set X),
      ∃ e : IntegralSingularHomology (k + 1) (A ∪ B : Set X) ≃+
          (((IntegralSingularHomology (k + 1) A × IntegralSingularHomology (k + 1) B) ⧸
              LinearMap.range (differenceMap A B (k + 1)).toIntLinearMap) ×
            LinearMap.ker (differenceMap A B k).toIntLinearMap),
        Function.Exact (sumMap A B (k + 1)) δ ∧
        Function.Exact δ (differenceMap A B k) ∧
        (∀ p, e (sumMap A B (k + 1) p) = (Submodule.Quotient.mk p, 0)) ∧
        ∀ x, ((e x).2 : IntegralSingularHomology k (A ∩ B : Set X)) = δ x := by
  obtain ⟨boundary, hex⟩ := exact_sequence_of_isOpen A B hA hB
  obtain ⟨e, he₁, he₂⟩ := LinearMap.exists_equiv_coker_prod_ker
    (differenceMap A B (k + 1)).toIntLinearMap
    (sumMap A B (k + 1)).toIntLinearMap (boundary k).toIntLinearMap
    (differenceMap A B k).toIntLinearMap (hex (k + 1)).2.2 (hex k).1 (hex k).2.1
  exact ⟨boundary k, e.toAddEquiv, (hex k).1, (hex k).2.1, he₁, he₂⟩
end SphereSixComplex.IntegralMayerVietoris

end
