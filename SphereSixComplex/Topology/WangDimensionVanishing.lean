module

public import SphereSixComplex.Topology.CellularDimensionVanishing
public import SphereSixComplex.Topology.WangHomologyPresentation

/-!
# Vanishing homology of a mapping torus above its fibre's dimension

A bundle over a bouquet of circles has no homology one degree above the top two degrees of its
fibre.  This is read straight off the Wang exact sequence: the incoming term is the fibre's
homology in the same degree and the outgoing term is the fibre's homology one degree below, so
both vanishing forces the middle term to vanish.

Together with the cellular dimension bound this is what discharges a collar's sixth homology: a
collar realized as a mapping torus over a fibre built from cells of dimension at most four has no
fifth or sixth fibre homology, hence none of its own in degree six.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

variable {ι F : Type}
  [Fintype ι] [Inhabited ι] [TopologicalSpace ι] [TopologicalSpace F]

/-- A finite-bouquet mapping torus has no `(k+1)`-st homology once its fibre has none in degrees
`k` and `k + 1`. -/
public theorem subsingleton_homology_succ_finiteBouquetMappingTorus
    [DiscreteTopology ι]
    (φ : ι → F ≃ₜ F) (k : ℕ)
    (hsucc : Subsingleton (IntegralSingularHomology (k + 1) F))
    (hk : Subsingleton (IntegralSingularHomology k F)) :
    Subsingleton (IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ)) := by
  let W := establishedFiniteBouquetMappingTorusWangSequence φ k
  have key : ∀ z : IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ), z = 0 := by
    intro z
    -- The fibre has no `k`-th homology, so the Wang boundary of `z` vanishes and `z` comes from
    -- the fibre; the fibre has no `(k+1)`-st homology either, so `z` is the image of `0`.
    have hz : W.boundary z = 0 := Subsingleton.elim _ _
    obtain ⟨w, hw⟩ := W.exact_inclusion_boundary z |>.mp hz
    rw [← hw, show w = 0 from Subsingleton.elim _ _, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

/-- A mapping torus over a fibre carrying the standard `A₂` toric cell labelling has no sixth
integral singular homology.  This is the shape of the remaining Section 7 collar obligation: the
labelling stops at degree four, so the fibre contributes nothing in degrees five and six. -/
public theorem subsingleton_homology_six_finiteBouquetMappingTorus_of_labelledA2Cells
    [DiscreteTopology ι]
    [Topology.CWComplex (Set.univ : Set F)]
    (e : ∀ n, Topology.CWComplex.cell (Set.univ : Set F) n ≃ cuspWCellIndex n)
    (φ : ι → F ≃ₜ F) :
    Subsingleton (IntegralSingularHomology 6 (FiniteBouquetMappingTorus φ)) :=
  subsingleton_homology_succ_finiteBouquetMappingTorus φ 5
    (subsingleton_integralSingularHomology_of_labelledA2Cells F e 6 (by omega))
    (subsingleton_integralSingularHomology_of_labelledA2Cells F e 5 (by omega))

end SphereSixComplex

end

end
