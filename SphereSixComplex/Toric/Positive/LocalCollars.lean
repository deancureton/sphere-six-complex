module

public import SphereSixComplex.Prerequisites.Topology.Collar.HalfSpace
public import SphereSixComplex.Prerequisites.Topology.Collar.OrthantHalfSpace
public import SphereSixComplex.Toric.Positive.QuadrantManifold

@[expose] public section

noncomputable section

open Function Set Topology
open scoped NNReal

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

public def carrierPositiveHalfSpaceChart (a : ChartIndex) :
    (Fin 2 → ℝ) × ℝ≥0 → carrierPositivePart :=
  carrierPositiveChart a ∘ orthantThreeHalfSpaceHomeomorph.symm

public theorem carrierPositiveHalfSpaceChart_isOpenEmbedding (a : ChartIndex) :
    IsOpenEmbedding (carrierPositiveHalfSpaceChart a) :=
  (carrierPositiveChart_isOpenEmbedding a).comp orthantThreeHalfSpaceHomeomorph.symm.isOpenEmbedding

public theorem carrierPositiveHalfSpaceChart_height_zero (a : ChartIndex)
    (p : (Fin 2 → ℝ) × ℝ≥0) :
    carrierHeight (carrierPositiveHalfSpaceChart a p).1 = 0 ↔ p.2 = 0 := by
  let u := orthantThreeHalfSpaceHomeomorph.symm p
  have hp : orthantThreeHalfSpaceHomeomorph u = p :=
    orthantThreeHalfSpaceHomeomorph.apply_symm_apply p
  rw [← hp, orthantThreeHalfSpaceHomeomorph_boundary]
  simp only [carrierPositiveHalfSpaceChart, Function.comp_apply, Homeomorph.symm_apply_apply]
  change carrierHeight (inclusion a (fun i ↦ (u.1 i : ℂ))) = 0 ↔ ∃ i, u.1 i = 0
  rw [carrierHeight_inclusion]
  simp only [rawHeight, mul_eq_zero, Complex.ofReal_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> tauto

public def localPositiveInclusion (r : ℝ) : constructedLocalPositivePart r → carrierPositivePart :=
  Subtype.val ∘ (positiveSublevelHomeomorph r).symm

public theorem localPositiveInclusion_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (localPositiveInclusion r) :=
  (positiveSublevel r).2.isOpenEmbedding_subtypeVal.comp
    (positiveSublevelHomeomorph r).symm.isOpenEmbedding

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
