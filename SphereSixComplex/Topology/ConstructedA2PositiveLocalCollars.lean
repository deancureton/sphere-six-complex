module

public import SphereSixComplex.Topology.LocalHalfSpaceCollars
public import SphereSixComplex.Topology.OrthantHalfSpace
public import SphereSixComplex.Topology.ConstructedA2PositiveQuadrantManifold
public import SphereSixComplex.Topology.BrownCollaringClassicalBoundary
public import Mathlib.Topology.Metrizable.Urysohn

@[expose] public section

noncomputable section

open Function Set Topology
open scoped NNReal

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

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

public theorem constructedPositiveCentralFiber_locallyCollared (r : ℝ) :
    LocallyCollared {q : constructedLocalPositivePart r | constructedModel.t q.1.1 = 0} := by
  intro q hq
  obtain ⟨a, u, hu⟩ := carrierPositiveChart_jointly_surjective (localPositiveInclusion r q)
  let p := orthantThreeHalfSpaceHomeomorph u
  have hp : carrierPositiveHalfSpaceChart a p = localPositiveInclusion r q := by
    simpa [carrierPositiveHalfSpaceChart, p] using hu
  have hp0 : p.2 = 0 := (carrierPositiveHalfSpaceChart_height_zero a p).mp (by
    rw [hp]
    exact hq)
  have hb : ∀ p q', carrierPositiveHalfSpaceChart a p = localPositiveInclusion r q' →
      (constructedModel.t q'.1.1 = 0 ↔ p.2 = 0) := by
    intro p q' he
    rw [← carrierPositiveHalfSpaceChart_height_zero a p, he]
    rfl
  have hxy : carrierPositiveHalfSpaceChart a (p.1, 0) = localPositiveInclusion r q := by
    simpa only [← hp0] using hp
  exact locallyCollared_of_overlapping_halfSpaceEmbedding
    {q : constructedLocalPositivePart r | constructedModel.t q.1.1 = 0}
    (localPositiveInclusion r) (localPositiveInclusion_isOpenEmbedding r)
    (carrierPositiveHalfSpaceChart a) (carrierPositiveHalfSpaceChart_isOpenEmbedding a)
    q p.1 hxy hb

public theorem constructedLocalPositivePart_metrizable (r : ℝ) :
    TopologicalSpace.MetrizableSpace (constructedLocalPositivePart r) := by
  let _ := Established.constructedLocalPositivePart_t2Space r
  let _ := Established.constructedLocalPositivePart_locallyCompactSpace r
  infer_instance

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
