module

public import SphereSixComplex.Geometry.PaperCentralCompactCore

/-!
# Elementary compact cores in the twice-punctured affine line

Closed lower bounds on the distances to `0` and `1`, together with an upper norm bound,
give compact subsets of the regular affine coordinate base.  Outside such a core, one of the
three corresponding end inequalities holds.
-/

open Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open Set

/-- The elementary threshold core in the affine line with `0` and `1` removed. -/
@[expose] public def puncturedAffineThresholdCore (delta0 delta1 R : ℝ) :
    Set RegularCoordinateBase :=
  {z | delta0 ≤ ‖(z : ℂ)‖ ∧ delta1 ≤ ‖(z : ℂ) - 1‖ ∧ ‖(z : ℂ)‖ ≤ R}

/-- Positive lower distance thresholds make the elementary affine core compact. -/
public theorem puncturedAffineThresholdCore_isCompact
    {delta0 delta1 R : ℝ} (hdelta0 : 0 < delta0) (hdelta1 : 0 < delta1) :
    IsCompact (puncturedAffineThresholdCore delta0 delta1 R) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have hclosed : IsClosed
      {z : ℂ | delta0 ≤ ‖z‖ ∧ delta1 ≤ ‖z - 1‖ ∧ ‖z‖ ≤ R} :=
    (isClosed_le continuous_const continuous_norm).inter
      ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
        (isClosed_le continuous_norm continuous_const))
  have hcompact : IsCompact
      {z : ℂ | delta0 ≤ ‖z‖ ∧ delta1 ≤ ‖z - 1‖ ∧ ‖z‖ ≤ R} := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed
    intro z hz
    exact mem_closedBall_zero_iff.mpr hz.2.2
  convert hcompact using 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hdelta0.trans_le hz.1)
    have hz1 : z ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp (hdelta1.trans_le hz.2.1))
    refine ⟨⟨z, ?_⟩, hz, rfl⟩
    simp only [RegularCoordinateBase, mem_compl_iff, mem_insert_iff,
      mem_singleton_iff, not_or]
    exact ⟨hz0, hz1⟩

/-- Outside the threshold core, the coordinate lies in one of the three affine ends. -/
public theorem not_mem_puncturedAffineThresholdCore_iff
    {delta0 delta1 R : ℝ} {z : RegularCoordinateBase} :
    z ∉ puncturedAffineThresholdCore delta0 delta1 R ↔
      ‖(z : ℂ)‖ < delta0 ∨ ‖(z : ℂ) - 1‖ < delta1 ∨ R < ‖(z : ℂ)‖ := by
  simp only [puncturedAffineThresholdCore, mem_ofPred_eq, not_and_or, not_le]

public theorem not_mem_puncturedAffineThresholdCore
    {delta0 delta1 R : ℝ} {z : RegularCoordinateBase}
    (hz : z ∉ puncturedAffineThresholdCore delta0 delta1 R) :
    ‖(z : ℂ)‖ < delta0 ∨ ‖(z : ℂ) - 1‖ < delta1 ∨ R < ‖(z : ℂ)‖ :=
  not_mem_puncturedAffineThresholdCore_iff.mp hz

end SphereSixComplex.Geometry.PaperAnalyticData
