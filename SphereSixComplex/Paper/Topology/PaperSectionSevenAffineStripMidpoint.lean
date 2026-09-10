module
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandTrivialization
@[expose] public section
namespace SphereSixComplex.Geometry.PaperAnalyticData
public noncomputable def sectionSevenAffineStripMidpoint : sectionSevenAffineVerticalStrip :=
  ⟨(2 : ℂ)⁻¹, by
    change (1 / 3 : ℝ) < ((2 : ℂ)⁻¹).re ∧ ((2 : ℂ)⁻¹).re < 2 / 3
    norm_num⟩

end SphereSixComplex.Geometry.PaperAnalyticData
