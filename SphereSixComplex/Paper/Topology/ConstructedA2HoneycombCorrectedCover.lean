module

public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCorrectedQuotientProof

@[expose] public section
noncomputable section
open Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
open SphereSixComplex.Geometry.CuspCombinatorics

public theorem iUnion_constructedA2CorrectedPlaneCell :
    ⋃ v, constructedA2CorrectedPlaneCell v = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let a : ℤ := ⌊(x 0 - 2 * x 1) / 2⌋
  let b : ℤ := ⌊(x 0 + x 1) / 2⌋
  let s := (x 0 - 2 * x 1) / 2 - a
  let t := (x 0 + x 1) / 2 - b
  have hs0 : 0 ≤ s := sub_nonneg.mpr (Int.floor_le _)
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Int.floor_le _)
  have hs1 : s ≤ 1 := le_of_lt (Int.fract_lt_one _)
  have ht1 : t ≤ 1 := le_of_lt (Int.fract_lt_one _)
  have hm (i j : ℤ)
      (h0 : |s + 2 * t - (i + 2 * j : ℤ)| ≤ 1)
      (h1 : |-s + t - (-i + j : ℤ)| ≤ 1)
      (hd : |2 * s + t - (2 * i + j : ℤ)| ≤ 1) :
      x ∈ ⋃ v, constructedA2CorrectedPlaneCell v := by
    refine Set.mem_iUnion.mpr ⟨![a + i, b + j], ?_⟩
    rcases abs_le.mp h0 with ⟨h0l, h0r⟩
    rcases abs_le.mp h1 with ⟨h1l, h1r⟩
    rcases abs_le.mp hd with ⟨hdl, hdr⟩
    simp only [constructedA2CorrectedPlaneCell, constructedA2CorrectedPlaneCenter,
      Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat, Int.cast_neg] at *
    dsimp [s, t] at *
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  by_cases hst : t ≤ s
  · by_cases hlo : 2 * s + t ≤ 1
    · apply hm 0 0 <;> norm_num <;> rw [abs_le] <;> constructor <;> linarith
    · by_cases hhi : s + 2 * t ≤ 2
      · apply hm 1 0 <;> norm_num <;> rw [abs_le] <;> constructor <;> linarith
      · apply hm 1 1 <;> norm_num <;> rw [abs_le] <;> constructor <;> linarith
  · by_cases hlo : s + 2 * t ≤ 1
    · apply hm 0 0 <;> norm_num <;> rw [abs_le] <;> constructor <;> linarith
    · by_cases hhi : 2 * s + t ≤ 2
      · apply hm 0 1 <;> norm_num <;> rw [abs_le] <;> constructor <;> linarith
      · apply hm 1 1 <;> norm_num <;> rw [abs_le] <;> constructor <;> linarith

public theorem constructedA2CorrectedPlaneCell_isClosed (v : ToricLattice) :
    IsClosed (constructedA2CorrectedPlaneCell v) := by
  exact (isClosed_le ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
    ((isClosed_le ((continuous_apply 1).sub continuous_const).abs continuous_const).inter
      (isClosed_le (((continuous_apply 0).sub (continuous_apply 1)).sub
        continuous_const).abs continuous_const))

public theorem constructedA2CorrectedPlaneCells_locallyFinite :
    LocallyFinite constructedA2CorrectedPlaneCell := by
  intro x
  let U : Set (Fin 2 → ℝ) := {y | |y 0 - x 0| < 1 ∧ |y 1 - x 1| < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
      (isOpen_lt ((continuous_apply 1).sub continuous_const).abs continuous_const)
  have hxU : x ∈ U := by simp [U]
  let a : ℤ := round ((x 0 - 2 * x 1) / 2)
  let b : ℤ := round ((x 0 + x 1) / 2)
  let lo : ToricLattice := ![a - 4, b - 4]
  let hi : ToricLattice := ![a + 4, b + 4]
  refine ⟨U, hUopen.mem_nhds hxU, (Set.finite_Icc lo hi).subset ?_⟩
  intro v hv
  obtain ⟨y, hy, hyU⟩ := hv
  have ha := abs_le.mp (abs_sub_round ((x 0 - 2 * x 1) / 2))
  have hb := abs_le.mp (abs_sub_round ((x 0 + x 1) / 2))
  have hy0 := abs_le.mp hy.1
  have hy1 := abs_le.mp hy.2.1
  have hu0 := abs_lt.mp hyU.1
  have hu1 := abs_lt.mp hyU.2
  change -(1 / 2 : ℝ) ≤ (x 0 - 2 * x 1) / 2 - a ∧
    (x 0 - 2 * x 1) / 2 - a ≤ 1 / 2 at ha
  change -(1 / 2 : ℝ) ≤ (x 0 + x 1) / 2 - b ∧
    (x 0 + x 1) / 2 - b ≤ 1 / 2 at hb
  norm_num [constructedA2CorrectedPlaneCenter] at hy0 hy1
  have hal : a - 4 ≤ v 0 := by
    have : ((a - 4 : ℤ) : ℝ) ≤ v 0 := by push_cast; linarith
    exact_mod_cast this
  have hbl : b - 4 ≤ v 1 := by
    have : ((b - 4 : ℤ) : ℝ) ≤ v 1 := by push_cast; linarith
    exact_mod_cast this
  have hau : v 0 ≤ a + 4 := by
    have : (v 0 : ℝ) ≤ (a + 4 : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hbu : v 1 ≤ b + 4 := by
    have : (v 1 : ℝ) ≤ (b + 4 : ℤ) := by push_cast; linarith
    exact_mod_cast this
  constructor
  · intro i
    fin_cases i
    · exact hal
    · exact hbl
  · intro i
    fin_cases i
    · exact hau
    · exact hbu

public def constructedA2CorrectedHoneycombCellData {r : ℝ} (hr : 0 < r) :
    ConstructedHoneycombCellData r where
  planeCell := constructedA2CorrectedPlaneCell
  planeCell_cover := iUnion_constructedA2CorrectedPlaneCell
  planeCell_closed := constructedA2CorrectedPlaneCell_isClosed
  planeCell_locallyFinite := constructedA2CorrectedPlaneCells_locallyFinite
  cellHomeomorph := constructedA2CorrectedFiniteQuotientCellHomeomorph hr
  cellHomeomorph_compatible := constructedA2CorrectedFiniteQuotientCellHomeomorph_compatible hr

public def constructedA2CorrectedHoneycombHomeomorph {r : ℝ} (hr : 0 < r) :
    (Fin 2 → ℝ) ≃ₜ constructedPositiveCentralFiber r :=
  (constructedA2CorrectedHoneycombCellData hr).honeycomb

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
