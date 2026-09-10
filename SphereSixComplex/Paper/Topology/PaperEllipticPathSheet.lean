module

public import SphereSixComplex.Paper.Geometry.PaperCentralEndCover
public import SphereSixComplex.Prerequisites.TriangleGroup.FreeProductTorsion
import all SphereSixComplex.Paper.TriangleGroup.Representation

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open Set Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent

public theorem orderThree_path_stays_entering_sheet (A : PaperAnalyticData)
    {R : ℝ}
    (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) R)
    (Q : C(unitInterval, UpperHalfPlane))
    (hcover : ∀ t, ∃ k : Delta,
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ < R)
    (g : Delta)
    (hg : ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction g • Q 0) : ℂ)‖ < R) :
    ∀ t, ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction g • Q t) : ℂ)‖ < R := by
  have hopen (k : Delta) : IsOpen {t : unitInterval |
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ < R} :=
    isOpen_lt (continuous_norm.comp
      ((continuous_subtype_val.comp orderThreeCayleyHomeomorph.continuous).comp
        ((fuchsianSourceAction_contMDiff k 0).continuous.comp Q.continuous))) continuous_const
  have hnorm (h k : Delta) (t : unitInterval)
      (hh : ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction h • Q t) : ℂ)‖ < R)
      (hk : ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ < R)
      (z : unitInterval) :
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction h • Q z) : ℂ)‖ =
        ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction k • Q z) : ℂ)‖ := by
    have D' := D
    rw [OrderThreeLinearCollarSourceData.eq_def] at D'
    obtain ⟨a, ha⟩ := D'.2 (fuchsianSourceAction h • Q t)
      (fuchsianSourceAction k • Q t) hh hk (h * k⁻¹) (by
        rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
        rw [map_mul, map_inv, mul_smul, inv_smul_smul])
    rw [← show fuchsianSourceAction (h * k⁻¹) •
        (fuchsianSourceAction k • Q z) = fuchsianSourceAction h • Q z by
        rw [map_mul, map_inv, mul_smul, inv_smul_smul], ha]
    exact orderThreeCayleyHomeomorph_norm_inl a _
  have hclopen : IsClopen {t : unitInterval |
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction g • Q t) : ℂ)‖ < R} := by
    refine ⟨?_, hopen g⟩
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨h, hh⟩ := hcover z
    apply Filter.mem_of_superset ((hopen h).mem_nhds hh)
    intro y hyh hyg
    apply hz
    change ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction g • Q z) : ℂ)‖ < R
    rw [hnorm g h y hyg hyh z]
    exact hh
  have heq := hclopen.eq_univ ⟨0, hg⟩
  intro t
  have ht : t ∈ ({t : unitInterval |
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction g • Q t) : ℂ)‖ < R} : Set _) := by
    rw [heq]
    exact mem_univ t
  exact ht

public theorem orderFour_path_stays_entering_sheet (A : PaperAnalyticData)
    {R : ℝ}
    (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) R)
    (Q : C(unitInterval, UpperHalfPlane))
    (hcover : ∀ t, ∃ k : Delta,
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ < R)
    (g : Delta)
    (hg : ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • Q 0) : ℂ)‖ < R) :
    ∀ t, ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • Q t) : ℂ)‖ < R := by
  have hopen (k : Delta) : IsOpen {t : unitInterval |
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ < R} :=
    isOpen_lt (continuous_norm.comp
      ((continuous_subtype_val.comp orderFourCayleyHomeomorph.continuous).comp
        ((fuchsianSourceAction_contMDiff k 0).continuous.comp Q.continuous))) continuous_const
  have hnorm (h k : Delta) (t : unitInterval)
      (hh : ‖(orderFourCayleyHomeomorph (fuchsianSourceAction h • Q t) : ℂ)‖ < R)
      (hk : ‖(orderFourCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ < R)
      (z : unitInterval) :
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction h • Q z) : ℂ)‖ =
        ‖(orderFourCayleyHomeomorph (fuchsianSourceAction k • Q z) : ℂ)‖ := by
    have D' := D
    rw [OrderFourLinearCollarSourceData.eq_def] at D'
    obtain ⟨a, ha⟩ := D'.2 (fuchsianSourceAction h • Q t)
      (fuchsianSourceAction k • Q t) hh hk (h * k⁻¹) (by
        rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
        rw [map_mul, map_inv, mul_smul, inv_smul_smul])
    rw [← show fuchsianSourceAction (h * k⁻¹) •
        (fuchsianSourceAction k • Q z) = fuchsianSourceAction h • Q z by
        rw [map_mul, map_inv, mul_smul, inv_smul_smul], ha]
    exact orderFourCayleyHomeomorph_norm_inr a _
  have hclopen : IsClopen {t : unitInterval |
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • Q t) : ℂ)‖ < R} := by
    refine ⟨?_, hopen g⟩
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨h, hh⟩ := hcover z
    apply Filter.mem_of_superset ((hopen h).mem_nhds hh)
    intro y hyh hyg
    apply hz
    change ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • Q z) : ℂ)‖ < R
    rw [hnorm g h y hyg hyh z]
    exact hh
  have heq := hclopen.eq_univ ⟨0, hg⟩
  intro t
  have ht : t ∈ ({t : unitInterval |
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • Q t) : ℂ)‖ < R} : Set _) := by
    rw [heq]
    exact mem_univ t
  exact ht

public theorem orderThree_fixes_of_generator_conjugate_in_factor
    (g : Delta) (h : ∃ a : CyclicThree, g * g₁ * g⁻¹ = Monoid.Coprod.inl a) :
    fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint := by
  obtain ⟨a, ha⟩ := h
  have hfix : fuchsianSourceAction (g * g₁ * g⁻¹) • fuchsianOneFixedPoint =
      fuchsianOneFixedPoint := by
    rw [ha]
    exact (establishedFuchsianOneStabilizerExact _).mpr ⟨a, rfl⟩
  rw [SphereSixComplex.TriangleGroup.g₁.eq_def] at hfix
  exact ((SphereSixComplex.TriangleGroup.FreeProductTorsion.fixed_by_conjugate_inl_iff
    g (Multiplicative.ofAdd (1 : ZMod 3)) (by decide) fuchsianOneFixedPoint).mp hfix).symm

public theorem orderFour_fixes_of_generator_conjugate_in_factor
    (g : Delta) (h : ∃ a : CyclicFour, g * g₂ * g⁻¹ = Monoid.Coprod.inr a) :
    fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint := by
  obtain ⟨a, ha⟩ := h
  have hfix : fuchsianSourceAction (g * g₂ * g⁻¹) • fuchsianTwoFixedPoint =
      fuchsianTwoFixedPoint := by
    rw [ha]
    exact (establishedFuchsianTwoStabilizerExact _).mpr ⟨a, rfl⟩
  rw [SphereSixComplex.TriangleGroup.g₂.eq_def] at hfix
  exact ((SphereSixComplex.TriangleGroup.FreeProductTorsion.fixed_by_conjugate_inr_iff
    g (Multiplicative.ofAdd (1 : ZMod 4)) (by decide) fuchsianTwoFixedPoint).mp hfix).symm

public theorem orderThree_generator_path_stays_standard_collar (A : PaperAnalyticData)
    {R : ℝ}
    (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) R)
    (z : UpperHalfPlane) (Q : Path z (fuchsianSourceAction g₁ • z))
    (hcover : ∀ t, ∃ k : Delta,
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ < R) :
    ∀ t, ‖(orderThreeCayleyHomeomorph (Q t) : ℂ)‖ < R := by
  obtain ⟨g, hg⟩ := hcover 0
  have hstay := A.orderThree_path_stays_entering_sheet D Q.toContinuousMap hcover g hg
  have D' := D
  rw [OrderThreeLinearCollarSourceData.eq_def] at D'
  obtain ⟨a, ha⟩ := D'.2 (fuchsianSourceAction g • (fuchsianSourceAction g₁ • z))
    (fuchsianSourceAction g • z)
    (by
      have ht := hstay 1
      change ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction g • Q 1) : ℂ)‖ < R at ht
      simpa only [Q.target] using ht)
    (by simpa only [Q.source] using hg) (g * g₁ * g⁻¹) (by
      rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
      simp only [map_mul, map_inv, mul_smul, inv_smul_smul])
  have hfix := orderThree_fixes_of_generator_conjugate_in_factor g ⟨a, ha⟩
  obtain ⟨b, hb⟩ := (establishedFuchsianOneStabilizerExact g).mp hfix
  intro t
  have ht := hstay t
  rw [hb, orderThreeCayleyHomeomorph_norm_inl] at ht
  exact ht

public theorem orderFour_generator_path_stays_standard_collar (A : PaperAnalyticData)
    {R : ℝ}
    (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) R)
    (z : UpperHalfPlane) (Q : Path z (fuchsianSourceAction g₂ • z))
    (hcover : ∀ t, ∃ k : Delta,
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ < R) :
    ∀ t, ‖(orderFourCayleyHomeomorph (Q t) : ℂ)‖ < R := by
  obtain ⟨g, hg⟩ := hcover 0
  have hstay := A.orderFour_path_stays_entering_sheet D Q.toContinuousMap hcover g hg
  have D' := D
  rw [OrderFourLinearCollarSourceData.eq_def] at D'
  obtain ⟨a, ha⟩ := D'.2 (fuchsianSourceAction g • (fuchsianSourceAction g₂ • z))
    (fuchsianSourceAction g • z)
    (by
      have ht := hstay 1
      change ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • Q 1) : ℂ)‖ < R at ht
      simpa only [Q.target] using ht)
    (by simpa only [Q.source] using hg) (g * g₂ * g⁻¹) (by
      rw [A.modular.modularParameter.toTriangleUniformization_sourceAction]
      simp only [map_mul, map_inv, mul_smul, inv_smul_smul])
  have hfix := orderFour_fixes_of_generator_conjugate_in_factor g ⟨a, ha⟩
  obtain ⟨b, hb⟩ := (establishedFuchsianTwoStabilizerExact g).mp hfix
  intro t
  have ht := hstay t
  rw [hb, orderFourCayleyHomeomorph_norm_inr] at ht
  exact ht

end SphereSixComplex.Geometry.PaperAnalyticData
