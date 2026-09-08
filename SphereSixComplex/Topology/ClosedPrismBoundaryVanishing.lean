module

public import SphereSixComplex.Topology.ClosedPrismRelativeBoundary
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex

public theorem closedPrism_relative_boundary_eq_zero
    (S T : ShortComplex (ChainComplex AddCommGrpCat.{0} ℕ))
    (hS : S.ShortExact) (hT : T.ShortExact)
    {f₁ : S.X₁ ⟶ T.X₁} {f₂ : S.X₂ ⟶ T.X₂} {f₃ : S.X₃ ⟶ T.X₃}
    (H₁ : Homotopy f₁ f₁) (H₂ : Homotopy f₂ f₂) (H₃ : Homotopy f₃ f₃)
    (h₁ : ∀ p q, S.f.f p ≫ H₂.hom p q = H₁.hom p q ≫ T.f.f q)
    (h₂ : ∀ p q, S.g.f p ≫ H₃.hom p q = H₂.hom p q ≫ T.g.f q)
    (n : ℕ) (hzero : closedPrismHomology H₁ n = 0) :
    closedPrismHomology H₃ (n + 1) ≫ hT.δ (n + 3) (n + 2) rfl = 0 := by
  have := hS.epi_g
  have := hS.mono_f
  apply (cancel_epi (S.X₃.homologyπ (n + 2))).mp
  ext z
  obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective (S.g.f (n + 2))).mp inferInstance
    (S.X₃.iCycles (n + 2) z)
  have hbcycle : (S.g.f (n + 1)) (S.X₂.d (n + 2) (n + 1) b) = 0 := by
    have hc := congrArg (fun f ↦ f b) (S.g.comm (n + 2) (n + 1))
    simp only [ConcreteCategory.comp_apply] at hc
    rw [← hc, hb]
    exact congrArg (fun f ↦ f z) (S.X₃.iCycles_d (n + 2) (n + 1))
  obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff
    (S.map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) (n + 1)))).mp
      (hS.map (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) (n + 1))).exact
        (S.X₂.d (n + 2) (n + 1) b) hbcycle
  change S.X₁.X (n + 1) at a
  change (S.f.f (n + 1)) a = S.X₂.d (n + 2) (n + 1) b at ha
  have hac : S.X₁.d (n + 1) n a = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (S.f.f n)).mp inferInstance
    have hc := congrArg (fun f ↦ f a) (S.f.comm (n + 1) n)
    simp only [ConcreteCategory.comp_apply] at hc
    rw [← hc, ha, map_zero]
    exact congrArg (fun f ↦ f b) (S.X₂.d_comp_d (n + 2) (n + 1) n)
  have hz₃ : AddCommGrpCat.asHom (S.X₃.iCycles (n + 2) z) ≫
      S.X₃.d (n + 2) (n + 1) = 0 := by
    apply AddCommGrpCat.int_hom_ext
    simp only [ConcreteCategory.comp_apply]
    simp

    exact congrArg (fun f ↦ f z) (S.X₃.iCycles_d (n + 2) (n + 1))
  have h := closedPrism_relative_boundary_on_cycle S T hT H₁ H₂ H₃ h₁ h₂ n
    (AddCommGrpCat.asHom (S.X₃.iCycles (n + 2) z)) hz₃
    (AddCommGrpCat.asHom b) (by apply AddCommGrpCat.int_hom_ext; simpa using hb)
    (AddCommGrpCat.asHom a) (by apply AddCommGrpCat.int_hom_ext; simpa using ha)
    (by apply AddCommGrpCat.int_hom_ext; simpa using hac)
  simp only [hzero, comp_zero, neg_zero] at h
  have hc : S.X₃.liftCycles (AddCommGrpCat.asHom (S.X₃.iCycles (n + 2) z))
      (n + 1) (by simp) hz₃ = AddCommGrpCat.asHom z := by
    apply (cancel_mono (S.X₃.iCycles (n + 2))).mp
    rw [liftCycles_i]
    apply AddCommGrpCat.int_hom_ext
    simp
  rw [hc] at h
  simpa using congrArg (fun f ↦ f (1 : ℤ)) h

end SphereSixComplex
