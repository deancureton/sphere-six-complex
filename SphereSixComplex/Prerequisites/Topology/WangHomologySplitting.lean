module

public import SphereSixComplex.Prerequisites.Topology.WangHomologyPresentation
public import Mathlib.Algebra.Module.Projective

@[expose] public section
noncomputable section
namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]


end WangHomologyPresentation

namespace CircleMappingTorusHomologyBases


variable {E C : Type*} [AddCommGroup E] [AddCommGroup C]

public theorem map_range_eq_of_conjugates (e : E ≃ₗ[ℤ] C) (d : E →ₗ[ℤ] E)
    (D : C →ₗ[ℤ] C) (h : e.toLinearMap.comp d = D.comp e.toLinearMap) :
    (LinearMap.range d).map e.toLinearMap = LinearMap.range D := by
  rw [← LinearMap.range_comp, h, LinearMap.range_comp]
  simp

public theorem map_ker_eq_of_conjugates (e : E ≃ₗ[ℤ] C) (d : E →ₗ[ℤ] E)
    (D : C →ₗ[ℤ] C) (h : e.toLinearMap.comp d = D.comp e.toLinearMap) :
    (LinearMap.ker d).map e.toLinearMap = LinearMap.ker D := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hx' := LinearMap.mem_ker.mp hx
    have hpoint := DFunLike.congr_fun h x
    simp only [LinearMap.coe_comp, Function.comp_apply] at hpoint
    rw [← hpoint, hx', map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply LinearMap.mem_ker.mpr
    apply e.injective
    have hpoint := DFunLike.congr_fun h (e.symm y)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hpoint
    rw [e.map_zero]
    calc
      e.toLinearMap (d (e.symm y)) = D (e.toLinearMap (e.symm y)) := hpoint
      _ = D y := congrArg D (e.apply_symm_apply y)
      _ = 0 := LinearMap.mem_ker.mp hy

public theorem circleDifference_conjugacy
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (k : ℕ)
    (e : IntegralSingularHomology k F ≃ₗ[ℤ] C) (monodromy : C →ₗ[ℤ] C)
    (hmonodromy : ∀ x, e (integralSingularHomologyMap k phi x) = monodromy (e x)) :
    e.toLinearMap.comp (circleMonodromyDifference phi k).toIntLinearMap =
      (monodromy - LinearMap.id).comp e.toLinearMap := by
  ext x
  simp [circleMonodromyDifference, hmonodromy]

public noncomputable def coinvariantsEquivOfConjugacy (e : E ≃ₗ[ℤ] C)
    (d : E →ₗ[ℤ] E) (D : C →ₗ[ℤ] C)
    (h : e.toLinearMap.comp d = D.comp e.toLinearMap) :
    (E ⧸ LinearMap.range d) ≃ₗ[ℤ] C ⧸ LinearMap.range D :=
  Submodule.Quotient.equiv _ _ e (map_range_eq_of_conjugates e d D h)

public def invariantsEquivOfConjugacy (e : E ≃ₗ[ℤ] C)
    (d : E →ₗ[ℤ] E) (D : C →ₗ[ℤ] C)
    (h : e.toLinearMap.comp d = D.comp e.toLinearMap) :
    LinearMap.ker d ≃ₗ[ℤ] LinearMap.ker D :=
  e.ofSubmodules _ _ (map_ker_eq_of_conjugates e d D h)

end CircleMappingTorusHomologyBases
end SphereSixComplex
end
end
