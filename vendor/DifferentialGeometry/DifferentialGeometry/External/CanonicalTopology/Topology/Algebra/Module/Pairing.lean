module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Tactic.Conv

@[expose] public section

universe v w

namespace DifferentialGeometry

theorem additive_pairing_bijective_at_generator
    {A : Type v} {C : Type w} [AddCommGroup C] (B : A → C →+ ℤ)
    (e : C ≃+ ℤ) (c : C) (hc : Function.Bijective (fun α => B α c)) :
    Function.Bijective (fun α => B α (e.symm 1)) := by
  have hec : c = e c • e.symm 1 := by
    apply e.injective
    rw [map_zsmul, e.apply_symm_apply]
    simp only [zsmul_eq_mul, mul_one, Int.cast_id]
  have hpair (α : A) : B α c = e c * B α (e.symm 1) := by
    conv_lhs => rw [hec]
    rw [map_zsmul]
    rfl
  obtain ⟨α, hα⟩ := hc.surjective 1
  have hu : IsUnit (e c) := IsUnit.of_mul_eq_one (B α (e.symm 1))
    ((hpair α).symm.trans hα)
  have hm := IsUnit.isUnit_iff_mulLeft_bijective.mp hu
  apply (Function.Bijective.of_comp_iff' hm (fun β => B β (e.symm 1))).mp
  have hfun : (e c * ·) ∘ (fun β => B β (e.symm 1)) = (fun β => B β c) := by
    funext β
    exact (hpair β).symm
  rw [hfun]
  exact hc

theorem additive_pairing_bijective_iff_isUnit
    {A : Type v} {C : Type w} [AddCommGroup C] (B : A → C →+ ℤ)
    (e : C ≃+ ℤ) (h : Function.Bijective (fun α => B α (e.symm 1))) (c : C) :
    Function.Bijective (fun α => B α c) ↔ IsUnit (e c) := by
  have hec : c = e c • e.symm 1 := by
    apply e.injective
    rw [map_zsmul, e.apply_symm_apply]
    simp only [zsmul_eq_mul, mul_one, Int.cast_id]
  have hfun : (fun α => B α c) = (e c * ·) ∘ (fun α => B α (e.symm 1)) := by
    funext α
    conv_lhs => rw [hec]
    rw [map_zsmul]
    rfl
  rw [hfun]
  exact (Function.Bijective.of_comp_iff (e c * ·) h).trans
    IsUnit.isUnit_iff_mulLeft_bijective.symm

end DifferentialGeometry
