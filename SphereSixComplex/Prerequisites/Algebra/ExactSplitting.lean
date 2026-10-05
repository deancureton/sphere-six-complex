module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

namespace LinearMap
variable {R : Type*} [Ring R] {A B C : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

/-- A projective quotient splits an exact sequence, preserving its inclusion and projection. -/
theorem exists_equiv_prod_of_exact
    (j : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hj : Function.Injective j) (hex : Function.Exact j g)
    (hg : Function.Surjective g) [Module.Projective R C] :
    ∃ e : B ≃ₗ[R] (A × C),
      (∀ a, e (j a) = (a, 0)) ∧ ∀ b, (e b).2 = g b := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  have hgs (c : C) : g (s c) = c := DFunLike.congr_fun hs c
  let f := j.coprod s
  have hgf (p : A × C) : g (f p) = p.2 := by
    change g (j p.1 + s p.2) = p.2
    rw [map_add, hex.apply_apply_eq_zero, hgs, zero_add]
  have hfi : Function.Injective f := by
    intro p q hpq
    have h₂ : p.2 = q.2 := (hgf p).symm.trans ((congrArg g hpq).trans (hgf q))
    apply Prod.ext
    · apply hj
      change j p.1 + s p.2 = j q.1 + s q.2 at hpq
      rw [h₂] at hpq
      exact add_right_cancel hpq
    · exact h₂
  have hfs : Function.Surjective f := by
    intro b
    have hz : g (b - s (g b)) = 0 := by rw [map_sub, hgs, sub_self]
    obtain ⟨a, ha⟩ := (hex _).mp hz
    refine ⟨(a, g b), ?_⟩
    change j a + s (g b) = b
    rw [ha, sub_add_cancel]
  let e := (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).symm
  refine ⟨e, ?_, ?_⟩
  · intro a
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change j a = j a + s 0
    rw [map_zero, add_zero]
  · intro b
    have h := hgf (e b)
    change g (e.symm (e b)) = (e b).2 at h
    rw [e.symm_apply_apply] at h
    exact h.symm
end LinearMap

end
