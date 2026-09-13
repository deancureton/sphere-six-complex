module

public import Mathlib.Algebra.Exact.Basic

@[expose] public section

namespace AddMonoidHom

public theorem eq_zero_of_exact_of_boundary_generator
    {A B C D E : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E]
    (i : A →+ B) (p : B →+ C) (q : C →+ D) (f : B →+ E)
    (hi : Function.Exact i p) (hp : Function.Exact p q)
    (hfi : ∀ a, f (i a) = 0) (z : B) (hfz : f z = 0)
    (hz : ∀ c, q c = 0 → ∃ n : ℤ, c = n • p z) : f = 0 := by
  ext x
  obtain ⟨n, hn⟩ := hz (p x) (hp.apply_apply_eq_zero x)
  have hx : p (x - n • z) = 0 := by rw [map_sub, map_zsmul, hn, sub_self]
  obtain ⟨a, ha⟩ := (hi _).mp hx
  have h := hfi a
  rw [ha, map_sub, map_zsmul, hfz, zsmul_zero, sub_zero] at h
  exact h

end AddMonoidHom
