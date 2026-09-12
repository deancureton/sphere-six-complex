module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Prod

@[expose] public section

namespace AddMonoidHom

public theorem prod_surjective_of_surjective_of_ker {G H K : Type*}
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    (p : G →+ H) (q : G →+ K) (hp : Function.Surjective p)
    (hq : ∀ k, ∃ x, p x = 0 ∧ q x = k) :
    Function.Surjective (q.prod p) := by
  rintro ⟨k, h⟩
  obtain ⟨x, hx⟩ := hp h
  obtain ⟨y, hy, hyq⟩ := hq (k - q x)
  exact ⟨y + x, by simp [map_add, hy, hyq, hx]⟩

end AddMonoidHom
