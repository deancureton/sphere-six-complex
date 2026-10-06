module

public import Mathlib.LinearAlgebra.Orientation

@[expose] public section

namespace DifferentialGeometry

theorem orientation_map_trans
    {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    {E F G : Type*} [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] [AddCommMonoid G] [Module R G]
    {ι : Type*} (A : E ≃ₗ[R] F) (B : F ≃ₗ[R] G) (o : Orientation R E ι) :
    Orientation.map ι (A.trans B) o = Orientation.map ι B (Orientation.map ι A o) := by
  induction o using Module.Ray.ind with
  | h f hf => rfl

end DifferentialGeometry
