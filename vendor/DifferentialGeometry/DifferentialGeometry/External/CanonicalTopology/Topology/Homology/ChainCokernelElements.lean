module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-! # Concrete representatives in the original chain-complex cokernel -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace DifferentialGeometry.Topology

variable {R : Type u} [Ring R] {K L K' L' : ChainComplex (ModuleCat.{v} R) ℕ}

/-- Every element of the ORIGINAL chain-complex cokernel is represented
by an original target chain in the same degree. -/
theorem chainCokernelπ_surjective (f : K ⟶ L) (n : ℕ) :
    Function.Surjective ((cokernel.π f).f n) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- A chain projects to zero exactly when it is the image of an original
source chain. This follows from exactness of the actual cokernel sequence. -/
theorem chainCokernelπ_eq_zero_iff (f : K ⟶ L) (n : ℕ) (c : L.X n) :
    (cokernel.π f).f n c = 0 ↔ ∃ b : K.X n, f.f n b = c := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f)
  have hSn := hS.map (eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n)
  constructor
  · exact (ShortComplex.moduleCat_exact_iff _).mp hSn c
  · rintro ⟨b, rfl⟩
    exact congrArg (fun k : K ⟶ cokernel f => k.f n b) (cokernel.condition f)

/-- Equality in the SAME cokernel is equality modulo the actual image. -/
theorem chainCokernelπ_eq_iff (f : K ⟶ L) (n : ℕ) (c d : L.X n) :
    (cokernel.π f).f n c = (cokernel.π f).f n d ↔ ∃ b : K.X n, f.f n b = c - d := by
  rw [← sub_eq_zero, ← map_sub, chainCokernelπ_eq_zero_iff]

/-- A map of the original cokernels acts by the original map on the
same representative chain. -/
theorem chainCokernelMap_π (f : K ⟶ L) (g : K' ⟶ L') (p : K ⟶ K') (q : L ⟶ L')
    (h : f ≫ q = p ≫ g) (n : ℕ) (c : L.X n) :
    (cokernel.map f g p q h).f n ((cokernel.π f).f n c) = (cokernel.π g).f n (q.f n c) :=
  congrArg (fun k : L ⟶ cokernel g => k.f n c) (cokernel.π_desc f _ _)

/-- An original cokernel map is an isomorphism when actual image
membership is reflected and every original target representative lifts
modulo the actual target image. -/
theorem isIso_chainCokernelMap_of_representatives (f : K ⟶ L) (g : K' ⟶ L')
    (p : K ⟶ K') (q : L ⟶ L') (h : f ≫ q = p ≫ g)
    (hinj : ∀ n, ∀ c : L.X n, ∀ b : K'.X n, g.f n b = q.f n c →
      ∃ a : K.X n, f.f n a = c)
    (hsurj : ∀ n, ∀ d : L'.X n, ∃ c : L.X n, ∃ b : K'.X n, g.f n b = d - q.f n c) :
    IsIso (cokernel.map f g p q h) := by
  have hcomp (n : ℕ) : IsIso ((cokernel.map f g p q h).f n) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · apply (injective_iff_map_eq_zero ((cokernel.map f g p q h).f n).hom).mpr
      intro z hz
      obtain ⟨c, rfl⟩ := chainCokernelπ_surjective f n z
      change (cokernel.map f g p q h).f n ((cokernel.π f).f n c) = 0 at hz
      rw [chainCokernelMap_π, chainCokernelπ_eq_zero_iff] at hz
      obtain ⟨b, hb⟩ := hz
      exact (chainCokernelπ_eq_zero_iff f n c).mpr (hinj n c b hb)
    · intro z
      obtain ⟨d, rfl⟩ := chainCokernelπ_surjective g n z
      obtain ⟨c, b, hb⟩ := hsurj n d
      refine ⟨(cokernel.π f).f n c, ?_⟩
      rw [chainCokernelMap_π]
      exact ((chainCokernelπ_eq_iff g n d (q.f n c)).mpr ⟨b, hb⟩).symm
  let := hcomp
  exact HomologicalComplex.Hom.isIso_of_components _

end DifferentialGeometry.Topology
