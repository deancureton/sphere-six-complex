module

public import DifferentialGeometry.Topology.Homology.Algebra.CokernelHomotopy
public import DifferentialGeometry.Topology.Homology.Algebra.LocallyNilpotent
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Ring k]
  {A K : ChainComplex (ModuleCat.{v} k) ℕ} (i : A ⟶ K)


theorem quasiIso_of_isZero_cokernel_homology [Mono i]
    (hQ : ∀ n, IsZero ((cokernel i).homology n)) :
    _root_.QuasiIso i := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
    mono_f := inferInstanceAs (Mono i)
    epi_g := inferInstanceAs (Epi (cokernel.π i)) }
  rw [_root_.quasiIso_iff]
  intro n
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (_root_.HomologicalComplex.homologyMap i n) :=
    (hS.homology_exact₁ (n + 1) n rfl).mono_g ((hQ (n + 1)).eq_zero_of_src _)
  have : Epi (_root_.HomologicalComplex.homologyMap i n) :=
    (hS.homology_exact₂ n).epi_f ((hQ n).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

variable (a : A ⟶ A) (b : End K) (hab : i ≫ b = a ≫ i)


theorem cokernel_π_endomorphism_pow (N : ℕ) :
    cokernel.π i ≫ (End.of (cokernelEndomorphism i a b hab) ^ N) =
      (b ^ N) ≫ cokernel.π i := by
  induction N with
  | zero => simp
  | succ N hN =>
    rw [pow_succ, End.mul_def, ← Category.assoc, cokernel_π_endomorphism,
      Category.assoc, hN, ← Category.assoc, ← End.mul_def, ← pow_succ]

theorem cokernelEndomorphism_locallyNilpotent
    (henter : ∀ n, ∀ x : K.X n, ∃ N : ℕ,
      ((b ^ N).f n) x ∈ LinearMap.range (i.f n).hom) :
    ∀ n, ∀ x : (cokernel i).X n, ∃ N : ℕ,
      ((End.of (cokernelEndomorphism i a b hab) ^ N).f n) x = 0 := by
  intro n x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective ((cokernel.π i).f n)).mp inferInstance x
  obtain ⟨N, z, hz⟩ := henter n y
  refine ⟨N, ?_⟩
  have hh := ConcreteCategory.congr_hom
    (_root_.HomologicalComplex.congr_hom (cokernel_π_endomorphism_pow i a b hab N) n) y
  change ((End.of (cokernelEndomorphism i a b hab) ^ N).f n) ((cokernel.π i).f n y) =
    (cokernel.π i).f n (((b ^ N).f n) y) at hh
  rw [← hz] at hh
  have hz0 := ConcreteCategory.congr_hom
    (_root_.HomologicalComplex.congr_hom (cokernel.condition i) n) z
  exact hh.trans hz0

include hab in
theorem quasiIso_of_eventually_in_image [Mono i]
    (H : Homotopy b (𝟙 K)) (hA : ∀ n : ℕ, A.X n ⟶ A.X (n + 1))
    (hcompat : ∀ n, i.f n ≫ H.hom n (n + 1) = hA n ≫ i.f (n + 1))
    (henter : ∀ n, ∀ x : K.X n, ∃ N : ℕ,
      ((b ^ N).f n) x ∈ LinearMap.range (i.f n).hom) :
    _root_.QuasiIso i := by
  apply quasiIso_of_isZero_cokernel_homology i
  exact isZero_homology_of_locallyNilpotent (cokernel i)
    (End.of (cokernelEndomorphism i a b hab)) (cokernelHomotopy i a b hab H hA hcompat)
    (cokernelEndomorphism_locallyNilpotent i a b hab henter)

end DifferentialGeometry.HomologicalComplex
