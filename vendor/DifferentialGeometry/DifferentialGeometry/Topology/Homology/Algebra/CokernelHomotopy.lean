module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Ring k]
  {A K : ChainComplex (ModuleCat.{v} k) ℕ} (i : A ⟶ K)

def cokernelDescAt (n : ℕ) {M : ModuleCat.{v} k} (φ : K.X n ⟶ M) (hφ : i.f n ≫ φ = 0) :
    (cokernel i).X n ⟶ M :=
  (PreservesCokernel.iso (_root_.HomologicalComplex.eval _ _ n) i).hom ≫
    cokernel.desc (i.f n) φ hφ


@[reassoc (attr := simp)]
theorem cokernel_π_descAt (n : ℕ) {M : ModuleCat.{v} k} (φ : K.X n ⟶ M) (hφ : i.f n ≫ φ = 0) :
    (cokernel.π i).f n ≫ cokernelDescAt i n φ hφ = φ := by
  exact (PreservesCokernel.π_iso_hom_assoc (_root_.HomologicalComplex.eval _ _ n) i
    (cokernel.desc ((_root_.HomologicalComplex.eval _ _ n).map i) φ hφ)).trans
      (cokernel.π_desc _ _ _)

variable (a : A ⟶ A) (b : K ⟶ K) (hab : i ≫ b = a ≫ i)


def cokernelEndomorphism : cokernel i ⟶ cokernel i := cokernel.map i i a b hab


@[reassoc (attr := simp)]
theorem cokernel_π_endomorphism :
    cokernel.π i ≫ cokernelEndomorphism i a b hab = b ≫ cokernel.π i :=
  cokernel.π_desc _ _ _

variable (H : Homotopy b (𝟙 K))
  (hA : ∀ n : ℕ, A.X n ⟶ A.X (n + 1))
  (hcompat : ∀ n, i.f n ≫ H.hom n (n + 1) = hA n ≫ i.f (n + 1))

include hcompat in
theorem desc_condition (n : ℕ) :
    i.f n ≫ (H.hom n (n + 1) ≫ (cokernel.π i).f (n + 1)) = 0 := by
  rw [← Category.assoc, hcompat, Category.assoc]
  have h := _root_.HomologicalComplex.congr_hom (cokernel.condition i) (n + 1)
  simp only [_root_.HomologicalComplex.comp_f, _root_.HomologicalComplex.zero_f_apply] at h
  rw [h, comp_zero]

def descHom (n : ℕ) : (cokernel i).X n ⟶ (cokernel i).X (n + 1) :=
  cokernelDescAt i n (H.hom n (n + 1) ≫ (cokernel.π i).f (n + 1))
    (desc_condition i b H hA hcompat n)

private theorem projection_descHom (n : ℕ) :
    (cokernel.π i).f n ≫ descHom i b H hA hcompat n =
      H.hom n (n + 1) ≫ (cokernel.π i).f (n + 1) :=
  cokernel_π_descAt _ _ _ _

def cokernelHomotopy : Homotopy (cokernelEndomorphism i a b hab) (𝟙 (cokernel i)) where
  hom n m := if h : n + 1 = m then
    descHom i b H hA hcompat n ≫ eqToHom (congrArg (cokernel i).X h) else 0
  zero n m hnm := by
    change ¬ n + 1 = m at hnm
    exact dite_eq_right hnm
  comm n := by
    have hπ : (cokernel.π i).f n ≫ (cokernelEndomorphism i a b hab).f n =
        b.f n ≫ (cokernel.π i).f n :=
      _root_.HomologicalComplex.congr_hom (cokernel_π_endomorphism i a b hab) n
    have hh := H.comm n
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hh ⊢
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        _root_.HomologicalComplex.id_f, zero_add] at hh ⊢
      apply (cancel_epi ((cokernel.π i).f 0)).mp
      rw [hπ, Preadditive.comp_add, Category.comp_id, ← Category.assoc,
        projection_descHom, Category.assoc, (cokernel.π i).comm, ← Category.assoc]
      exact congrArg (fun f ↦ f ≫ (cokernel.π i).f 0) hh |>.trans (by simp)
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hh ⊢
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        _root_.HomologicalComplex.id_f] at hh ⊢
      apply (cancel_epi ((cokernel.π i).f (n + 1))).mp
      rw [hπ]
      simp only [Preadditive.comp_add, Category.comp_id]
      rw [← Category.assoc ((cokernel.π i).f (n + 1)), (cokernel.π i).comm]
      rw [Category.assoc, projection_descHom]
      rw [← Category.assoc ((cokernel.π i).f (n + 1)), projection_descHom,
        Category.assoc, (cokernel.π i).comm]
      simpa only [Preadditive.add_comp, Category.assoc, Category.id_comp] using
        congrArg (fun f ↦ f ≫ (cokernel.π i).f (n + 1)) hh

end DifferentialGeometry.HomologicalComplex
