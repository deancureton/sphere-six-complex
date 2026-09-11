module

public import SphereSixComplex.Prerequisites.Topology.ClosedHomotopyPrism
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex

variable (S : ShortComplex (ChainComplex AddCommGrpCat ℕ))
  (hS : S.ShortExact) (H : Homotopy (𝟙 S.X₂) 0) (n : ℕ)

public def contractingPrismLift : S.X₁.cycles (n + 1) ⟶ S.X₂.X (n + 2) :=
  S.X₁.iCycles (n + 1) ≫ S.f.f (n + 1) ≫ H.hom (n + 1) (n + 2)

public theorem contractingPrismLift_boundary :
    contractingPrismLift S H n ≫ S.X₂.d (n + 2) (n + 1) =
      S.X₁.iCycles (n + 1) ≫ S.f.f (n + 1) := by
  have h := H.comm (n + 1)
  rw [dNext_eq _ (show ComplexShape.down ℕ |>.Rel (n + 1) n from rfl),
    prevD_eq _ (show ComplexShape.down ℕ |>.Rel (n + 2) (n + 1) from rfl)] at h
  have h' := congrArg (fun f ↦ S.X₁.iCycles (n + 1) ≫ S.f.f (n + 1) ≫ f) h
  simpa only [HomologicalComplex.id_f, HomologicalComplex.zero_f, Category.comp_id,
    Preadditive.comp_add, comp_zero, add_zero, S.f.comm_assoc,
    iCycles_d_assoc, zero_comp, zero_add, contractingPrismLift, Category.assoc] using h'.symm

public theorem contractingPrismLift_quotient_cycle :
    (contractingPrismLift S H n ≫ S.g.f (n + 2)) ≫ S.X₃.d (n + 2) (n + 1) = 0 := by
  rw [Category.assoc, S.g.comm, ← Category.assoc, contractingPrismLift_boundary,
    Category.assoc]
  have h := congrArg (fun f ↦ f.f (n + 1)) S.zero
  change S.f.f (n + 1) ≫ S.g.f (n + 1) = 0 at h
  rw [h, comp_zero]

public def contractingPrismClass : S.X₁.cycles (n + 1) ⟶ S.X₃.homology (n + 2) :=
  S.X₃.liftCycles (contractingPrismLift S H n ≫ S.g.f (n + 2)) (n + 1) (by simp)
    (contractingPrismLift_quotient_cycle S H n) ≫ S.X₃.homologyπ (n + 2)

public theorem contractingPrismClass_boundary :
    contractingPrismClass S H n ≫ hS.δ (n + 2) (n + 1) rfl = S.X₁.homologyπ (n + 1) := by
  have h := hS.δ_eq (n + 2) (n + 1) (by simp)
    (contractingPrismLift S H n ≫ S.g.f (n + 2))
    (contractingPrismLift_quotient_cycle S H n) (contractingPrismLift S H n) rfl
    (S.X₁.iCycles (n + 1)) (contractingPrismLift_boundary S H n).symm n (by simp)
  have he (hz) : S.X₁.liftCycles (S.X₁.iCycles (n + 1)) n (by simp) hz =
      𝟙 (S.X₁.cycles (n + 1)) := by
    apply (cancel_mono (S.X₁.iCycles (n + 1))).mp
    simp only [liftCycles_i, Category.id_comp]
  simpa only [contractingPrismClass, Category.assoc, he, Category.id_comp] using h

include H in
public theorem contractingPrism_boundary_isIso :
    IsIso (hS.δ (n + 2) (n + 1) rfl) := by
  have hz (k : ℕ) : IsZero (S.X₂.homology k) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    simpa only [homologyMap_id, homologyMap_zero] using H.homologyMap_eq k
  exact hS.isIso_δ (n + 2) (n + 1) rfl (hz _) (hz _)

public theorem contractingPrismClass_eq_inverse_boundary :
    let := contractingPrism_boundary_isIso S hS H n
    contractingPrismClass S H n =
      S.X₁.homologyπ (n + 1) ≫ inv (hS.δ (n + 2) (n + 1) rfl) := by
  let := contractingPrism_boundary_isIso S hS H n
  apply (cancel_mono (hS.δ (n + 2) (n + 1) rfl)).mp
  simp only [contractingPrismClass_boundary, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]


end SphereSixComplex
