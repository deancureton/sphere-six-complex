module

public import SphereSixComplex.TriangleGroup.FuchsianAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.Notation
import all SphereSixComplex.TriangleGroup.Representation

/-!
# Smoothness of the Fuchsian triangle-group action

The two explicit generators act by smooth Möbius transformations.  Smoothness for every element
of the free product follows by writing each cyclic-factor element as a power of its generator and
then applying free-product induction and closure under composition.
-/

open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups

noncomputable section

namespace SphereSixComplex.TriangleGroup

private abbrev UpperHalfPlaneModel := modelWithCornersSelf ℂ ℂ

private def ContMDiffPerm (n : WithTop ℕ∞) (p : Equiv.Perm UpperHalfPlane) : Prop :=
  ContMDiff UpperHalfPlaneModel UpperHalfPlaneModel n (fun z ↦ p z)

private theorem multiplicativeZMod_eq_generator_pow {k : ℕ} [NeZero k]
    (x : Multiplicative (ZMod k)) :
    x = Multiplicative.ofAdd (1 : ZMod k) ^ x.toAdd.val := by
  apply Multiplicative.toAdd.injective
  simp

private theorem contMDiffPerm_mul {n : WithTop ℕ∞} {p q : Equiv.Perm UpperHalfPlane}
    (hp : ContMDiffPerm n p) (hq : ContMDiffPerm n q) : ContMDiffPerm n (p * q) :=
  hp.comp hq

private theorem contMDiffPerm_pow {n : WithTop ℕ∞} (p : Equiv.Perm UpperHalfPlane)
    (hp : ContMDiffPerm n p) (k : ℕ) : ContMDiffPerm n (p ^ k) := by
  induction k with
  | zero =>
      change ContMDiff UpperHalfPlaneModel UpperHalfPlaneModel n
        (fun z : UpperHalfPlane ↦ z)
      simpa only [Function.id_def] using
        (contMDiff_id : ContMDiff UpperHalfPlaneModel UpperHalfPlaneModel n
          (id : UpperHalfPlane → UpperHalfPlane))
  | succ k ih =>
      rw [pow_succ]
      exact contMDiffPerm_mul ih hp

private theorem fuchsianOnePerm_contMDiff (n : WithTop ℕ∞) :
    ContMDiffPerm n fuchsianOnePerm := by
  change ContMDiff UpperHalfPlaneModel UpperHalfPlaneModel n
    (fun z : UpperHalfPlane ↦ fuchsianOneGL • z)
  apply UpperHalfPlane.contMDiff_smul
  simp [fuchsianOneGL]

private theorem fuchsianTwoPerm_contMDiff (n : WithTop ℕ∞) :
    ContMDiffPerm n fuchsianTwoPerm := by
  change ContMDiff UpperHalfPlaneModel UpperHalfPlaneModel n
    (fun z : UpperHalfPlane ↦ fuchsianTwoGL • z)
  apply UpperHalfPlane.contMDiff_smul
  simp [fuchsianTwoGL]

private theorem fuchsianSourceAction_inl_contMDiff (x : CyclicThree) (n : WithTop ℕ∞) :
    ContMDiffPerm n (fuchsianSourceAction (Monoid.Coprod.inl x)) := by
  rw [multiplicativeZMod_eq_generator_pow x]
  simp only [map_pow]
  rw [show Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3)) = g₁ by
      exact SphereSixComplex.TriangleGroup.g₁.eq_def.symm,
    fuchsianSourceAction_g₁]
  exact contMDiffPerm_pow _ (fuchsianOnePerm_contMDiff n) _

private theorem fuchsianSourceAction_inr_contMDiff (x : CyclicFour) (n : WithTop ℕ∞) :
    ContMDiffPerm n (fuchsianSourceAction (Monoid.Coprod.inr x)) := by
  rw [multiplicativeZMod_eq_generator_pow x]
  simp only [map_pow]
  rw [show Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) = g₂ by
      exact SphereSixComplex.TriangleGroup.g₂.eq_def.symm,
    fuchsianSourceAction_g₂]
  exact contMDiffPerm_pow _ (fuchsianTwoPerm_contMDiff n) _

/-- Every element of `Delta(3, 4, ∞)` acts smoothly on the source upper half-plane. -/
public theorem fuchsianSourceAction_contMDiff (g : Delta) (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (fun z : UpperHalfPlane ↦ fuchsianSourceAction g • z) := by
  change ContMDiffPerm n (fuchsianSourceAction g)
  induction g using Monoid.Coprod.induction_on with
  | inl x => exact fuchsianSourceAction_inl_contMDiff x n
  | inr x => exact fuchsianSourceAction_inr_contMDiff x n
  | mul x y hx hy =>
      rw [map_mul]
      exact contMDiffPerm_mul hx hy

/-- The source-side fields of a triangle uniformization, separated from any choice of invariant
holomorphic coordinate. -/
public structure SmoothTriangleSource where
  sourceAction : Delta →* Equiv.Perm UpperHalfPlane
  sourceAction_contMDiff : ∀ g (n : WithTop ℕ∞),
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (fun z : UpperHalfPlane ↦ sourceAction g • z)
  zOne : UpperHalfPlane
  zTwo : UpperHalfPlane
  zOne_fixed : sourceAction g₁ • zOne = zOne
  zTwo_fixed : sourceAction g₂ • zTwo = zTwo
  cuspRegion : Set UpperHalfPlane
  cuspRegion_nonempty : cuspRegion.Nonempty
  cuspRegion_invariant : ∀ z, sourceAction g₀ • z ∈ cuspRegion ↔ z ∈ cuspRegion

/-- The explicit Fuchsian source geometry, without an asserted invariant coordinate. -/
@[expose] public noncomputable def explicitFuchsianTriangleSource : SmoothTriangleSource where
  sourceAction := fuchsianSourceAction
  sourceAction_contMDiff := fuchsianSourceAction_contMDiff
  zOne := fuchsianOneFixedPoint
  zTwo := fuchsianTwoFixedPoint
  zOne_fixed := fuchsianOneFixedPoint_fixed
  zTwo_fixed := fuchsianTwoFixedPoint_fixed
  cuspRegion := fuchsianCuspRegion
  cuspRegion_nonempty := fuchsianCuspRegion_nonempty
  cuspRegion_invariant := fuchsianCuspRegion_invariant

end SphereSixComplex.TriangleGroup
