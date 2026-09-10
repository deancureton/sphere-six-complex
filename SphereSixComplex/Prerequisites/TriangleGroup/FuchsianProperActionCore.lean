module

public import SphereSixComplex.Prerequisites.TriangleGroup.BinaryIndexedCoprod
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import all SphereSixComplex.Prerequisites.TriangleGroup.FreeProductTorsion

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianProperFreeness

open SphereSixComplex.TriangleGroup

/-- An element fixing a point of a properly discontinuous group action has finite order. -/
public theorem isOfFinOrder_of_fixed_of_properlyDiscontinuous
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ProperlyDiscontinuousSMul G X] {g : G} {x : X} (hfixed : g • x = x) :
    IsOfFinOrder g := by
  rw [← finite_powers]
  apply (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := G) x).subset
  intro h hh
  change h • x = x
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff h g).mp hh
  clear hh
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, hfixed, ih]

/-- The explicit permutation representation regarded as a genuine action of `Delta`. -/
@[expose, instance_reducible] public noncomputable def fuchsianSourceMulAction :
    MulAction Delta UpperHalfPlane where
  smul g z := (fuchsianSourceAction g) z
  one_smul z := by
    change (fuchsianSourceAction 1) z = z
    rw [map_one]
    rfl
  mul_smul g h z := by
    change (fuchsianSourceAction (g * h)) z =
      (fuchsianSourceAction g) ((fuchsianSourceAction h) z)
    rw [map_mul]
    rfl

/-- Proper discontinuity on the full upper half-plane forces every point stabilizer element to
have finite order for the explicit Fuchsian action. -/
public theorem fuchsian_fixed_isOfFinOrder
    (hproper : letI := fuchsianSourceMulAction
      ProperlyDiscontinuousSMul Delta UpperHalfPlane)
    {g : Delta} {z : UpperHalfPlane} (hfixed : fuchsianSourceAction g • z = z) :
    IsOfFinOrder g := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane := hproper
  apply isOfFinOrder_of_fixed_of_properlyDiscontinuous (G := Delta)
    (X := UpperHalfPlane)
  exact hfixed

/-- The explicit Fuchsian action is free at every point outside its two elliptic orbits. -/
public theorem fuchsian_fixed_regular_eq_one
    (hproper : letI := fuchsianSourceMulAction
      ProperlyDiscontinuousSMul Delta UpperHalfPlane)
    {g : Delta} {z : UpperHalfPlane} (hz : FreeProductTorsion.IsFuchsianRegularPoint z)
    (hfixed : fuchsianSourceAction g • z = z) : g = 1 := by
  exact BinaryIndexedCoprod.finiteOrder_fixed_regular_eq_one hz
    (fuchsian_fixed_isOfFinOrder hproper hfixed) hfixed

/-- The upper half-plane with the two explicit Fuchsian elliptic orbits removed. -/
public abbrev FuchsianRegularBase :=
  {z : UpperHalfPlane // FreeProductTorsion.IsFuchsianRegularPoint z}

public theorem isFuchsianRegularPoint_smul (h : Delta) {z : UpperHalfPlane}
    (hz : FreeProductTorsion.IsFuchsianRegularPoint z) :
    FreeProductTorsion.IsFuchsianRegularPoint (fuchsianSourceAction h • z) := by
  intro g
  simpa only [← mul_smul, ← map_mul] using hz (g * h)

/-- The explicit Fuchsian action restricted to its regular locus. -/
@[expose, instance_reducible] public noncomputable def fuchsianRegularMulAction :
    MulAction Delta FuchsianRegularBase where
  smul g z := ⟨fuchsianSourceAction g • z.1, isFuchsianRegularPoint_smul g z.2⟩
  one_smul z := by
    apply Subtype.ext
    change fuchsianSourceAction 1 • z.1 = z.1
    simp
  mul_smul g h z := by
    apply Subtype.ext
    change fuchsianSourceAction (g * h) • z.1 =
      fuchsianSourceAction g • (fuchsianSourceAction h • z.1)
    rw [map_mul, mul_smul]

/-- In standard typeclass form, the explicit Fuchsian action is free on the regular locus. -/
public theorem fuchsianRegular_isCancelSMul
    (hproper : letI := fuchsianSourceMulAction
      ProperlyDiscontinuousSMul Delta UpperHalfPlane) :
    letI := fuchsianRegularMulAction
    IsCancelSMul Delta FuchsianRegularBase := by
  let _ := fuchsianRegularMulAction
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g z hfixed
  apply fuchsian_fixed_regular_eq_one hproper z.2
  exact congrArg Subtype.val hfixed

end SphereSixComplex.TriangleGroup.FuchsianProperFreeness
