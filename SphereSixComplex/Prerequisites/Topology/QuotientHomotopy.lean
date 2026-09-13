module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

open scoped unitInterval ContinuousMap
open Topology

namespace Topology.IsQuotientMap
variable {X Q Y : Type*} [TopologicalSpace X] [TopologicalSpace Q] [TopologicalSpace Y]
    {q : X → Q}

/-- Descend a homotopy constant on each fiber of a quotient map. -/
noncomputable def descendHomotopy (hq : IsQuotientMap q) {f g : C(Q, Y)}
    (H : ContinuousMap.Homotopy (f.comp ⟨q, hq.continuous⟩) (g.comp ⟨q, hq.continuous⟩))
    (h : ∀ t x y, q x = q y → H (t, x) = H (t, y)) :
    ContinuousMap.Homotopy f g where
  toFun p := H (p.1, Function.surjInv hq.surjective p.2)
  continuous_toFun := by
    apply hq.continuous_lift_prod_right
    apply H.continuous.congr
    intro p
    exact h p.1 p.2 _ (Function.surjInv_eq hq.surjective (q p.2)).symm
  map_zero_left x := (H.map_zero_left _).trans
    (congrArg f (Function.surjInv_eq hq.surjective x))
  map_one_left x := (H.map_one_left _).trans
    (congrArg g (Function.surjInv_eq hq.surjective x))

end Topology.IsQuotientMap

namespace Topology.IsQuotientMap
variable {ι V Q : Type*} [TopologicalSpace ι] [TopologicalSpace V]
  [AddCommGroup V] [Module ℝ V] [ContinuousSMul ℝ V] [TopologicalSpace Q]

/-- Radial contraction descends when a quotient identifies all zero vectors and respects scaling. -/
theorem contractibleSpace_of_smul
    {q : ι × V → Q} (hq : IsQuotientMap q) (p : Q)
    (hzero : ∀ i, q (i, 0) = p)
    (hsmul : ∀ (t : unitInterval) x y, q x = q y →
      q (x.1, (1 - (t : ℝ)) • x.2) = q (y.1, (1 - (t : ℝ)) • y.2)) :
    ContractibleSpace Q := by
  let H : ContinuousMap.Homotopy
      ((ContinuousMap.id Q).comp ⟨q, hq.continuous⟩)
      ((ContinuousMap.const Q p).comp ⟨q, hq.continuous⟩) :=
    { toFun := fun z ↦ q (z.2.1, (1 - (z.1 : ℝ)) • z.2.2)
      continuous_toFun := hq.continuous.comp
        (continuous_snd.fst.prodMk
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
            continuous_snd.snd))
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simpa using hzero x.1 }
  exact (contractible_iff_id_nullhomotopic Q).mpr
    ⟨p, ⟨hq.descendHomotopy H hsmul⟩⟩

end Topology.IsQuotientMap

end
