module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.Topology.ContinuousMap.Ordered

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap

namespace ContinuousMap.Homotopy


public def loopSwapExtend
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b}
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap) :
    C(ℝ, C(unitInterval, X)) :=
  (H.toContinuousMap.comp ContinuousMap.prodSwap).curry.IccExtend zero_le_one

public theorem loopSwapExtend_apply_coe
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b}
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (s t : unitInterval) :
    loopSwapExtend H t s = H (s, t) := by
  rw [loopSwapExtend, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem]
  rfl

public theorem loopSwapExtend_zero
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b}
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (t : ℝ) :
    loopSwapExtend H t 0 = p.extend t := by
  rw [loopSwapExtend, ContinuousMap.coe_IccExtend]
  change H (0, _) = p _
  exact H.map_zero_left _

public theorem loopSwapExtend_one
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b}
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (t : ℝ) :
    loopSwapExtend H t 1 = q.extend t := by
  rw [loopSwapExtend, ContinuousMap.coe_IccExtend]
  change H (1, _) = q _
  exact H.map_one_left _

/-- Horizontal composition for free loop homotopies with a common moving basepoint. -/
public def hcompLoop
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p₀ q₀ : Path a a} {p₁ q₁ : Path b b}
    (H : ContinuousMap.Homotopy p₀.toContinuousMap p₁.toContinuousMap)
    (K : ContinuousMap.Homotopy q₀.toContinuousMap q₁.toContinuousMap)
    (hjoin : ∀ s : unitInterval, H (s, 1) = K (s, 0)) :
    ContinuousMap.Homotopy (p₀.trans q₀).toContinuousMap
      (p₁.trans q₁).toContinuousMap where
  toFun x := if (x.2 : ℝ) ≤ 1 / 2 then
      loopSwapExtend H (2 * x.2) x.1
    else loopSwapExtend K (2 * x.2 - 1) x.1
  continuous_toFun := by
    have hcontH : Continuous (fun x : unitInterval × unitInterval ↦
        loopSwapExtend H (2 * x.2) x.1) := by fun_prop
    have hcontK : Continuous (fun x : unitInterval × unitInterval ↦
        loopSwapExtend K (2 * x.2 - 1) x.1) := by fun_prop
    apply continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
      hcontH.continuousOn hcontK.continuousOn
    intro x hx
    change (x.2 : ℝ) = 1 / 2 at hx
    rw [hx]
    norm_num
    exact (loopSwapExtend_apply_coe H x.1 1).trans
      ((hjoin x.1).trans
        (loopSwapExtend_apply_coe K x.1 0).symm)
  map_zero_left t := by
    simp only [loopSwapExtend_zero]
    rfl
  map_one_left t := by
    simp only [loopSwapExtend_one]
    rfl

public theorem hcompLoop_apply
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p₀ q₀ : Path a a} {p₁ q₁ : Path b b}
    (H : ContinuousMap.Homotopy p₀.toContinuousMap p₁.toContinuousMap)
    (K : ContinuousMap.Homotopy q₀.toContinuousMap q₁.toContinuousMap)
    (hjoin : ∀ s : unitInterval, H (s, 1) = K (s, 0))
    (x : unitInterval × unitInterval) :
    hcompLoop H K hjoin x =
      if (x.2 : ℝ) ≤ 1 / 2 then
        loopSwapExtend H (2 * x.2) x.1
      else loopSwapExtend K (2 * x.2 - 1) x.1 := rfl

public theorem hcompLoop_trace
    {X : Type*} [TopologicalSpace X] {a b : X}
    {p₀ q₀ : Path a a} {p₁ q₁ : Path b b}
    (H : ContinuousMap.Homotopy p₀.toContinuousMap p₁.toContinuousMap)
    (K : ContinuousMap.Homotopy q₀.toContinuousMap q₁.toContinuousMap)
    (hjoin : ∀ s : unitInterval, H (s, 1) = K (s, 0))
    (htrace : ∀ s : unitInterval, H (s, 0) = K (s, 1))
    (s : unitInterval) :
    hcompLoop H K hjoin (s, 0) =
      hcompLoop H K hjoin (s, 1) := by
  rw [hcompLoop_apply, hcompLoop_apply]
  norm_num
  exact (loopSwapExtend_apply_coe H s 0).trans
    ((htrace s).trans
      (loopSwapExtend_apply_coe K s 1).symm)



/-- Vertical composition preserves any pointwise equality between two synchronized homotopies. -/
public theorem trans_apply_eq_of_apply_eq
    {X : Type*} [TopologicalSpace X]
    {f₀ f₁ f₂ g₀ g₁ g₂ : C(unitInterval, X)}
    (F₀ : ContinuousMap.Homotopy f₀ f₁)
    (F₁ : ContinuousMap.Homotopy f₁ f₂)
    (G₀ : ContinuousMap.Homotopy g₀ g₁)
    (G₁ : ContinuousMap.Homotopy g₁ g₂)
    (x y : unitInterval)
    (h₀ : ∀ s : unitInterval, F₀ (s, x) = G₀ (s, y))
    (h₁ : ∀ s : unitInterval, F₁ (s, x) = G₁ (s, y))
    (s : unitInterval) :
    F₀.trans F₁ (s, x) = G₀.trans G₁ (s, y) := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact h₀ _
  · exact h₁ _


end ContinuousMap.Homotopy
