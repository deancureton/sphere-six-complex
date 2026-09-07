module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic

@[expose] public section
noncomputable section

open Set Topology
open scoped unitInterval

namespace SphereSixComplex

public structure ClosedTopologicalCollar (X : Type*) [TopologicalSpace X] (B : Set X) where
  neighborhood : Set X
  isClosed_neighborhood : IsClosed neighborhood
  chart : (B × unitInterval) ≃ₜ neighborhood
  zero : ∀ b, (chart (b, 0)).1 = b.1
  isOpen_lower : IsOpen {x | ∃ p : B × unitInterval, (p.2 : ℝ) < 1 ∧ (chart p).1 = x}
  boundary : ∀ p, (chart p).1 ∈ B ↔ p.2 = 0

namespace ClosedTopologicalCollar

variable {X : Type*} [TopologicalSpace X] {B : Set X}

public def pushParameter (s t : unitInterval) : unitInterval :=
  ⟨max (t : ℝ) ((s : ℝ) / 2), (t.2.1.trans (le_max_left _ _)),
    max_le t.2.2 (by linarith [s.2.2])⟩

public theorem continuous_pushParameter :
    Continuous (fun p : unitInterval × unitInterval ↦ pushParameter p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_snd.subtype_val.max (continuous_fst.subtype_val.div_const 2)

@[simp] public theorem pushParameter_zero (t : unitInterval) : pushParameter 0 t = t := by
  apply Subtype.ext
  change max (t : ℝ) (0 / 2) = t
  simpa using max_eq_left t.2.1

@[simp] public theorem pushParameter_one (s : unitInterval) : pushParameter s 1 = 1 := by
  apply Subtype.ext
  change max (1 : ℝ) ((s : ℝ) / 2) = 1
  exact max_eq_left (by linarith [s.2.2])

public def push (c : ClosedTopologicalCollar X B) (s : unitInterval) (x : X) : X := by
  classical
  exact if hx : x ∈ c.neighborhood then
    let p := c.chart.symm ⟨x, hx⟩
    (c.chart (p.1, pushParameter s p.2)).1
  else x

public theorem push_chart (c : ClosedTopologicalCollar X B) (s : unitInterval)
    (p : B × unitInterval) :
    c.push s (c.chart p).1 = (c.chart (p.1, pushParameter s p.2)).1 := by
  simp [push, (c.chart p).2]

public theorem push_outside_lower (c : ClosedTopologicalCollar X B) (s : unitInterval)
    (x : X) (hx : ¬ ∃ p : B × unitInterval, (p.2 : ℝ) < 1 ∧ (c.chart p).1 = x) :
    c.push s x = x := by
  by_cases hn : x ∈ c.neighborhood
  · let p := c.chart.symm ⟨x, hn⟩
    have hp : (c.chart p).1 = x := congrArg Subtype.val (c.chart.apply_symm_apply _)
    have ht : p.2 = 1 := by
      apply Subtype.ext
      apply le_antisymm p.2.2.2
      exact le_of_not_gt (fun h ↦ hx ⟨p, h, hp⟩)
    rw [← hp, push_chart, ht, pushParameter_one]
    congr 2
    exact Prod.ext rfl ht.symm
  · simp [push, hn]

public theorem continuous_push (c : ClosedTopologicalCollar X B) :
    Continuous (fun p : unitInterval × X ↦ c.push p.1 p.2) := by
  let N : Set (unitInterval × X) := Prod.snd ⁻¹' c.neighborhood
  let V : Set (unitInterval × X) := Prod.snd ⁻¹'
    {x | ∃ p : B × unitInterval, (p.2 : ℝ) < 1 ∧ (c.chart p).1 = x}
  have hN : IsClosed N := c.isClosed_neighborhood.preimage continuous_snd
  have hV : IsOpen V := c.isOpen_lower.preimage continuous_snd
  have hcov : N ∪ Vᶜ = univ := by
    ext p
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases h : p ∈ V
    · left
      obtain ⟨q, _, hq⟩ := h
      change p.2 ∈ c.neighborhood
      exact hq ▸ (c.chart q).2
    · exact Or.inr h
  have hleft : ContinuousOn (fun p : unitInterval × X ↦ c.push p.1 p.2) N := by
    rw [continuousOn_iff_continuous_domRestrict]
    let q : N → c.neighborhood := fun p ↦ ⟨p.1.2, p.2⟩
    have hq : Continuous q := (continuous_snd.comp continuous_subtype_val).subtype_mk _
    have he : (fun p : N ↦ c.push p.1.1 p.1.2) =
        fun p ↦ (c.chart ((c.chart.symm (q p)).1,
          pushParameter p.1.1 (c.chart.symm (q p)).2)).1 := by
      funext p
      have hp : p.1.2 ∈ c.neighborhood := p.2
      simp only [push, hp, dite_true, q]
    change Continuous (fun p : N ↦ c.push p.1.1 p.1.2)
    rw [he]
    apply Continuous.subtype_val
    apply c.chart.continuous.comp
    exact (c.chart.symm.continuous.comp hq).fst.prodMk
      (continuous_pushParameter.comp ((continuous_fst.comp continuous_subtype_val).prodMk
        (c.chart.symm.continuous.comp hq).snd))
  have hright : ContinuousOn (fun p : unitInterval × X ↦ c.push p.1 p.2) Vᶜ := by
    apply continuous_snd.continuousOn.congr
    intro p hp
    exact c.push_outside_lower p.1 p.2 hp
  rw [← continuousOn_univ, ← hcov]
  exact hleft.union_of_isClosed hright hN hV.isClosed_compl

@[simp] public theorem push_zero (c : ClosedTopologicalCollar X B) (x : X) :
    c.push 0 x = x := by
  by_cases hx : x ∈ c.neighborhood
  · simp [push, hx]
  · simp [push, hx]

public theorem boundary_subset (c : ClosedTopologicalCollar X B) : B ⊆ c.neighborhood := by
  intro x hx
  have h : (c.chart (⟨x, hx⟩, 0)).1 = x := c.zero ⟨x, hx⟩
  exact h ▸ (c.chart (⟨x, hx⟩, 0)).2

public theorem push_notMem_boundary (c : ClosedTopologicalCollar X B)
    (s : unitInterval) {x : X} (hx : x ∉ B) : c.push s x ∉ B := by
  by_cases hn : x ∈ c.neighborhood
  · let p := c.chart.symm ⟨x, hn⟩
    have hp : (c.chart p).1 = x := congrArg Subtype.val (c.chart.apply_symm_apply _)
    rw [← hp, push_chart, c.boundary]
    intro h
    have hval : max (p.2 : ℝ) ((s : ℝ) / 2) = 0 :=
      congrArg (fun t : unitInterval ↦ (t : ℝ)) h
    have ht : p.2 = 0 := Subtype.ext
      (le_antisymm ((le_max_left _ _).trans hval.le) p.2.2.1)
    exact hx (hp ▸ (c.boundary p).mpr ht)
  · simpa only [push, hn, dite_false] using hx

public theorem push_one_notMem_boundary (c : ClosedTopologicalCollar X B) (x : X) :
    c.push 1 x ∉ B := by
  by_cases hn : x ∈ c.neighborhood
  · let p := c.chart.symm ⟨x, hn⟩
    have hp : (c.chart p).1 = x := congrArg Subtype.val (c.chart.apply_symm_apply _)
    rw [← hp, push_chart, c.boundary]
    intro h
    have hval : max (p.2 : ℝ) (1 / 2) = 0 :=
      congrArg (fun t : unitInterval ↦ (t : ℝ)) h
    have := le_max_right (p.2 : ℝ) (1 / 2)
    linarith
  · simpa only [push, hn, dite_false] using (fun hx ↦ hn (c.boundary_subset hx))

public def interiorMap (c : ClosedTopologicalCollar X B) : C(X, ↥(Bᶜ)) :=
  ⟨fun x ↦ ⟨c.push 1 x, c.push_one_notMem_boundary x⟩,
    (c.continuous_push.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

public def interiorInclusion (B : Set X) : C(↥(Bᶜ), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

public def pushHomotopy (c : ClosedTopologicalCollar X B) :
    (ContinuousMap.id X).Homotopy ((interiorInclusion B).comp c.interiorMap) where
  toFun p := c.push p.1 p.2
  continuous_toFun := c.continuous_push
  map_zero_left := c.push_zero
  map_one_left _ := rfl

public def interiorPushHomotopy (c : ClosedTopologicalCollar X B) :
    (ContinuousMap.id ↥(Bᶜ)).Homotopy (c.interiorMap.comp (interiorInclusion B)) where
  toFun p := ⟨c.push p.1 p.2.1, c.push_notMem_boundary p.1 p.2.2⟩
  continuous_toFun := (c.continuous_push.comp
    (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _
  map_zero_left x := Subtype.ext (c.push_zero x)
  map_one_left _ := rfl

public def interiorHomotopyEquiv (c : ClosedTopologicalCollar X B) :
    ContinuousMap.HomotopyEquiv X ↥(Bᶜ) where
  toFun := c.interiorMap
  invFun := interiorInclusion B
  left_inv := ⟨c.pushHomotopy.symm⟩
  right_inv := ⟨c.interiorPushHomotopy.symm⟩

public theorem contractibleSpace (c : ClosedTopologicalCollar X B)
    [ContractibleSpace ↥(Bᶜ)] : ContractibleSpace X :=
  c.interiorHomotopyEquiv.contractibleSpace

end ClosedTopologicalCollar
end SphereSixComplex
