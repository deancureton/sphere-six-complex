module

public import SphereSixComplex.Topology.ClosedCollarPush
public import Mathlib.Topology.UrysohnsLemma

@[expose] public section
noncomputable section

open Set Topology
open scoped unitInterval

namespace SphereSixComplex

public abbrev TopologicalCollarParameter := {t : ℝ // 0 ≤ t ∧ t < 1}

public def openCollarZero : TopologicalCollarParameter := ⟨0, by norm_num⟩

public structure OpenTopologicalCollar (X : Type*) [TopologicalSpace X] (B : Set X) where
  neighborhood : TopologicalSpace.Opens X
  chart : (B × TopologicalCollarParameter) ≃ₜ neighborhood
  zero : ∀ b, (chart (b, openCollarZero)).1 = b.1

namespace OpenTopologicalCollar

variable {X : Type*} [TopologicalSpace X] {B : Set X}

public theorem boundary_subset (c : OpenTopologicalCollar X B) : B ⊆ c.neighborhood := by
  intro x hx
  have h : (c.chart (⟨x, hx⟩, openCollarZero)).1 = x := c.zero ⟨x, hx⟩
  exact h ▸ (c.chart (⟨x, hx⟩, openCollarZero)).2

public theorem chart_mem_boundary (c : OpenTopologicalCollar X B) (p : B × TopologicalCollarParameter) :
    (c.chart p).1 ∈ B ↔ p.2 = openCollarZero := by
  constructor
  · intro h
    have he : c.chart (⟨(c.chart p).1, h⟩, openCollarZero) = c.chart p :=
      Subtype.ext (c.zero ⟨(c.chart p).1, h⟩)
    exact (congrArg Prod.snd (c.chart.injective he)).symm
  · intro h
    rw [show p = (p.1, openCollarZero) from Prod.ext rfl h, c.zero]
    exact p.1.2

public def pushParameter (s a : unitInterval) (t : TopologicalCollarParameter) : TopologicalCollarParameter :=
  ⟨max (t : ℝ) ((s : ℝ) * a / 2), t.2.1.trans (le_max_left _ _),
    max_lt t.2.2 (by have := mul_le_one₀ s.2.2 a.2.1 a.2.2; linarith)⟩

public theorem continuous_pushParameter :
    Continuous (fun p : (unitInterval × unitInterval) × TopologicalCollarParameter ↦
      pushParameter p.1.1 p.1.2 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_snd.subtype_val.max
    ((continuous_fst.fst.subtype_val.mul continuous_fst.snd.subtype_val).div_const 2)

@[simp] public theorem pushParameter_zero_time (a : unitInterval) (t : TopologicalCollarParameter) :
    pushParameter 0 a t = t := by
  apply Subtype.ext
  change max (t : ℝ) (0 * (a : ℝ) / 2) = t
  simp [t.2.1]

@[simp] public theorem pushParameter_zero_weight (s : unitInterval) (t : TopologicalCollarParameter) :
    pushParameter s 0 t = t := by
  apply Subtype.ext
  change max (t : ℝ) ((s : ℝ) * 0 / 2) = t
  simp [t.2.1]

public def push (c : OpenTopologicalCollar X B) (w : C(X, unitInterval))
    (s : unitInterval) (x : X) : X := by
  classical
  exact if hx : x ∈ c.neighborhood then
    let p := c.chart.symm ⟨x, hx⟩
    (c.chart (p.1, pushParameter s (w x) p.2)).1
  else x

public theorem push_chart (c : OpenTopologicalCollar X B) (w : C(X, unitInterval))
    (s : unitInterval) (p : B × TopologicalCollarParameter) :
    c.push w s (c.chart p).1 =
      (c.chart (p.1, pushParameter s (w (c.chart p).1) p.2)).1 := by
  simp [push, (c.chart p).2]

public theorem push_of_weight_zero (c : OpenTopologicalCollar X B) (w : C(X, unitInterval))
    (s : unitInterval) (x : X) (hx : w x = 0) : c.push w s x = x := by
  by_cases hn : x ∈ c.neighborhood <;> simp [push, hn, hx]

public theorem continuous_push (c : OpenTopologicalCollar X B) (w : C(X, unitInterval))
    (V : Set X) (hVU : closure V ⊆ c.neighborhood)
    (hw : ∀ x ∉ V, w x = 0) :
    Continuous (fun p : unitInterval × X ↦ c.push w p.1 p.2) := by
  let U : Set (unitInterval × X) := Prod.snd ⁻¹' (c.neighborhood : Set X)
  let K : Set (unitInterval × X) := Prod.snd ⁻¹' closure V
  have hU : IsOpen U := c.neighborhood.2.preimage continuous_snd
  have hK : IsClosed K := isClosed_closure.preimage continuous_snd
  have hcov : U ∪ Kᶜ = univ := by
    ext p
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases h : p ∈ K
    · exact Or.inl (hVU h)
    · exact Or.inr h
  have hleft : ContinuousOn (fun p : unitInterval × X ↦ c.push w p.1 p.2) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    let q : U → c.neighborhood := fun p ↦ ⟨p.1.2, p.2⟩
    have hq : Continuous q := (continuous_snd.comp continuous_subtype_val).subtype_mk _
    have he : (fun p : U ↦ c.push w p.1.1 p.1.2) =
        fun p ↦ (c.chart ((c.chart.symm (q p)).1,
          pushParameter p.1.1 (w p.1.2) (c.chart.symm (q p)).2)).1 := by
      funext p
      have hp : p.1.2 ∈ c.neighborhood := p.2
      simp only [push, hp, dite_true, q]
    change Continuous (fun p : U ↦ c.push w p.1.1 p.1.2)
    rw [he]
    apply Continuous.subtype_val
    apply c.chart.continuous.comp
    exact (c.chart.symm.continuous.comp hq).fst.prodMk
      (continuous_pushParameter.comp
        (((continuous_fst.comp continuous_subtype_val).prodMk
          (w.continuous.comp (continuous_snd.comp continuous_subtype_val))).prodMk
          (c.chart.symm.continuous.comp hq).snd))
  have hright : ContinuousOn (fun p : unitInterval × X ↦ c.push w p.1 p.2) Kᶜ := by
    apply continuous_snd.continuousOn.congr
    intro p hp
    exact c.push_of_weight_zero w p.1 p.2 (hw p.2 (fun h ↦ hp (subset_closure h)))
  rw [← continuousOn_univ, ← hcov]
  exact hleft.union_of_isOpen hright hU hK.isOpen_compl

public structure PushWeight (c : OpenTopologicalCollar X B) where
  inner : Set X
  closure_subset : closure inner ⊆ c.neighborhood
  weight : C(X, unitInterval)
  zero_outside : ∀ x ∉ inner, weight x = 0
  one_boundary : ∀ x ∈ B, weight x = 1

public theorem nonempty_pushWeight [NormalSpace X] (c : OpenTopologicalCollar X B)
    (hB : IsClosed B) : Nonempty c.PushWeight := by
  obtain ⟨V, hV, hBV, hVU⟩ := normal_exists_closure_subset hB c.neighborhood.2 c.boundary_subset
  obtain ⟨f, hf0, hf1, hfI⟩ := exists_continuous_zero_one_of_isClosed
    hV.isClosed_compl hB (disjoint_left.mpr (fun x hx h ↦ hx (hBV h)))
  refine ⟨⟨V, hVU, ⟨fun x ↦ ⟨f x, hfI x⟩, f.continuous.subtype_mk _⟩, ?_, ?_⟩⟩
  · intro x hx
    exact Subtype.ext (hf0 hx)
  · intro x hx
    exact Subtype.ext (hf1 hx)

@[simp] public theorem push_zero (c : OpenTopologicalCollar X B)
    (w : C(X, unitInterval)) (x : X) : c.push w 0 x = x := by
  by_cases hx : x ∈ c.neighborhood <;> simp [push, hx]

public theorem push_notMem_boundary (c : OpenTopologicalCollar X B)
    (w : C(X, unitInterval)) (s : unitInterval) {x : X} (hx : x ∉ B) :
    c.push w s x ∉ B := by
  by_cases hn : x ∈ c.neighborhood
  · let p := c.chart.symm ⟨x, hn⟩
    have hp : (c.chart p).1 = x := congrArg Subtype.val (c.chart.apply_symm_apply _)
    rw [← hp, push_chart, c.chart_mem_boundary]
    intro h
    have hval : max (p.2 : ℝ) ((s : ℝ) * w (c.chart p).1 / 2) = 0 :=
      congrArg (fun t : TopologicalCollarParameter ↦ (t : ℝ)) h
    have ht : p.2 = openCollarZero := Subtype.ext
      (le_antisymm ((le_max_left _ _).trans hval.le) p.2.2.1)
    exact hx (hp ▸ (c.chart_mem_boundary p).mpr ht)
  · simpa only [push, hn, dite_false] using hx

public theorem push_one_notMem_boundary (c : OpenTopologicalCollar X B)
    (w : c.PushWeight) (x : X) : c.push w.weight 1 x ∉ B := by
  by_cases hx : x ∈ B
  · have hn := c.boundary_subset hx
    let p := c.chart.symm ⟨x, hn⟩
    have hp : (c.chart p).1 = x := congrArg Subtype.val (c.chart.apply_symm_apply _)
    rw [← hp, push_chart, c.chart_mem_boundary]
    intro h
    have hw : w.weight (c.chart p).1 = 1 := hp ▸ w.one_boundary x hx
    have hval : max (p.2 : ℝ) (1 / 2) = 0 := by
      have hv := congrArg (fun t : TopologicalCollarParameter ↦ (t : ℝ)) h
      change max (p.2 : ℝ) ((1 : ℝ) * (w.weight (c.chart p).1 : ℝ) / 2) = 0 at hv
      rw [hw] at hv
      change max (p.2 : ℝ) (1 * 1 / 2) = 0 at hv
      simpa only [one_mul] using hv
    have := le_max_right (p.2 : ℝ) (1 / 2)
    linarith
  · exact c.push_notMem_boundary w.weight 1 hx

public def interiorMap (c : OpenTopologicalCollar X B) (w : c.PushWeight) : C(X, ↥(Bᶜ)) :=
  ⟨fun x ↦ ⟨c.push w.weight 1 x, c.push_one_notMem_boundary w x⟩,
    ((c.continuous_push w.weight w.inner w.closure_subset w.zero_outside).comp
      (continuous_const.prodMk continuous_id)).subtype_mk _⟩

public def pushHomotopy (c : OpenTopologicalCollar X B) (w : c.PushWeight) :
    (ContinuousMap.id X).Homotopy
      ((ClosedTopologicalCollar.interiorInclusion B).comp (c.interiorMap w)) where
  toFun p := c.push w.weight p.1 p.2
  continuous_toFun := c.continuous_push w.weight w.inner w.closure_subset w.zero_outside
  map_zero_left := c.push_zero w.weight
  map_one_left _ := rfl

public def interiorPushHomotopy (c : OpenTopologicalCollar X B) (w : c.PushWeight) :
    (ContinuousMap.id ↥(Bᶜ)).Homotopy
      ((c.interiorMap w).comp (ClosedTopologicalCollar.interiorInclusion B)) where
  toFun p := ⟨c.push w.weight p.1 p.2.1, c.push_notMem_boundary w.weight p.1 p.2.2⟩
  continuous_toFun := ((c.continuous_push w.weight w.inner w.closure_subset w.zero_outside).comp
    (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _
  map_zero_left x := Subtype.ext (c.push_zero w.weight x)
  map_one_left _ := rfl

public def interiorHomotopyEquiv (c : OpenTopologicalCollar X B) (w : c.PushWeight) :
    ContinuousMap.HomotopyEquiv X ↥(Bᶜ) where
  toFun := c.interiorMap w
  invFun := ClosedTopologicalCollar.interiorInclusion B
  left_inv := ⟨(c.pushHomotopy w).symm⟩
  right_inv := ⟨(c.interiorPushHomotopy w).symm⟩

public theorem contractibleSpace [NormalSpace X] (c : OpenTopologicalCollar X B)
    (hB : IsClosed B) [ContractibleSpace ↥(Bᶜ)] : ContractibleSpace X := by
  obtain ⟨w⟩ := c.nonempty_pushWeight hB
  exact (c.interiorHomotopyEquiv w).contractibleSpace

end OpenTopologicalCollar
end SphereSixComplex
