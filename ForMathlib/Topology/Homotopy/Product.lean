module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Product

@[expose] public section
noncomputable section
open scoped ContinuousMap

namespace ContinuousMap.Homotopic

variable {B F X Y : Type*}
  [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y]
  [ContractibleSpace B]

public theorem of_fiber_slice (b : B) (f g : C(B × F, Y))
    (h : (f.comp ((ContinuousMap.const F b).prodMk (ContinuousMap.id F))).Homotopic
      (g.comp ((ContinuousMap.const F b).prodMk (ContinuousMap.id F)))) :
    f.Homotopic g := by
  obtain ⟨p, ⟨H⟩⟩ := id_nullhomotopic B
  have hb : (ContinuousMap.id B).Homotopic (ContinuousMap.const B b) :=
    (show (ContinuousMap.id B).Homotopic (ContinuousMap.const B p) from ⟨H⟩).trans
      ⟨(H.evalAt b).symm.toHomotopyConst⟩
  let r : C(B × F, B × F) :=
    (ContinuousMap.const (B × F) b).prodMk ContinuousMap.snd
  have hr : (ContinuousMap.id (B × F)).Homotopic r := by
    convert (ContinuousMap.Homotopic.comp hb (.refl ContinuousMap.fst)).prodMk
      (.refl (ContinuousMap.snd : C(B × F, F))) using 1 <;> ext x <;> rfl
  have hf : f.Homotopic (f.comp r) := by
    simpa only [ContinuousMap.comp_id] using
      ContinuousMap.Homotopic.comp (.refl f) hr
  have hg : g.Homotopic (g.comp r) := by
    simpa only [ContinuousMap.comp_id] using
      ContinuousMap.Homotopic.comp (.refl g) hr
  have hfg : (f.comp r).Homotopic (g.comp r) := by
    convert ContinuousMap.Homotopic.comp h
      (.refl (ContinuousMap.snd : C(B × F, F))) using 1 <;> ext x <;> rfl
  exact hf.trans (hfg.trans hg.symm)

public theorem of_product_slice (e : X ≃ₜ B × F) (b : B) (f g : C(X, Y))
    (h : (f.comp ((e.symm : C(B × F, X)).comp
        ((ContinuousMap.const F b).prodMk (ContinuousMap.id F)))).Homotopic
      (g.comp ((e.symm : C(B × F, X)).comp
        ((ContinuousMap.const F b).prodMk (ContinuousMap.id F))))) :
    f.Homotopic g := by
  have hp := of_fiber_slice b
    (f.comp (e.symm : C(B × F, X))) (g.comp (e.symm : C(B × F, X)))
    (by simpa only [ContinuousMap.comp_assoc] using h)
  have hx := ContinuousMap.Homotopic.comp hp (.refl (e : C(X, B × F)))
  convert hx using 1 <;> ext x <;> simp

end ContinuousMap.Homotopic
