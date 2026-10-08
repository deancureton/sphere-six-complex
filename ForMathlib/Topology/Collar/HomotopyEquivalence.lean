module

public import ForMathlib.Topology.Collar.OpenPush
public import ForMathlib.Topology.Homotopy.Equivalence

/-! # Homotopies into a collar neighborhood -/

@[expose] public section

open Set Topology ContinuousMap

namespace OpenTopologicalCollar

variable {X : Type*} [TopologicalSpace X] {B : Set X}

/-- A homotopy that moves the ambient space into a collar neighborhood, while keeping the
boundary inside that neighborhood throughout, makes the boundary inclusion a homotopy
equivalence. -/
theorem isHomotopyEquivalence_subtypeVal_of_homotopy
    (c : OpenTopologicalCollar X B) {f : C(X, X)}
    (H : (ContinuousMap.id X).Homotopy f)
    (hf : ∀ x, f x ∈ c.neighborhood)
    (hB : ∀ t (b : B), H (t, b.1) ∈ c.neighborhood) :
    IsHomotopyEquivalence (Subtype.val : B → X) := by
  let i : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let p : C(c.neighborhood, B) :=
    ⟨fun x ↦ (c.chart.symm x).1, c.chart.symm.continuous.fst⟩
  have hp (b : B) : p ⟨b.1, c.boundary_subset b.2⟩ = b := by
    have hb : (⟨b.1, c.boundary_subset b.2⟩ : c.neighborhood) =
        c.chart (b, openCollarZero) := Subtype.ext (c.zero b).symm
    simp [p, hb]
  let r : C(X, B) := p.comp ⟨fun x ↦ ⟨f x, hf x⟩, f.continuous.subtype_mk hf⟩
  let L : (ContinuousMap.id B).Homotopy (r.comp i) :=
    { toFun := fun z ↦ p ⟨H (z.1, z.2.1), hB z.1 z.2⟩
      continuous_toFun := p.continuous.comp
        ((H.continuous.comp (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _)
      map_zero_left := by
        intro b
        simpa using hp b
      map_one_left := by intro b; simp [r, i] }
  let F : C(X, c.neighborhood) := ⟨fun x ↦ ⟨f x, hf x⟩, f.continuous.subtype_mk hf⟩
  let q : C(X, B × TopologicalCollarParameter) := (c.chart.symm : C(_, _)).comp F
  let K : f.Homotopy (i.comp r) :=
    { toFun := fun z ↦
        (c.chart ((q z.2).1, ⟨(1 - (z.1 : ℝ)) * (q z.2).2.1,
          mul_nonneg (sub_nonneg.mpr z.1.2.2) (q z.2).2.2.1,
          lt_of_le_of_lt
            (mul_le_of_le_one_left (q z.2).2.2.1 (by linarith [z.1.2.1]))
            (q z.2).2.2.2⟩)).1
      continuous_toFun := by
        apply Continuous.subtype_val
        apply c.chart.continuous.comp
        apply Continuous.prodMk (q.continuous.comp continuous_snd).fst
        exact ((continuous_const.sub continuous_fst.subtype_val).mul
          (q.continuous.comp continuous_snd).snd.subtype_val).subtype_mk _
      map_zero_left := by
        intro x
        change (c.chart ((q x).1, _)).1 = f x
        simp only [Set.Icc.coe_zero, sub_zero, one_mul]
        exact congrArg Subtype.val (c.chart.apply_symm_apply (F x))
      map_one_left := by
        intro x
        change (c.chart ((q x).1, _)).1 = (r x).1
        simpa [openCollarZero, q, F, r, p] using c.zero (q x).1 }
  exact ⟨{ toFun := i
           invFun := r
           left_inv := ⟨L.symm⟩
           right_inv := ⟨(H.trans K).symm⟩ }, rfl⟩

end OpenTopologicalCollar
