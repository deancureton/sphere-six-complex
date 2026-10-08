module

public import ForMathlib.Topology.Collar.OpenPush
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

@[expose] public section

noncomputable section

open Function Set Topology
open scoped NNReal


public def openCollarOfOpenEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y × TopologicalCollarParameter → X) (hf : IsOpenEmbedding f) :
    OpenTopologicalCollar X (range (fun y ↦ f (y, openCollarZero))) where
  neighborhood := ⟨range f, hf.isOpen_range⟩
  chart := ((hf.isEmbedding.comp (isEmbedding_prodMkLeft openCollarZero)).toHomeomorph.symm.prodCongr
    (Homeomorph.refl TopologicalCollarParameter)).trans hf.isEmbedding.toHomeomorph
  zero b := by
    have hb := (hf.isEmbedding.comp (isEmbedding_prodMkLeft openCollarZero)).toHomeomorph.apply_symm_apply b
    exact congrArg Subtype.val hb

public theorem locallyCollared_of_openEmbedding {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (B : Set X) (f : Y × TopologicalCollarParameter → X) (hf : IsOpenEmbedding f)
    (hb : ∀ p, f p ∈ B ↔ p.2 = openCollarZero) (y : Y) :
    ∃ V : Set X, V ⊆ B ∧ f (y, openCollarZero) ∈ V ∧
      IsOpen {x : B | x.1 ∈ V} ∧ ∃ c : OpenTopologicalCollar X V,
        ∀ p, (c.chart p).1 ∈ B → p.2 = openCollarZero := by
  let V := range (fun y ↦ f (y, openCollarZero))
  have he : V = B ∩ range f := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(hb _).mpr rfl, mem_range_self _⟩
    · rintro ⟨hx, p, rfl⟩
      have hp := (hb p).mp hx
      exact ⟨p.1, by rw [← hp]⟩
  refine ⟨V, ?_, mem_range_self y, ?_, openCollarOfOpenEmbedding f hf, ?_⟩
  · rw [he]
    exact inter_subset_left
  · have hv : {x : B | x.1 ∈ V} = Subtype.val ⁻¹' range f := by
      ext x
      simp [he]
    rw [hv]
    exact hf.isOpen_range.preimage continuous_subtype_val

  · intro p hp
    apply ((openCollarOfOpenEmbedding f hf).chart_mem_boundary p).mp
    change ((openCollarOfOpenEmbedding f hf).chart p).1 ∈ V
    rw [he]
    exact ⟨hp, ((openCollarOfOpenEmbedding f hf).chart p).2⟩


public def openCollarParameterScale (ε : ℝ) (hε : 0 < ε) :
    TopologicalCollarParameter ≃ₜ {t : ℝ≥0 // (t : ℝ) < ε} where
  toFun t := ⟨⟨ε * t.1, mul_nonneg hε.le t.2.1⟩, by
    change ε * (t : ℝ) < ε
    nlinarith [t.2.2]⟩
  invFun t := ⟨t.1 / ε, div_nonneg t.1.2 hε.le, (div_lt_one hε).mpr t.2⟩
  left_inv t := by
    apply Subtype.ext
    change ε * (t : ℝ) / ε = t
    field_simp
  right_inv t := by
    apply Subtype.ext
    apply NNReal.eq
    change ε * ((t.1 : ℝ) / ε) = t.1
    field_simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp
      (continuous_subtype_val : Continuous (fun t : {t : ℝ≥0 // (t : ℝ) < ε} ↦ t.1))).div_const ε

@[simp]
public theorem openCollarParameterScale_zero (ε : ℝ) (hε : 0 < ε) :
    ((openCollarParameterScale ε hε openCollarZero).1 : ℝ≥0) = 0 := by
  apply NNReal.eq
  change ε * 0 = 0
  simp

public theorem locallyCollared_of_halfSpaceChart {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (B : Set X)
    (e : OpenPartialHomeomorph (Y × ℝ≥0) X) (y : Y)
    (hy : (y, 0) ∈ e.source)
    (hB : ∀ p ∈ e.source, e p ∈ B ↔ p.2 = 0) :
    ∃ V : Set X, V ⊆ B ∧ e (y, 0) ∈ V ∧
      IsOpen {x : B | x.1 ∈ V} ∧ ∃ c : OpenTopologicalCollar X V,
        ∀ p, (c.chart p).1 ∈ B → p.2 = openCollarZero := by
  obtain ⟨U, T, hU, hT, hyU, h0T, hUT⟩ := isOpen_prod_iff.mp e.open_source y 0 hy
  obtain ⟨ε, hε, heT⟩ := Metric.isOpen_iff.mp hT 0 h0T
  let scale := openCollarParameterScale ε hε
  have ht (t : TopologicalCollarParameter) : (scale t).1 ∈ T := by
    apply heT
    simpa [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (scale t).1.2] using (scale t).2
  let k : U × TopologicalCollarParameter → e.source :=
    fun p ↦ ⟨(p.1.1, (scale p.2).1), hUT ⟨p.1.2, ht p.2⟩⟩
  have hs : IsOpen {t : ℝ≥0 | (t : ℝ) < ε} :=
    isOpen_lt continuous_subtype_val continuous_const
  have hk : IsOpenEmbedding k := by
    apply (IsOpenEmbedding.of_comp_iff k e.open_source.isOpenEmbedding_subtypeVal).mp
    exact hU.isOpenEmbedding_subtypeVal.prodMap
      (hs.isOpenEmbedding_subtypeVal.comp scale.isOpenEmbedding)
  let f : U × TopologicalCollarParameter → X := e.source.domRestrict e ∘ k
  have hf : IsOpenEmbedding f := e.isOpenEmbedding_restrict.comp hk
  have hb : ∀ p, f p ∈ B ↔ p.2 = openCollarZero := by
    intro p
    rw [show f p = e (k p).1 from rfl, hB _ (k p).2]
    change (scale p.2).1 = 0 ↔ p.2 = openCollarZero
    rw [← openCollarParameterScale_zero ε hε]
    exact ⟨fun h ↦ scale.injective (Subtype.ext h), fun h ↦ congrArg (fun t ↦ (scale t).1) h⟩
  have he : f (⟨y, hyU⟩, openCollarZero) = e (y, 0) := by
    change e (y, (scale openCollarZero).1) = _
    rw [openCollarParameterScale_zero]
  simpa only [he] using locallyCollared_of_openEmbedding B f hf hb ⟨y, hyU⟩
