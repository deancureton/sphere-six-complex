module

public import SphereSixComplex.Topology.OpenCollarPush
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

@[expose] public section

noncomputable section

open Function Set Topology
open scoped NNReal

namespace SphereSixComplex

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
      IsOpen {x : B | x.1 ∈ V} ∧ Nonempty (OpenTopologicalCollar X V) := by
  let V := range (fun y ↦ f (y, openCollarZero))
  have he : V = B ∩ range f := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(hb _).mpr rfl, mem_range_self _⟩
    · rintro ⟨hx, p, rfl⟩
      have hp := (hb p).mp hx
      exact ⟨p.1, by rw [← hp]⟩
  refine ⟨V, ?_, mem_range_self y, ?_, ⟨openCollarOfOpenEmbedding f hf⟩⟩
  · rw [he]
    exact inter_subset_left
  · have hv : {x : B | x.1 ∈ V} = Subtype.val ⁻¹' range f := by
      ext x
      simp [he]
    rw [hv]
    exact hf.isOpen_range.preimage continuous_subtype_val

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
      IsOpen {x : B | x.1 ∈ V} ∧ Nonempty (OpenTopologicalCollar X V) := by
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

public theorem locallyCollared_of_overlapping_halfSpaceEmbedding
    {X Z Y : Type*} [TopologicalSpace X] [TopologicalSpace Z] [TopologicalSpace Y]
    (B : Set X) (i : X → Z) (hi : IsOpenEmbedding i)
    (f : Y × ℝ≥0 → Z) (hf : IsOpenEmbedding f) (x : X) (y : Y)
    (hxy : f (y, 0) = i x)
    (hB : ∀ p q, f p = i q → (q ∈ B ↔ p.2 = 0)) :
    ∃ V : Set X, V ⊆ B ∧ x ∈ V ∧ IsOpen {b : B | b.1 ∈ V} ∧
      Nonempty (OpenTopologicalCollar X V) := by
  let _ : Nonempty X := ⟨x⟩
  let _ : Nonempty (Y × ℝ≥0) := ⟨(y, 0)⟩
  let e : OpenPartialHomeomorph (Y × ℝ≥0) X := (hf.toOpenPartialHomeomorph f).trans (hi.toOpenPartialHomeomorph i).symm
  have hsource (p : Y × ℝ≥0) : p ∈ e.source ↔ f p ∈ range i := by
    simp [e]
  have he (p : Y × ℝ≥0) (hp : p ∈ e.source) : i (e p) = f p := by
    simp only [e, OpenPartialHomeomorph.trans_apply,
      IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    exact (hi.toOpenPartialHomeomorph i).right_inv (by simpa using (hsource p).mp hp)
  have hy : (y, 0) ∈ e.source := (hsource _).mpr ⟨x, hxy.symm⟩
  have hx : e (y, 0) = x := hi.injective ((he _ hy).trans hxy)
  have hb : ∀ p ∈ e.source, e p ∈ B ↔ p.2 = 0 :=
    fun p hp ↦ hB p (e p) (he p hp).symm
  simpa only [hx] using locallyCollared_of_halfSpaceChart B e y hy hb

end SphereSixComplex
