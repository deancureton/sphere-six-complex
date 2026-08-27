module

public import SphereSixComplex.Topology.OrderedCechRealization
public import SphereSixComplex.Topology.HorizontalTotalHomotopy

/-!
# Normalization of the ordered Čech complex

For a contravariant diagram of chain complexes on the nonempty finite subsets of a totally
ordered index type, the ordered Čech bicomplex (all tuples) retracts onto its normalized
subcomplex (strictly increasing tuples, one summand per support) through the semi-ordered
bicomplex (weakly increasing tuples).  The retraction is the sort-with-sign operator followed by
killing tuples with a repetition, and both steps are homotopic to the identity through the two
explicit homotopies of the Stacks Project, Tag 01FM, `lemma-alternating-usual`:
`c ∘ π` is homotopic to the identity, so the alternating complex is a homotopy retract of the
full ordered complex.

Everything is stated at the level of bicomplexes and then totalized.  The index type need not be
finite; when it is, the normalized bicomplex vanishes in simplicial degrees at least its
cardinality.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Finsupp SphereSixComplex.OrderedCechTuple

namespace SphereSixComplex

namespace SupportChainModels

variable {ι : Type} [LinearOrder ι] (M : SupportChainModels ι)

/-! ### Sorting with sign -/

omit [LinearOrder ι] in
/-- The identity operator is admissible on every class. -/
public theorem admissible_id (P : TupleClass ι) (n : ℕ) :
    Admissible P P (LinearMap.id : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) where
  range_subset a _ b hb := by
    have hb' : b ∈ (single a (1 : ℤ)).support := by simpa using hb
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hb')
    exact subset_rfl
  preserves a ha b hb := by
    have hb' : b ∈ (single a (1 : ℤ)).support := by simpa using hb
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hb')
    exact ha

public theorem admissible_sortWithSign (n : ℕ) :
    Admissible TupleClass.all TupleClass.monotone
      (sortWithSign (n + 1) : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) where
  range_subset _ _ _ hb := range_subset_of_mem_support_sortWithSign hb
  preserves _ _ _ hb := monotone_of_mem_support_sortWithSign hb

public theorem admissible_sortWithSign_all (n : ℕ) :
    Admissible TupleClass.all TupleClass.all
      (sortWithSign (n + 1) : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) where
  range_subset _ _ _ hb := range_subset_of_mem_support_sortWithSign hb
  preserves _ _ _ _ := trivial

public theorem admissible_id_monotone_all (n : ℕ) :
    Admissible TupleClass.monotone TupleClass.all
      (LinearMap.id : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) where
  range_subset a _ b hb := by
    have hb' : b ∈ (single a (1 : ℤ)).support := by simpa using hb
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hb')
    exact subset_rfl
  preserves _ _ _ _ := trivial

public theorem admissible_sortHomotopy (n : ℕ) :
    Admissible TupleClass.all TupleClass.all
      (sortHomotopy (n + 1) : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 2)) where
  range_subset _ _ _ hb := range_subset_of_mem_support_sortHomotopy hb
  preserves _ _ _ _ := trivial

/-- The sort-with-sign operator `κ` of Stacks 01FM as a map of bicomplexes into the
semi-ordered bicomplex. -/
public def sortMap : M.cechComplex TupleClass.all ⟶ M.cechComplex TupleClass.monotone :=
  M.realizeChainMap TupleClass.all TupleClass.monotone (fun n ↦ sortWithSign (n + 1))
    admissible_sortWithSign (fun _ a _ ↦ boundary_sortWithSign (single a 1))

/-- The inclusion of the semi-ordered bicomplex into the full ordered Čech bicomplex. -/
public def monotoneInclusion : M.cechComplex TupleClass.monotone ⟶ M.cechComplex TupleClass.all :=
  M.realizeChainMap TupleClass.monotone TupleClass.all (fun _ ↦ LinearMap.id)
    admissible_id_monotone_all (fun _ _ _ ↦ rfl)

/-- Sorting fixes weakly increasing tuples. -/
public theorem monotoneInclusion_sortMap : M.monotoneInclusion ≫ M.sortMap = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, monotoneInclusion, sortMap,
    realizeChainMap_f, realizeChainMap_f]
  exact (M.realize_comp _ _ _ (admissible_id_monotone_all n) (admissible_sortWithSign n)).symm.trans
    ((M.realize_congr _ _ fun a ha ↦ by
      simpa using sortWithSign_single_of_monotone ha).trans (M.realize_id _))

/-- The composite of sorting with sign and the inclusion of the semi-ordered bicomplex is the
realization of `κ` on the full bicomplex. -/
public theorem sortMap_monotoneInclusion :
    M.sortMap ≫ M.monotoneInclusion =
      M.realizeChainMap TupleClass.all TupleClass.all (fun n ↦ sortWithSign (n + 1))
        admissible_sortWithSign_all (fun _ a _ ↦ boundary_sortWithSign (single a 1)) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, monotoneInclusion, sortMap, realizeChainMap_f, realizeChainMap_f,
    realizeChainMap_f]
  exact (M.realize_comp _ _ _ (admissible_sortWithSign n) (admissible_id_monotone_all n)).symm.trans
    (M.realize_congr _ _ fun _ _ ↦ rfl)

/-- The first homotopy of Stacks 01FM: sorting with sign is homotopic to the identity. -/
public def sortHomotopyMap : Homotopy (M.sortMap ≫ M.monotoneInclusion) (𝟙 _) :=
  (Homotopy.ofEq M.sortMap_monotoneInclusion).trans
    ((M.realizeHomotopy TupleClass.all TupleClass.all
      (T := fun _ ↦ LinearMap.id) (T' := fun n ↦ sortWithSign (n + 1))
      (hT := admissible_id _) (hT' := admissible_sortWithSign_all)
      (hcomm := fun _ _ _ ↦ rfl) (hcomm' := fun n a _ ↦ boundary_sortWithSign (single a 1))
      (fun n ↦ sortHomotopy (n + 1)) admissible_sortHomotopy
      (fun n a _ ↦ boundary_sortHomotopy_add (single a 1))
      (fun a _ ↦ by
        have := boundary_sortHomotopy_add (single a 1)
        rw [show sortHomotopy 0 = (0 : Formal ι 0 →ₗ[ℤ] Formal ι 1) from rfl,
          LinearMap.zero_apply, add_zero] at this
        exact this)).symm.trans
      (Homotopy.ofEq (M.realizeChainMap_id TupleClass.all (admissible_id _) fun _ _ _ ↦ rfl)))

/-! ### Killing repetitions -/

public theorem admissible_strictProjection (n : ℕ) :
    Admissible TupleClass.monotone TupleClass.strictMono
      (strictProjection (n + 1) : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) where
  range_subset _ _ _ hb := range_subset_of_mem_support_strictProjection hb
  preserves _ _ _ hb := strictMono_of_mem_support_strictProjection hb

public theorem admissible_strictProjection_monotone (n : ℕ) :
    Admissible TupleClass.monotone TupleClass.monotone
      (strictProjection (n + 1) : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) where
  range_subset _ _ _ hb := range_subset_of_mem_support_strictProjection hb
  preserves _ _ _ hb := (strictMono_of_mem_support_strictProjection hb).monotone

public theorem admissible_id_strictMono_monotone (n : ℕ) :
    Admissible TupleClass.strictMono TupleClass.monotone
      (LinearMap.id : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 1)) where
  range_subset a _ b hb := by
    have hb' : b ∈ (single a (1 : ℤ)).support := by simpa using hb
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hb')
    exact subset_rfl
  preserves a ha b hb := by
    have hb' : b ∈ (single a (1 : ℤ)).support := by simpa using hb
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hb')
    exact ha.monotone

public theorem admissible_firstRepeatHomotopy (n : ℕ) :
    Admissible TupleClass.monotone TupleClass.monotone
      (firstRepeatHomotopy (n + 1) : Formal ι (n + 1) →ₗ[ℤ] Formal ι (n + 2)) where
  range_subset _ _ _ hb := range_subset_of_mem_support_firstRepeatHomotopy hb
  preserves _ ha _ hb := monotone_of_mem_support_firstRepeatHomotopy ha hb

/-- Kill every weakly increasing tuple with a repetition. -/
public def strictProjectionMap :
    M.cechComplex TupleClass.monotone ⟶ M.cechComplex TupleClass.strictMono :=
  M.realizeChainMap TupleClass.monotone TupleClass.strictMono (fun n ↦ strictProjection (n + 1))
    admissible_strictProjection (fun _ _ ha ↦ boundary_strictProjection ha)

/-- The inclusion of the normalized bicomplex into the semi-ordered bicomplex. -/
public def strictInclusion :
    M.cechComplex TupleClass.strictMono ⟶ M.cechComplex TupleClass.monotone :=
  M.realizeChainMap TupleClass.strictMono TupleClass.monotone (fun _ ↦ LinearMap.id)
    admissible_id_strictMono_monotone (fun _ _ _ ↦ rfl)

/-- Killing repetitions fixes strictly increasing tuples. -/
public theorem strictInclusion_strictProjectionMap :
    M.strictInclusion ≫ M.strictProjectionMap = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, strictInclusion, strictProjectionMap,
    realizeChainMap_f, realizeChainMap_f]
  exact (M.realize_comp _ _ _ (admissible_id_strictMono_monotone n)
    (admissible_strictProjection n)).symm.trans
    ((M.realize_congr _ _ fun a ha ↦ by
      simpa using strictProjection_single_of_strictMono ha).trans (M.realize_id _))

/-- The composite of killing repetitions and the inclusion of the normalized bicomplex is the
realization of `e` on the semi-ordered bicomplex. -/
public theorem strictProjectionMap_strictInclusion :
    M.strictProjectionMap ≫ M.strictInclusion =
      M.realizeChainMap TupleClass.monotone TupleClass.monotone (fun n ↦ strictProjection (n + 1))
        admissible_strictProjection_monotone (fun _ _ ha ↦ boundary_strictProjection ha) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, strictInclusion, strictProjectionMap, realizeChainMap_f,
    realizeChainMap_f, realizeChainMap_f]
  exact (M.realize_comp _ _ _ (admissible_strictProjection n)
    (admissible_id_strictMono_monotone n)).symm.trans (M.realize_congr _ _ fun _ _ ↦ rfl)

/-- The second homotopy of Stacks 01FM: killing repetitions is homotopic to the identity of the
semi-ordered bicomplex. -/
public def firstRepeatHomotopyMap :
    Homotopy (M.strictProjectionMap ≫ M.strictInclusion) (𝟙 _) :=
  (Homotopy.ofEq M.strictProjectionMap_strictInclusion).trans
    ((M.realizeHomotopy TupleClass.monotone TupleClass.monotone
      (T := fun _ ↦ LinearMap.id) (T' := fun n ↦ strictProjection (n + 1))
      (hT := admissible_id _) (hT' := admissible_strictProjection_monotone)
      (hcomm := fun _ _ _ ↦ rfl) (hcomm' := fun _ _ ha ↦ boundary_strictProjection ha)
      (fun n ↦ firstRepeatHomotopy (n + 1)) admissible_firstRepeatHomotopy
      (fun _ _ ha ↦ boundary_firstRepeatHomotopy_add ha)
      (fun a _ ↦ by
        rw [show firstRepeatHomotopy 1 = (0 : Formal ι 1 →ₗ[ℤ] Formal ι 2) from rfl,
          LinearMap.zero_apply, map_zero, strictProjection_single_of_strictMono (strictMono_fin_one a),
          LinearMap.id_apply, sub_self])).symm.trans
      (Homotopy.ofEq (M.realizeChainMap_id TupleClass.monotone (admissible_id _) fun _ _ _ ↦ rfl)))

/-! ### The normalization retraction -/

/-- The inclusion of the normalized bicomplex into the ordered Čech bicomplex. -/
public def normalizedInclusion :
    M.cechComplex TupleClass.strictMono ⟶ M.cechComplex TupleClass.all :=
  M.strictInclusion ≫ M.monotoneInclusion

/-- The normalization projection: sort with sign, then kill repetitions. -/
public def normalizedProjection :
    M.cechComplex TupleClass.all ⟶ M.cechComplex TupleClass.strictMono :=
  M.sortMap ≫ M.strictProjectionMap

public theorem normalizedInclusion_normalizedProjection :
    M.normalizedInclusion ≫ M.normalizedProjection = 𝟙 _ := by
  rw [normalizedInclusion, normalizedProjection, Category.assoc,
    ← Category.assoc M.monotoneInclusion, monotoneInclusion_sortMap, Category.id_comp,
    strictInclusion_strictProjectionMap]

/-- The composite contraction: the ordered Čech bicomplex retracts onto its normalization. -/
public def normalizationHomotopy :
    Homotopy (M.normalizedProjection ≫ M.normalizedInclusion) (𝟙 _) :=
  (Homotopy.ofEq (by simp only [normalizedProjection, normalizedInclusion, Category.assoc])).trans
    (((M.firstRepeatHomotopyMap.compLeft M.sortMap).compRight M.monotoneInclusion).trans
      ((Homotopy.ofEq (by simp)).trans M.sortHomotopyMap))

/-- Normalization is a homotopy equivalence of bicomplexes. -/
public def normalizationHomotopyEquiv :
    HomotopyEquiv (M.cechComplex TupleClass.all) (M.cechComplex TupleClass.strictMono) where
  hom := M.normalizedProjection
  inv := M.normalizedInclusion
  homotopyHomInvId := M.normalizationHomotopy
  homotopyInvHomId := Homotopy.ofEq M.normalizedInclusion_normalizedProjection

/-! ### Totalization -/

/-- The totalized normalization projection. -/
public def totalNormalizedProjection :
    M.cechTotal TupleClass.all ⟶ M.cechTotal TupleClass.strictMono :=
  HomologicalComplex₂.total.map M.normalizedProjection (ComplexShape.down ℕ)

/-- The totalized normalization inclusion. -/
public def totalNormalizedInclusion :
    M.cechTotal TupleClass.strictMono ⟶ M.cechTotal TupleClass.all :=
  HomologicalComplex₂.total.map M.normalizedInclusion (ComplexShape.down ℕ)

public theorem totalNormalizedInclusion_totalNormalizedProjection :
    M.totalNormalizedInclusion ≫ M.totalNormalizedProjection = 𝟙 _ := by
  rw [totalNormalizedInclusion, totalNormalizedProjection, ← HomologicalComplex₂.total.map_comp,
    normalizedInclusion_normalizedProjection, HomologicalComplex₂.total.map_id]

/-- The totalized contraction of the degenerate (non-normalized) part. -/
public def totalNormalizationHomotopy :
    Homotopy (M.totalNormalizedProjection ≫ M.totalNormalizedInclusion) (𝟙 _) :=
  (Homotopy.ofEq (HomologicalComplex₂.total.map_comp _ _ _).symm).trans
    ((horizontalTotalHomotopy M.normalizationHomotopy).trans
      (Homotopy.ofEq (HomologicalComplex₂.total.map_id _ _)))

/-- Normalization is a homotopy equivalence of total complexes. -/
public def totalNormalizationHomotopyEquiv :
    HomotopyEquiv (M.cechTotal TupleClass.all) (M.cechTotal TupleClass.strictMono) where
  hom := M.totalNormalizedProjection
  inv := M.totalNormalizedInclusion
  homotopyHomInvId := M.totalNormalizationHomotopy
  homotopyInvHomId := Homotopy.ofEq M.totalNormalizedInclusion_totalNormalizedProjection

/-! ### Vanishing above the cardinality of the index type -/

/-- There are no strictly increasing tuples longer than the index type. -/
public theorem isZero_cechObject_strictMono [Fintype ι] {n : ℕ} (hn : Fintype.card ι ≤ n) :
    IsZero (M.cechObject TupleClass.strictMono n) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective a ha.injective
  rw [Fintype.card_fin] at this
  omega

end SupportChainModels

end SphereSixComplex
