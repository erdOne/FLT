import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.OpenSubgroup

lemma Doset.isOpen_doset {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]
    (H U : Subgroup G) (hU : IsOpen (X := G) U) (x) : IsOpen (X := G) (doset x H U) :=
  doset_union_leftCoset H U x ▸ isOpen_iUnion fun _ ↦ hU.smul _

lemma Doset.isOpen_doset' {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]
    (U H : Subgroup G) (hU : IsOpen (X := G) U) (x) : IsOpen (X := G) (doset x U H) :=
  doset_union_rightCoset U H x ▸ isOpen_iUnion fun _ ↦ hU.smul _

instance {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G] (H : Subgroup G)
    (U : OpenSubgroup G) [CompactSpace (G ⧸ H)] : Finite (Doset.Quotient (G := G) H U) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (X := G ⧸ H)
    (fun x : Doset.Quotient (G := G) H U ↦ QuotientGroup.mk '' Doset.doset x.out⁻¹ U H) (by
    rintro x
    show IsOpen (X := G) _
    convert Doset.isOpen_doset' U H U.2 x.out⁻¹
    refine (QuotientGroup.preimage_image_mk _ _).trans ?_
    apply subset_antisymm
    · intro y hy
      simp only [Set.mem_iUnion, Set.mem_preimage, Subtype.exists, exists_prop,
        Doset.quotToDoset, Doset.mem_doset] at hy ⊢
      obtain ⟨a, ha, b, hb, c, hc, e⟩ := hy
      refine ⟨b, hb, c * a⁻¹, mul_mem hc (inv_mem ha), ?_⟩
      rw [← mul_assoc, ← e, mul_assoc, mul_inv_cancel, mul_one]
    · refine le_trans ?_ (Set.subset_iUnion _ 1)
      simp) (by
    rintro x -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [Set.mem_iUnion, Set.mem_image, Doset.mem_doset]
    obtain ⟨u, h, hu, hh, e⟩ := Doset.mk_out_eq_mul H U x⁻¹
    exact ⟨Doset.mk _ _ x⁻¹, x, ⟨h, hh, u, hu, by simp [e]⟩, rfl⟩)
  suffices t.toSet = Set.univ by rw [← Set.finite_univ_iff, ← this]; exact t.finite_toSet
  simp only [Set.eq_univ_iff_forall, Finset.mem_coe]
  intro x
  have := @ht (QuotientGroup.mk x.out⁻¹) trivial
  simp only [Set.mem_iUnion, Set.mem_image, Doset.mem_doset, SetLike.mem_coe, QuotientGroup.eq,
    exists_prop] at this
  obtain ⟨i, hit, _, ⟨u, hu, h, hh, rfl⟩, hmem⟩ := this
  suffices x = i from this ▸ hit
  rw [← Doset.out_eq' _ _ x, ← Doset.out_eq' _ _ i, Doset.eq]
  replace hmem := mul_mem hh hmem
  simp only [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] at hmem
  exact ⟨_, hmem, u, hu, by simp⟩
