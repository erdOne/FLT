import FLT.AutomorphicForm.Basic
import FLT.AutomorphicForm.DoubleCoset
import Mathlib

variable (GA GK ZA : Type*) [Group GK] [Group GA] [CommGroup ZA]
variable [TopologicalSpace GA] [TopologicalGroup GA]
variable [MulAction GK GA] [IsScalarTower GK GA GA]
variable [MulAction ZA GA] [IsScalarTower ZA GA GA] [SMulCommClass ZA GA GA] -- maybe use `IsCentralScalar` instead
variable (W : Type*) [AddCommGroup W] [DistribMulAction GK W] [DistribMulAction ZA W]
variable (R : Type*) [CommRing R] [Module R W] [SMulCommClass R GK W] [SMulCommClass R ZA W]

def subgroupIn (M N : Type*) [Group M] [Group N] [MulAction M N]
  [IsScalarTower M N N] : Subgroup N := (MonoidHom.smulOneHom (M := M) (N := N)).range

def FixedPonts.submodule (R G M : Type*) [Semiring R] [Monoid G] [AddCommMonoid M] [Module R M]
    [DistribMulAction G M] [SMulCommClass R G M] : Submodule R M where
  __ := FixedPoints.addSubmonoid G M
  smul_mem' r m hm a := by rw [← smul_comm, hm a]

lemma Subgroup.mem_sup_of_le_normalizer {C : Type*} [Group C] {s t : Subgroup C}
    (h : t ≤ normalizer s) {x : C} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro h
    rw [sup_eq_closure] at h
    induction h using closure_induction with
    | mem x hx =>
      cases hx with
      | inl h => exact ⟨x, h, 1, one_mem t, mul_one x⟩
      | inr h => exact ⟨1, one_mem s, x, h, one_mul x⟩
    | one => exact ⟨1, one_mem s, 1, one_mem t, one_mul 1⟩
    | mul x y hx hy hx' hy' =>
      obtain ⟨xs, hxs, xt, hxt, rfl⟩ := hx'
      obtain ⟨ys, hys, yt, hyt, rfl⟩ := hy'
      exact ⟨_, mul_mem hxs ((h hxt ys).mp hys), _, mul_mem hxt hyt, by group⟩
    | inv x hx hx' =>
      obtain ⟨xs, hxs, xt, hxt, rfl⟩ := hx'
      exact ⟨_, (h (inv_mem hxt) _).mp (inv_mem hxs), xt⁻¹, inv_mem hxt, by group⟩
  · rintro ⟨xs, hxs, xt, hxt, rfl⟩
    exact mul_mem_sup hxs hxt

local notation3 "gk" => subgroupIn GK GA
local notation3 "za" => subgroupIn ZA GA

variable (U : OpenSubgroup GA)

def AutomorphicForm.fixed : Submodule R (AutomorphicForm GA GK ZA W) :=
  FixedPonts.submodule R U.1 (AutomorphicForm GA GK ZA W)

variable {GA GK ZA W R U} in
@[simp]
lemma AutomorphicForm.mem_fixed {f} : f ∈ fixed GA GK ZA W R U ↔ HasLevel f U := by
  show (∀ _, _) ↔ ∀ _, _
  simp_rw [AutomorphicForm.ext_iff, funext_iff, forall_comm (α := U.1), Subtype.forall]
  rfl

@[simps]
noncomputable
def AutomorphicForm.fixedPointsToFun :
    fixed GA GK ZA W R U →ₗ[R] (Doset.Quotient (G := GA) gk ↑(U.1 ⊔ za)) → W where
  toFun f x := f.1.toFun x.out
  map_add' := by simp [funext_iff]
  map_smul' := by simp [funext_iff]

lemma AutomorphicForm.fixedPointsToFun_injective :
    Function.Injective (fixedPointsToFun GA GK ZA W R U) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  ext x
  obtain ⟨_, u, ⟨g, rfl⟩, hu', e⟩ := Doset.mk_out_eq_mul (subgroupIn GK GA) ↑(U.1 ⊔ za) x
  have : f.1.toFun _ = 0 := congr_fun hf (Doset.mk _ _ x)
  have H : za ≤ Subgroup.center GA := by rintro _ ⟨x, rfl⟩; simp [Subgroup.mem_center_iff]
  obtain ⟨u, hu, _, ⟨z, rfl⟩, rfl⟩ :=
    (Subgroup.mem_sup_of_le_normalizer (H.trans Subgroup.center_le_normalizer)).mp hu'
  simpa [e, mul_smul_comm, mem_fixed.mp f.2 _ _ hu, smul_eq_zero_iff_eq] using this

def AutomorphicForm.toFunSubmodule (g : GA) : Submodule R W where
  carrier := { x | ∀ z : ZA, ∀ u ∈ U, ∀ a : GK, g * (z • u) * g⁻¹ = a • 1 → a • x = z • x }
  add_mem' {x y} hx hy z u hu a e := by simp [hx z u hu a e, hy z u hu a e]
  zero_mem' z u hu a e := by simp
  smul_mem' r x hx z u hu a e := by rw [← smul_comm, hx z u hu a e, smul_comm]

lemma AutomorphicForm.range_fixedPointsToFun [SMulCommClass ZA GK W] :
    LinearMap.range (fixedPointsToFun GA GK ZA W R U) = Submodule.pi Set.univ fun x ↦
      toFunSubmodule GA GK ZA W R U x.out := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩ x - z u hu a e
    simp only [fixedPointsToFun_apply, Subgroup.smul_def]
    apply_fun (· • (x.out • f.1)) at e
    simp only [← mul_smul, inv_mul_cancel_right, smul_one_mul] at e
    apply_fun (AutomorphicForm.toFun · 1) at e
    simpa [mul_smul, (mem_fixed.mp f.2) _ _ hu] using e.symm
  · intro f hf
    have (x) : ∃ g : GK, ∃ z : ZA, ∃ u ∈ U,
        (Doset.mk (subgroupIn GK GA) ↑(U.1 ⊔ za) x).out = g • x * z • u := by
      obtain ⟨_, u, ⟨g, rfl⟩, hu', e⟩ := Doset.mk_out_eq_mul (subgroupIn GK GA) ↑(U.1 ⊔ za) x
      have H : za ≤ Subgroup.center GA := by rintro _ ⟨x, rfl⟩; simp [Subgroup.mem_center_iff]
      obtain ⟨u, hu, _, ⟨z, rfl⟩, rfl⟩ :=
        (Subgroup.mem_sup_of_le_normalizer (H.trans Subgroup.center_le_normalizer)).mp hu'
      exact ⟨g, z, u, hu, by simpa using e⟩
    choose g z u hu e using this
    have hf' : HasLevel (fun σ ↦ (g σ)⁻¹ • (z σ)⁻¹ • f (Doset.mk _ _ σ)) U.1 := by
      intro σ u₀ hu₀
      have : Doset.mk (subgroupIn GK GA) ↑(U.1 ⊔ za) (σ * u₀) = Doset.mk _ _ σ :=
        .symm <| Doset.mk_eq_of_doset_eq (Doset.rel_iff.mpr
          ⟨_, ⟨1, rfl⟩, u₀, Subgroup.mem_sup_left hu₀, by simp⟩)
      simp_rw [this, eq_inv_smul_iff (g := g σ), ← smul_comm (z _)⁻¹,
        inv_smul_eq_iff, ← mul_smul]
      refine hf _ trivial _ ((u σ)⁻¹ * u₀ * u (σ * u₀))
        (mul_mem (mul_mem (inv_mem (hu _)) hu₀) (hu _)) _ ?_
      nth_rw 1 [e]
      rw [← this, e, mul_inv_eq_iff_eq_mul]
      simp only [smul_mul_assoc, mul_smul_comm, mul_assoc, mul_inv_cancel_left, mul_smul,
        inv_smul_smul, one_mul]
    let f' : AutomorphicForm GA GK ZA W :=
    { toFun σ := (g σ)⁻¹ • (z σ)⁻¹ • f (Doset.mk _ _ σ)
      left_invt δ σ := by
        have : Doset.mk (subgroupIn GK GA) ↑(U.1 ⊔ za) (δ • σ) = Doset.mk _ _ σ :=
          .symm <| Doset.mk_eq_of_doset_eq (Doset.rel_iff.mpr
            ⟨_, ⟨δ, rfl⟩, 1, one_mem _, by simp⟩)
        simp only [this, inv_smul_eq_iff, ← mul_smul]
        rw [eq_comm, ← eq_inv_smul_iff, ← smul_comm (z σ)⁻¹, inv_smul_eq_iff, ← mul_smul]
        refine hf _ trivial _ ((u (δ • σ))⁻¹ * u σ) (mul_mem (inv_mem (hu _)) (hu _)) _ ?_
        nth_rw 1 [← this]
        rw [e, e, mul_inv_eq_iff_eq_mul]
        simp only [smul_mul_assoc, mul_smul_comm, mul_assoc, mul_inv_cancel_left, mul_smul,
          inv_smul_smul, one_mul]
      has_character σ z₀ := by
        have : Doset.mk (subgroupIn GK GA) ↑(U.1 ⊔ za) (z₀ • σ) = Doset.mk _ _ σ :=
          .symm <| Doset.mk_eq_of_doset_eq (Doset.rel_iff.mpr
            ⟨_, ⟨1, rfl⟩, _, Subgroup.mem_sup_right ⟨z₀, rfl⟩, by simp⟩)
        simp_rw [this, smul_comm z₀, eq_inv_smul_iff (g := g σ), ← smul_comm (z _)⁻¹,
          inv_smul_eq_iff, ← mul_smul]
        refine hf _ trivial _ ((u σ)⁻¹ * u (z₀ • σ)) (mul_mem (inv_mem (hu _)) (hu _)) _ ?_
        nth_rw 1 [e]
        rw [← this, e, mul_inv_eq_iff_eq_mul]
        simp only [mul_smul_comm, smul_mul_assoc, mul_smul, mul_assoc, mul_inv_cancel_left, one_mul,
          inv_smul_smul, ← smul_comm (z _)⁻¹]
        simp only [← smul_comm (z σ), smul_inv_smul, smul_comm z₀]
      right_invt := ⟨_, hf'⟩ }
    refine ⟨⟨f', mem_fixed.mpr hf'⟩, ?_⟩
    ext x
    simp only [fixedPointsToFun_apply, Quotient.out_eq, f']
    rw [inv_smul_eq_iff, eq_comm]
    refine hf _ trivial _ (u x.out)⁻¹ (inv_mem (hu _)) _ ?_
    rw [mul_inv_eq_iff_eq_mul, mul_smul_comm, ← smul_mul_assoc, mul_inv_eq_iff_eq_mul,
      inv_smul_eq_iff, smul_mul_assoc, one_mul, ← mul_smul_comm, ← e]
    simp only [Quotient.out_eq]

lemma AutomorphicForm.toFunSubmodule_eq (g : GA) :
    toFunSubmodule GA GK ZA W R U g = FixedPoints.submodule

variable [IsNoetherian R W] [CompactSpace (GA ⧸ subgroupIn GK GA)]

instance : IsNoetherian R (AutomorphicForm.fixed GA GK ZA W R U) :=
  let U' : OpenSubgroup GA := ⟨U.1 ⊔ za, Subgroup.isOpen_mono le_sup_left U.2⟩
  have : Finite (Doset.Quotient (G := GA) gk ↑(U.1 ⊔ za)) :=
    inferInstanceAs (Finite (Doset.Quotient (G := GA) ↑gk U'))
  isNoetherian_of_injective _ (AutomorphicForm.fixedPointsToFun_injective GA GK ZA W R U)
