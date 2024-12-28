import Mathlib.Topology.Algebra.OpenSubgroup

variable (GA GK ZA : Type*) [Group GK] [Group GA] [CommGroup ZA]
variable [TopologicalSpace GA] [TopologicalGroup GA]
variable [MulAction GK GA] [IsScalarTower GK GA GA]
variable [MulAction ZA GA] [IsScalarTower ZA GA GA] [SMulCommClass ZA GA GA] -- maybe use `IsCentralScalar` instead
variable (W : Type*) [AddCommGroup W] [DistribMulAction GK W] [DistribMulAction ZA W]

instance (priority := 10) (A B C : Type*) [Mul A] [Mul B] [MulOneClass C] [SMul A C] [SMul B C]
    [IsScalarTower B C C] [SMulCommClass A C C] : SMulCommClass A B C := by
  constructor
  intros a b c
  rw [← one_mul c, ← smul_mul_assoc b, ← mul_smul_comm, smul_mul_assoc, one_mul, one_mul]

variable {GA W} in
def AutomorphicForm.HasLevel (f : GA → W) (U : Subgroup GA) : Prop :=
  ∀ (g : GA), ∀ u ∈ U, f (g * u) = f g

@[ext]
structure AutomorphicForm : Type _ where
  toFun : GA → W
  left_invt : ∀ (δ : GK) (g : GA), toFun (δ • g) = δ • toFun g
  has_character : ∀ (g : GA) (z : ZA), toFun (z • g) = z • toFun g
  right_invt : ∃ U : OpenSubgroup GA, AutomorphicForm.HasLevel toFun U

variable {GA GK ZA W}

namespace AutomorphicForm

attribute [simp] left_invt has_character

instance : CoeFun (AutomorphicForm GA GK ZA W) (fun _ ↦ GA → W) where
  coe := AutomorphicForm.toFun

noncomputable
def level (f : AutomorphicForm GA GK ZA W) : OpenSubgroup GA := f.right_invt.choose

lemma hasLevel_level (f : AutomorphicForm GA GK ZA W) : HasLevel f f.level :=
  f.right_invt.choose_spec

instance : AddCommGroup (AutomorphicForm GA GK ZA W) where
  add f g :=
  { toFun := f + g
    left_invt := by simp [smul_add]
    has_character := by simp [smul_add]
    right_invt := ⟨f.level ⊓ g.level, fun σ u ⟨h₁, h₂⟩ ↦ by
      simp [f.hasLevel_level _ _ h₁, g.hasLevel_level _ _ h₂]⟩ }
  add_assoc _ _ _ := by ext; exact add_assoc _ _ _
  zero := ⟨0, by simp, by simp, ⟨⊤, by simp [HasLevel]⟩⟩
  zero_add _ := by ext; exact zero_add _
  add_zero _ := by ext; exact add_zero _
  nsmul n f := ⟨n • f, by simp [smul_comm (M := ℕ)], by simp [smul_comm (M := ℕ)],
    f.level, fun σ u h ↦ by simp [f.hasLevel_level _ _ h]⟩
  nsmul_zero _ := by ext; exact zero_nsmul _
  nsmul_succ _ _ := by ext; exact succ_nsmul _ _
  neg f := ⟨-f, by simp, by simp, f.level, fun σ u hu ↦ by
    simp [f.hasLevel_level _ _ hu]⟩
  zsmul n f := ⟨n • f, by simp [smul_comm (M := ℤ)], by simp [smul_comm (M := ℤ)],
    f.level, fun σ u h ↦ by simp [f.hasLevel_level _ _ h]⟩
  zsmul_zero' _ := by ext; exact zero_zsmul _
  zsmul_succ' _ _ := by ext; exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' _ _ := by ext; exact SubNegMonoid.zsmul_neg' _ _
  neg_add_cancel _ := by ext; exact neg_add_cancel _
  add_comm _ _ := by ext; exact add_comm _ _

section

variable (f g : AutomorphicForm GA GK ZA W)

@[simp] lemma add_apply (x) : (f + g) x = f x + g x := rfl
@[simp] lemma zero_apply (x) : (0 : AutomorphicForm GA GK ZA W) x = 0 := rfl
@[simp] lemma neg_apply (x) : (-f) x = - f x := rfl
@[simp] lemma sub_apply (x) : (f - g) x = f x - g x := (sub_eq_add_neg _ _).symm

end

section -- move me

variable {G₁ G₂ : Type*} [Group G₂] [TopologicalSpace G₂] [Group G₁] [MulDistribMulAction G₁ G₂]
variable [ContinuousConstSMul G₁ G₂]

open Pointwise in
instance : MulAction G₁ (OpenSubgroup G₂) where
  smul σ U := ⟨σ • U.1, U.2.smul σ⟩
  one_smul U := by ext x; exact congr(x ∈ $(one_smul _ U.1))
  mul_smul σ τ U := by ext x; exact congr(x ∈ $(mul_smul σ τ U.1))

instance : TopologicalSpace (ConjAct G₂) := inferInstanceAs (TopologicalSpace G₂)

instance [TopologicalGroup G₂] : ContinuousSMul (ConjAct G₂) G₂ :=
  ⟨show Continuous fun p : G₂ × G₂ ↦ p.1 * p.2 * p.1⁻¹ by continuity⟩

end

open Pointwise in
instance : DistribMulAction GA (AutomorphicForm GA GK ZA W) where
  smul σ f :=
  { toFun := (f <| · * σ)
    left_invt := by simp [smul_mul_assoc]
    has_character := by simp [smul_mul_assoc]
    right_invt := ⟨ConjAct.toConjAct σ • f.level, fun τ u hu ↦ by
      obtain ⟨u, hu, rfl⟩ := hu
      simp [ConjAct.toConjAct_smul, mul_assoc, ← f.hasLevel_level (τ * σ) _ hu]⟩ }
  one_smul f := by ext x; show f _ = f _; simp
  mul_smul σ τ f := by ext x; show f _ = f _; simp [mul_assoc]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

open Pointwise in
instance : DistribMulAction ZA (AutomorphicForm GA GK ZA W) where
  smul σ f :=
  { toFun := σ • f
    left_invt := by simp only [Pi.smul_apply, ← has_character, ← left_invt, smul_comm, implies_true]
    has_character g z := by simp only [Pi.smul_apply, ← has_character, ← left_invt, smul_comm σ z]
    right_invt := ⟨f.level, fun τ u hu ↦ by simp [f.hasLevel_level _ _ hu]⟩ }
  one_smul _ := by ext; exact one_smul _ _
  mul_smul _ _ _ := by ext; exact mul_smul _ _ _
  smul_zero _ := by ext; exact smul_zero _
  smul_add _ _ _ := by ext; exact smul_add _ _ _

@[simp]
lemma smul₁_apply (σ : GA) (f : AutomorphicForm GA GK ZA W) (x) :
  (σ • f) x = f (x * σ) := rfl

@[simp]
lemma smul₂_apply (σ : ZA) (f : AutomorphicForm GA GK ZA W) (x) :
  (σ • f) x = σ • f x := rfl

lemma smul_of_hasLevel {f : AutomorphicForm GA GK ZA W} {U : Subgroup GA}
    (hf : HasLevel f U) (σ : GA) (hσ : σ ∈ U) :
  σ • f = f := by ext; simp [hf _ _ hσ]

instance : IsScalarTower ZA GA (AutomorphicForm GA GK ZA W) := by
  constructor; intros; ext; simp [mul_smul_comm]

section module

variable {R : Type*} [CommRing R] [Module R W] [SMulCommClass R GK W] [SMulCommClass R ZA W]

instance : Module R (AutomorphicForm GA GK ZA W) where
  smul r f :=
  { toFun := r • f
    left_invt := by simp [smul_comm]
    has_character := by simp [smul_comm]
    right_invt := ⟨f.level, fun σ u hu ↦ by simp [f.hasLevel_level _ _ hu]⟩ }
  one_smul f := by ext; exact one_smul _ _
  mul_smul _ _ _ := by ext; exact mul_smul _ _ _
  smul_zero _ := by ext; exact smul_zero _
  smul_add _ _ _ := by ext; exact smul_add _ _ _
  add_smul _ _ _ := by ext; exact add_smul _ _ _
  zero_smul _ := by ext; exact zero_smul _ _

@[simp]
lemma smul₃_apply (r : R) (f : AutomorphicForm GA GK ZA W) (x) : (r • f) x = r • (f x) := rfl

instance : SMulCommClass R GA (AutomorphicForm GA GK ZA W) where
  smul_comm r g x := by ext; simp

end module
