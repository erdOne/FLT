/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/

import FLT.Proj3.CommAlgebraCat.Monoidal
import Mathlib.CategoryTheory.Functor.Category
import FLT.for_mathlib.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Yoneda
import FLT.Proj3.HopfMon

/-!
# The internal group object in the corepresentable functor from commutaive algebra

we prove that it is antiquivalent to hopf algebra.
-/

open CategoryTheory Opposite BigOperators

open scoped MonoidalCategory
open scoped TensorProduct

variable (k : Type v) [CommRing k]

local notation "⋆" => (coyoneda.obj <| op (CommAlgebraCat.of k k))

section setup

variable {k}
/--The binary product of two functors -/
@[simps]
def mul (F G : CommAlgebraCat k ⥤ Type v) :
    CommAlgebraCat k ⥤ Type v where
  obj A := (F.obj A) × (G.obj A)
  map f x := ⟨F.map f x.1, G.map f x.2⟩

/--
Taking binary product of two functors is functorial.
-/
@[simps]
def mulMap {a a' b b' : CommAlgebraCat k ⥤ Type v}
    (f : a ⟶ a') (g : b ⟶ b') :
    mul a b ⟶ mul a' b' where
  app X a := ⟨f.app X a.1, g.app X a.2⟩
  naturality X Y m := by
    ext ⟨c, d⟩
    simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq]
    have := congr_fun (f.naturality m) c
    rw [show f.app Y (a.map m c) = _ from congr_fun (f.naturality m) c,
      types_comp_apply, show g.app Y (b.map m d) = _ from
      congr_fun (g.naturality m) d, types_comp_apply]
    tauto

instance mulMap.isIso {a a' b b' : CommAlgebraCat k ⥤ Type v}
    (f : a ⟶ a') (g : b ⟶ b') [IsIso f] [IsIso g] :
    IsIso (mulMap f g) where
  out := by
    use mulMap (inv f) (inv g)
    constructor
    · ext X ⟨Y1, Y2⟩
      simp only [mul_obj, FunctorToTypes.comp, mulMap_app, NatIso.isIso_inv_app, NatTrans.id_app,
        types_id_apply, Prod.mk.injEq]
      constructor
      · rw [show inv (f.app X) = (inv f).app X by simp]
        change  (f ≫ inv f).app X Y1 = _
        simp only [IsIso.hom_inv_id, NatTrans.id_app, types_id_apply]
      · rw [show inv (g.app X) = (inv g).app X by simp]
        change  (g ≫ inv g).app X Y2 = _
        simp only [IsIso.hom_inv_id, NatTrans.id_app, types_id_apply]
    · ext X ⟨Y1, Y2⟩
      simp only [mul_obj, FunctorToTypes.comp, mulMap_app, NatIso.isIso_inv_app, NatTrans.id_app,
        types_id_apply, Prod.mk.injEq]
      constructor
      · rw [show inv (f.app X) = (inv f).app X by simp]
        change  (inv f ≫ f).app X Y1 = _
        simp only [IsIso.inv_hom_id, NatTrans.id_app, types_id_apply]
      · rw [show inv (g.app X) = (inv g).app X by simp]
        change  (inv g ≫ g).app X Y2 = _
        simp only [IsIso.inv_hom_id, NatTrans.id_app, types_id_apply]


lemma mulMap_comp {a a' a'' b b' b'' : CommAlgebraCat k ⥤ Type v}
    (f : a ⟶ a') (f' : a' ⟶ a'')
    (g : b ⟶ b') (g' : b' ⟶ b'') :
    mulMap (f ≫ f') (g ≫ g') =
    mulMap f g ≫ mulMap f' g' := by 
  ext X ⟨Y1, Y2⟩
  simp only [mul_obj, mulMap_app, FunctorToTypes.comp]

/--
The product of three functors is associative up to isomorphism.
-/
@[simps]
def mulAssoc (a b c : CommAlgebraCat k ⥤ Type v) :
    mul a (mul b c) ≅ mul (mul a b) c where
  hom := { app := fun x z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩ }
  inv := { app := fun x z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩ }

/--
shorthand for `mul F F`.
-/
@[simp]
def square (F : CommAlgebraCat k ⥤ Type v) : CommAlgebraCat k ⥤ Type v :=
  mul F F

/--
`Hom(k, -)` has the role of the unit up to isomorphism.
-/
@[simps]
def mulStar (a : CommAlgebraCat k ⥤ Type v) : mul a ⋆ ≅ a where
  hom := { app := fun x z ↦ z.1 }
  inv :=
  { app := fun x z ↦ ⟨z, Algebra.ofId k x⟩
    naturality := fun b c f ↦ types_ext _ _ fun x ↦ Prod.ext rfl <|
      AlgHom.ext fun x ↦ show algebraMap k c x = f (algebraMap k b x) from
      f.commutes _ |>.symm }
  hom_inv_id := by
    ext A ⟨x, (f : k →ₐ[k] A)⟩
    simp only [mul_obj, coyoneda_obj_obj, unop_op, FunctorToTypes.comp, NatTrans.id_app,
      types_id_apply, Prod.mk.injEq, true_and]
    refine AlgHom.ext fun x ↦ ?_
    change algebraMap k A x = _
    rw [Algebra.algebraMap_eq_smul_one, show x • 1 = x • f 1
      by rw [_root_.map_one], ← f.map_smul, Algebra.smul_def]
    simp
  inv_hom_id := by ext; simp

/--
`Hom(k, -)` has the role of the unit up to isomorphism.
-/
@[simps]
def starMul (a) : mul ⋆ a ≅ a where
  hom := { app := fun x z ↦ z.2 }
  inv :=
  { app := fun x z ↦ ⟨Algebra.ofId k x, z⟩
    naturality := fun b c f ↦ types_ext _ _ fun x ↦ Prod.ext
      (AlgHom.ext fun x ↦ show algebraMap k c x = f (algebraMap k b x) from
        f.commutes _ |>.symm) rfl }
  hom_inv_id := by
    ext A ⟨(f : k →ₐ[k] A), x⟩
    simp only [mul_obj, coyoneda_obj_obj, unop_op, FunctorToTypes.comp, NatTrans.id_app,
      types_id_apply, Prod.mk.injEq, and_true]
    refine AlgHom.ext fun x ↦ ?_
    change algebraMap k A x = _
    rw [Algebra.algebraMap_eq_smul_one, show x • 1 = x • f 1
      by rw [_root_.map_one], ← f.map_smul, Algebra.smul_def]
    simp
  inv_hom_id := by ext; simp

-- FIXME: **The formatting is not ideal**
/--
```
Hom(A, -) × Hom(B, -) ≅ Hom(A ⊗ B, -)
```
-/
@[simps]
noncomputable def coyonedaMulCoyoneda (A B : CommAlgebraCat k) :
    mul (coyoneda.obj <| op A) (coyoneda.obj <| op B) ≅
    (coyoneda.obj <| op <| A ⊗ B) where
  hom :=
  {
  app := fun X f ↦ Algebra.TensorProduct.lift f.1 f.2 fun a b ↦ show _ = _ by rw [mul_comm]
  naturality := by
    intro X Y f
    ext ⟨(x1 : A →ₐ[k] X), (x2 : B →ₐ[k] X)⟩
    simp only [coyoneda_obj_obj, unop_op, mul_obj, types_comp_apply, mul_map, coyoneda_obj_map]
    apply Algebra.TensorProduct.ext
    · ext a
      simp only [Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.includeLeft_apply]
      show f _ = f _
      simp only [RingHom.coe_coe]
      erw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    · ext b
      simp only [Algebra.TensorProduct.lift_comp_includeRight, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply]
      change f _ = f _
      simp only [RingHom.coe_coe]
      erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  }

  inv :=
  {
  app := fun X f ↦
    ⟨Algebra.TensorProduct.liftEquiv.symm f |>.1.1,
      Algebra.TensorProduct.liftEquiv.symm f |>.1.2⟩
  naturality := by
    intro X Y f
    change _ →ₐ[k] _ at f
    ext (T : _ →ₐ[k] _)
    simp only [unop_op] at T
    simp only [mul_obj, coyoneda_obj_obj, unop_op, Algebra.TensorProduct.liftEquiv_symm_apply_coe,
      types_comp_apply, coyoneda_obj_map, mul_map, Prod.mk.injEq]
    constructor <;> rfl
  }

  hom_inv_id := by
    dsimp only [mul_obj, coyoneda_obj_obj, unop_op, id_eq, eq_mpr_eq_cast, types_comp_apply,
      mul_map, coyoneda_obj_map, AlgHom.coe_comp, Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lift_tmul, RingHom.coe_coe,
      cast_eq, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.liftEquiv_symm_apply_coe]
    ext X ⟨(f1 : A →ₐ[k] _), (f2 : B →ₐ[k] _)⟩
    simp only [mul_obj, coyoneda_obj_obj, unop_op, FunctorToTypes.comp,
      Algebra.TensorProduct.lift_comp_includeLeft, Algebra.TensorProduct.lift_comp_includeRight,
      NatTrans.id_app, types_id_apply]

  inv_hom_id := by
    dsimp only [coyoneda_obj_obj, unop_op, Algebra.TensorProduct.liftEquiv_symm_apply_coe, mul_obj,
      types_comp_apply, coyoneda_obj_map, mul_map, id_eq, eq_mpr_eq_cast, AlgHom.coe_comp,
      Function.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lift_tmul,
      RingHom.coe_coe, cast_eq, AlgHom.coe_restrictScalars',
      Algebra.TensorProduct.includeRight_apply]
    ext X (f : A ⊗[k] B →ₐ[k] X)
    simp only [coyoneda_obj_obj, unop_op, FunctorToTypes.comp, NatTrans.id_app, types_id_apply]
    apply Algebra.TensorProduct.ext
    · ext a
      simp only [Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.includeLeft_apply]
    · ext b
      simp only [Algebra.TensorProduct.lift_comp_includeRight, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply]

end setup

/--
An affine monoid functor is an internal monoid object in the category of corepresentable functors.
-/
structure AffineMonoid extends CommAlgebraCat k ⥤ Type v where
  /--the underlying functor is corepresentable-/
  corep : toFunctor.Corepresentable
  /--the multiplication map-/
  m : mul toFunctor toFunctor ⟶ toFunctor
  /--the unit map-/
  e : ⋆ ⟶ toFunctor
  mul_assoc' : mulMap (𝟙 toFunctor) m ≫ m =
    (mulAssoc toFunctor toFunctor toFunctor).hom ≫ mulMap m (𝟙 toFunctor) ≫ m
  mul_one' : mulMap (𝟙 _) e ≫ m = (mulStar toFunctor).hom
  one_mul' : mulMap e (𝟙 _) ≫ m = (starMul toFunctor).hom

attribute [instance] AffineMonoid.corep

/--
An affine group functor is the internal group object in the category of corepresentable functors.
-/
structure AffineGroup extends AffineMonoid k where
  /--the inverse map-/
  i : toFunctor ⟶ toFunctor
  /-**Check if this correct**-/
  mul_inv :
  ({
    app := fun _ x ↦ (i.app _ x, x)
    naturality := by 
      intro X Y (f: X →ₐ[k] Y) 
      ext x
      simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq, and_true]
      have := i.naturality f
      change (i.app Y).comp _ = (toFunctor.map f).comp _ at this 
      exact congr_fun this x

  } ≫ m : toFunctor ⟶ toFunctor) = 𝟙 toFunctor
  inv_mul :
  ({
      app := fun _ x ↦ (x, i.app _ x)
      naturality := by 
        intro X Y (f: X →ₐ[k] Y)
        ext x 
        simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq, true_and]
        have := i.naturality f
        change (i.app Y).comp _ = (toFunctor.map f).comp _ at this
        exact congr_fun this x

    } ≫ m : toFunctor ⟶ toFunctor)= 𝟙 toFunctor

namespace AffineMonoid

variable {k}

/--morphism between two affine monoid functors-/
structure Hom (F G : AffineMonoid k) where
  /-- the underlying natural transformation-/
  hom : F.toFunctor ⟶ G.toFunctor
  one : F.e ≫ hom = G.e := by aesop_cat
  mul : F.m ≫ hom = mulMap hom hom ≫ G.m := by aesop_cat

attribute [reassoc, simp] Hom.one Hom.mul

instance : Category <| AffineMonoid k where
  Hom := Hom
  id F := { hom := 𝟙 _ }
  comp α β :=
  { hom := α.hom ≫ β.hom
    one := by rw [α.one_assoc, β.one]
    mul := by rw [α.mul_assoc, β.mul, mulMap_comp, Category.assoc] }

end AffineMonoid

namespace AffineGroup

variable {k}

/--Morphisms between two affine group functors. -/
structure Hom (F G : AffineGroup k) where
  /-- the underlying natural transformation. -/
  hom : F.toFunctor ⟶ G.toFunctor
  one : F.e ≫ hom = G.e := by aesop_cat
  mul : F.m ≫ hom = mulMap hom hom ≫ G.m := by aesop_cat

attribute [reassoc, simp] Hom.one Hom.mul

instance : Category <| AffineGroup k where
  Hom := Hom
  id F := { hom := 𝟙 _ }
  comp α β :=
  { hom := α.hom ≫ β.hom
    one := by rw [α.one_assoc, β.one]
    mul := by rw [α.mul_assoc, β.mul, mulMap_comp, Category.assoc] }

end AffineGroup

variable {k} in
/--A proposition stating that a corepresentable functor is an affine monoid with specified
multiplication and unit. -/
structure IsAffineMonoidWithChosenMulAndUnit
    (F : CommAlgebraCat k ⥤ Type v) [F.Corepresentable]
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) : Prop :=
  mul_assoc' : mulMap (𝟙 F) m ≫ m = (mulAssoc F F F).hom ≫ mulMap m (𝟙 F) ≫ m
  mul_one : mulMap (𝟙 F) e ≫ m = (mulStar F).hom
  one_mul : mulMap e (𝟙 F) ≫ m = (starMul F).hom

variable {k} in
/--A proposition stating that a corepresentable functor is an affine group with specified
multiplication, unit and inverse -/
structure IsAffineGroupWithChosenMulAndUnitAndInverse
    (F : CommAlgebraCat k ⥤ Type v) [F.Corepresentable]
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) (i : F ⟶ F)
    extends IsAffineMonoidWithChosenMulAndUnit F m e: Prop :=
  mul_inv :
    ({
      app := fun _ x ↦ (i.app _ x, x)
      naturality := by 
        intro X Y (f : X →ₐ[k] Y)
        ext x
        simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq, and_true]
        have := i.naturality f 
        change (i.app Y).comp _ = (F.map f).comp _ at this
        exact congr_fun this x

    } ≫ m : F ⟶ F) = 𝟙 F
  inv_mul :
    ({
        app := fun _ x ↦ (x, i.app _ x)
        naturality := by 
          intro X Y (f : X →ₐ[k] Y)
          ext x
          simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq, true_and]
          have := i.naturality f
          change (i.app Y).comp _ = (F.map f).comp _ at this
          exact congr_fun this x

      } ≫ m : F ⟶ F)= 𝟙 F

variable {k} in
open TensorProduct in
/-- A proposition stating that an algebra has a bialgebra structure with specified
  comultiplication and counit. -/
structure IsBialgebraWithChosenComulAndCounit
    (A : Type v) [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k) : Prop :=
  coassoc :
    (Algebra.TensorProduct.assoc k A A A |>.toAlgHom.comp <|
      Algebra.TensorProduct.map comul (AlgHom.id k A) |>.comp
        comul) =
    (Algebra.TensorProduct.map (AlgHom.id k A) comul).comp comul
  rTensor_counit_comp_comul :
    counit.toLinearMap.rTensor A ∘ₗ comul = TensorProduct.mk k _ _ 1
  lTensor_counit_comp_comul :
    counit.toLinearMap.lTensor A ∘ₗ comul = (TensorProduct.mk k _ _).flip 1
  mul_compr₂_counit :
    (LinearMap.mul k A).compr₂ counit =
    (LinearMap.mul k k).compl₁₂ counit counit
  mul_compr₂_comul :
    (LinearMap.mul k A).compr₂ comul =
    (LinearMap.mul k (A ⊗[k] A)).compl₁₂ comul comul

variable {k} in
/-- A proposition stating that an algebra has a Hopf algebra structure with specified
  comultiplication, counit and antipode map. -/
structure IsHopfAlgebraWithChosenComulAndCounitAndAntipode
    (A : Type v) [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k)
    (antipode : A →ₐ[k] A) extends
    IsBialgebraWithChosenComulAndCounit A comul counit : Prop :=
  mul_antipode_rTensor_comul :
      LinearMap.mul' k A ∘ₗ antipode.toLinearMap.rTensor A ∘ₗ comul =
        (Algebra.linearMap k A) ∘ₗ counit.toLinearMap
  mul_antipode_lTensor_comul :
    LinearMap.mul' k A ∘ₗ antipode.toLinearMap.lTensor A ∘ₗ comul =
      (Algebra.linearMap k A) ∘ₗ counit.toLinearMap

section setup

variable {k}
variable {A : Type v} [CommRing A] [Algebra k A]
open TensorProduct in
variable (comul : A →ₐ[k] A ⊗[k] A)
variable (counit : A →ₐ[k] k)
variable (antipode : A →ₐ[k] A)

open TensorProduct in
/--Any potential comultiplication can be reinterpreted as a multiplication in the functor
language.-/
@[simp]
noncomputable def comulToMul (comul : A →ₐ[k] A ⊗[k] A) :
    square (coyoneda.obj <| op <| CommAlgebraCat.of k A) ⟶
    coyoneda.obj <| op <| CommAlgebraCat.of k A :=
  (coyonedaMulCoyoneda (.of k A) (.of k A)).hom ≫ coyoneda.map (CommAlgebraCat.ofHom comul).op

/--Any potential counit can be reinterpreted as a unit map in the functor language.-/
@[simp]
noncomputable def counitToUnit :
    ⋆ ⟶ coyoneda.obj <| op <| CommAlgebraCat.of k A :=
  coyoneda.map <| op <| counit

/--Any potential antipodal map can be reinterpreted as an inverse map in the functor language.-/
@[simp]
noncomputable def antipodeToInverse :
    (coyoneda.obj <| op <| CommAlgebraCat.of k A) ⟶
    (coyoneda.obj <| op <| CommAlgebraCat.of k A) :=
  coyoneda.map (op antipode)

variable {F : CommAlgebraCat k ⥤ Type v} [F.Corepresentable]
variable (m : mul F F ⟶ F)
variable (e : (coyoneda.obj <| op (CommAlgebraCat.of k k)) ⟶ F)
variable (i : F ⟶ F)

-- **I think this is how it works but I am not sure**
/-- Any potential multiplication can be reinterpreted as a comultiplication in the algebra
language. -/
noncomputable def mToComul : F.coreprX →ₐ[k] F.coreprX ⊗[k] F.coreprX :=
  (coyonedaMulCoyoneda _ _).inv ≫ mulMap F.coreprW.hom F.coreprW.hom ≫ m ≫ F.coreprW.inv |>.app
    (F.coreprX ⊗ F.coreprX) (𝟙 _)

-- **I think this is how it works but I am not sure**
/-- Any potential unit can be reinterpreted as a counit in the algebra language. -/
noncomputable def eToCounit : F.coreprX →ₐ[k] k :=
  e ≫ F.coreprW.inv |>.app (CommAlgebraCat.of k k) (𝟙 _)

-- **I think this is how it works but I am not sure**
/-- Any potential inverse can be reinterpreted as an antipodal map in the algebra language. -/
noncomputable def iToAntipode : F.coreprX →ₐ[k] F.coreprX :=
  F.coreprW.hom ≫ i ≫ F.coreprW.inv |>.app (F.coreprX) (𝟙 _)


lemma crazy_comul_repr (comul : A →ₐ[k] A ⊗[k] A) (x : A): ∃ (ι : Type v) (s : Finset ι) (a b : ι → A),
  comul x = ∑ i in s, a i ⊗ₜ[k] b i := by
    classical
    use A ⊗[k] A
    set aa := comul x
    have mem : aa ∈ (⊤ : Submodule k (A ⊗[k] A)) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem
    obtain ⟨r, hr, (eq1 : ∑ i in r.support, (_ • _) = _)⟩ := mem
    choose a a' haa' using hr
    replace eq1 := calc _
      aa = ∑ i in r.support, r i • i := eq1.symm
      _ = ∑ i in r.support.attach, (r i : k) • (i : (A ⊗[k] A))
        := Finset.sum_attach _ _ |>.symm
      _ = ∑ i in r.support.attach, (r i • a i.2 ⊗ₜ[k] a' i.2) := by
        apply Finset.sum_congr rfl
        rintro i -
        rw [haa' i.2]
      _ = ∑ i in r.support.attach, ((r i • a i.2) ⊗ₜ[k] a' i.2) := by
        apply Finset.sum_congr rfl
        rintro i -
        rw [TensorProduct.smul_tmul']
    use r.support
    use fun i => if h : i ∈ r.support then r i • a h else 0
    use fun i => if h : i ∈ r.support then a' h else 0
    rw [eq1] ; conv_rhs => rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun _ _ ↦ (by split_ifs with h <;> aesop)

namespace auxlemma


lemma aux02 :
    (mulAssoc (coyoneda.obj (op (CommAlgebraCat.of k A))) (coyoneda.obj (op (CommAlgebraCat.of k A)))
        (coyoneda.obj (op (CommAlgebraCat.of k A)))).hom ≫
    mulMap (comulToMul comul) (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) ≫
      comulToMul comul =
    mulMap (𝟙 _) (coyonedaMulCoyoneda _ _).hom ≫
    (coyonedaMulCoyoneda _ _).hom ≫
      coyoneda.map (op <|
        (((CommAlgebraCat.ofHom comul :
            CommAlgebraCat.of k A ⟶ CommAlgebraCat.of k A ⊗ CommAlgebraCat.of k A) ▷ _) ≫
        (α_ _ _ _).hom)) ≫
    coyoneda.map (op <| CommAlgebraCat.ofHom comul) := by
  ext B ⟨f, g, h⟩
  change A →ₐ[k] B at f g h
  simp only [coyoneda_obj_obj, unop_op, comulToMul, square, mul_obj, FunctorToTypes.comp,
    mulAssoc_hom_app, mulMap_app, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
    coyoneda_map_app, Quiver.Hom.unop_op, NatTrans.id_app, types_id_apply]
  change _ = CommAlgebraCat.ofHom comul ≫ _
  congr 1
  change Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f g _).comp comul) _ _ = 
    (Algebra.TensorProduct.lift _ _ _).comp ((Algebra.TensorProduct.assoc k A A A).toAlgHom.comp 
    (Algebra.TensorProduct.map comul (AlgHom.id k A)))
  ext x <;> obtain ⟨ι, s, a, b, eq0⟩ := crazy_comul_repr comul x
  . simp only [Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.coe_comp, Function.comp_apply,
    eq0, map_sum, Algebra.TensorProduct.lift_tmul, CommAlgebraCat.coe_of, AlgEquiv.toAlgHom_eq_coe,
    AlgHom.coe_coe, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul,
    map_one, TensorProduct.sum_tmul, Algebra.TensorProduct.assoc_tmul]
    simp_rw [Algebra.TensorProduct.lift_tmul g h 
      (by intro x y; rw [commute_iff_eq, mul_comm]) (b _) (b := 1)]
    simp only [map_one, mul_one]

  · simp only [Algebra.TensorProduct.lift_comp_includeRight, CommAlgebraCat.coe_of,
    AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_restrictScalars', AlgHom.coe_coe,
    Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
    map_one, AlgHom.coe_id, id_eq]
    rw [show (1 : A ⊗[k] A) = (1 : A) ⊗ₜ[k] (1 : A) by rfl] 
    simp only [CommAlgebraCat.coe_of,
      Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    erw [Algebra.TensorProduct.lift_tmul] ; simp only [CommAlgebraCat.coe_of, map_one, one_mul]

lemma aux01  :
    mulMap (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) (comulToMul comul)
      ≫ comulToMul comul =
    mulMap (𝟙 _) (coyonedaMulCoyoneda _ _).hom ≫
    (coyonedaMulCoyoneda _ _).hom ≫
    coyoneda.map (op <| _ ◁ (CommAlgebraCat.ofHom comul :
      CommAlgebraCat.of k A ⟶ CommAlgebraCat.of k A ⊗ CommAlgebraCat.of k A)) ≫
    coyoneda.map (op <| CommAlgebraCat.ofHom comul) := by
  ext B ⟨f, ⟨g1, g2⟩⟩
  change A →ₐ[k] B at f g1 g2
  simp only [coyoneda_obj_obj, unop_op, square, comulToMul, mul_obj, FunctorToTypes.comp,
    mulMap_app, NatTrans.id_app, types_id_apply, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
    coyoneda_map_app, Quiver.Hom.unop_op]
  change _ = CommAlgebraCat.ofHom comul ≫ _
  congr 1 
  change Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift g1 g2 _).comp comul) _ = 
    (Algebra.TensorProduct.lift _ _ _).comp (Algebra.TensorProduct.map (AlgHom.id k A) comul)
  ext x 
  · simp only [Algebra.TensorProduct.lift_comp_includeLeft, CommAlgebraCat.coe_of, AlgHom.coe_comp,
    Function.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.coe_id, id_eq, map_one, Algebra.TensorProduct.lift_tmul, mul_one]

  · simp only [Algebra.TensorProduct.lift_comp_includeRight, AlgHom.coe_comp, Function.comp_apply,
    CommAlgebraCat.coe_of, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.lift_tmul, one_mul]


end auxlemma

end setup


variable {k} in
theorem isAffineMonoidWithChosenMulAndUnit_iff_isBialgebraWithChosenComulAndCounit
    {A : Type v} [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k) :
    IsAffineMonoidWithChosenMulAndUnit
      (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      (comulToMul comul)
      (counitToUnit counit) ↔
    IsBialgebraWithChosenComulAndCounit A comul counit := by
  
  constructor
  · rintro ⟨mul_assoc, mul_one, one_mul⟩
    let _ : AffineMonoid k :=
    { toFunctor := coyoneda.obj <| op <| CommAlgebraCat.of k A
      corep := inferInstance
      m := comulToMul comul
      e := counitToUnit counit
      mul_assoc' := mul_assoc
      mul_one' := mul_one
      one_mul' := one_mul }
    fconstructor

    · rw [auxlemma.aux01, auxlemma.aux02, ← IsIso.inv_comp_eq] at mul_assoc
      simp only [unop_op, CommAlgebraCat.coe_of, IsIso.inv_hom_id_assoc, Iso.cancel_iso_hom_left,
        ← coyoneda.map_comp] at mul_assoc
      apply Coyoneda.coyoneda_faithful.map_injective at mul_assoc
      apply_fun unop at mul_assoc
      exact mul_assoc.symm

    · have eq0 : mulMap (counitToUnit counit) (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) ≫ 
        comulToMul comul = (coyonedaMulCoyoneda _ _).hom ≫ coyoneda.map (op <|
          (Algebra.TensorProduct.map counit (AlgHom.id k A)).comp comul) := by
        simp only [counitToUnit, unop_op, comulToMul, square]
        ext B ⟨f, g⟩
        change k →ₐ[k] B at f ; change A →ₐ[k] B at g
        simp only [coyoneda_obj_obj, unop_op, FunctorToTypes.comp, mulMap_app, coyoneda_map_app,
          NatTrans.id_app, types_id_apply, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
          Quiver.Hom.unop_op]
        change (Algebra.TensorProduct.lift (f.comp counit) g _).comp comul = 
          (Algebra.TensorProduct.lift f g _).comp 
          ((Algebra.TensorProduct.map counit (AlgHom.id k A)).comp comul)
        ext x 
        obtain ⟨ι, s, a, b, eq0⟩ := crazy_comul_repr comul x
        simp only [AlgHom.coe_comp, Function.comp_apply, eq0, map_sum,
          Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

      have eq1 : (starMul (coyoneda.obj (op (CommAlgebraCat.of k A)))).hom =
          (coyonedaMulCoyoneda _ _).hom ≫ coyoneda.map 
          (op <| Algebra.TensorProduct.includeRight) := by
        simp only [unop_op, CommAlgebraCat.coe_of]
        ext B ⟨f, g⟩ ; change k →ₐ[k] B at f ; change A →ₐ[k] B at g
        simp only [coyoneda_obj_obj, unop_op, starMul_hom_app, FunctorToTypes.comp,
          coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of, coyoneda_map_app]
        change _ = (Algebra.TensorProduct.lift f g _).comp Algebra.TensorProduct.includeRight
        ext x
        simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.lift_tmul, map_one, one_mul] ; ring

      rw [eq0, eq1, ← IsIso.inv_comp_eq] at one_mul
      simp only [IsIso.Iso.inv_hom, unop_op, CommAlgebraCat.coe_of] at one_mul
      erw [Iso.inv_hom_id_assoc] at one_mul
      apply Coyoneda.coyoneda_faithful.map_injective at one_mul
      apply_fun unop at one_mul
      exact congr($(one_mul).toLinearMap)

    · have eq0 : mulMap (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) (counitToUnit counit) ≫ 
          comulToMul comul = (coyonedaMulCoyoneda _ _).hom ≫ coyoneda.map (op <| 
          (Algebra.TensorProduct.map (AlgHom.id k A) counit).comp comul) := by 
        simp only [counitToUnit, unop_op, comulToMul, square]
        ext B ⟨f, g⟩ ; change A →ₐ[k] B at f ; change k →ₐ[k] B at g
        simp only [coyoneda_obj_obj, unop_op, FunctorToTypes.comp, mulMap_app, NatTrans.id_app,
          types_id_apply, coyoneda_map_app, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
          Quiver.Hom.unop_op]
        change (Algebra.TensorProduct.lift f (g.comp counit) _ ).comp comul =
          (Algebra.TensorProduct.lift f g _).comp
          ((Algebra.TensorProduct.map (AlgHom.id k A) counit).comp comul)
        ext x ; obtain ⟨ι, s, a, b, eq0⟩ := crazy_comul_repr comul x
        simp only [AlgHom.coe_comp, Function.comp_apply, eq0, map_sum,
          Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
        
      have eq1 : (mulStar (coyoneda.obj (op (CommAlgebraCat.of k A)))).hom =
          (coyonedaMulCoyoneda _ _).hom ≫ coyoneda.map 
          (op <| Algebra.TensorProduct.includeLeft) := by
          simp only [unop_op, CommAlgebraCat.coe_of]
          ext B ⟨f, g⟩ ; change A →ₐ[k] B at f ; change k →ₐ[k] B at g
          simp only [coyoneda_obj_obj, unop_op, mulStar_hom_app, FunctorToTypes.comp,
            coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of, coyoneda_map_app]
          change _ = (Algebra.TensorProduct.lift f g _).comp Algebra.TensorProduct.includeLeft
          ext x
          simp only [Algebra.TensorProduct.lift_comp_includeLeft]
      
      rw [eq0, eq1, ← IsIso.inv_comp_eq] at mul_one
      simp only [IsIso.Iso.inv_hom, unop_op, CommAlgebraCat.coe_of] at mul_one
      erw [Iso.inv_hom_id_assoc] at mul_one
      apply Coyoneda.coyoneda_faithful.map_injective at mul_one
      apply_fun unop at mul_one
      change (Algebra.TensorProduct.map _ _).comp _ = Algebra.TensorProduct.includeLeft at mul_one
      apply_fun AlgHom.toLinearMap at mul_one
      exact mul_one

    · have eq0 := congr_fun (NatTrans.congr_app mul_assoc (.of k A))
        ⟨AlgHom.id _ _, ⟨Algebra.TensorProduct.lmul' k (S := A) |>.comp comul, AlgHom.id _ _⟩⟩
      simp only [mul_obj, coyoneda_obj_obj, unop_op, CommAlgebraCat.coe_of, mulMap_app,
        NatTrans.id_app, types_id_apply, FunctorToTypes.comp, mulAssoc_hom_app,
        Prod.mk.injEq] at eq0
      apply_fun AlgHom.toLinearMap at eq0
      simp only [unop_op, CommAlgebraCat.coe_of, comulToMul, square, FunctorToTypes.comp,
        coyonedaMulCoyoneda_hom_app, coyoneda_map_app, Quiver.Hom.unop_op,
        AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe] at eq0 ⊢
      ext
      simp

    · have eq0 := congr_fun (NatTrans.congr_app mul_assoc (.of k A))
        ⟨AlgHom.id _ _, ⟨Algebra.TensorProduct.lmul' k (S := A) |>.comp comul, AlgHom.id _ _⟩⟩
      simp only [mul_obj, coyoneda_obj_obj, unop_op, CommAlgebraCat.coe_of, mulMap_app,
        NatTrans.id_app, types_id_apply, FunctorToTypes.comp, mulAssoc_hom_app,
        Prod.mk.injEq] at eq0
      apply_fun AlgHom.toLinearMap at eq0
      simp only [unop_op, CommAlgebraCat.coe_of, comulToMul, square, FunctorToTypes.comp,
        coyonedaMulCoyoneda_hom_app, coyoneda_map_app, Quiver.Hom.unop_op,
        AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe] at eq0 ⊢
      ext a b
      simp

  · rintro ⟨coassoc, rTensor_counit_comp_comul,
      lTensor_counit_comp_comul, mul_compr₂_counit, mul_compr₂_comul⟩
    let ba : Bialgebra k A :={
      comul := comul
      counit := counit
      coassoc := by
        apply_fun AlgHom.toLinearMap at coassoc
        simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_toLinearMap,
          AlgEquiv.toAlgHom_toLinearMap] at coassoc
        exact coassoc
      rTensor_counit_comp_comul := rTensor_counit_comp_comul
      lTensor_counit_comp_comul := lTensor_counit_comp_comul
      counit_one := counit.map_one
      mul_compr₂_counit := mul_compr₂_counit
      comul_one := comul.map_one
      mul_compr₂_comul := mul_compr₂_comul
    }
    fconstructor

    · rw [auxlemma.aux01, auxlemma.aux02, ← IsIso.inv_comp_eq]
      simp only [unop_op, CommAlgebraCat.coe_of, IsIso.inv_hom_id_assoc, Iso.cancel_iso_hom_left,
        ← coyoneda.map_comp]
      congr 1
      apply_fun unop using unop_injective
      exact coassoc.symm

    · ext B ⟨f, g⟩
      change AlgHomPoint k A B at f ; change AlgHomPoint k k B at g
      simp only [coyoneda_obj_obj, unop_op, counitToUnit, CommAlgebraCat.coe_of, comulToMul, square,
        FunctorToTypes.comp, mulMap_app, NatTrans.id_app, types_id_apply,
        coyonedaMulCoyoneda_hom_app, coyoneda_map_app, Quiver.Hom.unop_op, mulStar_hom_app]
      symm
      change _ = (Algebra.TensorProduct.lift f (g.comp counit) _).comp comul
      ext (x : A)
      obtain ⟨I1, r, x1, x2, eq⟩ := crazy_comul_repr comul x
      simp only [AlgHom.coe_comp, Function.comp_apply, eq, map_sum, Algebra.TensorProduct.lift_tmul]
      have eq0 (y : A) : g (counit y) = counit y • g 1 := by
        rw [← mul_one (counit y), ← smul_eq_mul, map_smul]
        simp only [_root_.map_one, smul_eq_mul, mul_one]
      simp_rw [eq0 _] ; rw [map_one g, ← map_one f]
      simp_rw [← map_smul f] ; simp_rw [← f.map_mul, ← map_sum, mul_smul_one]
      have : ∑ x in r, counit (x2 x) • x1 x = AlgHomPoint.mul (AlgHom.id k A) 1 x := by
        symm ; unfold AlgHomPoint.mul
        have codef : Coalgebra.comul (R := k) (A := A) = comul := rfl
        simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply, codef,
          AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
          DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
          NonUnitalAlgHom.coe_coe, eq, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
          id_eq, Algebra.TensorProduct.lmul'_apply_tmul] ; rw [AlgHomPoint.one_def]
        simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.counitAlgHom_apply]
        calc _
          ∑ x in r, x1 x * (Algebra.ofId k A) (Coalgebra.counit (x2 x)) =
            ∑ x in r, x1 x * (Algebra.ofId k A) (Coalgebra.counit (x2 x) * 1) := by simp
          _ = ∑ x in r, x1 x * (Algebra.ofId k A) (Coalgebra.counit (x2 x) • 1) := by
            simp_rw [← smul_eq_mul k] ; rfl
          _ = ∑ x in r, x1 x * (Coalgebra.counit (x2 x) • 1) := by
            simp_rw [map_smul] ; rw [map_one (Algebra.ofId k A)]
          _ = ∑ x in r, counit (x2 x) • x1 x := by
            simp_rw [mul_smul_one] ; rfl
      rw [this]
      change f x = f (((AlgHom.id k A) * 1) x)
      rw [mul_one] ; rfl

    · ext B ⟨f, g⟩
      change AlgHomPoint k k B at f ; change AlgHomPoint k A B at g
      simp only [coyoneda_obj_obj, unop_op, counitToUnit, comulToMul, square, FunctorToTypes.comp,
        mulMap_app, coyoneda_map_app, NatTrans.id_app, types_id_apply, coyonedaMulCoyoneda_hom_app,
        CommAlgebraCat.coe_of, Quiver.Hom.unop_op, starMul_hom_app] ; symm
      change _ = (Algebra.TensorProduct.lift (f.comp counit) g _).comp comul
      ext (x : A)
      obtain ⟨I1, r, x1, x2, eq⟩ := crazy_comul_repr comul x
      simp only [AlgHom.coe_comp, Function.comp_apply, eq, map_sum, Algebra.TensorProduct.lift_tmul]
      have eq0 (y : A) : f (counit y) = counit y • f 1 := by
        rw [← mul_one (counit y), ← smul_eq_mul, map_smul]
        simp only [_root_.map_one, smul_eq_mul, mul_one]
      simp_rw [eq0 _] ; rw [map_one f, ← map_one g]
      simp_rw [← map_smul g] ; simp_rw [← g.map_mul, ← map_sum, smul_one_mul]
      have : ∑ x in r, counit (x1 x) • x2 x = AlgHomPoint.mul 1 (AlgHom.id k A) x := by
        symm ; unfold AlgHomPoint.mul
        have codef : Coalgebra.comul (R := k) (A := A) = comul := rfl
        simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply, codef,
          AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
          DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
          NonUnitalAlgHom.coe_coe, eq, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
          id_eq, Algebra.TensorProduct.lmul'_apply_tmul] ; rw [AlgHomPoint.one_def]
        simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.counitAlgHom_apply]
        calc _
          ∑ x in r, (Algebra.ofId k A) (Coalgebra.counit (x1 x)) * x2 x =
            ∑ x in r, (Algebra.ofId k A) (Coalgebra.counit (x1 x) * 1) * x2 x := by simp
          _ = ∑ x in r, (Algebra.ofId k A) (Coalgebra.counit (x1 x) • 1) * x2 x := by
            simp_rw [← smul_eq_mul k] ; rfl
          _ = ∑ x in r, (Coalgebra.counit (x1 x) • 1) * x2 x := by
            simp_rw [map_smul] ; rw [map_one (Algebra.ofId k A)]
          _ = ∑ x in r, counit (x1 x) • x2 x := by
            simp_rw [smul_one_mul] ; rfl
      rw [this] ; change g x = g ((1 * (AlgHom.id k A)) x)
      rw [one_mul] ; rfl


variable {k} in
theorem isAffineMonoidWithChosenMulAndUnit_iff_isBialgebraWithChosenComulAndCounit'
    {F : CommAlgebraCat k ⥤ Type v} [F.Corepresentable]
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) :
    IsAffineMonoidWithChosenMulAndUnit F m e ↔
    IsBialgebraWithChosenComulAndCounit F.coreprX (mToComul m) (eToCounit e) := by
  
  constructor
  · rintro ⟨mul_assoc, mul_one, one_mul⟩
    let _ : AffineMonoid k :=
    { toFunctor := F
      corep := inferInstance
      m := m
      e := e
      mul_assoc' := mul_assoc
      mul_one' := mul_one
      one_mul' := one_mul }
    fconstructor
    · sorry

    · sorry
    · sorry
    · ext a b 
      simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
        LinearMap.compr₂_apply, LinearMap.mul_apply', DistribMulActionHom.coe_toLinearMap,
        NonUnitalAlgHom.coe_to_distribMulActionHom, map_mul, NonUnitalAlgHom.coe_coe,
        LinearMap.compl₁₂_apply]
    · simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe]
      ext a b 
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', DistribMulActionHom.coe_toLinearMap,
        NonUnitalAlgHom.coe_to_distribMulActionHom, map_mul, NonUnitalAlgHom.coe_coe,
        LinearMap.compl₁₂_apply]


  · sorry


variable {k} in
theorem
  isAffineGroupWithChosenMulAndUnitAndInverse_iff_isBialgebraWithChosenComulAndCounitAndAntipode
    {A : Type v} [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k)
    (antipode : A →ₐ[k] A) :
    IsAffineGroupWithChosenMulAndUnitAndInverse
      (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      (comulToMul comul)
      (counitToUnit counit)
      (antipodeToInverse antipode) ↔
    IsBialgebraWithChosenComulAndCounit A comul counit := sorry

variable {k} in
theorem
  isAffineGroupWithChosenMulAndUnitAndInverse_iff_isBialgebraWithChosenComulAndCounitAndAntipode'
    {F : CommAlgebraCat k ⥤ Type v} [F.Corepresentable]
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) (i : F ⟶ F) :
    IsAffineGroupWithChosenMulAndUnitAndInverse F m e i ↔
    IsHopfAlgebraWithChosenComulAndCounitAndAntipode
      F.coreprX (mToComul m) (eToCounit e) (iToAntipode i) := sorry

noncomputable def affineGroupAntiToCommAlgCat :
    (AffineGroup k)ᵒᵖ ⥤ HopfAlgCat.{v} k := 
    { obj := fun F ↦
        { carrier := F.unop.coreprX
          isCommRing := inferInstance
          isHopfAlgebra :=
            let i := isAffineGroupWithChosenMulAndUnitAndInverse_iff_isBialgebraWithChosenComulAndCounitAndAntipode'
              F.unop.m F.unop.e F.unop.i |>.mp
                ⟨⟨F.unop.mul_assoc', F.unop.mul_one', F.unop.one_mul'⟩,
                  F.unop.mul_inv, F.unop.inv_mul⟩
            { comul := mToComul F.unop.m
              counit := eToCounit F.unop.e
              coassoc := by ext x; exact congr($(i.1.coassoc) x)
              rTensor_counit_comp_comul := i.1.2
              lTensor_counit_comp_comul := i.1.3
              counit_one := (eToCounit F.unop.e).map_one
              mul_compr₂_counit := i.1.4
              comul_one := (mToComul F.unop.m).map_one
              mul_compr₂_comul := i.1.5
              antipode := iToAntipode F.unop.i
              mul_antipode_rTensor_comul := i.2
              mul_antipode_lTensor_comul := i.mul_antipode_lTensor_comul } }
      map := sorry
      map_id := sorry
      map_comp := sorry }

noncomputable def commAlgebraCatToAffineGroup :
    HopfAlgCat.{v} k ⥤ (AffineGroup k)ᵒᵖ := 
  { obj := fun H ↦
    { unop :=
      let i := isAffineGroupWithChosenMulAndUnitAndInverse_iff_isBialgebraWithChosenComulAndCounitAndAntipode
        (Bialgebra.comulAlgHom k H) (Bialgebra.counitAlgHom k H) sorry |>.mpr sorry
      { toFunctor := coyoneda.obj (op <| CommAlgebraCat.of k H)
        corep := inferInstance
        m := (comulToMul <| Bialgebra.comulAlgHom _ _)
        e := (counitToUnit <| Bialgebra.counitAlgHom _ _)
        mul_assoc' := sorry
        mul_one' := sorry
        one_mul' := sorry
        i := (antipodeToInverse <| sorry)
        mul_inv := sorry
        inv_mul := sorry } }
    map := sorry
    map_id := sorry
    map_comp := sorry }

/--
The antiequivalence from affine group functor to category of hopf algebra.
-/
noncomputable def affineGroupAntiEquivCommAlgCat :
    (AffineGroup k)ᵒᵖ ≌ HopfAlgCat.{v} k where
  functor := affineGroupAntiToCommAlgCat k
  inverse := commAlgebraCatToAffineGroup k
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry
