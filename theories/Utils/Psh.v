From MuMuT Require Import Prelude.

(* (covariant) presheaves *)
Notation psh I := (I -> Type).

Declare Scope indexed_scope.
Open Scope indexed_scope.
Delimit Scope indexed_scope with indexed.

(* pointwise arrows *)
Definition arrᵢ {I} (X Y : psh I) : Type := forall i, X i -> Y i.
#[global] Infix "⇒ᵢ" := (arrᵢ) (at level 20) : indexed_scope.

Definition voidᵢ {I : Type} : I -> Type := fun _ => T0.
#[global] Notation "∅ᵢ" := (voidᵢ) : indexed_scope.

Definition sumᵢ {I} (X Y : psh I) : psh I := fun i => (X i + Y i)%type.
#[global] Infix "+ᵢ" := (sumᵢ) (at level 20) : indexed_scope.

Definition prodᵢ {I} (X Y : psh I) : psh I := fun i => (X i * Y i)%type.
#[global] Infix "×ᵢ" := (prodᵢ) (at level 20) : indexed_scope.

#[global] Notation "⦉ X ⦊ᵢ" := (sigT X) : type_scope.
 
(* pointwise arrows between F G : endo (psh I) *)
#[global] Notation "F ⇒ₙ G" := (forall X : psh _, F X ⇒ᵢ G X) (at level 30).

Equations joinᵢ {I J} (X : psh I) (Y : psh J) : psh (I * J) :=
  joinᵢ X Y (i , j) := X i + Y j.


Inductive fiber {A B} (f : A -> B) : psh B := Fib a : fiber f (f a).
Arguments Fib {A B f}.
Derive NoConfusion for fiber.

Equations fib_extr {A B} {f : A -> B} {b : B} : fiber f b -> A :=
  fib_extr (Fib a) := a .
Equations fib_coh {A B} {f : A -> B} {b : B} : forall p : fiber f b, f (fib_extr p) = b :=
  fib_coh (Fib _) := eq_refl .
Definition fib_constr {A B} {f : A -> B} a : forall b (p : f a = b), fiber f b :=
  eq_rect (f a) (fiber f) (Fib a).
 
(* These two functions form an isomorphism (fiber f ⇒ᵢ X) ≅ (∀ a → X (f a)) *)
Equations fib_into {A B} {f : A -> B} X (h : forall a, X (f a)) : fiber f ⇒ᵢ X :=
  fib_into _ h _ (Fib a) := h a .
Definition fib_from {A B} {f : A -> B} X (h : fiber f ⇒ᵢ X) a : X (f a) :=
  h _ (Fib a).

(* These two functions form an isomorphism (X @ i ⇒ᵢ Y) ≅ (X → Y i *)
#[global] Notation "X @ i" := (fiber (fun (_ : X) => i)) (at level 20) : indexed_scope.
Definition pin {I X} (i : I) : X -> (X @ i) i := Fib.
Definition pin_from {I X Y} {i : I} : ((X @ i) ⇒ᵢ Y) -> (X -> Y i) := fib_from _.
Definition pin_into {I X Y} {i : I} : (X -> Y i) -> (X @ i ⇒ᵢ Y) := fib_into _.

Equations pin_map {I X Y} (f : X -> Y) {i : I} : (X @ i) ⇒ᵢ (Y @ i) :=
  pin_map f _ (Fib x) := Fib (f x) .
