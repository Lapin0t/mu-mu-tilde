From MuMuT Require Import Prelude.
From MuMuT.Utils Require Import Psh Ctx.
From MuMuT.Lang Require Import Syntax Properties.

(*|
Basic Notions
=============

Poles
-----

Predicates on μμ~ configurations closed by anti-reduction.
|*)
Record ortho : Type := {
  pole : forall Γ, conf Γ -> Type ;
  expand : forall Γ (c1 c2 : conf Γ), c1 ↦ c2 -> pole Γ c2 -> pole Γ c1
}.
(*|
.. coq:: none
|*)
Arguments expand o {Γ c1 c2}.

(*|
Predicates on terms
-------------------
|*)
Definition Pred (A : ty) : Type := forall Γ, term Γ A -> Type .

(*|
Inclusion.
|*)
Definition entails {A} (P Q : Pred A) : Type := forall Γ (u : term Γ A), P Γ u -> Q Γ u .
Notation "P ⊑ Q" := (entails P Q) (at level 40).

(*|
"Bi-Sets"
---------

These are sets of terms and co-terms at the same type, still represented as predicates.
|*)
Record Pred2 (A : ty0) := { pos : Pred (t+ A) ; neg : Pred (t- A) } .
Arguments pos {A}.
Arguments neg {A}.
Notation "P ⁺" := (P.(pos)) (at level 10).
Notation "P ⁻" := (P.(neg)) (at level 10).

(*|
"Definedness" order: arrows go in the same direction for positive and negative sets.
|*)
Definition def_ord {A} (P Q : Pred2 A) : Type := (P⁺ ⊑ Q⁺) * (P⁻ ⊑ Q⁻) .
Notation "P ⊑₂ Q" := (def_ord P Q) (at level 42).

(*|
Extensional equality.
|*)
Definition def_eqv {A} (P Q : Pred2 A) : Type := (P ⊑₂ Q) * (Q ⊑₂ P) .
Notation "P ≡ Q" := (def_eqv P Q) (at level 42).

Section realizability.
(*|
Realizability
=============

Let's fix a pole O.
|*)
  Context (O : ortho).

  Notation "c ∈ ⫫" := (pole O _ c) (at level 30).
  Notation "u ⫫ k" := (pole O _ (Cut u k)) (at level 30).

(*|
Preliminary Constructions
-------------------------

Before interpreting types we need a couple tools. These will work the same way for every type A.
|*)
  Section basics.
    Context {A : ty0}.

(*|
First we define both the right orthogonal and the left orthogonal of sets of terms.
|*)
    Definition negR (P : Pred (t+ A)) : Pred (t- A) := fun Γ k => forall u, P Γ u -> u ⫫ k .
    Notation "P ⫫" := (negR P) (at level 30).

    Definition negL (P : Pred (t- A)) : Pred (t+ A) := fun Γ u => forall k, P Γ k -> u ⫫ k .
    Notation "⫫ P" := (negL P) (at level 30).

(*|
We continue with the negation, or "orthogonal" of a bi-set, together with a couple properties:
- contravariancy with respect to definedness
- double-negation introduction
- triple-negation elimination
|*)
    Definition neg2 (P : Pred2 A) : Pred2 A := {| pos := ⫫P⁻ ; neg := P⁺⫫ |}.
    Notation "P †" := (neg2 P) (at level 30).

    Definition neg_contra (P Q : Pred2 A) : P ⊑₂ Q -> Q† ⊑₂ P†
      := fun H => (fun Γ u q k p => q k (snd H Γ k p), fun Γ u q v p => q v (fst H Γ v p)) .

    Definition DNI (P : Pred2 A) : P ⊑₂ P††
      := ( fun Γ u p k q => q u p , fun Γ u p k q => q u p ).

    Definition TNE (P : Pred2 A) : P††† ⊑₂ P†
      := neg_contra _ _ (DNI P) .

(*|
Perhaps the most important definition: a bi-set is said to be "saturated" (or sometimes "orthogonality
candidate" or "stable") whenever its set of terms (resp coterms) is equal to the orthogonal of its set
of coterms (resp terms).

We also define 3 helpers to access the interesting parts of this property:

- Constructing an element of the pole.
- Eliminating the orthogonal.
|*)
    Definition saturated (P : Pred2 A) := P ≡ P†.  

    Definition ortho_sound {P : Pred2 A} (H : saturated P) {Γ u k} : P⁺ Γ u -> P⁻ Γ k -> u ⫫ k
      := fun p q => fst (fst H) Γ u p k q .

    Definition ortho_elimP {P : Pred2 A} (H : saturated P) {Γ u} : (⫫P⁻) Γ u -> P⁺ Γ u
      := fst (snd H) Γ u.

    Definition ortho_elimN {P : Pred2 A} (H : saturated P) {Γ k} : (P⁺⫫) Γ k -> P⁻ Γ k
      := snd (snd H) Γ k.

(*|
We know tackle the work of constucting saturated bi-sets. By the magic of orthogonality, taking the orthogonal
two times is enough to hit the ceiling! As usual there are two variants, depending on the polarity.
|*)
    Definition mkP (P : Pred (t+ A)) := {| pos := P ; neg := P⫫ |} .
    Definition mkN (P : Pred (t- A)) := {| pos := ⫫P ; neg := P |} .

    Definition complP (P : Pred (t+ A)) := (mkP P) † . (* {| pos := ⫫(P⫫) ; neg := P⫫ |} *)
    Definition complN (P : Pred (t- A)) := (mkN P) † . (* {| pos := ⫫P ; neg := (⫫P)⫫ |} *)
    Notation "⇑⁺ P " := (complP P) (at level 50).
    Notation "⇑⁻ P " := (complN P) (at level 50).
    

    Definition compP_sat (P : Pred (t+ A)) : saturated (⇑⁺ P)
      := ((fun _ _ p => p , snd (DNI (mkP P))),
          (fun _ _ p => p , snd (TNE (mkP P)))) .

    Definition compN_sat (P : Pred (t- A)) : saturated (⇑⁻ P)
      := ((fst (DNI (mkN P)) , fun _ _ p => p),
          (fst (TNE (mkN P)) , fun _ _ p => p)) .

(*|
And this completes our preliminary work.
|*)
  End basics.
  Notation "⇑⁺ P " := (complP P) (at level 50).
  Notation "⇑⁻ P " := (complN P) (at level 50).

(*|
## Interpretation of types

For each type constructor, we need to construct a bi-set interpreting the "nice" terms and co-terms. Depending on
the polarity of the type former, we construct this by taking the completion of either a predicate on the terms or
the co-terms of this type. These predicate caracterize the (co-)patterns. Our polarities are given by:

- Zero : +
- One  : -
- Prod : - → - → -
- Plus : + → + → +
- Fun  : + → - → -
|*)
  Equations ok_zer : Pred (t+ ⊥) :=
    ok_zer Γ _ := T0 .

  Equations ok_one : Pred (t- ⊤) :=
    ok_one Γ _ := T0 .

  Equations ok_prod {A B} (P : Pred (t- A)) (Q : Pred (t- B)) : Pred (t- (A × B)) :=
    ok_prod P Q Γ (Fst k) := P Γ k ;
    ok_prod P Q Γ (Snd k) := Q Γ k ;
    ok_prod P Q Γ _       := T0 .

  Equations ok_sum {A B} (P : Pred (t+ A)) (Q : Pred (t+ B)) : Pred (t+ (A + B)) :=
    ok_sum P Q Γ (Inl u) := P Γ u ;
    ok_sum P Q Γ (Inr u) := Q Γ u ;
    ok_sum P Q Γ _       := T0 .

  Equations ok_arr {A B} (P : Pred (t+ A)) (Q : Pred (t- B)) : Pred (t- (A → B)) :=
    ok_arr P Q Γ (App v k) := P Γ v * Q Γ k ;
    ok_arr P Q Γ _         := T0 .

  Notation "⟦⊥⟧" := (ok_zer) (at level 30).
  Notation "⟦⊤⟧" := (ok_one) (at level 30).
  Notation "P ⟦×⟧ Q" := (ok_prod P Q) (at level 30).
  Notation "P ⟦+⟧ Q" := (ok_sum P Q) (at level 30).
  Notation "P ⟦→⟧ Q" := (ok_arr P Q) (at level 30).

(*|
With all the "niceness" predicates defined we can now interpret any type by saturation and induction. We also
prove it is saturated, which was the whole point.
|*)
  Equations interp_ty0 (A : ty0) : Pred2 A :=
    interp_ty0 (⊥)      := ⇑⁺ ⟦⊥⟧ ;
    interp_ty0 (⊤)      := ⇑⁻ ⟦⊤⟧ ;
    interp_ty0 (A × B)  := ⇑⁻ interp_ty0 A⁻ ⟦×⟧ interp_ty0 B⁻ ;
    interp_ty0 (A + B)  := ⇑⁺ interp_ty0 A⁺ ⟦+⟧ interp_ty0 B⁺ ;
    interp_ty0 (A → B) := ⇑⁻ interp_ty0 A⁺ ⟦→⟧ interp_ty0 B⁻ .

  Definition interp_sat A : saturated (interp_ty0 A).
    destruct A;
      [ apply compP_sat
      | apply compN_sat
      | apply compN_sat
      | apply compP_sat
      | apply compN_sat ] .
  Defined.

(*|
## Finally the realizability predicates!

First we explain what it means for a term to realize a type. A term `u` *realizes* a type `A`, written `u ⊩ₜ A`
if we can prove that the term inhabits the semantic interpretation of the type, that is if the "niceness"
predicate is inhabited at `u`.
|*)
  Equations interp_ty (A : ty) : Pred A :=
    interp_ty (t+ A) := interp_ty0 A⁺ ; 
    interp_ty (t- A) := interp_ty0 A⁻ .
  Notation "u ⊩ₜ A" := (@interp_ty A _ u) (at level 40).

(*|
Similarly, a substitution `ρ` realizes a context `Γ` if for every `i : A ∈ Γ` the i-th element of `ρ` realizes `A`.
|*)
  Definition interp_a {Γ Δ} (ρ : Γ =[term]> Δ) := forall A i, ρ A i ⊩ₜ A .
  Notation "ρ ⊩ₐ Γ" := (@interp_a Γ _ ρ) (at level 40).

(*|
As is usual in categorical semantics, a term is interpreted as some kind of morphism between the interpretation
of its context to the interpretation of its type.

- The semantic interpretation of a term jugment is a uniform realizer of the type: a function taking a
  substitution realizing the context to a proof that the substituted term realizes the type.
- The semantic interpretation of a configuration jugment is similar, taking a substitution realizing the
  context to a proof that the substituted configuration is part of the pole.

Much like glueing, our semantic category for terms here looks like `{ u : term Γ A & u ⊩ₐ A }` which is
fibered on the syntactic category and our semantic morphisms from contexts to types live above their
syntactic counterpart (substitution). We present it in indexed fashion, working directly with the fibers
instead of the total space as is customary in type theory.
|*)
  Definition interp_t {Γ A} (u : term Γ A) := forall Δ (ρ : _ =[_]> Δ), ρ ⊩ₐ Γ -> (u /ₜ ρ) ⊩ₜ A .
  Definition interp_c {Γ}   (c : conf Γ)   := forall Δ (ρ : _ =[_]> Δ), ρ ⊩ₐ Γ -> (c /ₛ ρ) ∈ ⫫ .

(*|
Our last helper before the main proof: a substitution realizing a context can be extended by a term realizing
some type, this will be useful to extend the substitution while going under binders during the proof.
|*)
  Definition append_interp_a {Γ Δ} {ρ : Γ =[term]> Δ} {A u} (H1 : ρ ⊩ₐ Γ) (H2 : u ⊩ₜ A)
             : a_comp (ass1 u) (a_shift ρ) ⊩ₐ (Γ ▶ A).
    intros ? i; dependent elimination i; [ exact H2 | ].
    unfold a_comp, a_shift, t_shift; cbn; rewrite t_sub_ren.
    erewrite (t_sub_eq (ass1 u ⊛ᵣ s_pop) s_var); try reflexivity.
    rewrite t_sub_id_l.
    exact (H1 _ h).
  Defined.

(*|
## Adequacy

Every well-typed term verifies the niceness predicate! This goes by induction on the syntax, there are a couple
different cases, which slightly mimic a reduction procedure.

In the simple cases where the head-constructor looks like a (co)pattern for the type we recurse directly on
the subterms. In the other cases we use the antireduction of the pole to recurse on a simpler term (growing
the substitution), together with some use of the saturation property to land back on our feets.
|*)
  Scheme term_mutT := Induction for term Sort Type
    with conf_mutT := Induction for conf Sort Type.

  Definition t_adequacy {Γ A} (u : term Γ A) : interp_t u .
    revert Γ A u; apply (term_mutT (@interp_t) (@interp_c)).
    all: unfold interp_t, interp_c in * ; repeat intro; cbn.
  - exact (X _ h).
  - apply (ortho_elimP (interp_sat _)).
    intros k p.
    apply (O.(expand) RMu).
    unfold c_subst1; rewrite c_sub_sub.
    exact (X _ _ (append_interp_a X0 p)).
  - apply (ortho_elimN (interp_sat _)).
    intros v p.
    apply (O.(expand) RMu').
    unfold c_subst1; rewrite c_sub_sub.
    exact (X _ _ (append_interp_a X0 p)).
  - dependent elimination k; inversion X0.
  - exact (X1 (Inl _) (X _ _ X0)).
  - exact (X1 (Inr _) (X _ _ X0)).
  - dependent elimination k; cbn in *; try now inversion X1.
    apply (O.(expand) RApp).
    unfold t_subst1; rewrite t_sub_sub. 
    apply (ortho_sound (interp_sat _)).
    + exact (X _ _ (append_interp_a X0 (fst X1))).
    + exact (snd X1).
  - dependent elimination k; cbn in *; try now inversion X2.
    + apply (O.(expand) RFst).
      apply (fst (fst (interp_sat _))).
      * exact (X _ _ X1).
      * exact X2.
    + apply (O.(expand) RSnd).
      apply (fst (fst (interp_sat _))).
      * exact (X0 _ _ X1).
      * exact X2.
  - dependent elimination u; inversion X0.
  - exact (X2 (App _ _) (X _ _ X1 , X0 _ _ X1)).
  - exact (X1 (Fst _) (X _ _ X0)).
  - exact (X1 (Snd _) (X _ _ X0)).
  - dependent elimination u; cbn in *; try now inversion X2.
    + apply (O.(expand) RInl).
      unfold c_subst1; rewrite c_sub_sub.
      exact (X _ _ (append_interp_a X1 X2)).
    + apply (O.(expand) RInr).
      unfold c_subst1; rewrite c_sub_sub. 
      exact (X0 _ _ (append_interp_a X1 X2)).
  - apply (ortho_sound (interp_sat _)).
    + exact (X _ _ X1).
    + exact (X0 _ _ X1).
  Defined.

  Equations c_adequacy {Γ} (c : conf Γ) : interp_c c :=
    c_adequacy (Cut u k) Δ ρ H := fst (fst (interp_sat _)) _ _ (t_adequacy u Δ ρ H) _ (t_adequacy k Δ ρ H) .

End realizability.
