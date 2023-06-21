From MuMuT Require Import Prelude.
From MuMuT.Utils Require Import Psh Ctx.

Inductive ty0 : Type :=
| Zer : ty0
| One : ty0
| Prod : ty0 -> ty0 -> ty0
| Sum : ty0 -> ty0 -> ty0
| Arr : ty0 -> ty0 -> ty0
.

(*| .. coq:: none |*)
Derive NoConfusion for ty0.
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty0.

(*||*)
Notation "⊥" := (Zer) : ty_scope.
Notation "⊤" := (One) : ty_scope.
Notation "A × B" := (Prod A B) (at level 40) : ty_scope.
Notation "A + B" := (Sum A B) : ty_scope.
Notation "A → B" := (Arr A B) (at level 40) : ty_scope.

Variant ty : Type :=
| VTy : ty0 -> ty
| KTy : ty0 -> ty
.
Derive NoConfusion for ty.
Bind Scope ty_scope with ty.
Notation "'t+' t" := (VTy t) (at level 20) : ty_scope .
Notation "'t-' t" := (KTy t) (at level 20) : ty_scope .
Open Scope ty_scope.

Equations t_neg : ty -> ty :=
  t_neg (t+ a) := t- a ;
  t_neg (t- a) := t+ a .

Definition t_ctx : Type := Ctx.ctx ty.
Bind Scope ctx_scope with t_ctx.

Inductive term : t_ctx -> ty -> Type :=
| Var {Γ a} : Γ ∋ a -> term Γ a

| Mu {Γ a} : conf (Γ ▶ t- a) -> term Γ (t+ a)
| Mu' {Γ a} : conf (Γ ▶ t+ a) -> term Γ (t- a)

| OneI {Γ} : term Γ (t+ ⊤)
| Inl {Γ a b} : term Γ (t+ a) -> term Γ (t+ (a + b))
| Inr {Γ a b} : term Γ (t+ b) -> term Γ (t+ (a + b))
| Lam {Γ a b} : term (Γ ▶ t+ a) (t+ b) -> term Γ (t+ (a → b))
| Pair {Γ a b} : term Γ (t+ a) -> term Γ (t+ b) -> term Γ (t+ (a × b))

| ZerK {Γ} : term Γ (t- ⊥)
| App {Γ a b} : term Γ (t+ a) -> term Γ (t- b) -> term Γ (t- (a → b))
| Fst {Γ a b} : term Γ (t- a) -> term Γ (t- (a × b))
| Snd {Γ a b} : term Γ (t- b) -> term Γ (t- (a × b))
| Match {Γ a b} : conf (Γ ▶ t+ a) -> conf (Γ ▶ t+ b) -> term Γ (t- (a + b))
with conf : t_ctx -> Type :=
| Cut {Γ a} : term Γ (t+ a) -> term Γ (t- a) -> conf Γ
.

Definition s_var {Γ} : Γ =[term]> Γ := fun _ i => Var i .

Equations t_rename {Γ Δ} : Γ ⊆ Δ -> term Γ ⇒ᵢ term Δ :=
  t_rename f _ (Var i)    := Var (f _ i) ;
  t_rename f _ (Mu c)     := Mu (c_rename (r_shift f) c) ;
  t_rename f _ (Mu' c)    := Mu' (c_rename (r_shift f) c) ;
  t_rename f _ (OneI)     := OneI ;
  t_rename f _ (Lam u)    := Lam (t_rename (r_shift f) _ u) ;
  t_rename f _ (Pair u v) := Pair (t_rename f _ u) (t_rename f _ v) ;
  t_rename f _ (Inl u)    := Inl (t_rename f _ u) ;
  t_rename f _ (Inr u)    := Inr (t_rename f _ u) ;
  t_rename f _ (ZerK)     := ZerK ;
  t_rename f _ (App u k)  := App (t_rename f _ u) (t_rename f _ k) ;
  t_rename f _ (Fst k)    := Fst (t_rename f _ k) ;
  t_rename f _ (Snd k)    := Snd (t_rename f _ k) ;
  t_rename f _ (Match c1 c2) :=
    Match (c_rename (r_shift f) c1)
          (c_rename (r_shift f) c2)
with c_rename {Γ Δ} : Γ ⊆ Δ -> conf Γ -> conf Δ :=
   c_rename f (Cut v k) := Cut (t_rename f _ v) (t_rename f _ k) .

Definition a_ren {Γ1 Γ2 Γ3} : Γ2 ⊆ Γ3 -> Γ1 =[term]> Γ2 -> Γ1 =[term]> Γ3 :=
  fun f g _ i => t_rename f _ (g _ i) .

Definition t_shift {Γ} [y] : term Γ ⇒ᵢ term (Γ ▶ y) := @t_rename _ _ s_pop.
Definition c_shift {Γ} [y] : conf Γ -> conf (Γ ▶ y) := @c_rename _ _ s_pop.

Definition a_shift {Γ Δ} [y] (a : Γ =[term]> Δ) : (Γ ▶ y) =[term]> (Δ ▶ y) :=
  s_append (fun _ i => t_shift _ (a _ i)) (Var top).

(*  μx. ⟨ inr ( λy. μz. ⟨ inl z | x ⟩ ) | x ⟩    *)
Definition LEM {a} : term ∅ (t+ (a + (a → Zer))) :=
  Mu (Cut (Inr (Lam (Mu (Cut (Inl (Var (pop top)))
                             (Var (pop (pop top)))))))
           (Var top)) .

Equations t_subst {Γ Δ} : Γ =[term]> Δ -> term Γ ⇒ᵢ term Δ :=
  t_subst f _ (Var i)    := f _ i ;
  t_subst f _ (Mu c)     := Mu (c_subst (a_shift f) c) ;
  t_subst f _ (Mu' c)    := Mu' (c_subst (a_shift f) c) ;
  t_subst f _ (OneI)     := OneI ;
  t_subst f _ (Lam u)    := Lam (t_subst (a_shift f) _ u) ;
  t_subst f _ (Pair u v) := Pair (t_subst f _ u) (t_subst f _ v) ;
  t_subst f _ (Inl u)    := Inl (t_subst f _ u) ;
  t_subst f _ (Inr u)    := Inr (t_subst f _ u) ;
  t_subst f _ (ZerK)     := ZerK ;
  t_subst f _ (App u k)  := App (t_subst f _ u) (t_subst f _ k) ;
  t_subst f _ (Fst k)    := Fst (t_subst f _ k) ;
  t_subst f _ (Snd k)    := Snd (t_subst f _ k) ;
  t_subst f _ (Match c1 c2) :=
    Match (c_subst (a_shift f) c1)
          (c_subst (a_shift f) c2)
with c_subst {Γ Δ} : Γ =[term]> Δ -> conf Γ -> conf Δ :=
   c_subst f (Cut v k) := Cut (t_subst f _ v) (t_subst f _ k) .

Definition a_comp {Γ1 Γ2 Γ3} : Γ2 =[term]> Γ3 -> Γ1 =[term]> Γ2 -> Γ1 =[term]> Γ3 :=
  fun f g _ i => t_subst f _ (g _ i) .

Definition ass1 {Γ a} (v : term Γ a) : (Γ ▶ a) =[term]> Γ := s_append s_var v .

Definition t_subst1 {Γ a b} (u : term (Γ ▶ a) b) v := t_subst (ass1 v) _ u.
Definition c_subst1 {Γ a} (u : conf (Γ ▶ a)) v := c_subst (ass1 v) u.

Notation "u /ₜ ρ" := (t_subst ρ _ u) (at level 50, left associativity).
Notation "c /ₛ ρ" := (c_subst ρ c) (at level 50, left associativity).
Notation "u /ₜ₁ v" := (t_subst1 u v) (at level 50, left associativity).
Notation "c /ₛ₁ v" := (c_subst1 c v) (at level 50, left associativity).

Variant mu_red {Γ} : conf Γ -> conf Γ -> Prop :=
  | RMu {a} {c : conf (Γ ▶ t- a)} {k : term Γ (t- a)}
    : mu_red (Cut (Mu c) k) (c /ₛ₁ k)
  | RMu' {a} {v : term Γ (t+ a)} {c : conf (Γ ▶ t+ a)}
    : mu_red (Cut v (Mu' c)) (c /ₛ₁ v)
  | RApp {a b} {u : term (Γ ▶ t+ a) (t+ b)} {v : term Γ (t+ a)}
      {k : term Γ (t- b)}
    : mu_red (Cut (Lam u) (App v k)) (Cut (u /ₜ₁ v) k)
  | RFst {a b} {u : term Γ (t+ a)} {v : term Γ (t+ b)} {k : term Γ (t- a)}
    : mu_red (Cut (Pair u v) (Fst k)) (Cut u k)
  | RSnd {a b} {u : term Γ (t+ a)} {v : term Γ (t+ b)} {k : term Γ (t- b)}
    : mu_red (Cut (Pair u v) (Snd k)) (Cut v k)
  | RInl {a b} {u : term Γ (t+ a)} {c1 : conf (Γ ▶ t+ a)} {c2 : conf (Γ ▶ t+ b)}
    : mu_red (Cut (Inl u) (Match c1 c2)) (c1 /ₛ₁ u)
  | RInr {a b} {u : term Γ (t+ b)} {c1 : conf (Γ ▶ t+ a)} {c2 : conf (Γ ▶ t+ b)}
    : mu_red (Cut (Inr u) (Match c1 c2)) (c2 /ₛ₁ u) .

Inductive mu_red_star {Γ} (u : conf Γ) : conf Γ -> Prop :=
| RRefl : mu_red_star u u
| RStep {v w} : mu_red u v -> mu_red_star v w -> mu_red_star u w
.
Arguments RRefl {Γ u}.
Arguments RStep {Γ u v w}.

#[global] Notation "c1 ↦ c2" := (mu_red c1 c2) (at level 40).
#[global] Notation "c1 ↦* c2" := (mu_red_star c1 c2) (at level 40).
