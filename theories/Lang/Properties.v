From MuMuT Require Import Prelude.
From MuMuT.Utils Require Import Psh Ctx.
From MuMuT.Lang Require Import Syntax.

Scheme term_mut := Induction for term Sort Prop
  with conf_mut := Induction for conf Sort Prop.

Record ind_args (P_t : forall Γ a, term Γ a -> Prop) (P_c : forall Γ, conf Γ -> Prop) :=
  {
    x_var : forall (Γ : ctx ty) (a : ty) (h : Γ ∋ a), P_t Γ a (Var h) ;
    x_mu : forall (Γ : ctx ty) (a : ty0) (c : conf (Γ ▶ t- a)),
        P_c (Γ ▶ t- a)%ctx c -> P_t Γ (t+ a) (Mu c) ;
    x_mu' : forall (Γ : ctx ty) (a : ty0) (c : conf (Γ ▶ t+ a)),
        P_c (Γ ▶ t+ a)%ctx c -> P_t Γ (t- a) (Mu' c) ;
    x_onei : forall Γ : t_ctx, P_t Γ (t+ ⊤) OneI ;
    x_inl : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t+ a)), P_t Γ (t+ a) t -> P_t Γ (t+ (a + b)) (Inl t) ;
    x_inr : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t+ b)), P_t Γ (t+ b) t -> P_t Γ (t+ (a + b)) (Inr t) ;
    x_lam : forall (Γ : ctx ty) (a b : ty0) (t : term (Γ ▶ t+ a) (t+ b)), P_t (Γ ▶ t+ a)%ctx (t+ b) t -> P_t Γ (t+ (a → b)) (Lam t) ;
    x_pair : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t+ a)),
        P_t Γ (t+ a) t ->
        forall t0 : term Γ (t+ b), P_t Γ (t+ b) t0 -> P_t Γ (t+ (a × b)) (Pair t t0) ;
    x_zerk : forall Γ : t_ctx, P_t Γ (t- ⊥) ZerK ;
    x_app : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t+ a)),
        P_t Γ (t+ a) t ->
        forall t0 : term Γ (t- b), P_t Γ (t- b) t0 -> P_t Γ (t- (a → b)) (App t t0) ;
    x_fst : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t- a)),
        P_t Γ (t- a) t -> P_t Γ (t- (a × b)) (Fst t) ;
    x_snd : forall (Γ : t_ctx) (a b : ty0) (t : term Γ (t- b)),
        P_t Γ (t- b) t -> P_t Γ (t- (a × b)) (Snd t) ;
    x_match : forall (Γ : ctx ty) (a b : ty0) (c : conf (Γ ▶ t+ a)),
        P_c (Γ ▶ t+ a)%ctx c ->
        forall c0 : conf (Γ ▶ t+ b),
        P_c (Γ ▶ t+ b)%ctx c0 -> P_t Γ (t- (a + b)) (Match c c0) ;
    x_cut : forall (Γ : t_ctx) (a : ty0) (t : term Γ (t+ a)),
        P_t Γ (t+ a) t -> forall t0 : term Γ (t- a), P_t Γ (t- a) t0 -> P_c Γ (Cut t t0) ;
} .

Lemma t_ind_mut P_t P_c (arg : ind_args P_t P_c) Γ a (x : term Γ a) : P_t Γ a x .
  destruct arg; now apply (term_mut P_t P_c).
Qed.

Lemma c_ind_mut P_t P_c (arg : ind_args P_t P_c) Γ (x : conf Γ) : P_c Γ x .
  destruct arg; now apply (conf_mut P_t P_c).
Qed.

Definition t_ren_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> t_rename f1 a t = t_rename f2 a t .
Definition c_ren_proper_P Γ (c : conf Γ) : Prop :=
  forall Δ (f1 f2 : Γ ⊆ Δ), f1 ≡ₐ f2 -> c_rename f1 c = c_rename f2 c .
Lemma ren_proper_prf : ind_args t_ren_proper_P c_ren_proper_P.
  econstructor.
  all: unfold t_ren_proper_P, c_ren_proper_P.
  all: intros; cbn; f_equal; auto.
  all: try apply H; try apply H0; auto.
  all: apply r_shift_eq; auto.
Qed.

#[global] Instance t_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_rename Γ Δ).
intros f1 f2 H1 a x y ->; now apply (t_ind_mut _ _ ren_proper_prf).
Qed.

#[global] Instance c_ren_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@c_rename Γ Δ).
intros f1 f2 H1 x y ->; now apply (c_ind_mut _ _ ren_proper_prf).
Qed.

Definition t_ren_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    t_rename f1 a (t_rename f2 a t) = t_rename (s_ren f1 f2) a t.
Definition c_ren_ren_P Γ1 (c : conf Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2),
    c_rename f1 (c_rename f2 c) = c_rename (s_ren f1 f2) c.

Lemma ren_ren_prf : ind_args t_ren_ren_P c_ren_ren_P.
  econstructor; unfold t_ren_ren_P, c_ren_ren_P.
  all: intros; cbn; f_equal; auto.
  all: rewrite r_shift_comp; auto.
Qed.

Lemma t_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : t_rename f1 a (t_rename f2 a t) = t_rename (s_ren f1 f2) a t.
now apply (t_ind_mut _ _ ren_ren_prf). Qed.
Lemma c_ren_ren {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 ⊆ Γ2) (c : conf Γ1)
  : c_rename f1 (c_rename f2 c) = c_rename (s_ren f1 f2) c.
now apply (c_ind_mut _ _ ren_ren_prf). Qed.

Definition t_ren_id_l_P Γ a (t : term Γ a) : Prop := t_rename r_id a t = t.
Definition c_ren_id_l_P Γ (c : conf Γ) : Prop := c_rename r_id c = c.

Lemma ren_id_l_prf : ind_args t_ren_id_l_P c_ren_id_l_P.
  econstructor; unfold t_ren_id_l_P, c_ren_id_l_P.
  all: intros; cbn; f_equal; auto.
  all: rewrite r_shift_id; auto.
Qed.

Lemma t_ren_id_l {Γ} a (t : term Γ a) : t_rename r_id a t = t.
now apply (t_ind_mut _ _ ren_id_l_prf). Qed.
Lemma c_ren_id_l {Γ} (c : conf Γ) : c_rename r_id c = c.
now apply (c_ind_mut _ _ ren_id_l_prf). Qed.
  
#[global] Instance a_shift_eq {Γ Δ y} : Proper (ass_eq _ _ ==> ass_eq _ _) (@a_shift Γ Δ y).
  intros f1 f2 H.
  apply s_append_eq; auto.
  intros ? i; rewrite H; auto.
Qed.

Lemma a_shift_id {Γ a} : @a_shift Γ Γ a s_var ≡ₐ s_var.
  intros x i; destruct x; dependent elimination i; auto.
Qed.

Definition t_sub_proper_P Γ a (t : term Γ a) : Prop :=
  forall Δ (f1 f2 : Γ =[term]> Δ), f1 ≡ₐ f2 -> t_subst f1 a t = t_subst f2 a t .
Definition c_sub_proper_P Γ (c : conf Γ) : Prop :=
  forall Δ (f1 f2 : Γ =[term]> Δ), f1 ≡ₐ f2 -> c_subst f1 c = c_subst f2 c .

Lemma sub_proper_prf : ind_args t_sub_proper_P c_sub_proper_P.
  econstructor; unfold t_sub_proper_P, c_sub_proper_P.
  all: intros; cbn; f_equal; auto.
  all: try apply H; try apply H0; now apply a_shift_eq.
Qed.

#[global] Instance t_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> forall_relation (fun a => eq ==> eq)) (@t_subst Γ Δ).
  intros f1 f2 H1 a x y ->; now apply (t_ind_mut _ _ sub_proper_prf).
Qed.

#[global] Instance c_sub_eq {Γ Δ}
  : Proper (ass_eq _ _ ==> eq ==> eq) (@c_subst Γ Δ).
  intros f1 f2 H1 x y ->; now apply (c_ind_mut _ _ sub_proper_prf).
Qed.
Definition t_ren_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[term]> Γ2),
    t_rename f1 a (t_subst f2 a t)
    = t_subst (a_ren f1 f2) a t .
Definition c_ren_sub_P Γ1 (c : conf Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[term]> Γ2),
    c_rename f1 (c_subst f2 c)
    = c_subst (a_ren f1 f2) c .

Lemma a_ren_shift {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[ term ]> Γ2) {a : ty}
  : a_ren (r_shift (a:=a) f1) (a_shift f2) ≡ₐ a_shift (a_ren f1 f2) .
  intros ? i; dependent elimination i; cbn; auto.
  unfold t_shift, a_ren; rewrite 2 t_ren_ren; reflexivity.
Qed.
  

Lemma ren_sub_prf : ind_args t_ren_sub_P c_ren_sub_P.
  econstructor; unfold t_ren_sub_P, c_ren_sub_P.
  all: intros; cbn; f_equal; auto.
  all: rewrite <- (a_ren_shift f1 f2); auto.
Qed.

  
Lemma t_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[term]> Γ2) a (t : term Γ1 a)
  : t_rename f1 a (t_subst f2 a t) = t_subst (a_ren f1 f2) a t.
now apply (t_ind_mut _ _ ren_sub_prf). Qed.
Lemma c_ren_sub {Γ1 Γ2 Γ3} (f1 : Γ2 ⊆ Γ3) (f2 : Γ1 =[term]> Γ2) (c : conf Γ1)
  : c_rename f1 (c_subst f2 c) = c_subst (a_ren f1 f2) c.
now apply (c_ind_mut _ _ ren_sub_prf). Qed.
  
Lemma a_shift_ren {Γ1 Γ2 Γ3 y} (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 ⊆ Γ2)
  : a_shift (y:=y) (s_ren f1 f2) ≡ₐ s_ren (a_shift f1) (r_shift f2) .
  intros ? i; dependent elimination i; auto.
Qed.

Definition t_sub_ren_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 ⊆ Γ2),
    t_subst f1 a (t_rename f2 a t)
    = t_subst (s_ren f1 f2) a t .
Definition c_sub_ren_P Γ1 (c : conf Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 ⊆ Γ2),
    c_subst f1 (c_rename f2 c)
    = c_subst (s_ren f1 f2) c .

Lemma sub_ren_prf : ind_args t_sub_ren_P c_sub_ren_P.
  econstructor; unfold t_sub_ren_P, c_sub_ren_P.
  all: intros; cbn; f_equal; auto.
  all: try rewrite a_shift_ren; auto.
Qed.

Lemma t_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 ⊆ Γ2) a (t : term Γ1 a)
  : t_subst f1 a (t_rename f2 a t) = t_subst (s_ren f1 f2) a t.
now apply (t_ind_mut _ _ sub_ren_prf). Qed.
Lemma c_sub_ren {Γ1 Γ2 Γ3} (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 ⊆ Γ2) (c : conf Γ1)
  : c_subst f1 (c_rename f2 c) = c_subst (s_ren f1 f2) c.
now apply (c_ind_mut _ _ sub_ren_prf). Qed.

Lemma t_sub_id_r {Γ Δ} (f : Γ =[term]> Δ) a (i : Γ ∋ a) : t_subst f a (Var i) = f _ i.
destruct a; auto. Qed.

Lemma a_shift_comp {Γ1 Γ2 Γ3 y} (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 =[term]> Γ2)
  : a_shift (y:=y) (a_comp f1 f2) ≡ₐ a_comp (a_shift f1) (a_shift f2) .
  intros x i; dependent elimination i; unfold a_shift, a_comp, t_shift; auto.
  cbn; rewrite t_ren_sub, t_sub_ren.
  apply t_sub_eq; auto; reflexivity.
Qed.
    
Definition t_sub_sub_P Γ1 a (t : term Γ1 a) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 =[term]> Γ2),
    t_subst f1 a (t_subst f2 a t) = t_subst (a_comp f1 f2) a t.
Definition c_sub_sub_P Γ1 (c : conf Γ1) : Prop :=
  forall Γ2 Γ3 (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 =[term]> Γ2),
    c_subst f1 (c_subst f2 c) = c_subst (a_comp f1 f2) c.

Lemma sub_sub_prf : ind_args t_sub_sub_P c_sub_sub_P.
  econstructor; unfold t_sub_sub_P, c_sub_sub_P.
  all: intros; cbn; f_equal; auto.
  all: try rewrite a_shift_comp; auto.
Qed.

Lemma t_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 =[term]> Γ2) a (t : term Γ1 a)
  : t_subst f1 a (t_subst f2 a t) = t_subst (a_comp f1 f2) a t.
now apply (t_ind_mut _ _ sub_sub_prf). Qed.
Lemma c_sub_sub {Γ1 Γ2 Γ3} (f1 : Γ2 =[term]> Γ3) (f2 : Γ1 =[term]> Γ2) (c : conf Γ1)
  : c_subst f1 (c_subst f2 c) = c_subst (a_comp f1 f2) c.
now apply (c_ind_mut _ _ sub_sub_prf). Qed.

Definition t_sub_id_l_P Γ a (t : term Γ a) : Prop := t_subst s_var a t = t.
Definition c_sub_id_l_P Γ (c : conf Γ) : Prop := c_subst s_var c = c.

Lemma sub_id_l_prf : ind_args t_sub_id_l_P c_sub_id_l_P.
  econstructor; unfold t_sub_id_l_P, c_sub_id_l_P.
  all: intros; cbn; f_equal; auto.
  all: try rewrite a_shift_id; auto.
Qed.

Lemma t_sub_id_l {Γ} a (t : term Γ a) : t_subst s_var a t = t.
now apply (t_ind_mut _ _ sub_id_l_prf). Qed.
Lemma c_sub_id_l {Γ} (c : conf Γ) : c_subst s_var c = c.
now apply (c_ind_mut _ _ sub_id_l_prf). Qed.

Lemma sub1_sub {Γ Δ a} (f : Γ =[term]> Δ) (t : term Γ a) :
  a_comp (ass1 (t_subst f a t)) (a_shift f) ≡ₐ a_comp f (ass1 t).
  intros ? i; dependent elimination i; cbn; auto.
  unfold t_shift; rewrite t_sub_ren.
  apply t_sub_id_l.
Qed.

Lemma t_sub1_sub {Γ Δ a b} (f : Γ =[term]> Δ) (v : term Γ a) (t : term (Γ ▶ a) b)
  : t_subst (a_shift f) b t /ₜ₁ t_subst f a v = t_subst f b (t /ₜ₁ v) .
  unfold t_subst1; rewrite 2 t_sub_sub.
  apply t_sub_eq; auto.
  rewrite sub1_sub; reflexivity.
Qed.

Lemma c_sub1_sub {Γ Δ a} (f : Γ =[term]> Δ) (v : term Γ a) (s : conf (Γ ▶ a))
  : c_subst (a_shift f) s /ₛ₁ t_subst f a v = c_subst f (s /ₛ₁ v) .
  unfold c_subst1; rewrite 2 c_sub_sub, sub1_sub; reflexivity.
Qed.
