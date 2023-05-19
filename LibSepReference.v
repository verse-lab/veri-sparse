(** * LibSepReference: Appendix - The Full Construction *)

(** This file provides a pretty-much end-to-end construction of
    a weakest-precondition style characteristic formula generator
    (the function named [wpgen] in [WPgen]), for a core
    programming language with programs assumed to be in A-normal form.

    This file is included by the chapters from the course. *)

Set Implicit Arguments.
From SLF Require Export LibCore.
From SLF Require Export LibSepTLCbuffer LibSepVar LibSepFmap.
From SLF Require LibSepSimpl.

From mathcomp Require Import ssreflect ssrfun.

Module Fmap := LibSepFmap. (* Short name for Fmap module. *)

(* ################################################################# *)
(** * Imports *)

(* ================================================================= *)
(** ** Extensionality Axioms *)

(** These standard extensionality axioms may also be found in
    the [LibAxiom.v] file associated with the TLC library. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

Definition upd {A B : Type} (f : A -> B) x y :=
  fun z => If x = z then y else f z.

Lemma upd_eq A B (f : A -> B) x y : 
  upd f x y x = y.
Proof.
Admitted.

Lemma upd_neq A B (f : A -> B) x y z : 
  z <> x ->
  upd f x y z = f z.
Proof.
Admitted.

Definition uni {A B : Type} (fs : fset A) (f : A -> B) (g : A -> B) :=
  fun z => If indom fs z then f z else g z.

Notation "f '\u_' fs " := (uni fs f) (at level 10, left associativity).

Lemma uni_in A B {f g : A -> B} {x fs} : 
  indom fs x ->
  uni fs f g x = f x.
Proof.
Admitted.

Lemma uni0 A B (f g : A -> B) : 
  uni empty f g = g.
Proof.
Admitted.

Lemma uni_upd A B (f g : A -> B) x fs :
  ~ indom fs x ->
  uni (update fs x tt) f g = upd (uni fs f g) x (f x).
Proof.
Admitted.

Lemma uni_nin A B (f g : A -> B) x fs : 
  ~ indom fs x ->
  uni fs f g x = g x.
Proof.
Admitted.

Lemma uniA A B (f1 f2 g : A -> B) fs1 fs2 : 
  uni fs1 f1 (uni fs2 f2 g) = 
  uni (fs1 \+ fs2) (uni fs1 f1 f2) g.
Proof.
  rewrite /uni; apply/fun_ext_1=> ?.
  do ? case: classicT=> //.
Admitted.

Lemma upd_upd A B (f : A -> B) x y z w : 
  x <> z -> 
  upd (upd f x y) z w = upd (upd f z w) x y.
Proof.
Admitted.

(* Definition fcomp A B C (f : A -> B) (g : C -> A) := fun x => f (g (x)). *)


Lemma upd_uni_update A B (f g : A -> B) (x : A) (y : B) fs : 
  ~ indom fs x ->
  upd f x y \u_ (update fs x tt) g = upd (f \u_fs g) x y.
Proof.
  move=> ND; apply/fun_ext_1=> z.
  case: (prop_inv (indom (update fs x tt) z)).
  { move=> /[dup]/(@uni_in _ _ _ _ _ _)->.
    rewrite indom_update_eq=> -[->/[! upd_eq]//|].
    move=> E. 
    by rewrite ?upd_neq ?uni_in //; move: E=>/[swap]->. }
   move=> /[dup]? E; rewrite indom_update_eq in E.
  rewrite upd_neq ? uni_nin; autos*.
Qed.

Lemma updE A B (f : A -> B) x :
  f = upd f x (f x).
Admitted.
(* Lemma updE A B (f g : A -> B) x y :
  upd f x y = (fun _ => y) \u_() *)

Section LabeledType.

From mathcomp Require Import seq ssrbool ssrnat eqtype.

Section Gen.

Context (T : Type) (def : T).

Definition labType := nat.

Record labeled := Lab {
  lab  :  labType; 
  el   :> T;
}.

Definition labSeq := seq labeled.

Definition lookup (s : labSeq) (l : labType) : labeled := 
  nth (Lab 0%nat def) s (find [pred lt | lab lt == l] s).

Definition remove (s : labSeq) (l : labType) := 
  [seq lt <- s | lab lt != l].

Definition has_lab (s : labSeq) (l : labType) :=
  has (fun x => lab x == l) s.

Lemma hasnt_lab s l : 
  ~ has_lab s l -> 
    s = remove s l.
Proof using.
Admitted.

End Gen.

Context (S : Type) (T : Type) (def : T).

Definition lab_union (fss : labSeq (fset T)) : fset (labeled T).
Proof using. Admitted.
Definition label (lfs : labeled (fset T)) : fset (labeled T). 
Proof using. Admitted.
Definition lab_funs (f : labSeq (S -> T)) : labeled S -> T :=
  fun ls => 
    el (nth (Lab 0%nat (fun=> def)) f (lab ls)) (el ls).

Definition lab_fun (f : labeled (S -> T)) : labeled S -> T :=
  fun ls => el f (el ls).

Definition lab_fun_upd (f g : labeled S -> T) l : labeled S -> T :=
  fun ls => 
    if lab ls == l then f ls else g ls.

Lemma lab_fun_upd_neq f g l (l' : labType) x : 
  l' <> l -> lab_fun_upd f g l (Lab l' x) = g (Lab l' x).
Proof.
  by rewrite/lab_fun_upd; move/(negPP eqP)/negbTE->.
Qed.

Definition app_lab (f : labeled S -> T) : labType -> S -> T := 
  fun l s => f (Lab l s).

End LabeledType.

(* ================================================================= *)
(** ** Variables *)

(** The file [LibSepVar.v], whoses definitions are imported in the header to
    the present file, defines the type [var] as an alias for [string].
    It also provides the boolean function [var_eq x y] to compare two variables,
    and the tactic [case_var] to perform case analysis on expressions of the
    form [if var_eq x y then .. else ..] that appear in the goal. *)

(* ================================================================= *)
(** ** Finite Maps *)

(** The file [LibSepFmap.v], which is bound by the short name [Fmap] in the
    header, provides a formalization of finite maps. These maps are used to
    represent heaps in the semantics. The library provides a tactic called
    [fmap_disjoint] to automate disjointness proofs, and a tactic called
    [fmap_eq] for proving equalities between heaps modulo associativity and
    commutativity. Without these two tactics, pr oofs involving finite maps
    would be much more tedious and fragile. *)

(* ################################################################# *)
(** * Source Language *)

(* ================================================================= *)
(** ** Syntax *)

(** The grammar of primitive operations includes a number of operations. *)


Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_rand : prim
  | val_neg : prim
  | val_opp : prim
  | val_eq : prim
  | val_add : prim
  | val_neq : prim
  | val_sub : prim
  | val_mul : prim
  | val_div : prim
  | val_mod : prim
  | val_le : prim
  | val_lt : prim
  | val_ge : prim
  | val_gt : prim
  | val_ptr_add : prim.

(** Locations are defined as natural numbers. *)

Definition loc : Type := nat.

Definition hloc D : Type := loc * D.

(** The null location corresponds to address zero. *)

Definition null D (d : D) : hloc D := (0%nat, d).

(** The grammar of closed values includes includes basic values such as [int]
    and [bool], but also locations, closures. It also includes two special
    values, [val_uninit] used in the formalization of arrays, and [val_error]
    used for stating semantics featuring error-propagation. *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_uninit : val
  | val_error : val

(** The grammar of terms includes values, variables, functions, applications,
    sequence, let-bindings, and conditions. Sequences are redundant with
    let-bindings, but are useful in practice to avoid binding dummy names,
    and serve on numerous occasion as a warm-up before proving results on
    let-bindings. *)

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

(** A state consists of a finite map from location to values. Records and
    arrays are represented as sets of consecutive cells, preceeded by a
    header field describing the length of the block. *)

Definition state D : Type := fmap (hloc D) val.

(** The type [heap], a.k.a. [state]. By convention, the "state" refers to the
    full memory state when describing the semantics, while the "heap"
    potentially refers to only a fraction of the memory state, when definining
    Separation Logic predicates. *)

Definition hheap D : Type := state D.

Definition proj D (h : hheap D) d := 
  Fmap.filter (fun '(_, c) _ => c = d) h.

(* ================================================================= *)
(** ** Coq Tweaks *)

(** [h1 \u h2] is a notation for union of two heaps. *)

Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity).

(** Implicit types associated with meta-variables. *)



(* Implicit Types f : var. *)
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types w r vf vx : val.
(* Implicit Types t : trm. *)
(* Implicit Types d : D. *)
(* Implicit Types h : heap. *)
(* Implicit Types s : state. *)

(** The types of values and heap values are inhabited. *)

Check @arbitrary.

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Defined.


(** Coercions to improve conciseness in the statment of evaluation rules. *)

Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion val_prim : prim >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(* ================================================================= *)
(** ** Substitution *)

(** The standard capture-avoiding substitution, written [subst x v t]. *)

Fixpoint subst (y:var) (v':val) (t:trm) : trm :=
  let aux t := subst y v' t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val v') t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

(* ================================================================= *)
(** ** Semantics *)

(** Evaluation rules for unary operations are captured by the predicate
    [redupop op v1 v2], which asserts that [op v1] evaluates to [v2]. *)

Inductive evalunop : prim -> val -> val -> Prop :=
  | evalunop_neg : forall b1,
      evalunop val_neg (val_bool b1) (val_bool (neg b1))
  | evalunop_opp : forall n1,
      evalunop val_opp (val_int n1) (val_int (- n1)).

(** Evaluation rules for binary operations are captured by the predicate
    [redupop op v1 v2 v3], which asserts that [op v1 v2] evaluates to [v3]. *)

Inductive evalbinop : val -> val -> val -> val -> Prop :=
  | evalbinop_eq : forall v1 v2,
      evalbinop val_eq v1 v2 (val_bool (isTrue (v1 = v2)))
  | evalbinop_neq : forall v1 v2,
      evalbinop val_neq v1 v2 (val_bool (isTrue (v1 <> v2)))
  | evalbinop_add : forall n1 n2,
      evalbinop val_add (val_int n1) (val_int n2) (val_int (n1 + n2))
  | evalbinop_sub : forall n1 n2,
      evalbinop val_sub (val_int n1) (val_int n2) (val_int (n1 - n2))
  | evalbinop_mul : forall n1 n2,
      evalbinop val_mul (val_int n1) (val_int n2) (val_int (n1 * n2))
  | evalbinop_div : forall n1 n2,
      n2 <> 0 ->
      evalbinop val_div (val_int n1) (val_int n2) (val_int (Z.quot n1 n2))
  | evalbinop_mod : forall n1 n2,
      n2 <> 0 ->
      evalbinop val_mod (val_int n1) (val_int n2) (val_int (Z.rem n1 n2))
  | evalbinop_le : forall n1 n2,
      evalbinop val_le (val_int n1) (val_int n2) (val_bool (isTrue (n1 <= n2)))
  | evalbinop_lt : forall n1 n2,
      evalbinop val_lt (val_int n1) (val_int n2) (val_bool (isTrue (n1 < n2)))
  | evalbinop_ge : forall n1 n2,
      evalbinop val_ge (val_int n1) (val_int n2) (val_bool (isTrue (n1 >= n2)))
  | evalbinop_gt : forall n1 n2,
      evalbinop val_gt (val_int n1) (val_int n2) (val_bool (isTrue (n1 > n2)))
  | evalbinop_ptr_add : forall p1 p2 n,
      (p2:int) = p1 + n ->
      evalbinop val_ptr_add (val_loc p1) (val_int n) (val_loc p2).

(** The predicate [trm_is_val t] asserts that [t] is a value. *)

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(** Big-step evaluation judgement, written [eval s t s' v]. *)

Section eval1.

Context (D : Type) (d : D).

Implicit Types f : var.
Implicit Types v : val.

Inductive eval1 : hheap D -> trm -> hheap D -> val -> Prop :=
  | eval1_val : forall s v,
      eval1 s (trm_val v) s v
  | eval1_fun : forall s x t1,
      eval1 s (trm_fun x t1) s (val_fun x t1)
  | eval1_fix : forall s f x t1,
      eval1 s (trm_fix f x t1) s (val_fix f x t1)
  | eval1_app_args : forall s1 s2 s3 s4 t1 t2 v1 v2 r,
      (~ trm_is_val t1 \/ ~ trm_is_val t2) ->
      eval1 s1 t1 s2 v1 ->
      eval1 s2 t2 s3 v2 ->
      eval1 s3 (trm_app v1 v2) s4 r ->
      eval1 s1 (trm_app t1 t2) s4 r
  | eval1_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval1 s1 (subst x v2 t1) s2 v ->
      eval1 s1 (trm_app v1 v2) s2 v
  | eval1_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval1 s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval1 s1 (trm_app v1 v2) s2 v
  | eval1_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval1 s1 t1 s2 v1 ->
      eval1 s2 t2 s3 v ->
      eval1 s1 (trm_seq t1 t2) s3 v
  | eval1_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval1 s1 t1 s2 v1 ->
      eval1 s2 (subst x v1 t2) s3 r ->
      eval1 s1 (trm_let x t1 t2) s3 r
  | eval1_if : forall s1 s2 b v t1 t2,
      eval1 s1 (if b then t1 else t2) s2 v ->
      eval1 s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval1_unop : forall op m v1 v,
      evalunop op v1 v ->
      eval1 m (op v1) m v
  | eval1_binop : forall op m v1 v2 v,
      evalbinop op v1 v2 v ->
      eval1 m (op v1 v2) m v
  | eval1_ref : forall s v p,
     (forall p',  ~ Fmap.indom s (p', d) -> (p <= p')%Z) ->
      ~ Fmap.indom s (p, d) ->
      eval1 s (val_ref v) (Fmap.update s (p, d) v) (val_loc p)
  | eval1_get : forall s p v,
      Fmap.indom s (p, d) ->
      v = Fmap.read s (p, d) ->
      eval1 s (val_get (val_loc p)) s v
  | eval1_set : forall s p v,
      Fmap.indom s (p, d) ->
      eval1 s (val_set (val_loc p) v) (Fmap.update s (p, d) v) val_unit
  | eval1_free : forall s p,
      Fmap.indom s (p, d) ->
      eval1 s (val_free (val_loc p)) (Fmap.remove s (p, d)) val_unit.

(** Specialized eval1uation rules for addition and division, for avoiding the
    indirection via [eval1_binop] in the course. *)

Lemma eval1_add : forall s n1 n2,
  eval1 s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2)).
Proof using. intros. applys eval1_binop. applys evalbinop_add. Qed.

Lemma eval1_div : forall s n1 n2,
  n2 <> 0 ->
  eval1 s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2)).
Proof using. intros. applys eval1_binop. applys* evalbinop_div. Qed.

(** [eval1_like t1 t2] asserts that [t2] eval1uates like [t1]. In particular,
    this relation hold whenever [t2] reduces in small-step to [t1]. *)

Definition eval1_like (t1 t2:trm) : Prop :=
  forall s s' v, eval1 s t1 s' v -> eval1 s t2 s' v.

End eval1.

(* Section eval. *)

(* Inductive eval (D : Type) : fset D -> hheap D -> (D -> trm) -> hheap D -> (D -> val) -> Prop :=
  | eval_empty h ht hv : eval empty h ht h hv
  | eval_step  h1 h2 h3 ht d v hv fs : 
    ~ Fmap.indom fs d        ->
      eval1 d h1 (ht d) h2 v ->
      eval fs h2 ht h3 hv    ->
        eval (Fmap.update fs d tt) h1 ht h3 (upd hv d v). *)

Definition eval D (fs : fset D) (h : hheap D) (ht : D -> trm) (h' : hheap D) (hv : D -> val) : Prop :=
  (forall d, indom fs d -> eval1 d (proj h d) (ht d) (proj h' d) (hv d)) /\
  forall d, ~indom fs d -> proj h d = proj h' d.

Definition eval_like D (fs : fset D) ht1 ht2 : Prop :=
  forall s s' hv, eval fs s ht1 s' hv -> eval fs s ht2 s' hv.

Definition local D (fs : fset D) (h : hheap D) :=
  forall x d, indom h (x, d) -> indom fs d.

Lemma remove_union_not_r  [A B : Type] [h1 h2 : fmap A B] [x : A] :
  ~ indom h2 x -> 
  Fmap.remove h1 x \u h2 = Fmap.remove (h1 \u h2) x.
Proof.
Admitted.

Lemma eval1_frame D (d : D) t h1 h2 h fs v : 
  local fs h -> 
  ~ indom fs d ->
  eval1 d h1 t h2 v -> 
    eval1 d (h1 \+ h) t (h2 \+ h) v.
Proof.
  move=> l ?.
  have ? : forall x, ~ indom h (x, d) by move=> x /l.
  have ? : forall x s, ~ indom s (x, d) -> ~ indom (s \u h) (x, d).
  { move=> *. rewrite* indom_union_eq. }
  have ? : forall x s v, indom s (x, d) -> v = read s (x, d) -> v = read (s \u h) (x, d).
  { move=> *. rewrite* read_union_l. }
  have ? : forall x s, indom s (x, d) -> indom (s \u h) (x, d).
  { move=> *. rewrite* indom_union_eq. }
  elim=> *; rewrite -?update_union_not_r //; try by (econstructor; eauto).
  rewrite remove_union_not_r //; by (econstructor; eauto).
Qed.

(* Lemma eval_hv_dom D (fs : fset D) ht h h' (hv : fmap D val) :
  eval fs h ht h' hv ->
  Fmap.indom hv = Fmap.indom fs.
Proof.
  intros ev; induction ev.
  { apply fun_ext_1; introv.
    unfold indom, map_indom; simpls.
    applys* prop_ext. }
  applys fun_ext_1; introv.
  rewrite ?indom_update_eq IHev; eauto.
Qed. *)



Lemma fset_rect A : forall P : Type,
  P -> 
  (A -> P -> P) -> fset A -> P.
Proof.
Admitted.

Lemma fset_rectE A (P : Type) (p : P) (f : A -> P -> P) :
  (fset_rect p f empty = p) *
  ((forall (a b : A) (p : P), f a (f b p) = f b (f a p)) ->
    forall fs x, ~ Fmap.indom fs x -> fset_rect p f (update fs x tt) = f x (fset_rect p f fs)).
Admitted.

Lemma fset_ind A : forall P : fset A -> Prop,
  P empty -> 
  (forall fs x, P fs -> ~ Fmap.indom fs x -> P (update fs x tt)) -> forall fs, P fs.
Proof.
Admitted.

(* Lemma evalE D fs (h h' : hheap D) ht hv : 
  (* indom hv = indom fs -> *)
  eval fs h ht h' hv =
  .
Proof.
Admitted. *)

Lemma eval_seq D fs : forall s1 s2 s3 (ht1 ht2 : D -> trm) hv1 hv,
  eval fs s1 ht1 s2 hv1 ->
  eval fs s2 ht2 s3 hv ->
  eval fs s1 (fun d => trm_seq (ht1 d) (ht2 d)) s3 hv.
Proof.
  move=> > [] ? E1 [? E2]; splits=> *; last rewrite -E2 ?E1 //.
  by apply/eval1_seq; eauto.
Qed.

Lemma eval_let D fs : forall s1 s2 s3 (ht1 ht2 : D -> trm) (x : D -> var) hv1 hv,
  eval fs s1 ht1 s2 hv1 ->
  eval fs s2 (fun d => subst (x d) (hv1 d) (ht2 d)) s3 hv ->
  eval fs s1 (fun d => trm_let (x d) (ht1 d) (ht2 d)) s3 hv.
Proof.
  move=> > []? E1[? E2]; splits=> *; last rewrite -E2 ?E1 //.
  by apply/eval1_let; eauto.
Qed.

Lemma eval_if D fs :  forall s1 s2 (b : D -> bool) hv ht1 ht2,
  eval fs s1 (fun d => if b d then ht1 d else ht2 d) s2 hv ->
  eval fs s1 (fun d => trm_if (val_bool (b d)) (ht1 d) (ht2 d)) s2 hv.
Proof.
  move=> > [] *; splits*=>*.
  by apply/eval1_if; eauto.
Qed.

Lemma eval_app_fun D fs : forall s1 s2 hv1 hv2 (x : D -> var) ht1 hv,
  (forall d, indom fs d -> hv1 d = val_fun (x d) (ht1 d)) ->
  eval fs s1 (fun d => subst (x d) (hv2 d) (ht1 d)) s2 hv ->
  eval fs s1 (fun d => trm_app (hv1 d) (hv2 d)) s2 hv.
Proof.
  move=> > ? -[]*; splits*=>*.
  by apply/eval1_app_fun; eauto.
Qed.

Lemma eval_app_fix D fs : forall s1 s2 hv1 hv2 (x f : D -> var) ht1 hv,
  (forall d, indom fs d -> hv1 d = val_fix (f d) (x d) (ht1 d)) ->
  eval fs s1 (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (ht1 d))) s2 hv ->
  eval fs s1 (fun d => trm_app (hv1 d) (hv2 d)) s2 hv.
  move=> >.
  move=> ? -[]*; splits*=>*.
  by apply/eval1_app_fix; eauto.
Qed.

Lemma eval_val D fs : forall s (hv : D -> val),
  eval fs s (fun d => trm_val (hv d)) s hv.
Proof.
  move=> *; splits*=>*.
  exact/eval1_val.
Qed.

Lemma eval_fun D fs : forall (x : D -> var) ht1 hv s,
  (forall d, indom fs d -> hv d = val_fun (x d) (ht1 d)) ->
  eval fs s (fun d => trm_fun (x d) (ht1 d)) s hv.
Proof.
  move=> > E1 *.
  splits*=>*; rewrite ?E1 //.
  exact/eval1_fun.
Qed.

Lemma eval_fix D fs : forall (f x : D -> var) ht1 hv s,
  (forall d, indom fs d -> hv d = val_fix (f d) (x d) (ht1 d)) ->
  eval fs s (fun d => trm_fix (f d) (x d) (ht1 d)) s hv.
Proof.
  move=> > E1 *; splits*=>*; rewrite ?E1 //.
  exact/eval1_fix.
Qed.

Lemma eval_hv D (fs : fset D) ht hv hv' s1 s2 :
  eval fs s1 ht s2 hv' ->
  (forall d, indom fs d -> hv d = hv' d) ->
  eval fs s1 ht s2 hv.
Proof. case=> ?? E; splits*=> * /[! E] //; eauto. Qed.

(* ################################################################# *)
(** * Heap Predicates *)

(** We next define heap predicates and establish their properties.
    All this material is wrapped in a module, allowing us to instantiate
    the functor from [LibSepSimpl] that defines the tactic [xsimpl]. *)

Module Type Domain.

Parameter type : Type.

End Domain.

Module SepSimplArgs (Dom : Domain).

(* ================================================================= *)
(** ** Hprop and Entailment *)

Declare Scope hprop_scope.
Open Scope hprop_scope.

Definition D := Dom.type.

(** The type of heap predicates is named [hhprop]. *)

Definition hhprop := hheap D -> Prop.

(* Definition hhprop := hheap D -> hhprop. *)

(** Implicit types for meta-variables. *)

Implicit Types P : Prop.
Implicit Types H : hhprop.
Implicit Types d : D.
Implicit Types Q : val->hhprop.

(** Entailment for heap predicates, written [H1 ==> H2]. This entailment
    is linear. *)

Definition himpl (H1 H2:hhprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55, 
  format "'[' H1 ']' '/  '  ==>  '/  ' '[' H2 ']'") : hprop_scope.

(** Entailment between postconditions, written [Q1 ===> Q2]. *)

Definition qimpl A (Q1 Q2:A->hhprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(* ================================================================= *)
(** ** Definition of Heap Predicates *)

(** The core heap predicates are defined next, together with the
    associated notation:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [\Top] denotes the true heap predicate (affine)
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential quantifier
    - [\forall x, H] denotes a universal quantifier
    - [H1 \-* H2] denotes a magic wand between heap predicates
    - [Q1 \--* Q2] denotes a magic wand between postconditions. *)

Definition hempty : hhprop :=
  fun h => (h = Fmap.empty).

Definition hsingle (p:loc) (d : D) (v:val) : hhprop :=
  fun h => (h = Fmap.single (p, d) v).

Definition hstar (H1 H2 : hhprop) : hhprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hexists A (J:A->hhprop) : hhprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hhprop) : hhprop :=
  fun h => forall x, J x h.

Definition hlocal (H : hhprop) (fs : fset D) :=
  H ==> local fs.

Definition fsubst {A B C : Type} (fm : fmap A B) (f : A -> C) : fmap C B. Admitted.
(* Lemma fsubst_read {A B C : Type} `{Inhab B} (fm : fmap A B) (f : C -> A) x :
  read (fsubst fm f) x = read fm (f x).
Admitted.

Lemma fsubst_empty {A B C : Type} `{Inhab B} (f : C -> A) :
  fsubst (empty : fmap A B) f = empty.
Admitted. *)

Lemma fsubst_single {A B C : Type} `{Inhab B} (f : A -> C) (x : A) (y : B) :
  bijective f ->
  fsubst (single x y) f = single (f x) y.
Admitted.


Definition hsubst (H : hhprop) (f : D -> D) :=
  fun h => H (fsubst h (fun '(x, d) => (x, f d))).

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Declare Scope arr_scope.
Delimit Scope arr_scope with arr.

Notation "p '~⟨' l ',' x '⟩~>' v" := (hsingle p (Lab l%nat x) v) (at level 32, format "p  ~⟨ l ,  x ⟩~>  v") : hprop_scope.
Notation "p '~(' d ')~>' v" := (hsingle p d%arr v) (at level 32, format "p  ~( d )~>  v") : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\{' x |-> f '}' H" := (hsubst H (fun x => f)) 
  (at level 39, x binder, H at level 50, right associativity,
  format "'[' \{ x  |->  f } ']' '/   '  H").

(** The remaining operators are defined in terms of the preivous above,
    rather than directly as functions over heaps. Doing so reduces the
    amount of proofs, by allowing to better leverage the tactic [xsimpl]. *)

Definition hpure (P:Prop) : hhprop :=
  \exists (p:P), \[].

Definition htop : hhprop :=
  \exists (H:hhprop), H.

Definition hwand (H1 H2 : hhprop) : hhprop :=
  \exists H0, H0 \* hpure ((H1 \* H0) ==> H2).

Definition qwand A (Q1 Q2:A->hhprop) : hhprop :=
  \forall x, hwand (Q1 x) (Q2 x).

Definition hstar_fset (fs : fset D) (f : D -> hhprop) : hhprop :=
  fset_rect \[] (fun d H => f d \* H) fs.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "\Top" := (htop) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.

Reserved Notation "'\*_' ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \*_ ( i  <-  r ) '/  '  F ']'").

Notation "'\*_' ( i <- r ) F" :=
  (hstar_fset r (fun i => F)) : nat_scope.

(* ================================================================= *)
(** ** Basic Properties of Separation Logic Operators *)

(* ----------------------------------------------------------------- *)
(** *** Tactic for Automation *)

(** We set up [auto] to process goals of the form [h1 = h2] by calling
    [fmap_eq], which proves equality modulo associativity and commutativity. *)

Hint Extern 1 (_ = _ :> hheap _) => fmap_eq.

(** We also set up [auto] to process goals of the form [Fmap.disjoint h1 h2]
    by calling the tactic [fmap_disjoint], which essentially normalizes all
    disjointness goals and hypotheses, split all conjunctions, and invokes
    proof search with a base of hints specified in [LibSepFmap.v]. *)

Import Fmap.DisjointHints.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.

(* ----------------------------------------------------------------- *)
(** *** Properties of [himpl] and [qimpl] *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

Hint Resolve himpl_refl.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_trans_r : forall H2 H1 H3,
   H2 ==> H3 ->
   H1 ==> H2 ->
   H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans M2 M1. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hprop_op_comm : forall (op:hhprop->hhprop->hhprop),
  (forall H1 H2, op H1 H2 ==> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys himpl_antisym; applys M. Qed.

Lemma qimpl_refl : forall A (Q:A->hhprop),
  Q ===> Q.
Proof using. intros. unfolds*. Qed.

Hint Resolve qimpl_refl.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hempty] *)

Lemma hempty_intro :
  \[] Fmap.empty.
Proof using. unfolds*. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = Fmap.empty.
Proof using. auto. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (Fmap.union h1 h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = Fmap.union h1 h2.
Proof using. introv M. applys M. Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  applys hprop_op_comm. unfold hhprop, hstar. intros H1 H2.
  intros h (h1 & h2 & M1 & M2 & D' & U). rewrite~ Fmap.union_comm_of_disjoint in U.
  exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D''&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { applys* hstar_intro. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D''&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { applys* hstar_intro. } }
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D''&U). forwards E: hempty_inv M1. subst.
    rewrite~ Fmap.union_empty_l. }
  { intros M. exists (Fmap.empty:hheap D) h. splits~. { applys hempty_intro. } }
Qed.

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm. applys~ hstar_hempty_l.
Qed.

Lemma hstar_hexists : forall A (J:A->hhprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D''&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D''&U)). exists h1 h2. splits~. { exists~ x. } }
Qed.

Lemma hstar_hforall : forall H A (J:A->hhprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D'&U). intros x. exists~ h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1.
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1.
Qed.

(* ----------------------------------------------------------------- *)
(** ***  Properties of [hpure] *)

Lemma hpure_intro : forall P,
  P ->
  \[P] Fmap.empty.
Proof using. introv M. exists M. unfolds*. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = Fmap.empty.
Proof using. introv (p&M). split~. Qed.

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_r : forall P H h,
  (H \* \[P]) h = (H h /\ P).
Proof using.
  intros. rewrite hstar_comm. rewrite hstar_hpure_l. apply* prop_ext.
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure_l. rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof using.
  introv M N. rewrite <- (hstar_hempty_l \[P]). rewrite~ hstar_hpure_r.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof using. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_hpure_l in Hh. applys* W.
Qed.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  applys himpl_antisym; intros h M.
  { applys* hpure_intro_hempty. }
  { forwards* : hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using.
  intros. applys himpl_antisym; intros h; rewrite hstar_hpure_l; intros M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hexists] *)

Lemma hexists_intro : forall A (x:A) (J:A->hhprop) h,
  J x h ->
  (hexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hhprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma himpl_hexists_l : forall A H (J:A->hhprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hhprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hforall] *)

Lemma hforall_intro : forall A (J:A->hhprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hhprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

Lemma himpl_hforall_r : forall A (J:A->hhprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hhprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hhprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hhprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hwand] *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    rewrite (hstar_comm H H1). applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0.
    rewrite <- (hstar_hempty_r H0) at 1.
    applys himpl_frame_r. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H2 \* H1 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H2 \* H1 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. applys himpl_hwand_r_inv. applys himpl_refl. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. apply himpl_hwand_r. rewrite~ hstar_hempty_r. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- hstar_hempty_l at 1. applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_l. }
Qed.

Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using.
  introv HP. applys himpl_antisym.
  { lets K: hwand_cancel \[P] H. applys himpl_trans K.
    applys* himpl_hstar_hpure_r. }
  { rewrite hwand_equiv. applys* himpl_hstar_hpure_l. }
Qed.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. apply himpl_hwand_r. apply himpl_hwand_r.
  rewrite <- hstar_assoc. rewrite (hstar_comm H1 H2).
  applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite (hstar_comm H1 H2).
  rewrite hstar_assoc. applys himpl_hstar_trans_r.
  { applys hwand_cancel. } { applys hwand_cancel. }
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.

Lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 \-* H2) h2 ->
  H1 h1 ->
  Fmap.disjoint h1 h2 ->
  H2 (h1 \u h2).
Proof using.
  introv M2 M1 D'. unfolds hwand. lets (H0&M3): hexists_inv M2.
  lets (h0&h3&P1&P3&D''&U): hstar_inv M3. lets (P4&E3): hpure_inv P3.
  subst h2 h3. rewrite union_empty_r in D' M3 M2 *. applys P4. applys* hstar_intro.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of qwand *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hhprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    applys himpl_trans. applys hstar_hforall. simpl.
    applys himpl_hforall_l x. rewrite hstar_comm. applys hwand_cancel. }
  { applys himpl_hforall_r. intros x. rewrite* hwand_equiv. }
Qed.

Lemma qwand_cancel : forall A (Q1 Q2:A->hhprop),
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hhprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hhprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Arguments qwand_specialize [ A ].

(* ----------------------------------------------------------------- *)
(** *** Properties of [htop] *)

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { rewrite <- hstar_hempty_r at 1. applys himpl_frame_r. applys himpl_htop_r. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hsingle] *)

Lemma hsingle_intro : forall p d v,
  (p ~(d)~> v) (Fmap.single (p, d) v).
Proof using. intros. hnfs*. Qed.

Lemma hsingle_inv: forall p d v h,
  (p ~(d)~> v) h ->
  h = Fmap.single (p,d) v.
Proof using. auto. Qed.

Lemma hstar_hsingle_same_loc : forall p d w1 w2,
  (p ~(d)~> w1) \* (p ~(d)~> w2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D'&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.

(* ----------------------------------------------------------------- *)
(** *** Definition and Properties of [haffine] and [hgc] *)

Definition haffine (H:hhprop) :=
  True.

Lemma haffine_hany : forall (H:hhprop),
  haffine H.
Proof using. unfold haffine. auto. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using. applys haffine_hany. Qed.

Definition hgc := (* equivalent to [\exists H, \[haffine H] \* H] *)
  htop.

Notation "\GC" := (hgc) : hprop_scope.

Lemma haffine_hgc :
  haffine \GC.
Proof using. applys haffine_hany. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. applys himpl_htop_r. Qed.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. applys hstar_htop_htop. Qed.

Lemma hsubst_hempty f : 
  \{ x |-> f x } \[] = \[].
Proof.
  apply fun_ext_1=> ?; rewrite /hempty /hsubst.
Admitted.

Lemma hsubst_hpure f P : 
  \{ x |-> f x } \[P] = \[P].
Proof.
Admitted.

Lemma hsubst_hstar H1 H2 f :
  \{x |-> f x} H1 \* H2 = (\{x |-> f x} H1) \* (\{x |-> f x} H2).
Proof.
Admitted.

Lemma hsubst_htop f :
  \{x |-> f x} \Top = \Top.
Proof.
Admitted.


Lemma hsubst_hsingle f d x p: 
  \{ x |-> f x } p ~(d)~> x = p ~(f d)~> x.
Admitted.

Hint Rewrite hsubst_hempty hsubst_hsingle : hsubst.

(* ----------------------------------------------------------------- *)
(** *** Functor Instantiation to Obtain [xsimpl] *)

End SepSimplArgs.

(** We are now ready to instantiate the functor that defines [xsimpl].
    Demos of [xsimpl] are presented in chapter [Himpl.v]. *)

Module Reasoning (Dom : Domain).

Module SepSimplArgs := SepSimplArgs(Dom).

Module Export HS := LibSepSimpl.XsimplSetup(SepSimplArgs).

Export SepSimplArgs.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hlocal] *)

Lemma hstar_fset_empty (f : D -> hhprop) :
  hstar_fset empty f = \[].
Proof.
  by rewrite /hstar_fset fset_rectE.
Qed.

Lemma hstar_fset_update fs x (f : D -> hhprop) :
  ~ Fmap.indom fs x ->
  hstar_fset (update fs x tt) f = f x \* hstar_fset fs f.
Proof.
  move=> ?.
  rewrite /hstar_fset fset_rectE //.
  move=> *; by rewrite hstar_comm_assoc.
Qed.


Lemma hstar_fset_union fs1 fs2 (f : D -> hhprop) :
  disjoint fs1 fs2 ->
  hstar_fset (fs1 \u fs2) f = hstar_fset fs1 f \* hstar_fset fs2 f.
Proof.
Admitted.

Lemma hstar_fset_eq fs (f1 f2 : D -> hhprop) :
  (forall d, indom fs d -> f1 d = f2 d) ->
  hstar_fset fs f1 = hstar_fset fs f2.
Proof.
Admitted.

Lemma hstar_fset_emptys fs :
  hstar_fset fs (fun _ => \[]) = \[].
Proof.
  elim/fset_ind: fs=> [|?? E ?].
  { exact/hstar_fset_empty. }
  rewrite hstar_fset_update // E; xsimpl.
Qed.

Lemma hstar_fset_hstar fs P Q: 
  \*_(d <- fs) P d \* Q d = (\*_(d <- fs) P d) \* (\*_(d <- fs) Q d).
Proof.
  elim/fset_ind: fs=> [|?? E ?].
  { rewrite ?hstar_fset_empty; xsimpl. }
  rewrite ?hstar_fset_update // E; xsimpl.
Qed.


Lemma hstar_fset_pure fs P: 
  \*_(d <- fs) \[P d] = \[forall d, indom fs d -> P d].
Proof.
  elim/fset_ind: fs=> [|??].
  { rewrite hstar_fset_empty.
    apply/fun_ext_1=> ?; apply/prop_ext; split.
    { move->.
      have p: (forall d, indom (empty : fset D) d -> P d) by [].
      by exists p. }
  by case. }
  move=> E ?; rewrite hstar_fset_update // E.
  apply/fun_ext_1=> x; apply/prop_ext; split.
  { case=> ? [?] [][?] E1 [][?] E2 [].
    eexists.
    { move=> ?; rewrite indom_update_eq=> -[<-|]; eauto. }
    subst. rewrite E1 E2 /hempty; autos~. }
  case=> p ->; exists (empty : hheap D), (empty : hheap D); splits~.
  all: eexists=> //*; apply/p; rewrite* indom_update_eq.
Qed.

Lemma hstar_fset_pure_hstar fs P H: 
  \*_(d <- fs) \[P d] \* H d = \[forall d, indom fs d -> P d] \* \*_(d <- fs) H d.
Proof. by rewrite hstar_fset_hstar hstar_fset_pure. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hlocal] *)

Lemma local_union h1 h2 (fs : fset D) :
  local fs (h1 \u h2) = 
  (local fs h1 /\ local fs h2).
Proof.
  apply/prop_ext; split=> l.
  { split=> x d ?; apply/(l x); rewrite* indom_union_eq. }
  move=> x d; by rewrite* indom_union_eq.
Qed.

Lemma hlocal_hsingle p x fs d: 
  indom fs d ->
  hlocal (p ~(d)~> x) fs.
Proof. by move=> ?? -> ?? /[! indom_single_eq]-[?<-]. Qed.

Lemma hlocal_hsingle_single p x d: 
  hlocal (p ~(d)~> x) (single d tt).
Proof. exact/hlocal_hsingle/indom_single. Qed.

Lemma hlocal_hstar H1 H2 fs : 
  hlocal H1 fs -> hlocal H2 fs ->
  hlocal (H1 \* H2) fs.
Proof.
  move=> hl1 hl2 ? [?] [?] [/hl1 ?] [/hl2 ?] [_ ->].
  by rewrite* local_union.
Qed.

Lemma hlocal_hempty fs : hlocal \[] fs.
Proof. by move=> ? ->. Qed.

Lemma hlocal_hpure P fs : hlocal \[P] fs.
Proof. by move=> ? [?->]. Qed.

Lemma hlocal_hstar_fset (P : D -> hhprop) fs1 fs2: 
  (forall d, indom fs1 d -> hlocal (P d) fs2) ->
    hlocal (\*_(d <- fs1) P d) fs2.
Proof.
  elim/fset_ind: fs1.
  { rewrite hstar_fset_empty=> *; exact/hlocal_hempty. }
  move=> fs d IHfs ? IN. rewrite hstar_fset_update //.
  apply/hlocal_hstar/IHfs=> *; apply/IN; by rewrite* indom_update_eq.
Qed.

Lemma hlocal_hexists A fs (J : A -> _) :
  (forall x, hlocal (J x) fs) -> hlocal (hexists J) fs.
Proof. by move=> hl ? [? /hl]. Qed.

(** From now on, all operators have opaque definitions. *)

Global Opaque hempty hpure hstar hsingle hexists hforall
              hwand qwand htop hgc haffine.

(** At this point, the tactic [xsimpl] is defined. There remains to customize
    the tactic so that it recognizes the predicate [p ~~> v] in a special way
    when performing simplifications. *)

(** The tactic [xsimpl_hook_hsingle p v] operates as part of [xsimpl].
    The specification that follows makes sense only in the context of the
    presentation of the invariants of [xsimpl] described in [LibSepSimpl.v].
    This tactic is invoked on goals of the form [Xsimpl (Hla, Hlw, Hlt) HR],
    where [Hla] is of the form [H1 \* .. \* Hn \* \[]]. The tactic
    [xsimpl_hook_hsingle p v] searches among the [Hi] for a heap predicate
    of the form [p ~~> v']. If it finds one, it moves this [Hi] to the front,
    just before [H1]. Then, it cancels it out with the [p ~~> v] that occurs
    in [HR]. Otherwise, the tactic fails. *)

Ltac xsimpl_hook_hsingle p :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with (hsingle p ?v') =>
      constr:(true) end);
  apply xsimpl_lr_cancel_eq;
  [ xsimpl_lr_cancel_eq_repr_post tt | ].

(** The tactic [xsimpl_hook] handles cancellation of heap predicates of the
    form [p ~~> v]. It forces their cancellation against heap predicates of
    the form [p ~~> w], by asserting the equality [v = w]. Note: this tactic
    is later refined to also handle records. *)

Ltac xsimpl_hook H ::=
  match H with
  | hsingle ?p ?v => xsimpl_hook_hsingle p
  end.

(** One last hack is to improve the [math] tactic so that it is able
    to handle the [val_int] coercion in goals and hypotheses of the
    form [val_int ?n = val_int ?m], and so that it is able to process
    the well-founded relations [dowto] and [upto] for induction on
    integers. *)

Ltac math_0 ::=
  unfolds downto, upto;
  repeat match goal with
  | |- val_int _ = val_int _ => fequal
  | H: val_int _ = val_int _ |- _ => inverts H
  end.

(* ================================================================= *)
(** ** Properties of [haffine] *)

(** In this file, we set up an affine logic. The lemma [haffine_any] asserts
    that [haffine H] holds for any [H]. Nevertheless, let us state corollaries
    of [haffine_any] for specific heap predicates, to illustrate how the
    [xaffine] tactic works in chapter [Affine]. *)

Lemma haffine_hempty :
  haffine \[].
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hexists : forall A (J:A->hhprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hhprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hstar_hpure : forall (P:Prop) H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hgc :
  haffine \GC.
Proof using. intros. applys haffine_hany. Qed.

(** Using these lemmas, we are able to configure the [xaffine] tactic. *)

Ltac xaffine_core tt ::=
  repeat match goal with |- haffine ?H =>
    match H with
    | (hempty) => apply haffine_hempty
    | (hpure _) => apply haffine_hpure
    | (hstar _ _) => apply haffine_hstar
    | (hexists _) => apply haffine_hexists
    | (hforall _) => apply haffine_hforall
    | (hgc) => apply haffine_hgc
    | _ => eauto with haffine
    end
  end.

(* ################################################################# *)
(** * Reasoning Rules *)

Implicit Types P : Prop.
Implicit Types d : D.
Implicit Types H : hhprop.
(* Implicit Types Q : val->hhprop. *)

(* ================================================================= *)
(** ** Evaluation Rules for Primitives in Separation Style *)

(** These lemmas reformulated the big-step evaluation rule in a
    Separation-Logic friendly presentation, that is, by using disjoint
    unions as much as possible. *)

Hint Resolve indom_single : core.

Lemma eval_ref_sep : forall s1 s2 v p d,
  s2 = Fmap.single (p, d) v ->
  (forall p', ~ Fmap.indom s1 (p', d) -> (p <= p')%Z) ->
  Fmap.disjoint s2 s1 ->
  eval1 d s1 (val_ref v) (Fmap.union s2 s1) (val_loc p).
Proof using.
  introv -> ? D. forwards Dv: Fmap.indom_single p v.
  rewrite <- Fmap.update_eq_union_single. applys~ eval1_ref.
  intros N. applys~ Fmap.disjoint_inv_not_indom_both D N.
Qed.

Lemma eval_get_sep : forall s s2 p d v,
  s = Fmap.union (Fmap.single (p, d) v) s2 ->
  eval1 d s (val_get (val_loc p)) s v.
Proof using.
  introv ->. forwards Dv: Fmap.indom_single p v.
  applys eval1_get.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_set_sep : forall s1 s2 h2 p d w v,
  s1 = Fmap.union (Fmap.single (p, d) w) h2 ->
  s2 = Fmap.union (Fmap.single (p, d) v) h2 ->
  Fmap.disjoint (Fmap.single (p, d) w) h2 ->
  eval1 d s1 (val_set (val_loc p) v) s2 val_unit.
Proof using.
  introv -> -> D. forwards Dv: Fmap.indom_single p w.
  applys_eq eval1_set.
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

Lemma eval_free_sep : forall s1 s2 v p d,
  s1 = Fmap.union (Fmap.single (p, d) v) s2 ->
  Fmap.disjoint (Fmap.single (p, d) v) s2 ->
  eval1 d s1 (val_free p) s2 val_unit.
Proof using.
  introv -> D. forwards Dv: Fmap.indom_single p v.
  applys_eq eval1_free.
  { rewrite~ Fmap.remove_union_single_l.
    intros Dl. applys Fmap.disjoint_inv_not_indom_both D Dl.
    applys Fmap.indom_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

Lemma local_partition h d :
  exists h1 h2,
    local (single d tt) h1 /\
    disjoint h1 h2         /\ 
    h = h1 \u h2.
Admitted.

Lemma eval1_local (d : D) hd h h' t v :
  local (single d tt) hd ->
  disjoint hd h ->
  eval1 d (hd \u h) t h' v -> 
  exists hd', 
    local (single d tt) hd' /\
    h' = hd' \u h.
Admitted.

Lemma eval1_proj_nd d h h' t v : 
  eval1 d h t h' v -> 
  forall c, d <> c -> proj h c = proj h' c.
Proof.
Admitted.


(* ================================================================= *)
(** ** Hoare Reasoning Rules *)

(* ################################################################# *)
(** * Definition of total correctness Hoare Triples. *)

Definition hhoare (fs : fset D) (ht : D -> trm) (H : hhprop) (Q: (D -> val) -> hhprop) :=
  forall h, H h -> 
    exists h' hv, 
        eval fs h ht h' hv /\ Q hv h'.

Lemma hhoare_hsubst (fs : fset D) ht H Q f g : 
  cancel f g -> cancel g f ->
  hhoare fs ht H Q =
  hhoare (fsubst fs f) (ht \o g) (\{x |-> f x} H) (fun hv => \{x |-> f x} (Q (hv \o f))).
Proof.
Admitted.

Lemma eval_eq (fs : fset D) (ht1 ht2 : D -> trm) h h' hv : 
  (forall d, Fmap.indom fs d -> ht1 d = ht2 d) ->
  eval fs h ht1 h' hv -> eval fs h ht2 h' hv.
Proof.
  rewrite ?evalE=> E [??]; split=> // *; rewrite -E //; eauto.
Qed.

Lemma hhoare_eq (fs : fset D) (ht1 ht2 : D -> trm) H (Q: (D -> val) -> hhprop) : 
  (forall d, Fmap.indom fs d -> ht1 d = ht2 d) ->
  hhoare fs ht1 H Q -> hhoare fs ht2 H Q.
Proof.
  intros eq hh ? [h' [hv [ev ?]]]%hh.
  exists h', hv; splits~; applys~ eval_eq.
Qed.

Lemma hheap_eq_proj h1 h2 :
  (forall d, proj h1 d = proj h2 d) -> h1 = h2.
Admitted.

Lemma hhoare0 ht H Q : 
  hhoare empty ht H (fun=> Q) = (H ==> Q).
Proof.
  apply/prop_ext; split.
  { move=> hh ? /hh[?][?][][_] ev.
    apply: applys_eq_init; fequals.
    apply/hheap_eq_proj=> ?; exact/ev. }
  move=> hq h /hq ?; exists h, (fun (_ : D) => val_unit); by do ? split.
Qed.


Lemma eval_cup (fs1 fs2 : fset D) ht h1 h2 h3 hv1 hv2 : 
  disjoint fs1 fs2 ->
  eval fs1 h1 ht h2 hv1 ->
  eval fs2 h2 ht h3 hv2 ->
    eval (fs1 \u fs2) h1 ht h3 (hv1 \u_(fs1) hv2).
Proof.
  move=> disj; case=> ? E1[? E2]; splits*=> d.
  2: { rewrite indom_union_eq=> ?; rewrite* E1. }
  rewrite indom_union_eq=> -[] /[dup]/(disjoint_inv_not_indom_both disj) ??.
  { by rewrite -E2 // uni_in; auto. }
  by rewrite E1 // uni_nin; auto.
Qed.

(* Lemma eval_cup2 (fs1 fs2 : fset D) ht h1 h3 hv : 
  disjoint fs1 fs2 ->
  eval (fs1 \u fs2) h1 ht h3 hv -> 
  exists h2, 
    eval fs1 h1 ht h2 hv /\ eval fs2 h2 ht h3 hv.
Proof.
Admitted. *)

Lemma hhoare_union (fs1 fs2 : fset D) ht H (Q Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  hhoare fs1 ht H Q ->
  (forall hv, 
    hhoare fs2 ht (Q hv) (fun hv' => Q' (hv \u_fs1 hv'))) -> 
    hhoare (fs1 \u fs2) ht H Q'.
Proof.
  intros disj hh1 hh2 ? [h1[ hv1 [? Qh1]]]%hh1.
  destruct (hh2 hv1 _ Qh1) as [h2 [hv2 [ev ?]]].
  exists h2, (hv1 \u_(fs1) hv2); split~.
  applys eval_cup; eauto.
Qed.

Lemma filter_eq {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) `{Inhab B} : 
  (forall y x, P y x -> read fs1 y = read fs2 y) -> 
  filter P fs1 = filter P fs2.
Proof.
Admitted.

Lemma filter_in {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) `{Inhab B} x y : 
  P y x ->
  read (filter P fs) y = read fs y.
Proof.
Admitted.

Lemma filter_indom {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) y `{Inhab B} : 
  indom (filter P fs) y <-> (indom fs y /\ exists x, P y x).
Proof.
Admitted.

Lemma read_arb {A B : Type} (fs : fmap A B) x  `{Inhab B}: 
  ~ indom fs x -> read fs x = arbitrary.
Proof.
Admitted.

Lemma disj_filter {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) : 
  disjoint fs1 fs2 -> disjoint fs1 (filter P fs2).
Admitted.

Lemma filter_union {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) :
  disjoint fs1 fs2 ->
  filter P (fs1 \u fs2) = filter P fs1 \u filter P fs2.
Proof.
Admitted.

Lemma filter_union' {A B : Type} (fs1 fs2 : fmap A B) (P : A -> B -> Prop) :
  (forall x y y', P x y <-> P x y') -> 
  filter P (fs1 \u fs2) = filter P fs1 \u filter P fs2.
Proof.
  case: fs1 fs2=> f1 ? [f2 ?] E.
  apply/fmap_extens=> /= x.
  rewrite /map_filter /map_union /map_disjoint.
  case: (f1 x)=> // ?.
  case: classicT=> //; case: (f2 _)=> // ?. 
  by case: classicT=> // /E ? [].
Qed.

Definition insert D (fs : fset D) (fm1 fm2 : hheap D) : hheap D :=
  filter (fun '(_, d) _ => indom fs d) fm1 \u filter (fun '(_, d) _ => ~indom fs d) fm2.

Lemma insert_proj_in D (fs : fset D) (fm1 fm2 : hheap D) (d : D) :
  indom fs d -> proj (insert fs fm1 fm2) d = proj fm1 d.
Admitted.

Lemma insert_proj_nin D (fs : fset D) (fm1 fm2 : hheap D) (d : D) : 
  ~indom fs d -> proj (insert fs fm1 fm2) d = proj fm2 d.
Admitted.


Definition diff {A B} (fs1 fs2 : fmap A B) : fmap A B. Admitted.

Notation "fs1 '\-' fs2" := (diff fs1 fs2) (at level 20, right associativity).

Lemma diff0 {A B} (fs : fmap A B) : fs \- empty = fs.  Admitted.
Lemma diffxx {A B} (fs : fmap A B) : fs \- fs = empty.  Admitted.

Lemma diff_indom {A B} (fs1 fs2 : fmap A B) x:
  indom (fs1 \- fs2) x = (indom fs1 x /\ ~ indom fs2 x).
Admitted.

Lemma diff_upd d fs1 fs2 : 
  indom fs1 d ->
  fs1 \- fs2 = update (fs1 \- update fs2 d tt) d tt.
Admitted.

Lemma diff_disj {A B} (fm1 fm2 : fmap A B) : 
  disjoint (fm1 \- fm2) fm2.
Proof.
Admitted.

Lemma union_diff {A B} (fm1 fm2 : fmap A B) `{Inhab B} : 
  disjoint fm1 fm2 ->
  (fm1 \u fm2) \- fm2 = fm1.
Proof.
Admitted.


Arguments diff_upd : clear implicits.


Lemma filter_union_compl {A B : Type} (fs : fmap A B) (P : A -> B -> Prop) : 
  filter P fs \u filter (fun x y => ~ (P x y)) fs = fs.
Admitted.

Lemma insert_distr_union (fs : fset D) h1 h2 h:
  disjoint (filter (fun '(_, d) => fun=> ~ indom fs d) h1) h ->
  disjoint (filter (fun '(_, d) => fun=> indom fs d) h2) h ->
  insert fs h2 h1 \u h = insert fs (h2 \u h) (h1 \u h).
Proof.
  move=> ??; rewrite /insert ?filter_union' //; try by case.
  rewrite union_assoc -[_ \u _ \u filter (fun '(_, d) => fun=> ~ indom fs d) h]union_assoc.
  rewrite [filter _ h  \u _ ]union_comm_of_disjoint.
  { rewrite ?union_assoc -{1}(filter_union_compl h (fun '(_, d) => fun=> indom fs d)).
    do ? fequals. apply/fun_ext_2=> -[] //. }
  apply/disjoint_of_not_indom_both=> -[??] /filter_indom[_][??].
  by case/filter_indom=> _ [].
Qed.

(* Lemma inserthh (fs : fset D) h : 
  insert fs h h = h.
Admitted.

Lemma insert_union_disj (fs : fset D) h1 h2: 
  disjoint h2 h1 ->
  insert fs h1 h2 \u h1 = (filter (fun '(_, d) _ => ~indom fs d) h2) \u h1.
Admitted. *)

Lemma eval_union_insert (fs1 fs2 : fset D) h1 h2 hv ht :
  disjoint fs1 fs2 ->
  eval (fs1 \u fs2) h1 ht h2 hv -> 
    eval fs1 h1 ht (insert fs1 h2 h1) hv /\ 
    eval fs2 (insert fs1 h2 h1) ht h2 hv.
Proof.
  move=> dj [IN OUT]; do ? split.
  { move=> d ?. 
    have->//: proj (insert fs1 h2 h1) d = proj h2 d.
    { by apply/insert_proj_in. }
    apply IN; rewrite* indom_union_eq. }
  { by move=> d ? /[! insert_proj_nin]. }
  { move=> d I.
    have->//: proj (insert fs1 h2 h1) d = proj h1 d.
    { apply/insert_proj_nin/disjoint_inv_not_indom_both/I.
      autos*. }
    apply IN; rewrite* indom_union_eq. }
  move=> d ?.
  case: (prop_inv (indom fs1 d))=> ?.
  { exact/insert_proj_in. }
  rewrite insert_proj_nin //. 
  apply/OUT; rewrite* indom_union_eq.
Qed.

Lemma eval_cup2 (fs1 fs2 : fset D) h1 h2 hv ht: 
  disjoint fs1 fs2 -> 
  exists h', 
    forall h,
      disjoint (filter (fun '(_, d) => fun=> ~ indom fs1 d) h1) h -> 
      disjoint (filter (fun '(_, d) => fun=> indom fs1 d) h2) h -> 
      eval (fs1 \u fs2) (h1 \u h) ht (h2 \u h) hv -> 
        disjoint h h'                      /\ 
        eval fs1 (h1 \u h) ht (h' \u h) hv /\
        eval fs2 (h' \u h) ht (h2 \u h) hv /\
        h' = insert fs1 h2 h1.
Proof.
  move=> dj.
  exists (insert fs1 h2 h1)=> h H1 H2 /(eval_union_insert dj)[].
  rewrite -?insert_distr_union // => ??; splits=> //.
  rewrite disjoint_comm /insert disjoint_union_eq_l; splits*. 
Qed.

Lemma foo (fs : fset D) H Q ht :
  (forall h, hhoare fs ht (H \* (= h)) (Q \*+ (= h))) -> 
  (forall H', hhoare fs ht (H \* H') (Q \*+ H')).
Proof.
  move=> HH H' ? [h1] [h][?][?][?]->.
  case: (HH h (h1 \u h)).
  { exists h1, h; autos*. }
  move=> ? [hv][]/[swap]-[h'][?][?][->][?]-> ?.
  exists (h' \u h), hv; splits*.
  exists h', h; autos*.
Qed.

Lemma bar (fs : fset D) H Q ht :
  hhoare fs ht H Q <->
  (forall h, H h -> hhoare fs ht (= h) Q).
Proof.
  split=> hh ? /hh=> [|/(_ _ eq_refl)][h][hv][]??; exists h, hv; by subst.
Qed.

Lemma local_partition_fset h (fs : fset D) :
  exists h1 h2 fs',
    local fs h1     /\
    local fs' h2    /\
    disjoint fs fs' /\
    disjoint h1 h2  /\ 
    h = h1 \u h2.
Admitted.

Lemma proj_union h1 h2 d : 
  proj (h1 \u h2) d = proj h1 d \u proj h2 d.
Proof.
Admitted.

Lemma proj_diff h1 h2 d : 
  proj (h1 \- h2) d = proj h1 d \- proj h2 d.
Proof.
Admitted.

Lemma eval_frame h1 h2 h fs' (ht : D -> trm) (fs : fset D) hv: 
  eval fs h1 ht h2 hv ->
  local fs' h ->
  disjoint fs fs' ->
    eval fs (h1 \u h) ht (h2 \u h) hv.
Proof.
  case=> [IN OUT] lh dj.
  split=> d I; rewrite ?proj_union; last by rewrite ?OUT.
  apply/eval1_frame/IN=> // [??/filter_indom[/lh]|]; eauto.
  apply/disjoint_inv_not_indom_both; eauto.
Qed.

(*
  x ~(1)~> 5 [free x, ref 5] p ~~> 5

  
*)

(* Lemma eval1_union_disj_fset t d hv h1 h2 h h3 hv': 
  disjoint h1 h ->
  disjoint h2 h ->
  eval1 d h1 t h3 hv' -> 
  eval1 d (h1 \u h) t (h2 \u h) hv ->
  eval1 d h1 t h2 hv.
Proof.
  move=> ++ ev.
  elim: ev h2 h hv.
  { move=> > ?? ev.
    inversion ev; subst. }
  { move=> > ?? ev.
    inversion ev; subst. }
  { move=> > ?? ev.
    inversion ev; subst. }
  { do 7? intro. move=> -> ? IH > dj1 dj2 ev.
    econstructor; first eauto.
    apply/IH.
    { apply/dj1. }
    { apply/dj2. }
    inversion ev=> //; subst; inversion H2; by subst. }
  { do 8? intro. move=> -> ? IH > dj1 dj2 ev.
    apply/eval1_app_fix; first eauto. 
    apply/IH.
    { apply/dj1. }
    { apply/dj2. }
    inversion ev=> //; subst; inversion H2; by subst. }
  { do 7? intro. move=> ev1 IH1 ev2 IH2 > dj1 dj2 evh.
    inver
    econstructor.
    { apply/IH1. } }
    do 9? intro.
    move=> T ev IH1 IH2 IH3 IH4 IH5.
    intros ??? dj1 dj2 evh.
    inversion evh; subst=> //; try by case: T=> //=.
    { econstructor=> //. eauto. eauto.
      apply/IH5. }
    { econstructor=> //. eauto. eauto.
      apply/IH5. }
     }
Admitted.*)

(* Lemma eval_union_disj_fset ht (fs : fset D) hv h1 h2 h h3 hv': 
  local fs h ->
  eval fs h1 ht h3 hv' -> 
  eval fs (h1 \u h) ht (h2 \u h) hv ->
  eval fs h1 ht h2 hv.
Proof.
  move=> lh [IN1 OUT1] [IN2 OUT2]; split.
  { move=> d IN.
    apply/eval1_union_disj_fset.
    { exact/IN1. }
    move: (IN2 _ IN)=> /[! proj_union]; exact. }
  admit.
Admitted. *)

Lemma eval1_part h1 h2 h fs ht d hv: 
  ~indom fs d ->
  eval1 d (h1 \u h) ht h2 hv -> 
  local fs h ->
  disjoint h1 h ->
  exists h2', h2 = h2' \u h /\ disjoint h2' h.
Proof.
  remember (h1 \u h) as h1h eqn: HE1.
  move=> +ev; move: ev h1 HE1.
  elim; intros; subst; (try by eexists; eauto).
  { case: (H1 h1)=> // s2'[E ?]; subst.
    case: (H3 s2')=> // s3'[??]; subst.
    case: (H5 s3')=> // s4'[??]; subst.
    by eexists; eauto. }
  1-2: try by (case: (H1 h1)=> // s2'[E ?]; subst;
    by eexists; eauto).
  1-2: (case: (H0 h1)=> // s2'[E ?]; subst;
    case: (H2 s2')=> // s3'[??]; subst;
    by eexists; eauto).
  try by (case: (H0 h1)=> // s2'[E ?]; subst;
    by eexists; eauto).
  all: have ?: ~ indom h (p, d) by (move/H2 || move/H1).
  1-2: exists (update h1 (p, d) v); 
       rewrite update_union_not_r //; split=>//; 
       exact/disjoint_update_not_r.
  exists (Fmap.remove h1 (p, d)).
  rewrite remove_union_not_r //; split=>//.
  exact/disjoint_remove_l.
Qed.

Lemma eval_part h1 h2 h (fs fs' : fset D) ht hv: 
  disjoint fs fs' ->
  eval fs (h1 \u h) ht h2 hv -> 
  local fs' h ->
  disjoint h1 h ->
  exists h2', h2 = h2' \u h /\ disjoint h2' h.
Proof.
  move=> dj [IN OUT] lh dj'.
  exists (h2 \- h); split; last exact/diff_disj.
  apply/hheap_eq_proj=> d. 
  rewrite proj_union proj_diff.
  case: (prop_inv (indom fs d)).
  { move/[dup]/IN; rewrite proj_union=> + ?. 
    case/(@eval1_part _ _ _ fs').
    { apply/disjoint_inv_not_indom_both; by eauto. }
    { by move=> ?? /filter_indom[/lh]. }
    { apply/disjoint_of_not_indom_both=> -[??].
      case/filter_indom=> /[swap] _ /[swap] /filter_indom[+ _].
      applys* disjoint_inv_not_indom_both. }
    move=> ? [->] ? /[! @union_diff]; autos*. }
  move/OUT<-; rewrite proj_union union_diff //.
  apply/disj_filter; rewrite disjoint_comm.
  applys* @disj_filter.
Qed.

Lemma read_union_l' [A B : Type] `{Inhab B} [h1 : fmap A B] (h2 : fmap A B) [x : A] :
  ~indom h2 x -> read (h1 \u h2) x = read h1 x.
Proof.
  case: h1 h2=> ?? [??]. 
  rewrite /indom /union /= /read /= /map_indom /map_union.
  by case: (_ x)=> [?[]//|?]; case: (_ x).
Qed.

Lemma eval1_frame2 h1 h2 h fs ht d hv: 
  eval1 d (h1 \u h) ht (h2 \u h) hv -> 
  local fs h ->
  ~indom fs d ->
  disjoint h1 h ->
  disjoint h2 h ->
    eval1 d h1 ht h2 hv.
Proof.
  remember (h1 \u h) as h1h eqn: HE1.
  remember (h2 \u h) as h2h eqn: HE2.
  move=> ev; move: ev h1 h2 h HE1 HE2.
  elim; intros; subst; (try by econstructor; eauto).
  all: try have ?: h1 = h2 by (apply/union_eq_inv_of_disjoint; eauto).
  all: subst; try by econstructor.
  { case/(eval1_part H7): H0=> // ? [?]?; subst.
    case/(eval1_part H7): H2=> // ? [?]?; subst.
    econstructor=> //; [exact/H1|exact/H3|exact/H5]. }
  1-2: try by (case/(eval1_part H4): H=> // ? [?]?; subst;
    econstructor=> //; [exact/H0|exact/H2]).
  all: try have ?: ~ indom h (p, d) by (move/H0 || move/H1).
  all: try rewrite indom_union_eq in H.
  { move: HE2; rewrite update_union_not_r //.
    move/union_eq_inv_of_disjoint<-=> //.
    { applys* eval1_ref.
      { move=> ??; apply/H; rewrite* indom_union_eq. }
      rewrite* indom_union_eq in H0. }
    exact/disjoint_update_not_r. }
  { rewrite read_union_l' //; applys* eval1_get. }
  { move: HE2; rewrite update_union_not_r //.
    move/union_eq_inv_of_disjoint<-=> //.
    { applys* eval1_set. }
    exact/disjoint_update_not_r. }
  move: HE2. rewrite- remove_union_not_r //.
  move/union_eq_inv_of_disjoint<-=> //.
  { applys* eval1_free. }
  exact/disjoint_remove_l.
Qed.

Lemma eval_frame2 h1 h2 h fs' (ht : D -> trm) (fs : fset D) hv: 
  eval fs (h1 \u h) ht (h2 \u h) hv -> 
  local fs' h ->
  disjoint fs fs' ->
  disjoint h1 h ->
  disjoint h2 h ->
    eval fs h1 ht h2 hv.
Proof.
  move=> [IN OUT] lh d1 d2 d3.
  split.
  { move=> ? /[dup]D {}/IN /[! proj_union] IN.
    apply/eval1_frame2; first exact/IN.
    { move=> ?? /filter_indom[/lh]; eauto. }
    { exact/disjoint_inv_not_indom_both/D. }
    all: apply/disj_filter; rewrite disjoint_comm; applys* @disj_filter. }
  move=> ? /OUT /[! proj_union]/union_eq_inv_of_disjoint-> //.
  all: apply/disj_filter; rewrite disjoint_comm; applys* @disj_filter.
Qed.

Lemma local_preserv h1 h2 (fs: fset D) ht hv :
  local fs h1 -> 
  eval fs h1 ht h2 hv ->
    local fs h2.
Proof.
  move=> lh [IN OUT] x d; apply: contrapose_inv=> /[dup] I /OUT /(congr1 (@fmap_data _ _)).
  move/(congr1 (@^~ (x, d))).
  have: ~indom h1 (x, d) by move/lh.
  case: (h1) (h2) I=> /= ?? [??].
  rewrite /proj /indom /= /filter /= /map_indom /map_filter /=.
  case: (_ (_, _))=> [??[]//|].
  case: (_ (_, _))=> // ?; by case: classicT.
Qed.

Lemma baz (fs : fset D) H Q ht :
  (forall h, local fs h -> hhoare fs ht (H \* (= h)) (Q \*+ (= h))) -> 
  (forall H', hhoare fs ht (H \* H') (Q \*+ H')).
Proof.
  move=> hh.
  apply/foo=> h'.
  apply/bar=> ? [h][?][?][->][?]-> ? ->.
  case: (local_partition_fset h' fs)=> h'1 [h'2] [fs'].
  case=> lh'1 [lh'2] [?] [?] E; subst. 
  move/(_ _ (h \u h'1)): (hh h'1)=> []//.
  { exists h, h'1; splits*. }
  move=>  h' [hv] [ev].
  exists (h' \u h'2) hv; splits.
  { rewrite -union_assoc; apply/eval_frame; by [|eauto|]. }
  suff: disjoint h' h'2.
  { case: b=> h'' [?][?][->][]?->; exists h'', (h'1 \u h'2); splits*. }
  case: (local_partition_fset h fs)=> h1 [h2] [fs''][lh1][lh2][d][?]?; subst.
  replace ((h1 \u h2) \u h'1) with ((h1 \u h'1) \u h2) in ev.
  { case/(eval_part d): (ev); [autos*|autos*|].
    move=> hx[?] ?; subst; rewrite disjoint_union_eq_l; split; last autos*.
    apply/disjoint_of_not_indom_both=> -[??] /lh'2 /[swap]?.
    case/(@disjoint_inv_not_indom_both _ _ _ fs _); autos*.
    apply/local_preserv; [|apply/eval_frame2;first exact/ev; eauto|]; eauto.
    by move=> ??; rewrite indom_union_eq=> -[/lh1|/lh'1]. }
  rewrite ?union_assoc; fequals; apply union_comm_of_disjoint.
  apply/disjoint_of_not_indom_both=> -[??] /lh'1/[swap]/lh2/[swap].
  exact/disjoint_inv_not_indom_both.
Qed.

Lemma eval1_det h1 h2 ht d hv h2' hv' : 
  eval1 d h1 ht h2 hv ->
  eval1 d h1 ht h2' hv' ->
    h2 = h2' /\ hv = hv'.
Proof.
  move=> ev; elim: ev h2' hv'.
  all: intros; 
    match goal with 
    | H : eval1 _ _ _ _ _ |- _ => try by inversion H
    end.
  { inversion H6; subst. all: try by case: H=> /=.
    { case: (H1 _ _ H10)=> ??; subst.
      case: (H3 _ _ H12)=> ??; subst.
      by case: (H5 _ _ H15)=> ??; subst. }
    { inversion H0; subst; simpl in *; autos*.
      all: try by inversion H12.
      by inversion H12; inversion H13; subst. }
    inversion H0; subst; simpl in *; autos*=> //.
    inversion H13. }
  all: try by (inversion H2; subst=> //; simpl in *; autos*;
    case: H6=> *; subst; exact/H1).
  { inversion H3; subst; apply/H2; case: (H0 _ _ H7)=>-> //. }
  { inversion H3; subst; apply/H2; case: (H0 _ _ H10)=>->-> //. }
  { by inversion H1; subst; apply/H0. }
  { inversion H0; subst; simpl in *; autos*.
    all: try by inversion H; subst=> //.
    inversion H; inversion H6; subst; split=> //; by case: H5=>->. }
  { inversion H0; subst; simpl in *; autos*.
    all: try by inversion H; subst=> //.
    { inversion H4; subst; simpl in *; autos*.
      all: try by inversion H.
      inversion H; inversion H10; subst=> //. }
    inversion H; inversion H7; subst=> //; split=> //.
    all: try by case: H6 H8=> -> [->] //.
    all: try by case: H9 H10=> -> [->] //.
    case: H9 H10 H1 H6=>-> [->] <-/eq_nat_of_eq_int-> //. }
  { inversion H1; subst=> //; simpl in *; autos*.
    { by inversion H7. }
    have-> //: (p = p0). 
    exact/eq_nat_of_eq_int/Z.le_antisymm/H3/H0/H. }
  { inversion H1; subst=> //; simpl in *; autos*.
    by inversion H7. }
  { inversion H0; subst=> //; simpl in *; autos*.
    { inversion H4; subst=> //; simpl in *; autos*.
      by inversion H10. }
    by inversion H7. }
  inversion H0; subst=> //; simpl in *; autos*.
  by inversion H6.
Qed.

Lemma eval_det h1 h2 ht (fs : fset D) hv h2' hv' : 
  eval fs h1 ht h2 hv ->
  eval fs h1 ht h2' hv' ->
    h2 = h2' /\ (forall d, indom fs d -> hv d = hv' d).
Proof.
  case=> IN1 OUT1 [] IN2 OUT2.
  split=> [|d].
  { apply/hheap_eq_proj=> d.
    case: (prop_inv (indom fs d))=> [|/[dup]/OUT1<-/OUT2] //.
    by move=>/[dup]/IN1/[swap]/IN2/eval1_det/[apply]-[]. }
  by move=> /[dup]/IN1/[swap]/IN2/eval1_det/[apply]-[].
Qed.

Lemma hhoare_union2_aux (fs1 fs2 : fset D) ht h h' (Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  local fs1 h' ->
  (forall H', hhoare (fs1 \u fs2) ht ((= h) \* H') (Q' \*+ H')) ->
    hhoare fs1 ht ((= h) \* (= h')) (fun hv => 
      \exists h'',
        (= h'') \*  (= h') \* \[
          forall h', local fs2 h' -> 
            hhoare fs2 ht ((= h'') \* (= h')) (fun hv' => Q' (hv \u_fs1 hv') \* (= h'))]
      ).
Proof.
  move=> dj lh' hh ? -[h1][h2][->][->][?]->.
  case/(_ (h \u h')): (hh (= h')).
  { by exists h, h'. }
  move=> ? [hv][] /[swap]-[he [?]][?][->][?]-> ev.
  case: (eval_cup2 h he hv ht dj)=> // h'' HH.
  case: (HH h')=> //.
  1,2: rewrite disjoint_comm; applys* @disj_filter. 
  move=> d1 [ev1][ev2] h''E.
  exists (h'' \u h') hv; split=> //.
  exists h'', h'', h'; splits*. 
  exists h', (empty : hheap D); splits*.
  split=> // hi lhi ? [?][?][->][->][dji'']->.
  have ?: disjoint h hi.
  { subst. move: dji''. 
    rewrite /insert disjoint_union_eq_l=> -[_].
    move/(@disjoint_inv_not_indom_both _ _ _ _ _)=> Dj.
    apply/disjoint_of_not_indom_both=>-[? d] *.
    apply/Dj; eauto. apply/filter_indom; do ? split=> //; eauto.
    apply/disjoint_inv_not_indom_both/lhi; autos*. }
  case/(_ (h \u hi \u h')): (hh (= hi \u h')).
  { exists h (hi \u h'); autos*. }
  move=> ? [hv'] [/[swap]][he'][?][?][->][?]-> ev'.
  case: (eval_cup2 h he' hv' ht dj)=> // h''' HH'.
  case: (HH' (hi \u h'))=> //.
  1,2: rewrite disjoint_comm; applys* @disj_filter. 
  move=> dji' [ev1'][ev2'] ?.
  have ?: disjoint h' hi.
  { apply/disjoint_of_not_indom_both=> -[??]. 
    move=> /lh'/[swap]/lhi. applys* disjoint_inv_not_indom_both. }
  move/eval_frame: ev1=> /(_ _ _ lhi dj).
  rewrite ?union_assoc (union_comm_of_disjoint h' hi) //.
  case/(eval_det ev1')=> /union_eq_inv_of_disjoint<-; autos*.
  move=> hvE.
  exists (he' \u hi), hv'; splits.
  { apply/eval_frame2; first (rewrite ?union_assoc; eauto).
    all: autos*. }
  exists he', hi; splits*.
  have->//: hv \u_(fs1) hv' = hv'.
  apply/fun_ext_1=> x.
  case: (prop_inv (indom fs1 x))=> ?.
  { by rewrite uni_in // hvE. }
  by rewrite uni_nin.
Qed.

  

  (* move=> dj hh.
  move: (part_ex h dj)=> [h1] [h2] [h3] [lh1] [lh2] [lh3] [?] [?] [?] ?.
  exists () *)

  (* move=> dj hh.
  move=> ? -[h1][h2][H11][H22][?]->.
  move: (part_ex h1 dj)=> [h11] [h12] [h13] [lh1] [lh2] [lh3] [?] [?] [?] ?.
  case/(_ (h1 \u h2)): (hh (= h2)).
  { exists __, __; eauto. }
  move=> ? [hv'] [/[swap]] [h''][?][Qh'][->][?]->.
  case: (eval_cup2 h1 h'' hv' ht dj)=> // h''' HH.
  case/(HH h2)=> //.
  1,2: rewrite disjoint_comm; apply/disj_filter; autos*.
  move=>  ? [?][?] hE.
  have: exists h', h''' = h' \u (h12 \u h13) /\ local fs1 h'.
  { admit. }
  move: hE.
  subst=> /[swap].
  case=> h'''' [? lh']. subst.
  exists ((h'''' \u h12 \u h13) \u h2), hv'; splits*.
  exists (h' \u h12 \u h13), h2; do ? split*.
  exists (= h' \u h12 \u h13), (h' \u h12 \u h13), (empty : hheap D); splits*.
  split=> // H'' ? [?][hH''] [->] [?][?] ->.
  case/(_ (h1 \u (h3 \- h1))): (hh (= (h3 \- h1))).
  { exists __, __; splits; eauto.
     }
  exists (h' \u h3), hv'; split.
  
  { admit. }
  exists h', h3; splits.

Admitted. *)

Lemma hhoare_hv H Q fs ht : 
  hhoare fs ht H (fun hr => \exists hr', Q (hr \u_(fs) hr')) ->
  hhoare fs ht H Q.
Proof.
  move=> hh ? /hh[h'][hv][ev][hv']?.
  exists h', (hv \u_( fs) hv'); split=>//.
  by apply/eval_hv; eauto=> ?? /[! uni_in].
Qed.

Lemma hhoare_conseq : forall ht H' hQ' H hQ fs,
  hhoare fs ht H' hQ' ->
  H ==> H' ->
  hQ' ===> hQ ->
  hhoare fs ht H hQ.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h. { applys* MH. }
  exists h' v. splits~. { applys* MQ. }
Qed.

Lemma hhoare_union2 (fs1 fs2 : fset D) ht H H' (Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  (forall H', hhoare (fs1 \u fs2) ht (H \* H') (Q' \*+ H')) ->
    hhoare fs1 ht (H \* H') (fun hv => (\exists Q,
      Q \* 
      \[forall H', hhoare fs2 ht (Q \* H') (fun hv' => Q' (hv \u_(fs1) hv') \* H')]) \* H').
Proof.
  move=> d hh.
  apply/baz=> hx lh.
  apply/bar=> h [?][?][Hx][->][?]->.
  apply/hhoare_conseq; first (apply/hhoare_union2_aux; [apply/d|apply/lh|]).
  { move=> P; apply/bar=> ?[?][?][->][?][?]->. 
    move/bar: (hh P); apply; do ? eexists; eauto. }
  { move=> ?->; do ? eexists; eauto. }
  move=> ?? [h'] [h1][h2][->][][h3][h4][->][][?] ? [?]->[?]->.
  exists (h' \u h4), hx; splits*.
  exists (= h'), h' , h4; splits*.
  split=> //.
  exact/baz.
Qed.
(*   
  move=> dj hh.
  move: H'.
  apply/foo=> ?.
  apply/bar=> ? [h][h'][Hh][<-][?]->.
  have->: (= (h \u h')) = ((= h) \* (= h')).
  { apply/himpl_antisym=> [h1->|h1[h1'][h2'][->][->][]//].
    exists h, h'; autos*. }
  case: (@hhoare_union2_aux _ _ ht h Q' dj).
  { move=> ?? [?][?][->][?][?]->.
    apply/hh; exists h, __; autos*. }
  move=> Q /[dup]/(_ h') [hh2 _] P.
  eapply hhoare_conseq; [eauto|eauto|].
  xsimpl. apply/foo=> h0. case: (P h0)=> //.
Qed.

  move=> dj hh.
  move=> ? -[h1][h2][H11][H22][?]->.
  move: (part_ex h1 dj)=> [h11] [h12] [h13] [lh1] [lh2] [lh3] [?] [?] [?] ?.
  case/(_ (h1 \u h2)): (hh (= h2)).
  { exists __, __; eauto. }
  move=> ? [hv'] [/[swap]] [h''][?][Qh'][->][?]->.
  case: (eval_cup2 h1 h'' hv' ht dj)=> // h HH.
  case/(HH h2)=> //.
  1,2: rewrite disjoint_comm; apply/disj_filter; autos*.
  move=>  ? [?][?] hE.
  have: exists h', h = h' \u (h12 \u h13) /\ local fs1 h'.
  { admit. }
  move: hE.
  subst=> /[swap].
  case=> h' [? lh']. subst.
  exists ((h' \u h12 \u h13) \u h2), hv'; splits*.
  exists (h' \u h12 \u h13), h2; do ? split*.
  exists (= h' \u h12 \u h13), (h' \u h12 \u h13), (empty : hheap D); splits*.
  split=> // H'' ? [?][hH''] [->] [?][?] ->.
  case/(_ (h1 \u (h3 \- h1))): (hh (= (h3 \- h1))).
  { exists __, __; splits; eauto.
     }
  exists (h' \u h3), hv'; split.
  
  { admit. }
  exists h', h3; splits.
  
Admitted. *)


  (* case/(_ (h2 \u h22)): (hh (= h22)).
  exists 
  
  
  
  
  { exists h', h22, hv'; splits*.
    admit. }
  exists h22, (empty : hheap D); splits*.
   [h2][h3][h4][?][?]->.

  {  }
  
   /hh[h2][hv2]. [/(eval_cup2 dj)][h'][??] ?.
  exists h', hv2; splits*.
  exists h', (empty : hheap D); splits*; last by split.
  exists h2 hv2; splits*.
  have-> //: (hv2 \u_(fs1) hv2 = hv2).
  apply/fun_ext_1=> ?; rewrite /uni.
  by case: classicT. *)


(* Lemma hhoare_union2 (fs1 fs2 : fset D) ht H (Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  hhoare (fs1 \u fs2) ht H Q' ->
  exists Q,
    hhoare fs1 ht H (fun hv => 
      Q hv \* 
      \[hhoare fs2 ht (Q hv) (fun hv' => Q' (hv \u_(fs1) hv'))]).
Proof.
  move=> dj hh.
  exists (fun hv h => exists h' hv', eval fs2 h ht h' hv' /\ Q' (hv \u_(fs1) hv') h').
  move=> h1 /hh[h2][hv2][/(eval_cup2 dj)][h'][??] ?.
  exists h', hv2; splits*.
  exists h', (empty : hheap D); splits*; last by split.
  exists h2 hv2; splits*.
  have-> //: (hv2 \u_(fs1) hv2 = hv2).
  apply/fun_ext_1=> ?; rewrite /uni.
  by case: classicT.
Qed. *)

(* Lemma hhoare_union2 (fs1 fs2 : fset D) ht H (Q Q': (D -> val) -> hhprop) : 
  disjoint fs1 fs2 ->
  hhoare (fs1 \u fs2) ht H Q' ->
  exists Q,
    hhoare fs1 ht H Q /\
    (forall hv, 
      hhoare fs2 ht (Q hv) (fun hv' => Q' (hv \u_(fs1) hv'))).
Proof.
  move=> dj hh.
  (* case: (prop_inv (exists h, H h)). *)
  (* { case=> ? /[dup] ? /hh[h'][hv][ev Q'h']. *)
  exists (fun hv h => exists h', H h' /\ eval fs1 h' ht h hv).
  split.
  { move=> h /[dup] ? /hh[h'][hv][ev Q'h']. }
  move=> hv h' [h][] /hh [h1][hv1][][IN1 OUT1]? [IN2 OUT2].
  exists (filter (fun '(_, d) _ => ~indom fs2 d) h' \u 
          filter (fun '(_, d) _ =>  indom fs2 d) h1), hv1; splits.
  { splits=> d ?.  
    { rewrite -OUT2.
      { replace (proj (filter (fun '(_, d0) => fun=> ~ indom fs2 d0) h' \u 
                       filter (fun '(_, d0) => fun=> indom fs2 d0) h1) d) with (proj h1 d).
        { apply IN1; rewrite* indom_union_eq. }
        apply/filter_eq=> -[a ? x ->]. 
        rewrite read_union_r.
        { exact/eq_sym/filter_in. }
        by move=> /(@filter_indom _ _ _ _ _ _)[?][]. }
      by move/(disjoint_inv_not_indom_both dj). }
    apply/filter_eq=> -[a ??->].
    case: (prop_inv (indom h' (a, d)))=> IN.
    { rewrite read_union_l.
      { exact/eq_sym/filter_in. }
      apply/filter_indom; splits*. } 
    rewrite ?read_arb // indom_union_eq=> -[]/filter_indom; autos*.
    by case=> ? []. }
  
     }
  move=> F. exists (fun (_ : D -> val) (_ : hheap D) => False).
  splits*=> ?? //. 
  case: F; eauto.
Qed. *)


(* Lemma hhoare_hv_dom fs H Q ht (f : D -> val): 
  hhoare fs ht H Q ->
  hhoare fs ht H Q.
Proof.
  move=> hh ? /hh [h'][hv][ev IQ].
  do ? eexists; eauto.
  move/eval_hv_dom: ev=> ?.
  case: IQ=> ? [?][?][?][][]/[swap]->/[swap].
  by case=> _ ->; apply; do ? eexists; eauto.
Qed. *)


Section Hoare1.

Context (d : D).

Implicit Type v : val.

Definition hoare (t:trm) (H:hhprop) (Q:val->hhprop) :=
  forall h, H h -> 
    exists h' v, eval1 d h t h' v /\ Q v h'.

(** Structural rules for [hoare] triples. *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h. { applys* MH. }
  exists h' v. splits~. { applys* MQ. }
Qed.


Lemma hoare_hexists : forall t (A:Type) (J:A->hhprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hhoare_hexists : forall ht (A:Type) (J:A->hhprop) Q fs,
  (forall x, hhoare fs ht (J x) Q) ->
  hhoare fs ht (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

Lemma hhoare_hpure : forall ht (P:Prop) H Q fs,
  (P -> hhoare fs ht H Q) ->
  hhoare fs ht (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

(** Other structural rules, not required for setting up [wpgen]. *)

Lemma hoare_hforall : forall t (A:Type) (J:A->hhprop) Q,
  (exists x, hoare t (J x) Q) ->
  hoare t (hforall J) Q.
Proof using.
  introv (x&M) Hh. applys* hoare_conseq (hforall J) Q M.
  applys* himpl_hforall_l.
Qed.


Lemma hhoare_hforall : forall ht (A:Type) (J:A->hhprop) Q fs,
  (exists x, hhoare fs ht (J x) Q) ->
  hhoare fs ht (hforall J) Q.
Proof using.
  introv (x&M) Hh. applys* hhoare_conseq (hforall J) Q M.
  applys* himpl_hforall_l.
Qed.

Lemma hoare_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  hoare t H Q ->
  hoare t (\[P] \-* H) Q.
Proof using. introv HP M. rewrite* hwand_hpure_l. Qed.

Lemma hhoare_hwand_hpure_l : forall ht (P:Prop) H Q fs,
  P ->
  hhoare fs ht H Q ->
  hhoare fs ht (\[P] \-* H) Q.
Proof using. introv HP M. rewrite* hwand_hpure_l. Qed.


(** Reasoning rules for [hoare] triples. These rules follow directly
    from the big-step evaluation rules. *)

Lemma hoare_eval_like : forall t1 t2 H Q,
  eval1_like d t1 t2 ->
  hoare t1 H Q ->
  hoare t2 H Q.
Proof using.
  introv E M1 K0. forwards (s'&v&R1&K1): M1 K0.
  exists s' v. split. { applys E R1. } { applys K1. }
Qed.

Lemma hhoare_eval_like : forall ht1 ht2 H Q fs,
  eval_like fs ht1 ht2 ->
  hhoare fs ht1 H Q ->
  hhoare fs ht2 H Q.
Proof using.
  introv E M1 K0. forwards (s'&v&R1&K1): M1 K0.
  exists s' v. split. { applys E R1. } { applys K1. }
Qed.


Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h K. exists h v. splits.
  { applys eval1_val. }
  { applys* M. }
Qed.

Lemma hhoare_val :  forall hv H Q fs,
  H ==> Q hv ->
  hhoare fs (fun d => trm_val (hv d)) H Q.
Proof using.
  introv M. intros h K. exists h hv. splits.
  { applys* eval_val. }
  { applys* M. }
Qed.

Lemma hoare_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.
Proof using.
  introv M. intros h K. exists h __. splits.
  { applys~ eval1_fun. }
  { applys* M. }
Qed.

Lemma hhoare_fun : forall (x : D -> var) ht1 H Q fs,
  H ==> Q (fun d => val_fun (x d) (ht1 d)) ->
  hhoare fs (fun d => trm_fun (x d) (ht1 d)) H Q.
Proof using.
  move=> >. intros M h K. exists h __. splits.
  { applys* eval_fun. }
  { applys* M. }
Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof using.
  introv M. intros h K. exists h __. splits.
  { applys~ eval1_fix. }
  { applys* M. }
Qed.

Lemma hhoare_fix : forall (f x : D -> var) ht1 H Q fs,
  H ==> Q (fun d => val_fix (f d) (x d) (ht1 d)) ->
  hhoare fs (fun d => trm_fix (f d) (x d) (ht1 d)) H Q.
Proof using.
  move=> >. intros M h K. exists h __. splits.
  { applys* eval_fix. }
  { applys* M. }
Qed.

Lemma hoare_app_fun : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval1_app_fun E R1. } { applys K1. }
Qed.

Lemma hhoare_app_fun : forall hv1 hv2 (x : D -> var) ht1 H Q fs,
  (forall d, indom fs d -> hv1 d = val_fun (x d) (ht1 d)) ->
  hhoare fs (fun d => subst (x d) (hv2 d) (ht1 d)) H Q ->
  hhoare fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app_fun E R1. } { applys K1. }
Qed.

Lemma hoare_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval1_app_fix E R1. } { applys K1. }
Qed.

Lemma hhoare_app_fix : forall hv1 hv2 (f x : D -> var) ht1 H Q fs,
  (forall d, indom fs d -> hv1 d = val_fix (f d) (x d) (ht1 d)) ->
  hhoare fs (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (ht1 d))) H Q ->
  hhoare fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof using.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app_fix E R1. } { applys K1. }
Qed.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval1_seq R1 R2. }
Qed.

Lemma hhoare_seq : forall ht1 ht2 H Q H1 fs,
  hhoare fs ht1 H (fun hr => H1) ->
  hhoare fs ht2 H1 Q ->
  hhoare fs (fun d => trm_seq (ht1 d) (ht2 d)) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_seq R1 R2. }
Qed.

Lemma hoare_let : forall x t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v1, hoare (subst x v1 t2) (Q1 v1) Q) ->
  hoare (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval1_let R2. }
Qed.

Lemma hhoare_let : forall (x : D -> var) ht1 ht2 H Q Q1 fs,
  hhoare fs ht1 H Q1 ->
  (forall hv1, hhoare fs (fun d => subst (x d) (hv1 d) (ht2 d)) (Q1 hv1) Q) ->
  hhoare fs (fun d => trm_let (x d) (ht1 d) (ht2 d)) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_let R2. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval1_if. }
Qed.

Lemma hhoare_if : forall (b: D -> bool) ht1 ht2 H Q fs,
  hhoare fs (fun d => if b d then ht1 d else ht2 d) H Q ->
  hhoare fs (fun d => trm_if (b d) (ht1 d) (ht2 d)) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval_if. }
Qed.


(** Operations on the state. *)

Lemma single_fresh : forall null (h : hheap D) v,
  exists l, 
    Fmap.disjoint (single (l, d) v) h /\ l <> null /\ 
    (forall p', ~ Fmap.indom h (p', d) -> (l <= p')%Z).
Proof using.
Admitted.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~(d)~> v) \* H).
Proof using.
  intros. intros s1 K0.
  forwards~ (p&D&N&M): (single_fresh 0%nat s1 v).
  exists (Fmap.union (Fmap.single (p, d) v) s1) (val_loc p). split.
  { applys~ eval_ref_sep. }
  { applys~ hstar_intro.
    { exists p. rewrite~ hstar_hpure_l. split~. { applys~ hsingle_intro. } } }
Qed.

Lemma hoare_get : forall H v p,
  hoare (val_get p)
    ((p ~(d)~> v) \* H)
    (fun r => \[r = v] \* (p ~(d)~> v) \* H).
Proof using.
  intros. intros s K0. exists s v. split.
  { destruct K0 as (s1&s2&P1&P2&D&U).
    lets E1: hsingle_inv P1. subst s1. applys eval_get_sep U. }
  { rewrite~ hstar_hpure_l. }
Qed.

Lemma hoare_set : forall H w p v,
  hoare (val_set (val_loc p) v)
    ((p ~(d)~> w) \* H)
    (fun r => \[r = val_unit] \* (p ~(d)~> v) \* H).
Proof using.
  intros. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U).
  lets E1: hsingle_inv P1.
  exists (Fmap.union (Fmap.single (p, d) v) h2) val_unit. split.
  { subst h1. applys eval_set_sep U D. auto. }
  { rewrite hstar_hpure_l. split~.
    { applys~ hstar_intro.
      { applys~ hsingle_intro. }
      { subst h1. applys Fmap.disjoint_single_set D. } } }
Qed.

Lemma hoare_free : forall H p v,
  hoare (val_free (val_loc p))
    ((p ~(d)~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U).
  lets E1: hsingle_inv P1.
  exists h2 val_unit. split.
  { subst h1. applys eval_free_sep U D. }
  { rewrite hstar_hpure_l. split~. }
Qed.

(** Other operations. *)

Lemma hoare_unop : forall v H op v1,
  evalunop op v1 v ->
  hoare (op v1)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* eval1_unop. }
  { rewrite* hstar_hpure_l. }
Qed.

Lemma hoare_binop : forall v H op v1 v2,
  evalbinop op v1 v2 v ->
  hoare (op v1 v2)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* eval1_binop. }
  { rewrite* hstar_hpure_l. }
Qed.

(** Bonus: example of proofs for a specific primitive operation. *)

Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof.
  dup.
  { intros. applys hoare_binop. applys evalbinop_add. }
  { intros. intros s K0. exists s (val_int (n1 + n2)). split.
    { applys eval1_binop. applys evalbinop_add. }
    { rewrite* hstar_hpure_l. } }
Qed.

Lemma hoare_frame H (P : hhprop) Q t fs: 
  hlocal H fs ->
  ~ indom fs d ->
  hoare t P Q -> 
  hoare t (P \* H) (fun v => Q v \* H).
Proof.
  move=> hl ? ht ? [Ph][Hh] [/[dup]?/ht] [h'][v] [ev ?].
  case=> /[dup]/hl lfs ? [disj]->.
  exists (h' \u Hh), v; split*.
  { apply/eval1_frame; eauto. }
  exists h', Hh; splits=> //.
  case: (local_partition Ph d)=> Phd [Phnd] [?][?] E; subst.
  case/eval1_local: ev=> // h'd [lh'] ->.
  move: disj; rewrite ?disjoint_union_eq_l=> -[]; split=> //.
  apply/disjoint_of_not_indom_both=> -[??] /lfs /[swap] /lh'.
  by rewrite indom_single_eq=> <-.
Qed.


End Hoare1.

Lemma indom_update {A B : Type} {fm : fmap A B} {x y} :
  Fmap.indom (update fm x y) x.
Admitted.

Lemma update_neq {A B : Type} {fm : fmap A B} {x y z} `{Inhab B} :
  z <> x -> 
  read (update fm x y) z = read fm z.
Admitted.

Lemma update_eq {A B : Type} {fm : fmap A B} {x y} `{Inhab B} :
  read (update fm x y) x = y.
Admitted.

Lemma update_empty {A B : Type} {x : A} {y : B} :
  single x y = update empty x y.
Admitted.

Lemma indom_single {A B D : Type} {x : A} {y : B} (fm : fmap A D) `{Inhab D} :
  indom fm = indom (single x y) -> 
  fm = single x (read fm x).
Admitted.

Lemma update_update {A B : Type} {x z : A} {y w : B} (fm : fmap A B) :
  x <> z ->
    update (update fm x y) z w = 
    update (update fm z w) x y.
Proof.
Admitted.

Lemma fmapE'  {A B : Type} (fm1 fm2 : fmap A B) `{Inhab B} : 
  (fm1 = fm2) <-> (forall x, read fm1 x = read fm2 x).
Proof.
Admitted.

Lemma fmapE  {A B : Type} (fm1 fm2 : fmap A B) `{Inhab B} : 
  (fm1 = fm2) = (forall x, indom (fm1 \u fm2) x -> read fm1 x = read fm2 x).
Proof.
Admitted.

Lemma fmap0E A B (fm : fmap A B) `{Inhab B} : 
  (fm = empty) = (forall x, indom fm x -> read fm x = arbitrary).
Proof.
Admitted.

Lemma eval1_proj_d d h h' t v : 
  eval1 d h t h' v -> 
  eval1 d (proj h d) t (proj h' d) v.
Proof.
Admitted.

Lemma hhoare_update Q' H Q ht fs d :
  ~ Fmap.indom fs d ->
  hoare d (ht d) H Q' -> 
  (forall v, hhoare fs ht (Q' v) (fun hv => Q (upd hv d v))) ->
  hhoare (update fs d tt) ht H Q.
Proof.
  move=> ? HH ?.
  rewrite update_eq_union_single.
  apply/(@hhoare_union _ _ _ _ (fun hv => Q' (hv d))).
  { exact/disjoint_single_of_not_indom. }
  { move=> ? /HH[h'][v][ev ?].
    exists h', (upd (fun (d : D) => v) d v); split*; rewrite ?upd_eq //.
    splits*=> >; rewrite indom_single_eq.
    { move=> <- /[! upd_eq]; exact/eval1_proj_d. }
    apply/eval1_proj_nd; eauto. }
  move=> hv; rewrite update_empty.
  apply/hhoare_conseq; eauto=> ?.
  by rewrite uni_upd ?uni0.
Qed.

Arguments hhoare_update _ {_}.

Lemma hhoareP H Q ht fs : 
  (exists (f : fset D -> (D -> val) -> hhprop),
    (exists hv, f empty hv = H) /\ 
    (forall hv, f fs hv = Q hv) /\
    forall (fs' : fset D) d hv, 
      indom fs d ->
      ~ indom fs' d ->
      hoare d (ht d) (f fs' hv) (fun v => f (update fs' d tt) (upd hv d v))) -> 
        hhoare fs ht H Q.
Proof.
  elim/fset_ind: fs H Q.
  { move=> ??.
    case=> f [][hv <-][/(_ hv)] QE _.
    move=> h /[! QE]. exists h, hv; split*.
    by constructor. }
  move=> fs x IHfs NIND H Q.
  case=> f [][hv<-] [QE] h1.
  apply/(hhoare_update (fun v => f (single x tt) (upd hv x v)))=> //.
  { rewrite update_empty; apply/h1; rewrite // indom_update_eq; eauto. }
  move=> v; apply/(IHfs _ _).
  exists (fun fs hv => f (update fs x tt) (upd hv x v)); splits*.
  { eexists; by rewrite ?update_empty; eauto. }
  move=> fs' d hv'.
  case: (prop_inv (x = d))=> [<- /NIND //|???].
  replace (fun v0 => f (update (update fs' d tt) x tt) (upd (upd hv' d v0) x v)) with 
    (fun v0 => f (update (update fs' x tt) d tt) (upd (upd hv' x v) d v0)).
  { apply/h1; rewrite* indom_update_eq. }
  apply/fun_ext_1=> ?. rewrite update_update 1?upd_upd //.
Qed.

Coercion read : fmap >-> Funclass.

Lemma hoare_Q_eq d t H Q1 Q2 :
  (forall v, Q1 v = Q2 v) -> 
  hoare d t H Q1 = hoare d t H Q2.
Admitted.

Lemma hlocal_subset fs1 fs2 H :
  (forall x, indom fs1 x -> indom fs2 x) ->
  hlocal H fs1 -> hlocal H fs2.
Admitted.

Arguments hlocal_subset _ {_}.

Lemma hhoare_hstar_fset H (P : D -> hhprop) (Q : D -> val -> hhprop) fs ht :
  (forall d, hlocal (P d) (single d tt)) ->
  (forall d v, hlocal (Q d v) (single d tt)) ->
  (forall d, indom fs d -> 
      hoare d (ht d) (P d \* H) (fun v => Q d v \* H)) ->
  hhoare fs ht ((\*_(d <- fs) P d) \* H) (fun hv => (\*_(d <- fs) Q d (hv d)) \* H).
Proof.
  move=> l l2 h1. 
  apply/hhoareP.
  set f := fun fs' hv => 
    ((\*_(d <- fs \- fs') P d) \* 
    H) \*
    (\*_(d <- fs') Q d (hv d)).
  exists f; splits; rewrite/f.
  { exists (fun (d : D) => arbitrary : val).
    rewrite diff0 hstar_fset_empty; xsimpl. }
  { move=> ?; rewrite diffxx hstar_fset_empty; xsimpl. }
  move=> fs' d' hv *.
  replace (fun v =>
    ((\*_(d <- fs \- update fs' d' tt) P d) \* H) \*
    \*_(d <- update fs' d' tt) Q d (upd hv d' v d)) with 
    (fun v0 =>
      (((\*_(d <- fs \- update fs' d' tt) P d) \* H) \* Q d' v0) \*
      \*_(d <- fs') Q d (hv d)).
  { eapply hoare_frame; eauto.
    { apply/hlocal_hstar_fset=> x ?.
      apply/(hlocal_subset (single x tt))/l2.
      by move=> ? /[! indom_single_eq]<-. }
    rewrite (diff_upd d') // hstar_fset_update.
    { replace ((P d' \* _) \* H) with 
       ((P d' \* H) \* \*_(d <- fs \- update fs' d' tt) P d) by xsimpl.
      replace (fun v => (_ \* H) \* _) with 
        (fun v => (Q d' v \* H) \* \*_(d <- fs \- update fs' d' tt) P d).
      { apply/hoare_frame; auto.
        apply/hlocal_hstar_fset=> x ?.
        { apply/(hlocal_subset (single x tt))=> // ?.
          rewrite indom_single_eq=><-; eauto. }
        rewrite diff_indom.
        rewrite* indom_update_eq. }
      apply/fun_ext_1. xsimpl. }
    rewrite diff_indom; rewrite* indom_update_eq. }
  apply/fun_ext_1=> v.
  rewrite hstar_fset_update //.
  under (@hstar_fset_eq fs' (fun _ => Q _ (upd _ _ _ _))).
  { move=> ??; rewrite upd_neq; first over.
    by move=> ?; subst. }
  rewrite upd_eq; xsimpl.
Qed.

Ltac hlocal := 
  repeat (intros; 
  match goal with 
  | |- hlocal (_ \* _) _ => apply hlocal_hstar
  | |- hlocal \[] _    => apply hlocal_hempty
  | |- hlocal (hexists _) _ => apply hlocal_hexists
  | |- hlocal (hsingle _ _ _) (single _ _) => apply hlocal_hsingle_single
  | |- hlocal (hpure _) _ => apply hlocal_hpure
  end).

Hint Extern 1 (hlocal _ _) => hlocal.

Lemma hhoare_val_eq H Q fs (f : D -> val) ht :
  hhoare fs ht H (fun hv => \[forall d, indom fs d -> hv d = f d] \* Q) ->
  hhoare fs ht H (fun hv => \[hv = f] \* Q).
Proof.
  move=> hh ? /hh [h'][hv][?][h1][h2][] [E] /hempty_inv-> [?][].
  rewrite union_empty_l=> *.
  exists h2 f; splits*; subst*.
  { by apply/eval_hv; eauto=> ? /E->. }
  exists (empty : hheap D), h2; splits*.
  by exists (@eq_refl _ f).
Qed.

Lemma hhoare_ref' : forall H (f : D -> val) fs,
  hhoare fs (fun d => val_ref (f d))
    H
    (fun hr => (\*_(d <- fs) \exists p, \[hr d = val_loc p] \* p ~(d)~> f d) \* H).
Proof.
  intros.
  replace H with ((\*_(_ <- fs) \[]) \* H) at 1; last (rewrite hstar_fset_emptys; xsimpl).
  apply (hhoare_hstar_fset _ (fun d v => \exists p, \[v = _] \* _))=> *; autos~.
  replace (\[] \* H) with H by xsimpl.
  exact/hoare_ref.
Qed.

Lemma hhoare_ref : forall H (f : D -> val) fs,
  hhoare fs (fun d => val_ref (f d))
    H
    (fun hr => (\exists (p : D -> loc), \[hr = val_loc \o p] \* \*_(d <- fs) p d ~(d)~> f d) \* H).
Proof.
Admitted.


Lemma hhoare_get : forall H (v : D -> val) (p : D -> loc) fs,
  hhoare fs (fun d => val_get (p d))
    ((\*_(d <- fs) p d ~(d)~> v d) \* H)
    (fun hr => 
      \[hr = v] \* 
      (\*_(d <- fs) p d ~(d)~> v d) \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_assoc -hstar_fset_pure_hstar=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _] \* _)); autos~.
  move=> d ?. 
  apply/hoare_conseq; by [apply hoare_get|eauto|xsimpl].
Qed.

Lemma hhoare_set : forall H (w : D -> val) (v : D -> val) (p : D -> loc) fs,
  hhoare fs (fun d => val_set (val_loc (p d)) (v d))
    ((\*_(d <- fs) p d ~(d)~> w d) \* H)
    (fun hr => \[hr = fun _ => val_unit] \* (\*_(d <- fs) p d ~(d)~> v d) \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_assoc -hstar_fset_pure_hstar=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _] \* _)); autos~.
  move=> d ?. 
  apply/hoare_conseq; by [apply hoare_set|eauto|xsimpl].
Qed.

Lemma hhoare_free : forall H (v : D -> val) (p : D -> loc) fs,
  hhoare fs (fun d => val_free (val_loc (p d)))
    ((\*_(d <- fs) p d ~(d)~> v d) \* H)
    (fun hr => \[hr = fun _ => val_unit] \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_fset_pure=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _])); autos~.
  move=> d ?. 
  apply/hoare_conseq; by [apply hoare_free|eauto|xsimpl].
Qed.

Lemma hhoare_unop : forall (v : D -> val) H (op : D -> prim) (v1 : D -> val) fs,
  (forall d, indom fs d -> evalunop (op d) (v1 d) (v d)) ->
  hhoare fs (fun d => (op d) (v1 d))
    H
    (fun hr => \[hr = v] \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  replace H with ((\*_(_ <- fs) \[]) \* H) at 1; last (rewrite hstar_fset_emptys; xsimpl).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_fset_pure=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _])); autos~.
  move=> d ?. 
  apply/hoare_conseq; [apply hoare_unop|eauto|xsimpl]; by eauto.
Qed.

Lemma hhoare_binop :  forall (v : D -> val) H (op : D -> prim) (v1 v2 : D -> val) fs,
  (forall d, indom fs d -> evalbinop (op d) (v1 d) (v2 d) (v d)) ->
  hhoare fs (fun d => (op d) (v1 d) (v2 d))
    H
    (fun hr => \[hr = v] \* H).
Proof using.
  intros.
  apply (hhoare_val_eq (fun _ => _)).
  replace H with ((\*_(_ <- fs) \[]) \* H) at 1; last (rewrite hstar_fset_emptys; xsimpl).
  apply/hhoare_conseq=> [||?]; [|eauto|]; first last.
  { rewrite -hstar_fset_pure=> ?. exact. }
  apply (hhoare_hstar_fset _ (fun d v => \[v = _])); autos~.
  move=> d ?. 
  apply/hoare_conseq; [apply hoare_binop|eauto|xsimpl]; by eauto.
Qed.

(* ================================================================= *)
(** ** Definition of Separation Logic Triples. *)

(** A Separation Logic triple [triple t H Q] may be defined either in
    terms of Hoare triples, or in terms of [wp], as [H ==> wp t Q].
    We prefer the former route, which we find more elementary. *)
(* 
Definition triple (t : trm) (H : hhprop) (Q:val -> hhprop) : Prop :=
  forall (H' : hhprop), hoare t (H \* H') (Q \*+ H'). *)

Section htriple.

Context (fs : fset D).

Definition htriple (ht : D -> trm) (H : hhprop) (Q : (D -> val) -> hhprop) : Prop :=
  forall (H' : hhprop), hhoare fs ht (H \* H') (Q \*+ H').

(** We introduce a handy notation for postconditions of functions
    that return a pointer:  [funloc p => H] is short for
    [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* H)]. *)

Notation "'funloc' p '=>' H" :=
  (fun hr => \exists (p : D -> loc), \[hr = val_loc \o p] \* H)
  (at level 200, p ident, format "'funloc'  p  '=>'  H") : hprop_scope.

(* ================================================================= *)
(** ** Structural Rules *)

(** Consequence and frame rule. *)


Lemma htriple_conseq : forall ht H' Q' H Q,
  htriple ht H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  htriple ht H Q.
Proof using.
  introv M MH MQ. intros HF. applys hhoare_conseq M.
  { xchanges MH. }
  { intros x. xchanges (MQ x). }
Qed.

Lemma htriple_frame : forall ht H Q H',
  htriple ht H Q ->
  htriple ht (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF. applys hhoare_conseq (M (HF \* H')); xsimpl.
Qed.

(** Details for the proof of the frame rule. *)

Lemma htriple_frame' : forall ht H Q H',
  htriple ht H Q ->
  htriple ht (H \* H') (Q \*+ H').
Proof using.
  introv M. unfold htriple in *. rename H' into H1. intros H2.
  applys hhoare_conseq. applys M (H1 \* H2).
  { rewrite hstar_assoc. auto. }
  { intros v. rewrite hstar_assoc. auto. }
Qed.

(** Extraction rules. *)

Lemma htriple_hexists : forall ht (A:Type) (J:A->hhprop) Q,
  (forall x, htriple ht (J x) Q) ->
  htriple ht (hexists J) Q.
Proof using.
  introv M. intros HF. rewrite hstar_hexists.
  applys hhoare_hexists. intros. applys* M.
Qed.

Lemma htriple_hpure : forall ht (P:Prop) H Q,
  (P -> htriple ht H Q) ->
  htriple ht (\[P] \* H) Q.
Proof using.
  introv M. intros HF. rewrite hstar_assoc.
  applys hhoare_hpure. intros. applys* M.
Qed. (* Note: can also be proved from [triple_hexists] *)

Lemma htriple_hforall : forall A (x:A) ht (J:A->hhprop) Q,
  htriple ht (J x) Q ->
  htriple ht (hforall J) Q.
Proof using.
  introv M. applys* htriple_conseq M. applys hforall_specialize.
Qed.

Lemma htriple_hwand_hpure_l : forall ht (P:Prop) H Q,
  P ->
  htriple ht H Q ->
  htriple ht (\[P] \-* H) Q.
Proof using.
  introv HP M. applys* htriple_conseq M. rewrite* hwand_hpure_l.
Qed.

(** Combined and ramified rules. *)

Lemma htriple_conseq_frame : forall H2 H1 Q1 ht H Q,
  htriple ht H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  htriple ht H Q.
Proof using.
  introv M WH WQ. applys htriple_conseq WH WQ. applys htriple_frame M.
Qed.

Lemma htriple_ramified_frame : forall H1 Q1 ht H Q,
  htriple ht H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  htriple ht H Q.
Proof using.
  introv M W. applys htriple_conseq_frame (Q1 \--* Q) M W.
  { rewrite~ <- qwand_equiv. }
Qed.

(** Named heaps. *)

Lemma hexists_named_eq : forall H,
  H = (\exists h, \[H h] \* (= h)).
Proof using.
  intros. apply himpl_antisym.
  { intros h K. applys hexists_intro h.
    rewrite* hstar_hpure_l. }
  { xpull. intros h K. intros ? ->. auto. }
Qed.

Lemma htriple_named_heap : forall ht H Q,
  (forall h, H h -> htriple ht (= h) Q) ->
  htriple ht H Q.
Proof using.
  introv M. rewrite (hexists_named_eq H).
  applys htriple_hexists. intros h.
  applys* htriple_hpure.
Qed.

(* ================================================================= *)
(** ** Rules for Terms *)

Lemma htriple_eval_like : forall ht1 ht2 H Q,
  eval_like fs ht1 ht2 ->
  htriple ht1 H Q ->
  htriple ht2 H Q.
Proof using.
  introv E M1. intros H'. applys hhoare_eval_like E. applys M1.
Qed.

Lemma htriple_val : forall (v : D -> val) H Q,
  H ==> Q v ->
  htriple (fun d => trm_val (v d)) H Q.
Proof using.
  introv M. intros HF. applys hhoare_val. { xchanges M. }
Qed.

Lemma htriple_fun : forall (x : D -> var) ht1 H Q,
  H ==> Q (fun d => val_fun (x d) (ht1 d)) ->
  htriple (fun d => trm_fun (x d) (ht1 d)) H Q.
Proof using.
  introv M. intros HF. applys~ hhoare_fun. { xchanges M. }
Qed.

Lemma htriple_fix : forall (f x : D -> var) ht1 H Q,
  H ==> Q (fun d => val_fix (f d) (x d) (ht1 d)) ->
  htriple (fun d => trm_fix (f d) (x d) (ht1 d)) H Q.
Proof using.
  introv M. intros HF. applys~ hhoare_fix. { xchanges M. }
Qed.

Lemma htriple_seq : forall ht1 ht2 H Q H1,
  htriple ht1 H (fun hv => H1) ->
  htriple ht2 H1 Q ->
  htriple (fun d => trm_seq (ht1 d) (ht2 d)) H Q.
Proof using.
  introv M1 M2. intros HF. applys hhoare_seq.
  { applys M1. }
  { applys hhoare_conseq M2; xsimpl. }
Qed.

Lemma htriple_let : forall x t1 t2 Q1 H Q,
  htriple t1 H Q1 ->
  (forall v1, htriple (fun d => subst (x d) (v1 d) (t2 d)) (Q1 v1) Q) ->
  htriple (fun d => trm_let (x d) (t1 d) (t2 d)) H Q.
Proof using.
  introv M1 M2. intros HF. applys hhoare_let.
  { applys M1. }
  { intros v. applys hhoare_conseq M2; xsimpl. }
Qed.

Lemma htriple_let_val : forall x v1 t2 H Q,
  htriple (fun d => subst (x d) (v1 d) (t2 d)) H Q ->
  htriple (fun d => trm_let (x d) (v1 d) (t2 d)) H Q.
Proof using.
  introv M. applys htriple_let (fun v => \[v = v1] \* H).
  { applys htriple_val. xsimpl*. }
  { intros v. applys htriple_hpure. intros ->. applys M. }
Qed.

Lemma htriple_if : forall (b:D -> bool) t1 t2 H Q,
  htriple (fun d => if (b d) then (t1 d) else (t2 d)) H Q ->
  htriple (fun d => trm_if (b d) (t1 d) (t2 d)) H Q.
Proof using.
  introv M1. intros HF. applys hhoare_if. applys M1.
Qed.

Lemma htriple_app_fun : forall x v1 v2 t1 H Q,
  (forall d, indom fs d -> v1 d = val_fun (x d) (t1 d)) ->
  htriple (fun d => subst (x d) (v2 d) (t1 d)) H Q ->
  htriple (fun d => trm_app (v1 d) (v2 d)) H Q.
Proof using.
  (* can also be proved using [triple_eval_like] *)
  unfold htriple. introv E M1. intros H'.
  applys hhoare_app_fun E. applys M1.
Qed.

Lemma htriple_app_fun_direct : forall x v2 t1 H Q,
  htriple (fun d => subst (x d) (v2 d) (t1 d)) H Q ->
  htriple (fun d => trm_app (val_fun (x d) (t1 d)) (v2 d)) H Q.
Proof using. introv M. applys* htriple_app_fun. Qed.

Lemma htriple_app_fix : forall v1 v2 f x t1 H Q,
  (forall d, indom fs d -> v1 d = val_fix (f d) (x d) (t1 d)) ->
  htriple (fun d => subst (x d) (v2 d) (subst (f d) (v1 d) (t1 d))) H Q ->
  htriple (fun d => trm_app (v1 d) (v2 d)) H Q.
Proof using.
  (* can also be proved using [htriple_eval_like] *)
  unfold htriple. introv E M1. intros H'.
  applys hhoare_app_fix E. applys M1.
Qed.

Lemma htriple_app_fix_direct : forall v2 f x t1 H Q,
  htriple (fun d => subst x v2 (subst f (val_fix f x t1) t1)) H Q ->
  htriple (fun d => trm_app (val_fix f x t1) v2) H Q.
Proof using. introv M. applys* htriple_app_fix. Qed.

(* ================================================================= *)
(** ** Triple-Style Specification for Primitive Functions *)

(** Operations on the state. *)

Lemma htriple_ref : forall (v : D -> val),
  htriple (fun d => val_ref (v d))
    \[]
    (funloc p => \*_(d <- fs) p d ~(d)~> v d).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_ref; xsimpl~.
Qed.

Lemma htriple_get : forall v (p : D -> loc),
  htriple (fun d => val_get (p d))
    (\*_(d <- fs) p d ~(d)~> v d)
    (fun hr => \[hr = v] \* (\*_(d <- fs) p d ~(d)~> v d)).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_get; xsimpl~.
Qed.

Lemma htriple_set : forall (w : D -> val) (p : D -> loc) (v : D -> val),
  htriple (fun d => val_set (val_loc (p d)) (v d))
    (\*_(d <- fs) p d ~(d)~> w d)
    (fun _ => \*_(d <- fs) p d ~(d)~> v d).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_set; xsimpl~.
Qed.

Lemma htriple_free : forall (p : D -> loc) v,
  htriple (fun d => val_free (val_loc (p d)))
    (\*_(d <- fs) p d ~(d)~> v d)
    (fun _ => \[]).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_free; xsimpl~.
Qed.

(** Other operations. *)

Lemma htriple_unop : forall v op v1,
  (forall d, indom fs d -> evalunop (op d) (v1 d) (v d)) ->
  htriple (fun d => (op d) (v1 d)) \[] (fun hr => \[hr = v]).
Proof using.
  introv R. unfold htriple. intros H'.
  applys* hhoare_conseq hhoare_unop. xsimpl*.
Qed.

Lemma htriple_binop : forall v (op : D -> prim) v1 v2,
  (forall d, indom fs d -> evalbinop (op d) (v1 d) (v2 d) (v d)) ->
  htriple (fun d => (op d) (v1 d) (v2 d)) \[] (fun hr => \[hr = v]).
Proof using.
  introv R. unfold htriple. intros H'.
  applys* hhoare_conseq hhoare_binop. xsimpl*.
Qed.


Lemma htriple_add : forall (n1 n2 : D -> int),
  htriple (fun d => val_add (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (n1 d + n2 d)]).
Proof using. intros. applys* htriple_binop; intros. apply evalbinop_add. Qed.

Lemma htriple_div : forall (n1 n2 : D -> int),
  (forall d, indom fs d -> n2 d <> 0) ->
  htriple (fun d => val_div (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (Z.quot (n1 d) (n2 d))]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_div. Qed.

Lemma htriple_neg : forall (b1:D -> bool),
  htriple (fun d => val_neg (b1 d))
    \[]
    (fun hr => \[hr = fun d => val_bool (neg (b1 d))]).
Proof using. intros. applys* htriple_unop; intros; applys* evalunop_neg. Qed.

Lemma htriple_opp : forall (n1 : D -> int),
  htriple (fun d => val_opp (n1 d))
    \[]
    (fun hr => \[hr = fun d => val_int (- (n1 d))]).
Proof using. intros. applys* htriple_unop; intros; applys* evalunop_opp. Qed.

Lemma htriple_eq : forall (v1 v2 : D -> val),
  htriple (fun d => val_eq (v1 d) (v2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue ((v1 d) = (v2 d))]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_eq. Qed.

Lemma htriple_neq : forall (v1 v2 : D -> val),
  htriple (fun d => val_neq (v1 d) (v2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (v1 d <> v2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys evalbinop_neq. Qed.

Lemma htriple_sub : forall (n1 n2 : D -> int),
  htriple (fun d => val_sub (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (n1 d - n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_sub. Qed.

Lemma htriple_mul : forall (n1 n2 : D -> int),
  htriple (fun d => val_mul (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (n1 d * n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_mul. Qed.

Lemma htriple_mod : forall (n1 n2 : D -> int),
  (forall d, indom fs d -> n2 d <> 0) ->
  htriple (fun d => val_mod (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => val_int (Z.rem (n1 d) (n2 d))]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_mod. Qed.

Lemma htriple_le : forall (n1 n2 : D -> int),
  htriple (fun d => val_le (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (n1 d <= n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_le. Qed.

Lemma htriple_lt : forall (n1 n2 : D -> int),
  htriple (fun d => val_lt (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (n1 d < n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_lt. Qed.

Lemma htriple_ge : forall (n1 n2 : D -> int),
  htriple (fun d => val_ge (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (n1 d >= n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_ge. Qed.

Lemma htriple_gt : forall (n1 n2 : D -> int),
  htriple (fun d => val_gt (n1 d) (n2 d))
    \[]
    (fun hr => \[hr = fun d => isTrue (n1 d > n2 d)]).
Proof using. intros. applys* htriple_binop; intros; applys* evalbinop_gt. Qed.

Lemma htriple_ptr_add : forall (p : D -> loc) (n : D -> int),
  (forall d, indom fs d -> p d + n d >= 0) ->
  htriple (fun d => val_ptr_add (p d) (n d))
    \[]
    (fun hr => \[hr = fun d => val_loc (abs (p d + n d))]).
Proof using.
  intros. applys* htriple_binop; intros; applys* evalbinop_ptr_add.
  { rewrite~ abs_nonneg. }
Qed.

Lemma htriple_ptr_add_nat : forall (p : D -> loc) (f:D -> nat),
  htriple (fun d => val_ptr_add (p d) (f d))
    \[]
    (fun hr => \[hr = fun d => val_loc (p d + f d)%nat]).
Proof using.
  intros. applys htriple_conseq htriple_ptr_add. { math. } { xsimpl. }
  { xsimpl. intros. subst. 
    applys fun_ext_1; intros; fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.

(* ================================================================= *)
(** ** Alternative Definition of [wp] *)

(* ----------------------------------------------------------------- *)
(** *** Definition of the Weakest-Precondition Judgment. *)

(** [wp] is defined on top of [hhoare] htriples. More precisely [wp t Q]
    is a heap predicate such that [H ==> wp t Q] if and only if
    [htriple t H Q], where [htriple t H Q] is defined as
    [forall H', hhoare t (H \* H') (Q \*+ H')]. *)

Definition wp t := fun Q =>
  \exists H, H \* \[forall H', hhoare fs t (H \* H') (Q \*+ H')].

(** Equivalence with htriples. *)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (htriple t H Q).
Proof using.
  unfold wp, htriple. iff M.
  { intros H'. applys hhoare_conseq. 2:{ applys himpl_frame_l M. }
     { clear M. rewrite hstar_hexists. applys hhoare_hexists. intros H''.
       rewrite (hstar_comm H''). rewrite hstar_assoc.
       applys hhoare_hpure. intros N. applys N. }
     { auto. } }
  { xsimpl H. apply M. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Structural Rule for [wp] *)

(** The ramified frame rule. *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using.
  intros. unfold wp. xpull. intros H M.
  xsimpl (H \* (Q1 \--* Q2)). intros H'.
  applys hhoare_conseq M; xsimpl.
Qed.

Arguments wp_ramified : clear implicits.

(** Corollaries. *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  introv M. applys himpl_trans_r (wp_ramified Q1 Q2). xsimpl. xchanges M.
Qed.

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using. intros. applys himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_ramified_frame : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.

(* ----------------------------------------------------------------- *)
(** *** Weakest-Precondition Style Reasoning Rules for Terms. *)

Lemma wp_eval_like : forall t1 t2 Q,
  eval_like fs t1 t2 ->
  wp t1 Q ==> wp t2 Q.
Proof using.
  introv E. unfold wp. xpull. intros H M. xsimpl H.
  intros H'. applys hhoare_eval_like E M.
Qed.

Lemma wp_val : forall v Q,
  Q v ==> wp (fun d => trm_val (v d)) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hhoare_val. xsimpl. Qed.

Lemma wp_fun : forall x t Q,
  Q (fun d => val_fun (x d) (t d)) ==> wp (fun d => trm_fun (x d) (t d)) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hhoare_fun. xsimpl. Qed.

Lemma wp_fix : forall f x t Q,
  Q (fun d => val_fix (f d) (x d) (t d)) ==> wp (fun d => trm_fix (f d) (x d) (t d)) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hhoare_fix. xsimpl. Qed.

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  (forall d, v1 d = val_fun (x d) (t1 d)) ->
  wp (fun d => subst (x d) (v2 d) (t1 d)) Q ==> wp (fun d => trm_app (v1 d) (v2 d)) Q.
Proof using. introv EQ1. unfold wp. xsimpl; intros. applys* hhoare_app_fun. Qed.
(* variant: introv EQ1. applys wp_eval_like. introv R. applys* eval_app_fun. *)

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  (forall d, v1 d = val_fix (f d) (x d) (t1 d)) ->
  wp (fun d => subst (x d) (v2 d) (subst (f d) (v1 d) (t1 d))) Q ==> wp (fun d => trm_app (v1 d) (v2 d)) Q.
Proof using. introv EQ1. unfold wp. xsimpl; intros. applys* hhoare_app_fix. Qed.
(* variant: introv EQ1. applys wp_eval_like. introv R. applys* eval_app_fix. *)

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun hr => wp t2 Q) ==> wp (fun d => trm_seq (t1 d) (t2 d)) Q.
Proof using.
  intros. unfold wp at 1. xsimpl. intros H' M1.
  unfold wp at 1. xsimpl. intros H''.
  applys hhoare_seq. applys (rm M1). applys* wp_equiv.
Qed.

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (fun d => subst (x d) (v d) (t2 d)) Q) ==> wp (fun d => trm_let (x d) (t1 d) (t2 d)) Q.
Proof using.
  intros. unfold wp at 1. xsimpl. intros H' M1.
  unfold wp at 1. xsimpl. intros H''.
  applys hhoare_let. applys (rm M1). intros v. simpl. unfold wp.
  repeat rewrite hstar_hexists. applys hhoare_hexists; intros H'''.
  rewrite (hstar_comm H'''). rewrite hstar_assoc.
  applys hhoare_hpure; intros M2. applys hhoare_conseq M2; xsimpl.
Qed.

Lemma wp_if : forall (b : D -> bool) t1 t2 Q,
  wp (fun d => if (b d) then (t1 d) else (t2 d)) Q ==> wp (fun d => trm_if (b d) (t1 d) (t2 d)) Q.
Proof using.
  intros. repeat unfold wp. xsimpl; intros H M H'.
  applys hhoare_if. applys M.
Qed.

Lemma wp_if_case : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (fun d => trm_if b (t1 d) (t2 d)) Q.
Proof using. intros. applys himpl_trans wp_if. case_if~. Qed.

Lemma wp_ht_eq ht1 ht2 Q : 
  (forall d, indom fs d -> ht1 d = ht2 d) ->
  wp ht1 Q = wp ht2 Q.
Proof.
Admitted.

Lemma wp_hv ht Q :
  wp ht (fun hv => \exists hv', Q (hv \u_(fs) hv')) ==>
  wp ht Q.
Proof.
  rewrite /wp. xsimpl=> H' hh ?.
  apply/hhoare_hv/hhoare_conseq; eauto.
  by xsimpl.
Qed.

End htriple.

Lemma htriple_hsubst f g fs ht H Q: 
  cancel f g -> cancel g f ->
  htriple fs ht H Q = 
  htriple (fsubst fs f) (ht \o g) (\{x |-> f x} H) (fun hv => \{x |-> f x} Q (hv \o f)).
Proof.
Admitted.

Arguments htriple_hsubst _ _ {_}.

Lemma wp_union Q t fs1 fs2 : 
  disjoint fs1 fs2 ->
  wp fs1 t (fun hr1 => wp fs2 t (fun hr2 => Q (hr1 \u_(fs1) hr2))) = 
  wp (fs1 \u fs2) t Q.
Proof.
  move=> dj.
  apply/himpl_antisym.
  { rewrite {1}/wp. xsimpl=> ? M1.
    rewrite /wp; xsimpl=> ?. apply/hhoare_union=> //= ?.
    by apply wp_equiv. }
  rewrite {1}/wp. xsimpl=> P hh.
  rewrite {1}/wp. xsimpl=> H.
  rewrite /wp.
  move/hhoare_union2: (hh)=> /(_ H dj) ?.
  apply/hhoare_conseq; [eauto|xsimpl|].
  xsimpl*.
Qed. 

Lemma wp_union2 Q t fs1 fs2 : 
  disjoint fs1 fs2 ->
  wp (fs1 \u fs2) t Q ==>
  wp fs1 t (fun=> wp fs2 t Q).
Proof.
Admitted.

(* Lemma wp_union2 Q t fs1 fs2 : 
  disjoint fs1 fs2 ->
  wp (fs1 \u fs2) t Q ==>
  wp fs1 t (fun hr1 => \exists hv, wp fs2 t (fun hr2 => \[forall d, indom fs1 d -> hr2 d = hv d] \* Q (hr1 \u_(fs1) hr2))).
Proof.
  move=> dj.
  rewrite {1}/wp. xsimpl=> P hh.
  rewrite {1}/wp. xsimpl=> H.
  rewrite /wp.
  move/hhoare_union2: (hh)=> /(_ H dj) ?.
  apply/hhoare_conseq; [eauto|xsimpl|].
  move=> ?. xpull=> ?? HH; xsimpl*.
Qed. *)

Lemma wp0 ht Q : wp empty ht (fun=> Q) = Q.
Proof.
  rewrite /wp. xsimpl.
  { move=> ? /(_ \[]) /[! hhoare0]; by rew_heap. }
  move=> ?; by rewrite hhoare0.
Qed.



Notation "'funloc' p '=>' H" :=
  (fun (r:D -> val) => \exists (p : D -> loc), \[r = val_loc \o p] \* H)
  (at level 200, p ident, format "'funloc'  p  '=>'  H") : hprop_scope.

(* ################################################################# *)
(** * WP Generator *)

(** This section defines a "weakest-precondition style characteristic
     formula generator". This technology adapts the technique of
     "characteristic formulae" (originally developed in CFML 1.0)
     to produce weakest preconditions. (The formulae, their manipulation,
     and their correctness proofs are simpler in wp-style.)

    The goal of the section is to define a function [wpgen t], recursively
    over the structure of [t], such that [wpgen t Q] entails [wp t Q].
    Unlike [wp t Q], which is defined semantically, [wpgen t Q] is defined
    following the syntax of [t].

    Technically, we define [wpgen E t], where [E] is a list of bindings,
    to compute a formula that entails [wp (isubst E t)], where [isubst E t]
    denotes the iterated substitution of bindings from [E] inside [t]. *)

(* ================================================================= *)
(** ** Definition of Context as List of Bindings *)

(** In order to define a structurally recursive and relatively
    efficient characteristic formula generator, we need to introduce
    contexts, that essentially serve to apply substitutions lazily. *)

Open Scope liblist_scope.

(** A context is an association list from variables to values. *)

(* Definition ctx : Type := list (var*val).

(** [lookup x E] returns [Some v] if [x] is bound to a value [v],
    and [None] otherwise. *)

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E1 => if var_eq x y
                   then Some v
                   else lookup x E1
  end.

(** [rem x E] denotes the removal of bindings on [x] from [E]. *)

Fixpoint rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E1 =>
      let E1' := rem x E1 in
      if var_eq x y then E1' else (y,v)::E1'
  end.

(** [ctx_disjoint E1 E2] asserts that the two contexts have disjoint
    domains. *)

Definition ctx_disjoint (E1 E2:ctx) : Prop :=
  forall x v1 v2, lookup x E1 = Some v1 -> lookup x E2 = Some v2 -> False.

(** [ctx_equiv E1 E2] asserts that the two contexts bind same
    keys to same values. *)

Definition ctx_equiv (E1 E2:ctx) : Prop :=
  forall x, lookup x E1 = lookup x E2.

(** Basic properties of context operations follow. *)

Section CtxOps.

Lemma lookup_app : forall E1 E2 x,
  lookup x (E1 ++ E2) = match lookup x E1 with
                         | None => lookup x E2
                         | Some v => Some v
                         end.
Proof using.
  introv. induction E1 as [|(y,w) E1']; rew_list; simpl; intros.
  { auto. } { case_var~. }
Qed.

Lemma lookup_rem : forall x y E,
  lookup x (rem y E) = If x = y then None else lookup x E.
Proof using.
  intros. induction E as [|(z,v) E'].
  { simpl. case_var~. }
  { simpl. case_var~; simpl; case_var~. }
Qed.

Lemma rem_app : forall x E1 E2,
  rem x (E1 ++ E2) = rem x E1 ++ rem x E2.
Proof using.
  intros. induction E1 as [|(y,w) E1']; rew_list; simpl. { auto. }
  { case_var~. { rew_list. fequals. } }
Qed.

Lemma ctx_equiv_rem : forall x E1 E2,
  ctx_equiv E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv M. unfolds ctx_equiv. intros y.
  do 2 rewrite lookup_rem. case_var~.
Qed.

Lemma ctx_disjoint_rem : forall x E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_disjoint (rem x E1) (rem x E2).
Proof using.
  introv D. intros y v1 v2 K1 K2. rewrite lookup_rem in *.
  case_var~. applys* D K1 K2.
Qed.

Lemma ctx_disjoint_equiv_app : forall E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_equiv (E1 ++ E2) (E2 ++ E1).
Proof using.
  introv D. intros x. do 2 rewrite~ lookup_app.
  case_eq (lookup x E1); case_eq (lookup x E2); auto.
  { intros v2 K2 v1 K1. false* D. }
Qed.

End CtxOps. *)



(* ================================================================= *)
(** ** Multi-Substitution *)

(* ----------------------------------------------------------------- *)
(** *** Definition of Multi-Substitution *)

(** The specification of the characteristic formula generator is expressed
    using the multi-substitution function, which substitutes a list of
    bindings inside a term. *)
(* 
Fixpoint isubst (E:ctx) (t:trm) : trm :=
  match t with
  | trm_val v =>
       v
  | trm_var x =>
       match lookup x E with
       | None => t
       | Some v => v
       end
  | trm_fun x t1 =>
       trm_fun x (isubst (rem x E) t1)
  | trm_fix f x t1 =>
       trm_fix f x (isubst (rem x (rem f E)) t1)
  | trm_if t0 t1 t2 =>
       trm_if (isubst E t0) (isubst E t1) (isubst E t2)
  | trm_seq t1 t2 =>
       trm_seq (isubst E t1) (isubst E t2)
  | trm_let x t1 t2 =>
       trm_let x (isubst E t1) (isubst (rem x E) t2)
  | trm_app t1 t2 =>
       trm_app (isubst E t1) (isubst E t2)
  end.

(* ----------------------------------------------------------------- *)
(** *** Properties of Multi-Substitution *)

(** The goal of this entire section is only to establish [isubst_nil]
    and [isubst_rem], which assert:

        isubst nil t = t
    and
        isubst ((x,v)::E) t = subst x v (isubst (rem x E) t)
*)

(** The first targeted lemma. *)

Lemma isubst_nil : forall t,
  isubst nil t = t.
Proof using. intros t. induction t; simpl; fequals. Qed.

(** The next lemma relates [subst] and [isubst]. *)

Lemma subst_eq_isubst_one : forall x v t,
  subst x v t = isubst ((x,v)::nil) t.
Proof using.
  intros. induction t; simpl.
  { fequals. }
  { case_var~. }
  { fequals. case_var~. { rewrite~ isubst_nil. } }
  { fequals. case_var; try case_var; simpl; try case_var; try rewrite isubst_nil; auto. }
  { fequals*. }
  { fequals*. }
  { fequals*. case_var~. { rewrite~ isubst_nil. } }
  { fequals*. }
Qed.

(** The next lemma shows that equivalent contexts produce equal
    results for [isubst]. *)

Lemma isubst_ctx_equiv : forall t E1 E2,
  ctx_equiv E1 E2 ->
  isubst E1 t = isubst E2 t.
Proof using.
  hint ctx_equiv_rem.
  intros t. induction t; introv EQ; simpl; fequals~.
  { rewrite~ EQ. }
Qed.

(** The next lemma asserts that [isubst] distribute over concatenation. *)

Lemma isubst_app : forall t E1 E2,
  isubst (E1 ++ E2) t = isubst E2 (isubst E1 t).
Proof using.
  hint ctx_disjoint_rem.
  intros t. induction t; simpl; intros.
  { fequals. }
  { rename v into x. rewrite~ lookup_app.
    case_eq (lookup x E1); introv K1; case_eq (lookup x E2); introv K2; auto.
    { simpl. rewrite~ K2. }
    { simpl. rewrite~ K2. } }
  { fequals. rewrite* rem_app. }
  { fequals. do 2 rewrite* rem_app. }
  { fequals*. }
  { fequals*. }
  { fequals*. { rewrite* rem_app. } }
  { fequals*. }
Qed.

(** The next lemma asserts that the concatenation order is irrelevant
    in a substitution if the contexts have disjoint domains. *)

Lemma isubst_app_swap : forall t E1 E2,
  ctx_disjoint E1 E2 ->
  isubst (E1 ++ E2) t = isubst (E2 ++ E1) t.
Proof using.
  introv D. applys isubst_ctx_equiv. applys~ ctx_disjoint_equiv_app.
Qed.

(** We are ready to derive the second targeted property of [isubst]. *)

Lemma isubst_rem : forall x v E t,
  isubst ((x, v)::E) t = subst x v (isubst (rem x E) t).
Proof using.
  intros. rewrite subst_eq_isubst_one. rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. rewrite lookup_rem. case_var~. }
  { intros y v1 v2 K1 K2. simpls. rewrite lookup_rem in K1. case_var. }
Qed.

(** A variant useful for [trm_fix] is proved next. *)

Lemma isubst_rem_2 : forall f x vf vx E t,
  isubst ((f,vf)::(x,vx)::E) t = subst x vx (subst f vf (isubst (rem x (rem f E)) t)).
Proof using.
  intros. do 2 rewrite subst_eq_isubst_one. do 2 rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. do 2 rewrite lookup_rem. case_var~. }
  { intros y v1 v2 K1 K2. rew_listx in *. simpls. do 2 rewrite lookup_rem in K1. case_var. }
  
  Qed. *)
(* ================================================================= *)
(** ** Definition of [wpgen] *)

(** The definition of [wpgen E t] comes next. It depends on a predicate
    called [mkstruct] for handling structural rules, and on one auxiliary
    definition for each term rule. *)

(* ----------------------------------------------------------------- *)
(** *** Definition of [mkstruct] *)

(** Let [formula] denote the type of [wp t] and [wpgen t]. *)

Section WPgen.

Context (fs : fset D).

Definition formula := ((D -> val) -> hhprop) -> hhprop.

Implicit Type F : formula.

(** [mkstruct F] transforms a formula [F] into one that satisfies structural
    rules of Separation Logic. This predicate transformer enables integrating
    support for the frame rule (and other structural rules), in characteristic
    formulae. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* Q).

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. xsimpl. Qed.

Arguments mkstruct_ramified : clear implicits.

Lemma mkstruct_erase : forall Q F,
  F Q ==> mkstruct F Q.
Proof using. unfolds mkstruct. xsimpl. Qed.

Arguments mkstruct_erase : clear implicits.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfolds mkstruct. xpull. intros Q. xsimpl Q. xchanges WQ.
Qed.

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using.
  intros. unfold mkstruct. xpull. intros Q'. xsimpl Q'.
Qed.

Lemma mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.
Proof using.
  introv WF. unfolds mkstruct. xpull. intros Q'. xchange WF. xsimpl Q'.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Definition of Auxiliary Definition for [wpgen] *)

(** we state auxiliary definitions for [wpgen], one per term construct.
    For simplicity, we here assume the term [t] to be in A-normal form.
    If it is not, the formula generated will be incomplete, that is,
    useless to prove htriples about the term [t]. Note that the actual
    generator in CFML2 does support terms that are not in A-normal form. *)

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_val (v:D->val) : formula := fun Q =>
  Q v.

Definition wpgen_fun (Fof:(D->val)->formula) : formula := fun Q =>
  \forall (vf : D -> val), \[forall (vx : D -> val) Q', Fof vx Q' ==> wp fs (fun d => trm_app (vf d) (vx d)) Q'] \-* Q vf.

Definition wpgen_fix (Fof:(D->val)->(D->val)->formula) : formula := fun Q =>
  \forall hvf, \[forall hvx Q', Fof hvf hvx Q' ==> wp fs (fun d => trm_app (hvf d) (hvx d)) Q'] \-* Q hvf.

(* Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end. *)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

Definition wpgen_let (F1:formula) (F2of:(D->val)->formula) : formula := fun Q =>
  F1 (fun hv => F2of hv Q).

Definition wpgen_if (t:D->trm) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[t = fun=> trm_val (val_bool b)] \* (if b then F1 Q else F2 Q).

Definition wpgen_if_trm (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => mkstruct (wpgen_if v F1 F2)).

(* ----------------------------------------------------------------- *)
(** *** Recursive Definition of [wpgen] *)

(** [wpgen E t] is structurally recursive on [t]. Note that this function does
    not recurse through values. Note also that the context [E] gets extended
    when traversing bindings, in the let-binding and the function cases. *)

Definition is_val (t : D -> trm) :=
  exists v, t = fun d => trm_val (v d).

Definition get_val (t : D -> trm) :=
  fun d => match t d with trm_val v => v | _ => arbitrary end.

Lemma is_val_val hv : is_val (fun d => trm_val (hv d)).
Proof. exists __; eauto. Qed.

Definition is_fun (t : D -> trm) :=
  exists x t, t = fun d => trm_fun (x d) (t d).

Definition is_fix (t : D -> trm) :=
  exists f x t, t = fun d => trm_fix (f d) (x d) (t d).

Definition is_if (t : D -> trm) :=
  exists t0 t1 t2, t = fun d => trm_if (t0 d) (t1 d) (t2 d).

Definition is_seq (t : D -> trm) :=
  exists t1 t2, t = fun d => trm_seq (t1 d) (t2 d).

Definition is_let (t : D -> trm) :=
  exists x t1 t2, t = fun d => trm_let (x d) (t1 d) (t2 d).

Definition get_var (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_fun x _ | trm_let x _ _ | trm_fix _ x _ => x
    | _ => arbitrary
    end.

Definition get_fun (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_fun _ t | trm_let _ _ t | trm_fix _ _ t => t
    | _ => trm_val 0
    end.

Instance Inhab_trm : Inhab trm.
split.
by exists (trm_val 0).
Qed.

Definition get_f (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_fix f _ _ => f
    | _ => arbitrary
    end.

Definition get_cond (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_if f _ _ => f
    | _ => arbitrary
    end.

Definition get_then (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_if _ f _ => f
    | _ => arbitrary
    end.

Definition get_else (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_if _ _ f => f
    | _ => arbitrary
    end.

Definition get_seq1 (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_seq f _ => f
    | _ => arbitrary
    end.

Definition get_seq2 (t : D -> trm) :=
  fun d => 
    match t d with
    | trm_seq _ f => f
    | _ => arbitrary
    end.

Definition get_letvar (t : D -> trm) :=
  fun d => 
    match t d with 
    | trm_let _ f _ => f 
    | _ => arbitrary
    end.

Definition wpgen (t : D -> trm) : formula :=
  mkstruct (
         If is_val t then wpgen_val (get_val t)
    else If is_fun t then wpgen_fun (fun hv => wp fs (fun d => subst (get_var t d) (hv d) (get_fun t d)))
    else If is_fix t then wpgen_fix (fun hvf hv => wp fs (fun d => subst (get_var t d) (hv d) (subst (get_f t d) (hvf d) (get_fun t d))))
    else If is_if  t then wpgen_if  (get_cond t) (wp fs (fun d => get_then t d)) (wp fs (fun d => get_else t d))
    else If is_seq t then wpgen_seq (wp fs (fun d => get_seq1 t d)) (wp fs (fun d => get_seq2 t d))
    else If is_let t then wpgen_let (wp fs (fun d => get_letvar t d)) (fun hv => wp fs (fun d => subst (get_var t d) (hv d) (get_fun t d)))
    else wp fs t
  ).

Lemma wpgenE :
  (forall hv      , wpgen (fun d => trm_val (hv d))        
    = mkstruct (wpgen_val hv))                                                                               *
  (forall x t1    , wpgen (fun d => trm_fun (x d) (t1 d))  
    = mkstruct (wpgen_fun (fun v => wp fs (fun d => subst (x d) (v d) (t1 d)))))                             *
  (forall t1 t2   , wpgen (fun d => trm_seq (t1 d) (t2 d)) 
    = mkstruct (wpgen_seq (wp fs t1) (wp fs t2))) *
  (forall x t1 t2 , wpgen (fun d => trm_let (x d) (t1 d) (t2 d)) 
    = mkstruct (wpgen_let (wp fs t1) (fun v => wp fs (fun d => subst (x d) (v d) (t2 d)))))                  *
  (forall t1 t2   , wpgen (fun d => trm_app (t1 d) (t2 d)) 
    = mkstruct (wp fs (fun d => trm_app (t1 d) (t2 d))))                                                     *
  (forall f x t1  , wpgen (fun d => trm_fix (f d) (x d) (t1 d))
    = mkstruct (wpgen_fix (fun hvf hv => wp fs (fun d => subst (x d) (hv d) (subst (f d) (hvf d) (t1 d)))))) *
  (forall t0 t1 t2, wpgen (fun d => trm_if (t0 d) (t1 d) (t2 d))
    = mkstruct (wpgen_if t0 (wp fs t1) (wp fs t2))).
Proof.
Admitted.

(* Definition wpgen (t:trm) : formula :=
  mkstruct match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_fail
  | trm_fun x t1 => wpgen_fun (fun v => wp (subst x v t1))
  | trm_fix f x t1 => wpgen_fix (fun vf v => wp (subst x v (subst f vf t1)))
  | trm_if t0 t1 t2 => wpgen_if t0 (wp t1) (wp t2)
  | trm_seq t1 t2 => wpgen_seq (wp t1) (wp t2)
  | trm_let x t1 t2 => wpgen_let (wp t1) (fun v => wp (subst x v t2))
  | trm_app t1 t2 => wp t
  end. *)

(* ----------------------------------------------------------------- *)
(** *** Soundness of [wpgen] *)

(** [formula_sound t F] asserts that, for any [Q], the Separation Logic
    judgment [htriple (fun d => F Q) t Q] is valid. In other words, it states that
    [F] is a stronger formula than [wp t].

    The soundness theorem that we are ultimately interested in asserts that
    [formula_sound (isubst E t) (wpgen E t)] holds for any [E] and [t]. *)

Definition formula_sound (t:D -> trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp fs t Q.

Lemma wp_sound : forall t,
  formula_sound t (wp fs t).
Proof using. intros. intros Q. applys himpl_refl. Qed.

(** One soundness lemma for [mkstruct]. *)

Lemma mkstruct_wp : forall t,
  mkstruct (wp fs t) = (wp fs t).
Proof using.
  intros. applys fun_ext_1. intros Q. applys himpl_antisym.
  { unfold mkstruct. xpull. intros Q'. applys wp_ramified. }
  { applys mkstruct_erase. }
Qed.

Lemma mkstruct_sound : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. unfolds formula_sound. intros Q'.
  rewrite <- mkstruct_wp. applys* mkstruct_monotone M.
Qed.

(** One soundness lemma for each term construct. *)

Lemma wpgen_fail_sound : forall t,
  formula_sound t wpgen_fail.
Proof using. intros. intros Q. unfold wpgen_fail. xpull. Qed.

Lemma wpgen_val_sound : forall v,
  formula_sound (fun d => trm_val (v d)) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.

Lemma wpgen_fun_sound : forall x t1 Fof,
  (forall hvx, formula_sound (fun d => subst (x d) (hvx d) (t1 d)) (Fof hvx)) ->
  formula_sound (fun d => trm_fun (x d) (t1 d)) (wpgen_fun Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fun. applys himpl_hforall_l (fun d => val_fun (x d) (t1 d)).
  xchange hwand_hpure_l.
  { intros. applys himpl_trans_r. { applys* wp_app_fun. } { applys* M. } }
  { applys wp_fun. }
Qed.

Lemma wpgen_fix_sound : forall f x t1 Fof,
  (forall hvf hvx, formula_sound (fun d => subst (x d) (hvx d) (subst (f d) (hvf d) (t1 d))) (Fof hvf hvx)) ->
  formula_sound (fun d => trm_fix (f d) (x d) (t1 d)) (wpgen_fix Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fix. applys himpl_hforall_l (fun d => val_fix (f d) (x d) (t1 d)).
  xchange hwand_hpure_l.
  { intros. applys himpl_trans_r. { applys* wp_app_fix. } { applys* M. } }
  { applys wp_fix. }
Qed.

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (fun d => trm_seq (t1 d) (t2 d)) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_seq. applys himpl_trans wp_seq.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound t1 F1 ->
  (forall hv, formula_sound (fun d => subst (x d) (hv d) (t2 d)) (F2of hv)) ->
  formula_sound (fun d => trm_let (x d) (t1 d) (t2 d)) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_let. applys himpl_trans wp_let.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_if_sound : forall F1 F2 t0 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (fun d => trm_if (t0 d) (t1 d) (t2 d)) (wpgen_if t0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. xpull. intros b ->.
  applys himpl_trans wp_if. case_if. { applys S1. } { applys S2. }
Qed.

(** The main inductive proof for the soundness theorem. *)

Lemma wpgen_sound : forall t,
  formula_sound t (wpgen t).
Proof using.
Admitted.

Lemma himpl_wpgen_wp : forall t Q,
  wpgen t Q ==> wp fs t Q.
Proof using.
  introv M. lets N: (@wpgen_sound t). applys* N.
Qed.

(** The final theorem for closed terms. *)

Lemma htriple_of_wpgen : forall t H Q,
  H ==> wpgen t Q ->
  htriple fs t H Q.
Proof using.
  introv M. rewrite <- wp_equiv. xchange M. applys himpl_wpgen_wp.
Qed.

Lemma wp_of_wpgen : forall t H Q,
  H ==> wpgen t Q ->
  H ==> wp fs t Q.
Proof using.
  introv M. rewrite wp_equiv. applys* htriple_of_wpgen.
Qed.


(* ################################################################# *)
(** * Practical Proofs *)

(** This last section shows the techniques involved in setting up the lemmas
    and tactics required to carry out verification in practice, through
    concise proof scripts. *)

(* ================================================================= *)
(** ** Lemmas for Tactics to Manipulate [wpgen] Formulae *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_erase. Qed.

Lemma xval_lemma : forall v H Q,
  H ==> Q v ->
  H ==> wpgen_val v Q.
Proof using. introv M. applys M. Qed.

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. xchange M. Qed.

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. xchange M. Qed.

Lemma xif_lemma : forall b H F1 F2 Q,
  (b = true -> H ==> F1 Q) ->
  (b = false -> H ==> F2 Q) ->
  H ==> (wpgen_if (fun=>b) F1 F2) Q.
Proof using. introv M1 M2. unfold wpgen_if. xsimpl* b. case_if*. Qed.

Lemma xapp_lemma' : forall t t' Q1 H1 H Q,
  (forall d, indom fs d -> t' d = t d) ->
  htriple fs t' H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp fs t Q.
Proof using.
  introv tE M W. rewrite <- wp_equiv in M. xchange W. xchange M.
  rewrite (wp_ht_eq _ t)=> //.
  applys wp_ramified_frame.
Qed.

Lemma xapp_lemma : forall t Q1 H1 H Q,
  htriple fs t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp fs t Q.
Proof using.
  introv M W. rewrite <- wp_equiv in M. xchange W. xchange M.
  applys wp_ramified_frame.
Qed.

Lemma xfun_spec_lemma : forall (S:(D -> val)->Prop) H Q Fof,
  (forall (hvf : D -> val),
    (forall (hvx : D -> val) H' Q', (H' ==> Fof hvx Q') -> 
      htriple fs (fun d => trm_app (hvf d) (hvx d)) H' Q') ->
        S hvf) ->
  (forall hvf, S hvf -> (H ==> Q hvf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M1 M2. unfold wpgen_fun. xsimpl. intros vf N.
  applys M2. applys M1. introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Lemma xfun_nospec_lemma : forall H Q Fof,
  (forall (hvf : D -> val),
     (forall (hvx : D -> val)  H' Q', (H' ==> Fof hvx Q') -> 
        htriple fs (fun d => trm_app (hvf d) (hvx d)) H' Q') ->
     (H ==> Q hvf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Lemma xwp_lemma_fun : forall hv1 (hv2 : D -> val) x t H Q,
  (hv1 = fun d => val_fun (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (t d)) Q ->
  htriple fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof using.
  introv M1 M2. rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (fun d => subst (x d) (hv2 d) (t d)) Q).
  by applys* wp_app_fun; rewrite M1.
Qed.

Lemma xwp_lemma_wp_fun : forall hv1 (hv2 : D -> val) x t H Q,
  (hv1 = fun d => val_fun (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (t d)) Q ->
  H ==> wp fs (fun d => trm_app (hv1 d) (hv2 d)) Q.
Proof using.
  introv M1 M2. xchange M2.
  xchange (>> wpgen_sound (fun d => subst (x d) (hv2 d) (t d)) Q).
  by applys* wp_app_fun; rewrite M1.
Qed.

Lemma xwp_lemma_fix : forall hv1 (hv2 : D -> val) f x t H Q,
  (hv1 = fun d => val_fix (f d) (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (t d))) Q ->
  htriple fs (fun d => trm_app (hv1 d) (hv2 d)) H Q.
Proof using.
  introv M1 M2. rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (t d))) Q).
  applys* wp_app_fix. by rewrite M1.
Qed.

Lemma xwp_lemma_wp_fix : forall hv1 (hv2 : D -> val) f x t H Q,
  (hv1 = fun d => val_fix (f d) (x d) (t d)) ->
  H ==> wpgen (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (t d))) Q ->
  H ==> wp fs (fun d => trm_app (hv1 d) (hv2 d)) Q.
Proof using.
  introv M1 M2. xchange M2.
  xchange (>> wpgen_sound (fun d => subst (x d) (hv2 d) (subst (f d) (hv1 d) (t d))) Q).
  applys* wp_app_fix. by rewrite M1.
Qed.

Lemma xhtriple_lemma : forall t H (Q:(D->val)->hhprop),
  H ==> mkstruct (wp fs t) Q ->
  htriple fs t H Q.
Proof using.
  introv M. rewrite <- wp_equiv. xchange M. unfold mkstruct.
  xpull. intros Q'. applys wp_ramified_frame.
Qed.

End WPgen.

(* ================================================================= *)
(** ** Tactics to Manipulate [wpgen] Formulae *)

(** The tactic are presented in [WPgen]. *)

(** Database of hints for [xapp]. *)

Hint Resolve htriple_get htriple_set htriple_ref htriple_free : htriple.

Hint Resolve htriple_add htriple_div htriple_neg htriple_opp htriple_eq
   htriple_neq htriple_sub htriple_mul htriple_mod htriple_le htriple_lt
   htriple_ge htriple_gt htriple_ptr_add htriple_ptr_add_nat : htriple.

(** [xstruct] removes the leading [mkstruct]. *)

Tactic Notation "xstruct" :=
  applys xstruct_lemma.

(** [xstruct_if_needed] removes the leading [mkstruct] if there is one. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xval" :=
  xstruct_if_needed; applys xval_lemma.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys xseq_lemma.

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q =>
  match F with
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xif" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xif_lemma; rew_bool_eq.

(** [xapp_try_clear_unit_result] implements some post-processing for
    cleaning up unused variables. *)

Tactic Notation "xapp_try_clear_unit_result" :=
  try match goal with |- (_ -> val) -> _ => intros _ end.

Tactic Notation "xhtriple" :=
  intros; applys xhtriple_lemma.

Tactic Notation "xhtriple_if_needed" :=
  try match goal with |- htriple ?t ?H ?Q => applys xhtriple_lemma end.

(** [xapp_simpl] performs the final step of the tactic [xapp]. *)

Lemma xapp_simpl_lemma : forall (F : formula) H Q,
  H ==> F Q ->
  H ==> F Q \* (Q \--* protect Q).
Proof using. introv M. xchange M. unfold protect. xsimpl. Qed.

Tactic Notation "xapp_simpl" :=
  first [ applys xapp_simpl_lemma; do 2? xsimpl (* handles specification coming from [xfun] *)
        | (do 2? xsimpl); unfold protect; xapp_try_clear_unit_result ].

Tactic Notation "xapp_pre" :=
  xhtriple_if_needed; xseq_xlet_if_needed; xstruct_if_needed.

(** [xapp_nosubst E] implements the heart of [xapp E]. If the argument [E] was
    always a htriple, it would suffice to run [applys xapp_lemma E; xapp_simpl].
    Yet, [E] might be an specification involving quantifiers. These quantifiers
    need to be first instantiated. This instantiation is achieved by means of
    the tactic [forwards_nounfold_then] offered by the TLC library. *)

Tactic Notation "xapp_nosubst" constr(E) :=
  xapp_pre;
  forwards_nounfold_then E ltac:(fun K => applys xapp_lemma' K=>//; xapp_simpl).

(** [xapp_apply_spec] implements the heart of [xapp], when called without
    argument. If finds out the specification htriple, either in the hint data
    base named [htriple], or in the context by looking for an induction
    hypothesis. Disclaimer: as explained in [WPgen], the simple
    implementation of [xapp_apply_spec] which we use here does not apply when
    the specification includes premises that cannot be solved by [eauto];
    it such cases, the tactic [xapp E] must be called, providing the
    specification [E] explicitly. This limitation is overcome using more
    involved [Hint Extern] tricks in CFML 2.0. *)

Tactic Notation "xapp_apply_spec" :=
  first [ first [solve [ eauto with lhtriple ]| solve [ eauto with htriple ]]
        | match goal with H: _ |- _ => eapply H end ].

(** [xapp_nosubst_for_records] is place holder for implementing [xapp] on
    records. It is implemented further on. *)

Ltac xapp_nosubst_for_records tt :=
 fail.

(** [xapp] first calls [xhtriple] if the goal is [htriple t H Q] instead
    of [H ==> wp t Q]. *)

Tactic Notation "xapp_nosubst" :=
  xapp_pre;
  first [ applys xapp_lemma; [ xapp_apply_spec | xapp_simpl ]
        | xapp_nosubst_for_records tt ].

(** [xapp_try_subst] checks if the goal is of the form:
    - either [forall (r:val), (r = ...) -> ...]
    - or [forall (r:val), forall x, (r = ...) -> ...]

    in which case it substitutes [r] away. *)

Tactic Notation "xapp_try_subst" :=
  try match goal with
  | |- forall (r:D->val), (r = _) -> _ => intros ? ->
  | |- forall (r:D->val), forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.

Tactic Notation "xapp" constr(E) :=
  xapp_nosubst E; xapp_try_subst.

Tactic Notation "xapp" :=
  xapp_nosubst; xapp_try_subst.

Tactic Notation "xapp_debug" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xapp_lemma.

(** [xapp] is essentially equivalent to
    [ xapp_debug; [ xapp_apply_spec | xapp_simpl ] ]. *)

Tactic Notation "xfun" constr(S) :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_spec_lemma S.

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_nospec_lemma.

(** [xvars] may be called for unfolding "program variables as definitions",
    which take the form [Vars.x], and revealing the underlying string. *)

Tactic Notation "xvars" :=
  DefinitionsForVariables.libsepvar_unfold.

(** [xwp_simpl] is a specialized version of [simpl] to be used for
    getting the function [wp] to compute properly. *)

Ltac xwp_simpl :=
  xvars;
  cbn beta delta [
     var_eq subst
     string_dec string_rec string_rect
     sumbool_rec sumbool_rect
     Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
     Bool.bool_dec bool_rec bool_rect ] iota zeta;
  simpl; rewrite ?wpgenE; try (unfold subst; simpl).

Tactic Notation "xwp" :=
  intros;
  first [ applys xwp_lemma_fun; [ reflexivity | ]
        | applys xwp_lemma_fix; [ reflexivity | ] 
        | applys wp_of_wpgen];
  xwp_simpl.

(* ================================================================= *)
(** ** Notations for Triples and [wpgen] *)

Declare Scope wp_scope.

(** Notation for printing proof obligations arising from [wpgen]. *)

Notation "'PRE' H 'CODE' F 'POST' Q" :=
  (H ==> (mkstruct F) Q)
  (at level 8, H at level 0, F, Q at level 0,
   format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

Notation "` F" :=
  (mkstruct F)
  (at level 10,
   format "` F") : wp_scope.

(** Custom grammar for the display of characteristic formulae. *)

Declare Custom Entry wp.

Notation "<[ e ]>" :=
  e
  (at level 0, e custom wp at level 99) : wp_scope.

Notation "` F" :=
  (mkstruct F)
  (in custom wp at level 10,
   format "` F") : wp_scope.

Notation "( x )" :=
  x
  (in custom wp,
   x at level 99) : wp_scope.

Notation "{ x }" :=
  x
  (in custom wp at level 0,
   x constr,
   only parsing) : wp_scope.

Notation "x" :=
  x
  (in custom wp at level 0,
   x constr at level 0) : wp_scope.

Notation "'Fail'" :=
  ((wpgen_fail))
  (in custom wp at level 69) : wp_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (in custom wp at level 69) : wp_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (in custom wp at level 69,
   x name, (* NOTE: For compilation with Coq 8.12, replace "name" with "ident",
               here and in the next 3 occurrences in the rest of the section. *)
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
  format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'WP' [ d 'in' fs  '=>' t ] '{' v ',' Q '}'" := 
    (wp fs (fun d => t) (fun v => Q)) (at level 30, d name, v name,
  format "'[' 'WP'  [  d '['  'in'  ']' fs   '=>' '/    ' '['  t ']'  ] '/' '['   '{'  v ','  Q  '}' ']' ']' ") : wp_scope.

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (in custom wp at level 68,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

Notation "'App' '[' d 'in' fs ']' f v1" :=
  ((wp fs (fun d => trm_app (f d) (v1 d))))
  (in custom wp at level 68, d name, f, fs, v1 at level 0) : wp_scope.

Notation "'App' '[' d 'in' fs ']' f v1 v2" :=
  ((wp fs (fun d => trm_app (trm_app (f d) (v1 d)) (v2 d))))
  (in custom wp at level 68, d name, f, fs, v1, v2 at level 0) : wp_scope.

Notation "'If_' v 'Then' F1 'Else' F2" :=
  ((wpgen_if v F1 F2))
  (in custom wp at level 69,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   left associativity,
   format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Fun' x '=>' F1" :=
  ((wpgen_fun (fun x => F1)))
  (in custom wp at level 69,
   x name,
   F1 custom wp at level 99,
   right associativity,
  format "'[v' '[' 'Fun'  x  '=>'  F1  ']' ']'") : wp_scope.

Notation "'Fix' f x '=>' F1" :=
  ((wpgen_fix (fun f x => F1)))
  (in custom wp at level 69,
   f name, x name,
   F1 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'Fix'  f  x  '=>'  F1  ']' ']'") : wp_scope.

(* ================================================================= *)
(** ** Notation for Concrete Terms *)

(** The custom grammar for [trm] is defined in [LibSepVar]. *)

Declare Scope val_scope.

(** Terms *)

Notation "<{ e }>" :=
  e
  (at level 0, e custom trm at level 99) : trm_scope.

Notation "( x )" :=
  x
  (in custom trm, x at level 99) : trm_scope.

Notation "'begin' e 'end'" :=
  e
  (in custom trm, e custom trm at level 99, only parsing) : trm_scope.

Notation "{ x }" :=
  x
  (in custom trm, x constr) : trm_scope.

Notation "x" := x
  (in custom trm at level 0,
   x constr at level 0) : trm_scope.

Notation "t1 t2" := (trm_app t1 t2)
  (in custom trm at level 30,
   left associativity,
   only parsing) : trm_scope.

Notation "'if' t0 'then' t1 'else' t2" :=
  (trm_if t0 t1 t2)
  (in custom trm at level 69,
   t0 custom trm at level 99,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   left associativity,
   format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'else' '/' '['   t2 ']' ']'") : trm_scope.

Notation "'if' t0 'then' t1 'end'" :=
  (trm_if t0 t1 (trm_val val_unit))
  (in custom trm at level 69,
   t0 custom trm at level 99, (* at level 0 ? *)
   t1 custom trm at level 99,
   left associativity,
   format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'end' ']'") : trm_scope.

Notation "t1 ';' t2" :=
  (trm_seq t1 t2)
  (in custom trm at level 68,
   t2 custom trm at level 99,
   right associativity,
   format "'[v' '[' t1 ']' ';' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'let' x '=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (in custom trm at level 69,
   x at level 0,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   right associativity,
   format "'[v' '[' 'let'  x  '='  t1  'in' ']' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'fix' f x1 '=>' t" :=
  (val_fix f x1 t)
  (in custom trm at level 69,
   f, x1 at level 0,
   t custom trm at level 99,
   format "'fix'  f  x1  '=>'  t") : val_scope.

Notation "'fix_' f x1 '=>' t" :=
  (trm_fix f x1 t)
  (in custom trm at level 69,
   f, x1 at level 0,
   t custom trm at level 99,
   format "'fix_'  f  x1  '=>'  t") : trm_scope.

Notation "'fun' x1 '=>' t" :=
  (val_fun x1 t)
  (in custom trm at level 69,
   x1 at level 0,
   t custom trm at level 99,
   format "'fun'  x1  '=>'  t") : val_scope.

Notation "'fun_' x1 '=>' t" :=
  (trm_fun x1 t)
  (in custom trm at level 69,
   x1 at level 0,
   t custom trm at level 99,
   format "'fun_'  x1  '=>'  t") : trm_scope.

Notation "()" :=
  (trm_val val_unit)
  (in custom trm at level 0) : trm_scope.

Notation "()" :=
  (val_unit)
  (at level 0) : val_scope.

(** Notation for Primitive Operations. *)

Notation "'ref'" :=
  (trm_val (val_prim val_ref))
  (in custom trm at level 0) : trm_scope.

Notation "'free'" :=
  (trm_val (val_prim val_free))
  (in custom trm at level 0) : trm_scope.

Notation "'not'" :=
  (trm_val (val_prim val_neg))
  (in custom trm at level 0) : trm_scope.

Notation "! t" :=
  (val_get t)
  (in custom trm at level 67,
   t custom trm at level 99) : trm_scope.

Notation "t1 := t2" :=
  (val_set t1 t2)
  (in custom trm at level 67) : trm_scope.

Notation "t1 + t2" :=
  (val_add t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "'- t" :=
  (val_opp t)
  (in custom trm at level 57,
   t custom trm at level 99) : trm_scope.

Notation "t1 - t2" :=
  (val_sub t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 * t2" :=
  (val_mul t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 / t2" :=
  (val_div t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 'mod' t2" :=
  (val_mod t1 t2)
  (in custom trm at level 57) : trm_scope.

Notation "t1 = t2" :=
  (val_eq t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 <> t2" :=
  (val_neq t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 <= t2" :=
  (val_le t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 < t2" :=
  (val_lt t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 >= t2" :=
  (val_ge t1 t2)
  (in custom trm at level 60) : trm_scope.

Notation "t1 > t2" :=
  (val_gt t1 t2)
  (in custom trm at level 60) : trm_scope.

(* ================================================================= *)
(** ** Scopes, Coercions and Notations for Concrete Programs *)

Module ProgramSyntax.

Export NotationForVariables.

Module Vars := DefinitionsForVariables.

Close Scope fmap_scope.
Open Scope string_scope.
Open Scope val_scope.
Open Scope trm_scope.
Open Scope wp_scope.
Coercion string_to_var (x:string) : var := x.

End ProgramSyntax.


(* ================================================================= *)
(** ** Treatment of Functions of 2 and 3 Arguments *)

(** As explained in chapter [Struct], there are different ways to
    support functions of several arguments: curried functions, n-ary
    functions, or functions expecting a tuple as argument.

    For simplicity, we here follow the approach based on curried
    function, specialized for arity 2 and 3. It is possible to state
    arity-generic definitions and lemmas, but the definitions become
    much more technical.

    From an engineering point of view, it is easier and more efficient
    to follow the approach using n-ary functions, as the CFML tool does. *)

(* ----------------------------------------------------------------- *)
(** *** Syntax for Functions of 2 or 3 Arguments. *)

Notation "'fun' x1 x2 '=>' t" :=
  (val_fun x1 (trm_fun x2 t))
  (in custom trm at level 69,
   x1, x2 at level 0,
   format "'fun'  x1  x2  '=>'  t") : val_scope.

Notation "'fix' f x1 x2 '=>' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (in custom trm at level 69,
   f, x1, x2 at level 0,
   format "'fix'  f  x1  x2  '=>'  t") : val_scope.

Notation "'fun_' x1 x2 '=>' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (in custom trm at level 69,
   x1, x2 at level 0,
   format "'fun_'  x1  x2  '=>'  t") : trm_scope.

Notation "'fix_' f x1 x2 '=>' t" :=
  (trm_fix f x1 (trm_fun x2 t))
  (in custom trm at level 69,
   f, x1, x2 at level 0,
   format "'fix_'  f  x1  x2  '=>'  t") : trm_scope.

Notation "'fun' x1 x2 x3 '=>' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
   x1, x2, x3 at level 0,
   format "'fun'  x1  x2  x3  '=>'  t") : val_scope.

Notation "'fix' f x1 x2 x3 '=>' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
   f, x1, x2, x3 at level 0,
   format "'fix'  f  x1  x2  x3  '=>'  t") : val_scope.

Notation "'fun_' x1 x2 x3 '=>' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
   x1, x2, x3 at level 0, format "'fun_'  x1  x2  x3  '=>'  t") : trm_scope.

Notation "'fix_' f x1 x2 x3 '=>' t" :=
  (trm_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (in custom trm at level 69,
   f, x1, x2, x3 at level 0, format "'fix_'  f  x1  x2  x3  '=>'  t") : trm_scope.

(* ----------------------------------------------------------------- *)
(** *** Evaluation Rules for Applications to 2 or 3 Arguments. *)

(** [eval_like] judgment for applications to several arguments. *)

(* Lemma eval_like_app_fun2 : forall v0 v1 v2 x1 x2 t1,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  x1 <> x2 ->
  eval_like (subst x2 v2 (subst x1 v1 t1)) (v0 v1 v2).
Proof using.
  introv E N. introv R. applys* eval_app_args.
  { applys eval_app_fun E. simpl. rewrite var_eq_spec. case_if. applys eval_fun. }
  { applys* eval_val. }
  { applys* eval_app_fun. }
Qed. *)

Lemma eval_like_app_fix2 fs : forall v0 v1 v2 f x1 x2 t1,
  (v0 = fun d => val_fix (f d) (x1 d) (trm_fun (x2 d) (t1 d))) ->
  (forall d, x1 d <> x2 d /\ f d <> x2 d) ->
  eval_like fs (fun d => subst (f d) (v0 d) (subst (x1 d) (v1 d) (subst (x2 d) (v2 d) (t1 d)))) (fun d => (v0 d) (v1 d) (v2 d)).
Proof using.
Admitted.

(* Lemma eval_like_app_fun3 : forall v0 v1 v2 v3 x1 x2 x3 t1,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2  /\ x1 <> x3 /\ x2 <> x3) ->
  eval_like (subst x3 v3 (subst x2 v2 (subst x1 v1 t1))) (v0 v1 v2 v3).
Proof using.
  introv E (N1&N2&N3). introv R. applys* eval_app_args.
  { applys* eval_like_app_fun2 E. simpl. do 2 (rewrite var_eq_spec; case_if). applys eval_fun. }
  { applys eval_val. }
  { applys* eval_app_fun. }
Qed.

Lemma eval_like_app_fix3 : forall v0 v1 v2 v3 f x1 x2 x3 t1,
  v0 = val_fix f x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2 /\ f <> x2 /\ f <> x3 /\ x1 <> x3 /\ x2 <> x3) ->
  eval_like (subst x3 v3 (subst x2 v2 (subst x1 v1 (subst f v0 t1)))) (v0 v1 v2 v3).
Proof using.
  introv E (N1&N2&N3&N4&N5). introv R. applys* eval_app_args.
  { applys* eval_like_app_fix2 E. simpl. do 3 (rewrite var_eq_spec; case_if). applys eval_fun. }
  { applys eval_val. }
  { applys* eval_app_fun. }
Qed. *)

(* ----------------------------------------------------------------- *)
(** *** Reasoning Rules for Applications to 2 or 3 Arguments *)

(** Weakest preconditions for applications to several arguments. *)

(* Lemma wp_app_fun2 fs : forall x1 x2 v0 v1 v2 t1 Q,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t1 d))) ->
  (forall d, x1 d <> x2 d) ->
  wp fs (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t1 d))) Q ==> wp fs (fun d => trm_app (v0 d) (v1 d) (v2 d)) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fun2. Qed.

Lemma wp_app_fix2 fs : forall f x1 x2 v0 v1 v2 t1 Q,
  (v0 = fun d => val_fix (f d) (x1 d) (trm_fun (x2 d) (t1 d))) ->
  (forall d, x1 d <> x2 d /\ f d <> x2 d) ->
  wp fs (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (subst (f d) (v0 d) (t1 d)))) Q ==> wp fs (fun d => trm_app (v0 d) (v1 d) (v2 d)) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fix2. Qed. *)

(* Lemma wp_app_fun3 : forall x1 x2 x3 v0 v1 v2 v3 t1 Q,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2 /\ x1 <> x3 /\ x2 <> x3) ->
  wp (subst x3 v3 (subst x2 v2 (subst x1 v1 t1))) Q ==> wp (trm_app v0 v1 v2 v3) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fun3. Qed.

Lemma wp_app_fix3 : forall f x1 x2 x3 v0 v1 v2 v3 t1 Q,
  v0 = val_fix f x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2 /\ f <> x2 /\ f <> x3 /\ x1 <> x3 /\ x2 <> x3) ->
  wp (subst x3 v3 (subst x2 v2 (subst x1 v1 (subst f v0 t1)))) Q ==> wp (trm_app v0 v1 v2 v3) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fix3. Qed. *)

(* ----------------------------------------------------------------- *)
(** *** Generalization of [xwp] to Handle Functions of Two Arguments *)

(** Generalization of [xwp] to handle functions of arity 2 and 3,
    and to handle weakening of an existing specification. *)

Lemma xwp_lemma_fun2 : forall v0 v1 v2 x1 x2 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t d))) ->
  (forall d, var_eq (x1 d) (x2 d) = false) ->
  H ==> wpgen fs (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d)) H Q.
Proof using.
Admitted.


Lemma xwp_lemma_wp_fun2 : forall v0 v1 v2 x1 x2 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (t d))) ->
  (forall d, var_eq (x1 d) (x2 d) = false) ->
  H ==> wpgen fs (fun d => subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d)) Q.
Proof using.
Admitted.

Lemma xwp_lemma_fix2 fs : forall f v0 v1 v2 x1 x2 t H Q,
  (v0 = fun d => val_fix (f d) (x1 d) (trm_fun (x2 d) (t d))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (f d) (x2 d) = false) ->
  H ==> wpgen fs (fun d => subst (f d) (v0 d) (subst (x1 d) (v1 d) (subst (x2 d) (v2 d) (t d)))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d)) H Q.
Proof using.
Admitted.


Lemma xwp_lemma_wp_fix2 fs : forall f v0 v1 v2 x1 x2 t H Q,
  (v0 = fun d => val_fix (f d) (x1 d) (trm_fun (x2 d) (t d))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (f d) (x2 d) = false) ->
  H ==> wpgen fs (fun d => subst  (f d) (v0 d) (subst (x1 d) (v1 d) (subst (x2 d) (v2 d) (t d)))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d)) Q.
Proof using.
Admitted.


Lemma xwp_lemma_fun3 : forall v0 v1 v2 v3 x1 x2 x3 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (x1 d) (x3 d) = false /\ var_eq (x2 d) (x3 d) = false) ->
  H ==> wpgen fs (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) H Q.
Proof using.
Admitted.

Lemma xwp_lemma_wp_fun3 : forall v0 v1 v2 v3 x1 x2 x3 t H Q fs,
  (v0 = fun d => val_fun (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d, var_eq (x1 d) (x2 d) = false /\ var_eq (x1 d) (x3 d) = false /\ var_eq (x2 d) (x3 d) = false) ->
  H ==> wpgen fs (fun d => subst (x3 d) (v3 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (t d)))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) Q.
Proof using.
Admitted.


Lemma xwp_lemma_fix3 : forall f v0 v1 v2 v3 x1 x2 x3 t H Q fs,
  (v0 = fun d => val_fix (f d) (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d,
         var_eq (x1 d) (x2 d) = false 
      /\ var_eq (f  d) (x2 d) = false 
      /\ var_eq (f  d) (x3 d) = false
      /\ var_eq (x1 d) (x3 d) = false 
      /\ var_eq (x2 d) (x3 d) = false) ->
  H ==> wpgen fs (fun d => subst (f d) (v0 d) (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (subst (x3 d) (v3 d) (t d))))) Q ->
  htriple fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) H Q.
Proof using.
Admitted.

Lemma xwp_lemma_wp_fix3 : forall f v0 v1 v2 v3 x1 x2 x3 t H Q fs,
  (v0 = fun d => val_fix (f d) (x1 d) (trm_fun (x2 d) (trm_fun (x3 d) (t d)))) ->
  (forall d,
         var_eq (x1 d) (x2 d) = false 
      /\ var_eq (f  d) (x2 d) = false 
      /\ var_eq (f  d) (x3 d) = false
      /\ var_eq (x1 d) (x3 d) = false 
      /\ var_eq (x2 d) (x3 d) = false) ->
  H ==> wpgen fs (fun d => subst  (f d) (v0 d)  (subst (x2 d) (v2 d) (subst (x1 d) (v1 d) (subst (x3 d) (v3 d) (t d))))) Q ->
  H ==> wp fs (fun d => (v0 d) (v1 d) (v2 d) (v3 d)) Q.
Proof using.
Admitted.


Tactic Notation "xwp" :=
  intros;
  first [ applys xwp_lemma_fun;     [ reflexivity | ]
        | applys xwp_lemma_wp_fun;  [ reflexivity | ]
        | applys xwp_lemma_fix;     [ reflexivity | ]
        | applys xwp_lemma_wp_fix;  [ reflexivity | ]
        | applys xwp_lemma_fix2;    [ reflexivity | reflexivity | ]
        | applys xwp_lemma_wp_fun2; [ reflexivity | reflexivity | ]
        | applys xwp_lemma_fun2;    [ reflexivity | reflexivity | ]
        | applys xwp_lemma_fix2;    [ reflexivity | (do ? split); reflexivity | ]
        | applys xwp_lemma_fun3;    [ reflexivity | (do ? split); reflexivity | ]
        | applys xwp_lemma_fix3;    [ reflexivity | (do ? split); reflexivity | ]
        | applys xwp_lemma_wp_fix2; [ reflexivity | (do ? split); reflexivity | ]
        | applys xwp_lemma_wp_fun3; [ reflexivity | (do ? split); reflexivity | ]
        | applys xwp_lemma_wp_fix3; [ reflexivity | (do ? split); reflexivity | ]
        | applys wp_of_wpgen
        | fail 1 "xwp only applies to functions defined using [val_fun] or [val_fix], with at most 3 arguments" ];
  xwp_simpl.

(* ================================================================= *)
(** ** Bonus: Triples for Applications to Several Arguments *)

(** Triples for applications to 2 arguments. Similar rules can be stated and
    proved for 3 arguments. These rules are not needed for the verification
    framework. *)

(* Lemma htriple_app_fun2 : forall v0 v1 v2 x1 x2 t1 H Q,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  x1 <> x2 ->
  htriple (fun d => subst x2 v2 (subst x1 v1 t1)) H Q ->
  htriple (fun d => v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys htriple_eval_like M1. applys* eval_like_app_fun2.
Qed.

Lemma htriple_app_fix2 : forall f x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  htriple (fun d => subst x2 v2 (subst x1 v1 (subst f v0 t1))) H Q ->
  htriple (fun d => v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys htriple_eval_like M1. applys* eval_like_app_fix2.
Qed.

(* ================================================================= *)
(** ** Specification of Record Operations *)

(** The chapter [Struct] shows how to these specifications may be
    realized. *)

Implicit Types k : nat.

(* ----------------------------------------------------------------- *)
(** *** Representation of Records *)

(** A field name is implemented as a natural number *)

Definition field : Type := nat.

(** A record field is described as the pair of a field and a value stored
    in that field. *)

Definition hrecord_field : Type := (field * val).

(** A record consists of a list of fields. *)

Definition hrecord_fields : Type := list hrecord_field.

Implicit Types kvs : hrecord_fields.

(** Record fields syntax, e.g., [`{ head := x; tail := q }]. *)

Notation "`{ k1 := v1 }" :=
  ((k1,(v1:val))::nil)
  (at level 0, k1 at level 0, only parsing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::nil)
  (at level 0, k1, k2 at level 0, only parsing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::(k3,(v3:val))::nil)
  (at level 0, k1, k2, k3 at level 0, only parsing)
  : val_scope.

Notation "`{ k1 := v1 }" :=
  ((k1,v1)::nil)
  (at level 0, k1 at level 0, only printing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,v1)::(k2,v2)::nil)
  (at level 0, k1, k2 at level 0, only printing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,v1)::(k2,v2)::(k3,v3)::nil)
  (at level 0, k1, k2, k3 at level 0, only printing)
  : val_scope.

Open Scope val_scope.

(** [hrecord kvs p], written [p ~~~> kvs], describes a record at location [p],
    with fields described by the list [kvs]. *)

Parameter hrecord : forall (kvs:hrecord_fields) (p:loc), hhprop.

Notation "p '~~~>' kvs" := (hrecord kvs p)
  (at level 32) : hprop_scope.

(** The heap predicate [hrecord kvs p] captures in particular the invariant
    that the location [p] is not null. *)

Parameter hrecord_not_null : forall p kvs,
  hrecord kvs p ==> hrecord kvs p \* \[p <> null].

(* ----------------------------------------------------------------- *)
(** *** Read Operation on Record Fields *)

(** [val_get_field k p], written [p'.k], reads field [k] from the record
    at location [p]. *)

Parameter val_get_field : field -> val.

Notation "t1 '`.' k" :=
  (val_get_field k t1)
  (in custom trm at level 56, k at level 0, format "t1 '`.' k" ) : trm_scope.

(** Generator of specifications of [val_get_field]. *)

Fixpoint hfields_lookup (k:field) (kvs:hrecord_fields) : option val :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some vi
                       else hfields_lookup k kvs'
  end.

(** Specification of [val_get_field] in terms of [hrecord]. *)

Parameter htriple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  htriple (fun d => val_get_field k p)
    (hrecord kvs p)
    (fun r => \[r = v] \* hrecord kvs p).

(* ----------------------------------------------------------------- *)
(** *** Write Operation on Record Fields *)

(** [val_set_field k p v], written [Set p'.k ':= v], update the contents
    of the field [k] from the record at location [p], with the value [v]. *)

Parameter val_set_field : field -> val.

Notation "t1 '`.' k ':=' t2" :=
  (val_set_field k t1 t2)
  (in custom trm at level 56,
   k at level 0, format "t1 '`.' k  ':='  t2")
   : trm_scope.

(** Generator of specifications for [val_set_field]. *)

Fixpoint hfields_update (k:field) (v:val) (kvs:hrecord_fields)
                        : option hrecord_fields :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                   then Some ((k,v)::kvs')
                   else match hfields_update k v kvs' with
                        | None => None
                        | Some LR => Some ((ki,vi)::LR)
                        end
  end.

(** Specification of [val_set_field] in terms of [hrecord]. *)

Parameter htriple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  htriple (fun d => val_set_field k p v)
    (hrecord kvs p)
    (fun _ => hrecord kvs' p).

(* ----------------------------------------------------------------- *)
(** *** Allocation of Records *)

(** [val_alloc_hrecord ks] allocates a record with fields [ks], storing
    uninitialized contents. *)

Parameter val_alloc_hrecord : forall (ks:list field), trm.

Parameter htriple_alloc_hrecord : forall ks,
  ks = nat_seq 0 (LibListExec.length ks) ->
  htriple (fun d => val_alloc_hrecord ks)
    \[]
    (funloc p => hrecord (LibListExec.map (fun k => (k,val_uninit)) ks) p).

(** An arity-generic version of the definition of allocation combined with
    initialization is beyond the scope of this course. We only include
    constructors for arity 2 and 3. *)

(** [val_new_record_2 k1 k2 v1 v2], written [`{ k1 := v1 ; k2 := v2 }],
    allocates a record with two fields and initialize the fields. *)

Parameter val_new_hrecord_2 : forall (k1:field) (k2:field), val.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  (val_new_hrecord_2 k1 k2 v1 v2)
  (in custom trm at level 65,
   k1, k2 at level 0,
   v1, v2 at level 65) : trm_scope.

Open Scope trm_scope.

Parameter htriple_new_hrecord_2 : forall k1 k2 v1 v2,
  k1 = 0%nat ->
  k2 = 1%nat ->
  htriple <{ `{ k1 := v1; k2 := v2 } }>
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 }).

Hint Resolve val_new_hrecord_2 : htriple.

(** [val_new_record_3 k1 k2 k3 v1 v2 v3], written
    [`{ k1 := v1 ; k2 := v2 ; k3 := v3 }],
    allocates a record with three fields and initialize the fields. *)

Parameter val_new_hrecord_3 : forall (k1:field) (k2:field) (k3:field), val.

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  (val_new_hrecord_3 k1 k2 k3 v1 v2 v3)
  (in custom trm at level 65,
   k1, k2, k3 at level 0,
   v1, v2, v3 at level 65) : trm_scope.

Parameter htriple_new_hrecord_3 : forall k1 k2 k3 v1 v2 v3,
  k1 = 0%nat ->
  k2 = 1%nat ->
  k3 = 2%nat ->
  htriple <{ `{ k1 := v1; k2 := v2; k3 := v3 } }>
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 ; k3 := v3 }).

Hint Resolve val_new_hrecord_3 : htriple.

(* ----------------------------------------------------------------- *)
(** *** Deallocation of Records *)

(** [val_dealloc_hrecord p], written [delete p], deallocates the record
    at location [p]. *)

Parameter val_dealloc_hrecord : val.

Notation "'delete'" :=
  (trm_val val_dealloc_hrecord)
  (in custom trm at level 0) : trm_scope.

Parameter htriple_dealloc_hrecord : forall kvs p,
  htriple (fun d => val_dealloc_hrecord p)
    (hrecord kvs p)
    (fun _ => \[]).

Hint Resolve htriple_dealloc_hrecord : htriple.

(* ----------------------------------------------------------------- *)
(** *** Extending [xapp] to Support Record Access Operations *)

(** The tactic [xapp] is refined to automatically invoke the lemmas
    [htriple_get_field_hrecord] and [htriple_set_field_hrecord]. *)

Parameter xapp_get_field_lemma : forall H k p Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_lookup k kvs with
     | None => \[False]
     | Some v => ((fun r => \[r = v] \* hrecord kvs p) \--* protect Q) end ->
  H ==> wp (val_get_field k p) Q.

Parameter xapp_set_field_lemma : forall H k p v Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_update k v kvs with
     | None => \[False]
     | Some kvs' => ((fun _ => hrecord kvs' p) \--* protect Q) end ->
  H ==> wp (val_set_field k p v) Q.

Ltac xapp_nosubst_for_records tt ::=
  first [ applys xapp_set_field_lemma; xsimpl; simpl; xapp_simpl
        | applys xapp_get_field_lemma; xsimpl; simpl; xapp_simpl ].

(* ----------------------------------------------------------------- *)
(** *** Extending [xsimpl] to Simplify Record Equalities *)

(** [fequals_fields] simplifies equalities between values of types
    [hrecord_fields], i.e. list of pairs of field names and values. *)

Ltac fequals_fields :=
  match goal with
  | |- nil = nil => reflexivity
  | |- cons _ _ = cons _ _ => applys args_eq_2; [ fequals | fequals_fields ]
  end.

(** At this point, the tactic [xsimpl] is refined to take into account
    simplifications of predicates of the form [p ~~~> kvs]. The idea is to find
    a matching predicate of the form [p ~~~> kvs'] on the right-hand side of
    the entailment, then to simplify the list equality [kvs = kvs']. *)

Ltac xsimpl_hook_hrecord p :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with hrecord ?kvs' p =>
      constr:(true) end);
  apply xsimpl_lr_cancel_eq;
  [ fequal; first [ reflexivity | try fequals_fields ] | ].

Ltac xsimpl_hook H ::=
  match H with
  | hsingle ?p ?v => xsimpl_hook_hsingle p
  | hrecord ?kvs ?p => xsimpl_hook_hrecord p
  end. *)
Section For_loop.

Import ProgramSyntax Vars.

Definition For_aux (N : int) (body : trm) : trm :=
  trm_fix "for" "cnt"
    <{ let "cond" = ("cnt" < N) in 
      if "cond" then 
        let "body" = body in
        "body" "cnt";
        let "cnt" = "cnt" + 1 in 
        "for" "cnt"
      else 0 }>.

Definition For (Z : int) (N : int) (body : trm) : trm :=
  let f := For_aux N body in <{ let g = f in g Z }>.

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
   Z, N, i at level 0,
   format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.


Open Scope Z_scope.

Definition Union {T D : Type} (l : fset T) (fs : T -> fset D) : fset D. Admitted.
Definition interval (x y : int) : fset int. Admitted.

Lemma intervalU x y : x < y -> interval x y = update (interval (x + 1) y) x tt.
Admitted.

Lemma intervalUr x y : x <= y -> interval x (y + 1) = update (interval x y) y tt.
Admitted.

Lemma intervalgt x y : x <= y -> interval y x = empty.
Admitted.


Lemma Union_upd {T} (x : T) (fs : fset T) (fsi : T -> fset D) : 
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  Union (update fs x tt) fsi = fsi x \u Union fs fsi.
Admitted.

Lemma Union0 {T} (fsi : T -> fset D) : Union empty fsi = empty.
Admitted.

Lemma Union_union {T D} (fs : fset T) (fsi1 fsi2 : T -> fset D) :
  Union fs fsi1 \u Union fs fsi2 = Union fs (fun t => fsi1 t \u fsi2 t).
Admitted.

Lemma Union_label {T D} (fs : fset T) l  (fsi : T -> fset D) :
  label (Lab l (Union fs fsi)) = Union fs (fun t => label (Lab l (fsi t))).
Admitted.


Hint Resolve eqtype.eqxx : lhtriple.

Lemma wp_for_aux i fs fs' ht (H : int -> int -> int -> (D -> val) -> hhprop) Z N f fsi hv0 k :
  (Z <= i <= N) ->
  (* (forall x y z hv1 hv2, x <= y <= z -> H x y hv1 \* H y z hv2 ==> \exists hv, H x z hv) -> *)
  (* (forall k Z i hv, exists k', forall j, H k' i j hv = H k Z j hv) -> *)
  (forall i j k hv1 hv2, (forall x, indom (Union (interval i j) fsi) x -> hv1 x = hv2 x) -> H k i j hv1 = H k i j hv2) ->
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  fs = Union (interval i N) fsi ->
  (forall t, subst "for" t f = f) ->
  (forall t, subst "cnt" t f = f) ->
  (forall t, subst "cond" t f = f) ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For i N f) ->
  (forall j k hv, H k Z j hv ==> wp (fs' \u fsi j) ((fun=> f j) \u_fs' ht) (fun hr => H k Z (j + 1) (hv \u_(Union (interval Z j) fsi) hr))) ->
  (H k Z i hv0) ==> wp (fs' \u fs) ht (fun hr => H k Z N (hv0 \u_(Union (interval Z i) fsi) hr)).
Proof. 
  move=> + hP ?-> sfor scnt scond  + +.
  move: ht hv0.
  induction_wf IH: (upto N) i; rewrite /upto le_zarith lt_zarith in IH.
  move=> ht hv0 lN dj htE.
  rewrite -wp_union // (wp_ht_eq _ _ _ htE) /For /For_aux.
  Opaque subst.
  (* xwp. rewrite wp_of_wpgen. xapp.
  Transparent subst. 
  rewrite sfor /=. 
  xapp; rewrite scnt scond -/(For_aux N f).
  xwp; xif; rewrite lt_zarith.
  { move=> ?.
    xwp; xseq.
    apply: himpl_trans; first last.
    { apply/wp_conseq=> ?. xwp. xlet. xapp. }
    apply: himpl_trans; first last.
    { apply/wp_conseq=> ?. 
      rewrite hstar_hempty_l. 
      apply himpl_qwand_r=> ?. rewrite /protect. 
      xsimpl=>->.
      set (ht' := (fun=> For_aux N f (i + 1)) \u_fs' ht).
      rewrite (wp_ht_eq _ ht').
      { apply/wp_conseq=> ?; rewrite (wp_ht_eq _ ht'). xsimpl*. admit. }
      admit. }
    rewrite (wp_union (fun hr2 => H k Z N (_ \u_ _ hr2))) //.
    rewrite // intervalU // Union_upd // -union_assoc.
    rewrite union_comm_of_disjoint -?union_assoc; first rewrite union_comm_of_disjoint.
    2-3: admit.
    rewrite -wp_union; first last.
    { admit. }
    set (ht' := (fun=> f i) \u_fs' ht).
    rewrite (wp_ht_eq _ ht'); first last.
    { admit. }
    rewrite (wp_ht_eq (_ \u_ _ _) ht'); first last.
    { admit. }
    apply: himpl_trans; last apply/wp_union2; first last.
    { admit. }
    move: (H0 i k hv0)=> /wp_equiv S; xapp S.
    move=> hr.
    apply: himpl_trans; first last.
    { apply: wp_conseq=> ?; rewrite uniA=> ?; exact. }
    set (hv0 \u_ _ _); rewrite [_ \u fsi i]union_comm_of_disjoint; first last.
    { admit. }
    rewrite -Union_upd // -intervalUr; last math.
    rewrite union_comm_of_disjoint; last admit.
    apply IH; try math.
    { admit. }
    { admit. }
    move=> j ??.
    rewrite (wp_ht_eq _ ((fun=> f j) \u_ fs' ht)) //.
    move=> ??; rewrite /uni; case: classicT=> //. }
    move=> ?; have->: i = N by math.
    xwp; xval.
    rewrite intervalgt ?Union0; last math.
    apply: himpl_trans; first last.
    { apply: wp_conseq=> ?. rewrite (hP _ _ _ _ hv0)=> [?|*]; first exact.
      by rewrite uni_in. }
    by rewrite wp0. *)
Admitted.

Lemma wp_for fs fs' ht (H : int -> int -> int -> (D -> val) -> hhprop) Z N (f : trm) fsi hv0 k (P : hhprop) Q :
(* (forall x y z hv1 hv2, x <= y <= z -> H x y hv1 \* H y z hv2 ==> \exists hv, H x z hv) -> *)
  (forall k Z i hv, exists k', forall j hv', (forall x, indom (Union (interval Z i) fsi) x -> hv x = hv' x) -> H k' i j hv' = H k Z j hv') ->
  (forall j k hv, H k j j hv ==> wp (fs' \u fsi j) ((fun=> f j) \u_fs' ht) (H k j (j + 1))) ->
  (forall i j k hv1 hv2, (forall x, indom (Union (interval i j) fsi) x -> hv1 x = hv2 x) -> H k i j hv1 = H k i j hv2) ->
  (P ==> H k Z Z hv0) -> 
  (H k Z N ===> Q) ->
  (Z <= N) ->
  (forall i j, i <> j -> disjoint (fsi i) (fsi j)) ->
  fs = Union (interval Z N) fsi ->
  (forall t, subst "for" t f = f) ->
  (forall t, subst "cnt" t f = f) ->
  (forall t, subst "cond" t f = f) ->
  disjoint fs' fs ->
  (forall x, indom fs' x -> ht x = For Z N f) ->
  P ==> wp (fs' \u fs) ht Q.
Proof.
  move=> hp Hwp Heq HP HQ *.
  apply: himpl_trans; first exact/HP.
  apply: himpl_trans; first last.
  { apply: wp_conseq; exact/HQ. }
  apply: himpl_trans.
  { apply/(@wp_for_aux Z); eauto; first math.
    clear k HP HQ=> i k hv.
    case: (hp k Z i hv)=> k' /[dup]HE<- ? // /Hwp; apply/wp_conseq=> hr.
    rewrite -(HE _ (hv \u_ (Union (interval Z i) fsi) hr)).
    { erewrite Heq; eauto. admit. }
    admit. }
  apply/wp_conseq=> ?; rewrite intervalgt ?Union0 ?uni0 //; by math.
Admitted.
      (* rewrite wp_union // intervalU // Union_upd // -union_assoc. *)
    (*   }
Qed. *)


End For_loop.



End Reasoning.

(* From mathcomp Require Import seq.

Section Def.

From mathcomp Require Import ssrbool ssrnat eqtype.



Record htrm (D : Type) := {
  fs : fset D  ;
  ht : D -> trm;
}.

Definition htrm_def (D : Type) : htrm D := {|
  fs := empty;
  ht := fun=> 0 
|}.

(* Definition htrms  := seq (sigT (fun D => htrm D)). *)

Record HD (f : nat -> Type) := {
  num : nat;
  tp  : f num;
}.

Definition htrms (f : nat -> Type) :=
  seq (sigT (fun (n : nat) => htrm (f n))).

Definition lookup f n (hts : htrms f) : trm 

Definition ht_of (f : nat -> Type) (hts : htrms f) : HD f -> trm :=
  fun '(Build_HD n tp) => (hts n).(ht) tp.

Definition fs_of (f : nat -> Type) (hts : htrms f) (ids : seq nat) : fset (HD f).
refine (make 
  (fun '(Build_HD n tp) => 
    if n \in ids then 
      fmap_data (hts n).(fs) tp
    else None
  ) _).
Admitted.

Definition prj f (P : nat -> Prop) (fs : fset (HD f)) := 
  LibSepFmap.filter (fun d _ => P d.(num)) fs.

End Def.

Module Type HT.

Parameter f : nat -> Type.

End HT.

Module Reasoning_htrms (H : HT).

Export H.

Module Dom : Domain with Definition type := HD f.
Definition type := HD f.
End Dom.

Module Export RD := Reasoning(Dom).
Include Dom.


Section Focus.

Context (hts : htrms f).

Definition ht_of_f := @ht_of f.
Coercion ht_of_f : htrms >-> Funclass.

Implicit Type hts : htrms f.
Implicit Type fs  : fset (HD f).


Lemma focus hts fs (Q : (D -> trm) -> hhprop) n : 
  let fs 
  wp (fs_of hts) hts Q =
  wp (prj (= n) )

End Focus.

End Reasoning_htrms. *)

(* From mathcomp Require Import seq.

Fixpoint vec (n : nat) : Type := 
  match n with
  | S n => nat * vec n
  | O   => nat
  end.

Definition Vec := sigT vec.

Module VecDom : Domain with Definition type := Vec.
Definition type := Vec.
End VecDom.


Module RV := Reasoning(VecDom).

Definition Vec_union (fss : seq (fset Vec)) : fset Vec.
Admitted.

Definition mark (n : nat) (fs : (fset Vec)) : fset Vec.
Admitted.

Definition htrm := Vec -> trm.

(* Definition htrm_def : htrm := {|
  fs := empty;
  ht := fun=> 0
|}. *)

Definition htrms := seq htrm.

Implicit Type hts : htrms.
Implicit Type fss  : seq (fset Vec).


Definition hts_of hts : Vec -> trm := 
  fun '(existT n v) => 
    nth n 

Lemma focus hts fss (Q : (D -> trm) -> hhprop) n : 
  wp (Vec_union fss) hts Q =
  wp (mak n (nth empty n fss))  *)

(* Section Def.
From mathcomp Require Import ssrbool ssrnat eqtype.

Fixpoint lookup (hts : htrms) (n : nat) : htrm := 
  match hts with 
  | [::] => htrm_def 
  | (k, ht) :: hts => if k == n then ht else lookup hts n
  end.

End Def. *)

Module nReasoning(D : Domain).

Module HD : Domain with Definition type := labeled D.type.
Definition type := labeled D.type.
End HD.

Module NR := Reasoning(HD).
Export NR.

Record fset_htrm := FH {
  fs_of : fset D.type;
  ht_of : D.type -> trm;
}.

From mathcomp Require Import seq.

(* Definition htrm := D.type -> trm. *)
(* Definition htrms := labSeq htrm. *)
(* Definition fset_htrm := labSeq ( * htrm). *)

(* Implicit Type ht  : htrm. *)
(* Implicit Type hts : htrms. *)
(* Implicit Type fss : labSeq (fset D.type). *)

Definition fset_of : labSeq fset_htrm -> fset (HD.type). Admitted.
Definition htrm_of : labSeq fset_htrm -> (HD.type -> trm). Admitted.

Lemma fset_of_cons fs_ht fs_hts l : 
    fset_of ((Lab l fs_ht) :: fs_hts) = 
    label (Lab l (fs_of fs_ht)) \u fset_of fs_hts.
Admitted.

Lemma fset_of_nil : 
    fset_of nil = empty.
Admitted.


Definition adequate (Q : (HD.type -> val) -> hhprop) (fs : fset HD.type) :=
  forall hv' hv, Q hv = Q (hv \u_(fs) hv').


Definition nwp (fs_hts : labSeq fset_htrm) Q := wp (fset_of fs_hts) (htrm_of fs_hts) Q.

Definition eld : D -> D.type := @el _.

Coercion eld : D >-> D.type.

Lemma fset_htrm_lookup_remove l fs_hts : 
  let fs_ht := lookup (FH empty (fun=> val_unit : trm)) fs_hts l in
  let fs    := fs_of (el fs_ht) in 
    fset_of fs_hts = 
    label (Lab l fs) \u 
    fset_of (remove fs_hts l).
Proof.
Admitted.

Lemma fset_htrm_label_remove_disj l fs_hts fs : 
    disjoint
      (label (Lab l fs))
      (fset_of (remove fs_hts l)).
Proof.
Admitted.

Lemma lookup_eq l fs_hts (d : D) : 
  let fs_ht := lookup (FH empty (fun=> val_unit : trm)) fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    indom (label (Lab l fs)) d ->
      htrm_of fs_hts d = ht d.
Proof.
Admitted.

Lemma remove_eq l fs_hts (d : D) : 
  let fs_ht := lookup (FH empty (fun=> val_unit : trm)) fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    indom (fset_of (remove fs_hts l)) d ->
      htrm_of fs_hts d = htrm_of (remove fs_hts l) d.
Proof.
Admitted.

Lemma indom_label l (fs : fset D.type) l' x :
  indom (label (Lab l fs)) (Lab l' x) -> l' = l.
Proof.
Admitted.

Lemma indom_remove l fs_hts l' x :
  indom (fset_of (remove fs_hts l)) (Lab l' x) -> l' <> l.
Proof.
Admitted.

(* Declare Scope labfset_scope.
Delimit Scope labfset_scope with lbfs. *)
Declare Scope fset_scope.
Delimit Scope fset_scope with fs.
(**
Declare Scope labtrm_scope.
Delimit Scope labtrm_scope with lbtrm. *)
Declare Scope fs_hts.
Delimit Scope fs_hts with fh.

Declare Scope fun_scope.
Delimit Scope fun_scope with fn.

Notation "'⟨' l ',' x '⟩'" := (label (Lab l%nat x%fs)) (at level 5, right associativity, format "⟨ l ,  x ⟩").

Definition ntriple H fs_hts Q := H ==> nwp fs_hts Q.

Lemma xfocus_lemma (l : labType) fs_hts (Q : (HD.type -> val) -> hhprop) H : 
  let fs_ht := lookup (FH empty (fun=> val_unit : trm)) fs_hts l in
  let fs    := fs_of (el fs_ht) in 
  let ht    := ht_of (el fs_ht) in
    H ==> wp ⟨l, fs⟩ [eta ht]
            (fun hr => nwp (remove fs_hts l) (fun hr' => Q (hr \u_⟨l, fs⟩ hr'))) ->
    ntriple H fs_hts Q.
Proof.
  move=> fs_ht fs ht.
  apply: himpl_trans_r.
  rewrite /nwp (fset_htrm_lookup_remove l fs_hts) -wp_union -/fs_ht; first last.
  { exact/fset_htrm_label_remove_disj. }
  under (wp_ht_eq (htrm_of fs_hts))=> ? IN.
  { rewrite (lookup_eq _ IN); over. }
  rewrite -/fs_ht -/ht.
  apply/wp_conseq=> hv.
  under (wp_ht_eq (htrm_of fs_hts))=> ? IN.
  { rewrite (remove_eq _ _ IN); over. }
  move=> h Hwp; rewrite -/fs //.
Qed.

Lemma xunfocus_lemma (Q : (HD.type -> val) (*-> (HD.type -> val)*) -> hhprop) fs_hts 
  (ht : D.type -> trm) (fs : fset D.type) H (ht' : HD.type -> _)
  (Q' : (HD.type -> val) -> (HD.type -> val) -> hhprop)
  (l : labType) :
  ~ has_lab fs_hts l ->
  (forall l, ht = (fun d => ht' (Lab l d))) ->
  (forall hr hr', Q' hr hr' = Q (hr \u_⟨l, fs⟩ hr')) ->
  (* adequate (fun hr => Q hr hr) (⟨l, fs⟩ \u fset_of fs_hts) -> *)
  ntriple H ((Lab l (FH fs ht)) :: fs_hts) (fun hr => Q hr) ->
  H ==> wp ⟨l, fs⟩ ht' (fun hr => nwp fs_hts (fun hr' => Q' hr hr')).
Proof.
  rewrite /ntriple/nwp=> /hasnt_lab /[dup]rE {1}-> /[! fset_of_cons] htE QE.
  apply: himpl_trans_r.
  (* apply: himpl_trans. *)
  rewrite -wp_union /=; first last.
  {  exact/fset_htrm_label_remove_disj. }
  under wp_ht_eq=> -[l' d] IN.
  { move: (htE l')=> /(congr1 (@^~ d)) {}htE.
    rewrite (@lookup_eq l) /lookup /= eqtype.eqxx //= htE. over. }
  move=> /= h Hwp; simpl; apply/wp_conseq; eauto=> hr /=; simpl.
  (* xpull=> hv' {Hwp}h Hwp; exists hv'. *)
  (* move: h Hwp. *)
  under wp_ht_eq=> ? IN.
  { rewrite (@remove_eq l) /= eqtype.eqxx /= // -rE; over. }
  rewrite -rE // => {Hwp}h Hwp.
  eapply wp_conseq; last exact/Hwp.
  by move=> ??; rewrite QE.
Qed.

Lemma nwp0 Q : 
  nwp nil (fun=> Q) = Q.
Proof. by rewrite /nwp fset_of_nil wp0. Qed.

Lemma xcleanup_lemma fs_hts Q v l fs H Q' : 
  ~ has_lab fs_hts l ->
  (forall hr, Q' hr = Q (v \u_⟨l, fs⟩ hr)) ->
  ntriple H fs_hts (fun hr => Q (lab_fun_upd v hr l)) -> 
  H ==> nwp fs_hts (fun hr => Q' hr).
Proof.
  move=> /hasnt_lab-> QE.
  apply: himpl_trans_r; rewrite /nwp.
  move=> ? Hwp; apply/wp_hv; apply: wp_conseq Hwp=> hr ? Qh.
  exists (lab_fun_upd v hr l); rewrite QE.
  move: Qh; apply: applys_eq_init; fequals; apply/fun_ext_1=> -[l' ?].
  rewrite /uni; case: classicT=> [/indom_label->|].
  { by rewrite /lab_fun_upd eqtype.eqxx. }
  by case: classicT=> // /indom_remove /(@lab_fun_upd_neq _ _ _ _ _ _ _)->.
Qed.


Lemma hhoare_ref_lab : forall H (f : D.type -> val) fs l,
  hhoare ⟨l, fs⟩ (fun d => val_ref (f d))
    H
    (fun hr => (\exists (p : D.type -> loc), \[hr = fun d => val_loc (p d)] \* \*_(d <- ⟨l, fs⟩) p d ~(d)~> f d) \* H).
Proof.
Admitted.

Lemma lhtriple_ref : forall (f : val)  l x, 
  htriple ⟨l, (single x tt)⟩ (fun d => val_ref f)
    \[]
    (fun hr => (\exists (p : loc), \[hr = fun=> val_loc p] \*  p ~(Lab l x)~> f)).
Proof.
Admitted.

Lemma htriple_ref_lab : forall (f : val) fs l,
  htriple ⟨l, fs⟩ (fun d => val_ref f)
    \[]
    (fun hr => (\exists (p : D.type -> loc), \[hr = fun d => val_loc (p d)] \* \*_(d <- ⟨l, fs⟩) p d ~(d)~> f)).
Proof.
Admitted.

Lemma lhtriple_get : forall v (p : loc) fs,
  htriple fs (fun d => val_get p)
    (\*_(d <- fs) p ~(d)~> v)
    (fun hr => \[hr = fun => v] \* (\*_(d <- fs) p ~(d)~> v)).
Proof using.
  intros. unfold htriple. intros H'. applys hhoare_conseq hhoare_get; xsimpl~.
Qed.

Lemma lhtriple_set : forall v (w : _ -> val) (p : loc) fs,
  htriple fs (fun d => val_set p (w d))
  (\*_(d <- fs) p ~(d)~> v)
  (fun hr => \[hr = w] \* (\*_(d <- fs) p ~(d)~> w d)).
Proof using.
Admitted.

Hint Resolve htriple_ref_lab lhtriple_ref lhtriple_get lhtriple_set : lhtriple.

Arguments xfocus_lemma _ {_}.
Arguments xunfocus_lemma _ {_}.

(* From mathcomp Require Import seq. *)


(* Lemma xnwp0_lemma H Q l fs ht' :
  H ==> wp ⟨l, fs⟩ ht' Q ->
  H ==> wp ⟨l, fs⟩ ht' (fun hr => nwp nil (fun _ => Q hr)).
Proof.
  apply: himpl_trans_r.
  by apply: wp_conseq=> ?; rewrite nwp0.
Qed. *)

Lemma xnwp0_lemma H Q :
  H ==> Q ->
  ntriple H nil (fun=> Q).
Proof.
  by apply: himpl_trans_r=> ? /[! nwp0].
Qed.

Lemma nwp_of_ntriple H Q fs_hts :
  ntriple H fs_hts Q =
  H ==> nwp fs_hts Q.
Proof. by []. Qed.

Notation "'N-WP' fs_hts '{{' v ',' Q '}}'" := 
    (nwp 
      fs_hts%fh
      (fun v => Q%fn)) (at level 20, v name,
      format "'N-WP'  '[' fs_hts '/'  '{{'  v ','  Q  '}}' ']' ") 
    : wp_scope.

Notation "'{{' H '}}' fs_hts '{{' v ',' Q '}}'" := 
    (ntriple 
      H%fn
      fs_hts%fh
      (fun v => Q%fn)) (at level 20, v name,
      format " '[' '[' '{{'  H  '}}' ']' '/   ' '[' fs_hts ']' '/' '[' '{{'  v ','  Q  '}}' ']' ']' ") 
    : wp_scope.

Notation "'[{' fs1 ';' fs2 ';' .. ';' fsn '}]'" := 
  (cons fs1%fh (cons fs2%fh .. (cons fsn%fh nil) ..)) (at level 30
  , format "[{ '['  fs1 ';' '/'  fs2 ';' '/'  .. ';' '/'  fsn  ']' }] "
  ) : fs_hts.

Notation "'[{' fs '}]'" := 
  (cons fs%fh nil) (at level 30, format "[{  fs  }]") : fs_hts.

Export ProgramSyntax.

Notation "'[' l '|' d 'in' fs '=>' t ]" := (Lab l%nat (FH fs%fs (fun d => <{ t }>))) (at level 20, d name) : fs_hts.

Tactic Notation "xfocus" constr(S) := 
  let n := eval vm_compute in (Z.to_nat S) in
  apply (xfocus_lemma n); simpl; try apply xnwp0_lemma.

Tactic Notation "xunfocus" := 
eapply xunfocus_lemma=> //=; [intros; remember ((_ \u_ _) _); reflexivity|].

Tactic Notation "xcleanup" constr(n) := 
match goal with 
| |- context G [?v \u_ ⟨_, ?fs⟩] => eapply ((@xcleanup_lemma _ _ v n fs))
end=>//; [intros; remember ((_ \u_ _) _); reflexivity|].


Tactic Notation "xin" constr(S1) ":" tactic(tac) := 
  let n := eval vm_compute in (Z.to_nat S1) in
  xfocus n; tac; try(
  first [xunfocus | xcleanup n]; simpl; try apply xnwp0_lemma).


Tactic Notation "xin" constr(S1) constr(S2) ":" tactic(tac) := 
  let n1 := eval vm_compute in (Z.to_nat S1) in
  let n2 := eval vm_compute in (Z.to_nat S2) in
  xfocus n1; tac; first [xunfocus | xcleanup n1];
  xfocus n2; tac; first [xunfocus | xcleanup n2]; simpl; try apply xnwp0_lemma.

Tactic Notation "xnsimpl" := 
  rewrite /ntriple; xsimpl; rewrite -nwp_of_ntriple.

Notation "f '[' i ']' '(' j ')'" := (f (Lab i%nat j)) (at level 30, format "f [ i ] ( j )") : fun_scope.
Notation "'⟨' l ',' x '⟩'" := ((Lab l%nat x%fs)) (at level 5, right associativity, format "⟨ l ,  x ⟩") : arr_scope.

Lemma hstar_fset_label_single Q x l : 
  \*_(d <- ⟨l, single x tt⟩) Q d = 
  Q (Lab l x).
Proof.
Admitted.


Hint Rewrite hstar_fset_label_single : hstar_fset.


Arguments lab_fun_upd /.

Context (bigop : forall {A}, (int -> int -> int) -> fset A -> (A -> int) -> int).
Reserved Notation "'\big[' f ']' ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \big[ f ] ( i  <-  r ) '/  '  F ']'").

Notation "'\big[' f ']' ( i <- r ) F" :=
  (bigop f r (fun i => F)) : nat_scope.

Lemma bigopxSx op l : bigop op (interval l (l + 1)) = @^~ l.
Proof.
Admitted.

Lemma op_bigop0 {T} op x F : op x (\big[op](i <- (empty : fset T)) F i) = x.
Proof.
Admitted.


(* Hypotheses (Distr : forall fs f i, (Σ_(j <- fs) f j) * i = Σ_(j <- fs) f j * i). *)
(* Hypotheses (Monot : forall fs f g, (forall i, indom fs i -> (f i <= g i)%Z) -> (Σ_(j <- fs) f j <= Σ_(j <- fs) g j)%Z). *)
(* Hypotheses (Const : forall c, Σ_(i <- [0,i]) c = c * i). *)

Arguments wp_for _ _ {_}.

Lemma Union_singleE (x y : int) : 
  Union (interval x y) (fun x => single x tt) = 
  interval x y.
Proof.
Admitted.


Definition Sum : fset int -> (int -> int) -> int. Admitted.
Reserved Notation "'Σ_' ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' Σ_ ( i  <-  r ) '/  '  F ']'").

Notation "'Σ_' ( i <- r ) F" :=
  (Sum r (fun i => F)) : nat_scope.

Lemma xfor_big_op_lemma H (R R' : D.type -> hhprop) op p s fsi1 (*fsi2*) vr
  Z N  (*op1 : int -> int -> int*) (i : nat) j (*k*) (C1 : D.type -> trm) (*C2 : D.type -> trm*) (C : trm)
  Pre Post: 
  (forall (l : int) (x : int), 
    Z <= l <= N ->
    {{ H l \* 
       (\*_(d <- ⟨j, fsi1 l⟩) R d) \* 
       p ~⟨i, s⟩~> x }}
      [{
        [i| _  in single s tt  => subst vr l C];
        [j| ld in fsi1 l       => C1 ld]
        (* [k| ld in fsi2 l       => C2 ld] *)
      }]
    {{ hv, 
        H (l + 1) \* 
        (\*_(d <- ⟨j, fsi1 l⟩) R' d) \* 
        p ~⟨i, s⟩~> (x + (op hv l)) }}) ->
  (Z <= N)%Z ->
  (forall t : val, subst "for" t C = C) -> 
  (forall t : val, subst "cnt" t C = C) ->
  (forall t : val, subst "cond" t C = C) ->
  (Pre ==> 
    H Z \* 
    (\*_(d <- ⟨j, Union (interval Z N) fsi1⟩) R d) \*
    p ~⟨i, s⟩~> 0) ->
  (forall hv, 
    H N \* 
    (\*_(d <- ⟨j, Union (interval Z N) fsi1⟩) R' d) \* 
    p ~⟨i, s⟩~> (Σ_(i <- interval Z N) (op hv i)) ==>
    Post hv) -> 
  {{ Pre }}
    [{
      [i| _  in single s tt => For Z N (trm_fun vr C)];
      [j| ld in Union (interval Z N) fsi1 => C1 ld]
      (* [k| ld in Union (interval Z N) fsi2 => C2 ld] *)
    }]
  {{ hv, Post hv }}.
Proof.
  (* move=> IH *.
  rewrite /ntriple /nwp ?fset_of_cons /= ?Union_label.
  rewrite fset_of_nil union_empty_r Union_union.
  apply/(
    wp_for _ ⟨i, single s tt⟩
      (fun x (r : int) q hv => H q \* p ~⟨i, s⟩~> op1 x (\big[op1](l <- interval r q) op2 hv l))
      Z N C
      (fun t : int => ⟨j, fsi1 t⟩ \u ⟨k, fsi2 t⟩)
      (fun=> 0) x)=> //.
  { admit. }
  { clear -IH. 
    move=>l x hv; move: (IH l x).
    rewrite /ntriple /nwp ?fset_of_cons /= ?fset_of_nil bigopxSx.
    rewrite union_empty_r intervalgt; last math.
    rewrite op_bigop0; apply:himpl_trans_r.
    erewrite wp_ht_eq; eauto. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  admit. *)
Admitted.

Opaque label.
Opaque nwp.

End nReasoning.

Hint Resolve eqtype.eqxx : lhtriple.

(* ################################################################# *)
(** * Demo Programs *)


Module DemoPrograms.

Module Pow.

Module Dom : Domain with Definition type := int.
Definition type := int.
End Dom.

Module Export RD := Reasoning(Dom).
Include Dom.

Export ProgramSyntax.
Import Vars.

Reserved Notation "'Σ_' ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' Σ_ ( i  <-  r ) '/  '  F ']'").

Notation "'Σ_' ( i <- r ) F" :=
  (sum r (fun i => F)) : nat_scope.

Print Dom.type.

Section pow.


Context (i : int).
Context (iL0 : i >= 0).
Context (int0i : fset int).
Hypotheses (int0iH : forall x, indom int0i x = (0 <= x <= i)%Z).
(*  *)
Notation "'[0,i]'" := (int0i).



Definition to_int (v : val) : int := 
  match v with 
  | val_int i => i 
  | _ => 0
  end.

Coercion to_int : val >-> Z.

Definition pow_aux : trm :=
  <{ fix f n d p =>
     let b = (n <= 0) in
      if b then 
        let x = ! p in x
      else 
        let x = ! p   in
        let y = x * d in
        p := y;
        let m = n - 1 in
        f m d p }>.

Definition pow : trm :=
  <{ fun d n => let p = ref 1 in pow_aux n d p; free p }>.



From mathcomp Require Import zify.

(* Lemma htriple_pow_aux (s : int -> int) (n : int) (p : D -> loc):

  (forall j, (0 <= j)%Z -> (0 <= s j)%Z) ->

  (Σ_(j <- [0,i]) s j <= s i * i)%Z ->

    htriple [0,i] 
      (fun d => pow_aux n d (p d))
      (\*_(d <- [0,i]) p d ~(d)~> s d)
      (fun v => \[Σ_(j <- [0,i]) v j <= v i * i]%Z \* \Top).
Proof.
  move: s p.
  induction_wf IH: (downto 0) n; rewrite /downto in IH.
  move=> s p H H'.
  xwp; autos*; xapp; rewrite -/pow_aux.
  xwp; xif.
  { move=> _. xwp; xapp. xwp; xval. xsimpl*. }
  move=> ?.
  xwp; xapp. rewrite -/pow_aux.
  xwp; xapp. rewrite -/pow_aux.
  xwp; xapp; rewrite -/pow_aux.
  xwp; xapp; rewrite -/pow_aux.
  rewrite wp_equiv.
  apply IH.
  { math. }
  { move=> ? /[dup]/H. math. }
  have: ((Σ_(j <- [0,i]) s j) * i <= s i * i * i)%Z.
  apply/Zmult_le_compat_r=> //.
  apply/Z.le_trans. 
  rewrite Distr.
  apply/Monot=> ? /[! int0iH] -[??].
  apply/Z.mul_le_mono_nonneg_l; eauto.
Qed. *)

(* Lemma htriple_pow_sum (k : int) :
  htriple [0,i] 
    (fun d => pow d k)
    \[]
    (fun v => \[Σ_(j <- [0,i]) v j <= v i * i]%Z \* \Top).
Proof.
  rewrite /pow /=.
  xwp; xapp=> p /=; rewrite -/pow_aux.
  rewrite wp_equiv.
  apply/htriple_pow_aux.
  { math. }
  rewrite Const; math.
Qed. *)

End pow.

End Pow.

Module Pow1.

Module Dom : Domain with Definition type := int.
Definition type := int.
End Dom.

Module Export RD := nReasoning(Dom).
Include Dom.

(* Export ProgramSyntax. *)
Import Vars.

Print Dom.type.

Section pow.

Context    (i : int).
Context    (iL0 : i >= 0).
(* Context    (int0i : fset int). *)
(* Hypotheses (int0iH : forall x, indom int0i x = (0 <= x <= i)%Z). *)

Notation "'{::' i '}'" := (single i tt) (at level 10) : fset_scope.
Notation "'[0,i]'" := (interval 0 i).

Notation "'for' i <- '[' Z ',' N ']' '{' t '}'"  :=
  (For Z N <{ fun_ i => t }>)
  (in custom trm at level 69,
   Z, N, i at level 0,
   format "'[' for  i  <-  [ Z ','  N ] ']'  '{' '/   ' '[' t  '}' ']'") : trm_scope.


Reserved Notation "'Σ_' ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' Σ_ ( i  <-  r ) '/  '  F ']'").

Notation "'Σ_' ( i <- r ) F" :=
  (Sum r (fun i => F)) : nat_scope.


(* Hypotheses (Distr : forall fs f i, (Σ_(j <- fs) f j) * i = Σ_(j <- fs) f j * i).
Hypotheses (Monot : forall fs f g, (forall i, indom fs i -> (f i <= g i)%Z) -> (Σ_(j <- fs) f j <= Σ_(j <- fs) g j)%Z).
Hypotheses (Const : forall c, Σ_(i <- [0,i]) c = c * i). *)

Definition to_int (v : val) : int := 
  match v with 
  | val_int i => i 
  | _ => 0
  end.

Coercion to_int : val >-> Z.

Definition pow_aux : trm :=
  <{ fix f n d p =>
     let b = (n <= 0) in
     if b then 
      let x = ! p in x
     else 
      let x = ! p   in
      let y = x * d in
      p := y;
      let m = n - 1 in
      f m d p }>.

Definition pow : trm :=
  <{ fun d n => let p = ref 1 in pow_aux n d p }>.

Definition pow_sum : trm := 
  <{ fun x a => 
      let p = ref 1 in
      for j <- [0, i] { 
        let n = ! p in 
        let k = ! x in 
        let l = k + n in 
        let m = n * a in
        x := l;
        p := m
    } 
  }>.

(* Opaque For. *)

Hypotheses (Distr : forall fs f i, (Σ_(j <- fs) f j) * i = Σ_(j <- fs) f j * i).
Hypotheses (Monot : forall fs f g, (forall i, indom fs i -> (f i <= g i)%Z) -> (Σ_(j <- fs) f j <= Σ_(j <- fs) g j)%Z).
Hypotheses (Const : forall c i, Σ_(i <- interval 0 i) c = c * i).


Lemma himpl_hstar_fset (R R' : D -> hhprop) (fs : fset D) : 
  (forall d, indom fs d -> R d ==> R' d) ->
  \*_(d <- fs) R d ==> \*_(d <- fs) R' d.
Proof.
Admitted.

Lemma label_single {T} (t : T) l : 
  ⟨l, {:: t}⟩ = {:: Lab l t}%fs.
Proof using.
Admitted.

Lemma optimize_pow_sum (x : int) (q : loc) :
  {{ q ~⟨1, 0⟩~> 0 }}
  [{
    [1| ld in {::0} => pow_sum q x ];
    [2| ld in [0,i] => pow x ld]
  }]
  {{ v, \Top \* q ~⟨1, 0⟩~> Σ_(j <- [0,i]) v[2](j) }}.
Proof.
  xin 2: xwp; xapp=> r; rewrite -/pow_aux.
  xin 1: xwp; xapp=> p; rewrite -/(For_aux i _)-/(For 0 i _).
  rewrite -{2}Union_singleE.
  set (H i := 
     \exists (a : int), 
       p ~⟨1,0⟩~> a \* 
       \[forall (r : loc) (y : int), 
            htriple 
              ⟨2, {::i}⟩ 
              (fun ld => pow_aux i x r) 
              (r ~⟨2, i⟩~> y) 
              (fun hv => \[hv[2](i) = a * y] \* \Top) ] ).
  set (R i := r i ~⟨2, i⟩~> 1).
  set (R' (i : int) := \Top).
  apply/(xfor_big_op_lemma H R R')=> //=; try xsimpl*; simpl.
  { move=> l y lb.
    rewrite /H /R /R' /ntriple; xsimpl=> z htg.
    move=> ht.
    xin 1: do ? (xwp; xapp).
    xin 2: xapp htg=> [|hv hvE].
    { by move=> ?; rewrite label_single indom_single_eq=> <-. }
    xsimpl. 
    { clear -htg lb=> r y.
      set (f d := Lab (lab d) (el d - 1)).
      set (g d := Lab (lab d) (el d + 1)).
      have [??]: cancel f g /\ cancel g f.
      { rewrite /f /g; split=> -[] ??; fequals=> /=; math. }
      rewrite (htriple_hsubst f g) //= /=.
      rewrite label_single fsubst_single /= -?label_single //. last exists g=> //.
      rewrite /comp /= -/eld hsubst_hsingle /=.
      apply/htriple_conseq; first last. 
      { move=> ?; rewrite hsubst_hstar hsubst_hpure hsubst_htop=> ?.
        exact. }
      { eauto. }
      replace (l + 1 - 1) with l; [|math].
      xwp; xapp; rewrite -/pow_aux.
      xwp; xif=> //; try math.
      move=> _. 
      do 4? (xwp; xapp); rewrite -/pow_aux.
      replace (l + 1 - 1) with l; [|math].
      xapp htg=> ? ->.
      rewrite fun_eta_1; xsimpl; math. }
    rewrite hvE /= Z.mul_1_r. 
    xsimpl*. }
  rewrite Union_singleE /R /H; xsimpl.
  { move=> {R}r y.
    xwp; xapp. 
    xwp; xif; rewrite -/pow_aux; try math.
    move=> _.
    xwp; xapp.
    xwp; xval.
    xsimpl*; math. }
  apply/himpl_hstar_fset=> -[l d]/= /indom_label-> //.
Qed.

From mathcomp Require Import zify.

Open Scope Z_scope.

Lemma htriple_pow_times_aux n (s : Dom.type -> int) v (p : Dom.type -> loc) q :
  n >= 0 ->
  (forall j, 0 <= j -> 0 <= s j) ->
  Σ_(j <- [0,i]) s j <= v * i ->
  0 <= v ->

    {{ q ~⟨2, i⟩~> v \* \*_(d <- ⟨1, [0,i]⟩) p d ~(d)~> s d }}
      [{ 
        [1| ld in [0,i] => pow_aux n ld (p ld)];
        [2| ld in {::i} => pow_aux (n + 1) ld q]
      }]
    {{ hr, \[Σ_(j <- [0,i]) hr[1](j) <= hr[2](i)] \* \Top }}.
Proof.
  move: s p v.
  induction_wf IH: (downto 0) n; rewrite /downto in IH.
  move=> s p v H H'.
  move=> *.
  xin 1: xwp; xapp; rewrite -/pow_aux.
  xin 1: xwp; xif=> cond.
  { move=> ?.
    have->: (n = 0) by math.
    xin 1: xwp; xapp.
    xin 1: xwp; xval.
    xin 2: xwp; xapp; rewrite -/pow_aux.
    xin 2: xwp; xif=> // _; rewrite -/pow_aux.
    xin 2: do 5? (xwp; xapp); rewrite -/pow_aux.
    xin 2: xwp; xif=> // ?; try (exfalso; math).
    xin 2: xwp; xapp.
    xin 2: xwp; xval.
    xsimpl*. }
  move=> ?.
  xin 2: xwp; xapp; rewrite -/pow_aux.
  xin 2: xwp; xif=> ?; try (exfalso; math).
  xin 2 1 : do 4? (xwp; xapp); rewrite -/pow_aux.
  replace (n + 1 - 1) with (n - 1 + 1); last math.
  rewrite hstar_comm.
  apply/(IH (n - 1) _ (fun d => s d * d)); try math.
  { move=> ? /[dup]/H'. math. }
  have: ((Σ_(j <- [0,i]) s j) * i <= v * i * i)%Z.
  apply/Zmult_le_compat_r=> //.
  apply/Z.le_trans. 
  rewrite Distr.
  apply/Monot=> ? /[! int0iH] -[??].
  apply/Z.mul_le_mono_nonneg_l; eauto.
Qed.

Lemma htriple_pow_times n :
  {{ \[n>=0] }}
    [{ 
      [1| ld in [0,i] => pow ld n ];
      [2| ld in {::i} => pow ld (n+1)%Z ]
    }] 
  {{ v , \[Σ_(j <- [0,i]) v[1](j) <= v[2](i)] \* \Top }}.
Proof.
  xnsimpl=> ?.
  xin 2: xwp; xapp=> p; rewrite -/pow_aux.
  xin 1: xwp; xapp=> q; rewrite -/pow_aux.
  rewrite hstar_comm.
  apply (htriple_pow_times_aux (fun _ => 1)); try math.
  rewrite Const; math.
Qed.
  
End pow.
End Pow1.

(* ----------------------------------------------------------------- *)
(** *** Definition and Verification of [incr]. *)

(** Here is an implementation of the increment function,
    written in A-normal form.

OCaml:

   let incr p =
       let n = !p in
       let m = n + 1 in
       p := m

The notation ['p] stands for [("x":var)]. It is defined in [LibSepVar.v]. *)

Definition incr : D -> val := fun d => 
  let s := length d in
  <{ fun 'p =>
     let 'n = ! 'p in
     let 'm = 'n + s in
     'p := 'm;
     'p := 'm }>.

(** Here is the Separation Logic htriple specifying increment.
    And the proof follows. Note that the script contains explicit
    references to the specification lemmas of the functions being
    called (e.g. [htriple_get] for the [get] operation). The actual
    CFML2 setup is able to automatically infer those names. *)

Arguments subst /.

Opaque wpgen.

Lemma htriple_incr fs : forall (p:loc) (n:int),
  htriple fs (fun d => incr d p)
    (\*_(d <- fs) p ~(d)~> n)
    (fun _ => \*_(d <- fs) p ~(d)~> (n + length d)).
Proof using.
  xwp; xapp. 
  xwp; xlet. 
  xwp; xapp. 
  xwp; xapp. 
  xapp. 
  xsimpl*.
Qed.

Definition pow : D -> val 

(** We register this specification so that it may be automatically invoked
    in further examples. *)

Hint Resolve htriple_incr : htriple.

(** Alternative definition using variable names without quotes, obtained
    by importing the module [Vars] from [LibSepVar.v]. *)

Module Export Def_incr. Import Vars.

Definition incr' : val :=
  <{ fun p =>
       let n = ! p in
       let m = n + 1 in
       p := m }>.

End Def_incr.

Lemma htriple_incr' : forall (p:loc) (n:int),
  htriple (fun d => incr' p)
    (p ~~> n)
    (fun _ => (p ~~> (n+1))).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl*.
Qed.

(* ================================================================= *)
(** ** The Decrement Function *)

Definition decr : val :=
  <{ fun 'p =>
       let 'n = ! 'p in
       let 'm = 'n - 1 in
       'p := 'm }>.

Module Export Def_decr. Import Vars.

Definition decr : val :=
  <{ fun p =>
       let n = !p in
       let m = n - 1 in
       p := m }>.

End Def_decr.

Lemma htriple_decr : forall (p:loc) (n:int),
  htriple (fun d => trm_app decr p)
    (p ~~> n)
    (fun _ => p ~~> (n-1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl*.
Qed.

Hint Resolve htriple_decr : htriple.

(* ----------------------------------------------------------------- *)
(** *** Definition and Verification of [mysucc]. *)

(** Another example, involving a call to [incr]. *)

Module Export Def_mysucc. Import Vars.

Definition mysucc : val :=
  <{ fun n =>
       let r = ref n in
       incr r;
       let x = !r in
       free r;
       x }>.

End Def_mysucc.

Lemma htriple_mysucc : forall n,
  htriple (fun d => trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  xwp. xapp. intros r. xapp. xapp. xapp. xval. xsimpl. auto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Definition and Verification of [myrec]. *)

(** Another example, involving a function involving 3 arguments, as
    well as record operations.

OCaml:

   let myrec r n1 n2 =
      r.myfield := r.myfield + n1 + n2
*)

Definition myfield : field := 0%nat.

Module Export Def_myrec. Import Vars.

Definition myrec : val :=
  <{ fun p n1 n2 =>
       let n = (p`.myfield) in
       let m1 = n + n1 in
       let m2 = m1 + n2 in
       p`.myfield := m2 }>.

Lemma htriple_myrec : forall (p:loc) (n n1 n2:int),
  htriple (fun d => myrec p n1 n2)
    (p ~~~> `{ myfield := n})
    (fun _ => p ~~~> `{ myfield := (n+n1+n2) }).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xsimpl.
Qed.

End Def_myrec.

(* ----------------------------------------------------------------- *)
(** *** Definition and Verification of [myfun]. *)

(** Another example involving a local function definition. *)

Module Export Def_myfun. Import Vars.

Definition myfun : val :=
  <{ fun p =>
       let f = (fun_ u => incr p) in
       f();
       f() }>.

End Def_myfun.

Lemma htriple_myfun : forall (p:loc) (n:int),
  htriple (fun d => myfun p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun (fun (f:val) => forall (m:int),
    htriple (fun d => f())
      (p ~~> m)
      (fun _ => p ~~> (m+1))); intros f Hf.
  { intros. applys Hf. clear Hf. xapp. xsimpl. }
  xapp.
  xapp.
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.

End DemoPrograms.

(* 2023-03-25 11:36 *)
