From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.
Require Import Wellfounded.

Set Warnings "-notation-overridden".
Require Import R_subsets.
Set Warnings "+notation-overridden".
Require Import Derive.

Open Scope R_scope.

Module private.

(* This lemma could be used to automatically prove that functions
  defined by our new command satisfy the specification that was given
  as a definition.  This lemma is not intended for final users' eyes
  because it exposes the nat type. We may want to add a pre-condition
  to restrict usage to the Rnat subset.  It is not certain this
  lemma will be used much, since unfold does the same trick.
  *)
Lemma Rnat_rec_to_nat_rec_p {A : Type} (v0 : A) (stf : R -> A -> A)
  (p : positive) :
   Rnat_rec v0 stf (IZR (Z.pos p)) =
   nat_rect (fun _ => A) v0 (fun x => stf (INR x))
     (Z.abs_nat (Z.pos p)).
Proof.
unfold Rnat_rec, IRN.
now rewrite IRZ_IZR.
Qed.

Lemma IRN_to_S (r : R) (p : Z) (q : Z):
  (q < p)%Z ->
  Rnat (r - IZR p) -> IRN (r - IZR q) =
     (Z.abs_nat (p - q) + IRN (r - IZR p))%nat.
Proof.
intros qltp rmpnat.
unfold IRN.
destruct (Rnat_exists_nat (r - IZR p)) as [v vq].
assert (rq : r = IZR (Z.of_nat v + p)).
  apply (Rplus_eq_reg_r (- (IZR p))).
  rewrite <- opp_IZR at 2.
  rewrite <- plus_IZR.
  replace (Z.of_nat v + p + - p)%Z with (Z.of_nat v) by ring.
  exact vq.
rewrite <- Zabs2Nat.inj_add.
    rewrite rq.
    rewrite <- minus_IZR, IRZ_IZR.
    rewrite <- minus_IZR.
    replace (Z.of_nat v + p - p)%Z with (Z.of_nat v) by ring.
    rewrite IRZ_IZR.
    apply f_equal.
    ring.
  lia.
rewrite vq, IRZ_IZR.
apply Nat2Z.is_nonneg.
Qed.

Lemma IRN_to_S_top (r : R) (p : Z) :
  (0 < p)%Z ->
  Rnat (r - IZR p) -> IRN r = (Z.abs_nat p + IRN (r - IZR p))%nat.
Proof.
intros pgt0 rmpnat.
unfold IRN.
destruct (Rnat_exists_nat (r - IZR p)) as [v vq].
  assert (rq : r = IZR (Z.of_nat v + p)).
  apply (Rplus_eq_reg_r (- (IZR p))).
  rewrite <- opp_IZR at 2.
  rewrite <- plus_IZR.
  replace (Z.of_nat v + p + - p)%Z with (Z.of_nat v) by ring.
  exact vq.
rewrite <- Zabs2Nat.inj_add.
    rewrite rq.
    rewrite <- minus_IZR, IRZ_IZR.
    replace (Z.of_nat v + p - p)%Z with (Z.of_nat v) by ring.
    rewrite IRZ_IZR.
    apply f_equal.
    ring.
  lia.
rewrite vq, IRZ_IZR.
apply Nat2Z.is_nonneg.
Qed.

Lemma Rnat_Rabs {f : R -> R} {fz : Z -> Z}
  (abs_morph : forall n z, n = IZR z -> f (Rabs n) = IZR (fz z))
  (n : R) (z : Z) (nnat : Rnat n) (nz : n = IZR z) : f n = IZR (fz z).
Proof.
rewrite <- (Rabs_right n);[ | assert (tmp := Rnat_ge0 n nnat); lra].
now apply abs_morph.
Qed.


Lemma nat_rect_transfer {A B : Type} (rel : A->B->Prop)
(va : A) (vb : B) (fa : nat-> A -> A) (fb : nat -> B -> B) :
rel va vb -> (forall n ua ub, rel ua ub -> rel (fa n ua) (fb n ub)) ->
forall n, rel (nat_rect (fun _ : nat => A) va fa n) (nat_rect (fun _ : nat => B) vb fb n).
intros base IH.
induction n as [|n IHn].
  simpl.
  exact base.
simpl.
apply IH.
apply IHn.
Qed.

Lemma nat_rect_list_IZR (l0 : list Z) 
  (l' : list R) (f : nat -> list Z -> list Z)
  (f' : nat -> list R -> list R)
  (n : nat) :
  l' = map IZR l0 ->
  (forall k lR lZ, lR = map IZR lZ ->
        f' k lR = map IZR (f k lZ)) ->
  nat_rect (fun _ => list R) l' f' n =
  map IZR (nat_rect (fun _ => list Z) l0 f n).
Proof.
intros ll' ff'.
apply (nat_rect_transfer (fun x y => x = map IZR y)); auto.
Qed.



Lemma Rnat_rec_nat (l0 : list R) (f : R -> list R -> list R) (n : R) :
  Forall Rnat l0 ->
  (forall n l, Rnat n -> Forall Rnat l -> Forall Rnat (f n l)) ->
  Rnat n -> Forall Rnat (Rnat_rec l0 f n).
Proof.
intros ln fn.
induction 1 as [ | n nnat Ih].
  now rewrite Rnat_rec0.
rewrite Rnat_rec_succ;[ | assumption].
now apply fn.
Qed.

Lemma Rnat_rec_nat' (l0 : list R) (f : R -> list R -> list R) :
  (forall k, Rnat (nth k l0 0)) ->
  (forall n l, (forall k, Rnat (nth k l 0)) ->
     Rnat n -> (forall k, Rnat (nth k (f n l) 0))) ->
  forall n, Rnat n -> (forall k, Rnat (nth k (Rnat_rec l0 f n) 0)).
Proof.
intros l0nat fnat m mnat.
induction mnat as [ | n nnat Ih].
  unfold Rnat_rec; rewrite IRN0.
  exact l0nat.
rewrite Rnat_rec_succ;[ | assumption].
apply fnat;[ | assumption].
exact Ih.
Qed.

Lemma IZR_map1 : forall opr opz,
  (forall a, opr (IZR a) = IZR (opz a)) ->
  forall a b, a = IZR b -> opr a = IZR (opz b).
Proof.
intros opr opz morph a b ab.
now rewrite ab, morph.
Qed.

Lemma IZR_map1' {opr} {opz} : 
  (forall a, opr (IZR a) = IZR (opz a)) ->
  forall a b, a = IZR b -> opr a = IZR (opz b).
Proof.
intros morph a b ab.
now rewrite ab, morph.
Qed.

(* This may be dead code. *)
Lemma IZR_map1_abs : forall opr opz,
  (forall x y, x = IZR y -> opr (Rabs x) = IZR (opz y)) ->
  forall a b, a = IZR b -> opr (Rabs a) = IZR (opz b).
Proof.
intros opr opz pmorph; exact pmorph.
Qed.

Lemma Zabs_nat_Zabs_involutive (f : nat -> Z) z :
  f (Z.abs_nat (Z.abs z)) = f (Z.abs_nat z).
Proof.
now unfold Z.abs, Z.abs_nat; destruct z.
Qed.

Lemma IZR_map2 : forall opr opz,
  (forall a b, opr (IZR a) (IZR b) = IZR (opz a b)) ->
  forall a b c d, a = IZR c -> b = IZR d ->
  opr a b = IZR (opz c d).
Proof.
intros opr opz morph a b c d ac bd.
now rewrite ac, bd, morph.
Qed.

Lemma IZR_map3 : forall opr opz,
  (forall a b c, opr (IZR a) (IZR b) (IZR c)= IZR (opz a b c)) ->
  forall a b c d e f, a = IZR d -> b = IZR e -> c = IZR f ->
  opr a b c = IZR (opz d e f).
Proof.
intros opr opz morph a b c d e f ad be cf.
now rewrite ad, be, cf, morph.
Qed.

Lemma IZR_map4 : forall opr opz,
  (forall a b c d, opr (IZR a) (IZR b) (IZR c) (IZR d)= IZR (opz a b c d)) ->
  forall a b c d e f g h, a = IZR e -> b = IZR f -> c = IZR g -> d = IZR h ->
  opr a b c d = IZR (opz e f g h).
Proof.
intros opr opz morph a b c d e f g h ae bf cg dh.
now rewrite ae, bf, cg, dh, morph.
Qed.

Lemma nth_map {A B : Type} (da : A) (db : B) (f : A -> B) (la : list A)
  (lb : list B) (k : nat):
  db = f da ->
  lb = map f la ->
  nth k lb db = f (nth k la da).
Proof.
  Check map_nth.
intros dq lq; rewrite dq, lq; apply map_nth.
Qed.

Lemma IRN_Z_abs_nat n z : n = IZR z -> IRN (Rabs n) = Z.abs_nat z.
Proof.
intros nzq; unfold IRN.
destruct (Rle_or_lt 0 n).
  rewrite Rabs_right;[ | lra].
  now rewrite nzq, IRZ_IZR.
rewrite Rabs_left;[ | lra].
rewrite nzq, <- opp_IZR, IRZ_IZR.
now destruct z.
Qed.

Lemma INR_Z_abs_nat n z : n = IZR z -> Rabs n = INR (Z.abs_nat z).
Proof.
intros nzq.
rewrite nzq.
rewrite <- abs_IZR.
rewrite INR_IZR_INZ.
now rewrite Nat2Z.inj_abs_nat.
Qed.

Lemma cancel_Rabs_pos (f : R -> R) (fz : Z -> Z):
  (forall (n : R) (z : Z), n = IZR z ->
     f (Rabs n) = IZR (fz z)) ->
  forall p : positive,
    f (IZR (Z.pos p)) = IZR (fz(Z.pos p)).
Proof.
intros morph p.
rewrite <- (morph _ _ eq_refl).
now rewrite <- abs_IZR.
Qed.

Lemma cancel_Rabs_pos2 (f : R -> R -> R) (fz : Z -> Z -> Z):
  (forall (n : R) (z : Z), n = IZR z ->
   forall (m : R) (y : Z), m = IZR y ->
     f (Rabs n) m = IZR (fz z y)) ->
  forall (p  : positive) (m:R) (y:Z), m=IZR y ->
    f (IZR (Z.pos p)) m = IZR (fz(Z.pos p) y).
Proof.
intros morph p m y my.
rewrite <- (morph _ _ eq_refl _ _ my).
now rewrite <- abs_IZR.
Qed.

Lemma cancel_Rabs_0 (f : R -> R) (fz : Z -> Z):
  (forall (n : R) (z : Z), n = IZR z ->
    f (Rabs n) = IZR (fz z)) ->
    f 0 = IZR (fz 0%Z).
Proof.
intros morph; rewrite <- (morph _ _ eq_refl).
now rewrite <- abs_IZR.
Qed.

Lemma compute_Rnat (n : R) (z : Z) : n = IZR z ->
  (0 <=? z)%Z = true -> Rnat n.
Proof.
intros nzq cmp.
apply Rint_Rnat.
  now rewrite nzq; apply Rint_Z.
rewrite nzq.
apply IZR_le.
now rewrite (Zle_is_le_bool 0).
Qed.


End private.

Ltac prove_recursive_specification T Order := unfold T;
  repeat split;
  (* The first now clause attempts to prove the base cases. *)
    (now (rewrite Rnat_rec0 || rewrite private.Rnat_rec_to_nat_rec_p)) ||
    (let N := fresh "n" in let Nnat := fresh "nnat" in
     let Protector := fresh "protect_base" in
     unfold Rnat_rec; intros N Nat;
     set (Protector := IRN (N - IZR Order));
     repeat (rewrite (private.IRN_to_S N Order);[ | reflexivity | assumption]);
     rewrite (private.IRN_to_S_top N Order);[ | reflexivity | assumption];
     (reflexivity (* useful when N is only used in recursive calls*) ||
       (simpl;
        let Last_eqn := fresh "H" in
        enough (Last_eqn : INR (IRN (N - IZR Order)) + IZR Order = N)
            by (rewrite Last_eqn; reflexivity);
            rewrite INR_IRN;[ring | assumption]))).
Fixpoint ty_R (n : nat) : Type := 
  match n with
   0 => R
  | S p => (R -> ty_R p)
  end.

Fixpoint id_R (n : nat) : (ty_R n):= 
  match n with
   0 => 0%R
  | S p => (fun k => (id_R p))
  end.

Fixpoint ty_Z (n : nat) : Type := 
  match n with
   0 => Z
  | S p => (Z -> ty_Z p)
  end.

Fixpoint id_Z (n : nat) : (ty_Z n):= 
  match n with
   0 => 0%Z
  | S p => (fun k => (id_Z p))
  end.


Definition P_trans1 (l : list (R -> R)) (f : Z -> R) (l' : list (Z->Z)) :=
forall i : nat, forall x : Z, nth i l (id_R 1) (f x) = f (nth i l' (id_Z 1) x).

Definition P_trans1' (l : list (R -> R)) (f : Z->R) (l' : list (Z->Z)) :=
forall (i : nat) (x : Z) (y : R), y = (f x) -> nth i l (id_R 1) y = f (nth i l' (id_Z 1) x).

Lemma trf_trans : forall l f l', P_trans1 l f l' -> P_trans1' l f l'.
Proof.
  intros l f l'.
  unfold P_trans1.
  unfold P_trans1'.
  intros H i x y xy.
  rewrite xy.
  apply H.
Qed.

Lemma trf_trans_rev : forall l f l', P_trans1 l f l' <-> P_trans1' l f l'.
Proof.
  intros l f l'.
  unfold P_trans1.
  unfold P_trans1'.
  split.
  intros H i x y xy.
  rewrite xy.
  apply H.
  intros H i x.
  apply H.
  reflexivity.
Qed.

Lemma fun1_trf (g : R -> R) (g' : Z -> Z) (f : Z -> R) : 
(forall x, g (f x) = f (g' x)) <-> (forall x y, x = (f y) -> (g x) = f (g' y)).
Proof.
  split.
    intros H x y xy.
    rewrite xy.
  apply H.
  intros H x.
  apply H.
  reflexivity.
Qed.


Lemma P_trans1_nil :  P_trans1 nil IZR nil.
unfold P_trans1.
destruct i as [|i].
intros.
reflexivity.
intros.
reflexivity.
Qed.

Lemma P_trans1_cons A A' B B': (forall x, A (IZR x) = IZR (A' x)) -> P_trans1 B IZR B' -> P_trans1 (cons A B) IZR (cons A' B').
Proof.
  unfold P_trans1.
  intros Aeq PtB i z.
  case i.
    now simpl.
  simpl.
  intro n.
  apply PtB.
Qed.



Lemma nth_overflow_1 A A' p x : nth (S p) (A::nil) (id_R 1) (IZR x) = IZR (nth (S p) (A'::nil) (id_Z 1) x).
case p.
reflexivity.
reflexivity.
Qed.

(* Lemma prf_if a az b bz c cz : a = IZR A ->  *)

Lemma nat_rect_list :
  forall (l0 : list (Z->Z)) (l' : list (R->R))
    (f : nat -> list (Z->Z) -> list (Z->Z))
    (f' : nat -> list (R->R) -> list (R->R))
    (n : nat),
    P_trans1 l' IZR l0 ->
    (forall n lr lz, P_trans1 lr IZR lz -> 
        P_trans1 (f' n lr) IZR (f n lz)) ->
    P_trans1 (nat_rect (fun _ : nat => list (R->R)) l' f' n) 
             IZR 
             (nat_rect (fun _ : nat => list (Z->Z)) l0 f n).
Proof.
  intros l0 l' f f' n H H'.
  apply (private.nat_rect_transfer (fun x y => P_trans1 x IZR y)); auto.
Qed. 


Elpi Command Recursive.

Elpi Accumulate lp:{{

pred type_to_nargs i:term, o:int.

type_to_nargs (prod _ _ c\T) N1 :-
  !, type_to_nargs T N, N1 is N + 1.

type_to_nargs {{R}} 0.

pred nargs_to_def_val i:int, o:term.

nargs_to_def_val N {{id_R lp:NasNat}} :-
int_to_nat N NasNat.

% sorting a list of integers removing duplicates
pred list_insert i:int, i:list int, o:list int.

list_insert I [] [I].

list_insert A [A | L] [A | L] :- !.

list_insert I [A | L] [I, A | L] :-
  I < A, !.

list_insert I [A | L] [A | L1] :-
  list_insert I L L1, !.
  
% sorting a list of integers: the main predicate

pred list_sort i:list int, o:list int.
list_sort [] [].

list_sort [A | L] L1 :-
  list_sort L L2, !,
  list_insert A L2 L1.

pred list_max i:list int o:int.
list_max [A] A.

list_max [A, B | L]  V:-
  A < B, !, list_max [B | L] V.

list_max [A, _B | L] V :-
  list_max [A | L] V.

% sorting an association list for values associated to integers

pred alist_insert i:pair int term, i:list (pair int term),
  o:list (pair int term).

alist_insert (pr I _) [pr I _ | _] _ :- !,
  coq.error "There are two declarations for the same integer"  I.

alist_insert (pr I V) [pr I2 V2 | L] [pr I V, pr I2 V2 | L] :-
  I < I2, !.

alist_insert (pr I V) [pr I2 V2 | L] [pr I2 V2 | L2] :-
  alist_insert (pr I V) L L2.

alist_insert (pr I V) [] [pr I V].

pred alist_sort i:list (pair int term), o:list (pair int term).

alist_sort [] [].

alist_sort [A | L] L2 :-
  alist_insert A L L2.

% converting a coq object of type positive to a builtin int
pred positive_to_int i:term, o:int.
% TODO regarder dans algebra tactics
positive_to_int {{xH}} 1 :- !.

positive_to_int {{:coq xI lp:X}} N1 :-
  positive_to_int X N,
  N1 is 2 * N + 1.

% TODO
positive_to_int {{xO lp:X}} N1 :-
  positive_to_int X N,
  N1 is 2 * N.

% converting a real number to an int
pred real_to_int i:term, o:int.

% actually, this works for any positive number encapsulated in two unary
% functions
real_to_int {{IZR (Z.pos lp:P)}} I :-
  positive_to_int P I.

real_to_int {{0}} 0.

% the inverse predicate, int_to_real, produces a real number that is
% the representation of the integer.

pred int_to_real i:int, o:term.

int_to_real I {{IZR lp:Iz}} :-
  int_to_Z I Iz.

pred int_to_Z i:int, o:term.
int_to_Z 0 {{Z0}} :- !.

int_to_Z I {{Z.pos lp:Ip}} :-
  int_to_positive I Ip.

pred int_to_positive i:int, o:term.
int_to_positive 1 {{xH}}:- !.

int_to_positive N (app[C, Td]) :-
  1 < N,
  Nd is N div 2,
  B is N mod 2,
  choose_pos_constructor.aux B C,
  int_to_positive Nd Td.

pred int_to_nat i:int, o:term.
int_to_nat 0 {{O}} :- !.

int_to_nat N {{S lp:N'}} :-
  std.do! [
    0 < N,
    N1 is N - 1,
    int_to_nat N1 N'
  ].
  
pred choose_pos_constructor.aux i:int, o:term.

choose_pos_constructor.aux 1 {{xI}} :- !.

choose_pos_constructor.aux 0 {{xO}} :- !.

choose_pos_constructor.aux _ _ :-
  coq.error "choose_pos_constructor.aux only accepts 0 or 1 as input".


pred replace_rec_call_by_seq_nth i:term, i:term, i:int, i:term, i:term, i:term ,i:term,
  o:term.

% replace (F (N - k)) by (nth (L - k) V 0) everywhere in term A
% But the subtraction (L - k) is actually computed and a number of type nat,
% while (N - k) is a term representing a subtraction, where k is a
% positive integer constant of type R

replace_rec_call_by_seq_nth VTy Def L F N V A B :-
  std.do! [
    A = app[F, app [{{Rminus}}, N, K]|Args ] ,
    real_to_int K Kn,
    In is L - Kn,
    int_to_nat In I,
    B = app[{{@nth}}, VTy, I, V, Def|Args]
  ].

pred make_one_spec i:term, i:term, o:pair int term.
make_one_spec V1 V2 (pr I1 V2) :-
  real_to_int V1 I1,!.

pred list_app i:list (pair int term), i:list (pair int term),
  o:list (pair int term).

list_app [] L2 L2.

list_app [A | L1] L2 [A | L3] :-
  list_app L1 L2 L3.

pred fetch_recursive_equation i:term, o:list term.

fetch_recursive_equation X [X] :-
  X = (prod _ _ _), !.

fetch_recursive_equation (app [And, Code1, Code2]) R_eqs :-
  std.do! [
    coq.locate "and" Andgref,
    And = global Andgref,
    fetch_recursive_equation Code1 L1,
    fetch_recursive_equation Code2 L2,
    std.append L1 L2 R_eqs
  ].

fetch_recursive_equation {{lp:_ = lp: _}} [].

fetch_recursive_equation A _ :-
  coq.say "wrong term" A,
  coq.error "expecting function specification to be a conjunction of"
   "formulas of the form f 0 = v1 f 1 = v2  or forall n, .. -> f n = V2"
   "but found expressions of another form".

pred collect_base_specs i:term, i:term, o:list (pair int term).

collect_base_specs F {{lp:F lp:V1 = lp:V2}} [S] :-
  std.do! [
    make_one_spec V1 V2 S
  ].

collect_base_specs _F (prod _ _ _) [].

collect_base_specs F {{lp:Code1 /\ lp:Code2}} Specs :-
  std.do! [
    collect_base_specs F Code1 Specs1,
    collect_base_specs F Code2 Specs2,
    std.append Specs1 Specs2 Specs
  ].

pred check_all_present i:int, i:list (pair int term), o:int.

check_all_present N [] N.

check_all_present N [pr N _ | L] N2 :-
  !,
  N1 is N + 1,
  check_all_present N1 L N2.

check_all_present N [pr _ _ | _] _ :-
  coq.error "missing value for" N.


pred make_initial_list i:term, i:list (pair int term), o:term.

make_initial_list T [] {{ @nil lp:T}}.

make_initial_list T [(pr  _ V) | L] (app [{{ @cons lp:T}}, V, Tl]) :-
  make_initial_list T L Tl, std.assert-ok! (coq.typecheck Tl _) "constructed a bad initial list".

pred make_recursive_step_list i:term, i:term, i:(term -> term), i:int, i:int,
   o:(term -> term).

make_recursive_step_list Ty _ZTy Func 0 _Rank R :-
  pi V\
   app [{{ @cons }}, Ty, (Func V), {{ @nil lp:Ty}}] = R V.

make_recursive_step_list Ty ZTy Func N Rank R :-
  std.do! [
    0 < N,
    N1 is N - 1,
    Rank1 is Rank + 1,
    int_to_nat Rank1 RankTerm,
    make_recursive_step_list Ty ZTy Func N1 Rank1 Func',
    pi V \
      app [{{ @cons}}, Ty, app [ {{ @nth}}, Ty, RankTerm, V, ZTy],
           Func' V] = R V
  ].

pred shift_real i:int, i:term, o:term.

shift_real 0 N N.

shift_real K N {{lp:N + lp:K_as_real}}:-
  std.do! [
    0 < K,
    int_to_real K K_as_real].

% QUIRKY: performs part of the jobs of finding the uses of the function
% given as second argument inside the fourth argument.
% The fourth argument has to be a sequence of nested implications whose
% conclusion is an equality.  The instances we are looking for have to be
% of the form (F (n - k)).  The k values must be real-positive numbers.
% The first argument is the depth of the recursion, The third argument
% is the numeric variable used for recursion.
pred eat_implications i:term, i:term, i:term, o:term.

eat_implications F N (prod _ _ G) R :-
  %(pi x\ not(occurs x (G x))),
  (pi x y\ G x = G y), !,
  pi h \ 
   eat_implications F N (G h) R.

eat_implications F N {{lp:F lp:N = lp:RHS}} RHS.

pred translate_recursive_body i:int, i:term, i:term, i:term, i:term, i:term, o:term.

translate_recursive_body Order F VTy DefN N RHS R :-

std.do! [
      % This should recognize (f (n - k)) and store k in the list
  (pi A E Op V Args\
         %         fold-map (app [F, app[Op, V, E]]) A
                  %                 (app [F, app[Op, V, E]]) [E | A]
    fold-map (app [F, app[Op, V, E]|Args]) A
    (app [F, app[Op, V, E]|Args])[E | A])
  =>
    fold-map RHS [] _ Uses,
  std.map Uses (real_to_int) Uses_int,
% TODO: just take the last element, or avoid sorting
  list_max Uses_int MaxUses,
% Need to generate an abstraction that gives the name V to
% the result of the recursive call
  std.assert! (MaxUses =< Order)
  "The number of base values does not match the depth of recursive calls",
  shift_real Order N N_plus_Order,
     (pi L \
      ((pi A B \ copy A B :-
         replace_rec_call_by_seq_nth VTy DefN MaxUses F N L A B),
       copy N N_plus_Order) =>
    copy RHS (RHS' L)),
    Order1 is Order - 1,
    make_recursive_step_list VTy DefN RHS' Order1 0 RecList,
    R = (fun `v` {{list lp:VTy}} RecList)
].

% The input must have the form:
%  fun f => f 0 = V1 /\ ... f k = Vk /\ forall n, ... -> ... -> f n = E
% Displays the ordered sequence of k integers (in builtin type int), such
% that (f (n - k)) appears in E.
pred find_uses i:term, o:term, o:term.

find_uses (fun N Ty Bo) R Order_Z :-
  pi arg\
    decl arg N Ty => % let one call the pretty printer and type checker inside
    find_uses_of Ty arg (Bo arg) R Order_Z. 
                              % R does not use f recursively, but rather
                              % the value of its recursion history at depth
                              % Order_Z (which must be a cic term of type Z)

pred find_uses_of i:term, i:term, i:term, o:term, o:term.

find_uses_of Ty F Spec Final Order_Z :-
  std.do! [
    collect_base_specs F Spec Sps,
    alist_sort Sps Sps2,
    Ty = prod _ _Ty' (c0\ T2),
    check_all_present 0 Sps2 Order,
    make_initial_list T2 Sps2 ListSps,
    fetch_recursive_equation Spec Ts,

  type_to_nargs T2 Nargs,
  nargs_to_def_val Nargs DefN,
% TODO : error reporting is not satisfactory here
    std.assert! (Ts = [prod Scalar_name Sc_type F1])
       "Expecting exactly one recursive equation",
    (pi n\
      decl n Scalar_name Sc_type =>
      (eat_implications F n (F1 n) (Body n),
      translate_recursive_body Order F T2 DefN n (Body n) (Main_expression n))),
    %Final = {{Rnat_rec lp:ListSps (fun x : R => lp:(Main_expression x)) }},
    Final = {{ fun r : R => @nth lp:T2 0 
                (@Rnat_rec (list lp:T2) lp:ListSps lp:{{ fun Scalar_name {{R}}
                              Main_expression}} r) lp:DefN}},
    int_to_Z Order Order_Z
  ].


pred make_eqn_proof i:Name, i:term, i:term, i:constant.

make_eqn_proof N_id Abs_eqn  Order C :-
std.do![
  Abs_eqn = fun _ _ F,
  Statement = (F (global (const C))),
  Eqs_N_id is N_id ^ "_eqn",
  coq.typecheck Eq_prf Statement ok,
  coq.ltac.collect-goals Eq_prf [G1] _ShelvedGs,
  coq.ltac.open(coq.ltac.call
    "prove_recursive_specification"
    [trm (global (const C)), trm Order]) G1 [],
  coq.env.add-const Eqs_N_id Eq_prf _ @opaque! _C_eqn,
  coq.say "Defined" Eqs_N_id].

make_eqn_proof _ _ _ _ :-
  coq.say "proof of equations failed".

main [trm (fun N Ty _ as Abs_eqn)] :-
std.do! [
  find_uses Abs_eqn Final Order,
  std.assert-ok! (coq.typecheck Final Ty) "Type error",
  coq.name->id N N_id,
  
  coq.env.add-const N_id Final Ty @transparent! C,
  coq.say "Defined" N_id,

   make_eqn_proof N_id Abs_eqn Order C
].

main _L :-
  coq.error [] "Usage: Recursive name equation_1 /\ .. /\ equation_n".

}}.

Elpi Typecheck.
Elpi Export Recursive.

  

Notation "'def' id 'such' 'that' bo" := (fun id => bo) 
 (id binder, bo at level 100, at level 1, only parsing).


Ltac rec_Rnat fun_name :=
(* This tactic is only meant to be used on statements of the form:
  Rnat x -> Rnat (fun_name x)
  where fun_name was defined using the Recursive command.  It succeeds
  if all operations that appear in the body of the definition are
  known to preserve membership in Rnat. *)
  let Nnat := fresh "nnat" in
  let M := fresh "m" in
  let L := fresh "l" in
  let Lnat := fresh "lnat" in
  let Mnat := fresh "mnat" in
  intros nnat;
  unfold fun_name;
  apply private.Rnat_rec_nat';[
    repeat ((intro; apply Rnat0)||(
             intros [ | k];[typeclasses eauto | revert k; cbn [nth]]
    )) |
    intros M L Lnat Mnat;
     repeat ((intro; apply Rnat0)||(
             intros [ | k];[typeclasses eauto | revert k; cbn [nth]]
    )) | assumption].



(* Elpi Trace Browser. *)
