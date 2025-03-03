From elpi Require Import elpi.
Require Import List Reals ClassicalEpsilon Lia Lra.

#[local]
Set Warnings "-notation-overridden".

Require Import R_subsets rec_def.

#[local]
Set Warnings "+notation-overridden".

Open Scope R_scope.

Lemma add_compute : forall x y, Rplus (IZR x) (IZR y) = IZR (Z.add x y).
Proof.
exact (fun x y => eq_sym (plus_IZR x y)).
Qed.

Lemma mul_compute : forall x y, Rmult (IZR x) (IZR y) = IZR (Z.mul x y).
Proof.
exact (fun x y => eq_sym (mult_IZR x y)).
Qed.

Lemma sub_compute : forall x y, Rminus (IZR x) (IZR y) = IZR (Z.sub x y).
Proof.
exact (fun x y => eq_sym (minus_IZR x y)).
Qed.

Lemma opp_compute : forall x, Ropp (IZR x) = IZR (Z.opp x).
Proof.
exact (fun x => eq_sym (opp_IZR x)).
Qed.

Lemma Zeq_bool_IZR_neq x y : (IZR x) <> (IZR y)  -> x <> y.
Proof.
  intros H1 H2.
  apply H1.
  rewrite H2.
  reflexivity.
Qed.


Lemma abs_compute : forall x, Rabs (IZR x) = IZR (Z.abs x).
Proof.
exact (fun x => eq_sym (abs_IZR x)).
Qed.

Definition Req_bool (x y : R) := if (Req_dec_T x y) then true else false.
Notation "x =? y" := (Req_bool x y) : R_scope.

Lemma eq_bool_compute : forall x y, Req_bool (IZR x) (IZR y) = (Zeq_bool x y).
Proof.
  intros.
  unfold Req_bool.
  destruct Req_dec_T as  [eqR|neqR] .
    now rewrite (Zeq_bool_IZR x y).
  unfold Zeq_bool.
  apply Zeq_bool_IZR_neq in neqR.
  rewrite <- Z.eqb_neq in neqR.
  now rewrite <- Z.eqb_compare, neqR.
Qed.
(*
Lemma if_compute : (forall x y z, if
Search (if _ then _ else _ ). *)
Definition MyINR : N -> R :=
fun n => match n with
| 0%N => 0
| N.pos p => IZR (Z.pos p)
  end.

Definition at_x (a b c : R) := fun x => if (Req_bool x a) then b else (c).

Definition at_x_Z (a b c : Z) := fun x => if (Zeq_bool x a) then b else c.

Lemma at_x_compute : forall a b c x, at_x (IZR a) (IZR b) (IZR c) (IZR x) = IZR (at_x_Z a b c x).
Proof.
  intros.
  unfold at_x.
  unfold at_x_Z.
  rewrite <-eq_bool_compute.
  now destruct (Req_bool (IZR x) (IZR a)).
Qed.


Definition IZR2 (f : Z -> Z) :=
fun r : R =>
  IZR(f (IRZ r)).


Lemma nil_2 :  nil = @map (ty_Z 1) (ty_R 1) IZR2 nil.
Proof.
  unfold IZR2.
  now simpl.
Qed.

Definition nat1 := nat.

Elpi Db R_translate.db lp:{{
pred int_to_nat i:int, o:term.
int_to_nat 0 {{O}} :- !.

int_to_nat N {{S lp:N'}} :-
  std.do! [
    0 < N,
    N1 is N - 1,
    int_to_nat N1 N'
  ].
pred type_to_nargs i:term, o:int.

type_to_nargs (prod _ _ c\T) N1 :-
  !, type_to_nargs T N, N1 is N + 1.

type_to_nargs {{R}} 0.

pred translate_prf i:term, o:term, o:term.
pred main_translate_prf i:term, o:term, o:term.
pred thm_table o:term, o:term, o:term.
pred nat_thm_table o:term, o:term, o:term.

pred meta_list_to_list i:(list term), o: term.
meta_list_to_list nil {{nil}}.
meta_list_to_list uvar _ :- coq.error "invalid input meta_list_to_list called with flexible argument".
meta_list_to_list [A|Tl] {{lp:A::lp:R}} :- meta_list_to_list Tl R.

pred translate_args i:list term, o:list term, o:list term.
translate_args nil nil nil.
translate_args [R|Tl] [Z|TlZ] [Prf|PrfT] :-
translate_prf R Z Prf,
translate_args Tl TlZ PrfT.

pred say i:term.
say T :- coq.say {coq.term->string T}.

pred sayL i:list term.
sayL nil :- coq.say "nil".
sayL [A|Tl] :- std.do![say A, coq.say "::", sayL Tl].

translate_prf (fun N {{nat}} F) (fun N {{nat}} F1)
  T :-
  (pi CN \
    translate_prf {{INR lp:CN}} {{Z.of_nat lp:CN}} {{INR_IZR_INZ lp:CN}} =>
    translate_prf (F CN) (F1 CN) (PF CN)),
    T = (fun N {{nat1}} PF).

translate_prf (fun M {{R}} Bo) (fun M {{Z}} BoZ) Prf :-
  (pi V VZ H\
  (decl V M {{R}} ,
  translate_prf V VZ H) ==>
  translate_prf (Bo V) (BoZ VZ) (Pf V VZ H),
  Prf = {{fun (r : R) (z : Z) (h : r = IZR z) => lp:(Pf r z h)}}).

translate_prf (fun L {{list R}} F) (fun L {{list Z}} F1)
  PF0 :-
  (pi Cl1 Cl2 Hll \
    translate_prf Cl1 Cl2 Hll ==>
    translate_prf Cl1 Cl2 Hll ==>
    translate_prf (F Cl1) (F1 Cl2) (PF Cl1 Cl2 Hll)),
    PF0 = {{fun (lr : list (ty_R 0)) (lz : list Z)
      (h : lr = @map Z R IZR lz :> list (ty_R 0)) => lp:(PF lr lz h)}}.

translate_prf (fun L {{list (R -> R)}} F) (fun L {{list (Z -> Z)}} F1)
   PF0 :-
   (pi Cl1 Cl2 Hll L2 \
   (decl Cl1 L {{list (R -> R)}},
    decl Cl2 _ {{list (Z -> Z)}},
    decl Hll `IH` {{P_trans1 lp:Cl1 IZR lp:Cl2}},
     translate_prf Cl1 Cl2 Hll) =>
     translate_prf (F Cl1) (F1 Cl2) (PF Cl1 Cl2 Hll)),
     PF0 = {{fun (lr : list (R->R)) (lz : list (Z->Z))
       (h : P_trans1 lr IZR lz ) => lp:(PF lr lz h)}}.

translate_prf (fun L {{list (ty_R lp:N)}} F) (fun L {{list (ty_Z lp:N)}} F1)
   PF0 :-
   (pi Cl1 Cl2 Hll L2 \
   (decl Cl1 L {{list (ty_R lp:N)}},
    decl Cl2 _ {{list (ty_Z lp:N)}},
    decl Hll `IH` {{P_transN lp:N lp:Cl1 IZR lp:Cl2}},
     translate_prf Cl1 Cl2 Hll) =>
     translate_prf (F Cl1) (F1 Cl2) (PF Cl1 Cl2 Hll)),
     PF0 = {{fun (lr : list (ty_R lp:N)) (lz : list (ty_Z lp:N))
       (h : P_transN lp:N lr IZR lz ) => lp:(PF lr lz h)}}.

translate_prf {{nth lp:K lp:L (id_R 0)}} {{nth lp:K lp:Lz (id_Z 0)}}
  {{private.nth_map (id_Z 0) (id_R 0) IZR lp:Lz lp:L lp:K eq_refl lp:H}} :-
  translate_prf L Lz H.

translate_prf {{nth lp:K lp:L (id_R 1) lp:A_r}} {{nth lp:K lp:Lz (id_Z 1) lp:A_z}}
  {{(trf_trans lp:L IZR lp:Lz lp:H) lp:K lp:A_z lp:A_r lp:Pa}} :-
  translate_prf L Lz H,
  translate_prf A_r A_z Pa.

translate_prf {{@nil R}} {{@nil Z}} {{eq_refl : nil = @map Z R IZR nil}}.

translate_prf {{@nil (R->R)}} {{@nil (Z->Z)}} {{P_trans1_nil}}.

translate_prf {{@cons R lp:A lp:L}} {{cons lp:A1 lp:L1}}
  {{f_equal2 (@cons (ty_R 0)) lp:Pfa lp:Pfl}}:-
  std.do! [
    translate_prf A A1 Pfa,
    translate_prf L L1 Pfl
  ].

translate_prf {{cons lp:A lp:L}} {{cons lp:A1 lp:L1}}
  {{P_trans1_cons lp:A lp:A1 lp:L lp:L1 (proj2 (fun1_trf lp:A lp:A1 IZR) lp:Pfa) lp:Pfl}}:-
  std.do! [
    translate_prf A A1 Pfa,
    translate_prf L L1 Pfl
  ].

translate_prf {{IZR lp:A}} {{lp:A}} {{eq_refl: IZR lp:A = IZR lp:A}}.

translate_prf (app [F, {{Rabs lp:A}}]) (app [F1, A1])
  {{lp:PFF1 lp:A lp:A1 lp:PRFA}} :-
  std.do![
    nat_thm_table F F1 PFF1,
    translate_prf A A1 PRFA
  ].

translate_prf {{lp:F (IZR (Zpos lp:P))}}
  {{lp:Fz (Zpos lp:P)}}
  {{private.cancel_Rabs_pos lp:F lp:Fz lp:Prf lp:P}} :-
  nat_thm_table F Fz Prf.

translate_prf {{lp:F (IZR (Zpos lp:P)) lp:R}}
  {{lp:Fz (Zpos lp:P) lp:Z}}
  {{private.cancel_Rabs_pos2 lp:F lp:Fz lp:Prf lp:P lp:R lp:Z lp:PrfRZ}} :-
  translate_prf R Z PrfRZ,
  nat_thm_table F Fz Prf.

translate_prf (app [F, A]) (app [F1, A1])
  {{private.IZR_map1 lp:F lp:F1 lp:PFF1 lp:A lp:A1 lp:PFRA}} :-
  std.do! [
  thm_table F F1 PFF1,
  translate_prf A A1 PFRA
  ].

type marker int -> term.

translate_prf (app [F, A]) (app [F1, A1])
  {{private.Rnat_Rabs lp:PFF1 lp:A lp:A1 lp:Nat_prf lp:PRFA}} :-
  std.do![
    nat_thm_table F F1 PFF1,
    translate_prf A A1 PRFA,
    coq.typecheck Hole {{Rnat lp:A}} ok,
    coq.ltac.collect-goals Hole [G] [],
    if (coq.ltac.open (coq.ltac.call-ltac1 "solve_Rnat") G [])
       (Nat_prf = Hole)
       (
        Test = {{(0 <=? lp:A1)%Z}},
        coq.reduction.vm.norm Test _ Tv,
        if (Tv = {{false}})
          ( coq.reduction.vm.norm A1 _ V1,
            coq.term->string {{IZR lp:V1}} V1R,
            Diagnostic is
              {coq.term->string F} ^ " has a negative input "
              ^ V1R,
           coq.error Diagnostic)
          (GPRF = {{private.compute_Rnat lp:A lp:A1 lp:PRFA eq_refl}},
           Nat_prf = GPRF)
        )

  ].



translate_prf (app [F, A, B]) (app [F1, A1, B1])
  {{private.IZR_map2 lp:F lp:F1 lp:PFF1 lp:A lp:B lp:A1 lp:B1 lp:PFRA lp:PFRB}}
  :-
  std.do! [
  thm_table F F1 PFF1,
  translate_prf A A1 PFRA,
  translate_prf B B1 PFRB
  ].

translate_prf (app [F, A, B, C]) (app [F1, A1, B1, C1])
  {{private.IZR_map3 lp:F lp:F1 lp:PFF1 lp:A lp:B lp:C lp:A1 lp:B1 lp:C1 lp:PFRA lp:PFRB lp:PFRC}}
  :-
  std.do! [
  thm_table F F1 PFF1,
  translate_prf A A1 PFRA,
  translate_prf B B1 PFRB,
  translate_prf C C1 PFRC
  ].

translate_prf (app [F, A, B, C, D]) (app [F1, A1, B1, C1, D1])
  {{private.IZR_map4 lp:F lp:F1 lp:PFF1 lp:A lp:B lp:C lp:D lp:A1 lp:B1 lp:C1 lp:D1 lp:PFRA lp:PFRB lp:PFRC lp:PRFD}}
  :-
  std.do! [
  thm_table F F1 PFF1,
  translate_prf A A1 PFRA,
  translate_prf B B1 PFRB,
  translate_prf C C1 PFRC,
  translate_prf D D1 PRFD,
  ].
translate_prf (app [F | Args]) (app [F1 | Args1])
  {{private.IZR_mapN lp:N lp:F lp:F1 lp:PFF1 lp:LArgs lp:LArgs1 lp:LPrf}}
  :-
  std.do! [
  coq.say "aioajizljaiol",
  coq.typecheck F Ty ok,
  coq.say "Ty",
  say Ty,
  type_to_nargs Ty Nint,
  int_to_nat Nint N,
  coq.say N,
  meta_list_to_list Args LArgs,
  coq.say "Args",
  sayL Args,
  coq.say "LArgs",
  say LArgs,
  thm_table F F1 PFF1,
  translate_args Args Args1 PRFArgs,
  meta_list_to_list Args1 LArgs1,
coq.say "Args1",
  sayL Args1,
  coq.say "Args1",
  say LArgs1,
  meta_list_to_list PRFArgs LPrf,
  ].
}}.

Elpi Db R_compute.db lp:{{

pred thm_table o:term, o:term, o:term.

thm_table {{Rplus}} {{Z.add}} {{add_compute}}.

thm_table {{Rmult}} {{Z.mul}} {{mul_compute}}.

thm_table {{Rminus}} {{Z.sub}} {{sub_compute}}.

thm_table {{Ropp}} {{Z.opp}} {{opp_compute}}.

thm_table {{Rabs}} {{Z.abs}} {{abs_compute}}.

thm_table {{Req_bool}} {{Zeq_bool}} {{eq_bool_compute}}.

thm_table {{at_x}} {{at_x_Z}} {{at_x_compute}}.

% arguments in a nat_thm_table relation are
% 1/ a function f from R -> R
% 2/ a function fz from Z -> Z
% 3/ a theorem f_prf with statement
%   forall x y, x = IZR y -> f (Rabs x) = IZR (fz y)
%  This reflect that recursive definitions are mirrored
% by function that first perform a Z.abs_nat operation
% to obtain the integer that will feed the recursive
% computation
% This table is used by R_compute, and its elements
% are produced by mirror_recursive_definition
pred nat_thm_table o:term, o:term, o:term.

}}.

Elpi Command R_compute.

Elpi Accumulate Db R_compute.db.
Elpi Accumulate Db R_translate.db.

Elpi Accumulate lp:{{

  main [trm E] :-
    std.do! [
      translate_prf E E1 _,
      coq.reduction.vm.norm E1 _ E2,
      E3 = {{IZR lp:E2}},
      coq.say " =" {coq.term->string E3}
    ].

main [trm E, str THM_name] :-
    std.do! [
      translate_prf E E1 PRF,
      coq.reduction.vm.norm E1 _ E2,
      E3 = {{IZR lp:E2}},
      coq.say " =" {coq.term->string E3},
      coq.typecheck PRF Stmt _,
      coq.env.add-const THM_name PRF Stmt @opaque! _
    ].

}}.

Elpi Export R_compute.

Elpi Command add_computation.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate lp:{{

% TODO: check that the proof C really states that B is the mirror of A
  main [str A, str B, str C] :-
    coq.locate A A1,
    coq.locate B B1,
    coq.locate C C1,
    coq.say "adding correspondence " {coq.term->string (global A1)}
      {coq.term->string (global B1)} "justified by" {coq.term->string (global C1)},
    coq.elpi.accumulate _ "R_compute.db"
     (clause _ _ (thm_table (global A1) (global B1) (global C1))).

  main L :-
    coq.error "Usage: Elpi add_computation Name1 Name2 Name3.\n instead received: " L.
}}.

Elpi Export add_computation.


Elpi Command mirror_recursive_definition.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate Db R_translate.db.

Elpi Accumulate lp:{{

pred prf_stmt i:term, i:term, i:term, o:term.

prf_stmt {{Z->Z}} Ft FG
  {{forall (n : R) z, n = IZR z ->
  lp:FG (Rabs n) = IZR (lp:Ft z)}}.

prf_stmt {{Z->Z->Z}} Ft FG
  {{forall (r : R) (z : Z), r = IZR z ->  forall (a : R) (b : Z) , a = IZR b ->
  (lp:FG (Rabs r)) a = IZR ((lp:Ft z) b) }}.

prf_stmt {{ty_Z lp:N}} Ft FG
  {{forall (lr : list R) (lz : list Z), lr = List.map IZR lz ->
  (@MappR lp:N lp:FG (List.map Rabs lr)) =  IZR (@MappZ lp:N lp:Ft lz)}}.

pred translate_list_prf i:list term, o:list term, o:list term.
pred main_translate_prf1 i:term, i:term, o:term, o:term, o:term.

main_translate_prf1
  L ((fun _N {{nat}} c\ (fun _N1 Ty _)) as F) L1 F1
  {{fun N : R => fun z : Z =>

     (nat_rect_list 
        lp:L1 lp:L lp:F1 lp:F
        (Z.abs_nat z)
        (fun (i : nat) (x : Z) =>
           match i return nth i lp:L (id_R 1) (IZR x) = IZR (nth i lp:L1 (id_Z 1) x) with
            | 0 =>  (lp:P 0%nat x)
            | S p => (nth_overflow_1 (nth 0 lp:L (id_R 1)) (nth 0 lp:L1 (id_Z 1)) p x)
            end)
        lp:FPRF)}} :-
      Ty = {{list (R -> R)}},
      std.do! [
      translate_prf L L1 P,
      translate_prf F F1 FPRF
    ].

main_translate_prf1
  L F L1 F1
  {{fun N : R => fun z : Z =>
     private.nth_map 0%Z 0 IZR _ _ 0 eq_refl
     (private.nat_rect_list_IZR lp:L1 lp:L lp:F1 lp:F
       (Z.abs_nat z) eq_refl lp:FPRF)}} :-
    std.do! [
      translate_prf L L1 _,
      translate_prf F F1 FPRF
    ].

main_translate_prf1
  L ((fun _N {{nat}} c\ (fun _N1 Ty _)) as F) L1 F1
  {{fun N : R => fun z : Z =>
     (nat_rect_list_N lp:N
        lp:L1 lp:L lp:F1 lp:F
        (Z.abs_nat z)
        (fun (i : nat) (x : Z) =>
           match i return nth i lp:L (id_R lp:N) (IZR x) = IZR (nth i lp:L1 (id_Z 1) x) with
            | 0 =>  (lp:P 0%nat x)
            | S p => (nth_overflow_1 (nth 0 lp:L (id_R lp:N)) (nth 0 lp:L1 (id_Z lp:N)) p x)
            end)
        lp:FPRF)}} 
      :-
      type_to_nargs Ty Nint,
      int_to_nat Nint N,
      std.do! [
      translate_prf L L1 P,
      translate_prf F F1 FPRF
    ].

main_translate_prf
  {{fun (n : R) =>
      nth 0 (Rnat_rec lp:L lp:Frstep0 n) (id_R 0)}}
  F Prf1 :-
  Frstep0 = (fun _ {{R}} Frstep),
  Fnstep = (fun _ {{nat}} c \ (Frstep {{INR lp:c}})),
  main_translate_prf1 L Fnstep Lz Fz Prf,
  F = {{fun (x : Z) =>
         nth 0 (nat_rect (fun _ => list Z) lp:Lz
           lp:Fz (Z.abs_nat x)) 0%Z}},
  std.assert-ok! (coq.typecheck F {{Z->Z}})
    "failed to typecheck mirror function",
  Prf1 =
    {{fun (n : R) (z : Z) (nzq : n = IZR z) =>
       eq_ind_r
         (fun x : nat =>
           nth 0 (nat_rect _ lp:L lp:Fnstep x) 0 =
           IZR (nth 0 (nat_rect _ lp:Lz lp:Fz (Z.abs_nat z)) 0%Z))
        (lp:Prf n z)
          (private.IRN_Z_abs_nat _ _ nzq)}}.

main_translate_prf
  {{fun (r : R) =>
      nth 0 (Rnat_rec lp:L lp:Frstep0 r) (id_R 1)}}
  F Prf1 :-
  Frstep0 = (fun _ {{R}} Frstep),
  Fnstep = (fun _ {{nat}} c \ (Frstep {{INR lp:c}})),
  main_translate_prf1 L Fnstep Lz Fz Prf,
  F = {{fun (x : Z) =>
         nth 0 (nat_rect (fun _ => list (Z->Z)) lp:Lz
           lp:Fz (Z.abs_nat x)) (id_Z 1)}},
  std.assert-ok! (coq.typecheck F {{Z->Z->Z}})
    "failed to typecheck mirror function",

  Prf1 =
    {{
      fun (r : R) (z : Z) (nzq : r = IZR z) =>
      private.IZR_map1'  (
       (eq_ind_r
         (fun x : nat =>
          P_trans1
          (nat_rect _ lp:L lp:Fnstep x) IZR
          (nat_rect _ lp:Lz lp:Fz (Z.abs_nat z))
          )
        (lp:Prf r z)
          (private.IRN_Z_abs_nat _ _ nzq)) 0%nat)
          }}.

main_translate_prf
  {{fun (r : R) =>
      nth 0 (Rnat_rec lp:L lp:Frstep0 r) (id_R lp:N)}}
  F Prf1 :-
  Frstep0 = (fun _ {{R}} Frstep),
  Fnstep = (fun _ {{nat}} c \ (Frstep {{INR lp:c}})),
  main_translate_prf1 L Fnstep Lz Fz Prf,
  F = {{fun (x : Z) =>
         nth 0 (nat_rect (fun _ => list (ty_Z lp:N)) lp:Lz
           lp:Fz (Z.abs_nat x)) (id_Z lp:N)}},
  std.assert-ok! (coq.typecheck F {{ty_Z (S lp:N)}})
    "failed to typecheck mirror function",

  Prf1 =
    {{
      fun (r : R) (z : Z) (nzq : r = IZR z) =>
      private.IZR_map1'  (
       (eq_ind_r
         (fun x : nat =>
          P_trans1
          (nat_rect _ lp:L lp:Fnstep x) IZR
          (nat_rect _ lp:Lz lp:Fz (Z.abs_nat z))
          )
        (lp:Prf r z)
          (private.IRN_Z_abs_nat _ _ nzq)) 0%nat)
          }}.

main [str F] :-
std.do! [
  std.assert! (coq.locate F (const FGR))
    "the argument is not a known constant",
  std.assert! (coq.env.const-body FGR (some Bo))
    "the constant does not have a value",
  std.assert! (main_translate_prf Bo T1 Prf)
    "translation failed.  Possible causes are:\n
1/ the function was not generated by the command Recursive\n
2/ some function without computational correspondence may be used\n
   (in that case, use add_computation to provide missing information)\n
3/ you are using a function that is defined only on natural numbers\n
   but you are not encapsulating its argument in a Rabs call",
  std.assert-ok! (coq.typecheck T1 Ty)
     "Anomaly: generating an ill-typed term",
  F_mirror is F ^ "_Z_mirror",
  coq.env.add-const F_mirror T1 Ty @transparent! C,
  Fterm = global (const C),
  prf_stmt Ty Fterm (global (const FGR)) Stmt,
  coq.say "Prf",
  say Prf,
  std.assert-ok! (coq.typecheck Prf Stmt)
          "Anomaly: generating an incorrect proof",
  F_prf is F ^ "_Z_prf",
  coq.env.add-const F_prf Prf Stmt @opaque! Cprf,
  coq.elpi.accumulate _ "R_compute.db"
    (clause _ _ (nat_thm_table (global (const FGR))
                   (global (const C))
                   (global (const Cprf))))
].

main L :-
  coq.error "Usage: Elpi mirror_recursive_definition Name.\n instead received: " L.
}}.

Elpi Query lp:{{

  prf_stmt {{ty_Z 3}} Fr Fz K,
  coq.typecheck K Ty ok,
  coq.say "K" {coq.term->string K}

}}.

Recursive (def foo1 such that
    foo1 0 = 0 /\
    forall n, Rnat (n-1) -> foo1 n = foo1 (n-1)).
    Print foo1.
    Print foo1_eqn.
Elpi Query lp:{{
  coq.locate "foo1" (const FGR),
  coq.env.const-body FGR (some Bo) ,
  main_translate_prf Bo T1 Prf,
  coq.typecheck Prf TP ok,
  coq.say "TP : "{coq.term->string TP},
  coq.say "Prf is " {coq.term->string Prf},
  coq.typecheck T1 Ty ok,
  coq.env.add-const "foo_m" T1 Ty @transparent! C,
  Fterm = global (const C),
  % prf_stmt Ty Fterm (global (const FGR)) Stmt,
  % Stmt = {{forall (r : R) (z : Z), r=IZR z -> forall (a :R) (b : Z) , a = IZR b -> foo (Rabs r) a = IZR (lp:Fterm (z) b)}},
  RF = coq.redflags.const FGR,
  RF' = coq.redflags.const C,
   coq.redflags.add coq.redflags.nored [RF,RF'] RFS,
   @redflags! RFS => coq.reduction.cbv.norm Stmt StmtLN,

  coq.say "Stmt is " {coq.term->string StmtLN},
  std.assert-ok! (coq.typecheck {{lp:Prf}} Stmt )
          "Anomaly: generating an incorrect proof",
coq.say "DEBUG TY2" {coq.term->string Stmt}

}}.
Elpi mirror_recursive_definition foo1.
Check foo1_Z_prf.
Print foo1_Z_mirror.


Recursive (def fib such that 
    fib 0 = 0 /\ 
    fib 1 = 1 /\
    forall n : R, Rnat (n - 2) -> 
    fib n = fib (n - 2) + fib (n - 1)).
Print fib.

Definition fib_Z_mirror' := fun x : Z => nth 0 (nat_rect (fun _ : nat => list Z) (0%Z ::1%Z :: nil) (fun (_ : nat) (v : list Z) => nth 1 v (id_Z 0) :: (nth 0 v (id_Z 0) + nth 1 v (id_Z 0))%Z ::nil)
(Z.abs_nat x)) 0%Z.

Elpi Query lp:{{
  (pi Msg Data \ std.debug-print Msg Data :- coq.say Msg Data,!) =>
  std.do! [
  coq.locate "fib" (const FGR),
  coq.env.const-body FGR (some Bo) ,
  main_translate_prf Bo _T1 Prf,
  coq.say "ICI ",
  say Prf,
  std.assert-ok! (coq.typecheck Prf Ty) "error"

  ]

}}.

Recursive (def tail_addmul such that 
  tail_addmul 0 = (fun m r x => r) /\
  forall n, Rnat (n-1) -> 
  tail_addmul n = (fun m r x  => tail_addmul (n - 1) m (m + r) x)).

Elpi Trace Browser.

Fail Elpi Query lp:{{
  (pi Msg Data \ std.debug-print Msg Data :- coq.say Msg Data,!) =>
  std.do! [
  coq.locate "tail_addmul" (const FGR),
  coq.env.const-body FGR (some Bo),
  main_translate_prf Bo _T1 Prf,
  say Prf,

  ]

}}.
Elpi mirror_recursive_definition fib.
Theorem a : forall (n : R) (z : Z), n = IZR z -> fib (Rabs n) = IZR (fib_Z_mirror z).

refine (fun (n : R) (z : Z) (nzq : n = IZR z) =>
eq_ind_r
  (fun x : nat =>
   nth 0
     (nat_rect _ (0 :: 1 :: nil)
        (fun (_ : nat) (v : list R) =>
         nth 1 v (id_R 0) :: nth 0 v (id_R 0) + nth 1 v (id_R 0) :: nil) x) 0 =
   IZR
     (nth 0
        (nat_rect _ (0%Z :: 1%Z :: nil)
           (fun (_ : nat) (v : list Z) =>
            nth 1 v (id_Z 0) :: (nth 0 v (id_Z 0) + nth 1 v (id_Z 0))%Z :: nil)
           (Z.abs_nat z)) 0%Z))
  ((fun (N : R) (z0 : Z) =>
    private.nth_map 0%Z 0 IZR _ _ 0 eq_refl
      (private.nat_rect_list_IZR (0%Z :: 1%Z :: nil) (0 :: 1 :: nil)
         (fun (_ : nat) (v : list Z) =>
          nth 1 v (id_Z 0) :: (nth 0 v (id_Z 0) + nth 1 v (id_Z 0))%Z :: nil)
         (fun (_ : nat) (v : list R) =>
          nth 1 v (id_R 0) :: nth 0 v (id_R 0) + nth 1 v (id_R 0) :: nil)
         (Z.abs_nat z0) eq_refl
         (fun (H : nat1) (lr : list (ty_R 0)) (lz : list Z)
            (h : lr = map IZR lz) =>
          f_equal2 cons
            (private.nth_map (id_Z 0) (id_R 0) IZR lz lr 1 eq_refl h)
            ((eq_ind_r
(fun lr0 : list (ty_R 0) =>
nth 0 lr0 (id_R 0) + nth 1 lr0 (id_R 0) :: nil = IZR (nth 0 lz (id_Z 0) + nth 1 lz (id_Z 0)) :: nil)
(eq_ind (IZR (nth 0 lz (id_Z 0)) + IZR (nth 1 lz (id_Z 0)))
(fun r : R => nth 0 (map IZR lz) (id_R 0) + nth 1 (map IZR lz) (id_R 0) :: nil = r :: nil)
(match
lz as l
return
(lr = map IZR l ->
nth 0 (map IZR l) (id_R 0) + nth 1 (map IZR l) (id_R 0) :: nil =
IZR (nth 0 l (id_Z 0)) + IZR (nth 1 l (id_Z 0)) :: nil)
with
| nil => fun _ : lr = map IZR nil => eq_refl
| z1 :: l =>
(fun (z2 : Z) (lz0 : list Z) (h0 : lr = map IZR (z2 :: lz0)) =>
match
lz0 as l0
return
(lr = map IZR (z2 :: l0) ->
nth 0 (map IZR (z2 :: l0)) (id_R 0) + nth 1 (map IZR (z2 :: l0)) (id_R 0) :: nil =
IZR (nth 0 (z2 :: l0) (id_Z 0)) + IZR (nth 1 (z2 :: l0) (id_Z 0)) :: nil)
with
| nil => fun _ : lr = map IZR (z2 :: nil) => eq_refl
| z3 :: l0 => (fun (z4 : Z) (lz1 : list Z) (_ : lr = map IZR (z2 :: z4 :: lz1)) => eq_refl)
z3 l0
end h0) z1 l
end h) (IZR (nth 0 lz (id_Z 0) + nth 1 lz (id_Z 0))) (add_compute (nth 0 lz (id_Z 0))
(nth 1 lz (id_Z 0)))) h)))))

 n z)
  (private.IRN_Z_abs_nat _ _ nzq)).

Qed.

Theorem a' : forall (n : R) (z : Z), n = IZR z -> fib (Rabs n) = IZR (fib_Z_mirror z).

refine (fun (n : R) (z : Z) (nzq : n = IZR z) =>
eq_ind_r
  (fun x : nat =>
   nth 0
     (nat_rect _ (0 :: 1 :: nil)
        (fun (_ : nat) (v : list R) =>
         nth 1 v (id_R 0) :: nth 0 v (id_R 0) + nth 1 v (id_R 0) :: nil) x) 0 =
   IZR
     (nth 0
        (nat_rect _ (0%Z :: 1%Z :: nil)
           (fun (_ : nat) (v : list Z) =>
            nth 1 v (id_Z 0) :: (nth 0 v (id_Z 0) + nth 1 v (id_Z 0))%Z :: nil)
           (Z.abs_nat z)) 0%Z))
  ((fun (N : R) (z0 : Z) =>
    private.nth_map 0%Z 0 IZR _ _ 0 eq_refl
      (private.nat_rect_list_IZR (0%Z :: 1%Z :: nil) (0 :: 1 :: nil)
         (fun (_ : nat) (v : list Z) =>
          nth 1 v (id_Z 0) :: (nth 0 v (id_Z 0) + nth 1 v (id_Z 0))%Z :: nil)
         (fun (_ : nat) (v : list R) =>
          nth 1 v (id_R 0) :: nth 0 v (id_R 0) + nth 1 v (id_R 0) :: nil)
         (Z.abs_nat z0) eq_refl
         (fun (H : nat1) (lr : list (ty_R 0)) (lz : list Z)
            (h : lr = map IZR lz) =>
          f_equal2 cons
            (private.nth_map (id_Z 0) (id_R 0) IZR lz lr 1 eq_refl h)

(eq_ind (IZR (nth 0 lz (id_Z 0)) + IZR (nth 1 lz (id_Z 0)))
(fun r : R => nth 0 lr (id_R 0) + nth 1 lr (id_R 0) :: nil = r :: nil)
(eq_ind_r (fun t : ty_R 0 => t + nth 1 lr (id_R 0) :: nil =
IZR (nth 0 lz (id_Z 0)) + IZR (nth 1 lz (id_Z 0)) :: nil)
(eq_ind_r
(fun t : ty_R 0 => IZR (nth 0 lz (id_Z 0)) + t :: nil =
IZR (nth 0 lz (id_Z 0)) + IZR (nth 1 lz (id_Z 0)) :: nil) eq_refl
(private.nth_map (id_Z 0) (id_R 0) IZR lz lr 1 eq_refl h))
(private.nth_map (id_Z 0) (id_R 0) IZR lz lr 0 eq_refl h)) (IZR (nth 0 lz (id_Z 0) +
nth 1 lz (id_Z 0)))
(add_compute (nth 0 lz (id_Z 0)) (nth 1 lz (id_Z 0))))
)))
n z)
  (private.IRN_Z_abs_nat _ _ nzq)).

Qed.

Theorem a'' : forall (n : R) (z : Z), n = IZR z -> fib (Rabs n) = IZR (fib_Z_mirror z).

refine (fun (n : R) (z : Z) (nzq : n = IZR z) =>
eq_ind_r
  (fun x : nat =>
   nth 0
     (nat_rect _ (0 :: 1 :: nil)
        (fun (_ : nat) (v : list R) =>
         nth 1 v (id_R 0) :: nth 0 v (id_R 0) + nth 1 v (id_R 0) :: nil) x) 0 =
   IZR
     (nth 0
        (nat_rect _ (0%Z :: 1%Z :: nil)
           (fun (_ : nat) (v : list Z) =>
            nth 1 v (id_Z 0) :: (nth 0 v (id_Z 0) + nth 1 v (id_Z 0))%Z :: nil)
           (Z.abs_nat z)) 0%Z))
  ((fun (N : R) (z0 : Z) =>
    private.nth_map 0%Z 0 IZR _ _ 0 eq_refl
      (private.nat_rect_list_IZR (0%Z :: 1%Z :: nil) (0 :: 1 :: nil)
         (fun (_ : nat) (v : list Z) =>
          nth 1 v (id_Z 0) :: (nth 0 v (id_Z 0) + nth 1 v (id_Z 0))%Z :: nil)
         (fun (_ : nat) (v : list R) =>
          nth 1 v (id_R 0) :: nth 0 v (id_R 0) + nth 1 v (id_R 0) :: nil)
         (Z.abs_nat z0) eq_refl
         (fun (H : nat1) (lr : list (ty_R 0)) (lz : list Z)
            (h : lr = map IZR lz) =>
          f_equal2 cons
            (private.nth_map (id_Z 0) (id_R 0) IZR lz lr 1 eq_refl h)

_

)))
n z)
  (private.IRN_Z_abs_nat _ _ nzq)).
  rewrite <-add_compute.



rewrite (private.nth_map (id_Z 0) (id_R 0) IZR lz lr _ eq_refl h).
rewrite (private.nth_map (id_Z 0) (id_R 0) IZR lz lr _ eq_refl h).
apply eq_refl.
Print eq_ind.
Show Proof.
Qed.

Recursive (def foo such that
    foo 0 = (fun m => 0) /\
    forall n, Rnat (n-1) -> foo n = fun m => (foo (n-1)) m).
    Print foo.
    (* Print foo_eqn.
Elpi Query lp:{{
  coq.locate "foo" (const FGR),
  coq.env.const-body FGR (some Bo) ,
  main_translate_prf Bo T1 Prf,
  coq.typecheck Prf TP ok,
  coq.say "TP : "{coq.term->string TP},
  coq.say "Prf is " {coq.term->string Prf},
  coq.typecheck T1 Ty ok,
  coq.env.add-const "foo_" T1 Ty @transparent! C,
  Fterm = global (const C),
  % prf_stmt Ty Fterm (global (const FGR)) Stmt,
  % Stmt = {{forall (r : R) (z : Z), r=IZR z -> forall (a :R) (b : Z) , a = IZR b -> foo (Rabs r) a = IZR (lp:Fterm (z) b)}},
  RF = coq.redflags.const FGR,
  RF' = coq.redflags.const C,
   coq.redflags.add coq.redflags.nored [RF,RF'] RFS,
   @redflags! RFS => coq.reduction.cbv.norm Stmt StmtLN,

  coq.say "Stmt is " {coq.term->string StmtLN},
  std.assert-ok! (coq.typecheck {{lp:Prf}} Stmt )
          "Anomaly: generating an incorrect proof",
coq.say "DEBUG TY2" {coq.term->string Stmt}

}}. *)
Elpi mirror_recursive_definition foo.
Print foo_Z_prf.
R_compute (foo  5 2).
(*
Parameter toto : forall (r : R) (z : Z),
r = IZR z ->
(fun x : nat =>
 P_trans1
   (nat_rect (fun _ : nat => list (R -> R)) ((fun _ : R => 0) :: nil)
      (fun (_ : nat) (v : list (R -> R)) =>
       (fun m : R => nth 0 v (id_R 1) m) :: nil) x) IZR
   (nat_rect (fun _ : nat => list (Z -> Z)) ((fun _ : Z => 0%Z) :: nil)
      (fun (_ : nat) (v : list (Z -> Z)) =>
       (fun m : Z => nth 0 v (id_Z 1) m) :: nil) (Z.abs_nat z))) (IRN (Rabs r)).
 Check ( eq_refl :
nth 0
(nat_rect (fun _ : nat => list (R -> R))
((fun _ : R => 0) :: nil)
(fun (_ : nat) (v : list (R -> R)) =>
(fun m : R => nth 0 v (id_R 1) m) :: nil)
(IRN (Rabs 1))) (id_R 1) = (foo (Rabs 1))
).

Recursive (def fib such that
    fib 0 = 0 /\
    fib 1 = 1 /\
    forall n : R, Rnat (n - 2) ->
    fib n = fib (n - 2) + fib (n - 1)).
Print fib.
Elpi mirror_recursive_definition fib.
Check fib_Z_prf.

 *)

Definition titi := (nat_rect (fun _ : nat => list (R -> R))
((fun _ : R => 0) :: nil)
(fun (_ : nat) (v : list (R -> R)) =>
(fun m : R => nth 0 v (id_R 1) m) :: nil)
(IRN (Rabs 1))).
Check titi.

Ltac r_compute_rewrite P := rewrite P.

Elpi Tactic r_compute.
Elpi Accumulate Db R_compute.db.
Elpi Accumulate Db R_translate.db.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ [trm X] as G) GL :-
  std.do! [
  translate_prf X V PRF ,
  coq.reduction.vm.norm V _ E2,
  coq.typecheck PRF Stmt ok,
  coq.say "stmt :" {coq.term->string Stmt},
  coq.ltac.call "r_compute_rewrite"
    [trm {{lp:PRF : lp:Stmt}}] G GL
  ].

solve A B :-
  coq.say "wrong" A B.
}}.

(* The following experiment prefigures what can be done
   so that R_compute returns not only the value but also
   the proof that this value is correct.

Recursive (def fib such that
  (fib 0 = 0 /\ fib 1 = 1 /\
   (forall n, Rnat (n - 2) ->
     fib n = fib (n - 2) + fib (n - 1)))).



Lemma fib_nat n : Rnat n -> Rnat (fib n).
Proof.
rec_Rnat fib.
Qed.

Existing Instance fib_nat.


*)
(*
Recursive (def fib such that
  (fib 0 = 0 /\ fib 1 = 1 /\
   (forall n, Rnat (n - 2) ->
     fib n = fib (n - 2) + fib (n - 1)))).

Recursive (def monster such that
  monster 0 = 1 /\
  forall n, Rnat (n - 1) -> monster n = fib (Rabs (monster (n - 1) + 2))).

Elpi Query lp:{{ main [str "fib"] }}.
Elpi Query lp:{{ main [str "monster"]}}.

Elpi R_compute (fib 6).
Elpi R_compute (monster (Rabs (fib 5 + 1))).
*)