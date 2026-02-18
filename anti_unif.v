From elpi Require Import elpi.
(* From Ltac2 Require Import Ltac2. *)
From Stdlib Require Import Reals Lra.
From OneNum Require Import R_subsets rec_def ring_simplify_bank field_simplify_bank.

From OneNum.srcElpi Extra Dependency "anti_unification.elpi" as anti_unif.
From OneNum.srcElpi Extra Dependency "tools.elpi" as tools.
From OneNum.srcElpi Extra Dependency "super_ring.elpi" as super.



Open Scope R_scope.
Lemma f_g_equal  {T:Type}{T':Type}{f : T -> T'} {g x y} : 
f = g -> x = y -> f x = g y.
Proof.
  intros.
  rewrite H; now rewrite H0.
Qed.
Elpi Command a.
Elpi Accumulate File anti_unif.
Ltac my_ring := ring.



Elpi Tactic anti_unification.
Elpi Accumulate File anti_unif.

Elpi Accumulate lp:{{

    solve (goal _Ctx _ {{lp:T1 = lp:T2}} _  _ as G ) GL :-
    main-anti-unif T1 T2  P ,
    refine P G GL.

    solve _ _ :-
    coq.ltac.fail _ "problem anti-unif".

}}.
Tactic Notation "anti-unif" :=
  elpi anti_unification.

Ltac anti_unif_pack tac :=
anti-unif ; ltac:(tac).

Ltac superring :=
my_ring || anti_unif_pack my_ring.

Section Test.
Variable x y : R.
Elpi Query lp:{{
    EX1 = {{cos x + sin y}},
    EX2 = {{cos (x + 1) + sin (y+0)}},
    
    anti-unif 0 EX1 EX2 A B C,!,
    holes_to_func A B E,
    coq.term->string E SE,
    coq.say SE,
    main-anti-unif EX1 EX2 P,
    coq.say SE,

    coq.typecheck P {{lp:EX1 = lp:EX2}} ok,
    main-anti-unif {{1+2 }} {{3-5}} P',
    coq.typecheck P' {{1+2 = 3-5}} ok
          }}.
Elpi Query lp:{{
    EX1 = {{cos(x + 1+2)}},
    EX2 = {{cos (x +2+ 1)}},
    
    anti-unif 0 EX1 EX2 A B C,!,
    holes_to_func A B E,
    coq.term->string E SE,
    coq.say SE,
    main-anti-unif EX1 EX2 P,
    coq.term->string P SP,
    coq.say SP,

    coq.typecheck P {{lp:EX1 = lp:EX2}} ok,
    main-anti-unif {{1+2 }} {{3-5}} P',
    coq.typecheck P' {{1+2 = 3-5}} ok
          }}.
End Test.



Tactic Notation "super_ring" :=
  elpi super_ring.
Elpi Tactic super_ring.
Elpi Accumulate File super.
Elpi Accumulate File tools.

Ltac super_ring' :=
repeat  (progress (super_ring ;try reflexivity)) ;  try reflexivity.

Elpi Accumulate lp:{{

    solve (goal _Ctx _ {{lp:T1 = lp:T2}} _  _ as G ) GL :-
    sub_ringable_r T1 [] L1,
    sub_ringable_r T2 L1 L2,
    remove_duplicates L2 L,
    terms_to_trms L TL, !,
    std.length L N,
    std.any->string N SN,
        coq.say "number of arguments: " SN,
    sayLT L,
    std.string.concat  "" ["r", SN] S,
    coq.ltac.call S TL G GL
    .

    solve _ _ :-
    coq.ltac.fail _ "problem super_ring".

}}.
Section Test.
Variable x y z t: R.

Elpi Query lp:{{
 T = {{ cos ( x+ y)}},
collect [{{Rplus}}] []T [] L1,
sayL L1 
}}.

Goal cos ( x+ y) = cos (y+ x).

super_ring.
reflexivity.
Qed.
Goal cos (x + 1 + 2) = cos (x + 2 + 1).

 super_ring.
 easy.
Qed.

Goal  x+cos (y +sin t) = cos (sin (t+0) + y +0)+x.
super_ring.
super_ring.
super_ring.
super_ring.
super_ring'.
Qed.

Goal  2 * sin (x+ cos(y)) + cos(y+x+0) = cos (x+y)+2* sin (cos (y)+x) .
super_ring'.
Qed.

Goal sin (x + 0) + 2*x - x = sin x + x.
super_ring'.
Qed.
Goal x + 3*x - 4*x = 0.

super_ring'.
Qed.
Goal (cos (x / 2 ^ (0 + 2))) = (cos (x / 4)).
  super_ring'.
Qed.

Goal - y ^ 2 + x ^ 2  = - y ^ 2 + x ^ 2.
super_ring.
super_ring.
super_ring.
super_ring.
reflexivity.
Qed.
Goal x ^ 2 = y ^ 2 -> x ^ 2 - y ^ 2 = 0.
intros.
super_ring.
super_ring.
super_ring.
lra.
Qed.
End Test.

Tactic Notation "super_field" :=
  elpi super_field.
Elpi Tactic super_field.
Elpi Accumulate File super.
Elpi Accumulate File tools.


Elpi Accumulate lp:{{

solve (goal Ctx _ {{lp:T1 = lp:T2}} _  _ as G ) GL :-
    coq.say "super_field called",
    sub_fieldable_r T1 [] L1,
    sub_fieldable_r T2 L1 L2,
    sayL L2,
    remove_duplicates L2 L,
    terms_to_trms L TL, !,
    std.length L N,

    std.any->string N SN,
    coq.say "number of arguments: " SN,
    std.string.concat  "" ["f", SN] S,
    coq.ltac.call S TL G GL
    .

solve _ _ :-
    coq.ltac.fail _ "problem super_field".

}}.


Elpi Tactic add_ge0s.
Elpi Accumulate File super.
Elpi Accumulate File tools.
Elpi Accumulate lp:{{

solve (goal Ctx _ _ _ _ as G) Gl :-
  std.filter Ctx (is_hyp_ge0 _)OldGe0s,
  newHs Ctx OldGe0s Ts,
  std.rev Ts RTs,
  letifyge0s RTs Let,
  refine Let G Gl.

solve _ _ :-
  coq.ltac.fail _ "problem add_ge0s".

}}.




Ltac add_ge0s := elpi add_ge0s.

(* TODO : we need to iterate on super_field ; but super_field may create additional goals, so progress doesn't work. We need to verify that the first goal does progress *)
Ltac super_field' :=
super_field ;  try reflexivity ; (add_ge0s ; try lra) .

Ltac lra' :=
add_ge0s; lra .


From Ltac2 Require Import Ltac2.
Ltac2 count_hyps () :=
  List.length (Control.hyps ()).
Ltac2 assert_hyps_eq (k : int) :=
  let n := List.length (Control.hyps ()) in
  if Int.equal n k then ()
  else fail.

Section Test.

Variable x y z : R.

Goal (Rnat x) -> (Rnat y)->(Rnat (x - y ^3))  -> (Rnat z)  -> (0 <= z) -> 0 <= x.
intros. 
Fail assumption.
Ltac2 Eval (assert_hyps_eq 8).
ltac1:(add_ge0s).
Ltac2 Eval (assert_hyps_eq 11).
ltac1:(add_ge0s).
Ltac2 Eval (assert_hyps_eq 11).
assumption.
Qed.
End Test.

Ltac super :=
  repeat progress (
      super_ring
   || super_field
   || add_ge0s
   || lra
  );
  try reflexivity.