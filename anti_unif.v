From elpi Require Import elpi.
From Stdlib Require Import Reals.
From OneNum.srcElpi Extra Dependency "anti_unification.elpi" as anti_unif.

Open Scope R_scope.
Lemma f_g_equal  {T:Type}{T':Type}{f : T -> T'} {g x y} : 
f = g -> x = y -> f x = g y.
Proof.
  intros.
  rewrite H; now rewrite H0.
Qed.

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