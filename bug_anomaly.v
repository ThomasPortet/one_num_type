Require Import List Reals.
From Ltac2 Require Import Ltac2.

Open Scope R_scope.
Lemma toto : True.
Proof.
assert (H : nth 0 (nat_rect (fun _ => list R)
           (0 :: 1 :: nil)
         (fun _ l => (nth 1 l 0 ::
                nth 0 l 0 + nth 1 l 0 :: nil)) 0) 0 = 0).