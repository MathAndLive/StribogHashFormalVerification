From VST.floyd Require Import proofauto library.
Require Import compcert.lib.Integers.

Module Wordsize_512.
  Definition wordsize := 512%nat.
  
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. 
    unfold wordsize; 
    congruence.
  Qed.
End Wordsize_512.

Strategy opaque [Wordsize_512.wordsize].

Module Vec512 := Make(Wordsize_512).

Notation block512 := Vec512.int.


Print block512.


Notation "a + b" := (Vec512.add a b).


Definition sum (a b : block512) := a + b.


Compute Vec512.intval (sum (Vec512.repr 3) (Vec512.repr 4)).
