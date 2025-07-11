From VST.floyd Require Import proofauto library.
Require Import compcert.lib.Integers.     


Module Wordsize_512.
 Definition wordsize := 512%nat.
 Remark wordsize_not_zero: wordsize <> 0%nat.
 Proof. unfold wordsize; congruence. Qed.
End Wordsize_512.


Strategy opaque [Wordsize_512.wordsize].


Module Vec512 := Make(Wordsize_512).

Print Make.