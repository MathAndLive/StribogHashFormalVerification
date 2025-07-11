Require Import Arith FunctionalExtensionality.

(** * Ассоциативные массивы *)

(* associative array, map, symbol table, dictionary *)

Definition key := nat.

(** ** Ассоциативные массивы как функции *)

Definition tmap (V : Type) : Type := key -> V.

Definition empty {V : Type} (d : V) : tmap V := fun _ => d.

Definition update {V : Type} (m : tmap V) (k : key) (v : V) : tmap V :=
  fun x => if k =? x then v else m x.

Example m : tmap bool := update (empty false) 7 true.

Compute m 2.
Compute m 7.

Lemma apply_empty : forall (V : Type) (k : key) (d : V),
  empty d k = d.
Proof. intros. unfold empty. reflexivity. Qed.

Lemma update_eq : forall (V : Type) (m : tmap V) k v,
  (update m k v) k = v.
Proof.
  intros V m k v. unfold update.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma update_neq : forall (V : Type) v k k' (m : tmap V),
  k <> k' -> (update m k v) k' = m k'.
Proof.
  intros. unfold update.
  apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma update_shadow : forall (V : Type) (m : tmap V) (v1 v2 : V) (k : key),
  update (update m k v1) k v2 = update m k v2.
Proof.
  intros V m v1 v2 k. apply functional_extensionality. intros x.
  destruct (Nat.eqb_spec k x) as [Heq | Hneq].
  - rewrite Heq. rewrite 2!update_eq. reflexivity.
  - rewrite 3!update_neq by assumption. reflexivity.
Qed.

Lemma update_same : forall (V : Type) (k : key) (m : tmap V),
  update m k (m k) = m.
Proof.
  intros V k m. apply functional_extensionality. intros x.
  unfold update. destruct (Nat.eqb_spec k x); auto.
Qed.

Lemma update_permute : forall (V : Type) (v1 v2 : V) (k1 k2 : key) (m : tmap V),
  k2 <> k1 -> update (update m k2 v2) k1 v1 = update (update m k1 v1) k2 v2.
Proof.
  intros V v1 v2 k1 k2 m Hneq. apply functional_extensionality. intros x.
  destruct (Nat.eqb_spec k1 x); destruct (Nat.eqb_spec k2 x); subst.
  - contradiction.
  - rewrite update_neq with (k := k2) by assumption.
    rewrite 2!update_eq. reflexivity.
  - rewrite update_neq with (k := k1) by assumption.
    rewrite 2!update_eq. reflexivity.
  - rewrite 4!update_neq by assumption. reflexivity.
Qed.

Definition pmap (V : Type) : Type := tmap (option V).

Definition pempty {V : Type} : pmap V := empty None.

Definition pupdate {V : Type} (m : pmap V) (k : key) (v : V) : pmap V :=
  update m k (Some v).
