(* Документация: https://coq.inria.fr/doc/V8.20.0/refman *)

Check nat.

Check Set.

Check Type.

(* 7 : nat, nat : Set, Set : Type 1, Type 1 : Type 2, ... *)

(* Стандартная библиотека: https://coq.inria.fr/doc/V8.20.0/stdlib *)

Check true.

Print bool.

Module Temp.

  (** Типы с конечным числом элементов *)

  Inductive Empty_set : Type :=.

  Inductive unit :=
    tt : unit.

  (* Inductive bool := true | false. *)

  Inductive bool : Set :=
  | true : bool
  | false : bool.

  Check bool_ind.

  (* Функции *)

  Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

  Compute negb true.
  Compute negb false.

  Definition andb b1 b2 :=
    match b1 with
    | true => b2
    | _ => false
    end.

  Check andb.

  Notation "b1 && b2" := (andb b1 b2).

  Locate "&&".

  (* Первые доказательства. *)

  Lemma negb_involutive : forall b : bool, negb (negb b) = b.
  Proof.
    intros b. destruct b.
    - simpl. reflexivity.
    - reflexivity.
  Qed.

  (* Для структуры: -, +, *, --, ++, **, ---, ... *)

  Theorem andb_commutative :
    forall b1 b2, b1 && b2 = b2 && b1.
  Proof.
    intros b1 b2. destruct b1.
    - destruct b2; reflexivity.
    - destruct b2.
      + reflexivity.
      + reflexivity.
  Qed.

  (** Индуктивные типы. *)

  Inductive nat :=
  | O : nat
  | S : nat -> nat.

  Check O.       (* 0 *)
  Check S O.     (* 1 *)
  Check S (S O). (* 2 *)

  Check nat_ind.

  Check S O.

  Fixpoint addn (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (addn n' m)
    end.

  Notation "n + m" := (addn n m).
End Temp.

Compute 2 + 4.

Lemma addn_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m H.
  rewrite H.
  (* rewrite <- H. *)
  reflexivity.
Qed.

(** Доказательство по индукции *)

Lemma addn_0_l : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.
Qed.

Lemma addn_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [ | n' IHn' ].
  - reflexivity.
  - simpl.
    (* rewrite IHn'. reflexivity. *)
    apply f_equal. apply IHn'.
Qed.

Check f_equal.

Search (?x = ?y -> ?f ?x = ?f ?y).

(** * Полиморфные списки *)

(* Inductive listnat : Type := *)
(* | nil : listnat *)
(* | cons : nat -> listnat -> listnat. *)

(* Check nil. *)
(* Check cons 7 (cons 1 nil). *)
(* Check listnat_ind. *)

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check list.
Check nil.
Check cons.
Check list_ind.

Print list_ind.

Check cons nat 7 (cons nat 1 (nil nat)).
Check cons _ 7 (cons _ 1 (nil _)).

(* Неявные аргументы *)

Arguments cons {X}.
Arguments nil {X}.
Check cons.
Check cons 7 (cons 1 nil).

(* Явная передача аргумента *)

Check @nil nat.

Notation "[]" := nil.
Notation "x :: xs" := (cons x xs).

Check 7 :: 1 :: 6 :: 9 :: [].

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check [7; 1; 6; 8].
Check [true; false; true].

Fixpoint length (X : Type) (xs : list X) : nat :=
  match xs with
  | [] => 0
  | x :: xs => S (length X xs)
  end.

Check length.
Compute length _ [7; 1].

Arguments length {X}.
Compute length [7; 1].

Fixpoint append {X : Type} (xs ys : list X) : list X :=
  match xs with
  | [] => ys
  | x :: xs => x :: append xs ys
  end.

Notation "xs ++ ys" := (append xs ys).

Fixpoint rev {X : Type} (xs : list X) : list X :=
  match xs with
  | []     => []
  | x :: xs => rev xs ++ [x]
  end.

Definition hd {X : Type} (default : X) (xs : list X) : X :=
  match xs with
  | []    => default
  | x :: _ => x
  end.

Definition tl {X : Type} (xs : list X) : list X :=
  match xs with
  | []    => []
  | _ :: t => t
  end.

Require Import Arith.

(** * Утверждения про списки *)

Lemma app_nil_l : forall (X : Type) (xs : list X),
  [] ++ xs = xs.
Proof.
  intros X xs. simpl. reflexivity.
Qed.

Lemma tl_length_pred : forall (X : Type) (xs : list X),
  pred (length xs) = length (tl xs).
Proof.
  intros X xs. destruct xs as [| x xs]; reflexivity.
Qed.

(** ** Структурная индукция на списках *)

Check nat_ind.
(* nat_ind : forall P : nat -> Prop,
     P 0 ->
     (forall n : nat, P n -> P (S n)) ->
     forall n : nat, P n *)

Check list_ind.
(* list_ind : forall (X : Type) (P : list X -> Prop),
     P [] ->
     (forall (x : X) (l : list X), P l -> P (x :: l)) ->
     forall l : list X, P l *)

Lemma app_assoc : forall (X : Type) (xs ys zs : list X),
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof.
  intros X xs ys zs. induction xs as [| x xs IHxs].
  - reflexivity.
  - simpl. rewrite IHxs. reflexivity.
Qed.

Section list_facts.
  Variable X : Type.

  Lemma rev_length : forall (xs : list X),
    length (rev xs) = length xs.
  Proof.
    intros xs. induction xs as [| x xs IHxs].
    - reflexivity.
    - simpl. rewrite <- IHxs.
  Abort.

  Lemma app_length : forall (xs ys : list X),
    length (xs ++ ys) = length xs + length ys.
  Proof.
    intros xs ys. induction xs as [| x xs IHxs].
    - reflexivity.
    - simpl. rewrite IHxs. reflexivity.
  Qed.

  Lemma rev_length : forall (xs : list X),
      length (rev xs) = length xs.
  Proof.
    intros xs. induction xs as [| x xs IHxs].
    - reflexivity.
    - simpl. rewrite <- IHxs.
      rewrite app_length. simpl.
      (* Search (?x + ?y = ?y + ?x). *)
      rewrite Nat.add_comm. reflexivity.
  Qed.
End list_facts.

(** * Декартово произведение *)

(* Inductive prod (A B : Type) : Type := *)
(*   pair : A -> B -> prod A B. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
    pair x _ => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (_, y) => y end.

Fixpoint combine {X Y : Type} (xs : list X) (ys : list Y) : list (X * Y) :=
  match xs, ys with
  | x :: xs, y :: ys => (x, y) :: combine xs ys
  | _, _ => []
  end.

Print combine.

(** * Тип [option] *)

(* Inductive option (A : Type) : Type := *)
(* | Some : A -> option A *)
(* | None : option A. *)

Fixpoint nth_error {A : Type} (l : list A) (n : nat) : option A :=
  match n, l with
  | 0  , x :: _ => Some x
  | S n, _ :: l => nth_error l n
  | _  , _     => None
  end.

(** * Функции высшего порядка *)

(* functions as first-class citizens, anonymous functions, filter, map, fold *)

Fixpoint filter {X : Type} (test : X -> bool) (xs : list X) : list X :=
  match xs with
  | []     => []
  | x :: xs => if test x then
               x :: filter test xs
             else
               filter test xs
  end.

Compute filter Nat.odd [1; 2; 3; 4].
Compute filter (fun x => 2 <? x) [1; 2; 3; 4].

Fixpoint map {X Y : Type} (f : X -> Y) (xs : list X) : list Y :=
  match xs with
  | [] => []
  | x :: xs => (f x) :: (map f xs)
  end.

Compute map Nat.odd [1; 2; 3; 4].

Fixpoint fold_right {X Y : Type} (f : Y -> X -> X) (x : X) (ys : list Y) : X :=
  match ys with
  | [] => x
  | y :: ys => f y (fold_right f x ys)
  end.

Compute fold_right plus 0 [1; 2; 3; 4].

(* Возвращаем функции, частичное применение *)

Definition negb : bool -> bool :=
  fun b : bool => if b then false else true.

Definition plusn (n : nat) : nat -> nat := plus n.

(** * Тактики *)

(* apply with, assumption, injection, ... *)

(* Inductive nat :=
   | O : nat
   | S : nat -> nat.

  Все конструкторы инъективны и не равны. *)

Lemma S_injective : forall n m : nat,
  S n = S m -> n = m.
Proof.
  intros n m H.
  (* assert (H0 : n = pred (S n)). *)
  (* { reflexivity. } *)
  (* rewrite H0, H. simpl. reflexivity. *)

  injection H as H'. exact H'.
Qed.

Lemma S_injective' : forall n m : nat,
  S n = S m -> n = m.
Proof.
  intros n m H.
  (* injection H as H'. exact H'. *)
  apply (f_equal pred) in H. simpl in H. exact H.
Qed.

Lemma discriminate_ex1 : forall n m : nat,
  false = true -> n = m.
Proof.
  intros n m contra.
  (* discriminate contra. *)

  set (f := fun (b : bool) => if b then m else n).
  apply (f_equal f) in contra. simpl in contra. exact contra.
Qed.

(** ** Обобщение индукционной гипотезы *)

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - intros H. destruct m as [| m'].
    + reflexivity.
    + simpl in H. discriminate H.
  - intros H. destruct m as [| m'].
    + discriminate H.
    + Abort.

Lemma double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [| m'].
    + discriminate H.
    + apply f_equal, IHn'. injection H as H'. exact H'.
Qed.

Lemma double_injective' : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IHm'];
    intros n H; destruct n as [| n'].
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - apply f_equal, IHm'. injection H as H'. exact H'.
Qed.

(** ** Разворачивание определений *)

Definition square n := n * n.

Lemma square_mult : forall n m,
  square (n * m) = square n * square m.
Proof.
  intros n m. simpl. (* ? *)
  unfold square.
  rewrite Nat.mul_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite Nat.mul_comm. apply Nat.mul_assoc. }
  rewrite H. rewrite Nat.mul_assoc. reflexivity.
Qed.

(** ** destruct на выражениях *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then
    true
  else
    if n =? 5 then
      true
    else
      false.

Lemma sillyfun_odd : forall n : nat,
  sillyfun n = true -> Nat.odd n = true.
Proof.
  intros n H. unfold sillyfun in H.
  destruct (n =? 3) eqn:H0.
  - apply Nat.eqb_eq in H0. rewrite H0. reflexivity.
  - destruct (n =? 5) eqn:H1.
    + apply Nat.eqb_eq in H1. rewrite H1. reflexivity.
    + discriminate H.
Qed.

(** * Список тактик

intros                  перемещает гипотезы/переменные из цели в контекст
reflexivity             доказывает цель вида x = x
apply                   доказывает цель с использованием гипотезы, леммы или конструктора
apply ... in H          применяет гипотезу, лемму или конструктор к гипотезе H в контексте (прямое рассуждение)
apply ... with ...      явно указывает значения для переменных
simpl                   упрощает выражения в цели
simpl in H                             ... в гипотезе H
rewrite                 использует равенство для перезаписи цели
rewrite ... in H                                        ... гипотезы H
symmetry                преобразует цель вида a = b в b = a
symmetry in H           преобразует гипотезу вида a = b в b = a
transitivity y          доказывает цель a = c, предлагая доказать две новых подцели: a = b и b = c
unfold                  раскрывает определение в цели
unfold ... in H                            ... в гипотезе
destruct ... as ...     анализ случаев для значений индуктивно определенных типов
destruct ... eqn:H      указывает имя уравнения, которое будет добавлено в контекст, фиксируя результат анализа случаев
induction ... as ...    индукция по значениям индуктивно определённых типов
injection ... as ...    рассуждение на основе инъективности для равенств между значениями индуктивно определённых типов
discriminate            рассуждение на основе неравенства конструкторов
assert (H : e)          вводит локальное утверждениe с именем H
assert (e) as H
generalize dependent x  перемещает переменную x (и всё, что от неё зависит) из контекста обратно в явную гипотезу в цели
assumption              доказывает цель, если она совпадает с одним из утверждений в контексте
f_equal                 преобразует цель вида f x = f y в x = y

*)

(** * Логические операции и кванторы *)

(* Мы доказывали утверждения с квантором всеобщности, импликации и равенства.*)

(** Правила естественного вывода для интуиционистского исчисления предикатов:

     Introduction                    Elimination

P   Q                            P ∧ Q        P ∧ Q
───── (∧I)                       ───── (∧E₁)  ───── (∧E₂)
P ∧ Q                              P            Q

  P            Q                 P ∨ Q   P ⇒ R   Q ⇒ R
───── (∨I₁)  ───── (∨I₂)         ───────────────────── (∨E)
P ∨ Q        P ∨ Q                         R

P ⊢ Q                            P ⇒ Q   P
───── (⇒I)                       ───────── (⇒E)
P ⇒ Q                                Q

                                  ⊥
                                 ─── (⊥E)
                                  P

P[t/x]   (t - переменная)         ∀x P
───────────────────────── (∀I)   ────── (∀E)
          ∀x P                   P[t/x]

P[t/x]                           ∃x P   P[t/x] ⊢ Q
────── (∃I)                      ──────────────── (∃E)
 ∃x P                                   Q                 *)

(* [Prop] - тип утверждений *)

Check (forall n : nat, n + 0 = n).
Check (0 = 1).

Locate "=".
Check eq.

(** Конъюнкция *)

Locate "/\".
Check and.

Lemma and_intro : 1 = 1 /\ 2 = 2.
Proof.
  (* split. *)
  (* - reflexivity. *)
  (* - reflexivity. *)

  apply conj; reflexivity.
Qed.

Lemma and_elim : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* intros n m H. destruct H as [Hn Hm]. *)
  intros n m [Hn Hm].
  rewrite Hn, Hm. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q H. destruct H as [H' _]. exact H'.
Qed.

Lemma and_comm : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. split.
  - exact HQ.
  - exact HP.
Qed.

(** Дизъюнкция *)

Lemma or_intro_l : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left. apply HA.
Qed.

Lemma factor_is_O : forall n m,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* intros n m H. destruct H as [Hn | Hm]. *)
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. apply Nat.mul_0_r.
Qed.

(** Отрицание *)

(* Definition not (P : Prop) : Prop := P -> False. *)

(* Inductive False : Prop :=. *)

Lemma ex_falso_quodlibet : forall P : Prop,
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Lemma zero_not_one : 0 <> 1. (* ~ (0 = 1). *)
Proof.
  intros contra. discriminate contra.
Qed.

Lemma contrapositive : forall P Q,
  (P -> Q) -> ~ Q -> ~ P.
Proof.
  intros P Q HPQ HQn.

  (* unfold not. unfold not in HQn. *)
  (* intros HP. apply HQn. apply HPQ. exact HP. *)

  contradict HQn. apply HPQ. assumption.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H. destruct b.
  - (* apply ex_falso_quodlibet. *)
    exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed.

(** Квантор существования *)

Lemma four_is_Even : exists n : nat, 4 = double n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  (* intros n H. destruct H as [m Hm]. *)
  intros n [m Hm].
  exists (2 + m). exact Hm.
Qed.

(** Импликация и квантор всеобщности *)

(* тактики intros, apply *)

Locate "->".
Locate "<->".
Print iff.

(** * Функциональная экстенсиональность *)

(* Axiom functional_extensionality : forall {X Y : Type} (f g : X -> Y), *)
(*   (forall x : X, f x = g x) -> f = g. *)

Require Import Logic.FunctionalExtensionality.

(** Формальная система обладает свойством каноничности (canonicity), если любое
    ее замкнутое выражение редуцируется к каноничному виду, т.е. явно построено
    с помощью конструкторов. Добавление аксиом нарушает каноничность, позволяя
    получать выражения, которые нельзя редуцировать к каноничному виду.

    Подробнее: https://ncatlab.org/nlab/show/canonical+form *)

(** * Конструктивная логика *)

(* Доказательства в конструктивной логике не используют закон исключенного
   третьего или утверждения, из которых он выводится (например, снятие двойного
   отрицания или аксиому выбора). *)

Definition excluded_middle : Prop := forall P : Prop,
  P \/ ~ P.

Theorem dec_eq_nat : forall n m : nat,
  n = m \/ n <> m.
Proof.
  intros n m. destruct (n =? m) eqn:H.
  - left. apply Nat.eqb_eq. exact H.
  - right. apply Nat.eqb_neq. exact H.
Qed.

(* Require Import Logic.Classical. *)

(** Не доказуемы в конструктивной логике:
    ¬¬P ⇒ P
    ¬(P ∧ Q) ⇒ ¬P ∨ ¬Q
    ¬ ∀ x, P x ⇒ ∃ x, ¬ (P x)

    Taking the principle of excluded middle from the mathematician would be the
    same, say, as proscribing the telescope to the astronomer or to the boxer
    the use of his fists.  David Hilber

    Andrej Bauer. Five Stages of Accepting Constructive Mathematics
    https://www.youtube.com/watch?v=21qPOReu4FI *)

(** * Соответствие Карри-Ховарда *)

(**    Логика       Программирование
    ────────────────────────────────
     Утверждения         Типы
    Доказательста      Программы

               Примеры                       на Coq
    ────────────────────────────────
        P ⇒ Q           P → Q                P -> Q
        P ∧ Q           P × Q                P /\ Q
        P ∨ Q           P + Q                P \/ Q
         ¬ P            P → ⊥                  ~ P
     ∀ x ∈ X, P x    Π x : X, P x       forall x : X, P x
     ∃ x ∈ X, P x    Σ x : X, P x       exists x : X, P x
 *)

(* Каждая рекурсивная функция должна завершаться. *)

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.
