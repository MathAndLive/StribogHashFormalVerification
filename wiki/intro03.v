Require Import Arith Lia map.

(** * Синтаксис *)

(** Пример программы на нашем простом императивном языке программирования:

    z := x;
    y := 1;
    while z ≠ 0 do
      y := y * z;
      z := z - 1

    Чтобы записывать такие программы нам нужно определить язык команд с
    арифметическими и булевыми выражениями. *)

(** Состояние программы *)

Definition var := nat.
Definition state := var -> nat.
Definition empty_state : state := empty 0.

(** Арифметические выражения в форме Бэкуса-Наура:

    var := nat

    a := nat
       | var
       | a + a
       | a - a
       | a * a    *)

(** Арифметические выражения как индуктивный тип: *)

Inductive aexp : Type :=
| ANum   : nat -> aexp
| AId    : var -> aexp
| APlus  : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult  : aexp -> aexp -> aexp.

(** Арифметическое выражение 1 + 2 * 3 представляется в виде абстрактного
    синтаксического дерева (AST): *)

Check APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

(** Булевы выражения в форме Бэкуса-Наура:

    b := true
       | false
       | a = a
       | a ≠ a
       | a ≤ a
       | a > a
       | ¬ b
       | b ∧ b    *)

(** Булевы выражения как индуктивный тип: *)

Inductive bexp : Type :=
| BTrue  : bexp
| BFalse : bexp
| BEq    : aexp -> aexp -> bexp
| BNeq   : aexp -> aexp -> bexp
| BLe    : aexp -> aexp -> bexp
| BGt    : aexp -> aexp -> bexp
| BNot   : bexp -> bexp
| BAnd   : bexp -> bexp -> bexp.

(** Команды в форме Бэкуса-Наура:

    c := skip
       | x := a
       | c ; c
       | if b then c else c
       | while b do c          *)

(** Команды как индуктивный тип: *)

Inductive com : Type :=
| CSkip  : com
| CAsgn  : var -> aexp -> com
| CSeq   : com -> com -> com
| CIf    : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

(** Бесконечный цикл на нашем императивном языке:

    while true do
      skip           *)

Example loop : com :=
  CWhile BTrue CSkip.

(** z := x;
    y := 1;
    while z ≠ 0 do
      y := y * z;
      z := z - 1      *)

Definition x : var := 0.
Definition y : var := 1.
Definition z : var := 2.

(* Definition factorial : com := *)
(*   CSeq (CAsgn z (AId x)) *)
(*        (CSeq (CAsgn y (ANum 1)) *)
(*              (CWhile (BNeq (AId z) (ANum 0)) *)
(*                 (CSeq (CAsgn y (AMult (AId y) (AId z))) *)
(*                       (CAsgn z (AMinus (AId z) (ANum 1)))))). *)

(** * Семантика *)

(** Виды семантик, которые мы будем использовать:
    - денотационная,
    - операционная,
    - аксиоматическая.    *)

(** Денотационная семантика арифметических выражений: *)

(* Fixpoint aeval (a : aexp) : nat := *)
(*   match a with *)
(*   | ANum n       => n *)
(*   | APlus  a1 a2 => aeval a1 + aeval a2 *)
(*   | AMinus a1 a2 => aeval a1 - aeval a2 *)
(*   | AMult  a1 a2 => aeval a1 * aeval a2 *)
(*   end. *)

(* aeval : aexp -> (state -> nat) *)

Fixpoint aeval (a : aexp) (st : state) : nat :=
  match a with
  | ANum n       => n
  | AId x        => st x
  | APlus  a1 a2 => aeval a1 st + aeval a2 st
  | AMinus a1 a2 => aeval a1 st - aeval a2 st
  | AMult  a1 a2 => aeval a1 st * aeval a2 st
  end.

Compute aeval (APlus (ANum 1) (AMult (ANum 2) (ANum 3))) empty_state.

(** Денотационная семантика булевых выражений: *)

Fixpoint beval (b : bexp) (st : state) : bool :=
  match b with
  | BTrue      => true
  | BFalse     => false
  | BEq  a1 a2 => (aeval a1 st) =? (aeval a2 st)
  | BNeq a1 a2 => negb ((aeval a1 st) =? (aeval a2 st))
  | BLe  a1 a2 => (aeval a1 st) <=? (aeval a2 st)
  | BGt  a1 a2 => negb ((aeval a1 st) <=? (aeval a2 st))
  | BNot b1    => negb (beval b1 st)
  | BAnd b1 b2 => andb (beval b1 st) (beval b2 st)
  end.

(** Денотационная семантика команд (неудачная попытка): *)

Fixpoint ceval' (c : com) (st : state) : state :=
  match c with
  | CSkip       => st
  | CAsgn x a   => update st x (aeval a st)
  | CSeq c1 c2  => ceval' c2 (ceval' c1 st)
  | CIf b c1 c2 => if beval b st then ceval' c1 st else ceval' c2 st
  | CWhile b c  => st
                  (* if beval b st then *)
                  (*   ceval' (CWhile b c) (ceval' c st) *)
                  (* else *)
                  (*   st *)
  end.

(** Операционная семантика (с большим шагом) команд с помощью
    правил вывода:

                   ─────────────────                            (ESkip)
                   st =[ skip ]=> st

                   aeval a st = n
           ────────────────────────────────                     (EAsgn)
           st =[ x := a ]=> (update st x n)

                   st1 =[ c1 ]=> st2
                   st2 =[ c2 ]=> st3
                 ─────────────────────                           (ESeq)
                 st1 =[ c1; c2 ]=> st3

                  beval b st1 = true
                   st1 =[ c1 ]=> st2
         ──────────────────────────────────────               (EIfTrue)
          st1 =[ if b then c1 else c2 ]=> st2

                 beval b st1 = false
                  st1 =[ c2 ]=> st2
        ───────────────────────────────────────              (EIfFalse)
        st1 =[ if b then c1 else c2 end ]=> st2

                  beval b st1 = true
                   st1 =[ c ]=> st2
           st2 =[ while b do c end ]=> st3
           ───────────────────────────────                 (EWhileTrue)
           st1 =[ while b do c end ]=> st3

                 beval b st = false
            ─────────────────────────────                 (EWhileFalse)
            st =[ while b do c end ]=> st                               *)

(** Операционная семантика команд как индуктивный тип *)

Inductive ceval : com -> state -> state -> Prop :=
| ESkip       : forall st, ceval CSkip st st

| EAsgn       : forall st x a, ceval (CAsgn x a) st (update st x (aeval a st))

| ESeq        : forall st1 st2 st3 c1 c2,
                ceval c1 st1 st2 -> ceval c2 st2 st3 ->
                ceval (CSeq c1 c2) st1 st3

| EIfTrue     : forall st1 st2 b c1 c2,
                beval b st1 = true -> ceval c1 st1 st2 ->
                ceval (CIf b c1 c2) st1 st2

| EIfFalse    : forall st1 st2 b c1 c2,
                beval b st1 = false -> ceval c2 st1 st2 ->
                ceval (CIf b c1 c2) st1 st2

| EWhileTrue  : forall st1 st2 st3 b c,
                beval b st1 = true ->
                ceval c st1 st2 ->
                ceval (CWhile b c) st2 st3 ->
                ceval (CWhile b c) st1 st3

| EWhileFalse : forall st b c,
                beval b st = false ->
                ceval (CWhile b c) st st.

Hint Constructors ceval : core.

(** * Логика Флойда-Хоара (аксиоматическая семантика) *)

(** Тройка Хоара - это утверждение о состоянии до и после выполнения
    программы. Обычно его записывают так:

    { P } c { Q }

    Что означает следующее:

    - если программа [c] выполняется в состоянии, удовлетворяющем условию [P],
    - и если [c] завершается в некотором состоянии,
    - то это конечное состояние будет удовлетворять условию [Q].

    Условие [P] называется предусловием, а [Q] - постусловием. *)

(** Правила вывода для логики Флойда-Хоара:

              ────────────             (hoare_skip)
              {P} skip {P}

         ──────────────────────        (hoare_asgn)
         {Q [X ↦ a]} X := a {Q}

              {P} c1 {Q}
              {Q} c2 {R}
            ──────────────              (hoare_seq)
            {P} c1; c2 {R}

           {P ∧   b} c1 {Q}
           {P ∧ ¬ b} c2 {Q}
     ────────────────────────────        (hoare_if)
     {P} if b then c1 else c2 {Q}

            {P ∧ b} c {P}
      ─────────────────────────       (hoare_while)
      {P} while b do c {P ∧ ¬b}

             {P'} c {Q'}
               P  ⇒ P'
               Q' ⇒ Q
       ──────────────────────── (hoare_consequence)
              {P} c {Q}                             *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Definition assertion_sub x a (P : Assertion) : Assertion :=
  fun st => P (update st x (aeval a st)).

Definition bassertion (b : bexp) : Assertion :=
  fun st => beval b st = true.

Lemma bexp_eval_false : forall b st,
  beval b st = false -> ~ bassertion b st.
Proof.
  unfold bassertion. intros b st H0 H1. rewrite H0 in H1. discriminate.
Qed.

Hint Resolve bexp_eval_false : core.
Hint Unfold assert_implies assertion_sub update : core.

Inductive triple : Assertion -> com -> Assertion -> Prop :=
| HSkip        : forall P, triple P CSkip P
| HAsgn        : forall Q x a,
                 triple (assertion_sub x a Q) (CAsgn x a) Q
| HSeq         : forall P c Q d R,
                 triple P c Q -> triple Q d R ->
                 triple P (CSeq c d) R
| HIf          : forall P Q b c1 c2,
                 triple (fun st => P st /\ bassertion b st) c1 Q ->
                 triple (fun st => P st /\ ~ (bassertion b st)) c2 Q ->
                 triple P (CIf b c1 c2) Q

| HWhile       : forall P b c,
                 triple (fun st => P st /\ bassertion b st) c P ->
                 triple P (CWhile b c) (fun st => P st /\ ~ (bassertion b st))

| HConsequence : forall P Q P' Q' c,
                 assert_implies P P' -> assert_implies Q' Q -> triple P' c Q' ->
                 triple P c Q.

(**          {P'} c {Q}
               P  ⇒ P'
       ──────────────────────── (hoare_consequence_pre)
              {P} c {Q}                                 *)

Lemma hoare_consequence_pre : forall (P Q P' : Assertion) (c : com),
  assert_implies P P' -> triple P' c Q -> triple P c Q.
Proof.
  intros P Q P' c HP H. eapply HConsequence; eauto.
  (* apply HP. unfold assert_implies. intros st HQ. apply HQ. assumption. *)
  (* eauto. *)
Qed.

(** { True } x := 1 { x = 1 } *)

Example hoare_asgn_example1 :
  triple (fun st => True) (CAsgn x (ANum 1)) (fun st => st x = 1).
Proof.
  eapply hoare_consequence_pre.
  2: { apply HAsgn. }
  (* unfold assert_implies, assertion_sub, update. simpl. *)
  auto.
Qed.

(** { a = n } x := a; skip { x = n } *)

Example hoare_asgn_example2 : forall (a : aexp) (n : nat),
  triple (fun st => aeval a st = n) (CSeq (CAsgn x a) CSkip) (fun st => st x = n).
Proof.
  intros a n.
  eapply HSeq. 2: { constructor. }
  eapply hoare_consequence_pre. 2: { constructor. }
  auto.
Qed.

(** * Корректность логики Флойда-Хоара *)

(** {P} c {Q}:
    - если команда [c] выполняется в состоянии, удовлетворяющем условию [P],
    - и если [c] завершается в некотором состоянии,
    - то это конечное состояние будет удовлетворять условию [Q].   *)

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st', ceval c st st' -> P st -> Q st'.

Theorem hoare_sound : forall P c Q,
  triple P c Q -> valid P c Q.
Proof.
  intros P c Q H. induction H.
  - 
Abort.

Lemma hoare_skip : forall P, valid P CSkip P.
Proof.
  intros P st st' Hc HP. inversion Hc. subst. assumption.
Qed.

Lemma hoare_asgn : forall Q x a,
  valid (assertion_sub x a Q) (CAsgn x a) Q.
Proof.
  intros Q x a st st' Hc HP.
  inversion Hc; subst. assumption.
Qed.

Lemma hoare_seq : forall P Q R c d,
  valid P c Q -> valid Q d R ->
  valid P (CSeq c d) R.
Proof.
  intros P Q R c d H0 H1 st st' Hseq HP.
  inversion Hseq; subst. eauto.
Qed.

Lemma hoare_if : forall P Q b c1 c2,
  valid (fun st => P st /\ bassertion b st) c1 Q ->
  valid (fun st => P st /\ ~ bassertion b st) c2 Q ->
  valid P (CIf b c1 c2) Q.
Proof.
  intros P Q b c1 c2 H0 H1 st st' Hif HP. inversion Hif; subst; eauto.
Qed.

Lemma hoare_while : forall P b c,
  valid (fun st => P st /\ bassertion b st) c P ->
  valid P (CWhile b c) (fun st => P st /\ ~ bassertion b st).
Proof.
  intros P b c H st st' Hw HP.
  remember (CWhile b c) as d eqn:H0.
  induction Hw; inversion H0; subst; eauto.
Qed.

Lemma hoare_consequence : forall P P' Q' Q c,
  assert_implies P P' -> assert_implies Q' Q -> valid P' c Q' ->
  valid P c Q.
Proof.
  intros P P' Q Q' c Hpre Hpost H st st' Hc HP. eauto.
Qed.

Theorem hoare_sound : forall P c Q,
  triple P c Q -> valid P c Q.
Proof.
  intros P c Q H. induction H.
  - apply hoare_skip.
  - apply hoare_asgn.
  - apply hoare_seq with (Q := Q); assumption.
  - apply hoare_if; assumption.
  - apply hoare_while. assumption.
  - apply hoare_consequence with (P' := P') (Q' := Q'); assumption.
Qed.

(**
Запись:
https://dion.vc/video/0e19f251-7fbd-46c2-807e-d857cf566413

Читать можно Software Foundations:
- в томе 1 про синтаксис и семантику:
  https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html
- в томе 2 про логику Флойда-Хоара:
  https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html
  https://softwarefoundations.cis.upenn.edu/plf-current/HoareAsLogic.html

Дополнително:
- сепарационной логике (расширению логики Флойда-Хоара) посвящен том 6 Software Foundations
  https://softwarefoundations.cis.upenn.edu/slf-current/index.html
- книга про семантику: Nipkow, Klein. Concrete Semantics (написанна с помощью Isabell/HOL, но определения понятны и переводятся на Coq)
- материалы с курсу по семантике от Xavier Leroy (основной разработик компиляторов OCaml и CompCert)
  https://xavierleroy.org/CdF/2019-2020/
- компилятор CompCert: https://github.com/AbsInt/CompCert

*)

(** * Установка VST *)

(** Coq-пакеты находятся в отдельном репозитории:

$ opam repo add coq-released https://coq.inria.fr/opam/released

Нам нужна последняя стабильная версия пакета coq-vst:

$ opam pin add coq-vst 2.15    *)

(** * sumarray *)

(** Функция в файле sumarray.c:

    int sumarray(unsigned arr[], int length) {
        unsigned sum = 0;
        int i = 0;

        while (i < length) {
            sum += arr[i];
            i++;
        }

        return sum;
    }

    Используем утилиту clightgen из CompCert для получения AST программы:

    $ clightgen -normalize sumarray.c

    Получаем файл sumarray.v, который компилируем и импортируем.

    $ coqc sumarray.v    *)

(* Импортируем определения из VST и AST нашей программы. CompSpecs нужен для
   работы со структурами (struct) из AST, Vprog - для глобальных переменных. *)

From VST.floyd Require Import proofauto library.
Require Import sumarray reverse.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** * Функциональная спецификация sumarray *)

Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app : forall xs ys,
  sum_Z (xs ++ ys) = sum_Z xs + sum_Z ys.
Proof.
  intros xs ys. induction xs as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. apply Z.add_assoc.
Qed.

Lemma sum_Z_sublist_last : forall i l, 0 <= i < Zlength l ->
  sum_Z (sublist 0 (i + 1) l) = sum_Z (sublist 0 i l) + Znth i l.
Proof.
  intros i l H.
    (* sum_Z (sublist 0 (i + 1) l) = *)
(*        sum_Z (sublist 0 i l ++ [Znth i l]) = *)
(*        sum_Z (sublist 0 i l) + sum_Z [Znth i l] = *)
(*        sum_Z (sublist 0 i l) + Znth i l *)
  rewrite sublist_last_1 by lia.
  rewrite sum_Z_app. simpl. lia.
Qed.

(** * Тройка Хоара для sumarray *)

(** { arr ↦ contents } sumarray(arr, len) { arr ↦ contents ∧ result = sum_Z contents }

    При любом вызове sumarray существуют sh, arr, contents, len, такие что:
    - sh предоставляет право на чтение;
    - 0 ≤ len ≤ 2^32 / 2 - 1
    - первый параметр функции содержит значение arr, а второй содержит
      32-битное представление len;
    - в памяти по адресу arr находится массив с разрешением sh, содержащий
      элементы contents.

    Функция возвращает значение, равное [sum_Z contents], и оставляет массив
    в памяти неизменным. *)

Definition sumarray_spec :=
  DECLARE _sumarray
  WITH sh : share, arr : val, contents : list Z, len : Z
  PRE [tptr tuint, tint]
    PROP (readable_share sh; 0 <= len <= Int.max_signed)
    PARAMS (arr; Vint (Int.repr len))
    SEP (data_at sh (tarray tuint len) (map (fun x => Vint (Int.repr x)) contents) arr)
  POST [tuint]
    PROP ()
    RETURN (Vint (Int.repr (sum_Z contents)))
    SEP (data_at sh (tarray tuint len) (map (fun x => Vint (Int.repr x)) contents) arr).

(** * Доказательство тройки Хоара для sumarray *)

Lemma body_sumarray :
  semax_body Vprog [] f_sumarray sumarray_spec.
Proof.
  start_function.
  (* unfold MORE_COMMANDS, abbreviate. *)
  (* unfold POSTCONDITION, abbreviate. *)
  forward.
  (* hint. *)                (* не оставляйте hint *)
  forward.
  Check 0.                   (* : Z   - целые числа *)
  Check (Int.repr 0).        (* : int - 32-битные целые числа *)
  Check (Vint (Int.repr 0)). (* : val - тип для значений из CompCert *)
  (* hint. *)
  (* ∃ i, 0 ≤ i ≤ len ∧ sum = Σ^i_{k = 0} contents *)
  forward_while
    (EX i,
      PROP (0 <= i <= len)
      LOCAL (temp _i (Vint (Int.repr i));
             temp _sum (Vint (Int.repr (sum_Z (sublist 0 i contents))));
             temp _arr arr;
             temp _len (Vint (Int.repr len)))
      SEP (data_at sh (tarray tuint len) (map (fun x => Vint (Int.repr x)) contents) arr)).
  - (* текущее предусловие удовлетворяет инварианту цикла *)
    (* нужно доказать выражение (entailment) вида ENTAIL Delta, P |-- Q, которое
       означает "в контексте Delta любое состояние, удовлетворяющее P, будет
       удовлетворять Q *)
    Exists 0.
    (* для упрощения entailment *)
    entailer!.
  - (* условие цикла (i < len) корректно *)
    entailer!.
  - (* тело цикла удовлетворяет инварианту *)
    Fail forward.
    assert_PROP (Zlength contents = len).
    { entailer!.
      (* [Search Zlength map] or use list_solve *)
      list_solve. }
    do 3 forward.
    Exists (i + 1).
    entailer!.
    f_equal. f_equal.
    apply sum_Z_sublist_last. lia.
  - (* после цикла *)
    forward.
    entailer!.
    assert (i = Zlength contents) by list_solve.
    autorewrite with sublist. reflexivity.
Qed.

(** * reverse *)

(** Программа в файле reverse.c:

    struct list {
        unsigned head;
        struct list *tail;
    };

    struct list *reverse(struct list *l) {
        struct list *t, *r = NULL;

        while (l) {
            t = l;
            l = l->tail;
            t->tail = r;
            r = t;
        }

        return r;
    }
*)

(** * Тройка Хоара для reverse *)

Definition tlist : type := Tstruct _list noattr.

Fixpoint listrep (xs : list val) (p : val) : mpred :=
  match xs with
  | [] => !! (p = nullval) && emp
  | x :: xs => EX q, data_at Ews tlist (x , q) p
                 * listrep xs q
  end.

Lemma listrep_valid_pointer : forall xs p,
  listrep xs p |-- valid_pointer p.
Proof.
  intros xs p. destruct xs;
    unfold listrep; fold listrep.
  - entailer!.
  - Intros q. auto with valid_pointer.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_local_facts : forall xs p,
  listrep xs p |-- !! (is_pointer_or_null p /\ (p = nullval -> xs = [])).
Proof.
  intros xs p. destruct xs as [| x xs];
    unfold listrep; fold listrep.
  - entailer!.
  - Intros q. entailer!.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Definition reverse_spec :=
  DECLARE _reverse
  WITH l : val, xs : list val
  PRE [tptr tlist]
    PROP ()
    PARAMS (l)
    SEP (listrep xs l)
  POST [tptr tlist]
    EX r,
      PROP ()
      RETURN (r)
      SEP (listrep (rev xs) r).

Lemma body_reverse :
  semax_body Vprog [] f_reverse reverse_spec.
Proof.
  start_function.
  forward.
  forward_while
    (EX r p ys zs,
      PROP (rev xs = rev zs ++ ys)
      LOCAL (temp _r r; temp _l p)
      SEP (listrep ys r; listrep zs p)).
  - Exists nullval l (@nil val) xs.
    rewrite app_nil_r.
    unfold listrep; fold listrep. entailer!.
  - entailer!.
  - forward.
    destruct zs as [| z zs]; unfold listrep; fold listrep.
    + Intros. subst. contradiction.
    + Intros q. do 3 forward.
      Exists (p, q, z :: ys, zs).
      unfold fst, snd, listrep; fold listrep.
      assert (rev (z :: zs) ++ ys = rev zs ++ z :: ys).
      { simpl. rewrite <- app_assoc. reflexivity. }
      Exists r. entailer!.
  - forward. Exists r.
    rewrite H, H1 by reflexivity. simpl. entailer!.
Qed.

(** Читать можно:
- Software Foundations vol. 5: https://softwarefoundations.cis.upenn.edu/vc-current/Preface.html, https://softwarefoundations.cis.upenn.edu/vc-current/Verif_sumarray.html и https://softwarefoundations.cis.upenn.edu/vc-current/Verif_reverse.html
- руководство по тактикам VST https://raw.githubusercontent.com/PrincetonUniversity/VST/master/doc/VC.pdf

Дополнительно:
- дальше Software Foundations vol. 5 до https://softwarefoundations.cis.upenn.edu/vc-current/Verif_hash.html, где доказывается корректность реализации хеш-таблиц
- статья по верификации функции хеширования SHA-256 https://www.cs.princeton.edu/~appel/papers/verif-sha-2.pdf
- книга Appel, Program Logics for Certified Compilers https://www.cs.princeton.edu/~appel/papers/plcc.pdf *)
