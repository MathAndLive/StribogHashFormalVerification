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
       означает в контексте Delta любое состояние, удовлетворяющее P, будет
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
