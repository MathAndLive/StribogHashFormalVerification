From VST.floyd Require Import proofauto library.
Require Import streebog_generic.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.

(*
struct streebog_uint512 {
	__le64 qword[8];
};

void streebog_xor(const struct streebog_uint512 *x,
			 const struct streebog_uint512 *y,
			 struct streebog_uint512 *z)
{
	z->qword[0] = x->qword[0] ^ y->qword[0];
	z->qword[1] = x->qword[1] ^ y->qword[1];
	z->qword[2] = x->qword[2] ^ y->qword[2];
	z->qword[3] = x->qword[3] ^ y->qword[3];
	z->qword[4] = x->qword[4] ^ y->qword[4];
	z->qword[5] = x->qword[5] ^ y->qword[5];
	z->qword[6] = x->qword[6] ^ y->qword[6];
	z->qword[7] = x->qword[7] ^ y->qword[7];
}
*)

Definition t_streebog_uint512_st := Tstruct _streebog_uint512 noattr.
Definition streebog_uint512_arr_length := 8.

Check _streebog_uint512.
Print t_streebog_uint512_st.

Definition streebog_xor_spec :=
  DECLARE _streebog_xor (* название верифицируемой функции из сгенерированного файла .v*)
  WITH sh_r : share, sh_w : share, x : val, y : val, z : val,
            x_content : block512, y_content : block512, z_content : block512
            (* share = тип доступа к памяти: read/write *)
  PRE [tptr t_streebog_uint512_st, tptr t_streebog_uint512_st,
       tptr t_streebog_uint512_st]
       (* tptr - указатель на ... *)
    PROP(readable_share sh_r; writable_share sh_w)
    PARAMS (x; y; z) (* аргументы верифицируемой функции на C *)
    SEP (field_at sh_r t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s x_content)) x;
         field_at sh_r t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s y_content)) y;
         field_at sh_w t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s z_content)) z)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (field_at sh_r t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s x_content)) x;
         field_at sh_r t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s y_content)) y;
         field_at sh_w t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s (Vec512.xor x_content y_content))) z).

Definition xor_lists_of_int64s (l1 l2 : list Int64.int) : list Int64.int :=
  map (fun e => Int64.xor (fst e) (snd e)) (combine l1 l2).

Lemma Z_to_int64s_plus_one : forall n b,
  Z_to_int64s (S n) (Vec512.unsigned b) =
    Int64.repr (LSB 64 (Vec512.unsigned b)) ::
      Z_to_int64s n (Z.shiftr (Vec512.unsigned b) 64).
Proof.
  reflexivity.
Qed.

Lemma xor_lists_distr : forall (x y : Int64.int) (xs ys : list Int64.int),
  xor_lists_of_int64s (x::xs) (y::ys) =
    (Int64.xor x y) :: xor_lists_of_int64s xs ys.
Proof.
Admitted.

Lemma unsigned_shr_comm : forall x,
  Vec512.unsigned (Vec512.shr (Vec512.repr 64) x) = Z.shiftr (Vec512.unsigned x) 64.
Proof.
Admitted.

Lemma xor_unsigned_comm : forall x y,
  Z.lxor (Vec512.unsigned x) (Vec512.unsigned y) = Vec512.unsigned (Vec512.xor x y).
Proof.
Admitted.

Lemma xor_LSB_comm : forall x y,
  Z.lxor (LSB 64 x) (LSB 64 y) = LSB 64 (Z.lxor x y).
Proof.
Admitted.

Lemma xor_repr_comm : forall x y,
  Int64.xor (Int64.repr x) (Int64.repr y) = Int64.repr (Z.lxor x y).
Proof.
Admitted.


Lemma shiftr_xor : forall x y : block512,
  Z.shiftr (Vec512.unsigned (Vec512.xor x y)) 64 =
    Vec512.unsigned (Vec512.xor
      (Vec512.shr (Vec512.repr 64) x)
      (Vec512.shr (Vec512.repr 64) y)).
Proof.
  intros x y.
Admitted.

Lemma Z_to_int64s_xor : forall n x y,
  xor_lists_of_int64s (Z_to_int64s n (Vec512.unsigned x))
    (Z_to_int64s n (Vec512.unsigned y)) =
  Z_to_int64s n (Vec512.unsigned (Vec512.xor x y)).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - unfold Z_to_int64s; fold Z_to_int64s. simpl. reflexivity.
  - intros x y.
    rewrite 3!Z_to_int64s_plus_one.
    rewrite shiftr_xor.
    rewrite <- (IHn' (Vec512.shr (Vec512.repr 64) x) (Vec512.shr (Vec512.repr 64) y)).
    rewrite xor_lists_distr. 
    rewrite 2!unsigned_shr_comm.
    rewrite xor_repr_comm.
    rewrite xor_LSB_comm.
    rewrite xor_unsigned_comm.
    reflexivity.
Qed.

(* Lemma xor_block512_is_xor_int64s : forall (x y : block512), *)
(*   xor_lists_of_int64s (block512_to_int64s x) (block512_to_int64s y) = *)
(*     block512_to_int64s (Vec512.xor x y). *)
(* Proof. *)
  (* intros x y H1 H2. *)
  (* unfold xor_lists_of_int64s. *)
  (* unfold Vec512.xor. *)
  (* unfold Vec512.unsigned. *)
  (* unfold Vec512.repr. *)
  (* unfold block512_to_int64s. *)
  (* unfold Z_to_int64s. *)
  (* unfold Z_to_chunks. *)
  (* Search (Vec512.xor). *)
(* Admitted. *)

(* Lemma xor_int64s_is_xor_block512 : forall (x y : list Int64.int), *)
(*   xor_lists_of_int64s x y = block512_to_int64s (Vec512.xor (int64s_to_block512 x) (int64s_to_block512 y)). *)
(* Proof. *)
  (* intros x y x_content y_content i H. *)
  (* unfold block512_to_int64s. unfold Z_to_int64s. unfold Z_to_chunks. unfold LSB. *)
  (* induction i. *)
  (* - unfold block512_to_int64s. unfold Z_to_int64s. unfold Z_to_chunks. *)
(* Admitted. *)

Lemma body_sumarray :
  semax_body Vprog [] f_streebog_xor streebog_xor_spec.
Proof.
  start_function.
  assert (Zlength (block512_to_int64s x_content) = 8) by reflexivity.
  assert (Zlength (block512_to_int64s y_content) = 8) by reflexivity.
  assert (Zlength (block512_to_int64s z_content) = 8) by reflexivity.
  do 24 forward.
  entailer!.
  (* rewrite <- xor_block512_is_xor_int64s. *)
  unfold block512_to_int64s.
  rewrite <- (Z_to_int64s_xor 8).
  entailer!.
Qed.
