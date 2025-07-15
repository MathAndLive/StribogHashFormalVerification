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
            x_content : block512, y_content : block512,
            z_content : block512
            (* share = тип доступа к памяти: read/write *)
  PRE [tptr t_streebog_uint512_st, tptr t_streebog_uint512_st,
       tptr t_streebog_uint512_st]
       (* tptr - указатель на ... *)
    PROP(readable_share sh_r; writable_share sh_w;
         Zlength (block512_to_int64s x_content) = 8;
         Zlength (block512_to_int64s y_content) = 8;
         Zlength (block512_to_int64s z_content) = 8)
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

Fixpoint xor_lists_of_int64s (l1 l2 : list Int64.int) : list Int64.int :=
  map (fun e => Int64.xor (fst e) (snd e)) (combine l1 l2).

Lemma xor_block512_is_xor_int64s : forall (x y : block512),
  xor_lists_of_int64s (block512_to_int64s x) (block512_to_int64s y) =
    block512_to_int64s (Vec512.xor x y).
Proof.
  intros x y.
  induction (block512_to_int64s x) as [| b IHb].
  - simpl. destruct block512_to_int64s.
    + reflexivity.
    + Search ([] = ?x).
Admitted.

Lemma xor_int64s_is_xor_block512 : forall (x y : list Int64.int),
  xor_lists_of_int64s x y = block512_to_int64s (Vec512.xor (int64s_to_block512 x) (int64s_to_block512 y)).
Proof.
  (* intros x y x_content y_content i H. *)
  (* unfold block512_to_int64s. unfold Z_to_int64s. unfold Z_to_chunks. unfold LSB. *)
  (* induction i. *)
  (* - unfold block512_to_int64s. unfold Z_to_int64s. unfold Z_to_chunks. *)
Admitted.

Lemma body_sumarray :
  semax_body Vprog [] f_streebog_xor streebog_xor_spec.
Proof.
  start_function.
  assert_PROP (Zlength (block512_to_int64s x_content) = 8). {
    entailer!.
  }
  forward.
  assert_PROP (Zlength (block512_to_int64s y_content) = 8). {
    entailer!.
  }
  forward.
  assert_PROP (Zlength (block512_to_int64s z_content) = 8). {
    entailer!.
  }
  do 22 forward.
  entailer!.
  rewrite <- (xor_block512_is_xor_int64s x_content y_content).
  entailer!.
Qed.
