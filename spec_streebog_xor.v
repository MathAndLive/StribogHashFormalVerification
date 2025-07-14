From VST.floyd Require Import proofauto library.
Require Import streebog_xor.

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
  DECLARE _streebog_xor
  WITH sh : share, x : val, y : val, z : val,
            left_block : block512, right_block : block512,
            res_block : block512
  PRE [tptr t_streebog_uint512_st, tptr t_streebog_uint512_st,
       tptr t_streebog_uint512_st]
    PROP(readable_share sh)
    PARAMS (x; y; z)
    SEP (field_at sh t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s left_block)) x;
         field_at sh t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s right_block)) y;
         field_at sh t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s res_block)) z)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (field_at sh t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s left_block)) x;
         field_at sh t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s right_block)) y;
         field_at sh t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s (left_block xor right_block))) z).
