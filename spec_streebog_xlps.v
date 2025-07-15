From VST.floyd Require Import proofauto library.
Require Import streebog_xlps.

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

Definition tuint512 := Tstruct _streebog_uint512 noattr.


Definition streebog_xlps_spec :=
  DECLARE _streebog_xlps
  WITH   sh_r : share, sh_w : share,
         x : val, y : val, z : val,
         x_content : block512, y_content : block512, z_content : block512
  PRE [tptr tuint512, tptr tuint512, tptr tuint512]
    PROP(readable_share sh_r; writable_share sh_w;
         Zlength (block512_to_int64s x_content) = 8;
         Zlength (block512_to_int64s y_content) = 8)
    PARAMS (x; y; z)
    SEP (field_at sh_r tuint512 (DOT _qword) (map Vlong (block512_to_int64s x_content)) x;
         field_at sh_r tuint512 (DOT _qword) (map Vlong (block512_to_int64s y_content)) y;
         field_at sh_w tuint512 (DOT _qword) (map Vlong (block512_to_int64s z_content)) z)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (field_at sh_r tuint512 (DOT _qword) (map Vlong (block512_to_int64s x_content)) x;
         field_at sh_r tuint512 (DOT _qword) (map Vlong (block512_to_int64s y_content)) y;
         field_at sh_w tuint512 (DOT _qword)
           (map Vlong (block512_to_int64s (LPSX x_content y_content))) z).

Lemma body_streebog_xlps :
  semax_body Vprog [] f_streebog_xlps streebog_xlps_spec.
Proof.
  start_function.

  forward. forward. forward. (* утверждения, что в массивах xy_content есть индекс 0 *)
  forward. forward. forward. (* утверждения, что в массивах xy_content есть индекс 1 *)
  forward. forward. forward. (* утверждения, что в массивах xy_content есть индекс 2 *)
  forward. forward. forward. (* утверждения, что в массивах xy_content есть индекс 3 *)
  forward. forward. forward. (* утверждения, что в массивах xy_content есть индекс 4 *)
  forward. forward. forward. (* утверждения, что в массивах xy_content есть индекс 5 *)
  forward. forward. forward. (* утверждения, что в массивах xy_content есть индекс 6 *)
  forward. forward. forward. (* утверждения, что в массивах xy_content есть индекс 7 *)

    (* forward_while
    (EX i,
      PROP (0 <= i <= 7)
     *)
  forward.
  assert (0 <= 0 < Zlength (block512_to_int64s x_content))
    by (rewrite (Zlength (field)); simpl; lia).
  forward.
  (* assert_PROP (Zlength (block512_to_int64s x_content) = 8). *)

Qed.
