From VST.floyd Require Import proofauto library.
Require Import streebog_generic.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.

Definition tuint512 := Tstruct _streebog_uint512 noattr.

Definition streebog_xlps_spec :=
  DECLARE _streebog_xlps
  WITH   sh_r : share, sh_w : share,
         x : val, y : val, z : val,
         x_content : block512, y_content : block512, z_content : block512
  PRE [tptr tuint512, tptr tuint512, tptr tuint512]
    PROP(readable_share sh_r; writable_share sh_w)
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
  assert (Zlength (block512_to_int64s x_content) = 8) by reflexivity.
  assert (Zlength (block512_to_int64s y_content) = 8) by reflexivity.
  assert (Zlength (block512_to_int64s z_content) = 8) by reflexivity.

  do 24 forward.

  deadvars!.
  forward_loop
   (EX i:Z, EX j:Z, EX data: list int64,
    PROP (0 <= i <= 8 ;
          0 <= j <  i ;
          nth (Z.to_nat j) data default =
            nth (Z.to_nat j) (block512_to_int64s (LPSX x_content y_content)) Int64.zero)
    LOCAL( )
    SEP()
    ).
  - forward.
    entailer!.
  hint.

Qed.
