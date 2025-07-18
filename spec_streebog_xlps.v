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
    SEP (data_at sh_r tuint512 (map Vlong (block512_to_int64s x_content)) x;
         data_at sh_r tuint512 (map Vlong (block512_to_int64s y_content)) y;
         data_at sh_w tuint512 (map Vlong (block512_to_int64s z_content)) z)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (data_at sh_r tuint512 (map Vlong (block512_to_int64s x_content)) x;
         data_at sh_r tuint512 (map Vlong (block512_to_int64s y_content)) y;
         data_at sh_w tuint512
           (map Vlong (block512_to_int64s (LPSX x_content y_content))) z).

Definition inv_data_mem (sh_r : share) (i : Z) (x : val) (x_content : block512) : mpred :=
  (data_at sh_r tuint512 (map Vlong (block512_to_int64s x_content)) x).

Definition inv_data_mem_result (sh_w : share) (i : Z) (z : val) (x_content y_content z_content : block512) : mpred :=
  (data_at sh_w tuint512 (map Vlong ((sublist 0 i (block512_to_int64s
    (LPSX x_content y_content)) ++ (sublist i 8 (block512_to_int64s z_content))))) z).

(* SEP (inv_data_mem i x y z x_content y_content z_content) *)

     (* PROP (0 <= i <= 8; *)
     (*       sublist 0 i (block512_to_int64s (LPSX x_content y_content)) = *)
     (*        sublist 0 i (block512_to_int64s z_content)) *)
     (* LOCAL (temp _x x; *)
     (*        temp _y y; *)
     (*        temp _z z) *)
     (* SEP (data_at sh_r tuint512 (map Vlong (block512_to_int64s x_content)) x; *)
     (*       data_at sh_r tuint512 (map Vlong (block512_to_int64s y_content)) y; *)
     (*       data_at sh_w tuint512 (map Vlong (sublist 0 i (block512_to_int64s *)
     (*        (LPSX x_content y_content)) ++ (sublist i 8 (block512_to_int64s z_content)))) z) *)

Definition sumarray_Inv sh_r sh_w x y z x_content y_content z_content i :=
   (PROP (0 <= i <= 8;
           sublist 0 i (block512_to_int64s (LPSX x_content y_content)) =
            sublist 0 i (block512_to_int64s z_content))
     LOCAL (temp _i (Vint (Int.repr i));
             temp _x x;
            temp _y y;
            temp _z z)
     SEP (data_at sh_r tuint512 (map Vlong (block512_to_int64s x_content)) x;
           data_at sh_r tuint512 (map Vlong (block512_to_int64s y_content)) y;
           data_at sh_w tuint512 (map Vlong (sublist 0 i (block512_to_int64s
            (LPSX x_content y_content)) ++ (sublist i 8 (block512_to_int64s z_content)))) z)
   ).

Lemma body_streebog_xlps :
  semax_body Vprog [] f_streebog_xlps streebog_xlps_spec.
Proof.
  start_function.
  assert (Zlength (block512_to_int64s x_content) = 8) by reflexivity.
  assert (Zlength (block512_to_int64s y_content) = 8) by reflexivity.
  assert (Zlength (block512_to_int64s z_content) = 8) by reflexivity.

  do 24 forward.

  deadvars!.
  forward_for_simple_bound 8
  (EX i:Z,
    PROP (
           sublist 0 i (block512_to_int64s (LPSX x_content y_content)) =
            sublist 0 i (block512_to_int64s z_content))
     LOCAL (temp _Ax Ax;
            temp _r0 r0;
            temp _r1 r1;
            temp _r2 r2;
            temp _r3 r3;
            temp _r4 r4;
            temp _r5 r5;
            temp _r6 r6;
            temp _r7 r7)
      SEP (inv_data_mem sh_r i x x_content;
           inv_data_mem sh_r i y y_content;
           inv_data_mem_result sh_w i z x_content y_content z_content)).
  - entailer!.
  - forward.
Qed.
