From VST.floyd Require Import proofauto library.
Require Import streebog_generic.
Require Import compcert.lib.Zbits.

Require Import Coq.Lists.List.
Import ListNotations.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.

Definition tuint512 := Tstruct _streebog_uint512 noattr.

Definition block512_to_chunks (b : block512) : list Z :=
  Z_to_chunks 64 8 (Vec512.unsigned b).

Definition block512_to_vals (b : block512) : list val :=
  map (fun x => Vlong (Int64.repr x)) (block512_to_chunks b).

Definition streebog_xlps_spec :=
  DECLARE _streebog_xlps
  WITH sh_r : share, sh_w : share,
       x : val, y : val, z : val,
       x_content : block512, y_content : block512, z_content : block512
  PRE [tptr tuint512, tptr tuint512, tptr tuint512]
    PROP(readable_share sh_r; writable_share sh_w)
    PARAMS (x; y; z)
    SEP (data_at sh_r tuint512 (block512_to_vals x_content) x;
         data_at sh_r tuint512 (block512_to_vals y_content) y;
         data_at_ sh_w tuint512 z)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (data_at sh_r tuint512 (block512_to_vals x_content) x;
         data_at sh_r tuint512 (block512_to_vals y_content) y;
         data_at sh_w tuint512 (block512_to_vals (LPSX x_content y_content)) z).

Definition inv_data_mem (i : Z) (x y z : val) (x_content y_content z_content : block512) : mpred :=
  (data_at Ews tuint512 (block512_to_vals x_content) x &&
   data_at Ews tuint512 (block512_to_vals y_content) y &&
   data_at Ews tuint512 (block512_to_vals (int64s_to_block512
      (sublist 0 i (block512_to_int64s (LPSX x_content y_content)) ++
                            (sublist i 8 (block512_to_int64s z_content))))) z).


Definition A_Z := map Int64.unsigned A.
Definition A_rev := rev A.
Definition A_rev_Z := map Int64.unsigned A_rev.

Fixpoint dec_to_bin (t : Z) (n : nat): list Z :=
  match n with
  | O => []
  | S n' => Z_mod_two_p t 1 :: dec_to_bin (Z.shiftr t 1) n'
  end.

Compute Z_mod_two_p 252 1.
Compute dec_to_bin 252 8.

Fixpoint calc_a (A : list Z) (t : Z) (a : int64): int64 :=
  match A with
    | [] => a
    | x :: xs => let x' := Z_mod_two_p t 1 * x
      in calc_a xs (Z.shiftr t 1) (Int64.xor a (Int64.repr x'))
  end.


Definition create_Ax_line (A : list Z) : list int64 :=
  map (fun t => calc_a A t Int64.zero) (map Byte.unsigned pi').

Fixpoint create_Ax (A : list Z) (j : nat) : list (list int64) :=
  match j with
  | O => []
  | S j' => create_Ax_line (firstn 8 A) :: create_Ax (skipn 8 A) j'
  end.


Definition Ax : list (list int64) := create_Ax A_rev_Z 8.

Compute Ax.

Compute 0xd01f715b5c7ef8e6. (*14996829921374828774*)
Compute 0x16fa240980778325. (*1655675436240700197*)
Compute 0xa8a42e857ee049c8. (*12151888845446597064*)
(* ... *)
Compute 0xd6a30f258c153427. (*15466222199258821671*)



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
    LOCAL ( )
    SEP (inv_data_mem i x y z x_content y_content z_content)
    ).
  - forward.
    entailer!.
    lia .
    hint.
  - hint.

Qed.
