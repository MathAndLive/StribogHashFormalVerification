From VST.floyd Require Import proofauto library.
Require Import streebog_generic.
Require Import compcert.lib.Zbits.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.

(* Check (@nil (list val)).  *)

Definition tuint512 := Tstruct _streebog_uint512 noattr.

Definition block512_to_chunks (b : block512) : list Z :=
  Z_to_chunks 64 8 (Vec512.unsigned b).

Definition block512_to_vals (b : block512) : list val :=
  map (fun x => Vlong (Int64.repr x)) (block512_to_chunks b).

Definition Ax_to_vals (a : list (list int64)) : list (list val) :=
  map (fun i => map (fun j => Vlong j) i) a.


Definition gen_Ax : list (list int64) :=
  map (fun i =>
         map (fun j =>
                tableLPS_i_j (Z.of_nat i) (Z.of_nat j))
             (seq 0 256))
      (seq 0 8).

Definition streebog_xlps_spec :=
  DECLARE _streebog_xlps
  WITH sh_r : share, sh_w : share,
       x : val, y : val, z : val,
       x_content : block512, y_content : block512, z_content : block512,
       Ax : val
  PRE [tptr tuint512, tptr tuint512, tptr tuint512]
    PROP(readable_share sh_r; writable_share sh_w)
    PARAMS (x; y; z)
    SEP (data_at sh_r tuint512 (block512_to_vals x_content) x;
         data_at sh_r tuint512 (block512_to_vals y_content) y;
         data_at sh_w tuint512 (block512_to_vals z_content) z;
         data_at sh_r (tarray (tarray tulong 256) 8) (Ax_to_vals gen_Ax) Ax)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (data_at sh_r tuint512 (block512_to_vals x_content) x;
         data_at sh_r tuint512 (block512_to_vals y_content) y;
         data_at sh_w tuint512 (block512_to_vals (LPSX x_content y_content)) z;
         data_at sh_r (tarray (tarray tulong 256) 8) (Ax_to_vals gen_Ax) Ax).


Definition inv_data_mem (sh :share) (x : val) (x_content : block512) : mpred :=
  data_at sh tuint512 (block512_to_vals x_content) x.

Definition inv_data_mem_res (sh :share) (i : Z) (z : val) (x_content y_content z_content : block512) : mpred :=
  (
   data_at sh tuint512 (
      (sublist 0 i (block512_to_vals (LPSX x_content y_content)) ++
                            (sublist i 8 (block512_to_vals z_content)))) z).

(*
Definition A_rev := rev A.

Fixpoint calc_a (A : list int64) (t : Z) (i : nat) (a : int64): int64 :=
  match i with
  | O => a
  | S i' => match A with
    | [] => a
    | x :: xs => let x' := Z_mod_two_p t 1 * x
      in calc_a xs (Z.shiftr 1 t) i' (Int64.xor a x)
    end
  end.

Fixpoint create_Ax (pi : list byte) (A : list int64) (i : Z) : list int64 :=
  match i with
  | O => []
  | S i' =>
    match pi with
    | [] => []
    | x :: xs =>
    end
  end.

Fixpoint create_Ax (pi : list byte) (A : list int64) : list (list int64) . *)




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
   (EX i:Z,(*EX j:Z, EX data: list int64,*) 
    PROP(0 <= i <= 7)
    LOCAL (temp _i (Vint (Int.repr i)))
    SEP (inv_data_mem sh_r x x_content; inv_data_mem sh_r y y_content; 
         inv_data_mem_res sh_w i z x_content y_content z_content;
         data_at sh_r (tarray (tarray tulong 256) 8) (Ax_to_vals gen_Ax) Ax)
    ).
  - forward.
    entailer!.
    Exists 0. 
    entailer!. 
  - hint. Intros i. hint.
    forward_if.
    + hint. abbreviate_semax. unfold Ax_to_vals. forward.
    + 
    unfold inv_data_mem.
    unfold inv_data_mem_res.
    simpl.
    autorewrite with sublist.
    entailer!.
    hint.
    lia .
    hint.
  - hint.

Qed.
