From VST.floyd Require Import proofauto library.
Require Import streebog_generic.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.

Definition tuint512 := Tstruct _streebog_uint512 noattr.

Fixpoint gen_Ax_row (m i j : nat) :=
  match j with
  | O => nil
  | S j' => (tableLPS_i_j (Z.of_nat i) (Z.of_nat (m - j))) :: (gen_Ax_row m i j')
  end.

Fixpoint gen_Ax' (n m i : nat) :=
  match i with
  | O => nil
  | S i' => (gen_Ax_row m (n - i) m) :: (gen_Ax' n m i')
  end.

Definition gen_Ax := gen_Ax' 8 256 8.

Example test1: (Znth 0 (Znth 0 gen_Ax)) = Int64.repr 0xd01f715b5c7ef8e6.
Proof. reflexivity. Qed.

Example test3: (Znth 255 (Znth 7 gen_Ax)) = Int64.repr 0xd6a30f258c153427.
Proof. reflexivity. Qed.

Example test5: (Znth 1 (Znth 1 gen_Ax)) = Int64.repr 0x1906b59631b4f565.
Proof. reflexivity. Qed.


Definition block512_to_chunks (b : block512) : list Z :=
  Z_to_chunks 64 8 (Vec512.unsigned b).

Definition block512_to_vals (b : block512) : list val :=
  map (fun x => Vlong (Int64.repr x)) (block512_to_chunks b).


Definition data_mem (sh_r : share) (x : val) (x_content : block512) : mpred :=
  data_at sh_r tuint512 (block512_to_vals x_content) x.

Definition result_data_mem (sh_w : share) (i : Z) (z : val)
  (x_content y_content z_content : block512) : mpred :=
    (data_at sh_w tuint512 ((sublist 0 i (block512_to_vals (LPSX x_content y_content))) ++
        (sublist i 8 (block512_to_vals z_content))) z).

Definition Ax_data_mem (sh_r : share) (Ax : val) : mpred :=
   data_at sh_r (tarray (tarray tlong 256) 8) (map (map Vlong) gen_Ax) Ax.


Definition streebog_xlps_spec :=
  DECLARE _streebog_xlps
  WITH   sh_r : share, sh_w : share,
         x : val, y : val, z : val,
         x_content : block512, y_content : block512, z_content : block512,
         Ax: val
  PRE [tptr tuint512, tptr tuint512, tptr tuint512]
    PROP(readable_share sh_r; writable_share sh_w)
    PARAMS (x; y; z)
    SEP (
        data_mem sh_r x x_content;
        data_mem sh_r y y_content;
        data_mem sh_w z z_content;
        Ax_data_mem sh_r Ax)
        (* data_at sh_r tuint512 (block512_to_vals x_content) x; *)
        (* data_at sh_r tuint512 (block512_to_vals y_content) y; *)
        (* data_at sh_w tuint512 (block512_to_vals z_content) z; *)
     (* data_at sh_r (tarray (tarray tlong 256) 8) (map (map Vlong) gen_Ax) Ax) *)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (
        data_mem sh_r x x_content;
        data_mem sh_r y y_content;
        result_data_mem sh_w 8 z x_content y_content z_content;
        Ax_data_mem sh_r Ax).
        (* data_at sh_w tuint512 (block512_to_vals (LPSX x_content y_content)) z; *)
     (* data_at sh_r (tarray (tarray tlong 256) 8) (map (map Vlong) gen_Ax) Ax). *)

Lemma body_streebog_xlps :
  semax_body Vprog [] f_streebog_xlps streebog_xlps_spec.
Proof.
  start_function.
  assert (Zlength (block512_to_vals x_content) = 8) by reflexivity.
  assert (Zlength (block512_to_vals y_content) = 8) by reflexivity.
  assert (Zlength (map (map Vlong) gen_Ax) = 8) by reflexivity.
  assert (Zlength (Znth 0 (map (map Vlong) gen_Ax)) = 256) by reflexivity.
  assert (Zlength (Znth 1 (map (map Vlong) gen_Ax)) = 256) by reflexivity.
  assert (Zlength (Znth 2 (map (map Vlong) gen_Ax)) = 256) by reflexivity.
  assert (Zlength (Znth 3 (map (map Vlong) gen_Ax)) = 256) by reflexivity.
  assert (Zlength (Znth 4 (map (map Vlong) gen_Ax)) = 256) by reflexivity.
  assert (Zlength (Znth 5 (map (map Vlong) gen_Ax)) = 256) by reflexivity.
  assert (Zlength (Znth 6 (map (map Vlong) gen_Ax)) = 256) by reflexivity.
  assert (Zlength (Znth 7 (map (map Vlong) gen_Ax)) = 256) by reflexivity.
 
  unfold data_mem, result_data_mem, Ax_data_mem.
  do 24 forward.

  deadvars!.
  forward_loop
  (EX i:Z, 
          (* EX r0:val, EX r1:val, EX r2:val, EX r3:val, EX r4:val, EX r5:val, *)
          (*  EX r6:val, EX r7:val, *)
     PROP (0 <= i <= 8;
          sublist 0 i (block512_to_vals (LPSX x_content y_content)) =
          sublist 0 i (block512_to_vals z_content))
     LOCAL (temp _i (Vint (Int.repr i)))
     SEP (data_mem sh_r x x_content;
          data_mem sh_r y y_content;
          result_data_mem sh_w i z x_content y_content z_content;
          Ax_data_mem sh_r Ax)).
  - forward. 
    entailer!.
    Exists 0.
    entailer!.
    (* unfold result_data_mem. entailer!. rewrite (sublist_same 0 8). *)
    (* autorewrite with sublist. entailer!. *)
  - Intros i.
    forward_if.
    abbreviate_semax.
    unfold data_mem, result_data_mem, Ax_data_mem.
    forward.
Qed.
