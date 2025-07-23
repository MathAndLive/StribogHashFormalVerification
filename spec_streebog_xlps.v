From VST.floyd Require Import proofauto library.
Require Import streebog_generic.
Require Import spec_streebog_xor.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.

Definition tuint512 := Tstruct _streebog_uint512 noattr.

Fixpoint gen_Ax_row (m i j : nat) :=
  match j with
  | O => nil
  | S j' => (tableLPS_i_j (Z.of_nat i) (Byte.repr (Z.of_nat (m - j)))) :: (gen_Ax_row m i j')
  end.

Fixpoint gen_Ax' (n m i : nat) :=
  match i with
  | O => nil
  | S i' => (gen_Ax_row m (n - i) m) :: (gen_Ax' n m i')
  end.

Definition gen_Ax := gen_Ax' 8 256 8.

Definition Ax_vals := (map (map Vlong) gen_Ax).

Example test1: (Znth 0 (Znth 0 gen_Ax)) = Int64.repr 0xd01f715b5c7ef8e6.
Proof. reflexivity. Qed.

Example test3: (Znth 255 (Znth 7 gen_Ax)) = Int64.repr 0xd6a30f258c153427.
Proof. reflexivity. Qed.

Example test5: (Znth 1 (Znth 1 gen_Ax)) = Int64.repr 0x1906b59631b4f565.
Proof. reflexivity. Qed.


(* Definition block512_to_chunks (b : block512) : list Z := *)
(*   Z_to_chunks 64 8 (Vec512.unsigned b). *)
(**)
(* Definition block512_to_vals (b : block512) : list val := *)
(*   map (fun x => Vlong (Int64.repr x)) (block512_to_chunks b). *)
(**)

Definition data_mem (sh_r : share) (x : val) (x_content : block512) : mpred :=
  data_at sh_r tuint512 (block512_to_vals x_content) x.

Definition result_data_mem (sh_w : share) (i : Z) (data : val)
  (x_content y_content data_content : block512) : mpred :=
    (data_at sh_w tuint512 ((sublist 0 i (block512_to_vals (LPSX x_content y_content))) ++
        (sublist i 8 (block512_to_vals data_content))) data).

Definition Ax_data_mem (sh_r : share) (Ax_vals : list (list val)) (Ax : val) : mpred :=
   data_at sh_r (tarray (tarray tulong 256) 8) Ax_vals Ax.

(* Definition r_i_expr (i : Z) (j : Z) (x_content y_content : block512) : val := *)
(*   Vlong (Int64.repr (Z.shiftr (Znth j (block512_to_chunks (Vec512.xor x_content y_content))) (64 * i))). *)

Definition r_i_expr (i : Z) (j : Z) (x_content y_content : block512) : val :=
  Vlong (Int64.repr (Znth j (block512_to_chunks (Vec512.xor x_content y_content)))).

Definition gen_r_i_arr (x_content y_content : block512) :=
  map (fun _x => Vlong (Int64.repr _x)) (block512_to_chunks (Vec512.xor x_content y_content)).

Fixpoint Z_to_xor_list (k : nat) (x y : Z) : list val :=
  match k with
  | O => Vlong (Int64.xor (Int64.repr (LSB 64 x)) (Int64.repr (LSB 64 y))) :: nil
  | S k' => Vlong (Int64.xor (Int64.repr (LSB 64 x)) (Int64.repr (LSB 64 y))) ::
            (Z_to_xor_list k' (Z.shiftr x (Z.of_nat 64)) (Z.shiftr y (Z.of_nat 64)))
  end.

Lemma r_i_eq : forall (i j : Z) (r1 r2 : block512),
  Zlength (block512_to_chunks r1) = 8 -> Zlength (block512_to_chunks r2) = 8 ->
  r_i_expr i j r1 r2 = Znth j (Z_to_xor_list 8 (Vec512.unsigned r1) (Vec512.unsigned r2)).
Proof.
  intros i j r1 r2 H1 H2.
  (* intros i j r1 r2. *)
  unfold r_i_expr.
  unfold Z_to_xor_list.
  rewrite !Z.shiftr_shiftr.
  unfold block512_to_chunks.
  unfold Z_to_chunks.
  rewrite !xor_repr_comm.
  rewrite !xor_LSB_comm.
  Search (Z.lxor).
  rewrite <- !Z.shiftr_lxor.
  rewrite !Z.shiftr_shiftr.
  Search (Znth).
  Search map.
  (* induction j as [|j' Hj']. *)
  (* - simpl. *)
  (*   unfold block512_to_chunks in *. *)
  (*   unfold Z_to_chunks in *. *)
  (*   rewrite Znth_0_cons. *)
  (*   induction i as [|i' Hi']. *)
  (*   + rewrite Znth_0_cons. *)
  (*     rewrite Z.shiftr_0_r. *)
  (*     rewrite xor_repr_comm. *)
  (*     rewrite xor_LSB_comm. *)
  (*     rewrite xor_unsigned_comm. *)
  (*     reflexivity. *)
  (*   + rewrite Nat2Z.inj_succ.  *)
  (*     Search Zlength. *)
  (*     Search (Znth). *)
  (* unfold Z_to_xor_list. *)
  (* unfold block512_to_chunks, Z_to_chunks. *)
  (* rewrite Z.shiftr_0_r. *)

  (* split. *)
  (* +  *)
  (*   rewrite xor_repr_comm. *)
  (*   rewrite xor_LSB_comm. *)
  (*   rewrite xor_unsigned_comm. *)
  (*   unfold block512_to_chunks, Z_to_chunks. *)
  (*   rewrite Znth_0_cons. *)
  (*   reflexivity. *)
Admitted.

Definition streebog_xlps_spec :=
  DECLARE _streebog_xlps
  WITH   sh_r : share, sh_w : share,
         x : val, y : val, data : val,
         x_content : block512, y_content : block512, data_content : block512,
         Ax : val, gv : globals
  PRE [tptr tuint512, tptr tuint512, tptr tuint512]
    PROP(readable_share sh_r; writable_share sh_w)
    PARAMS (x; y; data)
    SEP (
        data_mem sh_r x x_content;
        data_mem sh_r y y_content;
        data_mem sh_w data data_content;
        Ax_data_mem sh_r Ax_vals (gv _Ax))
        (* Ax_data_mem sh_r gv _Ax) *)
        (* data_at sh_r tuint512 (block512_to_vals x_content) x; *)
        (* data_at sh_r tuint512 (block512_to_vals y_content) y; *)
        (* data_at sh_w tuint512 (block512_to_vals data_content) data; *)
     (* data_at sh_r (tarray (tarray tulong 256) 8) (map (map Vlong) gen_Ax) Ax) *)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (
        data_mem sh_r x x_content;
        data_mem sh_r y y_content;
        result_data_mem sh_w 8 data x_content y_content data_content;
        Ax_data_mem sh_r Ax_vals (gv _Ax)).
        (* Ax_data_mem sh_r gv _Ax). *)
        (* data_at sh_w tuint512 (block512_to_vals (LPSX x_content y_content)) data; *)
     (* data_at sh_r (tarray (tarray tulong 256) 8) (map (map Vlong) gen_Ax) Ax). *)


Lemma body_streebog_xlps :
  semax_body Vprog [] f_streebog_xlps streebog_xlps_spec.
Proof.
  start_function.
  (* assert (Zlength (block512_to_vals x_content) = 8) by reflexivity. *)
  (* assert (Zlength (block512_to_vals y_content) = 8) by reflexivity. *)
  (* assert (Zlength (block512_to_vals (Vec512.xor x_content y_content)) = 8) by reflexivity. *)
  (* assert (Zlength (map (map Vlong) gen_Ax) = 8) by reflexivity. *)
  (* assert (Zlength (Znth 0 (map (map Vlong) gen_Ax)) = 256) by reflexivity. *)
  (* assert (Zlength (Znth 1 (map (map Vlong) gen_Ax)) = 256) by reflexivity. *)
  (* assert (Zlength (Znth 2 (map (map Vlong) gen_Ax)) = 256) by reflexivity. *)
  (* assert (Zlength (Znth 3 (map (map Vlong) gen_Ax)) = 256) by reflexivity. *)
  (* assert (Zlength (Znth 4 (map (map Vlong) gen_Ax)) = 256) by reflexivity. *)
  (* assert (Zlength (Znth 5 (map (map Vlong) gen_Ax)) = 256) by reflexivity. *)
  (* assert (Zlength (Znth 6 (map (map Vlong) gen_Ax)) = 256) by reflexivity. *)
  (* assert (Zlength (Znth 7 (map (map Vlong) gen_Ax)) = 256) by reflexivity. *)
  (* assert (Zlength (Znth 0 (block512_to_vals (Vec512.xor x_content y_content))) = 8) by reflexivity. *)
 
  unfold data_mem, result_data_mem, Ax_data_mem.
  do 24 forward.

  (* Definition r_i_vals := (gen_r_i_arr x_content y_content). *)

  (* deadvars!. *)
  forward_loop
  (EX i:Z, 
          (* EX r0:val, EX r1:val, EX r2:val, EX r3:val, EX r4:val, EX r5:val, *)
          (*  EX r6:val, EX r7:val, *)
     PROP (0 <= i <= 8;
          sublist 0 i (block512_to_vals (LPSX x_content y_content)) =
          sublist 0 i (block512_to_vals data_content))
     LOCAL (temp _i (Vint (Int.repr i));
            temp _r0 (r_i_expr i 0 x_content y_content);
            temp _r1 (r_i_expr i 1 x_content y_content);
            temp _r2 (r_i_expr i 2 x_content y_content);
            temp _r3 (r_i_expr i 3 x_content y_content);
            temp _r4 (r_i_expr i 4 x_content y_content);
            temp _r5 (r_i_expr i 5 x_content y_content);
            temp _r6 (r_i_expr i 6 x_content y_content);
            temp _r7 (r_i_expr i 7 x_content y_content);
            temp _data data;
            gvars gv
     )
     SEP (data_mem sh_r x x_content;
          data_mem sh_r y y_content;
          result_data_mem sh_w i data x_content y_content data_content;
          Ax_data_mem sh_r Ax_vals (gv _Ax)
           (* data_at sh_r (tarray (tarray tulong 256) 8) (map (map Vlong) gen_Ax) (gv _Ax) *)
          (* data_at sh_r (tarray (tarray tulong 256) 8) (map (map Vlong) gen_Ax) (gv _Ax) *)
     )).

  - forward. 
    entailer!.
    Exists 0.
    entailer!.

    split. now rewrite r_i_eq.
    split. now rewrite r_i_eq.
    split. now rewrite r_i_eq.
    split. now rewrite r_i_eq.
    split. now rewrite r_i_eq.
    split. now rewrite r_i_eq.
    split. now rewrite r_i_eq.
    split. now rewrite r_i_eq.
    admit.

  - Intros i.
    Check _Ax.
    forward_if.
    -- unfold Ax_data_mem. forward.
       ++ entailer!. Search Z.land. unfold block512_to_chunks. unfold Z_to_chunks.
       rewrite Znth_0_cons. admit.
       ++ entailer!. admit.
       ++ unfold result_data_mem. unfold data_mem. forward.
          forward.
          +++ entailer!. admit.
          +++ 
          (* +++ unfold r_i_expr. unfold block512_to_chunks. unfold Z_to_chunks. *)
          (*     rewrite Znth_0_cons. *)
          (*     rewrite Znth_pos_cons. *)
          (*     rewrite Znth_0_cons. *)
          (*     rewrite 2!Znth_pos_cons. *)
          (*     rewrite Znth_0_cons. *)
              forward.

    (* + rewrite (r_i_eq 0 0 x_content y_content). intros Hr1. *)
    (* unfold r_i_expr. *)
    (* unfold block512_to_chunks, Z_to_chunks. *)
    (* rewrite Z.shiftr_0_r. *)
    (* split. *)
    (* +  *)
    (*   rewrite xor_repr_comm. *)
    (*   rewrite xor_LSB_comm. *)
    (*   rewrite xor_unsigned_comm. *)
    (*   unfold block512_to_chunks, Z_to_chunks. *)
    (*   rewrite Znth_0_cons. *)
    (*   reflexivity. *)
    (* +  *)
    (*   rewrite !xor_repr_comm. *)
    (*   rewrite !xor_LSB_comm. *)
    (*   rewrite <- !Z.shiftr_lxor. *)
    (*   rewrite !xor_unsigned_comm. *)
    (*   unfold block512_to_chunks, Z_to_chunks. *)
    (*   rewrite Znth_pos_cons. *)
    (*   split. *)
    (*   ++ rewrite Znth_0_cons. *)
    (*      reflexivity. *)
    (*   ++ rewrite 2!Znth_pos_cons. *)
    (*      split. *)
    (*      rewrite Znth_0_cons.  *)
    (*      +++ reflexivity. *)
    (*      +++ reflexivity. *)
    (*      +++ reflexivity. *)
    (*   ** reflexivity. *)
    (*   Search Znth. *)
    (*   Search Znth. *)
    (**)
    (*    *)
    (* Search (Znth ?y ?x = ?x. *)
    (* unfold block512_to_chunks. *)
    (* unfold Z_to_chunks. *)
    (* rewrite Znth_list_repeat_inrange. *)
    (* unfold result_data_mem. entailer!. rewrite (sublist_same 0 8). *)
    (* autorewrite with sublist. entailer!. *)
  (* - Intros i. *)
  (*   forward_if. *)
  (*   abbreviate_semax. *)
  (*   unfold data_mem, result_data_mem, Ax_data_mem. *)
  (*   forward. *)
Qed.
