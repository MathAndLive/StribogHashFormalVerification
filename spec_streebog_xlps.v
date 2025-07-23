From VST.floyd Require Import proofauto library.
Require Import streebog_generic.
Require Import compcert.lib.Zbits.

(* Definition Spec_streebog_xlps_VarSpecs : varspecs := (_Ax, (tarray (tarray tulong 256) 8))::nil. *)
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.
Require Import spec_streebog_xor.


Import ListNotations.

(* Check (@nil (list val)).  *)

Definition tuint512 := Tstruct _streebog_uint512 noattr.

Definition block512_to_chunks (b : block512) : list Z :=
  Z_to_chunks 64 8 (Vec512.unsigned b).

Definition block512_to_vals (b : block512) : list val :=
  map (fun x => Vlong (Int64.repr x)) (block512_to_chunks b).

Definition Ax_to_vals (a : list (list int64)) : list (list val) :=
  map (fun i => map (fun j => Vlong j) i) a.


Definition r_i_expr (j : Z) (x_content y_content : block512) : val :=
  Vlong (Int64.repr (Znth j (block512_to_chunks (Vec512.xor x_content y_content)))).

(* Compute (Vec512.xor (Vec512.repr (2^128 -1)) (Vec512.repr 0)).

Compute (block512_to_chunks (Vec512.xor (Vec512.repr (2^128 -1)) (Vec512.repr 0))).

Compute (Znth 1 (block512_to_chunks (Vec512.xor (Vec512.repr (2^128 -1)) (Vec512.repr 0)))).

Compute Vlong ((Int64.repr (Znth 3 (block512_to_chunks (Vec512.xor (Vec512.repr (2^128 -1)) (Vec512.repr 0)))))).


Compute (r_i_expr 0 (Vec512.repr 511) (Vec512.repr 0)). *)

Definition gen_Ax : list (list int64) :=
  map (fun i =>
         map (fun j =>
                tableLPS_i_j (Z.of_nat i) (Z.of_nat j))
             (seq 0 256))
      (seq 0 8).

Definition Ax_vals := Ax_to_vals gen_Ax.

Compute (Znth 2 Ax_vals).


Definition streebog_xlps_spec :=
  DECLARE _streebog_xlps
  WITH sh_r : share, sh_w : share,
       x : val, y : val, data : val,
       x_content : block512, y_content : block512, data_content : block512,
       gv : globals
  PRE [tptr tuint512, tptr tuint512, tptr tuint512]
    PROP(readable_share sh_r; writable_share sh_w)
    PARAMS (x; y; data)
    (* LOCAL (gvars gv) *)
    SEP (data_at sh_r tuint512 (block512_to_vals x_content) x;
         data_at sh_r tuint512 (block512_to_vals y_content) y;
         data_at sh_w tuint512 (block512_to_vals data_content) data;
         data_at sh_r (tarray (tarray tulong 256) 8) Ax_vals (gv _Ax))
  POST [tvoid]
    PROP()
    (* LOCAL (gvars gv) *)
    RETURN()
    SEP (data_at sh_r tuint512 (block512_to_vals x_content) x;
         data_at sh_r tuint512 (block512_to_vals y_content) y;
         data_at sh_w tuint512 (block512_to_vals (LPSX x_content y_content)) data;
         data_at sh_r (tarray (tarray tulong 256) 8) Ax_vals (gv _Ax)).


Definition inv_data_mem (sh :share) (x : val) (x_content : block512) : mpred :=
  data_at sh tuint512 (block512_to_vals x_content) x.

Definition inv_data_mem_res (sh :share) (i : Z) (z : val) (x_content y_content data_content : block512) : mpred :=
  (
   data_at sh tuint512 (
      (sublist 0 i (block512_to_vals (LPSX x_content y_content)) ++
                            (sublist i 8 (block512_to_vals data_content)))) z).



Fixpoint Z_to_xor_list (k : nat) (x y : Z) : list val :=
  match k with
  | O => Vlong (Int64.xor (Int64.repr (LSB 64 x)) (Int64.repr (LSB 64 y))) :: nil
  | S k' => Vlong (Int64.xor (Int64.repr (LSB 64 x)) (Int64.repr (LSB 64 y))) ::
            (Z_to_xor_list k' (Z.shiftr x (Z.of_nat 64)) (Z.shiftr y (Z.of_nat 64)))
  end.

Lemma r_i_eq : forall (j : Z) (r1 r2 : block512),
  Zlength (block512_to_chunks r1) = 8 -> Zlength (block512_to_chunks r2) = 8 ->
  r_i_expr j r1 r2 = Znth j (Z_to_xor_list 8 (Vec512.unsigned r1) (Vec512.unsigned r2)).
Proof.
  (* intros i j r1 r2 H1 H2.
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
  Search map. *)
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

Definition inv_data_mem2 (sh :share) (x : val) : mpred :=
  data_at_ sh tuint512 x.



Lemma body_streebog_xlps :
  semax_body  Vprog [] f_streebog_xlps streebog_xlps_spec.
Proof.
  start_function.
    (* assert (Zlength (block512_to_chunks x_content) = 8) by reflexivity.
  assert (Zlength (block512_to_chunks y_content) = 8) by reflexivity. *)
  (* assert (Zlength (block512_to_int64s z_content) = 8) by reflexivity. *)

  do 24 forward.
  (* Opaque Ax_vals.

  remember (Znth 0 Ax_vals) as ax0.
  remember (Znth 0 (block512_to_chunks (LPSX x_content y_content))) as chunk0.
  pose (idx := Z.land chunk0 255).
  pose (v := Znth idx ax0). *)

  deadvars!.
  forward_loop
   (EX i:Z,(*EX j:Z, EX data: list int64,*) 
    PROP(0 <= i <= 7;
          sublist 0 i (block512_to_vals (LPSX x_content y_content)) =
          sublist 0 i (block512_to_vals data_content))
    LOCAL (temp _i (Vint (Int.repr i));
            temp _r0 (r_i_expr 0 x_content y_content);
            temp _r1 (r_i_expr 1 x_content y_content);
            temp _r2 (r_i_expr 2 x_content y_content);
            temp _r3 (r_i_expr 3 x_content y_content);
            temp _r4 (r_i_expr 4 x_content y_content);
            temp _r5 (r_i_expr 5 x_content y_content);
            temp _r6 (r_i_expr 6 x_content y_content);
            temp _r7 (r_i_expr 7 x_content y_content);
            gvars gv;
            temp _data data) 
    SEP (inv_data_mem sh_r x x_content; inv_data_mem sh_r y y_content; 
         (* inv_data_mem sh_w data data_content;  *)
          data_at_ sh_w tuint512 data;
         (* inv_data_mem_res sh_w i data x_content y_content data_content; *)
         data_at sh_r (tarray (tarray tulong 256) 8) Ax_vals (gv _Ax))
    ).
    - forward.
    entailer!. normalize.
    Exists 0. 
    entailer!.
    split. 
    + rewrite r_i_eq; reflexivity.
    + split.  
      ++ now rewrite r_i_eq.
      ++ split.
        +++ now rewrite r_i_eq.
        +++ split. 
          ++++ now rewrite r_i_eq.
          ++++ split.
            +++++ now rewrite r_i_eq.
            +++++ split.
              ++++++ now rewrite r_i_eq.
              ++++++ split.
                +++++++ now rewrite r_i_eq.
                +++++++ split.  now rewrite r_i_eq. admit.
    - Intros i. forward_if.
      -- abbreviate_semax. forward.
        * entailer!. admit.
        * entailer!. (*rewrite Znth_0_cons.*) admit. 
        * forward.  deadvars!. forward.
          ** entailer!. admit.
          ** unfold r_i_expr. Search (Z.land).
          Search (upd_Znth). (*forward.*) admit.
      -- lia.
         

    (* + rewrite r_i_eq; reflexivity.
    + split.
      ++ rewrite r_i_eq.
        +++  unfold Z_to_xor_list. rewrite Znth_pos_cons.
          ++++ rewrite Znth_0_cons. reflexivity.
          ++++ lia.
        +++ reflexivity.
        +++ reflexivity.
      ++ split.
        *** now rewrite r_i_eq.
        *** split.
            **** now rewrite r_i_eq.
            **** split.
      lia. reflexivity. reflexivity. rewrite Znth_pos_cons. rewrite Znth_pos_cons. rewrite Znth_0_cons.
      split. reflexivity. 

    + reflexivity.
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
  - hint. *)

Qed.
