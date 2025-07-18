From VST.floyd Require Import proofauto library.
Require Import streebog_generic functional_spec.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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

Definition block512_to_chunks (b : block512) : list Z :=
  Z_to_chunks 64 8 (Vec512.unsigned b).

Definition block512_to_vals (b : block512) : list val :=
  map (fun x => Vlong (Int64.repr x)) (block512_to_chunks b).

Definition streebog_xor_spec :=
  DECLARE _streebog_xor (* название верифицируемой функции из сгенерированного файла .v*)
  WITH sh_r : share, sh_w : share, x : val, y : val, z : val,
       x_content : block512, y_content : block512, z_content : block512
       (* share = тип доступа к памяти: read/write *)
  PRE [tptr t_streebog_uint512_st, tptr t_streebog_uint512_st,
       tptr t_streebog_uint512_st]
       (* tptr - указатель на ... *)
    PROP(readable_share sh_r; writable_share sh_w)
    PARAMS (x; y; z) (* аргументы верифицируемой функции на C *)
    SEP (data_at sh_r t_streebog_uint512_st (block512_to_vals x_content) x;
         data_at sh_r t_streebog_uint512_st (block512_to_vals y_content) y;
         data_at_ sh_w t_streebog_uint512_st z)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (data_at sh_r t_streebog_uint512_st (block512_to_vals x_content) x;
         data_at sh_r t_streebog_uint512_st (block512_to_vals y_content) y;
         data_at sh_w t_streebog_uint512_st
            (block512_to_vals (Vec512.xor x_content y_content)) z).

Lemma signed_unsigned_bits : forall (x : block512) (n : Z),
  0 <= n < Vec512.zwordsize -> Z.testbit (Vec512.signed x) n = Z.testbit (Vec512.unsigned x) n.
Proof.
  intros x n.
  specialize (Vec512.same_bits_eqm (Vec512.signed x) (Vec512.unsigned x) n).
  intros H.
  lapply H.
  - intros T. exact T.
  - apply Vec512.eqm_signed_unsigned.
Qed.

Lemma Zlxor_mod_pow2 : forall x y n, 0 <= n ->
  (Z.lxor x y) mod 2 ^ n = Z.lxor (x mod 2 ^ n) (y mod 2 ^ n).
Proof.
  intros x y n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec. destruct (Z_lt_le_dec i n).
  - rewrite 3!Z.mod_pow2_bits_low by assumption.
    apply Z.lxor_spec.
  - now rewrite 3!Z.mod_pow2_bits_high.
Qed.

Lemma xor_unsigned_comm : forall x y,
  Z.lxor (Vec512.unsigned x) (Vec512.unsigned y) = Vec512.unsigned (Vec512.xor x y).
Proof.
  intros [x Hx] [y Hy]. simpl.
  rewrite Vec512.Z_mod_modulus_eq.
  unfold Vec512.modulus in *.
  rewrite two_power_nat_equiv in *.
  rewrite Zlxor_mod_pow2 by easy.
  now rewrite 2!Zmod_small by lia.
Qed.

Lemma testbit_ge_k : forall (w n : Z) (k : nat),
  n >= Z.of_nat k -> Z.testbit (w mod two_power_nat k) n = false.
Proof.
  intros w n k H0.
  specialize (Z.testbit_mod_pow2 w (Z.of_nat k) n); intros H1. 
  lapply H1.
  - clear H1; intros H2.
    rewrite two_power_nat_equiv.
    rewrite H2; clear H2. 
    rewrite Bool.andb_false_iff. 
    left.
    rewrite Zaux.Zlt_bool_false.
    + reflexivity.
    + apply Z.ge_le.
      exact H0.
  - lia. 
Qed.

Lemma xor_LSB_comm : forall (j : nat) (x y : Z),
  Z.lxor (LSB j x) (LSB j y) = LSB j (Z.lxor x y).
Proof.
  intros j x y.
  unfold LSB.
  rewrite 3!Zbits.Z_mod_two_p_eq. 
  rewrite <- Z.bits_inj_iff. 
  unfold Z.eqf.
  intros n.
  rewrite Z.lxor_spec.
  specialize (Z.lt_ge_cases n (Z.of_nat j)) as [Hnltj | Hngej].
  - rewrite two_power_nat_equiv.
    rewrite 3!Z.mod_pow2_bits_low.
    --- rewrite <- Z.lxor_spec. 
        reflexivity.
    --- exact Hnltj.
    --- exact Hnltj.
    --- exact Hnltj.
  - rewrite 3!testbit_ge_k. 
    -- reflexivity.
    -- apply Z.le_ge. exact Hngej.
    -- apply Z.le_ge. exact Hngej.
    -- apply Z.le_ge. exact Hngej. 
Qed.

Lemma xor_repr_comm : forall x y,
  Int64.xor (Int64.repr x) (Int64.repr y) = Int64.repr (Z.lxor x y).
Proof.
  intros x y.
  specialize (Int64.same_bits_eq (Int64.xor (Int64.repr x) (Int64.repr y)) (Int64.repr (Z.lxor x y))) as H; lapply H; clear H.
  - intros T; exact T.
  - intros i R. rewrite Int64.bits_xor.
    -- rewrite 3!Int64.testbit_repr.
       --- rewrite <- Z.lxor_spec.
           reflexivity.
       --- exact R.
       --- exact R.
       --- exact R.
    -- exact R.
Qed.

Lemma Z_to_chunks_xor : forall n m x y,
  map (uncurry Z.lxor) (combine (Z_to_chunks m n x) (Z_to_chunks m n y)) =
  Z_to_chunks m n (Z.lxor x y).
Proof.
   induction n; intros m x y; simpl.
  - reflexivity.
  - now rewrite <- xor_LSB_comm, Z.shiftr_lxor, IHn.
Qed.

Lemma body_streebog_xor :
  semax_body Vprog [] f_streebog_xor streebog_xor_spec.
Proof.
  start_function.
  unfold block512_to_vals.
  assert (Zlength (block512_to_chunks x_content) = 8) by reflexivity.
  assert (Zlength (block512_to_chunks y_content) = 8) by reflexivity.
  do 24 forward.
  unfold block512_to_vals, block512_to_chunks.
  rewrite !xor_repr_comm, <- xor_unsigned_comm, <- Z_to_chunks_xor.
  entailer!.
Qed.
