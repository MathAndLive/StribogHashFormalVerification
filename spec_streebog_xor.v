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

Lemma xor_unsigned_comm : forall x y,
  Z.lxor (Vec512.unsigned x) (Vec512.unsigned y) = Vec512.unsigned (Vec512.xor x y).
Proof.
  intros x y.
  rewrite <- Z.bits_inj_iff.
  unfold Z.eqf.
  intros n.
  rewrite Z.lxor_spec.
  specialize (Z.lt_ge_cases n 0) as [Hl0 | Hg0].
  - destruct n.
    -- discriminate.
    -- discriminate.
    -- reflexivity.
  - specialize (Z.lt_ge_cases n Vec512.zwordsize) as [Hl | Hg].
    -- specialize (Vec512.same_bits_eqm (Vec512.signed x) (Vec512.unsigned x) n) as L1.
        lapply L1.
        --- intros H1. clear L1.
          specialize (Vec512.same_bits_eqm (Vec512.signed y) (Vec512.unsigned y) n) as L2.
          lapply L2.
          ---- intros H2. clear L2.
             specialize (Vec512.same_bits_eqm (Vec512.signed (Vec512.xor x y)) (Vec512.unsigned (Vec512.xor x y)) n) as L3.
             lapply L3.
             ----- intros H3. clear L3.
                 lapply H1.
                 ------ intros N1. rewrite <- N1. clear N1. clear H1.
                      lapply H2.
                      ------- intros N2. rewrite <- N2. clear N2. clear H2.
                            lapply H3.
                            -------- intros N3. rewrite <- N3. clear N3. clear H3.
                                   specialize (Vec512.bits_signed x n) as G1.
                                   lapply G1.
                                   + intros J1. rewrite J1. clear J1. clear G1.
                                     destruct (zlt n Vec512.zwordsize) as [l1 | g1].
                                     ++ clear l1. specialize (Vec512.bits_signed y n) as G2. 
                                        lapply G2.
                                        +++ intros J2. rewrite J2. clear J2. clear G2.
                                            destruct (zlt n Vec512.zwordsize) as [l2 | g2].
                                            ++++ clear l2. specialize (Vec512.bits_signed (Vec512.xor x y) n) as G3.
                                                 lapply G3.
                                                 +++++ intros J3. rewrite J3. clear J3. clear G3.
                                                       destruct (zlt n Vec512.zwordsize) as [l3 | g3].
                                                       ++++++ clear l3. specialize (Vec512.bits_xor x y n) as W.
                                                              lapply W.
                                                              * intros T. symmetry. exact T.
                                                              * lia.
                                                       ++++++ rewrite Z.ge_le_iff in g3. rewrite <- Z.nlt_ge in g3. contradiction (g3 Hl).
                                                 +++++ exact Hg0.
                                            ++++ rewrite Z.ge_le_iff in g2. rewrite <- Z.nlt_ge in g2. contradiction (g2 Hl).
                                        +++ exact Hg0.
                                     ++ rewrite Z.ge_le_iff in g1. rewrite <- Z.nlt_ge in g1. contradiction (g1 Hl).
                                   + exact Hg0.
                            -------- lia.
                      ------- lia.
                 ------ lia.
             ----- apply Vec512.eqm_signed_unsigned.
          ---- apply Vec512.eqm_signed_unsigned.
        --- apply Vec512.eqm_signed_unsigned.
    -- clear Hg0. simpl.
       assert (U1 : x = Vec512.repr (Vec512.unsigned x)). { symmetry. apply Vec512.repr_unsigned. } rewrite U1. clear U1.
       assert (U2 : y = Vec512.repr (Vec512.unsigned y)). { symmetry. apply Vec512.repr_unsigned. } rewrite U2. clear U2.
       rewrite 2!Vec512.unsigned_repr_eq.
       rewrite Vec512.Z_mod_modulus_eq.
       rewrite Vec512.modulus_power.
       rewrite two_p_equiv.
       rewrite 3!Z.mod_pow2_bits_high.
       + reflexivity.
       + pose proof Vec512.wordsize_pos. lia.
       + pose proof Vec512.wordsize_pos. lia.
       + pose proof Vec512.wordsize_pos. lia.  
Qed.

Lemma testbit_ge_k : forall (w n : Z) (k : nat),
  n >= Z.of_nat k -> Z.testbit (w mod two_power_nat k) n = false.
Proof.
  intros w n k H0.
  specialize (Z.testbit_mod_pow2 w (Z.of_nat k) n); intros H1. 
  lapply H1.
  - clear H1; intros H2.  
    assert (P: two_power_nat k = 2 ^ (Z.of_nat k)) by apply two_power_nat_equiv; rewrite P; clear P.
    rewrite H2; clear H2. rewrite Bool.andb_false_iff. left. specialize (Zaux.Zlt_bool_false n (Z.of_nat k)); intros H3.
    lapply H3.
    + lia.
    + lia.
  - lia. 
Qed.

Lemma xor_LSB_comm : forall (m : nat) (x y : Z),
  Z.lxor (LSB m x) (LSB m y) = LSB m (Z.lxor x y).
Proof.
  intros m x y.
  unfold LSB.
  rewrite 3!Zbits.Z_mod_two_p_eq. 
  rewrite <- Z.bits_inj_iff. 
  unfold Z.eqf.
  intros n.
  rewrite Z.lxor_spec.
  specialize (Z.lt_ge_cases n (Z.of_nat m)).
  intros H. destruct H.
  - assert (P: two_power_nat m = 2 ^ (Z.of_nat m)) by apply two_power_nat_equiv; rewrite P; clear P.
    rewrite 3!Z.mod_pow2_bits_low.
    --- rewrite <- Z.lxor_spec. 
        reflexivity.
    --- assumption.
    --- assumption.
    --- assumption.
  - rewrite 3!testbit_ge_k. 
    reflexivity. 
    apply Z.le_ge; assumption.
    apply Z.le_ge; assumption.
    apply Z.le_ge; assumption.
Qed.

Lemma xor_repr_comm : forall x y,
  Int64.xor (Int64.repr x) (Int64.repr y) = Int64.repr (Z.lxor x y).
Proof.
  intros x y. 
  specialize (Int64.same_bits_eq (Int64.xor (Int64.repr x) (Int64.repr y)) (Int64.repr (Z.lxor x y))) as H; lapply H; clear H.
  - intros T; exact T.
  - intros i H1. specialize (Int64.bits_xor (Int64.repr x) (Int64.repr y) i) as H2; lapply H2; clear H2.
    -- intros H2; rewrite H2; clear H2. rewrite 3!Int64.testbit_repr.
       --- rewrite <- Z.lxor_spec.
           reflexivity.
       --- assumption.
       --- assumption.
       --- assumption.
    -- assumption.
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
