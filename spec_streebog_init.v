From VST.floyd Require Import proofauto library.
Require Import streebog_generic.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.



(* void *shash_desc_ctx(struct shash_desc *desc)
{
	return desc->__ctx;
} *)


Definition t_shash_desc := Tstruct _shash_desc noattr.
Definition t_streebog_state := Tstruct _streebog_state noattr.
Definition t_crypto_shash := Tstruct _crypto_shash noattr.

Definition shash_desc_ctx_spec :=
  DECLARE _shash_desc_ctx
  WITH descp: val
  PRE [ tptr t_shash_desc ]
    PROP (isptr descp)
    PARAMS (descp)
    SEP ()
  POST [ tptr tvoid ]
    PROP ()
    RETURN (offset_val (sizeof t_shash_desc) descp)
    SEP ().

Lemma body_shash_desc_ctx :
  semax_body Vprog [] f_shash_desc_ctx shash_desc_ctx_spec.
Proof.
  start_function.
  forward.
Qed.

Definition crypto_shash_digestsize_spec :=
  DECLARE _crypto_shash_digestsize
  WITH sh: share, tfm: val, desc: val
  PRE [tptr t_crypto_shash]
    PROP (isptr tfm)
    PARAMS (tfm)
    SEP (field_at sh t_shash_desc (DOT _tfm) tfm desc)
  POST [tuint]
    PROP ()
    RETURN (Vint (Int.repr 64))
    SEP (field_at sh t_shash_desc (DOT _tfm) tfm desc).


Definition streebog_init_spec := 
  DECLARE _streebog_init 
  WITH sh : share, desc : val, tfm : val
  PRE [tptr t_shash_desc]
  PROP(writable_share sh;
        isptr desc;
        isptr tfm)
  PARAMS (desc)
  SEP (field_at sh t_shash_desc (DOT _tfm) tfm desc;
        data_at_ sh t_streebog_state (offset_val (sizeof t_shash_desc) desc))

  POST [ tint ]
  PROP()
  RETURN (Vint Int.zero)
  SEP ( field_at sh t_shash_desc (DOT _tfm) tfm desc;
        data_at_ sh t_streebog_state (offset_val (sizeof t_shash_desc) desc);
        field_at sh t_streebog_state (DOT _h) (map Vlong (block512_to_int64s Vec512.zero)) (offset_val (sizeof t_shash_desc) desc) * 
        field_at sh t_streebog_state (DOT _N) (map Vlong (block512_to_int64s Vec512.zero)) (offset_val (sizeof t_shash_desc) desc) * 
        field_at sh t_streebog_state (DOT _Sigma) (map Vlong (block512_to_int64s Vec512.zero)) (offset_val (sizeof t_shash_desc) desc) * 
        field_at sh t_streebog_state (DOT _hash) (map Vlong (block512_to_int64s Vec512.zero)) (offset_val (sizeof t_shash_desc) desc)).

(* void *memset(void *s, int c, size_t n); *)


(* Definition memset_spec :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive (Vint c);
                   temp 3%positive (Vint (Int.repr n)))
       SEP (memory_block sh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at sh (tarray tuchar n) (repeat (Vint c) (Z.to_nat n)) p). *)

Definition memset_spec :=
  DECLARE _memset
   WITH sh : share, s: val, n: Z, c: Z
   PRE [ tptr tvoid, tint, tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned; isptr s)
       PARAMS (s; Vint (Int.repr c); Vint (Int.repr n))
       SEP (memory_block sh n s)
    POST [ tptr tvoid ]
       PROP()
       RETURN(s)
       SEP(data_at sh (tarray tuchar n) (repeat (Vint (Int.repr c)) (Z.to_nat n)) s).

(* Lemma body_memset_spec :
  semax_body Vprog [] f_shash_desc_ctx shash_desc_ctx_spec.
Proof.
  start_function.
  forward.
Qed. *)



Definition Gprog : funspecs :=
  ltac:(with_library prog [shash_desc_ctx_spec; streebog_init_spec; memset_spec; crypto_shash_digestsize_spec]).


Lemma body_streebog_init :
  semax_body Vprog Gprog f_streebog_init streebog_init_spec.
Proof.
  start_function.
  Intros.
  forward_call(desc).
  forward.
  forward_call(sh, tfm, desc).
  hint.
  forward_call((offset_val (sizeof t_shash_desc) desc), 0, (sizeof t_streebog_state)).
  Check memset.
  (* forward_call (sh, offset_val (sizeof t_shash_desc) desc, sizeof t_streebog_state). *)


Qed.

