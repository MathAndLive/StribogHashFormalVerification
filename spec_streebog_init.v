From VST.floyd Require Import proofauto library.
Require Import streebog_init.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.

(*
static int streebog_init(struct shash_desc *desc)
{
	struct streebog_state *ctx = shash_desc_ctx(desc);
	unsigned int digest_size = crypto_shash_digestsize(desc->tfm);
	unsigned int i;

	memset(ctx, 0, sizeof(struct streebog_state));
	for (i = 0; i < 8; i++) {
		if (digest_size == STREEBOG256_DIGEST_SIZE)
			ctx->h.qword[i] = cpu_to_le64(0x0101010101010101ULL);
	}
	return 0;
}
*)

Definition t_shash_desc := Tstruct _shash_desc noattr.
Definition t_streebog_state := Tstruct _streebog_state noattr.

Definition streebog_init_spec := 
  DECLARE _streebog_init 
  WITH sh : share, desc : val, tfm : val, ctx : val, digest_size : Z, ctx_content : block512,
            hash_content : block512, h_content : block512,
            N_content : block512, Sigma_content : block512

  PRE [tptr t_shash_desc]
    PROP(writable_share sh; digest_size = 64;
         Zlength (block512_to_int64s hash_content) = 8;
         Zlength (block512_to_int64s h_content) = 8;
         Zlength (block512_to_int64s N_content) = 8;
         Zlength (block512_to_int64s Sigma_content) = 8)
    PARAMS (desc) 
    SEP ( field_at sh t_shash_desc (DOT ___ctx) (map Vlong (block512_to_int64s ctx_content)) desc * 
          field_at sh t_shash_desc (DOT _tfm) tfm desc;
          data_at sh (tarray (tptr tvoid) 0) (map Vlong (block512_to_int64s ctx_content)) ctx;
          field_at sh t_streebog_state (DOT _h)
             (map Vlong (block512_to_int64s h_content)) ctx * field_at sh t_streebog_state (DOT _N)
             (map Vlong (block512_to_int64s N_content)) ctx * field_at sh t_streebog_state (DOT _Sigma)
             (map Vlong (block512_to_int64s Sigma_content)) ctx * field_at sh t_streebog_state (DOT _hash)
             (map Vlong (block512_to_int64s hash_content)) ctx)
  POST [ tint ]
    PROP()
    RETURN (Vint Int.zero)
    SEP ( field_at sh t_shash_desc (DOT ___ctx) (map Vlong (block512_to_int64s ctx_content)) desc * 
          field_at sh t_shash_desc (DOT _tfm) tfm desc;
          data_at sh (tarray (tptr tvoid) 0) (map Vlong (block512_to_int64s ctx_content)) ctx;
          field_at sh t_streebog_state (DOT _h)
             (map Vlong (block512_to_int64s Vec512.zero)) ctx * field_at sh t_streebog_state (DOT _N)
             (map Vlong (block512_to_int64s Vec512.zero)) ctx * field_at sh t_streebog_state (DOT _Sigma)
             (map Vlong (block512_to_int64s Vec512.zero)) ctx * field_at sh t_streebog_state (DOT _hash)
             (map Vlong (block512_to_int64s Vec512.zero)) ctx).

