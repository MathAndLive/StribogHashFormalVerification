From VST.floyd Require Import proofauto library.
Require Import streebog_generic.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Require Import functional_spec.

Import ListNotations.

(*
void streebog_add512(const struct streebog_uint512 *x,
			    const struct streebog_uint512 *y,
			    struct streebog_uint512 *r)
{
	u64 carry = 0;
	int i;

	for (i = 0; i < 8; i++) {
		const u64 left = le64_to_cpu(x->qword[i]);
		u64 sum;

		sum = left + le64_to_cpu(y->qword[i]) + carry;
		if (sum != left)
			carry = (sum < left);
		r->qword[i] = cpu_to_le64(sum);
	}
}
*)

Definition t_streebog_uint512_st := Tstruct _streebog_uint512 noattr.
Definition streebog_uint512_arr_length := 8.

Definition streebog_add512_spec :=
  DECLARE _streebog_add512 (* название верифицируемой функции из сгенерированного файла .v*)
  WITH sh_r : share, sh_w : share, x : val, y : val, r : val,
            x_content : block512, y_content : block512,
            r_content : block512
            (* share = тип доступа к памяти: read/write *)
  PRE [tptr t_streebog_uint512_st, tptr t_streebog_uint512_st,
       tptr t_streebog_uint512_st]
       (* tptr - указатель на ... *)
    PROP(readable_share sh_r; writable_share sh_w)
    PARAMS (x; y; r) (* аргументы верифицируемой функции на C *)
    SEP (field_at sh_r t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s x_content)) x;
         field_at sh_r t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s y_content)) y;
         field_at sh_w t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s r_content)) r)
  POST [tvoid]
    PROP()
    RETURN()
    SEP (field_at sh_r t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s x_content)) x;
         field_at sh_r t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s y_content)) y;
         field_at sh_w t_streebog_uint512_st (DOT _qword)
            (map Vlong (block512_to_int64s (Vec512.add x_content y_content))) r).

Lemma body_add_512 :
  semax_body Vprog [] f_streebog_add512 streebog_add512_spec.
Proof.
  start_function.
  assert (Zlength (block512_to_int64s x_content) = 8) by reflexivity.
  assert (Zlength (block512_to_int64s y_content) = 8) by reflexivity.
  assert (Zlength (block512_to_int64s r_content) = 8) by reflexivity.
  forward.  
  forward_for_simple_bound 8 (EX i:Z, 
  PROP ((* empty *)) 
  LOCAL (temp _carry (Vlong (Int64.repr (Int.signed (Int.repr 0)))); (* carry должен быть равен функции доп. бита над list int64 подсписком *) 
   temp _x x; temp _y y;
   temp _r r) (* r должен быть равен функции суммы подсписков *)
  SEP (field_at sh_r t_streebog_uint512_st (DOT _qword)
          (map Vlong (block512_to_int64s x_content)) x;
   field_at sh_r t_streebog_uint512_st (DOT _qword)
     (map Vlong (block512_to_int64s y_content)) y;
   field_at sh_w t_streebog_uint512_st (DOT _qword)
     (map Vlong (block512_to_int64s r_content)) r))%assert.
  
Admitted.