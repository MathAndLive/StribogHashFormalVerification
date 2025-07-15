From VST.floyd Require Import proofauto library.
Require Import Lia.
Require Import functional_spec.
Require Import compcert.lib.Integers.
Require Import Arith.
Require Import Coq.Strings.Ascii.
Require Import List.
Import ListNotations.

Definition hex_char_to_bits (char : string) : bits :=
  match char with
  | String "0" EmptyString => rev [false; false; false; false]
  | String "1" EmptyString => rev [false; false; false; true]
  | String "2" EmptyString => rev [false; false; true; false]
  | String "3" EmptyString => rev [false; false; true; true]
  | String "4" EmptyString => rev [false; true; false; false]
  | String "5" EmptyString => rev [false; true; false; true]
  | String "6" EmptyString => rev [false; true; true; false]
  | String "7" EmptyString => rev [false; true; true; true]
  | String "8" EmptyString => rev [true; false; false; false]
  | String "9" EmptyString => rev [true; false; false; true]
  | String "a" EmptyString => rev [true; false; true; false]
  | String "b" EmptyString => rev [true; false; true; true]
  | String "c" EmptyString => rev [true; true; false; false]
  | String "d" EmptyString => rev [true; true; false; true]
  | String "e" EmptyString => rev [true; true; true; false]
  | String "f" EmptyString => rev [true; true; true; true]
  | _ => []
  end.

Definition hex_string_to_bits (s : string) : bits :=
  flat_map (fun c => hex_char_to_bits (String c "")) (list_ascii_of_string s).

Module TestExample1.
  Definition M1 : bits := hex_string_to_bits "323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130".
  Definition h := IV512.
  Definition N := Vec512.repr 0.
  Definition m := 0x01323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130.
  Definition h_xor_N := Vec512.xor h N.
  Definition s_h_xor_N := s h_xor_N.
  Definition p_s_h_xor_N := p s_h_xor_N.
  Definition K := l p_s_h_xor_N.


  Lemma test_s_h_xor_N : Vec512.unsigned s_h_xor_N = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc.
  Proof. reflexivity. Qed.
  
  Lemma test_p_s_h_xor_N : Vec512.unsigned p_s_h_xor_N = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc.
  Proof. reflexivity. Qed.
  
  Lemma test_K : Vec512.unsigned K = 0xb383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574.
  Proof. reflexivity. Qed.

  Module TestE.
    Definition LPSX (a b : block512) : block512 :=
      l (p (s (Vec512.xor a b))).

    Module TestIteration1.
      Definition K1 := K.
      Definition xor_K1_m := Vec512.xor K1 (Vec512.repr m).
      Definition s_xor_K1_m := s xor_K1_m.
      Definition p_s_xor_K1_m := p s_xor_K1_m.
      Definition l_p_s_xor_K1_m := l p_s_xor_K1_m.
      Definition C1 := Vec512.repr (hd 0 C).
      Definition xor_K1_C1 := Vec512.xor K1 C1.
      Definition s_xor_K1_C1 := s xor_K1_C1.
      Definition p_s_xor_K1_C1 := p s_xor_K1_C1.
      Definition l_p_s_xor_K1_C1 := l p_s_xor_K1_C1.

      Lemma test_xor_K1_m : Vec512.unsigned xor_K1_m = 0xb2b1cd1ef7ec924286b7cf1cffe49c4c84b5c91afde694448abbcb18fbe0964682b3c516f9e2904080b1cd1ef7ec924286b7cf1cffe49c4c84b5c91afde69444.
      Proof. reflexivity. Qed.

      Lemma test_s_xor_K1_m : Vec512.unsigned s_xor_K1_m = 0x4645d95fc0beec2c432f8914b62d4efd3e5e37f14b097aead67de417c220b0482492ac996667e0ebdf45d95fc0beec2c432f8914b62d4efd3e5e37f14b097aea.
      Proof. reflexivity. Qed.
      
      Lemma test_p_s_xor_K1_m : Vec512.unsigned p_s_xor_K1_m = 0x46433ed624df433e452f5e7d92452f5ed98937e4acd989375f14f117995f14f1c0b64bc266c0b64bbe2d092067be2d09ec4e7ab0e0ec4e7a2cfdea48eb2cfdea.
      Proof. reflexivity. Qed.
      
      Lemma test_l_p_s_xor_K1_m : Vec512.unsigned l_p_s_xor_K1_m = 0xe60059d4d8e0758024c73f6f3183653f56579189602ae4c21e7953ebc0e212a0ce78a8df475c2fd4fc43fc4b71c01e35be465fb20dad2cf690cdf65028121bb9.
      Proof. reflexivity. Qed.

      Lemma test_xor_K1_C1 : Vec512.unsigned xor_K1_C1 = 0x028ba7f4d01e7f9d5848d3af0eb1d96b9ce98a6de0917562c2cd44a3bb516188f8ff1cbf5cb3cc7511c1d6266ab47661b6f5881802a0e8576e0399773c72e073.
      Proof. reflexivity. Qed.
      
      Lemma test_s_xor_K1_C1 : Vec512.unsigned s_xor_K1_C1 = 0xddf644e6e15f5733bff249410445536f4e9bd69e200f3596b3d9ea737d70a1d7d1b6143b9c9288357758f8ef78278aa155f4d717dda7cb12b211e87e7f19203d.
      Proof. reflexivity. Qed.
      
      Lemma test_p_s_xor_K1_C1 : Vec512.unsigned p_s_xor_K1_C1 = 0xddbf4eb3d17755b2f6f29bd9b658f4114449d6ea14f8d7e8e6419e733bef177ee104207d9c78dd7f5f450f709227a719575335a1888acb20336f96d735a1123d.
      Proof. reflexivity. Qed.

      Lemma test_l_p_s_xor_K1_C1 : Vec512.unsigned l_p_s_xor_K1_C1 = 0xd0b00807642fd78f13f2c3ebc774e80de0e902d23aef2ee9a73d010807dae9c188be14f0b2da27973569cd2ba051301036f728bd1d7eec33f4d18af70c46cf1e.
      Proof. reflexivity. Qed.

      Lemma test_LSPX_eq_l_p_s_xor_K1_C1 : Vec512.unsigned l_p_s_xor_K1_C1 = Vec512.unsigned (LPSX K1 C1).
      Proof. reflexivity. Qed.
    End TestIteration1.
  End TestE.
  Compute g_N N h m.

End TestExample1.

(*example 2*)

Module Example2. (* пример 2 из ГОСТа*)
Definition M1 : bits := hex_string_to_bits "fbe2e5f0eee3c820fbeafaebef20fffbf0e1e0f0f520e0ed20e8ece0ebe5f0f2f120fff0eeec20f120faf2fee5e2202ce8f6f3ede220e8e6eee1e8TOf2d1202ce8TOf2e5e220e5d1".

Definition h := IV512.
Definition N := Vec512.repr 0.

Definition h_xor_N := Vec512.xor h N.

Definition s_h_xor_N := s h_xor_N.
Compute Vec512.unsigned s_h_xor_N ?= 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc .

Definition p_s_h_xor_N := p s_h_xor_N.
Compute Vec512.unsigned s_h_xor_N ?= 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc .

Definition l_p_s_h_xor_N := l p_s_h_xor_N.
Compute Vec512.unsigned l_p_s_h_xor_N ?= 0xb383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574 .

Definition k1 := l_p_s_h_xor_N.

Definition m :=0xfbeafaebef20fffbf0e1e0f0f520e0ed20e8ece0ebe5f0f2f120fff0eeec20f120faf2fee5e2202ce8f6f3ede220e8e6eee1e8f0f2d1202ce8f0f2e5e220e5d1.
Definition xor_k1_m := Vec512.xor k1 (Vec512.repr m).

Definition k2:= 0xd0b00807642fd78f13f2c3ebc774e80de0e902d23aef2ee9a73d010807dae9c188be14f0b2da27973569cd2ba051301036f728bd1d7eec33f4d18af70c46cf1e.
Compute Vec512.unsigned xor_k1_m ?= 0x486906c521f45a8f43621cde3bf44599936b10ce2531558642a303de2038858593790ed02b3685585b750fc32cf44d925d6214de3c0585585b730ecb2cf440a5.

Definition s_xor_k1_m := s xor_k1_m.
Compute Vec512.unsigned s_xor_k1_m ?=0xf29131ac18e613035196148598e6c8e8de6fe9e75c840c432c731185f906a8a8de5404e1428fa8bf47354d408be63aecb79693857f6ea8bf473d04e48be6eb00.

Definition p_s_xor_k1_m := p s_xor_k1_m.
Compute Vec512.unsigned p_s_xor_k1_m ?=0xf251de2cde47b74791966f735435963d3114e911044d9304ac85e785e14085e418985cf9428b7f8be6e684068fe66ee613c80ca8a83aa8eb03e843a8bfecbf00.

Definition l_p_s_xor_k1_m := l p_s_xor_k1_m.
Compute Vec512.unsigned l_p_s_xor_k1_m ?=0x909aa733e1f52321a2fe35bfb8f67e92fbc70ef544709d5739d8faaca4acf126e83e273745c25b7b8f4a83a7436f6353753cbbbe492262cd3a868eace0104af1.

Definition xor_k1_c1 := Vec512.xor k1 (Vec512.repr (hd 0 C)).
Compute Vec512.unsigned xor_k1_c1 ?= 0x028ba7f4d01e7f9d5848d3af0eb1d96b9ce98a6de0917562c2cd44a3bb516188f8ff1cbf5cb3cc7511c1d6266ab47661b6f5881802a0e8576e0399773c72e073.

Definition s_xor_k1_c1 := s xor_k1_c1.
Compute Vec512.unsigned s_xor_k1_c1 ?=0xddf644e6e15f5733bff249410445536f4e9bd69e200f3596b3d9ea737d70a1d7d1b6143b9c9288357758f8ef78278aa155f4d717dda7cb12b211e87e7f19203d.

Definition p_s_xor_k1_c1 := p s_xor_k1_c1.
Compute Vec512.unsigned p_s_xor_k1_c1 ?=0xddbf4eb3d17755b2f6f29bd9b658f4114449d6ea14f8d7e8e6419e733bef177ee104207d9c78dd7f5f450f709227a719575335a1888acb20336f96d735a1123d.

Definition l_p_s_xor_k1_c1 := l p_s_xor_k1_c1.
Compute Vec512.unsigned l_p_s_xor_k1_c1 ?=0xd0b00807642fd78f13f2c3ebc774e80de0e902d23aef2ee9a73d010807dae9c188be14f0b2da27973569cd2ba051301036f728bd1d7eec33f4d18af70c46cf1e.

  (*Compute generate_keys k1 13%nat.*)
  (*Definition k12 := 0x9d46bf66234a7ed06c3b2120d2a3f15e0fedd87189b75b3cd2f206906b5ee00dc9a1eab800fb8cc5760b251f4db5cdef427052fa345613fd076451901279ee4c.
  Compute k12.
  Definition k13 := 0x0f79104026b900d8d768b6e223484c9761e3c585b3a405a6d2d8565ada926c3f7782ef127cd6b98290bf612558b4b60aa3cbc28fd94f95460d76b621cb45be70.
  Compute k13.*)
End Example2.

Module Some_tests.
(* А.1 Пример 1 *)
Definition M1 : bits := hex_string_to_bits "323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130".

Compute bits_to_bytes(hex_string_to_bits "486f64c1917879417fef082b3381a4e211c324f074654c38823a7b76f830ad00fa1fbae42b1285c0352f227524bc9ab16254288dd6863dccd5b9f54a1ad0541b").
Compute block512_to_bytes( H512 M1).

Definition testbytes : bits := hex_string_to_bits "32". (* 00110010  *)
Compute testbytes.

Compute bytes_to_Z 1 (Z_to_bytes 1 50).

Compute bytes_to_block512(Z_to_bytes 1 50).

Compute (bytes_to_Z 1 (block512_to_bytes  (int64s_to_block512 (Z_to_int64s 1 (int64s_to_Z  1 (block512_to_int64s  (bytes_to_block512 (bits_to_bytes [false; false; true; true; false; false; true; false])))))))).

Compute bytes_to_Z 1 (bits_to_bytes[false; false; true; true; false; false; true; false]).

Compute (bytes_to_Z 1 (block512_to_bytes  (int64s_to_block512 (Z_to_int64s 1 (int64s_to_Z  1 (block512_to_int64s  (bytes_to_block512 (bits_to_bytes [false; true; false; false; true; true; false; false])))))))).

Compute Z_to_chunks 4 2 50.

End Some_tests.
