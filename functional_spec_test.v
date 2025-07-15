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
  | String "0" EmptyString => [false; false; false; false]
  | String "1" EmptyString => [false; false; false; true]
  | String "2" EmptyString => [false; false; true; false]
  | String "3" EmptyString => [false; false; true; true]
  | String "4" EmptyString => [false; true; false; false]
  | String "5" EmptyString => [false; true; false; true]
  | String "6" EmptyString => [false; true; true; false]
  | String "7" EmptyString => [false; true; true; true]
  | String "8" EmptyString => [true; false; false; false]
  | String "9" EmptyString => [true; false; false; true]
  | String "a" EmptyString => [true; false; true; false]
  | String "b" EmptyString => [true; false; true; true]
  | String "c" EmptyString => [true; true; false; false]
  | String "d" EmptyString => [true; true; false; true]
  | String "e" EmptyString => [true; true; true; false]
  | String "f" EmptyString => [true; true; true; true]
  | _ => []
  end.

Module TestMessage.
  Definition hex_string_to_bits (s : string) : bits :=
    let conv := flat_map (fun c => hex_char_to_bits (String c "")) (list_ascii_of_string s)
    in conv.

  Definition m_str: string := "323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130".

  Definition m_z : Z := 0x323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130.
  Definition m_512 : Z := 0x01323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130.

  Definition m_less : bits := hex_string_to_bits m_str.
  Definition m_less_add : bits := (repeat false (511 - (length m_less))) ++ [true] ++ m_less.

  Compute Vec512.unsigned (bits_to_block512_be m_less) ?= m_z.
  Compute Vec512.unsigned (bits_to_block512_be m_less_add) ?= m_512.
Module TestMessage.


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
    Definition K1 := K.
    Definition C1 := Vec512.repr (hd 0 C).

    Module TestIteration1.
      Definition xor_K1_m := Vec512.xor K1 (Vec512.repr m).
      Definition s_xor_K1_m := s xor_K1_m.
      Definition p_s_xor_K1_m := p s_xor_K1_m.
      Definition l_p_s_xor_K1_m := l p_s_xor_K1_m.
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
    End TestIteration1.

    Module TestLPSX.
      Lemma test_LSPX : Vec512.unsigned (LPSX K1 C1) = 0xd0b00807642fd78f13f2c3ebc774e80de0e902d23aef2ee9a73d010807dae9c188be14f0b2da27973569cd2ba051301036f728bd1d7eec33f4d18af70c46cf1e.
      Proof. reflexivity. Qed.
    End TestLPSX.
  End TestE.
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

<<<<<<< HEAD
(* Program Fixpoint nat_to_bits (x : nat) {measure x} : bits :=
  match x with
  | O => [false]
  | S O => [true]
  |  S (S _) => (Nat.eqb (x mod 2) 1) :: nat_to_bits (x / 2)
  end.
Next Obligation.
  intros.
  simpl.
Qed. *)

Module test_LPSX_K1.
  Definition N : block512 := IV512.
  Definition h : block512 := Vec512.repr 0.
  Definition m : Z := 0x01323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130.

  Definition z_to_block512 (z : Z) : block512 := bytes_to_block512 (Z_to_bytes 64 z).

  Definition k1_test : Z := 0xb383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574.
  Definition k1_result: block512 := LPSX h N.

  (* Example test_LPSX :
      k1_result = z_to_block512 k1_test.
  Proof.
      reflexivity.
  Qed. *)

  (* OR *)
  Compute (LPSX h N).
  Compute (z_to_block512 k1_test).
End test_LPSX_K1.

(* Module test_bits.
(* А.1 Пример 1 *)
  Definition m_less : bits := hex_string_to_bits "323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130".
  Definition m_512 : Z := 0x01323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130.
  Definition m_less_added := Vec512.unsigned (bits_to_block512 ((repeat false (511 - (length m_less))) ++ (true :: m_less)) ).
  Compute m_less_added ?= m_512.
End test_bits. *)


Module Helpers_0x.
  Definition hex_char (n : Z) : ascii :=
  ascii_of_nat (Z.to_nat (if n <? 10 then 48 + n else 87 + n)).

  Fixpoint Z2hex_aux (fuel : nat) (n : Z) : string :=
    match fuel with
    | O => "???" (* защита от зацикливания *)
    | S fuel' =>
      if n <? 16 then String (hex_char n) ""
      else Z2hex_aux fuel' (Z.div n 16) ++ String (hex_char (Z.rem n 16)) ""
    end.

  Definition Z2hex (n : Z) : string := Z2hex_aux 1000 n.
End Helpers_0x.


Module test_generate_keys.
Definition keys_result := map Vec512.repr [
    0xb383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574;
    0xd0b00807642fd78f13f2c3ebc774e80de0e902d23aef2ee9a73d010807dae9c188be14f0b2da27973569cd2ba051301036f728bd1d7eec33f4d18af70c46cf1e;
    0x9d4475c7899f2d0bb0e8b7dac6ef6e6b44ecf66716d3a0f16681105e2d13712a1a9387ecc257930e2d61014a1b5c9fc9e24e7d636eb1607e816dbaf927b8fca9;
    0x5c283daba5ec1f233b8c833c48e1c670dae2e40cc4c3219c73e58856bd96a72fdf9f8055ffe3c004c8cde3b8bf78f95f3370d0a3d6194ac5782487defd83ca0f;
    0x109f33262731f9bd569cbc9317baa551d4d2964fa18d42c41fab4e37225292ec2fd97d7493784779046388469ae195c436fa7cba93f8239ceb5ffc818826470c;
    0xb32c9b02667911Cf8f8a0877be9a170757e25026ccf41e67c6b5da70b1b874743e1135cfbefe244237555c676c153d99459bc382573aee2d85d30d99f286c5e7;
    0x8a13c1b195fd0886ac49989e7d84b08bc7b00e4f3f62765ece6050fcbabdc2346c8207594714e8e9c9c7aad694edc922d6b01e17285eb7e61502e634559e32f1;
    0x52cec3b11448bb8617d0ddfbc926f2e88730cb9179d6decea5acbffd323ec3764c47f7a9e13bb1db56c342034773023d617ff01cc546728e71dff8de5d128cac;
    0xf38c5b7947e7736d502007a05ea64a4eb9c243cb82154aa138b963bbb7f28e74d4d710445389671291d70103f48fd4d4c01fc415e3fb7dc61c6088afa1a1e735;
    0x0740b3faa03ed39b257dd6e3db7c1bf56b6e18e40cdaabd30617cecbaddd618ea5e61bb4654599581dd30c24c1ab877ad0687948286cfefaa7eef99f6068b315;
    0x185811cf3c2633aec8cfdfcae9dbb29347011bf92b95910a3ad71e5fca678e45e374f088f2e5c29496e9695ce8957837107bb3aa56441af11a82164893313116;
    0x9d46bf66234a7ed06c3b2120d2a3f15e0fedd87189b75b3cd2f206906b5ee00dc9a1eab800fb8cc5760b251f4db5cdef427052fa345613fd076451901279ee4c;
    0x0f79104026b900d8d768b6e223484c9761e3c585b3a405a6d2d8565ada926c3f7782ef127cd6b98290bf612558b4b60aa3cbc28fd94f95460d76b621cb45be70
  ].

  Definition N : block512 := IV512.
  Definition h : block512 := Vec512.repr 0.
  Definition K1 := LPSX h N.
  Definition keys := generate_keys K1 13.

  Definition c1: Z := 0xb1085bda1ecadae9ebcb2f81c0657c1f2f6a76432e45d016714eb88d7585c4fc4b7ce09192676901a2422a08a460d31505767436cc744d23dd806559f2a64507.
  Definition c2: Z := 0x6fa3b58aa99d2f1a4fe39d460f70b5d7f3feea720a232b9861d55e0f16b501319ab5176b12d699585cb561c2db0aa7ca55dda21bd7cbcd56e679047021b19bb7.
  Definition K2 := LPSX K1 (Vec512.repr c1).
  Definition K3 := LPSX K2 (Vec512.repr c2).

  Definition vec2int := map (fun x => x.(Vec512.intval)).

  Import Helpers_0x.

  (* Проверяем, что конвертация block512 <-> Z <-> 0x корректна *)
  (* Definition test1 := (Vec512.repr 0x0740b3faa03ed39b257dd6e3db7c1bf56b6e18e40cdaabd30617cecbaddd618ea5e61bb4654599581dd30c24c1ab877ad0687948286cfefaa7eef99f6068b315).
  Compute Vec512.intval test1.
  Compute Z2hex (Vec512.intval test1). *)
  
  Compute Z2hex (Vec512.intval K1). (* must be: b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574 *)
  Compute Z2hex (Vec512.intval K2). (* must be: d0b00807642fd78f13f2c3ebc774e80de0e902d23aef2ee9a73d010807dae9c188be14f0b2da27973569cd2ba051301036f728bd1d7eec33f4d18af70c46cf1e *)                                
  
  Compute vec2int keys.
  Compute vec2int keys_result. 

  Example test_gen_keys :
    keys_result = keys.
  Proof.
      reflexivity.
  Qed. 

End test_generate_keys.

Module test_E.
  Definition N : block512 := IV512.
  Definition h : block512 := IV512.
  Definition m : Z := 323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130.

  Definition test_result := 0xfc221dc8b814fc27a4de079d10097600209e5375776898961f70bded0647bd8f1664cfa8bb8d8ff1e0df3e621568b66aa075064b0e81cce132c8d1475809ebd2.  
  Definition K1 := LPSX h N.

  Definition keys := generate_keys K1 13.
  Definition e_result := E keys (Vec512.repr m).

   (* Example test_E :
    e_result = Vec512.repr test_result.
  Proof.
      reflexivity.
  Qed.  *)

  Compute Vec512.repr test_result.
  Compute e_result.

End test_E. 
=======
Compute bytes_to_Z 1 (Z_to_bytes 1 50).

Compute bytes_to_block512(Z_to_bytes 1 50).

Compute (bytes_to_Z 1 (block512_to_bytes  (int64s_to_block512 (Z_to_int64s 1 (int64s_to_Z  1 (block512_to_int64s  (bytes_to_block512 (bits_to_bytes [false; false; true; true; false; false; true; false])))))))).

Compute bytes_to_Z 1 (bits_to_bytes[false; false; true; true; false; false; true; false]).

Compute (bytes_to_Z 1 (block512_to_bytes  (int64s_to_block512 (Z_to_int64s 1 (int64s_to_Z  1 (block512_to_int64s  (bytes_to_block512 (bits_to_bytes [false; true; false; false; true; true; false; false])))))))).

Compute Z_to_chunks 4 2 50.

End Some_tests.
>>>>>>> e61f27b64c75f4b22d6c6bfb69e00d5281bacc4c
