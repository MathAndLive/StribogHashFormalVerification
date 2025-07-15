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

Module Example1.
  Definition M1 : bits := hex_string_to_bits "323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130".

  Definition h := IV512.
  Definition N := Vec512.repr 0.

  Definition h_xor_N := Vec512.xor h N.

  Definition s_h_xor_N := s h_xor_N.
  Compute Vec512.unsigned s_h_xor_N ?= 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc .

  Definition p_s_h_xor_N := p s_h_xor_N.
  Compute Vec512.unsigned s_h_xor_N ?= 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc .

  Definition K := l p_s_h_xor_N.
  Compute Vec512.unsigned K ?= 0xb383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574b383fc2eced4a574 .

  Definition K1 := K.
  Definition m := 0x01323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130.

  Definition xor_k1_m := Vec512.xor K1 (Vec512.repr m).
  Compute Vec512.unsigned xor_k1_m ?= 0xb2b1cd1ef7ec924286b7cf1cffe49c4c84b5c91afde694448abbcb18fbe0964682b3c516f9e2904080b1cd1ef7ec924286b7cf1cffe49c4c84b5c91afde69444 .
  
  Definition s_xor_k1_m := s xor_k1_m.
  Compute Vec512.unsigned s_xor_k1_m ?= 0x4645d95fc0beec2c432f8914b62d4efd3e5e37f14b097aead67de417c220b0482492ac996667e0ebdf45d95fc0beec2c432f8914b62d4efd3e5e37f14b097aea.

  Definition p_s_xor_k1_m := p s_xor_k1_m.
  Compute Vec512.unsigned p_s_xor_k1_m ?= 0x46433ed624df433e452f5e7d92452f5ed98937e4acd989375f14f117995f14f1c0b64bc266c0b64bbe2d092067be2d09ec4e7ab0e0ec4e7a2cfdea48eb2cfdea.

  Definition l_p_s_xor_k1_m := l p_s_xor_k1_m.
  Compute Vec512.unsigned l_p_s_xor_k1_m ?= 0xe60059d4d8e0758024c73f6f3183653f56579189602ae4c21e7953ebc0e212a0ce78a8df475c2fd4fc43fc4b71c01e35be465fb20dad2cf690cdf65028121bb9.
  
  Definition C1 := Vec512.repr (hd 0 C).

  Definition xor_K1_C1 := Vec512.xor K1 C1.
  Compute Vec512.unsigned xor_K1_C1 ?= 0x028ba7f4d01e7f9d5848d3af0eb1d96b9ce98a6de0917562c2cd44a3bb516188f8ff1cbf5cb3cc7511c1d6266ab47661b6f5881802a0e8576e0399773c72e073.

  Definition s_xor_K1_C1 := s xor_K1_C1.
  Compute s_xor_K1_C1.
  Compute Vec512.unsigned s_xor_K1_C1.
  Compute Vec512.unsigned s_xor_K1_C1 ?= 0xddf644e6e15f5733bff249410445536f4e9bd69e200f3596b3d9ea737d70a1d7d1b6143b9c9288357758f8ef78278aa155f4d717dda7cb12b211e87e7f19203d.
End Example1.