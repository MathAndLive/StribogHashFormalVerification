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

(* А.1 Пример 1 *)
Definition M1 : bits := hex_string_to_bits "323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130".

(* А.1.1 Для функции хэширования с длиной хэш-кода 512 бит  *)

Definition h := IV512.
Definition N := Vec512.repr 0.
(* После преобразования S: *)
Compute (s (Vec512.xor h N)).
Compute 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc.


Compute (H512 M1).

Definition test_H512_result : block512 := bits_to_block512 (hex_string_to_bits "486f64c1917879417fef082b3381a4e2110324f074654c38823a7b76f830ad00fa1fbae42b1285c0352f227524bc9ab16254288dd6863dccd5b9f54a1ad0541b.").
Compute test_H512_result.