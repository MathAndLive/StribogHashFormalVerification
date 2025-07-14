From VST.floyd Require Import proofauto library.
Require Import functional_spec.
Require Import compcert.lib.Integers.
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

Definition hex_string_to_bits (s : string) : bits :=
  flat_map (fun c => hex_char_to_bits (String c "")) (list_ascii_of_string s).

Compute hex_string_to_bits "fe".

(* Definition M1 : bits := (nat_to_bits (Z.to_nat 0x323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130)).
Definition test_H512_result : Z := 486f64c1917879417fef082b3381a4e2110324f074654c38823a7b76f830ad00fa1fbae42b1285c0352f227524bc9ab16254288dd6863dccd5b9f54a1ad0541b.
Compute  (Z.to_nat 0x0132313039383736353433323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313).


(* Compute (bits_to_block512 ((repeat false (511 - (length M1))) ++ (true :: M1)) = stage_3_first_line_result). *)

Example test_H512 :  M1 = (bits_to_block512 (nat_to_bits (Z.to_nat test_H512_result))).
Proof. reflexivity. Qed.0x *)