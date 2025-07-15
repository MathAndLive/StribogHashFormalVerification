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

Definition hex_string_to_bits (s : string) : bits :=
  flat_map (fun c => hex_char_to_bits (String c "")) (list_ascii_of_string s).

Compute hex_string_to_bits "fe".

(* А.1 Пример 1 *)
Definition M1 : bits := hex_string_to_bits "323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130".

(* А.1.1 Для функции хэширования с длиной хэш-кода 512 бит  *)
Definition stage_3_first_line_result : block512 := bits_to_block512 (hex_string_to_bits "01323130393837363534333231303938373635343332313039383736353433323130393837363534333231303938373635343332313039383736353433323130").
Example test_stage_3_first_line_result : bits_to_block512 ((repeat false (511 - (length M1))) ++ (true :: M1)) = stage_3_first_line_result.
Proof. reflexivity. Qed.

Definition test_H512_result : block512 := bits_to_block512 (hex_string_to_bits "00557be5e584fd52a449b16b0251d05d27f94ab76cbaa6da890b59d8ef1e159d").
Example test_H512 : (H512 M1) = test_H512_result.
Proof. reflexivity. Qed.

(* Program Fixpoint nat_to_bits (x : nat) {measure x} : bits :=
  match x with
  | O => [false]
  | S O => [true]
  |  S (S _) => (Nat.eqb (x mod 2) 1) :: nat_to_bits (x / 2)
  end.
Next Obligation.
  simpl.
  destruct Nat.divmod.
  destruct fst.
  - lia.
  -
Qed. *)