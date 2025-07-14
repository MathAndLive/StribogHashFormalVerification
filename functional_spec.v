From VST.floyd Require Import proofauto library.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Zbits.
Require Import Coq.Strings.Ascii.
Require Import Coq.Program.Wf.
Require Import compcert.lib.Coqlib.
Require Import List.
Import ListNotations.

Module Wordsize_512.
 Definition wordsize := 512%nat.
 Remark wordsize_not_zero: wordsize <> 0%nat.
 Proof. unfold wordsize; congruence. Qed.
End Wordsize_512.

Strategy opaque [Wordsize_512.wordsize].

Module Vec512 := Make(Wordsize_512).
Definition bits := list bool.

Strategy 0 [Wordsize_512.wordsize].

Notation block512 := Vec512.int.

(* n младших битов числа b*)
Definition LSB (n: nat) (b: Z) : Z :=
  Z_mod_two_p b n.

(* разделение числа на k векторов длины m *)
Fixpoint Z_to_chunks (m : nat) (k : nat) (z : Z) : list Z :=
  match k with
  | O => nil
  | S k' => (LSB m z) :: Z_to_chunks m k' (Z.shiftr z (Z.of_nat m))
  end.

(* разделение числа на k байтов *)
Definition Z_to_bytes (k : nat) (z : Z) : list byte :=
  map Byte.repr (Z_to_chunks 8 k z).

Definition block512_to_bytes (b : block512) : list byte :=
  Z_to_bytes 64 (Vec512.unsigned b).

(* поиск i-ого элемента списка *)
Definition nthi_Z (il: list Z) (t: Z) : Z :=
  nth (Z.to_nat t) il default.

Definition nthi_bytes (il: list byte) (t: Z) : byte :=
  nth (Z.to_nat t) il default.

Fixpoint bytes_to_Z (k : nat) (il: list byte): Z :=
  match k with
  | O => Z.zero
  | S k' => match il with
    | [] => Z.zero
    | x::xs =>(Byte.unsigned x) + (Z.shiftl (bytes_to_Z k' xs ) 8)
    end
  end.

(* склеивание списка байтов в вектор *)
Definition bytes_to_block512 (il: list byte): block512 :=
  Vec512.repr (bytes_to_Z 64 il).

Definition Z_to_int64s (k : nat) (z : Z) : list int64 :=
  map Int64.repr (Z_to_chunks 64 k z).


Definition block512_to_int64s (b : block512) : list int64 :=
  Z_to_int64s 8 (Vec512.unsigned b).

(* Конвертирует 8 бит в 1 байт *)
Definition bits_to_byte (bs: bits) : byte :=
  Byte.repr (
    match bs with
    | b0 :: b1:: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: [] =>
        (if b7 then 128 else 0) +
        (if b6 then 64 else 0) +
        (if b5 then 32 else 0) +
        (if b4 then 16 else 0) +
        (if b3 then 8 else 0) +
        (if b2 then 4 else 0) +
        (if b1 then 2 else 0) +
        (if b0 then 1 else 0)
    | _ => 0 (* TODO: сделать ошибку на длину вектора не равно 8 *)
    end
  ).

Fixpoint group_bits (bs: bits) : list bits :=
  match bs with
  | b0::b1::b2::b3::b4::b5::b6::b7::tail =>
      [b0; b1; b2; b3; b4; b5; b6; b7] :: group_bits tail
  | _ => []
  end.

Definition bits_to_bytes (bs: bits) : list byte :=
  map bits_to_byte (group_bits bs).

Definition bits_to_block512 (bs: bits) : block512 :=
  bytes_to_block512 (bits_to_bytes bs).


Definition pi' : list byte := map Byte.repr
    [
        252; 238; 221; 17; 207; 110; 49; 22; 251; 196; 250; 218; 35; 197; 4; 77;
        233; 119; 240; 219; 147; 46; 153; 186; 23; 54; 241;187; 20; 205; 95; 193;
        249; 24; 101; 90; 226; 92; 239; 33; 129; 28; 60; 66; 139; 1; 142; 79;
        5; 132; 2; 174; 227; 106; 143; 160; 6; 11; 237; 152; 127; 212; 211; 31;
        235; 52; 44; 81; 234; 200; 72; 171; 242; 42; 104; 162; 253; 58; 206; 204;
        181; 112; 14; 86; 8; 12; 118; 18; 191; 114; 19; 71; 156; 183; 93; 135;
        21; 61; 150; 41; 16; 123; 154; 199; 243; 145; 120; 111; 157; 158; 178; 177;
        50; 117; 25; 61; 255; 53; 138; 126; 109; 84; 198; 128; 195; 189; 13; 87;
        223; 245; 36; 169; 62; 168; 67; 201; 215; 121; 214; 246; 124; 34; 185; 3;
        224; 15; 236; 222; 122; 148; 176; 188; 220; 232; 40; 80; 78; 51; 10; 74;
        167; 151; 96; 115; 30; 0; 98; 68; 26; 184; 56; 130; 100; 159; 38; 65;
        173; 69; 70; 146; 39; 94; 85; 47; 140; 163; 165; 125; 105; 213; 149; 59;
        7; 88; 179; 64; 134; 172; 29; 247; 48; 55; 107; 228; 136; 217; 231; 137;
        225; 27; 131;73; 76; 63; 248; 254; 141;83; 170; 144; 202; 216; 133; 97;
        32; 113; 103; 164; 45; 43; 9; 91; 203; 155; 37; 208; 190; 229; 108; 82;
        89; 166; 116; 210; 230; 244; 180; 192; 209; 102; 175; 194; 57; 75; 99; 182
    ].

(* применение функции pi *)
Definition pi (il: list byte) :=
  map (fun x => nthi_bytes pi' (Byte.unsigned x) ) il.

(* функция S *)
Definition s (v : block512) : block512 :=
    bytes_to_block512 (pi (block512_to_bytes v)).


(* Инициализационный вектор для хэша 512 бит — все нули *)
Definition IV512 : block512 := Vec512.repr 0.


Definition permute (permutation_list : list Z) (l : block512) : block512 :=
  let bytes := block512_to_bytes l in
    bytes_to_block512 (map (fun i => nthi_bytes bytes i)  permutation_list).

Definition tau : list Z :=
  [0; 8; 16; 24; 32; 40; 48; 56;
   1; 9; 17; 25; 33; 41; 49; 57;
   2; 10; 18; 26; 34; 42; 50; 58;
   3; 11; 19; 27; 35; 43; 51; 59;
   4; 12; 20; 28; 36; 44; 52; 60;
   5; 13; 21; 29; 37; 45; 53; 61;
   6; 14; 22; 30; 38; 46; 54; 62;
   7; 15; 23; 31; 39; 47; 55; 63].

Definition p (l : block512) : block512 := permute (rev tau) l.

Definition g(N h m: block512) : block512.
Admitted.

Definition stage_1 (IV : block512) : block512 * block512 * block512 :=
  let h := IV in
  let N := Vec512.repr 0 in
  let Sigma := Vec512.repr 0 in
  (h, N, Sigma) .


Function stage_2 (h N Sigma : block512) (M : bits) {measure length M} : block512 * block512 * block512 * bits :=
  if lt_dec (length M) 512
  then (h, N, Sigma, M)
  else let m := bytes_to_block512 (bits_to_bytes (rev (firstn 512 (rev M)))) in
       let h := g N h m in
       let N := Vec512.repr (Vec512.unsigned N + 512) in
       let Sigma := Vec512.repr ((Vec512.unsigned Sigma) + (Vec512.unsigned m))in
       let M := firstn ((length M) - 512) M in
       stage_2 h N Sigma M.
Proof.
  intros. eapply Nat.le_lt_trans.
  - apply firstn_le_length.
  - lia.
Defined.


Definition stage_3 (h N Sigma : block512%Z) (M : bits) : block512 :=
  let m := bits_to_block512 ((repeat false (511 - (length M))) ++ (true :: M)) in
  let h := g N h m in
  let N := Vec512.repr (Vec512.unsigned N + (Z.of_nat (length M))) in
  let Sigma := Vec512.repr ((Vec512.unsigned Sigma) + (Z.of_nat (8 * (length (block512_to_bytes m))))) in
  let h := g (Vec512.repr 0) h N in
  let h := g (Vec512.repr 0) h Sigma in
  h.

Definition H512 (M : bits) : block512 :=
  let '(h, N, Sigma) := (stage_1 IV512) in
  let '(h', N', Sigma', M') := (stage_2 h N Sigma M) in
  stage_3 h' N' Sigma' M'.
  
Fixpoint int64s_to_Z (k : nat) (il: list int64): Z :=
  match k with
  | O => Z.zero
  | S k' => match il with
    | [] => Z.zero
    | x::xs =>(Int64.unsigned x) + (Z.shiftl (int64s_to_Z k' xs ) 64)
    end
  end.
  
Definition int64s_to_block512 (il: list int64): block512 :=
  Vec512.repr (int64s_to_Z 8 il).

Definition A : list int64 :=
  [ Int64.repr 0x8e20faa72ba0b470; Int64.repr 0x47107ddd9b505a38; Int64.repr 0xad08b0e0c3282d1c; Int64.repr 0xd8045870ef14980e; 
    Int64.repr 0x6c022c38f90a4c07; Int64.repr 0x3601161cf205268d; Int64.repr 0x1b8e0b0e798c13c8; Int64.repr 0x83478b07b2468764;
    Int64.repr 0xa011d380818e8f40; Int64.repr 0x5086e740ce47c920; Int64.repr 0x2843fd2067adea10; Int64.repr 0x14aff010bdd87508;
    Int64.repr 0x0ad97808d06cb404; Int64.repr 0x05e23c0468365a02; Int64.repr 0x8c711e02341b2d01; Int64.repr 0x46b60f011a83988e;
    Int64.repr 0x90dab52a387ae76f; Int64.repr 0x486dd4151c3dfdb9; Int64.repr 0x24b86a840e90f0d2; Int64.repr 0x125c354207487869;
    Int64.repr 0x092e94218d243cba; Int64.repr 0x8a174a9ec8121e5d; Int64.repr 0x4585254f64090fa0; Int64.repr 0xaccc9ca9328a8950;
    Int64.repr 0x9d4df05d5f661451; Int64.repr 0xc0a878a0a1330aa6; Int64.repr 0x60543c50de970553; Int64.repr 0x302a1e286fc58ca7;
    Int64.repr 0x18150f14b9ec46dd; Int64.repr 0x0c84890ad27623e0; Int64.repr 0x0642ca05693b9f70; Int64.repr 0x0321658cba93c138;
    Int64.repr 0x86275df09ce8aaa8; Int64.repr 0x439da0784e745554; Int64.repr 0xafc0503c273aa42a; Int64.repr 0xd960281e9d1d5215;
    Int64.repr 0xe230140fc0802984; Int64.repr 0x71180a8960409a42; Int64.repr 0xb60c05ca30204d21; Int64.repr 0x5b068c651810a89e;
    Int64.repr 0x456c34887a3805b9; Int64.repr 0xac361a443d1c8cd2; Int64.repr 0x561b0d22900e4669; Int64.repr 0x2b838811480723ba;
    Int64.repr 0x9bcf4486248d9f5d; Int64.repr 0xc3e9224312c8c1a0; Int64.repr 0xeffa11af0964ee50; Int64.repr 0xf97d86d98a327728;
    Int64.repr 0xe4fa2054a80b329c; Int64.repr 0x727d102a548b194e; Int64.repr 0x39b008152acb8227; Int64.repr 0x9258048415eb419d;
    Int64.repr 0x492c024284fbaec0; Int64.repr 0xaa16012142f35760; Int64.repr 0x550b8e9e21f7a530; Int64.repr 0xa48b474f9ef5dc18;
    Int64.repr 0x70a6a56e2440598e; Int64.repr 0x3853dc371220a247; Int64.repr 0x1ca76e95091051ad; Int64.repr 0x0edd37c48a08a6d8;
    Int64.repr 0x07e095624504536c; Int64.repr 0x8d70c431ac02a736; Int64.repr 0xc83862965601dd1b; Int64.repr 0x641c314b2b8ee083
    ].

(* если b в виде битов (big-endian) это b_63 ... b_0, а A это [a_0 ; ... ; a_63] то эта функция выдаёт b_63 * a_0 XOR ... XOR b_0 * a_63 *)
Definition b_times_A (b : int64) : int64 :=
  let b_Z := Int64.unsigned b in fst (fold_right (fun x y => ((Int64.xor (fst y) (if (Z.testbit b_Z (snd y)) then x else (Int64.repr 0))), (snd y) + 1)) (Int64.repr 0, 0) A).

(* функция линейного преобразования *)
Definition l (b : block512) : block512 :=
  int64s_to_block512 (map (fun x => b_times_A x) (block512_to_int64s b)).