From VST.floyd Require Import proofauto library.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Zbits.
Require Import Coq.Strings.Ascii.
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
Definition Vec := list bool.

Strategy 0 [Wordsize_512.wordsize].

Notation block512 := Vec512.int.

    (* выделение первых n битов*)
Definition LSB (n: nat) (b: Z) : Z :=
  Z_mod_two_p b n.

  (* разделение числа на k байтов *)
Fixpoint Z_to_bytes (k : nat) (z : Z) : list byte :=
  match k with
  | O => nil
  | S k' => Byte.repr (LSB 8 z) :: Z_to_bytes k' (Z.shiftr z 8)
  end.

Definition block512_to_bytes (b : block512) : list byte :=
  Z_to_bytes 64 (Vec512.unsigned b).

    (* поиск i-ого элемента списка *)
Definition nthi (il: list Z) (t: Z) :=
  nth (Z.to_nat t) il 0.

Definition nthi_b (il: list byte) (t: Z) :=
  nth (Z.to_nat t) il Byte.zero.

Definition pi' : list byte := map Byte.repr
    [
        252; 238; 221; 17; 207; 110; 49; 22; 251; 196; 250; 218; 35; 197; 4; 77;
        233; 119; 240; 219; 147; 46;153; 186; 23; 54; 241;187; 20; 205; 95; 193;
        249; 24; 101; 90; 226; 92; 239; 33; 129; 28; 60; 66; 139; 1; 142; 79;
        5; 132; 2; 174; 227; 106; 143; 160; 6; 11; 237; 152; 127; 212; 211; 31;
        235; 52; 44; 81; 234; 200; 72; 171; 242; 42; 104; 162; 253; 58; 206; 204;
        181; 112; 14; 86; 8; 12; 118; 18; 191; 114; 19; 71;156; 183; 93; 135;
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
  map (fun x => nthi_b pi' (Byte.unsigned x) ) il.

Fixpoint bytelist_to_Z (k : nat) (il: list byte): Z :=
  match k with
  | O => Z.zero
  | S k' => match il with
    | [] => Z.zero
    | x::xs =>(Byte.unsigned x) + (Z.shiftl (bytelist_to_Z k' xs ) 8)
    end
  end.

    (* склеивание списка байтов в вектор *)
Definition bytelist_to_Vec(k : nat) (il: list byte): block512 :=
  Vec512.repr (bytelist_to_Z k il).

    (* функция S *)
Definition s (v : block512) : block512 :=
    bytelist_to_Vec 64 (pi (block512_to_bytes v)).

  (* Инициализационный вектор для хэша 512 бит — все нули *)
Definition IV512 : block512 := Vec512.repr 0.

Definition p' : list Z :=
  [0; 8; 16; 24; 32; 40; 48; 56;
   1; 9; 17; 25; 33; 41; 49; 57;
   2; 10; 18; 26; 34; 42; 50; 58;
   3; 11; 19; 27; 35; 43; 51; 59;
   4; 12; 20; 28; 36; 44; 52; 60;
   5; 13; 21; 29; 37; 45; 53; 61;
   6; 14; 22; 30; 38; 46; 54; 62;
   7; 15; 23; 31; 39; 47; 55; 63].



Fixpoint permute_a0toa63 (perm : list Z) (l : list byte) : list byte :=
  match perm with
  | [] => []
  | i :: ps => (nth (Z.to_nat i) l default) :: (permute_a0toa63 ps l)
  end.

Definition p (perm : list Z) (l : list byte) : list byte := rev (permute_a0toa63 perm l).


Definition A' : list Z :=
  [ 0x8e20faa72ba0b470; 0x47107ddd9b505a38; 0xad08b0e0c3282d1c; 0xd8045870ef14980e;
    0x6c022c38f90a4c07; 0x3601161cf205268d; 0x1b8e0b0e798c13c8; 0x83478b07b2468764;
    0xa011d380818e8f40; 0x5086e740ce47c920; 0x2843fd2067adea10; 0x14aff010bdd87508;
    0x0ad97808d06cb404; 0x05e23c0468365a02; 0x8c711e02341b2d01; 0x46b60f011a83988e;
    0x90dab52a387ae76f; 0x486dd4151c3dfdb9; 0x24b86a840e90f0d2; 0x125c354207487869;
    0x092e94218d243cba; 0x8a174a9ec8121e5d; 0x4585254f64090fa0; 0xaccc9ca9328a8950;
    0x9d4df05d5f661451; 0xc0a878a0a1330aa6; 0x60543c50de970553; 0x302a1e286fc58ca7;
    0x18150f14b9ec46dd; 0x0c84890ad27623e0; 0x0642ca05693b9f70; 0x0321658cba93c138;
    0x86275df09ce8aaa8; 0x439da0784e745554; 0xafc0503c273aa42a; 0xd960281e9d1d5215;
    0xe230140fc0802984; 0x71180a8960409a42; 0xb60c05ca30204d21; 0x5b068c651810a89e;
    0x456c34887a3805b9; 0xac361a443d1c8cd2; 0x561b0d22900e4669; 0x2b838811480723ba;
    0x9bcf4486248d9f5d; 0xc3e9224312c8c1a0; 0xeffa11af0964ee50; 0xf97d86d98a327728;
    0xe4fa2054a80b329c; 0x727d102a548b194e; 0x39b008152acb8227; 0x9258048415eb419d;
    0x492c024284fbaec0; 0xaa16012142f35760; 0x550b8e9e21f7a530; 0xa48b474f9ef5dc18;
    0x70a6a56e2440598e; 0x3853dc371220a247; 0x1ca76e95091051ad; 0x0edd37c48a08a6d8;
    0x07e095624504536c; 0x8d70c431ac02a736; 0xc83862965601dd1b; 0x641c314b2b8ee083
    ].

Definition A : list int64 := map (fun x => Int64.repr x) A'.

Fixpoint Z_to_int64s (k : nat) (z : Z) : list int64 :=
  match k with
  | O => nil
  | S k' => (Int64.repr (LSB 64 z))::
              (Z_to_int64s k' (Z.shiftr z 64) )
  end.

Definition block512_to_int64s (b : block512) : list int64 :=
  Z_to_int64s 8 (Vec512.unsigned b).


Definition g(N h m: block512) : block512.

Admitted.
    
Definition stage_3 : block512.
Admitted.

(* 
Definition stage_2(M : Vec) :=
  if (length M <? 512)%nat then stage_3
  else take 512 rev M. *)