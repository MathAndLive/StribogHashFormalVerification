Require Import compcert.lib.Integers.
Require Import compcert.lib.Zbits.
Require Import compcert.lib.Coqlib.
Import ListNotations.

Module Wordsize_512.
 Definition wordsize := 512%nat.
 Remark wordsize_not_zero: wordsize <> 0%nat.
 Proof. unfold wordsize; congruence. Qed.
End Wordsize_512.


Strategy opaque [Wordsize_512.wordsize].

Module Vec512 := Make(Wordsize_512).

Notation block512 := Vec512.int.

Definition firstn_z (n: nat) (b: Z) : Z :=
  Z_mod_two_p b n.

Fixpoint Z_to_bytes (k : nat) (z : Z) : list byte :=
  match k with
  | O => nil
  | S k' => (Byte.repr (firstn_z 8 z))::
              (Z_to_bytes k' (Z.shiftr z 8) )
  end.

Definition block512_to_bytes (b : block512) : list byte :=
  Z_to_bytes 64 (Vec512.unsigned b).

(* Compute (block512_to_bytes (Vec512.repr 3000)). *)

Definition nthi (il: list Z) (t: Z) := nth (Z.to_nat t) il 0.

Definition pi' : list Z :=
    [
        252; 238; 221; 17; 207; 110; 49; 22; 251; 196; 250; 218; 35; 197; 4; 77;
        233; 119; 240; 219; 147; 46;153; 186; 23; 54; 241;187; 20; 205; 95; 193;
        249; 24; 101; 90; 226; 92; 239; 33; 129; 28; 60; 66; 139; 1; 142; 79;
        5; 132; 2; 174; 227; 106; 143; 160; 6; 11;237; 152; 127; 212; 211; 31;
        235; 52; 44; 81;234; 200; 72; 171; 242; 42; 104; 162; 253; 58; 206; 204;
        181; 112; 14; 86; 8; 12; 118; 18; 191; 114; 19; 71;156; 183; 93; 135;
        21; 61; 150; 41; 16; 123; 154; 199; 243; 145; 120; 111; 157; 158; 178; 177;
        50; 117; 25; 61; 255; 53; 138; 126; 109; 84; 198; 128; 195; 189; 13; 87;
        223; 245; 36; 169; 62; 168; 67; 201; 215; 121;214; 246; 124; 34; 185; 3;
        224; 15; 236; 222; 122; 148; 176; 188; 220; 232; 40; 80; 78; 51; 10; 74;
        167; 151; 96; 115; 30; 0; 98; 68; 26; 184; 56; 130; 100; 159; 38; 65;
        173; 69; 70; 146; 39; 94; 85; 47; 140; 163; 165; 125; 105; 213; 149; 59;
        7; 88; 179; 64; 134; 172; 29; 247; 48; 55; 107; 228; 136; 217; 231; 137;
        225; 27; 131;73; 76; 63; 248; 254; 141;83; 170; 144; 202; 216; 133; 97;
        32; 113; 103; 164; 45; 43; 9; 91; 203; 155; 37; 208; 190; 229; 108; 82;
        89; 166; 116; 210; 230; 244; 180; 192; 209; 102; 175; 194; 57; 75; 99; 182
    ].

Definition pi (il: list byte) :=
  map (fun x => nthi pi' (Byte.unsigned x) ) il.


Print Vec512.

