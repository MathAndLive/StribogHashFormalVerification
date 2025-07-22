(* --- ШАПКА --- *)

From VST.floyd Require Import proofauto library.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Zbits.
Require Import Coq.Strings.Ascii.
Require Import Coq.Program.Wf.
Require Import compcert.lib.Coqlib.
Require Import List.
Import ListNotations.

(* --- БЛОК В 512 БИТ --- *)

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

(* --- СЛУЖЕБНЫЕ ФУНКЦИИ --- *)

(* n младших битов числа b*)
Definition LSB (n: nat) (b: Z) : Z :=
  Z_mod_two_p b n.

(* разбиение числа на k "векторов" длины m *)
Fixpoint Z_to_chunks (m : nat) (k : nat) (z : Z) : list Z :=
  match k with
  | O => nil
  | S k' => (LSB m z) :: Z_to_chunks m k' (Z.shiftr z (Z.of_nat m))
  end.

(* разбиение числа на k байтов *)
Definition Z_to_bytes (k : nat) (z : Z) : list byte :=
  map Byte.repr (Z_to_chunks 8 k z).

(* разбиение блока на байты *)
Definition block512_to_bytes (b : block512) : list byte :=
  Z_to_bytes 64 (Vec512.unsigned b).

(* t-й элемента списка целых *)
Definition nthi_Z (il: list Z) (t: Z) : Z :=
  nth (Z.to_nat t) il Inhabitant_Z.

(* t-й элемента списка байтов *)
Definition nthi_bytes (il: list byte) (t: Z) : byte :=
  nth (Z.to_nat t) il Inhabitant_byte.

(* склеивание байтов в число *)
Fixpoint bytes_to_Z (k : nat) (il: list byte): Z :=
  match k with
  | O => Z.zero
  | S k' => match il with
    | [] => Z.zero
    | x::xs => (Byte.unsigned x) + (Z.shiftl (bytes_to_Z k' xs ) 8)
    end
  end.

(* склейка списка байтов в блок *)
Definition bytes_to_block512 (il: list byte): block512 :=
  Vec512.repr (bytes_to_Z 64 il).

(* разбиение числа на UL *)
Definition Z_to_int64s (k : nat) (z : Z) : list int64 :=
  map Int64.repr (Z_to_chunks 64 k z).

(* склеивание UL в число *)
Definition block512_to_int64s (b : block512) : list int64 :=
  Z_to_int64s 8 (Vec512.unsigned b).

(* перевод 8 бит в 1 байт *)
(* пока что на всех машинах слово имеет длину 8 бит, но, возможно, в будущем это будет не так *)
Fixpoint bits_to_byte_rec (k : Z) (bs : bits) : byte :=
  match k with
  | 0 => Byte.repr 0
  | _ => match bs with
         | nil => Byte.repr 0
         | x :: xs => Byte.repr ((if x then 1 else 0) + 2 * Byte.unsigned (bits_to_byte_rec (k - 1) xs))
         end
  end.

(* склеивание битов в байт *)
Definition bits_to_byte (bs: bits) : byte := bits_to_byte_rec 8 bs.

(* группировка битов в списки по 8 *)
Fixpoint group_bits (bs: bits) : list bits :=
  match bs with
  | b0::b1::b2::b3::b4::b5::b6::b7::tail =>
      [b0; b1; b2; b3; b4; b5; b6; b7] :: group_bits tail
  | _ => [bs]
  end.

(* разбиение кучки битов на байты *)
Definition bits_to_bytes (bs: bits) : list byte :=
  map bits_to_byte (group_bits bs).

(* склейка битов в блок (little-endian) *)
Definition bits_to_block512_le (bs: bits) : block512 :=
  bytes_to_block512 (bits_to_bytes bs).

(* склейка битов в блок (big-endian) *)
Definition bits_to_block512_be (bs: bits) : block512 :=
  bits_to_block512_le (rev bs).

(* склейка LU в число *)
Fixpoint int64s_to_Z (k : nat) (il: list int64): Z :=
  match k with
  | O => Z.zero
  | S k' => match il with
    | [] => Z.zero
    | x::xs =>(Int64.unsigned x) + (Z.shiftl (int64s_to_Z k' xs ) 64)
    end
  end.
  
(* склейка LU в вектор *)
Definition int64s_to_block512 (il: list int64): block512 :=
  Vec512.repr (int64s_to_Z 8 il).

(* выбор из списка индексов тех, на позиции которых стоят единицы в битовом представлении числа j *)
Fixpoint bit_rec (j : Z) (indices : list Z) : list Z :=
  match indices with
  | nil => nil
  | x :: xs => if Z.testbit j x
               then x :: bit_rec j xs
               else bit_rec j xs
  end.

Definition bit (j : Z) : list Z := bit_rec j [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16;
        17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30;
        31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44;
        45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58;
        59; 60; 61; 62; 63].

(* t-й элемент списка из LU *)
Definition nthi_int64 (il: list int64) (t: Z) : int64 :=
  nth (Z.to_nat t) il Inhabitant_int64.
  
Definition lastn (n : nat) (ls : bits) : bits :=
  rev (firstn n (rev ls)).

(* --- ПОСТОЯННЫЕ ВЕЛИЧИНЫ --- *)

(* инициализационный вектор для хэша 512 бит - все нули *)
Definition IV512 : block512 := Vec512.repr 0.

Definition pi' : list byte := map Byte.repr
    [
        252; 238; 221; 17; 207; 110; 49; 22; 251; 196; 250; 218; 35; 197; 4; 77;
        233; 119; 240; 219; 147; 46; 153; 186; 23; 54; 241; 187; 20; 205; 95; 193;
        249; 24; 101; 90; 226; 92; 239; 33; 129; 28; 60; 66; 139; 1; 142; 79;
        5; 132; 2; 174; 227; 106; 143; 160; 6; 11; 237; 152; 127; 212; 211; 31;
        235; 52; 44; 81; 234; 200; 72; 171; 242; 42; 104; 162; 253; 58; 206; 204;
        181; 112; 14; 86; 8; 12; 118; 18; 191; 114; 19; 71; 156; 183; 93; 135;
        21; 161; 150; 41; 16; 123; 154; 199; 243; 145; 120; 111; 157; 158; 178; 177;
        50; 117; 25; 61; 255; 53; 138; 126; 109; 84; 198; 128; 195; 189; 13; 87;
        223; 245; 36; 169; 62; 168; 67; 201; 215; 121; 214; 246; 124; 34; 185; 3;
        224; 15; 236; 222; 122; 148; 176; 188; 220; 232; 40; 80; 78; 51; 10; 74;
        167; 151; 96; 115; 30; 0; 98; 68; 26; 184; 56; 130; 100; 159; 38; 65;
        173; 69; 70; 146; 39; 94; 85; 47; 140; 163; 165; 125; 105; 213; 149; 59;
        7; 88; 179; 64; 134; 172; 29; 247; 48; 55; 107; 228; 136; 217; 231; 137;
        225; 27; 131; 73; 76; 63; 248; 254; 141; 83; 170; 144; 202; 216; 133; 97;
        32; 113; 103; 164; 45; 43; 9; 91; 203; 155; 37; 208; 190; 229; 108; 82;
        89; 166; 116; 210; 230; 244; 180; 192; 209; 102; 175; 194; 57; 75; 99; 182
    ].

Definition tau : list Z :=
  [0; 8; 16; 24; 32; 40; 48; 56;
   1; 9; 17; 25; 33; 41; 49; 57;
   2; 10; 18; 26; 34; 42; 50; 58;
   3; 11; 19; 27; 35; 43; 51; 59;
   4; 12; 20; 28; 36; 44; 52; 60;
   5; 13; 21; 29; 37; 45; 53; 61;
   6; 14; 22; 30; 38; 46; 54; 62;
   7; 15; 23; 31; 39; 47; 55; 63].

Definition A : list int64 := map Int64.repr
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

Definition C : list Z :=
  [
    0xb1085bda1ecadae9ebcb2f81c0657c1f2f6a76432e45d016714eb88d7585c4fc4b7ce09192676901a2422a08a460d31505767436cc744d23dd806559f2a64507; 
    0x6fa3b58aa99d2f1a4fe39d460f70b5d7f3feea720a232b9861d55e0f16b501319ab5176b12d699585cb561c2db0aa7ca55dda21bd7cbcd56e679047021b19bb7; 
    0xf574dcac2bce2fc70a39fc286a3d843506f15e5f529c1f8bf2ea7514b1297b7bd3e20fe490359eb1c1c93a376062db09c2b6f443867adb31991e96f50aba0ab2; 
    0xef1fdfb3e81566d2f948e1a05d71e4dd488e857e335c3c7d9d721cad685e353fa9d72c82ed03d675d8b71333935203be3453eaa193e837f1220cbebc84e3d12e; 
    0x4bea6bacad4747999a3f410c6ca923637f151c1f1686104a359e35d7800fffbdbfcd1747253af5a3dfff00b723271a167a56a27ea9ea63f5601758fd7c6cfe57; 
    0xae4faeae1d3ad3d96fa4c33b7a3039c02d66c4f95142a46c187f9ab49af08ec6cffaa6b71c9ab7b40af21f66c2bec6b6bf71c57236904f35fa68407a46647d6e; 
    0xf4c70e16eeaac5ec51ac86febf240954399ec6c7e6bf87c9d3473e33197a93c90992abc52d822c3706476983284a05043517454ca23c4af38886564d3a14d493; 
    0x9b1f5b424d93c9a703e7aa020c6e41414eb7f8719c36de1e89b4443b4ddbc49af4892bcb929b069069d18d2bd1a5c42f36acc2355951a8d9a47f0dd4bf02e71e; 
    0x378f5a541631229b944c9ad8ec165fde3a7d3a1b258942243cd955b7e00d0984800a440bdbb2ceb17b2b8a9aa6079c540e38dc92cb1f2a607261445183235adb; 
    0xabbedea680056f52382ae548b2e4f3f38941e71cff8a78db1fffe18a1b3361039fe76702af69334b7a1e6c303b7652f43698fad1153bb6c374b4c7fb98459ced; 
    0x7bcd9ed0efc889fb3002c6cd635afe94d8fa6bbbebab076120018021148466798a1d71efea48b9caefbacd1d7d476e98dea2594ac06fd85d6bcaa4cd81f32d1b; 
    0x378ee767f11631bad21380b00449b17acda43c32bcdf1d77f82012d430219f9b5d80ef9d1891cc86e71da4aa88e12852faf417d5d9b21b9948bc924af11bd720
  ].

(* --- ПРЕОБРАЗОВАНИЕ S --- *)

(* действие pi' над одним байтом *)
Definition pi_byte (x : byte) : byte :=
  nthi_bytes pi' (Byte.unsigned x).

(* действие функции pi над списком байт *)
Definition pi (il: list byte) :=
  map (fun x => pi_byte x) il.

Definition s (v : block512) : block512 :=
    bytes_to_block512 (pi (block512_to_bytes v)).

(* --- ПРЕОБРАЗОВАНИЕ P --- *)

Definition tau_bytes (bytes : list byte) : list byte :=
  (map (fun i => nthi_bytes bytes i) tau).

Definition p (l : block512) : block512 :=
    bytes_to_block512 (tau_bytes (block512_to_bytes l)).

(* --- ПРЕОБРАЗОВАНИЕ L --- *)

(* если b в виде битов (big-endian) это b_63 ... b_0, а A это [a_0 ; ... ; a_63] то эта функция выдаёт b_63 * a_0 XOR ... XOR b_0 * a_63 *)
Definition b_times_A (b : int64) : int64 :=
  fold_right Int64.xor (Int64.repr 0) (map (fun x => nthi_int64 (rev A) x) (bit (Int64.unsigned b))). 

Definition l (b : block512) : block512 :=
  int64s_to_block512 (map (fun x => b_times_A x) (block512_to_int64s b)).

(* --- LPSX, КЛЮЧИ И НЕПОСРЕДСТВЕННО ХЕШ-ФУНКЦИЯ --- *)

Definition LPSX (block1 block2 : block512): block512 := l (p (s (Vec512.xor block1 block2))).

(* оптимизированная версия для генерации ключей, которая запоминает предыдущие вычисленные значения *)
Fixpoint generate_keys_tailrec (acc : list block512) (n : nat) : list block512 :=
  match n with
  | O => acc
  | S i =>
      match acc with
      | [] => acc  (* generate_keys_tailrec acc i  *)
      | k_prev :: _ =>
          let index := (List.length acc)%nat in
          let Ci_1 := Vec512.repr (nthi_Z C (Z.of_nat index - 1)) in (* index - 1, т.к. нумерация массива C с 0 *)
          let k_new := LPSX k_prev Ci_1 in  
          generate_keys_tailrec (k_new :: acc) i
      end
  end.

Definition generate_keys (K1 : block512) (n : nat) : list block512 :=
  List.rev (generate_keys_tailrec [K1] (n - 1)).

Definition E (keys: list block512) (m: block512) : block512 :=
  if Nat.eqb (List.length keys) 13 then
    let first_keys := firstn 12 keys in
    let k13 := last keys IV512 in
    Vec512.xor k13 (fold_left LPSX first_keys m)  
  else
    m.

Definition g_N (N h m : block512) : block512 :=
  let K1 := LPSX h N in
  let keys := generate_keys K1 13 in
  let e := E keys m in
  Vec512.xor (Vec512.xor e h) m.

Definition stage_1 (IV : block512) : block512 * block512 * block512 :=
  let h := IV in
  let N := Vec512.repr 0 in
  let Sigma := Vec512.repr 0 in
  (h, N, Sigma).

Function stage_2 (h N Sigma : block512) (M : bits) {measure length M} : block512 * block512 * block512 * bits :=
  if lt_dec (length M) 512
  then (h, N, Sigma, M)
  else let m' := bits_to_block512_be (lastn 512 M) in
       let h' := g_N N h m' in
       let N' := Vec512.add N (Vec512.repr 512) in
       let Sigma' := Vec512.add Sigma m' in
       let M' := firstn ((length M) - 512) M in
       stage_2 h' N' Sigma' M'.
Proof.
  intros. eapply Nat.le_lt_trans.
  - apply firstn_le_length.
  - lia.
Defined.

Definition stage_3 (h N Sigma : block512%Z) (M : bits) : block512 :=
  let m' := bits_to_block512_be ((repeat false (511 - (length M))) ++ [true] ++ M) in
  let h_g := g_N N h m' in
  let N' := Vec512.add N (Vec512.repr (Z.of_nat (length M))) in
  let Sigma' := Vec512.add Sigma m' in
  let h_N := g_N IV512 h_g N' in
  let h_S := g_N IV512 h_N Sigma' in
  h_S.

Definition H512 (M : bits) : block512 :=
  let '(h, N, Sigma) := (stage_1 IV512) in
  let '(h', N', Sigma', M') := (stage_2 h N Sigma M) in
  stage_3 h' N' Sigma' M'.

(* --- ПРИЛОЖЕНИЕ: ФУНКЦИОНАЛЬНАЯ СПЕЦИФИКАЦИЯ ОПТИМИЗИРОВАННОГО АЛГОРИТМА --- *)

Definition tableLPS_i_j (i : Z) (j : byte) : int64 := (* i = 0, ... , 7 ; j = 0, ... 255 *)
  fold_right Int64.xor (Int64.repr 0) (map (fun k => (nthi_int64 A (63 - 8 * i - k))) (bit (Byte.unsigned (pi_byte j)))). 

Definition LPS_opt (b : block512) : block512 :=
  let tbytes := tau_bytes (block512_to_bytes b) in
  int64s_to_block512 (
  map (
    fun k => fold_right Int64.xor (Int64.repr 0) (
      map (
        fun i => tableLPS_i_j i (nthi_bytes tbytes (8 * k + i))
        ) 
      [0; 1; 2; 3; 4; 5; 6; 7]
      )
    ) 
    [0; 1; 2; 3; 4; 5; 6; 7]
  ).

Lemma list_int64_nth_equal : forall (l1 : list int64) (l2 : list int64),
  l1 = l2 <-> ((length l1 = length l2) /\ forall (i : nat), (Nat.lt i (length l1)) -> nth i l1 Inhabitant_int64 = nth i l2 Inhabitant_int64).
Proof.
  intros l1 l2.
  split.
  - split. list_solve. list_solve.
  - list_simplify. destruct H as [sizes elements].
    -- rewrite 2!Zlength_correct. 
       rewrite Nat2Z.inj_iff.
       exact sizes.
    -- unfold Znth. 
       destruct (Z_lt_dec i 0).
       --- reflexivity.
       --- destruct H as [sizes elements].
           specialize (elements (Z.to_nat i)).
           lapply elements.
           + trivial.
           + destruct H2 as [ge0 ltl]. unfold Nat.lt.
             rewrite Nat2Z.inj_lt. rewrite Z2Nat_id'. destruct i.
             ++ simpl. rewrite <- Zlength_correct. exact ltl.
             ++ simpl. rewrite <- Zlength_correct. exact ltl.
             ++ simpl. specialize (Zlt_neg_0 p0) as notn. contradiction (n notn).
Qed.

Lemma list_byte_nth_equal : forall (l1 : list byte) (l2 : list byte),
  l1 = l2 <-> ((length l1 = length l2) /\ forall (i : nat), (Nat.lt i (length l1)) -> nth i l1 Inhabitant_byte = nth i l2 Inhabitant_byte).
Proof.
  intros l1 l2.
  split.
  - split. list_solve. list_solve.
  - list_simplify. destruct H as [sizes elements].
    -- rewrite 2!Zlength_correct. 
       rewrite Nat2Z.inj_iff.
       exact sizes.
    -- unfold Znth. 
       destruct (Z_lt_dec i 0).
       --- reflexivity.
       --- destruct H as [sizes elements].
           specialize (elements (Z.to_nat i)).
           lapply elements.
           + trivial.
           + destruct H2 as [ge0 ltl]. unfold Nat.lt.
             rewrite Nat2Z.inj_lt. rewrite Z2Nat_id'. destruct i.
             ++ simpl. rewrite <- Zlength_correct. exact ltl.
             ++ simpl. rewrite <- Zlength_correct. exact ltl.
             ++ simpl. specialize (Zlt_neg_0 p0) as notn. contradiction (n notn).
Qed.

Lemma remove_fold_right_xor : forall (l1 : list int64) (l2 : list int64),
 l1 = l2 -> fold_right Int64.xor (Int64.repr 0) l1 = fold_right Int64.xor (Int64.repr 0) l2.
Proof.
  intros l1 l2 equal.
  list_solve.
Qed.

Lemma remove_map : forall (T1 T2 : Type) (f : T1 -> T2) (l1 : list T1) (l2 : list T1),
  l1 = l2 -> map f l1 = map f l2.
Proof.
  intros T1 T2 f l1 l2 equal.
  list_solve.
Qed.

Lemma ZtoC_length : forall (m : nat) (k : nat) (z : Z),
  length (Z_to_chunks m k z) = k.
Proof.
  intros m k.
  induction k as [| k' IHk'].
  - easy.
  - intros z.
    simpl.
    specialize (IHk' (Z.shiftr z (Z.of_nat m))) as W.
    rewrite W.
    reflexivity.
Qed.

Lemma ZtoB_length : forall (k : nat) (z : Z),
  length (Z_to_bytes k z) = k.
Proof.
  intros k z.
  unfold Z_to_bytes.
  rewrite length_map.
  apply ZtoC_length.
Qed.

Lemma BtoZ_nonneg : forall (k : nat) (lb : list byte),
  0 <= bytes_to_Z k lb.
Proof.
  intros k.
  induction k as [| k' IHk'].
  - easy.
  - intros lb. simpl. destruct lb.
    -- easy.
    -- pose proof (Byte.unsigned_range i).
       apply Z.add_nonneg_nonneg.
       + apply H.
       + apply Z.mul_nonneg_nonneg.
         lia.
         apply Z.mul_nonneg_nonneg.
         lia.
         apply Z.mul_nonneg_nonneg.
         lia.
         apply Z.mul_nonneg_nonneg.
         lia.
         apply Z.mul_nonneg_nonneg.
         lia.
         apply Z.mul_nonneg_nonneg.
         lia.
         apply Z.mul_nonneg_nonneg.
         lia.
         apply Z.mul_nonneg_nonneg.
         lia.
         apply IHk'.
Qed.

Lemma BtoZ_lt : forall (k : nat) (lb : list byte),
 length lb = k -> bytes_to_Z k lb <= (two_power_nat (k * 8%nat)) - 1.
Proof.
  intros k.
  induction k as [| k' IHk'].
  - easy.
  - intros lb.
    intros hyp.
    simpl.
    destruct lb.
    -- discriminate.
    -- assert (Datatypes.length lb = k') as size by list_solve.
       clear hyp.
       rewrite 7!Pos2Z.pos_xI.
       rewrite Pos.pred_double_spec.
       ring_simplify.
       rewrite Pos2Z.inj_pred.
       + assert (Z.pos (shift_nat (k' * 8) 1)~0 = 2 * Z.pos (shift_nat (k' * 8) 1)) as L by apply Pos2Z.pos_xO; rewrite L; clear L.
         rewrite Z.mul_pred_r.
         ring_simplify.
         rewrite shift_nat_correct.
         ring_simplify.
         rewrite <- two_power_nat_correct.
         specialize (IHk' lb).
         lapply IHk'.
         * rep_lia.
         * exact size.
       + easy.
Qed.

Lemma elim_ZtoB : forall (k : nat) (lb : list byte),
  (length lb = k) -> Z_to_bytes k (bytes_to_Z k lb) = lb.
Proof.
  intros k.
  induction k as [| k' IHk'].
  - intros lb size.
    simpl.
    unfold Z_to_bytes.
    unfold Z_to_chunks.
    list_simplify.
    symmetry.
    apply Z2Nat.inj_iff.
    -- exact H2.
    -- lia.
    -- rewrite Zlength_correct.
       simpl.
       rewrite Nat2Z.id.
       exact size.
  - intros lb size'.
    simpl.
    destruct lb.
    + discriminate.
    + assert (Datatypes.length lb = k') as size by list_solve.
      clear size'.
      specialize (IHk' lb).
      lapply IHk'.
      ++ intros H; clear IHk'.
         unfold Z_to_bytes.
         unfold Z_to_chunks.
         fold Z_to_chunks.
         simpl.
         apply cons_congr.
         * assert (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * bytes_to_Z k' lb))))))) = (bytes_to_Z k' lb) * 2^8) as W by lia; rewrite W; clear W.
           unfold LSB.
           rewrite Z_mod_two_p_eq.
           rewrite two_power_nat_equiv.
           rewrite Z_mod_plus_full.
           simpl.
           Search Z.modulo.
           assert (Z.pow_pos 2 8 = Byte.modulus) as K by reflexivity; rewrite K; clear K.
           rewrite <- Byte.unsigned_repr_eq.
           rewrite 2!Byte.repr_unsigned.
           reflexivity.
         * assert ((Z.shiftr (Byte.unsigned i + 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * bytes_to_Z k' lb)))))))) 8) = bytes_to_Z k' lb) as big_one.
           ** assert (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * bytes_to_Z k' lb))))))) = (bytes_to_Z k' lb) * 2^8) as obvious by lia; rewrite obvious; clear obvious.
              rewrite Z.shiftr_div_pow2.
              -- rewrite Z.div_add.
                 --- assert (Byte.unsigned i / 2 ^ 8 = 0) as tiny.
                     { apply Z.div_small. rep_lia. }
                     rewrite tiny.
                     reflexivity.
                 --- lia.
              -- lia.
          ** rewrite big_one; clear big_one.
             auto. (* слева Z_to_bytes по определению *)
      ++ exact size.
Qed.

Lemma elim_transform : forall (lb : list byte),
  (length lb = 64%nat) -> block512_to_bytes (bytes_to_block512 lb) = lb.
Proof.
  intros lb size.
  unfold bytes_to_block512.
  unfold block512_to_bytes.
  list_simplify.
  - rewrite Zlength_correct.
    rewrite ZtoB_length.
    rewrite Zlength_correct.
    apply inj_eq.
    symmetry.
    exact size.
  - clear H0.
    specialize (Vec512.unsigned_repr (bytes_to_Z 64 lb)) as UR.
    lapply UR.
    -- clear UR.
       intros cancel.
       rewrite cancel.
       clear cancel.
       pose proof elim_ZtoB as elim.
       specialize (elim 64%nat lb).
       lapply elim.
       --- clear elim. 
           intros thing.
           rewrite thing.
           + reflexivity.
       --- easy.
    -- split.
       --- apply BtoZ_nonneg.
       --- apply BtoZ_lt.
           exact size.  
Qed.
  
Lemma ps_short : forall (b : block512),
  p (s b) = bytes_to_block512 (tau_bytes (pi (block512_to_bytes b))).
Proof.
  intros b.
  unfold p. 
  unfold s.
  rewrite elim_transform.
  - reflexivity. 
  - reflexivity.
Qed.

Lemma map_nthi_bytes : forall (f : Z -> byte) (l : list Z) (i : Z),
  (0 <= i < Zlength l) -> nthi_bytes (map f l) i = f (nthi_Z l i).
Proof.
  intros f l0 i R.
  destruct R as [ige0 iltsize].
  unfold nthi_bytes.
  assert (Nat.lt (Z.to_nat i) (length l0)).
  { rewrite Nat2Z.inj_lt. rewrite <- Zlength_correct. lia. }
  assert (~ l0 = []).
  {  admit. }
  
Admitted.

Lemma ith_of_pi_tau : forall (b: block512) (i : Z),
  (0 <= i < 64) -> pi_byte (nthi_bytes (tau_bytes (block512_to_bytes b)) i) = nthi_bytes (block512_to_bytes (p (s b))) i.
Proof.
  intros b i R.
  rewrite ps_short.
  rewrite elim_transform.
  unfold tau_bytes.
  assert (Zlength tau = 64) as sixtyfourbytes by reflexivity.
  rewrite <- sixtyfourbytes in R; clear sixtyfourbytes.
  rewrite 2!map_nthi_bytes.
  - admit. 
  - exact R.
  - exact R.
Admitted.

Lemma l_equiv : forall (b : block512), 
  map (fun k : Z =>
     fold_right Int64.xor (Int64.repr 0)
       (map
          (fun i : Z =>
           fold_right Int64.xor (Int64.repr 0)
             (map (fun k0 : Z => nthi_int64 A (63 - 8 * i - k0))
                (bit
                   (Byte.unsigned
                      (nthi_bytes (block512_to_bytes b)
                         (8 * k + i)))))) [0; 1; 2; 3; 4; 5; 6; 7]))
    [0; 1; 2; 3; 4; 5; 6; 7] =
  map (fun x : int64 => b_times_A x) (block512_to_int64s b).
Proof.
  intros b.
  admit.
Admitted.

Definition the_thing (b : block512) (k : Z) : int64 :=
  fold_right Int64.xor (Int64.repr 0)
    (map
       (fun i : Z =>
        fold_right Int64.xor (Int64.repr 0)
          (map (fun k0 : Z => nthi_int64 A (63 - 8 * i - k0))
             (bit
                (Byte.unsigned
                   (pi_byte
                      (nthi_bytes
                         (tau_bytes (block512_to_bytes b))
                         (8 * k + i)))))))
       [0; 1; 2; 3; 4; 5; 6; 7]).

Lemma alg_equiv : forall (b : block512),
  LPS_opt b = l (p (s b)).
Proof.
  intros b.
  unfold LPS_opt.
  unfold tableLPS_i_j.
  assert ((fun k : Z =>
      fold_right Int64.xor (Int64.repr 0)
        (map
           (fun i : Z =>
            fold_right Int64.xor (Int64.repr 0)
              (map (fun k0 : Z => nthi_int64 A (63 - 8 * i - k0))
                 (bit
                    (Byte.unsigned
                       (pi_byte
                          (nthi_bytes
                             (tau_bytes (block512_to_bytes b))
                             (8 * k + i)))))))
           [0; 1; 2; 3; 4; 5; 6; 7])) = the_thing b) as H by reflexivity; rewrite H; clear H.
  assert (map (the_thing b) [0; 1; 2; 3; 4; 5; 6; 7] = 
          map (fun k : Z => fold_right Int64.xor (Int64.repr 0)
    (map
       (fun i : Z =>
        fold_right Int64.xor (Int64.repr 0)
          (map (fun k0 : Z => nthi_int64 A (63 - 8 * i - k0))
             (bit
                (Byte.unsigned
                   (nthi_bytes (block512_to_bytes (p (s b))) (8 * k + i))))))
       [0; 1; 2; 3; 4; 5; 6; 7])) [0; 1; 2; 3; 4; 5; 6; 7]) as H.
  - unfold the_thing.
    pose proof map_ext_in as M.
    specialize (M Z int64 (fun k : Z =>
                             fold_right Int64.xor (Int64.repr 0)
                               (map
                                  (fun i : Z =>
                                   fold_right Int64.xor (Int64.repr 0)
                                     (map (fun k0 : Z => nthi_int64 A (63 - 8 * i - k0))
                                        (bit
                                           (Byte.unsigned
                                              (pi_byte
                                                 (nthi_bytes
                                                    (tau_bytes (block512_to_bytes b))
                                                    (8 * k + i)))))))
                                  [0; 1; 2; 3; 4; 5; 6; 7])) (fun k : Z =>
                             fold_right Int64.xor (Int64.repr 0)
                               (map
                                  (fun i : Z =>
                                   fold_right Int64.xor (Int64.repr 0)
                                     (map (fun k0 : Z => nthi_int64 A (63 - 8 * i - k0))
                                        (bit
                                           (Byte.unsigned
                                              (nthi_bytes (block512_to_bytes (p (s b)))
                                                 (8 * k + i)))))) [0; 1; 2; 3; 4; 5; 6; 7])) [0; 1; 2; 3; 4; 5; 6; 7]).
    lapply M.
    -- trivial.
    -- clear M.
       intros i R1.
       apply remove_fold_right_xor.
       pose proof map_ext_in as M.
       specialize (M Z int64 (fun i0 : Z =>
         fold_right Int64.xor (Int64.repr 0)
           (map (fun k0 : Z => nthi_int64 A (63 - 8 * i0 - k0))
              (bit
                 (Byte.unsigned
                    (pi_byte
                       (nthi_bytes (tau_bytes (block512_to_bytes b))
                          (8 * i + i0))))))) (fun i0 : Z =>
         fold_right Int64.xor (Int64.repr 0)
           (map (fun k0 : Z => nthi_int64 A (63 - 8 * i0 - k0))
              (bit
                 (Byte.unsigned
                    (nthi_bytes (block512_to_bytes (p (s b)))
                       (8 * i + i0)))))) [0; 1; 2; 3; 4; 5; 6; 7] ).
       lapply M.
       + trivial.
       + clear M.
         intros l R2.
         apply remove_fold_right_xor.
         apply remove_map.
         apply f_equal.
         apply f_equal.
         apply ith_of_pi_tau.
         unfold In in R1.
         unfold In in R2.
         lia.
  - rewrite H; clear H.
    unfold l.
    apply f_equal.
    apply l_equiv.
Qed.