From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "streebog_generic.c".
  Definition normalized := true.
End Info.

Definition _Ax : ident := $"Ax".
Definition _C : ident := $"C".
Definition _Ki : ident := $"Ki".
Definition _N : ident := $"N".
Definition _Sigma : ident := $"Sigma".
Definition __179 : ident := $"_179".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___ctx : ident := $"__ctx".
Definition _buf : ident := $"buf".
Definition _buffer : ident := $"buffer".
Definition _buffer0 : ident := $"buffer0".
Definition _buffer512 : ident := $"buffer512".
Definition _carry : ident := $"carry".
Definition _crypto_shash : ident := $"crypto_shash".
Definition _crypto_shash_digestsize : ident := $"crypto_shash_digestsize".
Definition _ctx : ident := $"ctx".
Definition _data : ident := $"data".
Definition _desc : ident := $"desc".
Definition _digest : ident := $"digest".
Definition _digest_size : ident := $"digest_size".
Definition _h : ident := $"h".
Definition _hash : ident := $"hash".
Definition _i : ident := $"i".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _memzero_explicit : ident := $"memzero_explicit".
Definition _qword : ident := $"qword".
Definition _r : ident := $"r".
Definition _r0 : ident := $"r0".
Definition _r1 : ident := $"r1".
Definition _r2 : ident := $"r2".
Definition _r3 : ident := $"r3".
Definition _r4 : ident := $"r4".
Definition _r5 : ident := $"r5".
Definition _r6 : ident := $"r6".
Definition _r7 : ident := $"r7".
Definition _shash_desc : ident := $"shash_desc".
Definition _shash_desc_ctx : ident := $"shash_desc_ctx".
Definition _src : ident := $"src".
Definition _streebog_add512 : ident := $"streebog_add512".
Definition _streebog_finup : ident := $"streebog_finup".
Definition _streebog_g : ident := $"streebog_g".
Definition _streebog_init : ident := $"streebog_init".
Definition _streebog_round : ident := $"streebog_round".
Definition _streebog_stage2 : ident := $"streebog_stage2".
Definition _streebog_stage3 : ident := $"streebog_stage3".
Definition _streebog_state : ident := $"streebog_state".
Definition _streebog_uint512 : ident := $"streebog_uint512".
Definition _streebog_update : ident := $"streebog_update".
Definition _streebog_xlps : ident := $"streebog_xlps".
Definition _streebog_xor : ident := $"streebog_xor".
Definition _sum : ident := $"sum".
Definition _tfm : ident := $"tfm".
Definition _u : ident := $"u".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _z : ident := $"z".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_shash_desc_ctx := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_desc, (tptr (Tstruct _shash_desc noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _desc (tptr (Tstruct _shash_desc noattr)))
                   (Tstruct _shash_desc noattr)) ___ctx
                 (tarray (tptr tvoid) 0))))
|}.

Definition v_buffer0 := {|
  gvar_info := (Tstruct _streebog_uint512 noattr);
  gvar_init := (Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_buffer512 := {|
  gvar_info := (Tstruct _streebog_uint512 noattr);
  gvar_init := (Init_int64 (Int64.repr 512) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_C := {|
  gvar_info := (tarray (Tstruct _streebog_uint512 noattr) 12);
  gvar_init := (Init_int64 (Int64.repr (-2485875557311036153)) ::
                Init_int64 (Int64.repr 393629796148727075) ::
                Init_int64 (Int64.repr (-6754790274496408811)) ::
                Init_int64 (Int64.repr 5439469365787846913) ::
                Init_int64 (Int64.repr 8164666092170888444) ::
                Init_int64 (Int64.repr 3416673298225156118) ::
                Init_int64 (Int64.repr (-1456017820199060449)) ::
                Init_int64 (Int64.repr (-5690197136805012759)) ::
                Init_int64 (Int64.repr (-1839434093156000841)) ::
                Init_int64 (Int64.repr 6187279703545204054) ::
                Init_int64 (Int64.repr 6680353111800457162) ::
                Init_int64 (Int64.repr (-7298901872439027368)) ::
                Init_int64 (Int64.repr 7049644210616860977) ::
                Init_int64 (Int64.repr (-864996302891308136)) ::
                Init_int64 (Int64.repr 5756617672941942231) ::
                Init_int64 (Int64.repr 8044472966569602842) ::
                Init_int64 (Int64.repr (-7413321957414139214)) ::
                Init_int64 (Int64.repr (-4416073813734008015)) ::
                Init_int64 (Int64.repr (-4482987944555914487)) ::
                Init_int64 (Int64.repr (-3178960912623755599)) ::
                Init_int64 (Int64.repr (-942812440248616069)) ::
                Init_int64 (Int64.repr 500284797115703179) ::
                Init_int64 (Int64.repr 736897264563094581) ::
                Init_int64 (Int64.repr (-759739805091352633)) ::
                Init_int64 (Int64.repr 2453545613902729518) ::
                Init_int64 (Int64.repr 3770615292731340785) ::
                Init_int64 (Int64.repr (-2830772728543181890)) ::
                Init_int64 (Int64.repr (-6208444620473117067)) ::
                Init_int64 (Int64.repr (-7101582131303926465)) ::
                Init_int64 (Int64.repr 5228262994497780861) ::
                Init_int64 (Int64.repr (-483888881063566115)) ::
                Init_int64 (Int64.repr (-1216007410580887854)) ::
                Init_int64 (Int64.repr 6924100797842914903) ::
                Init_int64 (Int64.repr 8815411985524614133) ::
                Init_int64 (Int64.repr (-2306123697621624298)) ::
                Init_int64 (Int64.repr (-4626015647904893533)) ::
                Init_int64 (Int64.repr 3863584730013237181) ::
                Init_int64 (Int64.repr 9157256337175220298) ::
                Init_int64 (Int64.repr (-7332070146717441181)) ::
                Init_int64 (Int64.repr 5470303086780565401) ::
                Init_int64 (Int64.repr (-403001272738480786)) ::
                Init_int64 (Int64.repr (-4651719845764640971)) ::
                Init_int64 (Int64.repr 788727410957665974) ::
                Init_int64 (Int64.repr (-3460270058291677260)) ::
                Init_int64 (Int64.repr 1765299679436771014) ::
                Init_int64 (Int64.repr 3271518754420466796) ::
                Init_int64 (Int64.repr 8044769494611016128) ::
                Init_int64 (Int64.repr (-5886294125112011815)) ::
                Init_int64 (Int64.repr (-8609098747985210221)) ::
                Init_int64 (Int64.repr 3825602603916217075) ::
                Init_int64 (Int64.repr 452446299611596036) ::
                Init_int64 (Int64.repr 689802556301519927) ::
                Init_int64 (Int64.repr (-3222538619168582711)) ::
                Init_int64 (Int64.repr 4151974468354279369) ::
                Init_int64 (Int64.repr 5885227241753020756) ::
                Init_int64 (Int64.repr (-808662116433476116)) ::
                Init_int64 (Int64.repr (-6593536122058250466)) ::
                Init_int64 (Int64.repr 3939737308429920473) ::
                Init_int64 (Int64.repr 7625030863455372335) ::
                Init_int64 (Int64.repr (-826080903307786608)) ::
                Init_int64 (Int64.repr (-8524113173205498726)) ::
                Init_int64 (Int64.repr 5672275422532263454) ::
                Init_int64 (Int64.repr 281380427509154113) ::
                Init_int64 (Int64.repr (-7268990933225191001)) ::
                Init_int64 (Int64.repr 8241943909947890395) ::
                Init_int64 (Int64.repr 1024811438257941088) ::
                Init_int64 (Int64.repr 8875339887478807636) ::
                Init_int64 (Int64.repr (-9220482469366411599)) ::
                Init_int64 (Int64.repr 4384629960448215428) ::
                Init_int64 (Int64.repr 4214588714556932644) ::
                Init_int64 (Int64.repr (-7760657801401704482)) ::
                Init_int64 (Int64.repr 4003517910951731867) ::
                Init_int64 (Int64.repr 8409566287612976365) ::
                Init_int64 (Int64.repr 3934170050419472067) ::
                Init_int64 (Int64.repr 8799589676340368116) ::
                Init_int64 (Int64.repr (-6924452640828345525)) ::
                Init_int64 (Int64.repr 2305809517515071747) ::
                Init_int64 (Int64.repr (-8556303705294866213)) ::
                Init_int64 (Int64.repr 4047299315547567091) ::
                Init_int64 (Int64.repr (-6071170440955072686)) ::
                Init_int64 (Int64.repr 7767201709909290267) ::
                Init_int64 (Int64.repr (-2404261073471416227)) ::
                Init_int64 (Int64.repr (-1172399226437013864)) ::
                Init_int64 (Int64.repr (-8494508046909130294)) ::
                Init_int64 (Int64.repr 2306265363756902009) ::
                Init_int64 (Int64.repr (-2811816562482542751)) ::
                Init_int64 (Int64.repr 3459546049211465364) ::
                Init_int64 (Int64.repr 8920961057104103931) ::
                Init_int64 (Int64.repr 5241224916922783520) ::
                Init_int64 (Int64.repr (-363639462662366311)) ::
                Init_int64 (Int64.repr (-1793096024275736494)) ::
                Init_int64 (Int64.repr 6737648500547374214) ::
                Init_int64 (Int64.repr (-567432850498805861)) ::
                Init_int64 (Int64.repr (-3628709211139007113)) ::
                Init_int64 (Int64.repr (-3309159807712644742)) ::
                Init_int64 (Int64.repr 4003391552391360954) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_Ax := {|
  gvar_info := (tarray (tarray tulong 256) 8);
  gvar_init := (Init_int64 (Int64.repr (-3449914152334722842)) ::
                Init_int64 (Int64.repr 1655675436240700197) ::
                Init_int64 (Int64.repr (-6294855228262954552)) ::
                Init_int64 (Int64.repr 7692436852485539419) ::
                Init_int64 (Int64.repr 7944767383739642379) ::
                Init_int64 (Int64.repr 7375912571862768299) ::
                Init_int64 (Int64.repr 8531621007806830582) ::
                Init_int64 (Int64.repr 5446419180642098421) ::
                Init_int64 (Int64.repr (-1059499611280678328)) ::
                Init_int64 (Int64.repr (-4213753619370844929)) ::
                Init_int64 (Int64.repr (-7685436758959488309)) ::
                Init_int64 (Int64.repr (-8507095832536951962)) ::
                Init_int64 (Int64.repr (-5727666919681594315)) ::
                Init_int64 (Int64.repr (-6802251677229597572)) ::
                Init_int64 (Int64.repr (-8254882399351822538)) ::
                Init_int64 (Int64.repr (-2963443116236294498)) ::
                Init_int64 (Int64.repr 4012342115537918347) ::
                Init_int64 (Int64.repr 827838291506483100) ::
                Init_int64 (Int64.repr 6525469606859508924) ::
                Init_int64 (Int64.repr (-1302516510377167899)) ::
                Init_int64 (Int64.repr (-3287696482558819634)) ::
                Init_int64 (Int64.repr 6777738565449644268) ::
                Init_int64 (Int64.repr 2127729288458423481) ::
                Init_int64 (Int64.repr (-5979641435708907380)) ::
                Init_int64 (Int64.repr 3425445086786567286) ::
                Init_int64 (Int64.repr 6283365864194149720) ::
                Init_int64 (Int64.repr 4508966634055461951) ::
                Init_int64 (Int64.repr (-3956347948533301233)) ::
                Init_int64 (Int64.repr (-8958235849539321362)) ::
                Init_int64 (Int64.repr (-6451097220159049968)) ::
                Init_int64 (Int64.repr 1169503776548179293) ::
                Init_int64 (Int64.repr 3236197049891167050) ::
                Init_int64 (Int64.repr 4139797763442523987) ::
                Init_int64 (Int64.repr 665867157242705332) ::
                Init_int64 (Int64.repr (-3632074103806184353)) ::
                Init_int64 (Int64.repr (-480165491543012632)) ::
                Init_int64 (Int64.repr (-7175794025084913793)) ::
                Init_int64 (Int64.repr (-4891266947021344571)) ::
                Init_int64 (Int64.repr 8279328341064508326) ::
                Init_int64 (Int64.repr 8699652512864448814) ::
                Init_int64 (Int64.repr 1493669113326647565) ::
                Init_int64 (Int64.repr (-8913355287108365694)) ::
                Init_int64 (Int64.repr (-7428115828930903249)) ::
                Init_int64 (Int64.repr (-1122594082256748708)) ::
                Init_int64 (Int64.repr (-2638436681903294598)) ::
                Init_int64 (Int64.repr 7213694902063784067) ::
                Init_int64 (Int64.repr 3606986015359070415) ::
                Init_int64 (Int64.repr 2226993429167565701) ::
                Init_int64 (Int64.repr (-1626655458778658891)) ::
                Init_int64 (Int64.repr (-155830074161824072)) ::
                Init_int64 (Int64.repr (-4019354269600588517)) ::
                Init_int64 (Int64.repr 3362491544435630434) ::
                Init_int64 (Int64.repr (-543171864122386436)) ::
                Init_int64 (Int64.repr (-1500748340013990499)) ::
                Init_int64 (Int64.repr 6202204220323106892) ::
                Init_int64 (Int64.repr 7782725910730377251) ::
                Init_int64 (Int64.repr 4992423427324475949) ::
                Init_int64 (Int64.repr (-6069507873198870796)) ::
                Init_int64 (Int64.repr (-4981412381147480387)) ::
                Init_int64 (Int64.repr 8762606059501956154) ::
                Init_int64 (Int64.repr 909032130396396784) ::
                Init_int64 (Int64.repr (-3794130214445188569)) ::
                Init_int64 (Int64.repr (-1581857205145608055)) ::
                Init_int64 (Int64.repr 2911917226527387418) ::
                Init_int64 (Int64.repr (-29606055545944944)) ::
                Init_int64 (Int64.repr (-6986598835479228349)) ::
                Init_int64 (Int64.repr (-7622553720905619977)) ::
                Init_int64 (Int64.repr 5950058544532743196) ::
                Init_int64 (Int64.repr (-7238726919175986157)) ::
                Init_int64 (Int64.repr 5698720643590432933) ::
                Init_int64 (Int64.repr 4590093076103754027) ::
                Init_int64 (Int64.repr (-4051817703674255657)) ::
                Init_int64 (Int64.repr (-7874752173245345369)) ::
                Init_int64 (Int64.repr (-3206675767335985190)) ::
                Init_int64 (Int64.repr 2527688998029402246) ::
                Init_int64 (Int64.repr (-6613068290131372744)) ::
                Init_int64 (Int64.repr (-5475462282476513179)) ::
                Init_int64 (Int64.repr (-2476224818989663998)) ::
                Init_int64 (Int64.repr 746835149394006664) ::
                Init_int64 (Int64.repr (-4439097830540963949)) ::
                Init_int64 (Int64.repr (-8381188714028275378)) ::
                Init_int64 (Int64.repr 3038106099207656754) ::
                Init_int64 (Int64.repr 4803145926997125441) ::
                Init_int64 (Int64.repr 8342440384570031794) ::
                Init_int64 (Int64.repr 567617802345927532) ::
                Init_int64 (Int64.repr (-8462174278995479462)) ::
                Init_int64 (Int64.repr 8025735324585635615) ::
                Init_int64 (Int64.repr (-4114788870165791805)) ::
                Init_int64 (Int64.repr 4929469829189035833) ::
                Init_int64 (Int64.repr (-2156687725213153239)) ::
                Init_int64 (Int64.repr (-6703216507674453184)) ::
                Init_int64 (Int64.repr 1803493583038003433) ::
                Init_int64 (Int64.repr (-798329033517561076)) ::
                Init_int64 (Int64.repr 4866257953349776469) ::
                Init_int64 (Int64.repr (-2881586968609681338)) ::
                Init_int64 (Int64.repr 5904837599487181600) ::
                Init_int64 (Int64.repr (-1751404658544025235)) ::
                Init_int64 (Int64.repr 584899160564492448) ::
                Init_int64 (Int64.repr 4265810503903446395) ::
                Init_int64 (Int64.repr 9177151576238383682) ::
                Init_int64 (Int64.repr 1071073603652986584) ::
                Init_int64 (Int64.repr (-9084530271202362426)) ::
                Init_int64 (Int64.repr (-5646558050215169759)) ::
                Init_int64 (Int64.repr 7611627310280434023) ::
                Init_int64 (Int64.repr (-672316357324885724)) ::
                Init_int64 (Int64.repr 1902669556594646997) ::
                Init_int64 (Int64.repr 3299185814952216158) ::
                Init_int64 (Int64.repr 162323292021668392) ::
                Init_int64 (Int64.repr (-8000659364857713777)) ::
                Init_int64 (Int64.repr 4383024360765511191) ::
                Init_int64 (Int64.repr (-6132602339835939872)) ::
                Init_int64 (Int64.repr 486614660218769016) ::
                Init_int64 (Int64.repr (-2719545495518631314)) ::
                Init_int64 (Int64.repr (-4375968196978273657)) ::
                Init_int64 (Int64.repr 7863729074315859255) ::
                Init_int64 (Int64.repr (-218924545085480020)) ::
                Init_int64 (Int64.repr 8951786643819447678) ::
                Init_int64 (Int64.repr (-353906219941580608)) ::
                Init_int64 (Int64.repr (-4648186943094007815)) ::
                Init_int64 (Int64.repr 7530500863912017011) ::
                Init_int64 (Int64.repr (-3857101380884306125)) ::
                Init_int64 (Int64.repr (-4900426833387150423)) ::
                Init_int64 (Int64.repr 990193778535137764) ::
                Init_int64 (Int64.repr 8117357270855080334) ::
                Init_int64 (Int64.repr (-1958737615231400367)) ::
                Init_int64 (Int64.repr (-8335991217236952542)) ::
                Init_int64 (Int64.repr (-1257524536484031271)) ::
                Init_int64 (Int64.repr 1718822681616686641) ::
                Init_int64 (Int64.repr 6961522769181906131) ::
                Init_int64 (Int64.repr (-5484305234749273335)) ::
                Init_int64 (Int64.repr (-7937688194096367973)) ::
                Init_int64 (Int64.repr 1152200028548938700) ::
                Init_int64 (Int64.repr 5823834453039898164) ::
                Init_int64 (Int64.repr 7773598444791552847) ::
                Init_int64 (Int64.repr (-7748566396808749089)) ::
                Init_int64 (Int64.repr 3101253293019121702) ::
                Init_int64 (Int64.repr 7457074164217006015) ::
                Init_int64 (Int64.repr 5320195162284156637) ::
                Init_int64 (Int64.repr 243449716865181500) ::
                Init_int64 (Int64.repr 2289947023052076689) ::
                Init_int64 (Int64.repr (-6865222830833884824)) ::
                Init_int64 (Int64.repr (-3125766407752414026)) ::
                Init_int64 (Int64.repr 81161648191184148) ::
                Init_int64 (Int64.repr (-6042612589264945768)) ::
                Init_int64 (Int64.repr 6075945013281335908) ::
                Init_int64 (Int64.repr 2788856880649849282) ::
                Init_int64 (Int64.repr (-2395274399495856578)) ::
                Init_int64 (Int64.repr 324396990138905680) ::
                Init_int64 (Int64.repr (-1877593596060902587)) ::
                Init_int64 (Int64.repr (-933557273990899616)) ::
                Init_int64 (Int64.repr 7123846060914028283) ::
                Init_int64 (Int64.repr (-1707799477997380959)) ::
                Init_int64 (Int64.repr (-3695168523200452277)) ::
                Init_int64 (Int64.repr 6031026536892922120) ::
                Init_int64 (Int64.repr 1965816801922384577) ::
                Init_int64 (Int64.repr 3931338956203361439) ::
                Init_int64 (Int64.repr 8861940517347756806) ::
                Init_int64 (Int64.repr (-4729330958009382163)) ::
                Init_int64 (Int64.repr (-3469750885225755017)) ::
                Init_int64 (Int64.repr (-609345208040739792)) ::
                Init_int64 (Int64.repr 5572461372037239437) ::
                Init_int64 (Int64.repr 6858706557858047480) ::
                Init_int64 (Int64.repr 2662949688993444842) ::
                Init_int64 (Int64.repr (-8787131195311298390)) ::
                Init_int64 (Int64.repr 5509314122389360537) ::
                Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr (-1383502062457639183)) ::
                Init_int64 (Int64.repr (-5394441511420951183)) ::
                Init_int64 (Int64.repr (-4538009734547167057)) ::
                Init_int64 (Int64.repr 7294821348383980951) ::
                Init_int64 (Int64.repr 1556781143949091865) ::
                Init_int64 (Int64.repr (-5143453854527814507)) ::
                Init_int64 (Int64.repr (-6231725607568124708)) ::
                Init_int64 (Int64.repr 6399492080795727508) ::
                Init_int64 (Int64.repr 6480618509961472896) ::
                Init_int64 (Int64.repr 6651796292448961220) ::
                Init_int64 (Int64.repr (-9039379881592873734)) ::
                Init_int64 (Int64.repr (-3368928583049484814)) ::
                Init_int64 (Int64.repr 9014933841900722282) ::
                Init_int64 (Int64.repr (-5313138990712806835)) ::
                Init_int64 (Int64.repr 4464185957374872323) ::
                Init_int64 (Int64.repr 8369614684611882462) ::
                Init_int64 (Int64.repr (-2314253684224802006)) ::
                Init_int64 (Int64.repr 4184807344621328495) ::
                Init_int64 (Int64.repr (-416877369211048492)) ::
                Init_int64 (Int64.repr (-4601104153956108869)) ::
                Init_int64 (Int64.repr (-8832334567565406314)) ::
                Init_int64 (Int64.repr (-4276759940385717781)) ::
                Init_int64 (Int64.repr 5118365764737974277) ::
                Init_int64 (Int64.repr (-5817318216839193948)) ::
                Init_int64 (Int64.repr (-7559459305766471453)) ::
                Init_int64 (Int64.repr (-5062433083419813503)) ::
                Init_int64 (Int64.repr 2401711544679111342) ::
                Init_int64 (Int64.repr 3561923520242669555) ::
                Init_int64 (Int64.repr (-3532880518803123357)) ::
                Init_int64 (Int64.repr 4058829818276389447) ::
                Init_int64 (Int64.repr 3886047694019568547) ::
                Init_int64 (Int64.repr (-1832513523723862919)) ::
                Init_int64 (Int64.repr (-2282946932479315455)) ::
                Init_int64 (Int64.repr 8924929278139012626) ::
                Init_int64 (Int64.repr 1331474846468077429) ::
                Init_int64 (Int64.repr 3688112457392680411) ::
                Init_int64 (Int64.repr (-8128869658901373666)) ::
                Init_int64 (Int64.repr (-2800442932217115310)) ::
                Init_int64 (Int64.repr 8594609768612760290) ::
                Init_int64 (Int64.repr 2726061736819093246) ::
                Init_int64 (Int64.repr 8432568231234711754) ::
                Init_int64 (Int64.repr 1394428440333707873) ::
                Init_int64 (Int64.repr 3480761923618622183) ::
                Init_int64 (Int64.repr (-6549938669455423444)) ::
                Init_int64 (Int64.repr (-2557210388226677738)) ::
                Init_int64 (Int64.repr 6606631250711679400) ::
                Init_int64 (Int64.repr (-5565449249649961443)) ::
                Init_int64 (Int64.repr 3805079748905877175) ::
                Init_int64 (Int64.repr 6732799438848024528) ::
                Init_int64 (Int64.repr 1740381552367314429) ::
                Init_int64 (Int64.repr (-7049605152226390697)) ::
                Init_int64 (Int64.repr (-7301821334266889977)) ::
                Init_int64 (Int64.repr (-6640210139413117356)) ::
                Init_int64 (Int64.repr 9114039532680445782) ::
                Init_int64 (Int64.repr (-8706145630329408066)) ::
                Init_int64 (Int64.repr 4740280500255198845) ::
                Init_int64 (Int64.repr (-7364986191033393605)) ::
                Init_int64 (Int64.repr 4677133250592641897) ::
                Init_int64 (Int64.repr 2064740540553908653) ::
                Init_int64 (Int64.repr 5635608617223108017) ::
                Init_int64 (Int64.repr 405364986802432324) ::
                Init_int64 (Int64.repr (-2201961380379971819)) ::
                Init_int64 (Int64.repr (-996686890363501196)) ::
                Init_int64 (Int64.repr (-5232153442900033703)) ::
                Init_int64 (Int64.repr 7204814001741149167) ::
                Init_int64 (Int64.repr (-7112822854342448533)) ::
                Init_int64 (Int64.repr (-2075666958427384515)) ::
                Init_int64 (Int64.repr (-3044622371378720350)) ::
                Init_int64 (Int64.repr (-735322660952861160)) ::
                Init_int64 (Int64.repr 5055377021101169937) ::
                Init_int64 (Int64.repr 2338722779569817530) ::
                Init_int64 (Int64.repr (-4810158077569602095)) ::
                Init_int64 (Int64.repr (-5880324585148774480)) ::
                Init_int64 (Int64.repr (-92735671970965116)) ::
                Init_int64 (Int64.repr 6157071442428213104) ::
                Init_int64 (Int64.repr 2975029274371912206) ::
                Init_int64 (Int64.repr (-6388002753503104508)) ::
                Init_int64 (Int64.repr (-8210013691007369206)) ::
                Init_int64 (Int64.repr 1232492524471570505) ::
                Init_int64 (Int64.repr (-2882334302602089590)) ::
                Init_int64 (Int64.repr (-1176503769679394355)) ::
                Init_int64 (Int64.repr 5257241564096297929) ::
                Init_int64 (Int64.repr 2464735455726714258) ::
                Init_int64 (Int64.repr 7042525932786256327) ::
                Init_int64 (Int64.repr 5383430437057708513) ::
                Init_int64 (Int64.repr (-9165639089139931438)) ::
                Init_int64 (Int64.repr 8180504468988773530) ::
                Init_int64 (Int64.repr (-7811745856517059405)) ::
                Init_int64 (Int64.repr (-8588116552094593422)) ::
                Init_int64 (Int64.repr 2852004074480194774) ::
                Init_int64 (Int64.repr (-2425962953646272056)) ::
                Init_int64 (Int64.repr 1803328357492127077) ::
                Init_int64 (Int64.repr 4858945115384074231) ::
                Init_int64 (Int64.repr 3950575839625518469) ::
                Init_int64 (Int64.repr (-8917695930802984102)) ::
                Init_int64 (Int64.repr (-145076424947021831)) ::
                Init_int64 (Int64.repr 1108813352833195938) ::
                Init_int64 (Int64.repr 7873852611041932237) ::
                Init_int64 (Int64.repr (-8807924330091954304)) ::
                Init_int64 (Int64.repr 4364323801185615026) ::
                Init_int64 (Int64.repr 2398360536387216280) ::
                Init_int64 (Int64.repr 1799390525764624831) ::
                Init_int64 (Int64.repr (-4021501417171059953)) ::
                Init_int64 (Int64.repr (-7486541618912780118)) ::
                Init_int64 (Int64.repr (-6190759395405375648)) ::
                Init_int64 (Int64.repr 3876565764214766838) ::
                Init_int64 (Int64.repr 4796471483616844589) ::
                Init_int64 (Int64.repr (-9078179002738608964)) ::
                Init_int64 (Int64.repr 4426823959205439592) ::
                Init_int64 (Int64.repr (-4867265942287893081)) ::
                Init_int64 (Int64.repr (-8709138140781999575)) ::
                Init_int64 (Int64.repr (-8106050619368481097)) ::
                Init_int64 (Int64.repr (-7276302018314108455)) ::
                Init_int64 (Int64.repr 5995874508989790934) ::
                Init_int64 (Int64.repr (-3904959024401322027)) ::
                Init_int64 (Int64.repr 6121943503617667562) ::
                Init_int64 (Int64.repr (-7357619962525698960)) ::
                Init_int64 (Int64.repr (-594783741313669426)) ::
                Init_int64 (Int64.repr 4057186521996334845) ::
                Init_int64 (Int64.repr (-3371379372744438166)) ::
                Init_int64 (Int64.repr (-963807582447019941)) ::
                Init_int64 (Int64.repr 3606388455605925834) ::
                Init_int64 (Int64.repr (-3402335503256741200)) ::
                Init_int64 (Int64.repr (-2633472432197800099)) ::
                Init_int64 (Int64.repr 4994595691461742609) ::
                Init_int64 (Int64.repr (-287499806972292317)) ::
                Init_int64 (Int64.repr (-415255898085389115)) ::
                Init_int64 (Int64.repr 224924677899329907) ::
                Init_int64 (Int64.repr (-4787903812062860931)) ::
                Init_int64 (Int64.repr (-7117007535139299777)) ::
                Init_int64 (Int64.repr 4643606057380146820) ::
                Init_int64 (Int64.repr 8170101366277257277) ::
                Init_int64 (Int64.repr 5247274052076714522) ::
                Init_int64 (Int64.repr 2843634712633457790) ::
                Init_int64 (Int64.repr 6653764741899674996) ::
                Init_int64 (Int64.repr (-6590095222431687656)) ::
                Init_int64 (Int64.repr 5966053074084851212) ::
                Init_int64 (Int64.repr 6973782895139854790) ::
                Init_int64 (Int64.repr 1053075329826327416) ::
                Init_int64 (Int64.repr 5686957219799131644) ::
                Init_int64 (Int64.repr 6128148527793546544) ::
                Init_int64 (Int64.repr 7744966212764822571) ::
                Init_int64 (Int64.repr 6825189543235932381) ::
                Init_int64 (Int64.repr 6335039532207739033) ::
                Init_int64 (Int64.repr (-702303264799870444)) ::
                Init_int64 (Int64.repr (-2501142381219237701)) ::
                Init_int64 (Int64.repr (-63736767550524848)) ::
                Init_int64 (Int64.repr (-5139509241509718040)) ::
                Init_int64 (Int64.repr (-1691527963252192179)) ::
                Init_int64 (Int64.repr 4579640280547581377) ::
                Init_int64 (Int64.repr (-3805587825649165700)) ::
                Init_int64 (Int64.repr (-5852087023198257873)) ::
                Init_int64 (Int64.repr (-765615049054547097)) ::
                Init_int64 (Int64.repr (-9159531958967877355)) ::
                Init_int64 (Int64.repr 1701221534727831069) ::
                Init_int64 (Int64.repr 143567289798857946) ::
                Init_int64 (Int64.repr (-2699332421248910457)) ::
                Init_int64 (Int64.repr 4948985270110618827) ::
                Init_int64 (Int64.repr (-5543732441286991355)) ::
                Init_int64 (Int64.repr (-2329713146933312238)) ::
                Init_int64 (Int64.repr 4274217762734258062) ::
                Init_int64 (Int64.repr 7342806736664356691) ::
                Init_int64 (Int64.repr 7522333479813991768) ::
                Init_int64 (Int64.repr 2708779702122154455) ::
                Init_int64 (Int64.repr 207476186215560617) ::
                Init_int64 (Int64.repr (-8628431931618945653)) ::
                Init_int64 (Int64.repr 8853646698977545680) ::
                Init_int64 (Int64.repr (-5201797973802170294)) ::
                Init_int64 (Int64.repr 2357279825774737218) ::
                Init_int64 (Int64.repr 8483993473664995954) ::
                Init_int64 (Int64.repr 4724111818068163166) ::
                Init_int64 (Int64.repr (-2768274804658414860)) ::
                Init_int64 (Int64.repr (-5318313563289330544)) ::
                Init_int64 (Int64.repr 2249718511765334659) ::
                Init_int64 (Int64.repr 5272591748466192064) ::
                Init_int64 (Int64.repr (-2073340951391569504)) ::
                Init_int64 (Int64.repr 2776630815808759972) ::
                Init_int64 (Int64.repr (-4083768591946816339)) ::
                Init_int64 (Int64.repr 6748897444385354158) ::
                Init_int64 (Int64.repr (-8314047173220335676)) ::
                Init_int64 (Int64.repr 7194726172547692725) ::
                Init_int64 (Int64.repr 3020746408739878662) ::
                Init_int64 (Int64.repr (-7667334713766802783)) ::
                Init_int64 (Int64.repr 1478557495761493870) ::
                Init_int64 (Int64.repr (-6371379053116686997)) ::
                Init_int64 (Int64.repr (-4653088522465829676)) ::
                Init_int64 (Int64.repr (-7150235257203209499)) ::
                Init_int64 (Int64.repr 8773415655487925411) ::
                Init_int64 (Int64.repr (-8520903472992452271)) ::
                Init_int64 (Int64.repr (-3163975446911651585)) ::
                Init_int64 (Int64.repr (-7901560580871601763)) ::
                Init_int64 (Int64.repr 7005867263497735452) ::
                Init_int64 (Int64.repr 7675725909834103025) ::
                Init_int64 (Int64.repr (-3669878932537014886)) ::
                Init_int64 (Int64.repr (-3679452721810599616)) ::
                Init_int64 (Int64.repr (-3302999316559974631)) ::
                Init_int64 (Int64.repr (-8018343602745740236)) ::
                Init_int64 (Int64.repr 6446852894758673377) ::
                Init_int64 (Int64.repr 3536276771707901625) ::
                Init_int64 (Int64.repr (-4570123184600305775)) ::
                Init_int64 (Int64.repr 1880712834197509142) ::
                Init_int64 (Int64.repr (-1470025562744541890)) ::
                Init_int64 (Int64.repr (-80077366908983670)) ::
                Init_int64 (Int64.repr (-2952009681785237108)) ::
                Init_int64 (Int64.repr 9223162618811069253) ::
                Init_int64 (Int64.repr (-1416020629502695934)) ::
                Init_int64 (Int64.repr 3446931972246104288) ::
                Init_int64 (Int64.repr (-6524226022288242494)) ::
                Init_int64 (Int64.repr (-514065082116261524)) ::
                Init_int64 (Int64.repr 8044714566578636388) ::
                Init_int64 (Int64.repr 899695262891359953) ::
                Init_int64 (Int64.repr 5346640886603386803) ::
                Init_int64 (Int64.repr 7609605358721751426) ::
                Init_int64 (Int64.repr (-1947208340915670372)) ::
                Init_int64 (Int64.repr 7424177041890759418) ::
                Init_int64 (Int64.repr 622456526930891934) ::
                Init_int64 (Int64.repr 5165985204832904632) ::
                Init_int64 (Int64.repr (-4921347668337133925)) ::
                Init_int64 (Int64.repr 1613975629095627463) ::
                Init_int64 (Int64.repr 3743188935298671376) ::
                Init_int64 (Int64.repr (-7807542783308671673)) ::
                Init_int64 (Int64.repr 3525594259049595491) ::
                Init_int64 (Int64.repr 2150892601541107498) ::
                Init_int64 (Int64.repr (-7753463515993923973)) ::
                Init_int64 (Int64.repr (-8935746409621528474)) ::
                Init_int64 (Int64.repr 8872220406569654538) ::
                Init_int64 (Int64.repr 6866296227128558599) ::
                Init_int64 (Int64.repr 3761167278933387308) ::
                Init_int64 (Int64.repr (-305475917358065633)) ::
                Init_int64 (Int64.repr (-4435285524132652488)) ::
                Init_int64 (Int64.repr 4228633590610731860) ::
                Init_int64 (Int64.repr 7835003908488177431) ::
                Init_int64 (Int64.repr (-6722350558698175490)) ::
                Init_int64 (Int64.repr (-1044613210859996888)) ::
                Init_int64 (Int64.repr (-5821121957545137675)) ::
                Init_int64 (Int64.repr 1349613906234605704) ::
                Init_int64 (Int64.repr 5480101227398385749) ::
                Init_int64 (Int64.repr (-5553297850540738849)) ::
                Init_int64 (Int64.repr (-4201136726860115708)) ::
                Init_int64 (Int64.repr (-2543366168260696991)) ::
                Init_int64 (Int64.repr 5697665705733517606) ::
                Init_int64 (Int64.repr (-6041526508745193338)) ::
                Init_int64 (Int64.repr (-1736920950216879121)) ::
                Init_int64 (Int64.repr (-1865833671459600587)) ::
                Init_int64 (Int64.repr 8114372000315616487) ::
                Init_int64 (Int64.repr (-2295405696421701421)) ::
                Init_int64 (Int64.repr (-4301889994291395106)) ::
                Init_int64 (Int64.repr 6514673741809760914) ::
                Init_int64 (Int64.repr 2028745036443421680) ::
                Init_int64 (Int64.repr 7951840676504081086) ::
                Init_int64 (Int64.repr (-8728854924803072269)) ::
                Init_int64 (Int64.repr 3257488053753699657) ::
                Init_int64 (Int64.repr 5462048584050449257) ::
                Init_int64 (Int64.repr 2888449390839178204) ::
                Init_int64 (Int64.repr 2623779414765477133) ::
                Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 2217625486366293593) ::
                Init_int64 (Int64.repr (-2852167199689781714)) ::
                Init_int64 (Int64.repr (-8178668483775083923)) ::
                Init_int64 (Int64.repr 449848170471514086) ::
                Init_int64 (Int64.repr (-2106542423149941382)) ::
                Init_int64 (Int64.repr (-5624522274687379540)) ::
                Init_int64 (Int64.repr (-2172114777618002935)) ::
                Init_int64 (Int64.repr 7212776911211787145) ::
                Init_int64 (Int64.repr (-4130496117776355209)) ::
                Init_int64 (Int64.repr (-2957080010621532842)) ::
                Init_int64 (Int64.repr (-7279105153645570813)) ::
                Init_int64 (Int64.repr 8998286907834995254) ::
                Init_int64 (Int64.repr (-8259426253366367458)) ::
                Init_int64 (Int64.repr 2569772316994557489) ::
                Init_int64 (Int64.repr 7072552358222933103) ::
                Init_int64 (Int64.repr 6202751171352790083) ::
                Init_int64 (Int64.repr (-1245154309739981909)) ::
                Init_int64 (Int64.repr 3101505317318492847) ::
                Init_int64 (Int64.repr 558485074769857340) ::
                Init_int64 (Int64.repr 3227640092592097683) ::
                Init_int64 (Int64.repr (-3181953461981398077)) ::
                Init_int64 (Int64.repr (-7051413710130708660)) ::
                Init_int64 (Int64.repr (-6455244644869543503)) ::
                Init_int64 (Int64.repr 739279269719302455) ::
                Init_int64 (Int64.repr 8664752777909958777) ::
                Init_int64 (Int64.repr 1388453396622152786) ::
                Init_int64 (Int64.repr 6599683241336188488) ::
                Init_int64 (Int64.repr (-6266452200325908973)) ::
                Init_int64 (Int64.repr (-4714453985167570930)) ::
                Init_int64 (Int64.repr 8249767866405689678) ::
                Init_int64 (Int64.repr 2010769185903198412) ::
                Init_int64 (Int64.repr 4499143453925984539) ::
                Init_int64 (Int64.repr (-3032821782465321947)) ::
                Init_int64 (Int64.repr 7420230276096312864) ::
                Init_int64 (Int64.repr (-6059579480658099270)) ::
                Init_int64 (Int64.repr (-1117239733381894670)) ::
                Init_int64 (Int64.repr (-909212912894522239)) ::
                Init_int64 (Int64.repr 369639636906606229) ::
                Init_int64 (Int64.repr (-5920507181493347236)) ::
                Init_int64 (Int64.repr (-1623422355912714089)) ::
                Init_int64 (Int64.repr (-819109107960477763)) ::
                Init_int64 (Int64.repr 674806955088625732) ::
                Init_int64 (Int64.repr 845690623854802413) ::
                Init_int64 (Int64.repr 3095326542374540917) ::
                Init_int64 (Int64.repr 1547806179781594036) ::
                Init_int64 (Int64.repr (-6928131449446634602)) ::
                Init_int64 (Int64.repr (-7978387008151887634)) ::
                Init_int64 (Int64.repr (-5092790373799279822)) ::
                Init_int64 (Int64.repr 8377608645786683048) ::
                Init_int64 (Int64.repr (-8404085163148987144)) ::
                Init_int64 (Int64.repr (-6680135151672486108)) ::
                Init_int64 (Int64.repr 1271666011600462331) ::
                Init_int64 (Int64.repr (-4508766657043449013)) ::
                Init_int64 (Int64.repr 8548435521660023553) ::
                Init_int64 (Int64.repr (-8457552694728712158)) ::
                Init_int64 (Int64.repr 5616893326001226895) ::
                Init_int64 (Int64.repr (-1556162744992024092)) ::
                Init_int64 (Int64.repr (-1205170911864076431)) ::
                Init_int64 (Int64.repr 4156831343068283431) ::
                Init_int64 (Int64.repr 9015744611689039596) ::
                Init_int64 (Int64.repr 1178765317173785889) ::
                Init_int64 (Int64.repr 8600794883889031131) ::
                Init_int64 (Int64.repr 9079622133368661919) ::
                Init_int64 (Int64.repr (-9143218162887404081)) ::
                Init_int64 (Int64.repr (-1322012043035905320)) ::
                Init_int64 (Int64.repr 6379875802289901371) ::
                Init_int64 (Int64.repr 3327029748415724602) ::
                Init_int64 (Int64.repr (-3598675978930772759)) ::
                Init_int64 (Int64.repr 3975920340366592351) ::
                Init_int64 (Int64.repr 351057548220787279) ::
                Init_int64 (Int64.repr (-494374270297395786)) ::
                Init_int64 (Int64.repr (-6797482127449578867)) ::
                Init_int64 (Int64.repr (-6271513871047433527)) ::
                Init_int64 (Int64.repr (-5391202171346223645)) ::
                Init_int64 (Int64.repr 973430231520913931) ::
                Init_int64 (Int64.repr 2474631233414644459) ::
                Init_int64 (Int64.repr 8323529084266646932) ::
                Init_int64 (Int64.repr 5896542754160037759) ::
                Init_int64 (Int64.repr 5776631596258909093) ::
                Init_int64 (Int64.repr (-7531920944658137336)) ::
                Init_int64 (Int64.repr (-1944378678253672890)) ::
                Init_int64 (Int64.repr (-7600052524204151854)) ::
                Init_int64 (Int64.repr (-6893757906364221865)) ::
                Init_int64 (Int64.repr (-5417663775224075975)) ::
                Init_int64 (Int64.repr (-3463018575918649293)) ::
                Init_int64 (Int64.repr (-4355896866576560414)) ::
                Init_int64 (Int64.repr 5066349040802640226) ::
                Init_int64 (Int64.repr (-3832040218430353754)) ::
                Init_int64 (Int64.repr (-5022127186073427391)) ::
                Init_int64 (Int64.repr (-5760205649905515658)) ::
                Init_int64 (Int64.repr (-3682592943448214971)) ::
                Init_int64 (Int64.repr 620745253452480431) ::
                Init_int64 (Int64.repr 7170371354478543620) ::
                Init_int64 (Int64.repr (-3243138426245655406)) ::
                Init_int64 (Int64.repr (-6342229909603660050)) ::
                Init_int64 (Int64.repr 5616375817416440342) ::
                Init_int64 (Int64.repr (-8870679586099490053)) ::
                Init_int64 (Int64.repr 545142251616668746) ::
                Init_int64 (Int64.repr 1840415404509817501) ::
                Init_int64 (Int64.repr 3076816780185585867) ::
                Init_int64 (Int64.repr (-2236038491890475595)) ::
                Init_int64 (Int64.repr (-5265565634421662756)) ::
                Init_int64 (Int64.repr 4655765800686771985) ::
                Init_int64 (Int64.repr (-3184455780776656925)) ::
                Init_int64 (Int64.repr (-4329891895266721376)) ::
                Init_int64 (Int64.repr 967704752989906183) ::
                Init_int64 (Int64.repr (-2453369219621509257)) ::
                Init_int64 (Int64.repr 342320036591677913) ::
                Init_int64 (Int64.repr (-7727424896238752584)) ::
                Init_int64 (Int64.repr 5733492639588199668) ::
                Init_int64 (Int64.repr 8676232990602936187) ::
                Init_int64 (Int64.repr (-2177637442214955324)) ::
                Init_int64 (Int64.repr 891007692783537782) ::
                Init_int64 (Int64.repr 5530953135517340007) ::
                Init_int64 (Int64.repr (-77338390116598942)) ::
                Init_int64 (Int64.repr 5875991211011295779) ::
                Init_int64 (Int64.repr 7908089112272280464) ::
                Init_int64 (Int64.repr (-5351294182861674929)) ::
                Init_int64 (Int64.repr (-1699358638691327462)) ::
                Init_int64 (Int64.repr 5188655642672603326) ::
                Init_int64 (Int64.repr (-3957428329836418835)) ::
                Init_int64 (Int64.repr 1164083840287178307) ::
                Init_int64 (Int64.repr (-688934606240348979)) ::
                Init_int64 (Int64.repr (-5742990474071065369)) ::
                Init_int64 (Int64.repr (-4559415251918357453)) ::
                Init_int64 (Int64.repr (-900500588591915419)) ::
                Init_int64 (Int64.repr 5817298602163052882) ::
                Init_int64 (Int64.repr (-2336254881232391787)) ::
                Init_int64 (Int64.repr (-1017582217264035705)) ::
                Init_int64 (Int64.repr (-5807800758854471359)) ::
                Init_int64 (Int64.repr (-4894935254985706863)) ::
                Init_int64 (Int64.repr 8333329281937734983) ::
                Init_int64 (Int64.repr 2719861874677791534) ::
                Init_int64 (Int64.repr 4885292800615670402) ::
                Init_int64 (Int64.repr (-4024837660657646692)) ::
                Init_int64 (Int64.repr (-469070517292075224)) ::
                Init_int64 (Int64.repr (-959192081528933100)) ::
                Init_int64 (Int64.repr (-2118965651282375849)) ::
                Init_int64 (Int64.repr 4221179734651483784) ::
                Init_int64 (Int64.repr (-8753565237829909479)) ::
                Init_int64 (Int64.repr (-1154590910992552368)) ::
                Init_int64 (Int64.repr (-6581079840356043907)) ::
                Init_int64 (Int64.repr (-6213080069565557126)) ::
                Init_int64 (Int64.repr (-8207737411648898122)) ::
                Init_int64 (Int64.repr 850552765312385596) ::
                Init_int64 (Int64.repr 1402653215185847248) ::
                Init_int64 (Int64.repr 3175939251395899376) ::
                Init_int64 (Int64.repr (-8266124085476784603)) ::
                Init_int64 (Int64.repr 2169261616483133143) ::
                Init_int64 (Int64.repr (-783353522753980066)) ::
                Init_int64 (Int64.repr (-6985242707593122172)) ::
                Init_int64 (Int64.repr 85714207561706353) ::
                Init_int64 (Int64.repr (-3144020876992367703)) ::
                Init_int64 (Int64.repr 7287520887976551487) ::
                Init_int64 (Int64.repr 3605676990221371687) ::
                Init_int64 (Int64.repr (-4723810431255075725)) ::
                Init_int64 (Int64.repr 1026094932781897876) ::
                Init_int64 (Int64.repr 9135574439929960512) ::
                Init_int64 (Int64.repr (-3786270785434042865)) ::
                Init_int64 (Int64.repr 8256622359585822262) ::
                Init_int64 (Int64.repr 4033359129032594319) ::
                Init_int64 (Int64.repr (-7043653618608814603)) ::
                Init_int64 (Int64.repr 8879051520642450152) ::
                Init_int64 (Int64.repr 2463002853672171364) ::
                Init_int64 (Int64.repr 7053292190262318566) ::
                Init_int64 (Int64.repr (-248498398681715328)) ::
                Init_int64 (Int64.repr 3862201594369721709) ::
                Init_int64 (Int64.repr 697442331525125342) ::
                Init_int64 (Int64.repr 6811230057957505478) ::
                Init_int64 (Int64.repr (-5657567826490042474)) ::
                Init_int64 (Int64.repr 171160018304620258) ::
                Init_int64 (Int64.repr (-3337554936541615871)) ::
                Init_int64 (Int64.repr (-5198148571682983763)) ::
                Init_int64 (Int64.repr (-6077992829291364200)) ::
                Init_int64 (Int64.repr (-7219476334722048163)) ::
                Init_int64 (Int64.repr 6351877321657769725) ::
                Init_int64 (Int64.repr (-162784225521973519)) ::
                Init_int64 (Int64.repr (-4289228127673790998)) ::
                Init_int64 (Int64.repr 8526791872987965423) ::
                Init_int64 (Int64.repr 4491371790726137681) ::
                Init_int64 (Int64.repr 4396673666873670338) ::
                Init_int64 (Int64.repr 8743931579300238346) ::
                Init_int64 (Int64.repr 3947926637113932030) ::
                Init_int64 (Int64.repr (-1325742131508201294)) ::
                Init_int64 (Int64.repr 2805305279135909565) ::
                Init_int64 (Int64.repr (-8069744929592156831)) ::
                Init_int64 (Int64.repr 1231502002127476018) ::
                Init_int64 (Int64.repr (-1582241816814275336)) ::
                Init_int64 (Int64.repr 4826890634005776883) ::
                Init_int64 (Int64.repr 3794792297866047004) ::
                Init_int64 (Int64.repr 3135499373384246202) ::
                Init_int64 (Int64.repr 6694122039957974820) ::
                Init_int64 (Int64.repr 1935115932566705934) ::
                Init_int64 (Int64.repr 4338263838416359859) ::
                Init_int64 (Int64.repr (-9059768515799845440)) ::
                Init_int64 (Int64.repr (-7524887977742479061)) ::
                Init_int64 (Int64.repr 5359806862929196636) ::
                Init_int64 (Int64.repr (-5436716847237886658)) ::
                Init_int64 (Int64.repr (-3480054883363057706)) ::
                Init_int64 (Int64.repr (-2795666698909346130)) ::
                Init_int64 (Int64.repr (-2950244695246795206)) ::
                Init_int64 (Int64.repr (-4501005457862486206)) ::
                Init_int64 (Int64.repr (-7898587395205002365)) ::
                Init_int64 (Int64.repr (-1496818034941141111)) ::
                Init_int64 (Int64.repr 5274078341366336463) ::
                Init_int64 (Int64.repr (-2539074510682960890)) ::
                Init_int64 (Int64.repr (-2710223267574174915)) ::
                Init_int64 (Int64.repr 5119503887236322139) ::
                Init_int64 (Int64.repr 3555980726376690868) ::
                Init_int64 (Int64.repr 7382217954126223788) ::
                Init_int64 (Int64.repr 6590727208353260398) ::
                Init_int64 (Int64.repr 4926005702714158792) ::
                Init_int64 (Int64.repr (-4230818350109251941)) ::
                Init_int64 (Int64.repr 5002431046872466873) ::
                Init_int64 (Int64.repr (-9647412374007789)) ::
                Init_int64 (Int64.repr (-7372584286772901441)) ::
                Init_int64 (Int64.repr (-6819610796696852011)) ::
                Init_int64 (Int64.repr 5970409028114053040) ::
                Init_int64 (Int64.repr (-8324807778112606892)) ::
                Init_int64 (Int64.repr (-5884498936515306960)) ::
                Init_int64 (Int64.repr (-7641993521841928247)) ::
                Init_int64 (Int64.repr 8198235727533288357) ::
                Init_int64 (Int64.repr (-3871703311687559810)) ::
                Init_int64 (Int64.repr (-8594982257436140403)) ::
                Init_int64 (Int64.repr (-4994055262696761942)) ::
                Init_int64 (Int64.repr (-8365176187817074402)) ::
                Init_int64 (Int64.repr 1708856473426981385) ::
                Init_int64 (Int64.repr (-5540451013923045004)) ::
                Init_int64 (Int64.repr (-1240014709356264159)) ::
                Init_int64 (Int64.repr (-5129151291003387064)) ::
                Init_int64 (Int64.repr (-8536298547235997700)) ::
                Init_int64 (Int64.repr (-5052725912443115463)) ::
                Init_int64 (Int64.repr 6505014135083665439) ::
                Init_int64 (Int64.repr 1623432725955778936) ::
                Init_int64 (Int64.repr (-4665408230260027646)) ::
                Init_int64 (Int64.repr 5666075560348206981) ::
                Init_int64 (Int64.repr (-1772371873578905089)) ::
                Init_int64 (Int64.repr 8432376462035786364) ::
                Init_int64 (Int64.repr (-6513389927613556724)) ::
                Init_int64 (Int64.repr (-5978916795594578013)) ::
                Init_int64 (Int64.repr 4104100579879510122) ::
                Init_int64 (Int64.repr 6976875711406816919) ::
                Init_int64 (Int64.repr (-7277887262532635604)) ::
                Init_int64 (Int64.repr 2634156532520407135) ::
                Init_int64 (Int64.repr (-3615183629119661772)) ::
                Init_int64 (Int64.repr (-8667861012070027416)) ::
                Init_int64 (Int64.repr 2011540227947838591) ::
                Init_int64 (Int64.repr 7718908375431380139) ::
                Init_int64 (Int64.repr 8373692717517598989) ::
                Init_int64 (Int64.repr (-2881372006732399137)) ::
                Init_int64 (Int64.repr (-4172148963179750648)) ::
                Init_int64 (Int64.repr (-4935653079537058085)) ::
                Init_int64 (Int64.repr (-419653460517795141)) ::
                Init_int64 (Int64.repr (-4095733584013070215)) ::
                Init_int64 (Int64.repr (-7178738375260204265)) ::
                Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 1573734057906676971) ::
                Init_int64 (Int64.repr 8061223461534846322) ::
                Init_int64 (Int64.repr 6896943113662517943) ::
                Init_int64 (Int64.repr (-6684479577299026121)) ::
                Init_int64 (Int64.repr (-1848796134642484594)) ::
                Init_int64 (Int64.repr (-6154690989385782295)) ::
                Init_int64 (Int64.repr 4162510391845980955) ::
                Init_int64 (Int64.repr 2327882902448955782) ::
                Init_int64 (Int64.repr 8793347329267755417) ::
                Init_int64 (Int64.repr 6146178317674281978) ::
                Init_int64 (Int64.repr (-5607868058828707323)) ::
                Init_int64 (Int64.repr (-7592296158317888934)) ::
                Init_int64 (Int64.repr (-9212911660536126686)) ::
                Init_int64 (Int64.repr (-9145213019870214061)) ::
                Init_int64 (Int64.repr (-8974064273515864399)) ::
                Init_int64 (Int64.repr 3488571446366183365) ::
                Init_int64 (Int64.repr (-4818509859632637472)) ::
                Init_int64 (Int64.repr 1782014302901600748) ::
                Init_int64 (Int64.repr 2110589867325741892) ::
                Init_int64 (Int64.repr 428034226284190376) ::
                Init_int64 (Int64.repr 3018429006678390104) ::
                Init_int64 (Int64.repr 8139552000579911892) ::
                Init_int64 (Int64.repr (-7449000817795980594)) ::
                Init_int64 (Int64.repr (-554784672583181223)) ::
                Init_int64 (Int64.repr 6087485725350400139) ::
                Init_int64 (Int64.repr (-1094279311787924490)) ::
                Init_int64 (Int64.repr (-3067315054511761192)) ::
                Init_int64 (Int64.repr 2052188783315922997) ::
                Init_int64 (Int64.repr 3347061610537023762) ::
                Init_int64 (Int64.repr (-6037609370058191662)) ::
                Init_int64 (Int64.repr 7601802823739910729) ::
                Init_int64 (Int64.repr 5427223960002698541) ::
                Init_int64 (Int64.repr (-8441883092361147793)) ::
                Init_int64 (Int64.repr 4732191161638433888) ::
                Init_int64 (Int64.repr 9050129908915332563) ::
                Init_int64 (Int64.repr (-6271772627504251637)) ::
                Init_int64 (Int64.repr 8603498811866336414) ::
                Init_int64 (Int64.repr 8982431302651350690) ::
                Init_int64 (Int64.repr (-2403954569064899868)) ::
                Init_int64 (Int64.repr (-6887300692913143132)) ::
                Init_int64 (Int64.repr 7651500160454006746) ::
                Init_int64 (Int64.repr 2873005019153034700) ::
                Init_int64 (Int64.repr 5061101738461280298) ::
                Init_int64 (Int64.repr (-6427943017191299681)) ::
                Init_int64 (Int64.repr 6047107240176819393) ::
                Init_int64 (Int64.repr (-3565487392017914713)) ::
                Init_int64 (Int64.repr (-860050635144703441)) ::
                Init_int64 (Int64.repr 3691109464541930070) ::
                Init_int64 (Int64.repr 1084786391384093669) ::
                Init_int64 (Int64.repr 2530702575822199829) ::
                Init_int64 (Int64.repr (-2001897773895570324)) ::
                Init_int64 (Int64.repr (-7984313537360218608)) ::
                Init_int64 (Int64.repr 7440628847619289821) ::
                Init_int64 (Int64.repr 7993815229764937219) ::
                Init_int64 (Int64.repr (-7102321862070372250)) ::
                Init_int64 (Int64.repr 6419567200065959308) ::
                Init_int64 (Int64.repr 9221278647829312305) ::
                Init_int64 (Int64.repr 238851030431874451) ::
                Init_int64 (Int64.repr 6204567353729893993) ::
                Init_int64 (Int64.repr 2941723218582937129) ::
                Init_int64 (Int64.repr 3405744221604057699) ::
                Init_int64 (Int64.repr (-3414260775781498256)) ::
                Init_int64 (Int64.repr (-630243096541958212)) ::
                Init_int64 (Int64.repr (-2642523561875128244)) ::
                Init_int64 (Int64.repr 7111960477780928629) ::
                Init_int64 (Int64.repr 791861289948326221) ::
                Init_int64 (Int64.repr 7211104391288295246) ::
                Init_int64 (Int64.repr (-2042541406712225754)) ::
                Init_int64 (Int64.repr 7822657685655187681) ::
                Init_int64 (Int64.repr (-4406307292033340719)) ::
                Init_int64 (Int64.repr (-8131030523631841081)) ::
                Init_int64 (Int64.repr (-8802980963000747638)) ::
                Init_int64 (Int64.repr (-6770192667321592762)) ::
                Init_int64 (Int64.repr 7516371414958424376) ::
                Init_int64 (Int64.repr (-1943496706622208227)) ::
                Init_int64 (Int64.repr 4567787221877943328) ::
                Init_int64 (Int64.repr 1317229451223574689) ::
                Init_int64 (Int64.repr 3252645056251118721) ::
                Init_int64 (Int64.repr (-7831179197836500750)) ::
                Init_int64 (Int64.repr 6281265548225752344) ::
                Init_int64 (Int64.repr (-351962499534708278)) ::
                Init_int64 (Int64.repr (-1631940460066600597)) ::
                Init_int64 (Int64.repr 4297595148202794489) ::
                Init_int64 (Int64.repr (-3008927322846862005)) ::
                Init_int64 (Int64.repr 6761811901839410261) ::
                Init_int64 (Int64.repr 477451256248428347) ::
                Init_int64 (Int64.repr 2245685895371328934) ::
                Init_int64 (Int64.repr 2413588227845229303) ::
                Init_int64 (Int64.repr (-1393160327733685309)) ::
                Init_int64 (Int64.repr 1506315913666580378) ::
                Init_int64 (Int64.repr 2320087374693644805) ::
                Init_int64 (Int64.repr 5719209754774381873) ::
                Init_int64 (Int64.repr (-3101775671365355855)) ::
                Init_int64 (Int64.repr (-9050365550734214517)) ::
                Init_int64 (Int64.repr (-4929072550917658235)) ::
                Init_int64 (Int64.repr (-3928850776122847335)) ::
                Init_int64 (Int64.repr 3289585166342119073) ::
                Init_int64 (Int64.repr 2194422202269271414) ::
                Init_int64 (Int64.repr (-4890882761947363848)) ::
                Init_int64 (Int64.repr (-5430506613987580482)) ::
                Init_int64 (Int64.repr (-1790580594818978458)) ::
                Init_int64 (Int64.repr 5253101879342254412) ::
                Init_int64 (Int64.repr 4812898377434546581) ::
                Init_int64 (Int64.repr (-1178681530171732704)) ::
                Init_int64 (Int64.repr 8149275110868556354) ::
                Init_int64 (Int64.repr (-8380298836167078388)) ::
                Init_int64 (Int64.repr (-3221140405119165748)) ::
                Init_int64 (Int64.repr (-6255680766103790442)) ::
                Init_int64 (Int64.repr (-5540969424577951293)) ::
                Init_int64 (Int64.repr 1432224081074282962) ::
                Init_int64 (Int64.repr (-5598541404947800830)) ::
                Init_int64 (Int64.repr (-8438536854292505907)) ::
                Init_int64 (Int64.repr (-1841429617779050073)) ::
                Init_int64 (Int64.repr (-6576605553857972174)) ::
                Init_int64 (Int64.repr 5004250396549262824) ::
                Init_int64 (Int64.repr (-5641753170762325668)) ::
                Init_int64 (Int64.repr (-1721490171009195683)) ::
                Init_int64 (Int64.repr (-18656020209364820)) ::
                Init_int64 (Int64.repr (-6307253241946191785)) ::
                Init_int64 (Int64.repr 978529526181848228) ::
                Init_int64 (Int64.repr (-1954809287555854024)) ::
                Init_int64 (Int64.repr (-7008601653975951518)) ::
                Init_int64 (Int64.repr 732993552781117657) ::
                Init_int64 (Int64.repr 4273982091657313169) ::
                Init_int64 (Int64.repr (-4160351166546394206)) ::
                Init_int64 (Int64.repr (-3548386105432120348)) ::
                Init_int64 (Int64.repr (-2560674075680303369)) ::
                Init_int64 (Int64.repr 708638407138063495) ::
                Init_int64 (Int64.repr 1465986126796164527) ::
                Init_int64 (Int64.repr (-808716807196504908)) ::
                Init_int64 (Int64.repr (-2512496676984847818)) ::
                Init_int64 (Int64.repr 5352588184630714835) ::
                Init_int64 (Int64.repr (-1907161587179371015)) ::
                Init_int64 (Int64.repr (-751637476751959947)) ::
                Init_int64 (Int64.repr (-8566479464406948205)) ::
                Init_int64 (Int64.repr 6559084273135036574) ::
                Init_int64 (Int64.repr (-6700434047127497649)) ::
                Init_int64 (Int64.repr 4449335781227758381) ::
                Init_int64 (Int64.repr 3035011549083218652) ::
                Init_int64 (Int64.repr (-630689241367039766)) ::
                Init_int64 (Int64.repr (-5328877893137183455)) ::
                Init_int64 (Int64.repr 919603488650096741) ::
                Init_int64 (Int64.repr (-8687403979097325975)) ::
                Init_int64 (Int64.repr (-5160595751240296997)) ::
                Init_int64 (Int64.repr (-574830343725974319)) ::
                Init_int64 (Int64.repr 3019397248150802050) ::
                Init_int64 (Int64.repr (-4101636578841929885)) ::
                Init_int64 (Int64.repr 1097362773642366011) ::
                Init_int64 (Int64.repr (-6749700297327230834)) ::
                Init_int64 (Int64.repr (-4794255656071343815)) ::
                Init_int64 (Int64.repr 5413132634553578770) ::
                Init_int64 (Int64.repr 7909129220654184363) ::
                Init_int64 (Int64.repr (-1022215713790539690)) ::
                Init_int64 (Int64.repr (-6394338277600721812)) ::
                Init_int64 (Int64.repr 7295884259285702637) ::
                Init_int64 (Int64.repr 556320636409441405) ::
                Init_int64 (Int64.repr 4388844399924746220) ::
                Init_int64 (Int64.repr (-4468973790889922593)) ::
                Init_int64 (Int64.repr 4487481272322899827) ::
                Init_int64 (Int64.repr 2849346480598996600) ::
                Init_int64 (Int64.repr (-6796577837039715120)) ::
                Init_int64 (Int64.repr 2800553338224165561) ::
                Init_int64 (Int64.repr 366621570969060578) ::
                Init_int64 (Int64.repr (-289283734738648945)) ::
                Init_int64 (Int64.repr 1039738102615038202) ::
                Init_int64 (Int64.repr (-6923431177941269597)) ::
                Init_int64 (Int64.repr 8877746371250819739) ::
                Init_int64 (Int64.repr 2493984735765172890) ::
                Init_int64 (Int64.repr (-2261116232290008805)) ::
                Init_int64 (Int64.repr 6238298085049257018) ::
                Init_int64 (Int64.repr (-2694943413733724597)) ::
                Init_int64 (Int64.repr 3836460342747308907) ::
                Init_int64 (Int64.repr 2676294094227046119) ::
                Init_int64 (Int64.repr 6767088510282879010) ::
                Init_int64 (Int64.repr (-2148194964369036924)) ::
                Init_int64 (Int64.repr (-7842985187494284346)) ::
                Init_int64 (Int64.repr (-997029337356864504)) ::
                Init_int64 (Int64.repr 8028842627157532468) ::
                Init_int64 (Int64.repr (-8167925555136623890)) ::
                Init_int64 (Int64.repr (-8993163367041208758)) ::
                Init_int64 (Int64.repr 3777009022124537770) ::
                Init_int64 (Int64.repr (-2337610794847163735)) ::
                Init_int64 (Int64.repr (-3715633070431974533)) ::
                Init_int64 (Int64.repr 7824343496386356074) ::
                Init_int64 (Int64.repr 5968143091536305177) ::
                Init_int64 (Int64.repr 1888660633022944597) ::
                Init_int64 (Int64.repr (-901090517175148343)) ::
                Init_int64 (Int64.repr 8278040155680581148) ::
                Init_int64 (Int64.repr (-7470492472060858402)) ::
                Init_int64 (Int64.repr 1654730189087319344) ::
                Init_int64 (Int64.repr (-2783180457764892139)) ::
                Init_int64 (Int64.repr 4181387719565602640) ::
                Init_int64 (Int64.repr 827365096447908888) ::
                Init_int64 (Int64.repr 6460552953851576321) ::
                Init_int64 (Int64.repr 6777930655889878140) ::
                Init_int64 (Int64.repr 306800625468133411) ::
                Init_int64 (Int64.repr (-2950477514527241489)) ::
                Init_int64 (Int64.repr (-7890474300493355257)) ::
                Init_int64 (Int64.repr (-7536238455300955163)) ::
                Init_int64 (Int64.repr 8819014139819394650) ::
                Init_int64 (Int64.repr 5083191892253807030) ::
                Init_int64 (Int64.repr (-6088398616729226231)) ::
                Init_int64 (Int64.repr (-4563133884731507938)) ::
                Init_int64 (Int64.repr 2243741177486741943) ::
                Init_int64 (Int64.repr 6941929889067815695) ::
                Init_int64 (Int64.repr (-4715573645110940313)) ::
                Init_int64 (Int64.repr (-3659154339625476166)) ::
                Init_int64 (Int64.repr 6683059061043741923) ::
                Init_int64 (Int64.repr (-3306965709039809011)) ::
                Init_int64 (Int64.repr 1160172879970786700) ::
                Init_int64 (Int64.repr 2626551480603044390) ::
                Init_int64 (Int64.repr (-1448607739115102973)) ::
                Init_int64 (Int64.repr 193358789913356447) ::
                Init_int64 (Int64.repr (-8779945660529464664)) ::
                Init_int64 (Int64.repr 2931971072476322371) ::
                Init_int64 (Int64.repr 4082995960922195919) ::
                Init_int64 (Int64.repr (-4022115910439396520)) ::
                Init_int64 (Int64.repr 499630455769364668) ::
                Init_int64 (Int64.repr 7131523401393503120) ::
                Init_int64 (Int64.repr (-7420802686533289185)) ::
                Init_int64 (Int64.repr (-2389059867685274008)) ::
                Init_int64 (Int64.repr (-8011457720252985448)) ::
                Init_int64 (Int64.repr 6018044326889064664) ::
                Init_int64 (Int64.repr (-3758507036639090938)) ::
                Init_int64 (Int64.repr (-5866173984516296469)) ::
                Init_int64 (Int64.repr 8974660178948161254) ::
                Init_int64 (Int64.repr (-9166981727465123308)) ::
                Init_int64 (Int64.repr (-8355514108002229647)) ::
                Init_int64 (Int64.repr (-2607906525303178614)) ::
                Init_int64 (Int64.repr 8362774292359536288) ::
                Init_int64 (Int64.repr (-6479053839288561491)) ::
                Init_int64 (Int64.repr 1858955261635127563) ::
                Init_int64 (Int64.repr 5310234037885853069) ::
                Init_int64 (Int64.repr (-1366128151566948929)) ::
                Init_int64 (Int64.repr 7672635907906100182) ::
                Init_int64 (Int64.repr 9088993202633987705) ::
                Init_int64 (Int64.repr (-481125181412677616)) ::
                Init_int64 (Int64.repr 4179004943692288782) ::
                Init_int64 (Int64.repr 6990089781475788750) ::
                Init_int64 (Int64.repr 3341529530529833727) ::
                Init_int64 (Int64.repr (-1114880798226424681)) ::
                Init_int64 (Int64.repr 7183025164891713361) ::
                Init_int64 (Int64.repr (-8074167908327940561)) ::
                Init_int64 (Int64.repr (-8625877922573028782)) ::
                Init_int64 (Int64.repr 5616063725052792238) ::
                Init_int64 (Int64.repr (-7278511447545936063)) ::
                Init_int64 (Int64.repr 7402153298307099571) ::
                Init_int64 (Int64.repr (-7229700661446241408)) ::
                Init_int64 (Int64.repr 6069745939631858853) ::
                Init_int64 (Int64.repr 1702837562631270897) ::
                Init_int64 (Int64.repr (-5335201043789483649)) ::
                Init_int64 (Int64.repr (-4371316523205818560)) ::
                Init_int64 (Int64.repr (-1414710531309244034)) ::
                Init_int64 (Int64.repr (-2866732521391700268)) ::
                Init_int64 (Int64.repr (-269033650220323598)) ::
                Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 6508252928261667935) ::
                Init_int64 (Int64.repr 3640503826637967126) ::
                Init_int64 (Int64.repr (-8260664001902594384)) ::
                Init_int64 (Int64.repr 1348601442542253331) ::
                Init_int64 (Int64.repr (-7741568816862732357)) ::
                Init_int64 (Int64.repr 3470964946849294217) ::
                Init_int64 (Int64.repr (-7114004277834650820)) ::
                Init_int64 (Int64.repr 2406578922524618436) ::
                Init_int64 (Int64.repr 7553767476075066185) ::
                Init_int64 (Int64.repr 1773059382815555018) ::
                Init_int64 (Int64.repr (-2177033920594176550)) ::
                Init_int64 (Int64.repr 7602963013936899976) ::
                Init_int64 (Int64.repr (-8896386920451112393)) ::
                Init_int64 (Int64.repr (-1636090738861820516)) ::
                Init_int64 (Int64.repr 3734279151533349847) ::
                Init_int64 (Int64.repr (-4622501732788078170)) ::
                Init_int64 (Int64.repr (-5700696714579987043)) ::
                Init_int64 (Int64.repr (-3322874679088450989)) ::
                Init_int64 (Int64.repr 1517505774541609326) ::
                Init_int64 (Int64.repr (-4256600509577499843)) ::
                Init_int64 (Int64.repr 286413024150043742) ::
                Init_int64 (Int64.repr (-210742597843175373)) ::
                Init_int64 (Int64.repr 6155127865493844068) ::
                Init_int64 (Int64.repr 3946370957870997301) ::
                Init_int64 (Int64.repr 8456056967321209441) ::
                Init_int64 (Int64.repr 8762568372896872964) ::
                Init_int64 (Int64.repr (-7200548653764673539)) ::
                Init_int64 (Int64.repr 8704785629896584901) ::
                Init_int64 (Int64.repr 2129547851938642216) ::
                Init_int64 (Int64.repr 4872226810457511252) ::
                Init_int64 (Int64.repr 4698189768461680075) ::
                Init_int64 (Int64.repr (-4985745053473129148)) ::
                Init_int64 (Int64.repr 1247139743251908941) ::
                Init_int64 (Int64.repr 3388965918511691326) ::
                Init_int64 (Int64.repr 8547964183296603711) ::
                Init_int64 (Int64.repr (-1534888524315653694)) ::
                Init_int64 (Int64.repr (-2060557476297818811)) ::
                Init_int64 (Int64.repr 1973323469691470228) ::
                Init_int64 (Int64.repr 7212314689372980012) ::
                Init_int64 (Int64.repr (-6490727215686144781)) ::
                Init_int64 (Int64.repr (-691251335016340437)) ::
                Init_int64 (Int64.repr 4544630765357902770) ::
                Init_int64 (Int64.repr 3565762190490661704) ::
                Init_int64 (Int64.repr (-3000886372066288082)) ::
                Init_int64 (Int64.repr 7723062443531325207) ::
                Init_int64 (Int64.repr (-384151690717899698)) ::
                Init_int64 (Int64.repr (-3407607540900108654)) ::
                Init_int64 (Int64.repr 613315330652479558) ::
                Init_int64 (Int64.repr 5848647206772088903) ::
                Init_int64 (Int64.repr (-7620478804617857244)) ::
                Init_int64 (Int64.repr 5623253290867798512) ::
                Init_int64 (Int64.repr 8644379976777982718) ::
                Init_int64 (Int64.repr 9068873100886698535) ::
                Init_int64 (Int64.repr 6865585822045173949) ::
                Init_int64 (Int64.repr (-7960415475299738791)) ::
                Init_int64 (Int64.repr (-78037178252163987)) ::
                Init_int64 (Int64.repr (-6036552908370569100)) ::
                Init_int64 (Int64.repr (-5234453658810295840)) ::
                Init_int64 (Int64.repr (-5782533702257302486)) ::
                Init_int64 (Int64.repr 7943035001321491445) ::
                Init_int64 (Int64.repr 8092813920709807747) ::
                Init_int64 (Int64.repr 6412852391016830144) ::
                Init_int64 (Int64.repr 7489137496080170866) ::
                Init_int64 (Int64.repr (-6846934210082871279)) ::
                Init_int64 (Int64.repr (-5100721943283203814)) ::
                Init_int64 (Int64.repr (-7654125100541031558)) ::
                Init_int64 (Int64.repr (-3854975555138210873)) ::
                Init_int64 (Int64.repr 5800047320741786758) ::
                Init_int64 (Int64.repr (-8800360431393007882)) ::
                Init_int64 (Int64.repr 2079209019540614633) ::
                Init_int64 (Int64.repr (-3052527271044734352)) ::
                Init_int64 (Int64.repr 4639881175437306122) ::
                Init_int64 (Int64.repr 9184509535464604344) ::
                Init_int64 (Int64.repr 3238525380743219808) ::
                Init_int64 (Int64.repr 2579172855526295131) ::
                Init_int64 (Int64.repr (-1228635456184067615)) ::
                Init_int64 (Int64.repr 4910562774881614121) ::
                Init_int64 (Int64.repr (-6136488346548838200)) ::
                Init_int64 (Int64.repr (-5949638873187971915)) ::
                Init_int64 (Int64.repr (-4466850499760778367)) ::
                Init_int64 (Int64.repr (-9106507852447496491)) ::
                Init_int64 (Int64.repr (-4198764938478682116)) ::
                Init_int64 (Int64.repr 5178112573250274679) ::
                Init_int64 (Int64.repr 3119304623419958813) ::
                Init_int64 (Int64.repr 6324631560907806971) ::
                Init_int64 (Int64.repr 8338124726278599389) ::
                Init_int64 (Int64.repr (-3488354259853412571)) ::
                Init_int64 (Int64.repr 5523451468713335151) ::
                Init_int64 (Int64.repr 96679968334812353) ::
                Init_int64 (Int64.repr 4004591297912343540) ::
                Init_int64 (Int64.repr 1804303645561188926) ::
                Init_int64 (Int64.repr 3414564928644964841) ::
                Init_int64 (Int64.repr 8826902743556372053) ::
                Init_int64 (Int64.repr 3678169468562197919) ::
                Init_int64 (Int64.repr 5483028549166638466) ::
                Init_int64 (Int64.repr (-5607253203545098824)) ::
                Init_int64 (Int64.repr 6007599541430339788) ::
                Init_int64 (Int64.repr 4245870974354337847) ::
                Init_int64 (Int64.repr 1219642172907949974) ::
                Init_int64 (Int64.repr 5863970350922153239) ::
                Init_int64 (Int64.repr 1426637866096676526) ::
                Init_int64 (Int64.repr 8329499613195619325) ::
                Init_int64 (Int64.repr 7293460681989249819) ::
                Init_int64 (Int64.repr 5926847591591509039) ::
                Init_int64 (Int64.repr 901996504954577888) ::
                Init_int64 (Int64.repr (-2947435315180425565)) ::
                Init_int64 (Int64.repr 2775869065158040641) ::
                Init_int64 (Int64.repr (-7408003181466091782)) ::
                Init_int64 (Int64.repr 980564833416484611) ::
                Init_int64 (Int64.repr 8122583090029955781) ::
                Init_int64 (Int64.repr (-6339869821034051906)) ::
                Init_int64 (Int64.repr 8252688313299173150) ::
                Init_int64 (Int64.repr (-5308753381427503341)) ::
                Init_int64 (Int64.repr (-3214418720874871800)) ::
                Init_int64 (Int64.repr 4165047539325464847) ::
                Init_int64 (Int64.repr 6537082023027094884) ::
                Init_int64 (Int64.repr 1061388303880967739) ::
                Init_int64 (Int64.repr (-3439216603605990096)) ::
                Init_int64 (Int64.repr 4372598463690682183) ::
                Init_int64 (Int64.repr 5356305457107221234) ::
                Init_int64 (Int64.repr (-2202173221228987020)) ::
                Init_int64 (Int64.repr 6828844005741486031) ::
                Init_int64 (Int64.repr 1634736421828301030) ::
                Init_int64 (Int64.repr 2900055638038661754) ::
                Init_int64 (Int64.repr (-5811428618995110611)) ::
                Init_int64 (Int64.repr (-1236902644612505684)) ::
                Init_int64 (Int64.repr 4319935728839132372) ::
                Init_int64 (Int64.repr (-2012017670879386820)) ::
                Init_int64 (Int64.repr 3189565836107981009) ::
                Init_int64 (Int64.repr 7166733185135723627) ::
                Init_int64 (Int64.repr (-7031080189493389975)) ::
                Init_int64 (Int64.repr 2646876563779348890) ::
                Init_int64 (Int64.repr 4967369675677166793) ::
                Init_int64 (Int64.repr (-4113278884554172970)) ::
                Init_int64 (Int64.repr (-9206676226773480252)) ::
                Init_int64 (Int64.repr 225573111445307704) ::
                Init_int64 (Int64.repr (-8097828069558456804)) ::
                Init_int64 (Int64.repr (-3361284874794094125)) ::
                Init_int64 (Int64.repr 1127567343755846360) ::
                Init_int64 (Int64.repr (-7941683050955393103)) ::
                Init_int64 (Int64.repr 451145037279633264) ::
                Init_int64 (Int64.repr (-1167980319168468145)) ::
                Init_int64 (Int64.repr 4094364856749802988) ::
                Init_int64 (Int64.repr (-4707526179174492584)) ::
                Init_int64 (Int64.repr (-8304679722360230108)) ::
                Init_int64 (Int64.repr (-208911549309316862)) ::
                Init_int64 (Int64.repr 776381720613993616) ::
                Init_int64 (Int64.repr 2123060872304924821) ::
                Init_int64 (Int64.repr 3026796356720902049) ::
                Init_int64 (Int64.repr (-5371983596467790293)) ::
                Init_int64 (Int64.repr (-9141054557691594713)) ::
                Init_int64 (Int64.repr 7010732288709669296) ::
                Init_int64 (Int64.repr 7542466544349531160) ::
                Init_int64 (Int64.repr 2438760495322740690) ::
                Init_int64 (Int64.repr 2361878727220396849) ::
                Init_int64 (Int64.repr 6699855903445002772) ::
                Init_int64 (Int64.repr 8414336326019407982) ::
                Init_int64 (Int64.repr (-890864983621679303)) ::
                Init_int64 (Int64.repr 2586880092266676745) ::
                Init_int64 (Int64.repr 5039677419028043818) ::
                Init_int64 (Int64.repr (-2828973375523697541)) ::
                Init_int64 (Int64.repr (-2274479917113210473)) ::
                Init_int64 (Int64.repr 853819707876968563) ::
                Init_int64 (Int64.repr 9080375331516374270) ::
                Init_int64 (Int64.repr (-5122479655205975768)) ::
                Init_int64 (Int64.repr (-334667111973876110)) ::
                Init_int64 (Int64.repr 1885681234769490694) ::
                Init_int64 (Int64.repr 5632287248797225049) ::
                Init_int64 (Int64.repr 5707966074104112314) ::
                Init_int64 (Int64.repr 5292871832700943306) ::
                Init_int64 (Int64.repr (-4425280711782465667)) ::
                Init_int64 (Int64.repr (-8010115003197586606)) ::
                Init_int64 (Int64.repr 1356511591660649037) ::
                Init_int64 (Int64.repr (-413164002085225839)) ::
                Init_int64 (Int64.repr 1735309813114226397) ::
                Init_int64 (Int64.repr 1482113217594025277) ::
                Init_int64 (Int64.repr (-7345342578160812094)) ::
                Init_int64 (Int64.repr 3920616765481948119) ::
                Init_int64 (Int64.repr (-2539471971494222128)) ::
                Init_int64 (Int64.repr (-7596287390569063390)) ::
                Init_int64 (Int64.repr 3839795465519223535) ::
                Init_int64 (Int64.repr (-3940827641809111282)) ::
                Init_int64 (Int64.repr (-5046731522120745525)) ::
                Init_int64 (Int64.repr (-4263513949386121203)) ::
                Init_int64 (Int64.repr (-1787219754860207612)) ::
                Init_int64 (Int64.repr (-7734133159495177735)) ::
                Init_int64 (Int64.repr 4580146175316881023) ::
                Init_int64 (Int64.repr (-128166216867852230)) ::
                Init_int64 (Int64.repr (-6367617656279915418)) ::
                Init_int64 (Int64.repr 8890201085145809590) ::
                Init_int64 (Int64.repr 3470619621865131175) ::
                Init_int64 (Int64.repr (-8241312141779035193)) ::
                Init_int64 (Int64.repr (-5534876229775900325)) ::
                Init_int64 (Int64.repr 6053592709615805279) ::
                Init_int64 (Int64.repr 646272098254178635) ::
                Init_int64 (Int64.repr (-5888865558858802738)) ::
                Init_int64 (Int64.repr (-8591929326586444401)) ::
                Init_int64 (Int64.repr (-5688488986824788864)) ::
                Init_int64 (Int64.repr (-4983499173087527693)) ::
                Init_int64 (Int64.repr (-4632899522488278341)) ::
                Init_int64 (Int64.repr (-3787219283657948459)) ::
                Init_int64 (Int64.repr (-3597611214417994595)) ::
                Init_int64 (Int64.repr 6214097213063763588) ::
                Init_int64 (Int64.repr (-6957016482492161654)) ::
                Init_int64 (Int64.repr 3107049094019418946) ::
                Init_int64 (Int64.repr 5174286234278374897) ::
                Init_int64 (Int64.repr 2047311623096740982) ::
                Init_int64 (Int64.repr 6907342047472479020) ::
                Init_int64 (Int64.repr (-8999822302401933828)) ::
                Init_int64 (Int64.repr (-9077824446806329057)) ::
                Init_int64 (Int64.repr (-5238628224259478544)) ::
                Init_int64 (Int64.repr (-286278184188467743)) ::
                Init_int64 (Int64.repr 6279086546886369895) ::
                Init_int64 (Int64.repr (-7111763952724994991)) ::
                Init_int64 (Int64.repr 6378829302158147775) ::
                Init_int64 (Int64.repr (-2701260688382412384)) ::
                Init_int64 (Int64.repr 1707114478485218309) ::
                Init_int64 (Int64.repr (-475903766153331799)) ::
                Init_int64 (Int64.repr 8952521925169686821) ::
                Init_int64 (Int64.repr 161643615999915483) ::
                Init_int64 (Int64.repr 7840966349619799731) ::
                Init_int64 (Int64.repr (-1860647909963426073)) ::
                Init_int64 (Int64.repr 4804617751974081465) ::
                Init_int64 (Int64.repr (-1941962826220480545)) ::
                Init_int64 (Int64.repr (-4194022054949071634)) ::
                Init_int64 (Int64.repr 5103108780454484242) ::
                Init_int64 (Int64.repr 7217212288695988216) ::
                Init_int64 (Int64.repr (-8367072105944185673)) ::
                Init_int64 (Int64.repr 7424700593695698624) ::
                Init_int64 (Int64.repr 530837114112846739) ::
                Init_int64 (Int64.repr (-8914914192314866065)) ::
                Init_int64 (Int64.repr 7356337889370479139) ::
                Init_int64 (Int64.repr (-3024245498886546880)) ::
                Init_int64 (Int64.repr 388346999380401736) ::
                Init_int64 (Int64.repr 4445532962863324068) ::
                Init_int64 (Int64.repr 1293141774615853941) ::
                Init_int64 (Int64.repr 2963424300454411929) ::
                Init_int64 (Int64.repr 9159436322932353053) ::
                Init_int64 (Int64.repr (-8178079759457690881)) ::
                Init_int64 (Int64.repr (-6781462814925669610)) ::
                Init_int64 (Int64.repr (-3660351011770032731)) ::
                Init_int64 (Int64.repr (-2764554606629422952)) ::
                Init_int64 (Int64.repr 8745445994659510125) ::
                Init_int64 (Int64.repr 2712499281397177721) ::
                Init_int64 (Int64.repr 8665263526924469134) ::
                Init_int64 (Int64.repr (-1116217019860613631)) ::
                Init_int64 (Int64.repr (-3279969923101429525)) ::
                Init_int64 (Int64.repr 6133214335435724732) ::
                Init_int64 (Int64.repr 2186432824420587949) ::
                Init_int64 (Int64.repr (-2377973508410649845)) ::
                Init_int64 (Int64.repr (-792938586613781334)) ::
                Init_int64 (Int64.repr (-6593048894752561826)) ::
                Init_int64 (Int64.repr (-6846521533785698315)) ::
                Init_int64 (Int64.repr (-7658945859747717862)) ::
                Init_int64 (Int64.repr 2520135847322613482) ::
                Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr (-6431546034540801915)) ::
                Init_int64 (Int64.repr (-3734344276616337082)) ::
                Init_int64 (Int64.repr 3350074738898785546) ::
                Init_int64 (Int64.repr (-3087537290518930568)) ::
                Init_int64 (Int64.repr 5218314535265292073) ::
                Init_int64 (Int64.repr (-7273530722636428511)) ::
                Init_int64 (Int64.repr (-6018834425438917611)) ::
                Init_int64 (Int64.repr (-4857756847281429629)) ::
                Init_int64 (Int64.repr 7679340362327570883) ::
                Init_int64 (Int64.repr (-4356919089224954978)) ::
                Init_int64 (Int64.repr (-1537645436465531641)) ::
                Init_int64 (Int64.repr (-3527000038845257602)) ::
                Init_int64 (Int64.repr (-3860082207360109002)) ::
                Init_int64 (Int64.repr (-6114440854127507578)) ::
                Init_int64 (Int64.repr 7616460892100196603) ::
                Init_int64 (Int64.repr (-2138881533747430324)) ::
                Init_int64 (Int64.repr (-60928274425748263)) ::
                Init_int64 (Int64.repr 8189256918584606246) ::
                Init_int64 (Int64.repr (-8512799164613234324)) ::
                Init_int64 (Int64.repr (-542011385176305846)) ::
                Init_int64 (Int64.repr (-955853235626380326)) ::
                Init_int64 (Int64.repr (-8690054700241246377)) ::
                Init_int64 (Int64.repr (-4915627966968657904)) ::
                Init_int64 (Int64.repr 7091615064334364808) ::
                Init_int64 (Int64.repr (-6718804449902036434)) ::
                Init_int64 (Int64.repr 5550830464468947297) ::
                Init_int64 (Int64.repr 713581410075442600) ::
                Init_int64 (Int64.repr (-1686763414692904740)) ::
                Init_int64 (Int64.repr (-4012569089265581075)) ::
                Init_int64 (Int64.repr (-4564265591045420378)) ::
                Init_int64 (Int64.repr (-7526725183622895423)) ::
                Init_int64 (Int64.repr (-1618962616641948609)) ::
                Init_int64 (Int64.repr 2853872292399425698) ::
                Init_int64 (Int64.repr 323287231984429739) ::
                Init_int64 (Int64.repr 5800111271866173940) ::
                Init_int64 (Int64.repr 6456197019857646684) ::
                Init_int64 (Int64.repr (-4788764096585525408)) ::
                Init_int64 (Int64.repr 3545808073164863556) ::
                Init_int64 (Int64.repr (-8838033575849078132)) ::
                Init_int64 (Int64.repr 8573723725737694645) ::
                Init_int64 (Int64.repr 3771362464791029260) ::
                Init_int64 (Int64.repr (-8756797828000803916)) ::
                Init_int64 (Int64.repr 4508333169251048092) ::
                Init_int64 (Int64.repr 3268697114254873650) ::
                Init_int64 (Int64.repr (-7480936564515780071)) ::
                Init_int64 (Int64.repr (-2622200848586076861)) ::
                Init_int64 (Int64.repr (-3154209968598978661)) ::
                Init_int64 (Int64.repr 4723163230487229057) ::
                Init_int64 (Int64.repr 1553360967820890590) ::
                Init_int64 (Int64.repr 2254305181080907086) ::
                Init_int64 (Int64.repr (-8431561145198858156)) ::
                Init_int64 (Int64.repr (-729080658032404407)) ::
                Init_int64 (Int64.repr (-2067705161691248465)) ::
                Init_int64 (Int64.repr (-5951526195452208906)) ::
                Init_int64 (Int64.repr 4878047023183611738) ::
                Init_int64 (Int64.repr 8492269102247498893) ::
                Init_int64 (Int64.repr (-7861001421720390007)) ::
                Init_int64 (Int64.repr (-6639113455905812787)) ::
                Init_int64 (Int64.repr 6941239243714266451) ::
                Init_int64 (Int64.repr (-7784683798008806806)) ::
                Init_int64 (Int64.repr (-6261302608745827747)) ::
                Init_int64 (Int64.repr (-1036596441456889118)) ::
                Init_int64 (Int64.repr 8639276009782157654) ::
                Init_int64 (Int64.repr 9016941811265117638) ::
                Init_int64 (Int64.repr 1960308938939271141) ::
                Init_int64 (Int64.repr (-1300196596143448428)) ::
                Init_int64 (Int64.repr 4653107235269969506) ::
                Init_int64 (Int64.repr (-5759735688565653405)) ::
                Init_int64 (Int64.repr 8066458028199831435) ::
                Init_int64 (Int64.repr 7912708914327622224) ::
                Init_int64 (Int64.repr (-2314676215374059544)) ::
                Init_int64 (Int64.repr 3608606144348027260) ::
                Init_int64 (Int64.repr (-5445482046623421752)) ::
                Init_int64 (Int64.repr (-666343020445230735)) ::
                Init_int64 (Int64.repr (-1461967762727829020)) ::
                Init_int64 (Int64.repr (-585592186796724846)) ::
                Init_int64 (Int64.repr (-7182445553549598542)) ::
                Init_int64 (Int64.repr 7749952586369404192) ::
                Init_int64 (Int64.repr 3996935472081250100) ::
                Init_int64 (Int64.repr 80822418044728547) ::
                Init_int64 (Int64.repr (-4488018245218812347)) ::
                Init_int64 (Int64.repr 6765964639669133047) ::
                Init_int64 (Int64.repr 7993593952928486248) ::
                Init_int64 (Int64.repr (-6180618743510879387)) ::
                Init_int64 (Int64.repr (-1374752810674738569)) ::
                Init_int64 (Int64.repr 6604321014022046087) ::
                Init_int64 (Int64.repr 5425228831020355089) ::
                Init_int64 (Int64.repr (-2459290586579529165)) ::
                Init_int64 (Int64.repr (-6512227628344389187)) ::
                Init_int64 (Int64.repr (-4038161879859125963)) ::
                Init_int64 (Int64.repr 7884360690673758346) ::
                Init_int64 (Int64.repr 4229988680144045891) ::
                Init_int64 (Int64.repr (-1937086139484354296)) ::
                Init_int64 (Int64.repr (-4715081982172532423)) ::
                Init_int64 (Int64.repr (-5564471778497872191)) ::
                Init_int64 (Int64.repr (-6167321930927824852)) ::
                Init_int64 (Int64.repr (-7338400710296206869)) ::
                Init_int64 (Int64.repr (-2463932355844019820)) ::
                Init_int64 (Int64.repr 1023464176459720743) ::
                Init_int64 (Int64.repr 5953806681838519435) ::
                Init_int64 (Int64.repr (-6703450163338108553)) ::
                Init_int64 (Int64.repr (-8772760200959340123)) ::
                Init_int64 (Int64.repr (-3606869407209130462)) ::
                Init_int64 (Int64.repr (-113514641864290853)) ::
                Init_int64 (Int64.repr (-8496240126189232547)) ::
                Init_int64 (Int64.repr 7464881323799303694) ::
                Init_int64 (Int64.repr 6479838958941986798) ::
                Init_int64 (Int64.repr 2150320025267137967) ::
                Init_int64 (Int64.repr (-1273605029682507155)) ::
                Init_int64 (Int64.repr 3065959290275158261) ::
                Init_int64 (Int64.repr 7768491166058748406) ::
                Init_int64 (Int64.repr (-2160441993028706923)) ::
                Init_int64 (Int64.repr 2838544162962025196) ::
                Init_int64 (Int64.repr (-1543226679767376690)) ::
                Init_int64 (Int64.repr 8143289031230873796) ::
                Init_int64 (Int64.repr (-471136232890197690)) ::
                Init_int64 (Int64.repr 4800734192802798397) ::
                Init_int64 (Int64.repr 5069301847005975966) ::
                Init_int64 (Int64.repr (-7472738570342865356)) ::
                Init_int64 (Int64.repr (-629902337468812959)) ::
                Init_int64 (Int64.repr 3477207782141206983) ::
                Init_int64 (Int64.repr 8393581151604544390) ::
                Init_int64 (Int64.repr 5454200485134280583) ::
                Init_int64 (Int64.repr 1977820635265254611) ::
                Init_int64 (Int64.repr 5336317674550303334) ::
                Init_int64 (Int64.repr 1628702425057113802) ::
                Init_int64 (Int64.repr (-5077194003076684380)) ::
                Init_int64 (Int64.repr (-2807924100419049673)) ::
                Init_int64 (Int64.repr (-7602237927096955373)) ::
                Init_int64 (Int64.repr (-8613989513110587006)) ::
                Init_int64 (Int64.repr 4329693734564294207) ::
                Init_int64 (Int64.repr (-7969704492587394418)) ::
                Init_int64 (Int64.repr (-5341971225009804708)) ::
                Init_int64 (Int64.repr 1002316287956021785) ::
                Init_int64 (Int64.repr 8123817450343849253) ::
                Init_int64 (Int64.repr (-5995244753425626800)) ::
                Init_int64 (Int64.repr 6225750233520130600) ::
                Init_int64 (Int64.repr 2458318110873639342) ::
                Init_int64 (Int64.repr 2800067129256744717) ::
                Init_int64 (Int64.repr 1931480967804418354) ::
                Init_int64 (Int64.repr 5009451183430504352) ::
                Init_int64 (Int64.repr 8277093151698926330) ::
                Init_int64 (Int64.repr 1533108837753842932) ::
                Init_int64 (Int64.repr 2341326448389799537) ::
                Init_int64 (Int64.repr (-384263426088680584)) ::
                Init_int64 (Int64.repr (-5448546659826264131)) ::
                Init_int64 (Int64.repr (-3489603814932409859)) ::
                Init_int64 (Int64.repr (-2276800750205552054)) ::
                Init_int64 (Int64.repr (-3172141978583613005)) ::
                Init_int64 (Int64.repr (-8383428399597182020)) ::
                Init_int64 (Int64.repr 1511499227515113749) ::
                Init_int64 (Int64.repr 4682651676809460962) ::
                Init_int64 (Int64.repr 2567875989502485583) ::
                Init_int64 (Int64.repr 8659386459796397182) ::
                Init_int64 (Int64.repr 2046928348708360270) ::
                Init_int64 (Int64.repr (-4831494504285825306)) ::
                Init_int64 (Int64.repr (-6376617430614617547)) ::
                Init_int64 (Int64.repr (-649224240691737472)) ::
                Init_int64 (Int64.repr (-5718240199574890210)) ::
                Init_int64 (Int64.repr (-3343371736306211220)) ::
                Init_int64 (Int64.repr 4702673030421790979) ::
                Init_int64 (Int64.repr 6054511810836278775) ::
                Init_int64 (Int64.repr (-6064629378475188787)) ::
                Init_int64 (Int64.repr 7499579606458811336) ::
                Init_int64 (Int64.repr 7348514155064275409) ::
                Init_int64 (Int64.repr (-1015567345283557347)) ::
                Init_int64 (Int64.repr (-4492766210804205094)) ::
                Init_int64 (Int64.repr 8813525404883467169) ::
                Init_int64 (Int64.repr 2164994259822327697) ::
                Init_int64 (Int64.repr 6597421062255884337) ::
                Init_int64 (Int64.repr (-9158847352482891559)) ::
                Init_int64 (Int64.repr 9117972659309999362) ::
                Init_int64 (Int64.repr (-4126146149809705657)) ::
                Init_int64 (Int64.repr (-7664125431600212947)) ::
                Init_int64 (Int64.repr 661629067092835514) ::
                Init_int64 (Int64.repr (-8990910267987189017)) ::
                Init_int64 (Int64.repr (-5684699404263594753)) ::
                Init_int64 (Int64.repr 6330108400931796937) ::
                Init_int64 (Int64.repr (-3724884032688239677)) ::
                Init_int64 (Int64.repr 4254967734907730594) ::
                Init_int64 (Int64.repr (-354222358303867239)) ::
                Init_int64 (Int64.repr 3112875118740399380) ::
                Init_int64 (Int64.repr 125923594147773921) ::
                Init_int64 (Int64.repr (-4224348324088252551)) ::
                Init_int64 (Int64.repr 8486087099266182759) ::
                Init_int64 (Int64.repr (-899516704765542462)) ::
                Init_int64 (Int64.repr 3785244107737198436) ::
                Init_int64 (Int64.repr 1778432600275197677) ::
                Init_int64 (Int64.repr 5554327820771626747) ::
                Init_int64 (Int64.repr (-9125873888260111048)) ::
                Init_int64 (Int64.repr 1322990948246386793) ::
                Init_int64 (Int64.repr (-6994470562969759928)) ::
                Init_int64 (Int64.repr (-3590159422512452580)) ::
                Init_int64 (Int64.repr (-4906229482268491141)) ::
                Init_int64 (Int64.repr 511870076939146397) ::
                Init_int64 (Int64.repr 3335510089505707606) ::
                Init_int64 (Int64.repr 8621895138429454776) ::
                Init_int64 (Int64.repr 479028388419905916) ::
                Init_int64 (Int64.repr (-5948196835187346255)) ::
                Init_int64 (Int64.repr 4916377836497777217) ::
                Init_int64 (Int64.repr (-2036806106031103884)) ::
                Init_int64 (Int64.repr 788822923521091204) ::
                Init_int64 (Int64.repr 8314061117774202651) ::
                Init_int64 (Int64.repr 6364252461279863311) ::
                Init_int64 (Int64.repr (-5206656178298892925)) ::
                Init_int64 (Int64.repr 1806257706863174412) ::
                Init_int64 (Int64.repr (-8925191491745597830)) ::
                Init_int64 (Int64.repr 1170806100400807862) ::
                Init_int64 (Int64.repr (-2562262019380620171)) ::
                Init_int64 (Int64.repr (-5173105300452255675)) ::
                Init_int64 (Int64.repr 4837143658242352860) ::
                Init_int64 (Int64.repr (-3447879581381977203)) ::
                Init_int64 (Int64.repr 1667755654663375659) ::
                Init_int64 (Int64.repr (-8008889794384173201)) ::
                Init_int64 (Int64.repr 3602555180387965990) ::
                Init_int64 (Int64.repr (-8517528477369449373)) ::
                Init_int64 (Int64.repr 3455740953342290871) ::
                Init_int64 (Int64.repr 4138546577895857533) ::
                Init_int64 (Int64.repr (-6873844175721544024)) ::
                Init_int64 (Int64.repr (-3996688694222846624)) ::
                Init_int64 (Int64.repr (-5859429290814017905)) ::
                Init_int64 (Int64.repr 1261244456175444567) ::
                Init_int64 (Int64.repr (-1127971154134850052)) ::
                Init_int64 (Int64.repr (-4806383621607904505)) ::
                Init_int64 (Int64.repr (-6835217442743092407)) ::
                Init_int64 (Int64.repr 9031240865077112636) ::
                Init_int64 (Int64.repr (-6217880067417114094)) ::
                Init_int64 (Int64.repr (-2635868727172939544)) ::
                Init_int64 (Int64.repr 394412054692524866) ::
                Init_int64 (Int64.repr 2432314508170265488) ::
                Init_int64 (Int64.repr (-166539262511851547)) ::
                Init_int64 (Int64.repr 7006844330343792498) ::
                Init_int64 (Int64.repr 278346198497942078) ::
                Init_int64 (Int64.repr (-1636572590627387664)) ::
                Init_int64 (Int64.repr (-283995352995468796)) ::
                Init_int64 (Int64.repr 7669743797692376087) ::
                Init_int64 (Int64.repr 9166748306592876771) ::
                Init_int64 (Int64.repr 889372471590932472) ::
                Init_int64 (Int64.repr 3612514438768772632) ::
                Init_int64 (Int64.repr 617497785983336795) ::
                Init_int64 (Int64.repr (-6467473714691543084)) ::
                Init_int64 (Int64.repr 2668158837283114291) ::
                Init_int64 (Int64.repr 5319466677421293656) ::
                Init_int64 (Int64.repr (-783169373594200386)) ::
                Init_int64 (Int64.repr 3285092965046078568) ::
                Init_int64 (Int64.repr 6499223501511427536) ::
                Init_int64 (Int64.repr (-8155684788573646594)) ::
                Init_int64 (Int64.repr (-2328952405567533493)) ::
                Init_int64 (Int64.repr 5524704457816617754) ::
                Init_int64 (Int64.repr 344074004607323811) ::
                Init_int64 (Int64.repr (-2937423556491112688)) ::
                Init_int64 (Int64.repr (-2172860304937777237)) ::
                Init_int64 (Int64.repr 7842383856428453227) ::
                Init_int64 (Int64.repr (-7511948974108511246)) ::
                Init_int64 (Int64.repr (-3107256478340786898)) ::
                Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 2977050733467402955) ::
                Init_int64 (Int64.repr (-4433056559795280924)) ::
                Init_int64 (Int64.repr 6843083487325801331) ::
                Init_int64 (Int64.repr (-5832022095348477074)) ::
                Init_int64 (Int64.repr 4596710564914050049) ::
                Init_int64 (Int64.repr (-3071577655826192177)) ::
                Init_int64 (Int64.repr (-1818622950572616906)) ::
                Init_int64 (Int64.repr (-1659885214252975343)) ::
                Init_int64 (Int64.repr (-1501381660417203921)) ::
                Init_int64 (Int64.repr (-1972215188736740119)) ::
                Init_int64 (Int64.repr (-7235140861651665910)) ::
                Init_int64 (Int64.repr 7977566138855156404) ::
                Init_int64 (Int64.repr (-8646986306084737980)) ::
                Init_int64 (Int64.repr (-4106256846778822490)) ::
                Init_int64 (Int64.repr 5180997731363154047) ::
                Init_int64 (Int64.repr (-7166042126536759145)) ::
                Init_int64 (Int64.repr 9001067694500156125) ::
                Init_int64 (Int64.repr 5676802573628429509) ::
                Init_int64 (Int64.repr 1433107396230432136) ::
                Init_int64 (Int64.repr 6713572130567065933) ::
                Init_int64 (Int64.repr (-7874251917315899216)) ::
                Init_int64 (Int64.repr 5871789863780081333) ::
                Init_int64 (Int64.repr (-3947486326973810559)) ::
                Init_int64 (Int64.repr (-1427497823886641742)) ::
                Init_int64 (Int64.repr (-6603026509317142517)) ::
                Init_int64 (Int64.repr (-2989420375491792143)) ::
                Init_int64 (Int64.repr 7160428156947634349) ::
                Init_int64 (Int64.repr 5989635181614578026) ::
                Init_int64 (Int64.repr 5726136755369928996) ::
                Init_int64 (Int64.repr 5219060730325499321) ::
                Init_int64 (Int64.repr 6865978405987415698) ::
                Init_int64 (Int64.repr 3988783069436589402) ::
                Init_int64 (Int64.repr 4443213711933756382) ::
                Init_int64 (Int64.repr (-8282738182725956928)) ::
                Init_int64 (Int64.repr 3955391676911487163) ::
                Init_int64 (Int64.repr 6177439773473968150) ::
                Init_int64 (Int64.repr (-8308416361595750623)) ::
                Init_int64 (Int64.repr 8509623126890771545) ::
                Init_int64 (Int64.repr (-7353215957417927723)) ::
                Init_int64 (Int64.repr 8001028422964991829) ::
                Init_int64 (Int64.repr (-6966513629138619735)) ::
                Init_int64 (Int64.repr 3835023588467167877) ::
                Init_int64 (Int64.repr 5819661247466791764) ::
                Init_int64 (Int64.repr (-992172329688645085)) ::
                Init_int64 (Int64.repr 8760359772340445599) ::
                Init_int64 (Int64.repr (-1328600795438692269)) ::
                Init_int64 (Int64.repr (-3795396859211817122)) ::
                Init_int64 (Int64.repr 6671019204036865196) ::
                Init_int64 (Int64.repr (-1766067631473053993)) ::
                Init_int64 (Int64.repr 2949792923608203050) ::
                Init_int64 (Int64.repr (-4670242450151420712)) ::
                Init_int64 (Int64.repr (-5514560225174748384)) ::
                Init_int64 (Int64.repr (-519762507317435225)) ::
                Init_int64 (Int64.repr (-9041398016674455802)) ::
                Init_int64 (Int64.repr (-7774109806991103540)) ::
                Init_int64 (Int64.repr (-4339851161610002939)) ::
                Init_int64 (Int64.repr (-5331871504355135390)) ::
                Init_int64 (Int64.repr (-4604611519556647877)) ::
                Init_int64 (Int64.repr 2645981896492773586) ::
                Init_int64 (Int64.repr (-3295201738936550318)) ::
                Init_int64 (Int64.repr 1120074597807199686) ::
                Init_int64 (Int64.repr 4500667440295315936) ::
                Init_int64 (Int64.repr 814351717187214181) ::
                Init_int64 (Int64.repr (-4260608365803648360)) ::
                Init_int64 (Int64.repr (-6493618329290361366)) ::
                Init_int64 (Int64.repr (-5019599812575477862)) ::
                Init_int64 (Int64.repr 4093856693608292508) ::
                Init_int64 (Int64.repr 7125167056442697036) ::
                Init_int64 (Int64.repr 172188691849570271) ::
                Init_int64 (Int64.repr (-3824870562085248321)) ::
                Init_int64 (Int64.repr 6954139586848965267) ::
                Init_int64 (Int64.repr (-2678272281518572279)) ::
                Init_int64 (Int64.repr (-1158445251986509940)) ::
                Init_int64 (Int64.repr 2284666520480811632) ::
                Init_int64 (Int64.repr (-12409227199172550)) ::
                Init_int64 (Int64.repr 8930832123182515776) ::
                Init_int64 (Int64.repr (-820005541954229409)) ::
                Init_int64 (Int64.repr (-8111421418093777633)) ::
                Init_int64 (Int64.repr 3719239275968789497) ::
                Init_int64 (Int64.repr 7225027691790830640) ::
                Init_int64 (Int64.repr 3182251027389772169) ::
                Init_int64 (Int64.repr (-2830686916959593770)) ::
                Init_int64 (Int64.repr 7361072929112976367) ::
                Init_int64 (Int64.repr (-6681141446173123434)) ::
                Init_int64 (Int64.repr (-2444688276085296214)) ::
                Init_int64 (Int64.repr (-7119552812013447818)) ::
                Init_int64 (Int64.repr (-7852492904693613231)) ::
                Init_int64 (Int64.repr (-6337978841883326477)) ::
                Init_int64 (Int64.repr (-8819165761471870053)) ::
                Init_int64 (Int64.repr 7614607569662344745) ::
                Init_int64 (Int64.repr (-4377360315748829314)) ::
                Init_int64 (Int64.repr 6601876756937142135) ::
                Init_int64 (Int64.repr (-5929675153657543200)) ::
                Init_int64 (Int64.repr 5916040036815203718) ::
                Init_int64 (Int64.repr 3849277851845729769) ::
                Init_int64 (Int64.repr (-319966206697414601)) ::
                Init_int64 (Int64.repr 8816361633245169558) ::
                Init_int64 (Int64.repr (-7116582315430182389)) ::
                Init_int64 (Int64.repr 893209141869861107) ::
                Init_int64 (Int64.repr (-759691323564417950)) ::
                Init_int64 (Int64.repr 5391758708148224125) ::
                Init_int64 (Int64.repr 7102355669925669485) ::
                Init_int64 (Int64.repr (-2124313487915786337)) ::
                Init_int64 (Int64.repr (-5493538576740350740)) ::
                Init_int64 (Int64.repr 423967304552176130) ::
                Init_int64 (Int64.repr 1804725524226817960) ::
                Init_int64 (Int64.repr (-7729374423713873670)) ::
                Init_int64 (Int64.repr (-6678900407066117707)) ::
                Init_int64 (Int64.repr (-3712309762369726088)) ::
                Init_int64 (Int64.repr 2604960590806201059) ::
                Init_int64 (Int64.repr 9113370928218001351) ::
                Init_int64 (Int64.repr (-6122178398465021673)) ::
                Init_int64 (Int64.repr (-517539461924792638)) ::
                Init_int64 (Int64.repr 1897625930223618397) ::
                Init_int64 (Int64.repr (-2627044337544422779)) ::
                Init_int64 (Int64.repr (-5368520319573628901)) ::
                Init_int64 (Int64.repr (-8445033315131506186)) ::
                Init_int64 (Int64.repr 6693395487758684627) ::
                Init_int64 (Int64.repr 1246877061712064266) ::
                Init_int64 (Int64.repr (-5108630304876121880)) ::
                Init_int64 (Int64.repr (-9091287293140015199)) ::
                Init_int64 (Int64.repr (-5322907583029518610)) ::
                Init_int64 (Int64.repr (-9217655704367401486)) ::
                Init_int64 (Int64.repr 2195091506890850572) ::
                Init_int64 (Int64.repr 4292257437309723068) ::
                Init_int64 (Int64.repr (-4431135924446288595)) ::
                Init_int64 (Int64.repr 6099518636483903857) ::
                Init_int64 (Int64.repr 5409477760446190126) ::
                Init_int64 (Int64.repr 2101101779678066681) ::
                Init_int64 (Int64.repr 7995562939114222238) ::
                Init_int64 (Int64.repr (-1826248674665228338)) ::
                Init_int64 (Int64.repr 1987411368021760782) ::
                Init_int64 (Int64.repr 3735534939621257502) ::
                Init_int64 (Int64.repr (-2524275000054324191)) ::
                Init_int64 (Int64.repr 6921956260593700555) ::
                Init_int64 (Int64.repr 5095276525830510734) ::
                Init_int64 (Int64.repr 2547781257418198087) ::
                Init_int64 (Int64.repr (-7675626561042279767)) ::
                Init_int64 (Int64.repr 4851558797077234316) ::
                Init_int64 (Int64.repr (-6488579283974826686)) ::
                Init_int64 (Int64.repr (-8326841241218372351)) ::
                Init_int64 (Int64.repr 799517226316244567) ::
                Init_int64 (Int64.repr 1302623186826566143) ::
                Init_int64 (Int64.repr (-113297619603834315)) ::
                Init_int64 (Int64.repr 7344674516440503497) ::
                Init_int64 (Int64.repr (-8623779067870354096)) ::
                Init_int64 (Int64.repr (-8533439458225326333)) ::
                Init_int64 (Int64.repr (-4603126268883107445)) ::
                Init_int64 (Int64.repr (-7973197708536194312)) ::
                Init_int64 (Int64.repr (-4726708571545645492)) ::
                Init_int64 (Int64.repr (-6226578880414609999)) ::
                Init_int64 (Int64.repr (-2172150278249813654)) ::
                Init_int64 (Int64.repr 3386660550720718567) ::
                Init_int64 (Int64.repr (-3363162943429923199)) ::
                Init_int64 (Int64.repr 1786417136983387643) ::
                Init_int64 (Int64.repr 4111277612234687770) ::
                Init_int64 (Int64.repr 2844226767071675414) ::
                Init_int64 (Int64.repr 188896447307719846) ::
                Init_int64 (Int64.repr 6808510159658366325) ::
                Init_int64 (Int64.repr (-410306091488513436)) ::
                Init_int64 (Int64.repr 6512098718293654820) ::
                Init_int64 (Int64.repr 5209617669142570203) ::
                Init_int64 (Int64.repr 4614544691242202233) ::
                Init_int64 (Int64.repr (-5842405484680023275)) ::
                Init_int64 (Int64.repr 8222555220526667572) ::
                Init_int64 (Int64.repr 298135476206323793) ::
                Init_int64 (Int64.repr (-8793714790512611344)) ::
                Init_int64 (Int64.repr (-5024773386346035683)) ::
                Init_int64 (Int64.repr 8348951118537590119) ::
                Init_int64 (Int64.repr (-23519872414406554)) ::
                Init_int64 (Int64.repr (-2330069969849625900)) ::
                Init_int64 (Int64.repr 7812314270723626552) ::
                Init_int64 (Int64.repr (-8986271087935241465)) ::
                Init_int64 (Int64.repr (-3622524305982436565)) ::
                Init_int64 (Int64.repr 781787989577348100) ::
                Init_int64 (Int64.repr 1097545755618110982) ::
                Init_int64 (Int64.repr (-1875247359481405125)) ::
                Init_int64 (Int64.repr (-7431240571726637047)) ::
                Init_int64 (Int64.repr 6413561000250395601) ::
                Init_int64 (Int64.repr (-2297974413839467719)) ::
                Init_int64 (Int64.repr (-2420437325520519033)) ::
                Init_int64 (Int64.repr (-6943483791886702931)) ::
                Init_int64 (Int64.repr (-4934423894786567090)) ::
                Init_int64 (Int64.repr 6041846867914260437) ::
                Init_int64 (Int64.repr 983012176686402208) ::
                Init_int64 (Int64.repr 8013309496113782989) ::
                Init_int64 (Int64.repr 6339875398895908740) ::
                Init_int64 (Int64.repr (-3538666427594506786)) ::
                Init_int64 (Int64.repr 4408181355641015627) ::
                Init_int64 (Int64.repr 7218296214373189274) ::
                Init_int64 (Int64.repr 1490673956378146056) ::
                Init_int64 (Int64.repr (-6020042233644427341)) ::
                Init_int64 (Int64.repr 3609148682737378125) ::
                Init_int64 (Int64.repr 4589759312890931693) ::
                Init_int64 (Int64.repr 485307887131061495) ::
                Init_int64 (Int64.repr (-1006505514783907130)) ::
                Init_int64 (Int64.repr 7400419660088140348) ::
                Init_int64 (Int64.repr (-4811727387649083207)) ::
                Init_int64 (Int64.repr (-201702532122178368)) ::
                Init_int64 (Int64.repr 4031981288869542223) ::
                Init_int64 (Int64.repr 1192539873960017241) ::
                Init_int64 (Int64.repr (-2716847390950127402)) ::
                Init_int64 (Int64.repr (-5720394842221137383)) ::
                Init_int64 (Int64.repr 3404397466593236148) ::
                Init_int64 (Int64.repr 6395260014310152578) ::
                Init_int64 (Int64.repr 8458118805010049424) ::
                Init_int64 (Int64.repr 686637310728372977) ::
                Init_int64 (Int64.repr 9203174238716976532) ::
                Init_int64 (Int64.repr 2790461050153670213) ::
                Init_int64 (Int64.repr (-1215777841619954369)) ::
                Init_int64 (Int64.repr 3551177834962834872) ::
                Init_int64 (Int64.repr 4740930672978945578) ::
                Init_int64 (Int64.repr 8720119818489180515) ::
                Init_int64 (Int64.repr (-6912511404154122432)) ::
                Init_int64 (Int64.repr 4201899973418284015) ::
                Init_int64 (Int64.repr (-3066786703078168880)) ::
                Init_int64 (Int64.repr 5299974858423760520) ::
                Init_int64 (Int64.repr (-8427296656488049755)) ::
                Init_int64 (Int64.repr 2433230087342221537) ::
                Init_int64 (Int64.repr (-8129266751121056780)) ::
                Init_int64 (Int64.repr 3288121563582017554) ::
                Init_int64 (Int64.repr (-4306187085560395302)) ::
                Init_int64 (Int64.repr (-4636922841085486049)) ::
                Init_int64 (Int64.repr (-9040036546550443692)) ::
                Init_int64 (Int64.repr (-7331307946986472273)) ::
                Init_int64 (Int64.repr (-4830036067553482006)) ::
                Init_int64 (Int64.repr 3106896430615223525) ::
                Init_int64 (Int64.repr 2307423530852907698) ::
                Init_int64 (Int64.repr 7902663780872242283) ::
                Init_int64 (Int64.repr 5037306929971572347) ::
                Init_int64 (Int64.repr 7156693133360150590) ::
                Init_int64 (Int64.repr (-6614975166080956655)) ::
                Init_int64 (Int64.repr (-3417482552752718638)) ::
                Init_int64 (Int64.repr (-3835077852318354033)) ::
                Init_int64 (Int64.repr (-2822409101866914704)) ::
                Init_int64 (Int64.repr (-4180372828664472695)) ::
                Init_int64 (Int64.repr (-2886932788949400970)) ::
                Init_int64 (Int64.repr 7454195011690754159) ::
                Init_int64 (Int64.repr (-1530506463707541699)) ::
                Init_int64 (Int64.repr (-5666619509207687094)) ::
                Init_int64 (Int64.repr (-7134301385646206888)) ::
                Init_int64 (Int64.repr (-7798375568681861538)) ::
                Init_int64 (Int64.repr (-1512223366238708370)) ::
                Init_int64 (Int64.repr (-3310794536895637388)) ::
                Init_int64 (Int64.repr 2493451753631079956) ::
                Init_int64 (Int64.repr 4911482502928907304) ::
                Init_int64 (Int64.repr (-3184962692644992473)) ::
                Init_int64 (Int64.repr (-708441506902627689)) ::
                Init_int64 (Int64.repr (-8743626479571068667)) ::
                Init_int64 (Int64.repr (-3013328945128910811)) ::
                Init_int64 (Int64.repr 5149588717409503965) ::
                Init_int64 (Int64.repr 8906728731821217221) ::
                Init_int64 (Int64.repr 8702390857433228080) ::
                Init_int64 (Int64.repr (-6436211820118481993)) ::
                Init_int64 (Int64.repr (-7501402557657795057)) ::
                Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr (-814020811044090319)) ::
                Init_int64 (Int64.repr 6153284078791660322) ::
                Init_int64 (Int64.repr (-7924199979417080819)) ::
                Init_int64 (Int64.repr (-7627788557312613284)) ::
                Init_int64 (Int64.repr 3906157135361813276) ::
                Init_int64 (Int64.repr 3197781696708977217) ::
                Init_int64 (Int64.repr 9018218993023744306) ::
                Init_int64 (Int64.repr 8161215902882505153) ::
                Init_int64 (Int64.repr (-6786679283147301613)) ::
                Init_int64 (Int64.repr 1599033237156680110) ::
                Init_int64 (Int64.repr (-4476747709721996328)) ::
                Init_int64 (Int64.repr 1428437427817679788) ::
                Init_int64 (Int64.repr (-2804118286073414109)) ::
                Init_int64 (Int64.repr 4093558283716908873) ::
                Init_int64 (Int64.repr (-1772500536847563363)) ::
                Init_int64 (Int64.repr (-4079331767052501201)) ::
                Init_int64 (Int64.repr 539627477864709796) ::
                Init_int64 (Int64.repr (-1315147642301337191)) ::
                Init_int64 (Int64.repr (-5824676539528879802)) ::
                Init_int64 (Int64.repr 4797810950713102559) ::
                Init_int64 (Int64.repr (-3817331037150205988)) ::
                Init_int64 (Int64.repr 2731329260335341744) ::
                Init_int64 (Int64.repr 3794965935413333946) ::
                Init_int64 (Int64.repr (-6382454075532447260)) ::
                Init_int64 (Int64.repr (-582634968331372348)) ::
                Init_int64 (Int64.repr (-220003226609410413)) ::
                Init_int64 (Int64.repr (-3520358024446283891)) ::
                Init_int64 (Int64.repr 5688168755867355180) ::
                Init_int64 (Int64.repr 6213507005586580951) ::
                Init_int64 (Int64.repr 5802579435438197024) ::
                Init_int64 (Int64.repr 2991218664073852995) ::
                Init_int64 (Int64.repr (-8689296717482718378)) ::
                Init_int64 (Int64.repr 6711132128484066176) ::
                Init_int64 (Int64.repr 242654484555249397) ::
                Init_int64 (Int64.repr 4389898240254123800) ::
                Init_int64 (Int64.repr (-880136828947304299)) ::
                Init_int64 (Int64.repr (-5126376845970890053)) ::
                Init_int64 (Int64.repr (-2506545781904574862)) ::
                Init_int64 (Int64.repr (-6140469489941988540)) ::
                Init_int64 (Int64.repr (-6316382206818377758)) ::
                Init_int64 (Int64.repr 1725411814906938365) ::
                Init_int64 (Int64.repr (-1405505124110851126)) ::
                Init_int64 (Int64.repr (-7033840997475339010)) ::
                Init_int64 (Int64.repr (-3120544724420889469)) ::
                Init_int64 (Int64.repr 7698554483870415567) ::
                Init_int64 (Int64.repr 2083354945920755114) ::
                Init_int64 (Int64.repr 6898849752995931942) ::
                Init_int64 (Int64.repr (-499802529744829295)) ::
                Init_int64 (Int64.repr (-4133668973393711748)) ::
                Init_int64 (Int64.repr 5706452145863989887) ::
                Init_int64 (Int64.repr (-1613246834554701368)) ::
                Init_int64 (Int64.repr (-8147567720753854041)) ::
                Init_int64 (Int64.repr 1079254955729419349) ::
                Init_int64 (Int64.repr (-5422857798912902584)) ::
                Init_int64 (Int64.repr 8520620050426552165) ::
                Init_int64 (Int64.repr (-1233497186445195412)) ::
                Init_int64 (Int64.repr (-2070001587790852660)) ::
                Init_int64 (Int64.repr 4499963962039319486) ::
                Init_int64 (Int64.repr 2901440900576963088) ::
                Init_int64 (Int64.repr 3088595718209916598) ::
                Init_int64 (Int64.repr (-5197093050450129731)) ::
                Init_int64 (Int64.repr (-8237063220492943534)) ::
                Init_int64 (Int64.repr 7047770774583942296) ::
                Init_int64 (Int64.repr (-1703042169098867813)) ::
                Init_int64 (Int64.repr 5507751753240489098) ::
                Init_int64 (Int64.repr (-8919521605304205917)) ::
                Init_int64 (Int64.repr 3497429715063228395) ::
                Init_int64 (Int64.repr 8403798937519193027) ::
                Init_int64 (Int64.repr 7716863145185650844) ::
                Init_int64 (Int64.repr (-2001633632672730264)) ::
                Init_int64 (Int64.repr 2285441291111813983) ::
                Init_int64 (Int64.repr (-7241512337833627908)) ::
                Init_int64 (Int64.repr 8646452152844209462) ::
                Init_int64 (Int64.repr (-4010445219181588183)) ::
                Init_int64 (Int64.repr 596269939152687266) ::
                Init_int64 (Int64.repr 126396174768673363) ::
                Init_int64 (Int64.repr 7604563766600272954) ::
                Init_int64 (Int64.repr 7514778052044922473) ::
                Init_int64 (Int64.repr 5856909215444622195) ::
                Init_int64 (Int64.repr (-3920095450865433734)) ::
                Init_int64 (Int64.repr (-7412957198037464486)) ::
                Init_int64 (Int64.repr (-1110360782546581920)) ::
                Init_int64 (Int64.repr (-6733220290461783066)) ::
                Init_int64 (Int64.repr (-1056595047710501837)) ::
                Init_int64 (Int64.repr 5597547380311408345) ::
                Init_int64 (Int64.repr 8999927920135924577) ::
                Init_int64 (Int64.repr 8107458139707323282) ::
                Init_int64 (Int64.repr (-8027509882197129045)) ::
                Init_int64 (Int64.repr (-5619916862902856001)) ::
                Init_int64 (Int64.repr 1544449580980397915) ::
                Init_int64 (Int64.repr (-1855670175655579184)) ::
                Init_int64 (Int64.repr 2717085303194761750) ::
                Init_int64 (Int64.repr (-4003578942489519192)) ::
                Init_int64 (Int64.repr 6576332390511288170) ::
                Init_int64 (Int64.repr 863069724348846190) ::
                Init_int64 (Int64.repr (-6082678545258443162)) ::
                Init_int64 (Int64.repr (-699355814275960202)) ::
                Init_int64 (Int64.repr (-753432223757259445)) ::
                Init_int64 (Int64.repr 5257886438263653361) ::
                Init_int64 (Int64.repr (-58105451783010107)) ::
                Init_int64 (Int64.repr (-3769432777904487275)) ::
                Init_int64 (Int64.repr 7401938927912888713) ::
                Init_int64 (Int64.repr 3873430931949926832) ::
                Init_int64 (Int64.repr 8968384715907354529) ::
                Init_int64 (Int64.repr 3891415866600138381) ::
                Init_int64 (Int64.repr (-7037774925807372330)) ::
                Init_int64 (Int64.repr (-8395395091055507401)) ::
                Init_int64 (Int64.repr (-7146083029845058293)) ::
                Init_int64 (Int64.repr (-4882904842532791462)) ::
                Init_int64 (Int64.repr (-1873652220891451667)) ::
                Init_int64 (Int64.repr (-3536131795277924142)) ::
                Init_int64 (Int64.repr (-1403573001291869090)) ::
                Init_int64 (Int64.repr (-5088779607545944291)) ::
                Init_int64 (Int64.repr (-8313586631448043859)) ::
                Init_int64 (Int64.repr 8560443928516176431) ::
                Init_int64 (Int64.repr 6378211438794997847) ::
                Init_int64 (Int64.repr 4574501553864105022) ::
                Init_int64 (Int64.repr 1146093564063439305) ::
                Init_int64 (Int64.repr (-1295543091548012925)) ::
                Init_int64 (Int64.repr 1185632357948392358) ::
                Init_int64 (Int64.repr 6764019065490062352) ::
                Init_int64 (Int64.repr 5365771212091189548) ::
                Init_int64 (Int64.repr 6015059598099124281) ::
                Init_int64 (Int64.repr (-5474560444064672759)) ::
                Init_int64 (Int64.repr 6872018205959509709) ::
                Init_int64 (Int64.repr (-1686595191600669191)) ::
                Init_int64 (Int64.repr 9202609495104344220) ::
                Init_int64 (Int64.repr (-4244889448366757700)) ::
                Init_int64 (Int64.repr (-6416910698925965966)) ::
                Init_int64 (Int64.repr 3336951714131389048) ::
                Init_int64 (Int64.repr 965865579684967188) ::
                Init_int64 (Int64.repr (-9077178407198133628)) ::
                Init_int64 (Int64.repr 3391160715626930072) ::
                Init_int64 (Int64.repr 6673902350225918448) ::
                Init_int64 (Int64.repr 8857268294825045211) ::
                Init_int64 (Int64.repr (-8987061666222536860)) ::
                Init_int64 (Int64.repr (-3481903128941179598)) ::
                Init_int64 (Int64.repr (-8801502686599601122)) ::
                Init_int64 (Int64.repr (-5384443564106997271)) ::
                Init_int64 (Int64.repr (-5178597804944813315)) ::
                Init_int64 (Int64.repr 1985536642513638344) ::
                Init_int64 (Int64.repr 7108223297540317230) ::
                Init_int64 (Int64.repr (-220193061688158216)) ::
                Init_int64 (Int64.repr (-7091786176595613461)) ::
                Init_int64 (Int64.repr 5542313256831765078) ::
                Init_int64 (Int64.repr 2533356463100303724) ::
                Init_int64 (Int64.repr 3282874618864022853) ::
                Init_int64 (Int64.repr (-807362380877997909)) ::
                Init_int64 (Int64.repr (-4792807770903466310)) ::
                Init_int64 (Int64.repr 4190193661499039865) ::
                Init_int64 (Int64.repr (-1092633768219832052)) ::
                Init_int64 (Int64.repr 2825385440488542411) ::
                Init_int64 (Int64.repr (-8503536052429987094)) ::
                Init_int64 (Int64.repr 1931730180050609704) ::
                Init_int64 (Int64.repr (-8001880953073427457)) ::
                Init_int64 (Int64.repr 4831797856215602079) ::
                Init_int64 (Int64.repr (-645269543821293674)) ::
                Init_int64 (Int64.repr 2041167104618677586) ::
                Init_int64 (Int64.repr 1419778117532032155) ::
                Init_int64 (Int64.repr (-6542979007418555825)) ::
                Init_int64 (Int64.repr 3103633138851124799) ::
                Init_int64 (Int64.repr (-2890213137699028537)) ::
                Init_int64 (Int64.repr (-6362912389259573102)) ::
                Init_int64 (Int64.repr (-2700866930001153325)) ::
                Init_int64 (Int64.repr (-8783460708933027037)) ::
                Init_int64 (Int64.repr 4082021896479345316) ::
                Init_int64 (Int64.repr 7311838950535313076) ::
                Init_int64 (Int64.repr 180372299864271581) ::
                Init_int64 (Int64.repr (-8593512055977044214)) ::
                Init_int64 (Int64.repr (-7839714311743241022)) ::
                Init_int64 (Int64.repr 5650486102836879499) ::
                Init_int64 (Int64.repr 3610925162266685226) ::
                Init_int64 (Int64.repr 4723485642561124674) ::
                Init_int64 (Int64.repr (-5576801316286630029)) ::
                Init_int64 (Int64.repr 7782831729257630727) ::
                Init_int64 (Int64.repr 6486091814822439562) ::
                Init_int64 (Int64.repr 2275312179377199727) ::
                Init_int64 (Int64.repr (-4356577886369969210)) ::
                Init_int64 (Int64.repr 4172206937772523332) ::
                Init_int64 (Int64.repr 2995630716225649890) ::
                Init_int64 (Int64.repr 4669626403474246818) ::
                Init_int64 (Int64.repr (-1596266820948465639)) ::
                Init_int64 (Int64.repr 875836825476482804) ::
                Init_int64 (Int64.repr 6189217070523331395) ::
                Init_int64 (Int64.repr 5066712921838268376) ::
                Init_int64 (Int64.repr 2371264715879810641) ::
                Init_int64 (Int64.repr 7873072164890950119) ::
                Init_int64 (Int64.repr (-6886072823080673784)) ::
                Init_int64 (Int64.repr 8911427141841525051) ::
                Init_int64 (Int64.repr 4777501028543424127) ::
                Init_int64 (Int64.repr (-2881080619539589106)) ::
                Init_int64 (Int64.repr (-4118760127225645183)) ::
                Init_int64 (Int64.repr 2425335601897305009) ::
                Init_int64 (Int64.repr 7491757150872493161) ::
                Init_int64 (Int64.repr 2663298514356195318) ::
                Init_int64 (Int64.repr (-3070564545610994918)) ::
                Init_int64 (Int64.repr 6782062002344207149) ::
                Init_int64 (Int64.repr 2941544419792095490) ::
                Init_int64 (Int64.repr (-8115464587714903664)) ::
                Init_int64 (Int64.repr 1705056651829531964) ::
                Init_int64 (Int64.repr (-2260216328267754838)) ::
                Init_int64 (Int64.repr 8677197541547869702) ::
                Init_int64 (Int64.repr 7963177360326436570) ::
                Init_int64 (Int64.repr (-8693626961078038845)) ::
                Init_int64 (Int64.repr 3981744263096980333) ::
                Init_int64 (Int64.repr (-6032473073021265668)) ::
                Init_int64 (Int64.repr 9148734745269085564) ::
                Init_int64 (Int64.repr (-4590727628469627653)) ::
                Init_int64 (Int64.repr (-455745844559811649)) ::
                Init_int64 (Int64.repr 8327617951594157672) ::
                Init_int64 (Int64.repr 3700969465860692682) ::
                Init_int64 (Int64.repr (-6263042869234113349)) ::
                Init_int64 (Int64.repr (-1963681140045128947)) ::
                Init_int64 (Int64.repr (-8205282925170609040)) ::
                Init_int64 (Int64.repr 5906760578843179748) ::
                Init_int64 (Int64.repr 2479410904363822220) ::
                Init_int64 (Int64.repr (-2790911102072263186)) ::
                Init_int64 (Int64.repr 3592944206891151383) ::
                Init_int64 (Int64.repr (-3170985866774345632)) ::
                Init_int64 (Int64.repr 683125414101514931) ::
                Init_int64 (Int64.repr (-7275100120953320559)) ::
                Init_int64 (Int64.repr (-3716053015111380465)) ::
                Init_int64 (Int64.repr 3783544556444699728) ::
                Init_int64 (Int64.repr 5704484573958821227) ::
                Init_int64 (Int64.repr (-2316541444978192748)) ::
                Init_int64 (Int64.repr 2771156630664652075) ::
                Init_int64 (Int64.repr (-4612731519127272345)) ::
                Init_int64 (Int64.repr (-2496909048962603959)) ::
                Init_int64 (Int64.repr 4376304874819502851) ::
                Init_int64 (Int64.repr (-7947882507510911457)) ::
                Init_int64 (Int64.repr 7502908372889601440) ::
                Init_int64 (Int64.repr (-5294337677919502636)) ::
                Init_int64 (Int64.repr 1470905800566295041) ::
                Init_int64 (Int64.repr (-7437272530063551316)) ::
                Init_int64 (Int64.repr 7221583138996667220) ::
                Init_int64 (Int64.repr (-4410508179385483738)) ::
                Init_int64 (Int64.repr 4484192965699807710) ::
                Init_int64 (Int64.repr 5816942215693799172) ::
                Init_int64 (Int64.repr 5012702627552211173) ::
                Init_int64 (Int64.repr 6928142386668309235) ::
                Init_int64 (Int64.repr (-347883043654205086)) ::
                Init_int64 (Int64.repr (-6832198047417275416)) ::
                Init_int64 (Int64.repr 5420052663719632076) ::
                Init_int64 (Int64.repr 592816685880348499) ::
                Init_int64 (Int64.repr (-4536641222120152805)) ::
                Init_int64 (Int64.repr (-6983915695234563530)) ::
                Init_int64 (Int64.repr 476621763234702202) ::
                Init_int64 (Int64.repr (-1313528706077679170)) ::
                Init_int64 (Int64.repr 8614303302290923471) ::
                Init_int64 (Int64.repr 3502774576018228727) ::
                Init_int64 (Int64.repr (-8223330671321994419)) ::
                Init_int64 (Int64.repr (-509974645718671777)) ::
                Init_int64 (Int64.repr (-1578286006032369884)) ::
                Init_int64 (Int64.repr (-6136975533329187962)) ::
                Init_int64 (Int64.repr (-7383254276185267892)) ::
                Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr (-1038424741147024148)) ::
                Init_int64 (Int64.repr 8147411679330008245) ::
                Init_int64 (Int64.repr (-5798244579743184959)) ::
                Init_int64 (Int64.repr (-7553031286637048475)) ::
                Init_int64 (Int64.repr 1805596730032847125) ::
                Init_int64 (Int64.repr (-7660920206580209736)) ::
                Init_int64 (Int64.repr (-2586795573306895959)) ::
                Init_int64 (Int64.repr (-7715201649543622056)) ::
                Init_int64 (Int64.repr (-9185181658886629287)) ::
                Init_int64 (Int64.repr (-4298695902449181348)) ::
                Init_int64 (Int64.repr (-401669858455882622)) ::
                Init_int64 (Int64.repr (-984352323850208303)) ::
                Init_int64 (Int64.repr 7682965931774537597) ::
                Init_int64 (Int64.repr 5596472239608840118) ::
                Init_int64 (Int64.repr 270258815560556349) ::
                Init_int64 (Int64.repr (-2406869955685926028)) ::
                Init_int64 (Int64.repr 3049702990379705311) ::
                Init_int64 (Int64.repr 8053010959342359354) ::
                Init_int64 (Int64.repr (-3160470844062310662)) ::
                Init_int64 (Int64.repr (-4908419681909338688)) ::
                Init_int64 (Int64.repr (-7606905927613335419)) ::
                Init_int64 (Int64.repr (-1488399621743639868)) ::
                Init_int64 (Int64.repr 386581700168432711) ::
                Init_int64 (Int64.repr (-6597137862831384657)) ::
                Init_int64 (Int64.repr (-2062015531745571433)) ::
                Init_int64 (Int64.repr (-9095225463651144263)) ::
                Init_int64 (Int64.repr (-5852262697859567071)) ::
                Init_int64 (Int64.repr (-930545735079915983)) ::
                Init_int64 (Int64.repr 7198320377835460046) ::
                Init_int64 (Int64.repr 5120731167067232824) ::
                Init_int64 (Int64.repr (-6651843357340761803)) ::
                Init_int64 (Int64.repr 8731195876909249510) ::
                Init_int64 (Int64.repr 90328536687932896) ::
                Init_int64 (Int64.repr 1365991463380576635) ::
                Init_int64 (Int64.repr 8434371908073207058) ::
                Init_int64 (Int64.repr (-2610822773904046285)) ::
                Init_int64 (Int64.repr 2221225747181776783) ::
                Init_int64 (Int64.repr 5924803646370735577) ::
                Init_int64 (Int64.repr (-2151921690007111561)) ::
                Init_int64 (Int64.repr (-112176346332349147)) ::
                Init_int64 (Int64.repr (-3823378446842105483)) ::
                Init_int64 (Int64.repr 7018118503369309971) ::
                Init_int64 (Int64.repr (-1765485143161682896)) ::
                Init_int64 (Int64.repr 3229068021579661477) ::
                Init_int64 (Int64.repr 1650985629915947228) ::
                Init_int64 (Int64.repr (-6316902234628255397)) ::
                Init_int64 (Int64.repr 2095097388851998898) ::
                Init_int64 (Int64.repr (-5204381343701972172)) ::
                Init_int64 (Int64.repr (-3441238494334806179)) ::
                Init_int64 (Int64.repr (-166247528511102440)) ::
                Init_int64 (Int64.repr 6297241211743328670) ::
                Init_int64 (Int64.repr 566791255125546650) ::
                Init_int64 (Int64.repr 6099120129211025059) ::
                Init_int64 (Int64.repr 6207265234025196670) ::
                Init_int64 (Int64.repr (-4702707661790596729)) ::
                Init_int64 (Int64.repr 9022666302357912129) ::
                Init_int64 (Int64.repr 4280222554823792025) ::
                Init_int64 (Int64.repr 7592864715621986368) ::
                Init_int64 (Int64.repr (-5978334025940980452)) ::
                Init_int64 (Int64.repr (-5666902402852558770)) ::
                Init_int64 (Int64.repr 4958563418731169029) ::
                Init_int64 (Int64.repr 1524851495198900193) ::
                Init_int64 (Int64.repr 8380074945713127666) ::
                Init_int64 (Int64.repr 6468045177866483127) ::
                Init_int64 (Int64.repr (-1205373434963637405)) ::
                Init_int64 (Int64.repr 7773082786155731613) ::
                Init_int64 (Int64.repr 4466211058774718179) ::
                Init_int64 (Int64.repr (-6706124934991252267)) ::
                Init_int64 (Int64.repr 1751387863358606581) ::
                Init_int64 (Int64.repr 1239861033085204038) ::
                Init_int64 (Int64.repr (-4998675501978519520)) ::
                Init_int64 (Int64.repr (-3351053600823745859)) ::
                Init_int64 (Int64.repr (-5756736010516488786)) ::
                Init_int64 (Int64.repr (-8891743236443811330)) ::
                Init_int64 (Int64.repr 8093393569995819349) ::
                Init_int64 (Int64.repr 1055908661886561321) ::
                Init_int64 (Int64.repr 296537535556471207) ::
                Init_int64 (Int64.repr 773163400336795022) ::
                Init_int64 (Int64.repr 5311761053276829201) ::
                Init_int64 (Int64.repr (-8485492023568532009)) ::
                Init_int64 (Int64.repr (-3662266335131785233)) ::
                Init_int64 (Int64.repr (-3949507912179585464)) ::
                Init_int64 (Int64.repr (-7893873303052160734)) ::
                Init_int64 (Int64.repr (-4064551234840739231)) ::
                Init_int64 (Int64.repr (-2169907731705796790)) ::
                Init_int64 (Int64.repr (-3261014646945153664)) ::
                Init_int64 (Int64.repr (-7329239303795474831)) ::
                Init_int64 (Int64.repr (-5486560906633510253)) ::
                Init_int64 (Int64.repr 8273478878667924360) ::
                Init_int64 (Int64.repr (-2980521874450729945)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_streebog_xor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_y, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_z, (tptr (Tstruct _streebog_uint512 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'16, tulong) :: (_t'15, tulong) :: (_t'14, tulong) ::
               (_t'13, tulong) :: (_t'12, tulong) :: (_t'11, tulong) ::
               (_t'10, tulong) :: (_t'9, tulong) :: (_t'8, tulong) ::
               (_t'7, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'15
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
              (Tstruct _streebog_uint512 noattr)) _qword (tarray tulong 8))
          (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong))
    (Ssequence
      (Sset _t'16
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                (Tstruct _streebog_uint512 noattr)) _qword (tarray tulong 8))
            (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong))
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _z (tptr (Tstruct _streebog_uint512 noattr)))
                (Tstruct _streebog_uint512 noattr)) _qword (tarray tulong 8))
            (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong)
        (Ebinop Oxor (Etempvar _t'15 tulong) (Etempvar _t'16 tulong) tulong))))
  (Ssequence
    (Ssequence
      (Sset _t'13
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                (Tstruct _streebog_uint512 noattr)) _qword (tarray tulong 8))
            (Econst_int (Int.repr 1) tint) (tptr tulong)) tulong))
      (Ssequence
        (Sset _t'14
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                  (Tstruct _streebog_uint512 noattr)) _qword
                (tarray tulong 8)) (Econst_int (Int.repr 1) tint)
              (tptr tulong)) tulong))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _z (tptr (Tstruct _streebog_uint512 noattr)))
                  (Tstruct _streebog_uint512 noattr)) _qword
                (tarray tulong 8)) (Econst_int (Int.repr 1) tint)
              (tptr tulong)) tulong)
          (Ebinop Oxor (Etempvar _t'13 tulong) (Etempvar _t'14 tulong)
            tulong))))
    (Ssequence
      (Ssequence
        (Sset _t'11
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                  (Tstruct _streebog_uint512 noattr)) _qword
                (tarray tulong 8)) (Econst_int (Int.repr 2) tint)
              (tptr tulong)) tulong))
        (Ssequence
          (Sset _t'12
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                    (Tstruct _streebog_uint512 noattr)) _qword
                  (tarray tulong 8)) (Econst_int (Int.repr 2) tint)
                (tptr tulong)) tulong))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _z (tptr (Tstruct _streebog_uint512 noattr)))
                    (Tstruct _streebog_uint512 noattr)) _qword
                  (tarray tulong 8)) (Econst_int (Int.repr 2) tint)
                (tptr tulong)) tulong)
            (Ebinop Oxor (Etempvar _t'11 tulong) (Etempvar _t'12 tulong)
              tulong))))
      (Ssequence
        (Ssequence
          (Sset _t'9
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                    (Tstruct _streebog_uint512 noattr)) _qword
                  (tarray tulong 8)) (Econst_int (Int.repr 3) tint)
                (tptr tulong)) tulong))
          (Ssequence
            (Sset _t'10
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                      (Tstruct _streebog_uint512 noattr)) _qword
                    (tarray tulong 8)) (Econst_int (Int.repr 3) tint)
                  (tptr tulong)) tulong))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _z (tptr (Tstruct _streebog_uint512 noattr)))
                      (Tstruct _streebog_uint512 noattr)) _qword
                    (tarray tulong 8)) (Econst_int (Int.repr 3) tint)
                  (tptr tulong)) tulong)
              (Ebinop Oxor (Etempvar _t'9 tulong) (Etempvar _t'10 tulong)
                tulong))))
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                      (Tstruct _streebog_uint512 noattr)) _qword
                    (tarray tulong 8)) (Econst_int (Int.repr 4) tint)
                  (tptr tulong)) tulong))
            (Ssequence
              (Sset _t'8
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                        (Tstruct _streebog_uint512 noattr)) _qword
                      (tarray tulong 8)) (Econst_int (Int.repr 4) tint)
                    (tptr tulong)) tulong))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _z (tptr (Tstruct _streebog_uint512 noattr)))
                        (Tstruct _streebog_uint512 noattr)) _qword
                      (tarray tulong 8)) (Econst_int (Int.repr 4) tint)
                    (tptr tulong)) tulong)
                (Ebinop Oxor (Etempvar _t'7 tulong) (Etempvar _t'8 tulong)
                  tulong))))
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                        (Tstruct _streebog_uint512 noattr)) _qword
                      (tarray tulong 8)) (Econst_int (Int.repr 5) tint)
                    (tptr tulong)) tulong))
              (Ssequence
                (Sset _t'6
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                          (Tstruct _streebog_uint512 noattr)) _qword
                        (tarray tulong 8)) (Econst_int (Int.repr 5) tint)
                      (tptr tulong)) tulong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _z (tptr (Tstruct _streebog_uint512 noattr)))
                          (Tstruct _streebog_uint512 noattr)) _qword
                        (tarray tulong 8)) (Econst_int (Int.repr 5) tint)
                      (tptr tulong)) tulong)
                  (Ebinop Oxor (Etempvar _t'5 tulong) (Etempvar _t'6 tulong)
                    tulong))))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                          (Tstruct _streebog_uint512 noattr)) _qword
                        (tarray tulong 8)) (Econst_int (Int.repr 6) tint)
                      (tptr tulong)) tulong))
                (Ssequence
                  (Sset _t'4
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                            (Tstruct _streebog_uint512 noattr)) _qword
                          (tarray tulong 8)) (Econst_int (Int.repr 6) tint)
                        (tptr tulong)) tulong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _z (tptr (Tstruct _streebog_uint512 noattr)))
                            (Tstruct _streebog_uint512 noattr)) _qword
                          (tarray tulong 8)) (Econst_int (Int.repr 6) tint)
                        (tptr tulong)) tulong)
                    (Ebinop Oxor (Etempvar _t'3 tulong)
                      (Etempvar _t'4 tulong) tulong))))
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                          (Tstruct _streebog_uint512 noattr)) _qword
                        (tarray tulong 8)) (Econst_int (Int.repr 7) tint)
                      (tptr tulong)) tulong))
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                            (Tstruct _streebog_uint512 noattr)) _qword
                          (tarray tulong 8)) (Econst_int (Int.repr 7) tint)
                        (tptr tulong)) tulong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _z (tptr (Tstruct _streebog_uint512 noattr)))
                            (Tstruct _streebog_uint512 noattr)) _qword
                          (tarray tulong 8)) (Econst_int (Int.repr 7) tint)
                        (tptr tulong)) tulong)
                    (Ebinop Oxor (Etempvar _t'1 tulong)
                      (Etempvar _t'2 tulong) tulong)))))))))))
|}.

Definition f_streebog_xlps := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_y, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_data, (tptr (Tstruct _streebog_uint512 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r0, tulong) :: (_r1, tulong) :: (_r2, tulong) ::
               (_r3, tulong) :: (_r4, tulong) :: (_r5, tulong) ::
               (_r6, tulong) :: (_r7, tulong) :: (_i, tint) ::
               (_t'31, tulong) :: (_t'30, tulong) :: (_t'29, tulong) ::
               (_t'28, tulong) :: (_t'27, tulong) :: (_t'26, tulong) ::
               (_t'25, tulong) :: (_t'24, tulong) :: (_t'23, tulong) ::
               (_t'22, tulong) :: (_t'21, tulong) :: (_t'20, tulong) ::
               (_t'19, tulong) :: (_t'18, tulong) :: (_t'17, tulong) ::
               (_t'16, tulong) :: (_t'15, tulong) :: (_t'14, tulong) ::
               (_t'13, tulong) :: (_t'12, tulong) :: (_t'11, tulong) ::
               (_t'10, tulong) :: (_t'9, tulong) :: (_t'8, tulong) ::
               (_t'7, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'30
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
              (Tstruct _streebog_uint512 noattr)) _qword (tarray tulong 8))
          (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong))
    (Ssequence
      (Sset _t'31
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                (Tstruct _streebog_uint512 noattr)) _qword (tarray tulong 8))
            (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong))
      (Sset _r0
        (Ebinop Oxor (Etempvar _t'30 tulong) (Etempvar _t'31 tulong) tulong))))
  (Ssequence
    (Ssequence
      (Sset _t'28
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                (Tstruct _streebog_uint512 noattr)) _qword (tarray tulong 8))
            (Econst_int (Int.repr 1) tint) (tptr tulong)) tulong))
      (Ssequence
        (Sset _t'29
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                  (Tstruct _streebog_uint512 noattr)) _qword
                (tarray tulong 8)) (Econst_int (Int.repr 1) tint)
              (tptr tulong)) tulong))
        (Sset _r1
          (Ebinop Oxor (Etempvar _t'28 tulong) (Etempvar _t'29 tulong)
            tulong))))
    (Ssequence
      (Ssequence
        (Sset _t'26
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                  (Tstruct _streebog_uint512 noattr)) _qword
                (tarray tulong 8)) (Econst_int (Int.repr 2) tint)
              (tptr tulong)) tulong))
        (Ssequence
          (Sset _t'27
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                    (Tstruct _streebog_uint512 noattr)) _qword
                  (tarray tulong 8)) (Econst_int (Int.repr 2) tint)
                (tptr tulong)) tulong))
          (Sset _r2
            (Ebinop Oxor (Etempvar _t'26 tulong) (Etempvar _t'27 tulong)
              tulong))))
      (Ssequence
        (Ssequence
          (Sset _t'24
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                    (Tstruct _streebog_uint512 noattr)) _qword
                  (tarray tulong 8)) (Econst_int (Int.repr 3) tint)
                (tptr tulong)) tulong))
          (Ssequence
            (Sset _t'25
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                      (Tstruct _streebog_uint512 noattr)) _qword
                    (tarray tulong 8)) (Econst_int (Int.repr 3) tint)
                  (tptr tulong)) tulong))
            (Sset _r3
              (Ebinop Oxor (Etempvar _t'24 tulong) (Etempvar _t'25 tulong)
                tulong))))
        (Ssequence
          (Ssequence
            (Sset _t'22
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                      (Tstruct _streebog_uint512 noattr)) _qword
                    (tarray tulong 8)) (Econst_int (Int.repr 4) tint)
                  (tptr tulong)) tulong))
            (Ssequence
              (Sset _t'23
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                        (Tstruct _streebog_uint512 noattr)) _qword
                      (tarray tulong 8)) (Econst_int (Int.repr 4) tint)
                    (tptr tulong)) tulong))
              (Sset _r4
                (Ebinop Oxor (Etempvar _t'22 tulong) (Etempvar _t'23 tulong)
                  tulong))))
          (Ssequence
            (Ssequence
              (Sset _t'20
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                        (Tstruct _streebog_uint512 noattr)) _qword
                      (tarray tulong 8)) (Econst_int (Int.repr 5) tint)
                    (tptr tulong)) tulong))
              (Ssequence
                (Sset _t'21
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                          (Tstruct _streebog_uint512 noattr)) _qword
                        (tarray tulong 8)) (Econst_int (Int.repr 5) tint)
                      (tptr tulong)) tulong))
                (Sset _r5
                  (Ebinop Oxor (Etempvar _t'20 tulong)
                    (Etempvar _t'21 tulong) tulong))))
            (Ssequence
              (Ssequence
                (Sset _t'18
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                          (Tstruct _streebog_uint512 noattr)) _qword
                        (tarray tulong 8)) (Econst_int (Int.repr 6) tint)
                      (tptr tulong)) tulong))
                (Ssequence
                  (Sset _t'19
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                            (Tstruct _streebog_uint512 noattr)) _qword
                          (tarray tulong 8)) (Econst_int (Int.repr 6) tint)
                        (tptr tulong)) tulong))
                  (Sset _r6
                    (Ebinop Oxor (Etempvar _t'18 tulong)
                      (Etempvar _t'19 tulong) tulong))))
              (Ssequence
                (Ssequence
                  (Sset _t'16
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                            (Tstruct _streebog_uint512 noattr)) _qword
                          (tarray tulong 8)) (Econst_int (Int.repr 7) tint)
                        (tptr tulong)) tulong))
                  (Ssequence
                    (Sset _t'17
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                              (Tstruct _streebog_uint512 noattr)) _qword
                            (tarray tulong 8)) (Econst_int (Int.repr 7) tint)
                          (tptr tulong)) tulong))
                    (Sset _r7
                      (Ebinop Oxor (Etempvar _t'16 tulong)
                        (Etempvar _t'17 tulong) tulong))))
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _i tint)
                                     (Econst_int (Int.repr 7) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Sset _t'15
                            (Ederef
                              (Ebinop Oadd
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _Ax (tarray (tarray tulong 256) 8))
                                    (Econst_int (Int.repr 0) tint)
                                    (tptr (tarray tulong 256)))
                                  (tarray tulong 256))
                                (Ebinop Oand (Etempvar _r0 tulong)
                                  (Econst_int (Int.repr 255) tint) tulong)
                                (tptr tulong)) tulong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                    (Tstruct _streebog_uint512 noattr))
                                  _qword (tarray tulong 8))
                                (Etempvar _i tint) (tptr tulong)) tulong)
                            (Etempvar _t'15 tulong)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'13
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                      (Tstruct _streebog_uint512 noattr))
                                    _qword (tarray tulong 8))
                                  (Etempvar _i tint) (tptr tulong)) tulong))
                            (Ssequence
                              (Sset _t'14
                                (Ederef
                                  (Ebinop Oadd
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _Ax (tarray (tarray tulong 256) 8))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr (tarray tulong 256)))
                                      (tarray tulong 256))
                                    (Ebinop Oand (Etempvar _r1 tulong)
                                      (Econst_int (Int.repr 255) tint)
                                      tulong) (tptr tulong)) tulong))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                        (Tstruct _streebog_uint512 noattr))
                                      _qword (tarray tulong 8))
                                    (Etempvar _i tint) (tptr tulong)) tulong)
                                (Ebinop Oxor (Etempvar _t'13 tulong)
                                  (Etempvar _t'14 tulong) tulong))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'11
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                        (Tstruct _streebog_uint512 noattr))
                                      _qword (tarray tulong 8))
                                    (Etempvar _i tint) (tptr tulong)) tulong))
                              (Ssequence
                                (Sset _t'12
                                  (Ederef
                                    (Ebinop Oadd
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _Ax (tarray (tarray tulong 256) 8))
                                          (Econst_int (Int.repr 2) tint)
                                          (tptr (tarray tulong 256)))
                                        (tarray tulong 256))
                                      (Ebinop Oand (Etempvar _r2 tulong)
                                        (Econst_int (Int.repr 255) tint)
                                        tulong) (tptr tulong)) tulong))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                          (Tstruct _streebog_uint512 noattr))
                                        _qword (tarray tulong 8))
                                      (Etempvar _i tint) (tptr tulong))
                                    tulong)
                                  (Ebinop Oxor (Etempvar _t'11 tulong)
                                    (Etempvar _t'12 tulong) tulong))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'9
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                          (Tstruct _streebog_uint512 noattr))
                                        _qword (tarray tulong 8))
                                      (Etempvar _i tint) (tptr tulong))
                                    tulong))
                                (Ssequence
                                  (Sset _t'10
                                    (Ederef
                                      (Ebinop Oadd
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _Ax (tarray (tarray tulong 256) 8))
                                            (Econst_int (Int.repr 3) tint)
                                            (tptr (tarray tulong 256)))
                                          (tarray tulong 256))
                                        (Ebinop Oand (Etempvar _r3 tulong)
                                          (Econst_int (Int.repr 255) tint)
                                          tulong) (tptr tulong)) tulong))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                            (Tstruct _streebog_uint512 noattr))
                                          _qword (tarray tulong 8))
                                        (Etempvar _i tint) (tptr tulong))
                                      tulong)
                                    (Ebinop Oxor (Etempvar _t'9 tulong)
                                      (Etempvar _t'10 tulong) tulong))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'7
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                            (Tstruct _streebog_uint512 noattr))
                                          _qword (tarray tulong 8))
                                        (Etempvar _i tint) (tptr tulong))
                                      tulong))
                                  (Ssequence
                                    (Sset _t'8
                                      (Ederef
                                        (Ebinop Oadd
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _Ax (tarray (tarray tulong 256) 8))
                                              (Econst_int (Int.repr 4) tint)
                                              (tptr (tarray tulong 256)))
                                            (tarray tulong 256))
                                          (Ebinop Oand (Etempvar _r4 tulong)
                                            (Econst_int (Int.repr 255) tint)
                                            tulong) (tptr tulong)) tulong))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                              (Tstruct _streebog_uint512 noattr))
                                            _qword (tarray tulong 8))
                                          (Etempvar _i tint) (tptr tulong))
                                        tulong)
                                      (Ebinop Oxor (Etempvar _t'7 tulong)
                                        (Etempvar _t'8 tulong) tulong))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'5
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                              (Tstruct _streebog_uint512 noattr))
                                            _qword (tarray tulong 8))
                                          (Etempvar _i tint) (tptr tulong))
                                        tulong))
                                    (Ssequence
                                      (Sset _t'6
                                        (Ederef
                                          (Ebinop Oadd
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _Ax (tarray (tarray tulong 256) 8))
                                                (Econst_int (Int.repr 5) tint)
                                                (tptr (tarray tulong 256)))
                                              (tarray tulong 256))
                                            (Ebinop Oand
                                              (Etempvar _r5 tulong)
                                              (Econst_int (Int.repr 255) tint)
                                              tulong) (tptr tulong)) tulong))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                                (Tstruct _streebog_uint512 noattr))
                                              _qword (tarray tulong 8))
                                            (Etempvar _i tint) (tptr tulong))
                                          tulong)
                                        (Ebinop Oxor (Etempvar _t'5 tulong)
                                          (Etempvar _t'6 tulong) tulong))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'3
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                                (Tstruct _streebog_uint512 noattr))
                                              _qword (tarray tulong 8))
                                            (Etempvar _i tint) (tptr tulong))
                                          tulong))
                                      (Ssequence
                                        (Sset _t'4
                                          (Ederef
                                            (Ebinop Oadd
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _Ax (tarray (tarray tulong 256) 8))
                                                  (Econst_int (Int.repr 6) tint)
                                                  (tptr (tarray tulong 256)))
                                                (tarray tulong 256))
                                              (Ebinop Oand
                                                (Etempvar _r6 tulong)
                                                (Econst_int (Int.repr 255) tint)
                                                tulong) (tptr tulong))
                                            tulong))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                                  (Tstruct _streebog_uint512 noattr))
                                                _qword (tarray tulong 8))
                                              (Etempvar _i tint)
                                              (tptr tulong)) tulong)
                                          (Ebinop Oxor (Etempvar _t'3 tulong)
                                            (Etempvar _t'4 tulong) tulong))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'1
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                                  (Tstruct _streebog_uint512 noattr))
                                                _qword (tarray tulong 8))
                                              (Etempvar _i tint)
                                              (tptr tulong)) tulong))
                                        (Ssequence
                                          (Sset _t'2
                                            (Ederef
                                              (Ebinop Oadd
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _Ax (tarray (tarray tulong 256) 8))
                                                    (Econst_int (Int.repr 7) tint)
                                                    (tptr (tarray tulong 256)))
                                                  (tarray tulong 256))
                                                (Ebinop Oand
                                                  (Etempvar _r7 tulong)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tulong) (tptr tulong))
                                              tulong))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr)))
                                                    (Tstruct _streebog_uint512 noattr))
                                                  _qword (tarray tulong 8))
                                                (Etempvar _i tint)
                                                (tptr tulong)) tulong)
                                            (Ebinop Oxor
                                              (Etempvar _t'1 tulong)
                                              (Etempvar _t'2 tulong) tulong))))
                                      (Ssequence
                                        (Sset _r0
                                          (Ebinop Oshr (Etempvar _r0 tulong)
                                            (Econst_int (Int.repr 8) tint)
                                            tulong))
                                        (Ssequence
                                          (Sset _r1
                                            (Ebinop Oshr
                                              (Etempvar _r1 tulong)
                                              (Econst_int (Int.repr 8) tint)
                                              tulong))
                                          (Ssequence
                                            (Sset _r2
                                              (Ebinop Oshr
                                                (Etempvar _r2 tulong)
                                                (Econst_int (Int.repr 8) tint)
                                                tulong))
                                            (Ssequence
                                              (Sset _r3
                                                (Ebinop Oshr
                                                  (Etempvar _r3 tulong)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tulong))
                                              (Ssequence
                                                (Sset _r4
                                                  (Ebinop Oshr
                                                    (Etempvar _r4 tulong)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tulong))
                                                (Ssequence
                                                  (Sset _r5
                                                    (Ebinop Oshr
                                                      (Etempvar _r5 tulong)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tulong))
                                                  (Ssequence
                                                    (Sset _r6
                                                      (Ebinop Oshr
                                                        (Etempvar _r6 tulong)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tulong))
                                                    (Sset _r7
                                                      (Ebinop Oshr
                                                        (Etempvar _r7 tulong)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tulong))))))))))))))))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint))))))))))))
|}.

Definition f_streebog_round := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) ::
                (_Ki, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_data, (tptr (Tstruct _streebog_uint512 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _streebog_xlps (Tfunction
                           ((tptr (Tstruct _streebog_uint512 noattr)) ::
                            (tptr (Tstruct _streebog_uint512 noattr)) ::
                            (tptr (Tstruct _streebog_uint512 noattr)) :: nil)
                           tvoid cc_default))
    ((Etempvar _Ki (tptr (Tstruct _streebog_uint512 noattr))) ::
     (Ebinop Oadd (Evar _C (tarray (Tstruct _streebog_uint512 noattr) 12))
       (Etempvar _i tint) (tptr (Tstruct _streebog_uint512 noattr))) ::
     (Etempvar _Ki (tptr (Tstruct _streebog_uint512 noattr))) :: nil))
  (Scall None
    (Evar _streebog_xlps (Tfunction
                           ((tptr (Tstruct _streebog_uint512 noattr)) ::
                            (tptr (Tstruct _streebog_uint512 noattr)) ::
                            (tptr (Tstruct _streebog_uint512 noattr)) :: nil)
                           tvoid cc_default))
    ((Etempvar _Ki (tptr (Tstruct _streebog_uint512 noattr))) ::
     (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr))) ::
     (Etempvar _data (tptr (Tstruct _streebog_uint512 noattr))) :: nil)))
|}.

Definition f_streebog_init := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_desc, (tptr (Tstruct _shash_desc noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ctx, (tptr (Tstruct _streebog_state noattr))) ::
               (_digest_size, tuint) :: (_i, tuint) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct _crypto_shash noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _shash_desc_ctx (Tfunction
                              ((tptr (Tstruct _shash_desc noattr)) :: nil)
                              (tptr tvoid) cc_default))
      ((Etempvar _desc (tptr (Tstruct _shash_desc noattr))) :: nil))
    (Sset _ctx (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _desc (tptr (Tstruct _shash_desc noattr)))
              (Tstruct _shash_desc noattr)) _tfm
            (tptr (Tstruct _crypto_shash noattr))))
        (Scall (Some _t'2)
          (Evar _crypto_shash_digestsize (Tfunction nil tint
                                           {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
          ((Etempvar _t'3 (tptr (Tstruct _crypto_shash noattr))) :: nil)))
      (Sset _digest_size (Etempvar _t'2 tint)))
    (Ssequence
      (Scall None
        (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                        (tptr tvoid) cc_default))
        ((Etempvar _ctx (tptr (Tstruct _streebog_state noattr))) ::
         (Econst_int (Int.repr 0) tint) ::
         (Esizeof (Tstruct _streebog_state noattr) tulong) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Econst_int (Int.repr 8) tint) tint)
                Sskip
                Sbreak)
              (Sifthenelse (Ebinop Oeq (Etempvar _digest_size tuint)
                             (Econst_int (Int.repr 32) tint) tint)
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                            (Tstruct _streebog_state noattr)) _h
                          (Tstruct _streebog_uint512 noattr)) _qword
                        (tarray tulong 8)) (Etempvar _i tuint) (tptr tulong))
                    tulong)
                  (Econst_long (Int64.repr 72340172838076673) tulong))
                Sskip))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_streebog_add512 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_y, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_r, (tptr (Tstruct _streebog_uint512 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_carry, tulong) :: (_i, tint) :: (_left, tulong) ::
               (_sum, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _carry (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 8) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _left
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _x (tptr (Tstruct _streebog_uint512 noattr)))
                    (Tstruct _streebog_uint512 noattr)) _qword
                  (tarray tulong 8)) (Etempvar _i tint) (tptr tulong))
              tulong))
          (Ssequence
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _y (tptr (Tstruct _streebog_uint512 noattr)))
                        (Tstruct _streebog_uint512 noattr)) _qword
                      (tarray tulong 8)) (Etempvar _i tint) (tptr tulong))
                  tulong))
              (Sset _sum
                (Ebinop Oadd
                  (Ebinop Oadd (Etempvar _left tulong) (Etempvar _t'1 tulong)
                    tulong) (Etempvar _carry tulong) tulong)))
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _sum tulong)
                             (Etempvar _left tulong) tint)
                (Sset _carry
                  (Ecast
                    (Ebinop Olt (Etempvar _sum tulong)
                      (Etempvar _left tulong) tint) tulong))
                Sskip)
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _r (tptr (Tstruct _streebog_uint512 noattr)))
                        (Tstruct _streebog_uint512 noattr)) _qword
                      (tarray tulong 8)) (Etempvar _i tint) (tptr tulong))
                  tulong) (Etempvar _sum tulong))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_streebog_g := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_N, (tptr (Tstruct _streebog_uint512 noattr))) ::
                (_m, (tptr (Tstruct _streebog_uint512 noattr))) :: nil);
  fn_vars := ((_Ki, (Tstruct _streebog_uint512 noattr)) ::
              (_data, (Tstruct _streebog_uint512 noattr)) :: nil);
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _streebog_xlps (Tfunction
                           ((tptr (Tstruct _streebog_uint512 noattr)) ::
                            (tptr (Tstruct _streebog_uint512 noattr)) ::
                            (tptr (Tstruct _streebog_uint512 noattr)) :: nil)
                           tvoid cc_default))
    ((Etempvar _h (tptr (Tstruct _streebog_uint512 noattr))) ::
     (Etempvar _N (tptr (Tstruct _streebog_uint512 noattr))) ::
     (Eaddrof (Evar _data (Tstruct _streebog_uint512 noattr))
       (tptr (Tstruct _streebog_uint512 noattr))) :: nil))
  (Ssequence
    (Sassign (Evar _Ki (Tstruct _streebog_uint512 noattr))
      (Evar _data (Tstruct _streebog_uint512 noattr)))
    (Ssequence
      (Scall None
        (Evar _streebog_xlps (Tfunction
                               ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                (tptr (Tstruct _streebog_uint512 noattr)) ::
                                (tptr (Tstruct _streebog_uint512 noattr)) ::
                                nil) tvoid cc_default))
        ((Eaddrof (Evar _Ki (Tstruct _streebog_uint512 noattr))
           (tptr (Tstruct _streebog_uint512 noattr))) ::
         (Etempvar _m (tptr (Tstruct _streebog_uint512 noattr))) ::
         (Eaddrof (Evar _data (Tstruct _streebog_uint512 noattr))
           (tptr (Tstruct _streebog_uint512 noattr))) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Econst_int (Int.repr 11) tint) tint)
                Sskip
                Sbreak)
              (Scall None
                (Evar _streebog_round (Tfunction
                                        (tint ::
                                         (tptr (Tstruct _streebog_uint512 noattr)) ::
                                         (tptr (Tstruct _streebog_uint512 noattr)) ::
                                         nil) tvoid cc_default))
                ((Etempvar _i tuint) ::
                 (Eaddrof (Evar _Ki (Tstruct _streebog_uint512 noattr))
                   (tptr (Tstruct _streebog_uint512 noattr))) ::
                 (Eaddrof (Evar _data (Tstruct _streebog_uint512 noattr))
                   (tptr (Tstruct _streebog_uint512 noattr))) :: nil)))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Ssequence
          (Scall None
            (Evar _streebog_xlps (Tfunction
                                   ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                    nil) tvoid cc_default))
            ((Eaddrof (Evar _Ki (Tstruct _streebog_uint512 noattr))
               (tptr (Tstruct _streebog_uint512 noattr))) ::
             (Ebinop Oadd
               (Evar _C (tarray (Tstruct _streebog_uint512 noattr) 12))
               (Econst_int (Int.repr 11) tint)
               (tptr (Tstruct _streebog_uint512 noattr))) ::
             (Eaddrof (Evar _Ki (Tstruct _streebog_uint512 noattr))
               (tptr (Tstruct _streebog_uint512 noattr))) :: nil))
          (Ssequence
            (Scall None
              (Evar _streebog_xor (Tfunction
                                    ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                     (tptr (Tstruct _streebog_uint512 noattr)) ::
                                     (tptr (Tstruct _streebog_uint512 noattr)) ::
                                     nil) tvoid cc_default))
              ((Eaddrof (Evar _Ki (Tstruct _streebog_uint512 noattr))
                 (tptr (Tstruct _streebog_uint512 noattr))) ::
               (Eaddrof (Evar _data (Tstruct _streebog_uint512 noattr))
                 (tptr (Tstruct _streebog_uint512 noattr))) ::
               (Eaddrof (Evar _data (Tstruct _streebog_uint512 noattr))
                 (tptr (Tstruct _streebog_uint512 noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _streebog_xor (Tfunction
                                      ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                       (tptr (Tstruct _streebog_uint512 noattr)) ::
                                       (tptr (Tstruct _streebog_uint512 noattr)) ::
                                       nil) tvoid cc_default))
                ((Eaddrof (Evar _data (Tstruct _streebog_uint512 noattr))
                   (tptr (Tstruct _streebog_uint512 noattr))) ::
                 (Etempvar _h (tptr (Tstruct _streebog_uint512 noattr))) ::
                 (Eaddrof (Evar _data (Tstruct _streebog_uint512 noattr))
                   (tptr (Tstruct _streebog_uint512 noattr))) :: nil))
              (Scall None
                (Evar _streebog_xor (Tfunction
                                      ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                       (tptr (Tstruct _streebog_uint512 noattr)) ::
                                       (tptr (Tstruct _streebog_uint512 noattr)) ::
                                       nil) tvoid cc_default))
                ((Eaddrof (Evar _data (Tstruct _streebog_uint512 noattr))
                   (tptr (Tstruct _streebog_uint512 noattr))) ::
                 (Etempvar _m (tptr (Tstruct _streebog_uint512 noattr))) ::
                 (Etempvar _h (tptr (Tstruct _streebog_uint512 noattr))) ::
                 nil)))))))))
|}.

Definition f_streebog_stage2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _streebog_state noattr))) ::
                (_data, (tptr tuchar)) :: nil);
  fn_vars := ((_m, (Tstruct _streebog_uint512 noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _memcpy (Tfunction ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                    (tptr tvoid) cc_default))
    ((Eaddrof (Evar _m (Tstruct _streebog_uint512 noattr))
       (tptr (Tstruct _streebog_uint512 noattr))) ::
     (Etempvar _data (tptr tuchar)) ::
     (Esizeof (Tstruct _streebog_uint512 noattr) tulong) :: nil))
  (Ssequence
    (Scall None
      (Evar _streebog_g (Tfunction
                          ((tptr (Tstruct _streebog_uint512 noattr)) ::
                           (tptr (Tstruct _streebog_uint512 noattr)) ::
                           (tptr (Tstruct _streebog_uint512 noattr)) :: nil)
                          tvoid cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
             (Tstruct _streebog_state noattr)) _h
           (Tstruct _streebog_uint512 noattr))
         (tptr (Tstruct _streebog_uint512 noattr))) ::
       (Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
             (Tstruct _streebog_state noattr)) _N
           (Tstruct _streebog_uint512 noattr))
         (tptr (Tstruct _streebog_uint512 noattr))) ::
       (Eaddrof (Evar _m (Tstruct _streebog_uint512 noattr))
         (tptr (Tstruct _streebog_uint512 noattr))) :: nil))
    (Ssequence
      (Scall None
        (Evar _streebog_add512 (Tfunction
                                 ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                  (tptr (Tstruct _streebog_uint512 noattr)) ::
                                  (tptr (Tstruct _streebog_uint512 noattr)) ::
                                  nil) tvoid cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
               (Tstruct _streebog_state noattr)) _N
             (Tstruct _streebog_uint512 noattr))
           (tptr (Tstruct _streebog_uint512 noattr))) ::
         (Eaddrof (Evar _buffer512 (Tstruct _streebog_uint512 noattr))
           (tptr (Tstruct _streebog_uint512 noattr))) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
               (Tstruct _streebog_state noattr)) _N
             (Tstruct _streebog_uint512 noattr))
           (tptr (Tstruct _streebog_uint512 noattr))) :: nil))
      (Scall None
        (Evar _streebog_add512 (Tfunction
                                 ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                  (tptr (Tstruct _streebog_uint512 noattr)) ::
                                  (tptr (Tstruct _streebog_uint512 noattr)) ::
                                  nil) tvoid cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
               (Tstruct _streebog_state noattr)) _Sigma
             (Tstruct _streebog_uint512 noattr))
           (tptr (Tstruct _streebog_uint512 noattr))) ::
         (Eaddrof (Evar _m (Tstruct _streebog_uint512 noattr))
           (tptr (Tstruct _streebog_uint512 noattr))) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
               (Tstruct _streebog_state noattr)) _Sigma
             (Tstruct _streebog_uint512 noattr))
           (tptr (Tstruct _streebog_uint512 noattr))) :: nil)))))
|}.

Definition f_streebog_stage3 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _streebog_state noattr))) ::
                (_src, (tptr tuchar)) :: (_len, tuint) :: nil);
  fn_vars := ((_buf, (Tstruct _streebog_uint512 noattr)) ::
              (_u, (Tunion __179 noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield (Evar _buf (Tstruct _streebog_uint512 noattr)) _qword
          (tarray tulong 8)) (Econst_int (Int.repr 0) tint) (tptr tulong))
      tulong) (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield (Evar _buf (Tstruct _streebog_uint512 noattr)) _qword
            (tarray tulong 8)) (Econst_int (Int.repr 1) tint) (tptr tulong))
        tulong) (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield (Evar _buf (Tstruct _streebog_uint512 noattr)) _qword
              (tarray tulong 8)) (Econst_int (Int.repr 2) tint)
            (tptr tulong)) tulong) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield (Evar _buf (Tstruct _streebog_uint512 noattr)) _qword
                (tarray tulong 8)) (Econst_int (Int.repr 3) tint)
              (tptr tulong)) tulong) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield (Evar _buf (Tstruct _streebog_uint512 noattr)) _qword
                  (tarray tulong 8)) (Econst_int (Int.repr 4) tint)
                (tptr tulong)) tulong) (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield (Evar _buf (Tstruct _streebog_uint512 noattr))
                    _qword (tarray tulong 8)) (Econst_int (Int.repr 5) tint)
                  (tptr tulong)) tulong) (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield (Evar _buf (Tstruct _streebog_uint512 noattr))
                      _qword (tarray tulong 8))
                    (Econst_int (Int.repr 6) tint) (tptr tulong)) tulong)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield (Evar _buf (Tstruct _streebog_uint512 noattr))
                        _qword (tarray tulong 8))
                      (Econst_int (Int.repr 7) tint) (tptr tulong)) tulong)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield (Evar _u (Tunion __179 noattr)) _buffer
                          (tarray tuchar 64)) (Econst_int (Int.repr 0) tint)
                        (tptr tuchar)) tuchar)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield (Evar _u (Tunion __179 noattr)) _buffer
                            (tarray tuchar 64))
                          (Econst_int (Int.repr 1) tint) (tptr tuchar))
                        tuchar) (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield (Evar _u (Tunion __179 noattr)) _buffer
                              (tarray tuchar 64))
                            (Econst_int (Int.repr 2) tint) (tptr tuchar))
                          tuchar) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield (Evar _u (Tunion __179 noattr)) _buffer
                                (tarray tuchar 64))
                              (Econst_int (Int.repr 3) tint) (tptr tuchar))
                            tuchar) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield (Evar _u (Tunion __179 noattr))
                                  _buffer (tarray tuchar 64))
                                (Econst_int (Int.repr 4) tint) (tptr tuchar))
                              tuchar) (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Efield (Evar _u (Tunion __179 noattr))
                                    _buffer (tarray tuchar 64))
                                  (Econst_int (Int.repr 5) tint)
                                  (tptr tuchar)) tuchar)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield (Evar _u (Tunion __179 noattr))
                                      _buffer (tarray tuchar 64))
                                    (Econst_int (Int.repr 6) tint)
                                    (tptr tuchar)) tuchar)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield (Evar _u (Tunion __179 noattr))
                                        _buffer (tarray tuchar 64))
                                      (Econst_int (Int.repr 7) tint)
                                      (tptr tuchar)) tuchar)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Evar _u (Tunion __179 noattr))
                                          _buffer (tarray tuchar 64))
                                        (Econst_int (Int.repr 8) tint)
                                        (tptr tuchar)) tuchar)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Evar _u (Tunion __179 noattr))
                                            _buffer (tarray tuchar 64))
                                          (Econst_int (Int.repr 9) tint)
                                          (tptr tuchar)) tuchar)
                                      (Econst_int (Int.repr 0) tint))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Evar _u (Tunion __179 noattr))
                                              _buffer (tarray tuchar 64))
                                            (Econst_int (Int.repr 10) tint)
                                            (tptr tuchar)) tuchar)
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _u (Tunion __179 noattr))
                                                _buffer (tarray tuchar 64))
                                              (Econst_int (Int.repr 11) tint)
                                              (tptr tuchar)) tuchar)
                                          (Econst_int (Int.repr 0) tint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _u (Tunion __179 noattr))
                                                  _buffer (tarray tuchar 64))
                                                (Econst_int (Int.repr 12) tint)
                                                (tptr tuchar)) tuchar)
                                            (Econst_int (Int.repr 0) tint))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Evar _u (Tunion __179 noattr))
                                                    _buffer
                                                    (tarray tuchar 64))
                                                  (Econst_int (Int.repr 13) tint)
                                                  (tptr tuchar)) tuchar)
                                              (Econst_int (Int.repr 0) tint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Evar _u (Tunion __179 noattr))
                                                      _buffer
                                                      (tarray tuchar 64))
                                                    (Econst_int (Int.repr 14) tint)
                                                    (tptr tuchar)) tuchar)
                                                (Econst_int (Int.repr 0) tint))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _u (Tunion __179 noattr))
                                                        _buffer
                                                        (tarray tuchar 64))
                                                      (Econst_int (Int.repr 15) tint)
                                                      (tptr tuchar)) tuchar)
                                                  (Econst_int (Int.repr 0) tint))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Evar _u (Tunion __179 noattr))
                                                          _buffer
                                                          (tarray tuchar 64))
                                                        (Econst_int (Int.repr 16) tint)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Econst_int (Int.repr 0) tint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Evar _u (Tunion __179 noattr))
                                                            _buffer
                                                            (tarray tuchar 64))
                                                          (Econst_int (Int.repr 17) tint)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Econst_int (Int.repr 0) tint))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _u (Tunion __179 noattr))
                                                              _buffer
                                                              (tarray tuchar 64))
                                                            (Econst_int (Int.repr 18) tint)
                                                            (tptr tuchar))
                                                          tuchar)
                                                        (Econst_int (Int.repr 0) tint))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _u (Tunion __179 noattr))
                                                                _buffer
                                                                (tarray tuchar 64))
                                                              (Econst_int (Int.repr 19) tint)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Econst_int (Int.repr 0) tint))
                                                        (Ssequence
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _u (Tunion __179 noattr))
                                                                  _buffer
                                                                  (tarray tuchar 64))
                                                                (Econst_int (Int.repr 20) tint)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Ssequence
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                  (Econst_int (Int.repr 21) tint)
                                                                  (tptr tuchar))
                                                                tuchar)
                                                              (Econst_int (Int.repr 0) tint))
                                                            (Ssequence
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 22) tint)
                                                                    (tptr tuchar))
                                                                  tuchar)
                                                                (Econst_int (Int.repr 0) tint))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 23) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                  (Econst_int (Int.repr 0) tint))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 27) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 28) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 29) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 30) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 31) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 33) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 34) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 35) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 36) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 37) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 38) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 39) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 40) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 41) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 42) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 43) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 44) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 45) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 46) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 47) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 48) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 49) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 50) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 51) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 52) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 53) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 54) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 55) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 56) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 57) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 58) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 59) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 60) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 61) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 62) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 63) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _buf (Tstruct _streebog_uint512 noattr))
                                                                    _qword
                                                                    (tarray tulong 8))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tulong))
                                                                    tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64)) ::
                                                                    (Etempvar _src (tptr tuchar)) ::
                                                                    (Etempvar _len tuint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _buffer
                                                                    (tarray tuchar 64))
                                                                    (Etempvar _len tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _streebog_g 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _h
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _N
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _m
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _streebog_add512 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _N
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _buf (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _N
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _streebog_add512 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _Sigma
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    _m
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _Sigma
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _memzero_explicit 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _u (Tunion __179 noattr))
                                                                    (tptr (Tunion __179 noattr))) ::
                                                                    (Esizeof (Tunion __179 noattr) tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _streebog_g 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _h
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _buffer0 (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _N
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _streebog_g 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    (tptr (Tstruct _streebog_uint512 noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _h
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _buffer0 (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _Sigma
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _hash
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                                                                    (Tstruct _streebog_state noattr))
                                                                    _h
                                                                    (Tstruct _streebog_uint512 noattr))
                                                                    (tptr (Tstruct _streebog_uint512 noattr))) ::
                                                                    (Esizeof (Tstruct _streebog_uint512 noattr) tulong) ::
                                                                    nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_streebog_update := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_desc, (tptr (Tstruct _shash_desc noattr))) ::
                (_data, (tptr tuchar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ctx, (tptr (Tstruct _streebog_state noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _shash_desc_ctx (Tfunction
                              ((tptr (Tstruct _shash_desc noattr)) :: nil)
                              (tptr tvoid) cc_default))
      ((Etempvar _desc (tptr (Tstruct _shash_desc noattr))) :: nil))
    (Sset _ctx (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sloop
      (Ssequence
        (Scall None
          (Evar _streebog_stage2 (Tfunction
                                   ((tptr (Tstruct _streebog_state noattr)) ::
                                    (tptr tuchar) :: nil) tvoid cc_default))
          ((Etempvar _ctx (tptr (Tstruct _streebog_state noattr))) ::
           (Etempvar _data (tptr tuchar)) :: nil))
        (Ssequence
          (Sset _data
            (Ebinop Oadd (Etempvar _data (tptr tuchar))
              (Econst_int (Int.repr 64) tint) (tptr tuchar)))
          (Sset _len
            (Ebinop Osub (Etempvar _len tuint)
              (Econst_int (Int.repr 64) tint) tuint))))
      (Sifthenelse (Ebinop Oge (Etempvar _len tuint)
                     (Econst_int (Int.repr 64) tint) tint)
        Sskip
        Sbreak))
    (Sreturn (Some (Etempvar _len tuint)))))
|}.

Definition f_streebog_finup := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_desc, (tptr (Tstruct _shash_desc noattr))) ::
                (_src, (tptr tuchar)) :: (_len, tuint) ::
                (_digest, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ctx, (tptr (Tstruct _streebog_state noattr))) ::
               (_t'2, tint) :: (_t'1, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct _crypto_shash noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _shash_desc_ctx (Tfunction
                              ((tptr (Tstruct _shash_desc noattr)) :: nil)
                              (tptr tvoid) cc_default))
      ((Etempvar _desc (tptr (Tstruct _shash_desc noattr))) :: nil))
    (Sset _ctx (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Scall None
      (Evar _streebog_stage3 (Tfunction
                               ((tptr (Tstruct _streebog_state noattr)) ::
                                (tptr tuchar) :: tuint :: nil) tvoid
                               cc_default))
      ((Etempvar _ctx (tptr (Tstruct _streebog_state noattr))) ::
       (Etempvar _src (tptr tuchar)) :: (Etempvar _len tuint) :: nil))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _desc (tptr (Tstruct _shash_desc noattr)))
                (Tstruct _shash_desc noattr)) _tfm
              (tptr (Tstruct _crypto_shash noattr))))
          (Scall (Some _t'2)
            (Evar _crypto_shash_digestsize (Tfunction nil tint
                                             {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
            ((Etempvar _t'3 (tptr (Tstruct _crypto_shash noattr))) :: nil)))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                       (Econst_int (Int.repr 32) tint) tint)
          (Scall None
            (Evar _memcpy (Tfunction
                            ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                            (tptr tvoid) cc_default))
            ((Etempvar _digest (tptr tuchar)) ::
             (Ebinop Oadd
               (Efield
                 (Efield
                   (Ederef
                     (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                     (Tstruct _streebog_state noattr)) _hash
                   (Tstruct _streebog_uint512 noattr)) _qword
                 (tarray tulong 8)) (Econst_int (Int.repr 4) tint)
               (tptr tulong)) :: (Econst_int (Int.repr 32) tint) :: nil))
          (Scall None
            (Evar _memcpy (Tfunction
                            ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                            (tptr tvoid) cc_default))
            ((Etempvar _digest (tptr tuchar)) ::
             (Ebinop Oadd
               (Efield
                 (Efield
                   (Ederef
                     (Etempvar _ctx (tptr (Tstruct _streebog_state noattr)))
                     (Tstruct _streebog_state noattr)) _hash
                   (Tstruct _streebog_uint512 noattr)) _qword
                 (tarray tulong 8)) (Econst_int (Int.repr 0) tint)
               (tptr tulong)) :: (Econst_int (Int.repr 64) tint) :: nil))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition composites : list composite_definition :=
(Composite _shash_desc Struct
   (Member_plain _tfm (tptr (Tstruct _crypto_shash noattr)) ::
    Member_plain ___ctx (tarray (tptr tvoid) 0) :: nil)
   noattr ::
 Composite _streebog_uint512 Struct
   (Member_plain _qword (tarray tulong 8) :: nil)
   noattr ::
 Composite _streebog_state Struct
   (Member_plain _hash (Tstruct _streebog_uint512 noattr) ::
    Member_plain _h (Tstruct _streebog_uint512 noattr) ::
    Member_plain _N (Tstruct _streebog_uint512 noattr) ::
    Member_plain _Sigma (Tstruct _streebog_uint512 noattr) :: nil)
   noattr ::
 Composite __179 Union
   (Member_plain _buffer (tarray tuchar 64) ::
    Member_plain _m (Tstruct _streebog_uint512 noattr) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_shash_desc_ctx, Gfun(Internal f_shash_desc_ctx)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) (tptr tvoid)
     cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: tint :: tulong :: nil) (tptr tvoid) cc_default)) ::
 (_memzero_explicit,
   Gfun(External (EF_external "memzero_explicit"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tulong :: nil) tvoid
     cc_default)) :: (_buffer0, Gvar v_buffer0) ::
 (_buffer512, Gvar v_buffer512) :: (_C, Gvar v_C) :: (_Ax, Gvar v_Ax) ::
 (_streebog_xor, Gfun(Internal f_streebog_xor)) ::
 (_streebog_xlps, Gfun(Internal f_streebog_xlps)) ::
 (_streebog_round, Gfun(Internal f_streebog_round)) ::
 (_streebog_init, Gfun(Internal f_streebog_init)) ::
 (_streebog_add512, Gfun(Internal f_streebog_add512)) ::
 (_streebog_g, Gfun(Internal f_streebog_g)) ::
 (_streebog_stage2, Gfun(Internal f_streebog_stage2)) ::
 (_streebog_stage3, Gfun(Internal f_streebog_stage3)) ::
 (_streebog_update, Gfun(Internal f_streebog_update)) ::
 (_crypto_shash_digestsize,
   Gfun(External (EF_external "crypto_shash_digestsize"
                   (mksignature nil AST.Xint
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     nil tint {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_streebog_finup, Gfun(Internal f_streebog_finup)) :: nil).

Definition public_idents : list ident :=
(_streebog_finup :: _crypto_shash_digestsize :: _streebog_update ::
 _streebog_stage3 :: _streebog_stage2 :: _streebog_g :: _streebog_add512 ::
 _streebog_init :: _streebog_round :: _streebog_xlps :: _streebog_xor ::
 _Ax :: _C :: _buffer512 :: _buffer0 :: _memzero_explicit :: _memset ::
 _memcpy :: _shash_desc_ctx :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


