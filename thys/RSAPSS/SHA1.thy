(*  Title:      RSAPSS/SHA1.thy
    ID:         $Id: SHA1.thy,v 1.3 2008-06-11 14:22:59 lsf37 Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt
*)

header  "Formal definition of the secure hash algorithm"

theory SHA1
imports SHA1Padding
begin

text {* We define the secure hash algorithm SHA-1 and give a proof for the
  length of the message digest *}

  (*
  constdefs M:: "bv"
  "M == [Zero,One,One,Zero,Zero,Zero,Zero,One,
  Zero,One,One,Zero,Zero,Zero,One,Zero,
  Zero,One,One,Zero,Zero,Zero,One,One]"
  *)

consts
  sha1 :: "bv \<Rightarrow> bv" (* Calculates the SHA-1 Hash of a given bv *) 
  sha1expand :: "bv \<times> nat \<Rightarrow> bv" (* Performs the SHA-1 Expansion *)
  sha1expandhelp :: "bv \<times> nat \<Rightarrow> bv"
  sha1block :: "bv \<times> bv \<times> bv \<times> bv \<times> bv \<times> bv \<times> bv \<Rightarrow> bv" (*Processes the 512 bit blocks *)
  sha1compressstart :: "nat \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv"
  sha1compress :: "nat \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv" (* Compression function of SHA-1 *)

  (*    Initialization Vectors     *)
  IV1 :: "bv"
  IV2 :: "bv"
  IV3 :: "bv"
  IV4 :: "bv"
  IV5 :: "bv"

  (*    Round constants            *)
  K1 :: "bv"
  K2 :: "bv"
  K3 :: "bv"
  K4 :: "bv"
  kselect :: "nat \<Rightarrow> bv"

  (*    Round functions           *)
  fif ::"bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv"
  fxor ::"bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv"
  fmaj ::"bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv"
  fselect ::"nat \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv"


  (*    Functions for Blockprocessing       *)
  getblock :: "bv \<Rightarrow> bv"
  delblock :: "bv \<Rightarrow> bv"
  delblockhelp :: "bv \<times> nat \<Rightarrow> bv"

defs
  sha1:
  "sha1 x == (let y = sha1padd x in (
  sha1block(getblock y,delblock y,IV1,IV2,IV3,IV4,IV5)))"

recdef
  sha1expand "measure(\<lambda>(x,i). i)"
  "sha1expand (x,i) = (if (i < 16) then x else
  (let y = sha1expandhelp(x,i) in
  (sha1expand(x@y,i-(1::nat)))))"

recdef
  sha1expandhelp "measure(\<lambda>(x,i). i)"
  "sha1expandhelp (x,i) =  
  (let j = (79+16-i) in (bvrol (bvxor(bvxor(select x (32*(j-(3::nat))) (31+(32*(j-(3::nat))))) (select x (32*(j-(8::nat))) (31+(32*(j-(8::nat)))))) (bvxor(select x (32*(j-(14::nat))) (31+(32*(j-(14::nat))))) (select x (32*(j-(16::nat))) (31+(32*(j-(16::nat))))))) 1))"

defs
  getblock:
  "getblock x == select x 0 511"

  delblock:
  "delblock x == delblockhelp (x,512)"

recdef delblockhelp "measure (\<lambda>(x,n).n)"
  "delblockhelp ([],n) = []"
  "delblockhelp (x#r,n) = (if (n <= 0) then (x#r) else (delblockhelp (r,n-(1::nat))))"


(*           Lemma for sha1block definition         *)

lemma sha1blockhilf: "length (delblock (x#a)) < Suc (length a)"
proof (simp add: delblock)
  have "\<And> n. length (delblockhelp (a,n)) <= length a" 
  proof -
    fix n
    show  "length (delblockhelp (a,n)) <= length a" 
      by (induct n rule: delblockhelp.induct, auto)
  qed
  thus "length (delblockhelp (a, 511)) < Suc (length a)" using le_less_trans[of "length (delblockhelp(a,511))" "length a"]  by (simp)
qed

recdef sha1block "measure(\<lambda>(b,x,A,B,C,D,E).length x)"
  "sha1block(b,[],A,B,C,D,E) = (let H = sha1compressstart 79 b A B C D E in
                                  (let AA = addmod32 A (select H 0 31);
                                       BB = addmod32 B (select H 32 63);
                                       CC = addmod32 C (select H 64 95);
                                       DD = addmod32 D (select H 96 127);
                                       EE = addmod32 E (select H 128 159) in
                                            AA@BB@CC@DD@EE))"
  "sha1block(b,x,A,B,C,D,E) =  (let H = sha1compressstart 79 b A B C D E in 
                                  (let AA = addmod32 A (select H 0 31);
                                       BB = addmod32 B (select H 32 63);
                                       CC = addmod32 C (select H 64 95);
                                       DD = addmod32 D (select H 96 127);
                                       EE = addmod32 E (select H 128 159) in
                                          sha1block(getblock x,delblock x,AA,BB,CC,DD,EE)))"
(hints recdef_simp:sha1blockhilf)

defs 
  sha1compressstart:
  "sha1compressstart r b A B C D E == sha1compress r (sha1expand(b,79)) A B C D E"

primrec 
  "sha1compress 0 b A B C D E = (let j = (79::nat) in
                                       (let W = select b (32*j) ((32*j)+31) in 
                                        (let AA = addmod32 (addmod32 (addmod32 W (bvrol A 5)) (fselect j B C D)) (addmod32 E (kselect j));
                                             BB = A;
                                             CC = bvrol B 30;
                                             DD = C;
                                             EE = D in
                                AA@BB@CC@DD@EE)))"

"sha1compress (Suc n) b A B C D E = (let j = (79 - (Suc n)) in
                                       (let W = select b (32*j) ((32*j)+31) in 
                                        (let AA = addmod32 (addmod32 (addmod32 W (bvrol A 5)) (fselect j B C D)) (addmod32 E (kselect j));
                                             BB = A;
                                             CC = bvrol B 30;
                                             DD = C;
                                             EE = D in
                               sha1compress n b AA BB CC DD EE)))"


(*        Initialization Vectors          *)
defs
  IV1:
  "IV1 == hexvtobv [x6,x7,x4,x5,x2,x3,x0,x1]"

  IV2:
  "IV2 == hexvtobv [xE,xF,xC,xD,xA,xB,x8,x9]"

  IV3:
  "IV3 == hexvtobv [x9,x8,xB,xA,xD,xC,xF,xE]"

  IV4:
  "IV4 == hexvtobv [x1,x0,x3,x2,x5,x4,x7,x6]"

  IV5:
  "IV5 == hexvtobv [xC,x3,xD,x2,xE,x1,xF,x0]"


(*          Round constants            *)

  K1:
  "K1 == hexvtobv [x5,xA,x8,x2,x7,x9,x9,x9]"

  K2:
  "K2 == hexvtobv [x6,xE,xD,x9,xE,xB,xA,x1]"

  K3:
  "K3 == hexvtobv [x8,xF,x1,xB,xB,xC,xD,xC]"
 
  K4:
  "K4 == hexvtobv [xC,xA,x6,x2,xC,x1,xD,x6]"

  kselect:
  "kselect r == (if (r < 20) then K1 else 
                    (if (r < 40) then K2 else
                        (if (r < 60) then K3 else
                            K4)))"

(*         Round functions       *)

defs
  fif:
  "fif x y z == bvor (bvand x y) (bvand (bv_not x) z)"

  fxor:
  "fxor x y z == bvxor (bvxor x y) z"

  fmaj:
  "fmaj x y z == bvor (bvor (bvand x y) (bvand x z)) (bvand y z)"

  fselect:
  "fselect r x y z == (if (r < 20) then (fif x y z) else 
                        (if (r < 40) then (fxor x y z) else
                          (if (r < 60) then (fmaj x y z) else
                             (fxor x y z))))"



lemma sha1blocklen: "length (sha1block (b,x,A,B,C,D,E)) = 160"
proof (induct b x A B C D E rule: sha1block.induct) 
  show "!!b A B C D E. length (sha1block (b, [], A, B, C, D, E)) = 160"
    by (simp add: Let_def addmod32len)
  show "!!b z aa A B C D E.
       ALL EE H DD CC BB AA.
          EE = addmod32 E (select H 128 159) &
          DD = addmod32 D (select H 96 127) &
          CC = addmod32 C (select H 64 95) &
          BB = addmod32 B (select H 32 63) &
          AA = addmod32 A (select H 0 31) &
          H = sha1compressstart 79 b A B C D E -->
          length
           (sha1block
             (getblock (z # aa), delblock (z # aa), AA, BB, CC, DD, EE)) =
          160
       ==> length (sha1block (b, z # aa, A, B, C, D, E)) = 160"
  by (simp add: Let_def)
qed  

lemma sha1len: "length (sha1 m) = 160"
proof (simp add: sha1)
  show "length (let y = sha1padd m
      in sha1block (getblock y, delblock y, IV1, IV2, IV3, IV4, IV5)) =
    160" by (simp add: sha1blocklen Let_def)
qed

(*
constdefs test::"nat \<Rightarrow> bv"
          "test n == select (sha1 M) (8*n) ((8*(n+1))-(1::nat))"

generate_code M ="M"
declare bv_mapzip_def [unfolded max_def, THEN meta_eq_to_obj_eq, code]
generate_code hash ="sha1 M"
generate_code test = "test"

ML {* M;
      hash;
      test 0;
      test 1;
      test 2; 
      test 3;
      test 4;
      test 5;
      test 6;
      test 7;
      test 8;
      test 9;
      test 10;
      test 11;
      test 12;
      test 13;
      test 14;
      test 15;
      test 16;
      test 17;
      test 18;
      test 19;
*}
*)
end
