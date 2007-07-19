(*  Title:      RSAPSS/Wordoperations.thy
    ID:         $Id: WordOperations.thy,v 1.2 2007-07-19 19:50:53 fhaftmann Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt
*)

header  {* Extensions to the Isabelle Word theory required for SHA1 *}

theory WordOperations
imports Word Efficient_Nat
begin

types bv = "bit list";

datatype HEX = x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | xA | xB | xC | xD | xE | xF

consts bvxor ::"bv \<Rightarrow> bv \<Rightarrow> bv"   (* Xors two bv. Shorter bv is filled with 0*) 
       bvand ::"bv \<Rightarrow> bv \<Rightarrow> bv"   (* Ands two bv. Shorter bv is filled with 0*)
       bvor  ::"bv \<Rightarrow> bv \<Rightarrow> bv"   (* Ors two bv. Shorter bv is filled with 0*)
       bvrol ::"bv \<Rightarrow> nat \<Rightarrow> bv"  (* Rotates bv nat positions left*)
       bvror ::"bv \<Rightarrow> nat \<Rightarrow> bv"  (* Rotates bv nat positions right*)
       addmod32 ::"bv \<Rightarrow> bv \<Rightarrow> bv"(* Adds to bv modulo 32*)
       zerolist::"nat \<Rightarrow> bv"      (* Returns a bv consisting of int zeros*)
       select :: "bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv" (* Returns bits int1 through int2 starting with msb*)
       hextobv :: "HEX \<Rightarrow> bv"     (* Calculates bv from given hex *)
       hexvtobv :: "HEX list \<Rightarrow> bv"
       bv_prepend :: "nat => bit => bv => bv" 

consts 
       bvrolhelp ::"bv \<times> nat \<Rightarrow> bv"(*Helpfunction for bvrol*)
       bvrorhelp ::"bv \<times> nat \<Rightarrow> bv"(*Helpfunction for bvror*)
       selecthelp1 ::"bv \<times> nat \<times> nat \<Rightarrow> bv" (*Helpfunction for select*)
       selecthelp2 :: "bv \<times> nat \<Rightarrow> bv" (*Helpfunction for select*)
       reverse :: "bv \<Rightarrow> bv" (*Reverses the list*)
       last :: "bv \<Rightarrow> bit"   (*Returns the last element*)
       dellast :: "bv \<Rightarrow> bv" (*Deletes the last element*)

defs
  bvxor:
  "bvxor a b == bv_mapzip (op bitxor) a b"

  bvand:
  "bvand a b == bv_mapzip (op bitand) a b"

  bvor:
  "bvor a b == bv_mapzip (op bitor) a b"

  bvrol:
  "bvrol x a == bvrolhelp(x,a)"

  bvror:
  "bvror x a == bvrorhelp(x,a)"

  addmod32:
  "addmod32 a b == reverse (select (reverse (nat_to_bv ((bv_to_nat a) + (bv_to_nat b)))) 0 31)"

  bv_prepend:
  "bv_prepend x b bv == replicate x b @ bv"
 

primrec
  "zerolist 0 = []"
  "zerolist (Suc n) = (zerolist n)@[Zero]"

defs
  select:
  "select x i l == (selecthelp1(x,i,l))"

primrec
  "hextobv x0 = [Zero,Zero,Zero,Zero]"
  "hextobv x1 = [Zero,Zero,Zero,One]"
  "hextobv x2 = [Zero,Zero,One,Zero]"
  "hextobv x3 = [Zero,Zero,One,One]"
  "hextobv x4 = [Zero,One,Zero,Zero]"
  "hextobv x5 = [Zero,One,Zero,One]"
  "hextobv x6 = [Zero,One,One,Zero]"
  "hextobv x7 = [Zero,One,One,One]"
  "hextobv x8 = [One,Zero,Zero,Zero]"
  "hextobv x9 = [One,Zero,Zero,One]"
  "hextobv xA = [One,Zero,One,Zero]"
  "hextobv xB = [One,Zero,One,One]"
  "hextobv xC = [One,One,Zero,Zero]"
  "hextobv xD = [One,One,Zero,One]"
  "hextobv xE = [One,One,One,Zero]"
  "hextobv xF = [One,One,One,One]"

primrec
  "hexvtobv [] = []"
  "hexvtobv (x#r) = (hextobv x)@hexvtobv r"

recdef 
  bvrolhelp "measure(\<lambda>(a,x).x)"
  "bvrolhelp (a,0) = a"
  "bvrolhelp ([],x) = []"
  "bvrolhelp ((x#r),(Suc n)) = bvrolhelp((r@[x]),n)"

recdef
  bvrorhelp "measure(\<lambda>(a,x).x)"
  "bvrorhelp (a,0) = a"
  "bvrorhelp ([],x) = []"
  "bvrorhelp (x,(Suc n)) = bvrorhelp((last x)#(dellast x),n)"

recdef
  selecthelp1 "measure(\<lambda>(x,i,n). i)"
  "selecthelp1 ([],i,n) = (if (i <= 0) then (selecthelp2([],n)) else (selecthelp1([],i-(1::nat),n-(1::nat))))"
  "selecthelp1 (x#l,i,n) = (if (i <= 0) then (selecthelp2(x#l,n)) else (selecthelp1(l,i-(1::nat),n-(1::nat))))"

recdef
  selecthelp2 "measure(\<lambda>(x,n). n)"
  "selecthelp2 ([],n) = (if (n <= 0) then [Zero] else (Zero#selecthelp2([],n-(1::nat))))"
  "selecthelp2 (x#l,n) = (if (n <= 0) then [x] else (x#selecthelp2(l,(n-(1::nat)))))" 

primrec
  "reverse [] = []"
  "reverse (x#r) = (reverse r)@[x]"

primrec 
  "last [] = Zero"
  "last (x#r) = (if (r=[]) then x else (last r))"

primrec
  "dellast [] = []"
  "dellast (x#r) = (if (r = []) then [] else (x#dellast r))"


lemma selectlenhelp: "ALL l. length (selecthelp2(l,i)) = (i + 1)"
proof
  show "\<And> l. length (selecthelp2 (l,i)) = i+1"
  proof (induct i)
    fix l
    show "length (selecthelp2 (l, 0)) = 0 + 1"
    proof (cases l)
      case Nil
      hence "selecthelp2(l, 0) = [Zero]" by (simp)
      thus ?thesis by (simp)
    next
      case (Cons a list)
      hence "selecthelp2(l, 0) = [a]" by (simp)
      thus ?thesis by (simp)
    qed
  next
    fix l
    case (Suc x)
    show "length (selecthelp2(l, (Suc x))) = (Suc x) + 1"
    proof (cases l)
      case Nil
      hence "(selecthelp2(l, (Suc x))) = Zero#selecthelp2(l, x)" by (simp) 
      thus "length (selecthelp2(l, (Suc x))) = (Suc x) + 1" using Suc by (simp)
    next
      case (Cons a b)
      hence "(selecthelp2(l, (Suc x))) = a#selecthelp2(b, x)" by (simp)
      hence "length (selecthelp2(l, (Suc x))) = 1+(length (selecthelp2(b,x)))" by (simp)
      thus "length (selecthelp2(l, (Suc x))) = (Suc x) + 1" using Suc by (simp)
    qed
  qed
qed

lemma selectlenhelp2:  "\<And> i. ALL l j. EX k. selecthelp1(l,i,j) = selecthelp1(k,0,j-i)"
proof (auto)
  fix i
  show "\<And> l j. \<exists>k. selecthelp1 (l, i, j) = selecthelp1 (k, 0, j - i)"
  proof (induct i)
    fix l and j 
    have "selecthelp1(l,0,j) = selecthelp1(l,0,j-(0::nat))" by (simp)
    thus "EX k. selecthelp1 (l, 0, j) = selecthelp1 (k, 0, j - (0::nat))" by (auto)
  next
    case (Suc x)
    have b: "selecthelp1(l,(Suc x),j) = selecthelp1(tl l, x, j-(1::nat))"
    proof (cases l)
      case Nil
      hence "selecthelp1(l,(Suc x),j) = selecthelp1(l,x,j-(1::nat))" by (simp)
      moreover have "tl l = l" using Nil by (simp)
      ultimately show ?thesis by (simp)
    next
      case (Cons head tail)
      hence "selecthelp1(l,(Suc x),j) = selecthelp1(tail,x,j-(1::nat))" by (simp)
      moreover have "tail = tl l" using Cons by (simp)
      ultimately show ?thesis by (simp)
    qed
    have "\<exists>k. selecthelp1 (l, x, j) = selecthelp1 (k, 0, j - (x::nat))" using Suc by (simp)
    moreover have  "EX k. selecthelp1(tl l,x,j-(1::nat)) = selecthelp1(k,0,j-(1::nat)-(x::nat))" using Suc[of "tl l" "j-(1::nat)"] by auto
    ultimately have "EX k. selecthelp1(l, Suc x, j) = selecthelp1(k,0,j-(1::nat) - (x::nat))" using b by (auto)
    thus "EX k. selecthelp1 (l, Suc x, j) = selecthelp1 (k, 0 , j - (Suc x))" by (simp)
  qed
qed

lemma selectlenhelp3: "ALL j. selecthelp1(l,0,j) = selecthelp2(l,j)"
proof
  fix j
  show "selecthelp1 (l, 0, j) = selecthelp2 (l, j)"
  proof (cases l)
    case Nil
    assume "l=[]"
    thus "selecthelp1 (l, 0, j) = selecthelp2 (l, j)" by (simp)
  next
    case (Cons a b)
    thus "selecthelp1(l,0,j) = selecthelp2(l,j)" by (simp)
  qed
qed

lemma selectlenhelp4: "length (selecthelp1(l,i,j)) = (j-i + 1)"
proof -
  from selectlenhelp2 have "EX k. selecthelp1(l,i, j) = selecthelp1(k,0,j-i)" by (simp)
  hence "EX k. length (selecthelp1(l, i, j)) = length (selecthelp1(k,0,j-i))" by (auto)
  hence c: "EX k. length (selecthelp1(l, i, j)) = length (selecthelp2(k,j-i))" using selectlenhelp3 by (simp)
  from c obtain k where d: "length (selecthelp1(l, i, j)) = length (selecthelp2(k,j-i))" by (auto)
  have "0<=j-i" by (arith)
  hence "length (selecthelp2(k,j-i)) = j-i+1" using selectlenhelp by (simp) 
  thus "length (selecthelp1(l,i,j)) = j-i+1" using d by (simp)
qed

lemma selectlen:"length (select bv i j) = (j-i)+1"
proof (simp add: select)
  from selectlenhelp4 show "length (selecthelp1(bv,i,j)) = Suc (j-i)" by (simp)
qed

lemma reverselen: "length (reverse a) = length a"
proof (induct a)
  show "length (reverse []) = length []" by (simp)
next
  case (Cons a1 a2)
  have "reverse (a1#a2) = reverse (a2)@[a1]" by (simp)
  hence "length (reverse (a1#a2)) = Suc (length (reverse (a2)))" by (simp)
  thus "length (reverse (a1#a2)) = length (a1#a2)" using Cons by (simp)
qed

lemma addmod32len: "\<And> a b. length (addmod32 a b) = 32"
proof (simp add: addmod32)
  fix a and b
  have "length (select (reverse (nat_to_bv (bv_to_nat a + bv_to_nat b))) 0 31) = 32" using selectlen[of _ 0 31] by (simp)
  thus "length (reverse (select (reverse (nat_to_bv (bv_to_nat a + bv_to_nat b))) 0 31)) = 32" using reverselen by (simp)
qed

end
