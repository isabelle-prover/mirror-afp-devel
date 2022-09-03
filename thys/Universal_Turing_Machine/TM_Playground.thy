(* Title: thys/TM_Playground.thy
   Author: Franz Regensburger (FABR) 02/2022
 *)

theory TM_Playground 
  imports
    StrongCopyTM
begin

(* Playground *)

(* ad numerals *)

value "[1::nat,2,3,4] ! 0"
value "[1::nat,2,3,4] ! 1"

value "<2::nat>"
value "tape_of (2::nat)"

value "<(0::nat,1::nat)>"
value "tape_of_nat_prod (0::nat,1::nat)"

value "<([0,1::nat],[0,1::nat])>"
value "tape_of_nat_prod ([0,1::nat],[0,1::nat])"

value "tape_of_nat_list [2,0,3::nat]"
value "<[2,0,3::nat]>"

(* ad fetch function *)


lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 0 Bk = (Nop , 0)" by auto
lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 0 Oc = (Nop , 0)" by auto

lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 1 Bk = (R , 3)" by auto
lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 1 Oc = (WB, 2)" by auto

lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 3 Bk = (WO, 0)"
  by (simp add: numeral_eqs_upto_12)

lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 3 Oc = (WB, 2)"
  by (simp add: numeral_eqs_upto_12)

(* fetch last instruction of program, which is explicitly given by the instr list *)
lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 4 Bk = (L, 8)"
  by (simp add: numeral_eqs_upto_12)

(* fetch instruction outside of explicitly given instr list *)
lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 4 Oc = (Nop, 0)"
  by (simp add: numeral_eqs_upto_12)

lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 10 Bk = (Nop, 0)"
  by (simp add: numeral_eqs_upto_12)

lemma "fetch [(R, 3),(WB,2), (R,1),(R,1), (WO,0),(WB,2), (L,8)] 10 Oc = (Nop, 0)"
  by (simp add: numeral_eqs_upto_12)


(* ad Hoare triples *)

(* This result can be validated by a simple test run *)
lemma 
  "\<lbrace>\<lambda>(l1, r1). (l1,r1) = ([], [Oc,Oc] )\<rbrace> tm_weak_copy \<lbrace>\<lambda>(l0,r0). \<exists>k l. (l0,r0) = (Bk \<up> k, [Oc,Oc,Bk,Oc,Oc] @ Bk \<up> l)\<rbrace>"
proof -
  have "\<lbrace>\<lambda>tap. tap = ([], <[1::nat]>) \<rbrace> tm_weak_copy \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[hd [1::nat], hd [1::nat]]> @ Bk \<up> l) \<rbrace>"    
    by (simp add: tm_weak_copy_correct5)
  then have "\<lbrace>\<lambda>tap. tap = ([], <[1::nat]>) \<rbrace> tm_weak_copy \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[1::nat, 1::nat]> @ Bk \<up> l) \<rbrace>"
    by force
  moreover have "<[1::nat]> = [Oc,Oc]"
    by (simp add: tape_of_list_def tape_of_nat_def)
  moreover have "<[1::nat, 1::nat]> = [Oc,Oc,Bk,Oc,Oc]"
    by (simp add: tape_of_list_def tape_of_nat_def)
  ultimately have "\<lbrace>\<lambda>tap. tap = ([], <[1::nat]>) \<rbrace> tm_weak_copy \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[hd [1::nat], hd [1::nat]]> @ Bk \<up> l) \<rbrace>"
    by simp
  then show ?thesis
    by (smt Hoare_haltI Hoare_halt_E0 \<open><[1, 1]> = [Oc, Oc, Bk, Oc, Oc]\<close> \<open><[1]> = [Oc, Oc]\<close>
        case_prodD case_prodI holds_for.simps is_final_eq list.discI list.inject list.sel(1)
        not_Cons_self2 tape_of_list_def tape_of_nat_def tape_of_nat_list.elims tape_of_nat_list.simps(3))
qed

(* However, this general result can never be validated by testing. It must be verified by a proof *)
lemma 
  "\<forall>n. \<lbrace>\<lambda>tap. tap = ([], Oc\<up>(n+1))\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k,  Oc\<up>(n+1) @ [Bk] @ Oc\<up>(n+1) @ Bk \<up> l) \<rbrace>"
proof 
  fix n
  have "\<lbrace>\<lambda>tap. tap = ([], <[n::nat]>)\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[n, n]> @ Bk \<up> l) \<rbrace>"
    by (rule tm_weak_copy_correct5)
  moreover have "<[n::nat]> =  Oc\<up>(Suc n)"
    by (simp add: tape_of_list_def tape_of_nat_def)
  moreover have "<[n, n]> =  Oc\<up>(Suc n) @ [Bk] @ Oc\<up>(Suc n)"
    by (simp add: tape_of_list_def tape_of_nat_def)
  ultimately have X: "\<lbrace>\<lambda>tap. tap = ([], Oc\<up>(Suc n))\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k,  Oc\<up>(Suc n) @ [Bk] @ Oc\<up>(Suc n) @ Bk \<up> l) \<rbrace>"
    by simp
  show "\<lbrace>\<lambda>tap. tap = ([], Oc\<up>(n+1))\<rbrace> tm_weak_copy \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k,  Oc\<up>(n+1) @ [Bk] @ Oc\<up>(n+1) @ Bk \<up> l) \<rbrace>" using X by auto
qed

end
