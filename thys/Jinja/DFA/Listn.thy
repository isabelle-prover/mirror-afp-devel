(*  Title:      HOL/MicroJava/BV/Listn.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Lists of a fixed length.
*)

section \<open>Fixed Length Lists\<close>

theory Listn
imports Err "HOL-Library.NList"
begin

definition le :: "'a ord \<Rightarrow> ('a list)ord"
where
  "le r = list_all2 (\<lambda>x y. x \<sqsubseteq>\<^sub>r y)"

abbreviation
  lesublist :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubseteq>\<^bsub>_\<^esub>] _)" [50, 0, 51] 50) where
  "x [\<sqsubseteq>\<^bsub>r\<^esub>] y == x <=_(Listn.le r) y"

abbreviation
  lesssublist :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubset>\<^bsub>_\<^esub>] _)" [50, 0, 51] 50) where
  "x [\<sqsubset>\<^bsub>r\<^esub>] y == x <_(Listn.le r) y"

(*<*)
notation (ASCII)
  lesublist  ("(_ /[<=_] _)" [50, 0, 51] 50) and
  lesssublist  ("(_ /[<_] _)" [50, 0, 51] 50)

abbreviation (input)
  lesublist2 :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubseteq>\<^sub>_] _)" [50, 0, 51] 50) where
  "x [\<sqsubseteq>\<^sub>r] y == x [\<sqsubseteq>\<^bsub>r\<^esub>] y"

abbreviation (input)
  lesssublist2 :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubset>\<^sub>_] _)" [50, 0, 51] 50) where
  "x [\<sqsubset>\<^sub>r] y == x [\<sqsubset>\<^bsub>r\<^esub>] y"
(*>*)

abbreviation
  plussublist :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'c list"
    ("(_ /[\<squnion>\<^bsub>_\<^esub>] _)" [65, 0, 66] 65) where
  "x [\<squnion>\<^bsub>f\<^esub>] y == x \<squnion>\<^bsub>map2 f\<^esub> y"

(*<*)
notation (ASCII)
  plussublist  ("(_ /[+_] _)" [65, 0, 66] 65)

abbreviation (input)
  plussublist2 :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'c list"
    ("(_ /[\<squnion>\<^sub>_] _)" [65, 0, 66] 65) where
  "x [\<squnion>\<^sub>f] y == x [\<squnion>\<^bsub>f\<^esub>] y"
(*>*)


primrec coalesce :: "'a err list \<Rightarrow> 'a list err"
where
  "coalesce [] = OK[]"
| "coalesce (ex#exs) = Err.sup (#) ex (coalesce exs)"

definition sl :: "nat \<Rightarrow> 'a sl \<Rightarrow> 'a list sl"
where
  "sl n = (\<lambda>(A,r,f). (nlists n A, le r, map2 f))"

definition sup :: "('a \<Rightarrow> 'b \<Rightarrow> 'c err) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list err"
where
  "sup f = (\<lambda>xs ys. if size xs = size ys then coalesce(xs [\<squnion>\<^bsub>f\<^esub>] ys) else Err)"

definition upto_esl :: "nat \<Rightarrow> 'a esl \<Rightarrow> 'a list esl"
where
  "upto_esl m = (\<lambda>(A,r,f). (Union{nlists n A |n. n \<le> m}, le r, sup f))"


lemmas [simp] = set_update_subsetI

lemma unfold_lesub_list: "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys = Listn.le r xs ys"
(*<*) by (simp add: lesub_def) (*>*)

lemma Nil_le_conv [iff]: "([] [\<sqsubseteq>\<^bsub>r\<^esub>] ys) = (ys = [])"
(*<*)
apply (unfold lesub_def Listn.le_def)
apply simp
done
(*>*)

lemma Cons_notle_Nil [iff]: "\<not> x#xs [\<sqsubseteq>\<^bsub>r\<^esub>] []"
(*<*)
apply (unfold lesub_def Listn.le_def)
apply simp
done
(*>*)

lemma Cons_le_Cons [iff]: "x#xs [\<sqsubseteq>\<^bsub>r\<^esub>] y#ys = (x \<sqsubseteq>\<^sub>r y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys)"
(*<*)
by (simp add: lesub_def Listn.le_def)
(*>*)

lemma list_update_le_cong:
  "\<lbrakk> i<size xs; xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys; x \<sqsubseteq>\<^sub>r y \<rbrakk> \<Longrightarrow> xs[i:=x] [\<sqsubseteq>\<^bsub>r\<^esub>] ys[i:=y]"
(*<*)
apply (unfold unfold_lesub_list)
apply (unfold Listn.le_def)
apply (simp add: list_all2_update_cong)
done
(*>*)


lemma le_listD: "\<lbrakk> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys; p < size xs \<rbrakk> \<Longrightarrow> xs!p \<sqsubseteq>\<^sub>r ys!p"
(*<*)
by (simp add: Listn.le_def lesub_def list_all2_nthD)
(*>*)

lemma le_list_refl: "\<forall>x. x \<sqsubseteq>\<^sub>r x \<Longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] xs"
(*<*)
apply (simp add: unfold_lesub_list lesub_def Listn.le_def list_all2_refl)
done
(*>*)


lemma le_list_trans: 
  assumes ord: "order r A"
      and xs:  "xs \<in> nlists n A" and ys: "ys \<in> nlists n A" and zs: "zs \<in> nlists n A"
      and      "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys" and "ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs"
    shows      "xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs"
(*<*)
  using assms
proof (unfold le_def lesssub_def lesub_def)
  assume "list_all2 r xs ys" and "list_all2 r ys zs"
  hence xs_ys_zs:  "\<forall>i < length xs. r (xs!i) (ys!i) \<and> r (ys!i) (zs!i)" 
        and len_xs_zs: "length xs = length zs" by (auto simp add: list_all2_conv_all_nth)
  from xs ys zs have inA: "\<forall>i<length xs. xs!i \<in> A \<and> ys!i \<in> A \<and> zs!i \<in> A" by (unfold nlists_def) auto
  
  from ord have "\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. x \<sqsubseteq>\<^sub>r y \<and> y \<sqsubseteq>\<^sub>r z \<longrightarrow> x \<sqsubseteq>\<^sub>r z" by (unfold order_def) blast
  hence "\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. r x y \<and> r y z \<longrightarrow> r x z" by (unfold lesssub_def lesub_def)
  with xs_ys_zs inA have "\<forall>i<length xs. r (xs!i) (zs!i)" by blast
  with len_xs_zs show "list_all2 r xs zs" by (simp add:list_all2_conv_all_nth)
qed
(*
  apply (unfold lesssub_def lesub_def)
  apply (unfold Listn.le_def)  
  apply (frule list_all2_trans)
    apply simp
  apply blast
  apply (simp add:list_all2_conv_all_nth)
  apply (intro strip)
  apply (erule order_trans) 
  apply (unfold list_def)
  apply (auto)
*)

lemma le_list_antisym: 
  assumes ord: "order r A"
      and xs:  "xs \<in> nlists n A" and ys: "ys \<in> nlists n A"
      and      "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys" and "ys [\<sqsubseteq>\<^bsub>r\<^esub>] xs"
    shows      "xs = ys"
(*<*)
  using assms
proof (simp add: le_def lesssub_def lesub_def)
  assume "list_all2 r xs ys" and "list_all2 r ys xs"
  hence xs_ys:  "\<forall>i < length xs. r (xs!i) (ys!i) \<and> r (ys!i) (xs!i)" 
        and len_xs_ys: "length xs = length ys" by (auto simp add: list_all2_conv_all_nth)
  from xs ys have inA: "\<forall>i<length xs. xs!i \<in> A \<and> ys!i \<in> A" by (unfold nlists_def) auto
  
  from ord have "\<forall>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq>\<^sub>r y \<and> y \<sqsubseteq>\<^sub>r x \<longrightarrow> x = y" by (unfold order_def) blast
  hence "\<forall>x\<in>A. \<forall>y\<in>A. r x y \<and> r y x \<longrightarrow> x = y" by (unfold lesssub_def lesub_def)
  with xs_ys inA have "\<forall>i<length xs. xs!i = ys!i" by blast
  with len_xs_ys show "xs = ys" by (simp add:list_eq_iff_nth_eq)
qed
(*
apply (unfold unfold_lesub_list)
  apply (unfold Listn.le_def)
  apply (auto simp add: list_eq_iff_nth_eq list_def list_all2_conv_all_nth)
  apply (rule order_antisym)     
 apply (auto simp add: list_def)
done
*)
(*>*)

lemma nth_in [rule_format, simp]:
  "\<forall>i n. size xs = n \<longrightarrow> set xs \<subseteq> A \<longrightarrow> i < n \<longrightarrow> (xs!i) \<in> A"
(*<*)
apply (induct "xs")
 apply simp
apply (simp add: nth_Cons split: nat.split)
done
(*>*)

lemma le_list_refl': "order r A \<Longrightarrow> xs \<in> nlists n A \<Longrightarrow> xs \<sqsubseteq>\<^bsub>Listn.le r\<^esub> xs"  
  apply (unfold le_def lesssub_def lesub_def list_all2_conv_all_nth)
  apply auto  
  apply (subgoal_tac "xs ! i \<in> A")  
   apply (subgoal_tac "(xs ! i) \<sqsubseteq>\<^sub>r (xs ! i)")
    apply (simp only: lesssub_def lesub_def)
   apply (fastforce dest: nlistsE_nth_in)
   apply (fastforce dest: order_refl)
  done

lemma order_listI [simp, intro!]: "order r A \<Longrightarrow> order(Listn.le r) (nlists n A)"  
(*<*)
proof-
  assume ord: "order r A"
  let ?r = "Listn.le r"
  let ?A = "nlists n A" 
  have "\<forall>x\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub> x" using ord le_list_refl' by auto
  moreover have "\<forall>x\<in>?A. \<forall>y\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub> y \<and> y \<sqsubseteq>\<^bsub>?r\<^esub>  x \<longrightarrow> x=y" using ord le_list_antisym by auto
  moreover have "\<forall>x\<in>?A. \<forall>y\<in>?A. \<forall>z\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub>y \<and> y \<sqsubseteq>\<^bsub>?r\<^esub> z \<longrightarrow> x \<sqsubseteq>\<^bsub>?r\<^esub> z" using ord le_list_trans by auto
  ultimately show ?thesis by (auto simp only: order_def)
qed
(*>*)

lemma le_list_refl2': "order r A \<Longrightarrow> xs \<in> (\<Union>{nlists n A |n. n \<le> mxs})\<Longrightarrow> xs \<sqsubseteq>\<^bsub>Listn.le r\<^esub> xs"  
  by (auto simp add:le_list_refl')
lemma le_list_trans2: 
  assumes "order r A"
      and "xs \<in> (\<Union>{nlists n A |n. n \<le> mxs})" and "ys \<in>(\<Union>{nlists n A |n. n \<le> mxs})" and "zs \<in>(\<Union>{nlists n A |n. n \<le> mxs})"
      and "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys" and "ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs"
    shows "xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs"
(*<*)using assms
proof(auto simp only:nlists_def le_def lesssub_def lesub_def)
  assume xA: "set xs \<subseteq> A" and "length xs \<le> mxs " and " length ys \<le> mxs "
     and yA: "set ys \<subseteq> A" and len_zs: "length zs \<le> mxs" 
     and zA: "set zs \<subseteq> A" and xy: "list_all2 r xs ys" and yz: "list_all2 r ys zs"
     and ord: "order r A" 
  from xy yz have xs_ys: "length xs = length ys" and ys_zs: "length ys = length zs" by (auto simp add:list_all2_conv_all_nth)
  from ord have "\<forall>x\<in>A.  \<forall>y\<in>A. \<forall>z\<in>A. x \<sqsubseteq>\<^sub>r y \<and> y \<sqsubseteq>\<^sub>r z \<longrightarrow> x \<sqsubseteq>\<^sub>r z" by (unfold order_def) blast
  hence trans: "\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. r x y \<and> r y z \<longrightarrow> r x z" by (simp only:lesssub_def lesub_def)

  from xA yA zA have x_inA: "\<forall>i<length xs. xs!i \<in> A"
                 and y_inA: "\<forall>i<length xs. ys!i \<in> A" 
                 and z_inA: "\<forall>i<length xs. zs!i \<in> A"  using xs_ys ys_zs  by auto
  
  from xy yz have "\<forall>i < length xs. r (xs!i) (ys!i)" 
              and "\<forall>i < length ys. r (ys!i) (zs!i)" by (auto simp add:list_all2_conv_all_nth)
  hence "\<forall>i < length xs. r (xs!i) (ys!i) \<and> r (ys!i) (zs!i)" using xs_ys ys_zs by auto

  with x_inA y_inA z_inA
  have "\<forall>i<length xs. r (xs!i)  (zs!i)" using trans  xs_ys ys_zs by blast
  thus "list_all2 r xs zs" using xs_ys ys_zs by (simp add:list_all2_conv_all_nth)
qed


lemma le_list_antisym2: 
  assumes "order r A"
      and "xs \<in>(\<Union>{nlists n A |n. n \<le> mxs})" and "ys \<in>(\<Union>{nlists n A |n. n \<le> mxs})" 
      and "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys" and "ys [\<sqsubseteq>\<^bsub>r\<^esub>] xs"
    shows " xs = ys"
(*<*)
  using assms
proof(auto simp only:nlists_def le_def lesssub_def lesub_def)
  assume xA: "set xs \<subseteq> A" and len_ys: "length ys \<le> mxs" and len_xs: "length xs \<le> mxs" 
     and yA: "set ys \<subseteq> A" and xy: "list_all2 r xs ys" and yx: "list_all2 r ys xs" 
     and ord: "order r A"
  from xy have len_eq_xs_ys: "length xs = length ys" by (simp add:list_all2_conv_all_nth)
  
  from ord have antisymm:"\<forall>x\<in>A. \<forall>y\<in>A. r x y \<and> r y x\<longrightarrow> x=y " by (auto simp only:lesssub_def lesub_def order_def)
  from xA yA have x_inA: "\<forall>i<length xs. xs!i \<in> A" and y_inA: "\<forall>i<length ys. ys!i \<in> A" by auto
  from xy yx have "\<forall>i < length xs. r (xs!i) (ys!i)" and "\<forall>i < length ys. r (ys!i) (xs!i)" by (auto simp add:list_all2_conv_all_nth)
  with x_inA y_inA
  have "\<forall>i<length xs. xs!i = ys!i" using antisymm len_eq_xs_ys by auto
  then show "xs = ys" using len_eq_xs_ys by (simp add:list_eq_iff_nth_eq)
qed
(*<*)


lemma order_listI2[intro!] : "order r A \<Longrightarrow> order(Listn.le r) (\<Union>{nlists n A |n. n \<le> mxs})"
(*<*)
proof-
  assume ord: "order r A"  
  let ?r = "Listn.le r"
  let ?A = "(\<Union>{nlists n A |n. n \<le> mxs})" 
  have "\<forall>x\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub> x" using ord le_list_refl2' by auto  \<comment>\<open> use order_listI \<close>
  moreover have "\<forall>x\<in>?A. \<forall>y\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub> y \<and> y \<sqsubseteq>\<^bsub>?r\<^esub>  x \<longrightarrow> x=y" using ord le_list_antisym2 by blast
  moreover have "\<forall>x\<in>?A.  \<forall>y\<in>?A. \<forall>z\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub>y \<and> y \<sqsubseteq>\<^bsub>?r\<^esub> z \<longrightarrow> x \<sqsubseteq>\<^bsub>?r\<^esub> z" using ord le_list_trans2 by blast
  ultimately show ?thesis by (auto simp only: order_def)
qed


lemma lesub_list_impl_same_size [simp]: "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<Longrightarrow> size ys = size xs"
(*<*)
apply (unfold Listn.le_def lesub_def)
apply (simp add: list_all2_lengthD)
done
(*>*)

lemma lesssub_lengthD: "xs [\<sqsubset>\<^sub>r] ys \<Longrightarrow> size ys = size xs"
(*<*)
apply (unfold lesssub_def)
apply auto
done
(*>*)


lemma le_list_appendI: "a [\<sqsubseteq>\<^bsub>r\<^esub>] b \<Longrightarrow> c [\<sqsubseteq>\<^bsub>r\<^esub>] d \<Longrightarrow> a@c [\<sqsubseteq>\<^bsub>r\<^esub>] b@d"
(*<*)
apply (unfold Listn.le_def lesub_def)
apply (rule list_all2_appendI, assumption+)
done
(*>*)

lemma le_listI:
  assumes "length a = length b"
  assumes "\<And>n. n < length a \<Longrightarrow> a!n \<sqsubseteq>\<^sub>r b!n"
  shows "a [\<sqsubseteq>\<^bsub>r\<^esub>] b"
(*<*)
proof -
  from assms have "list_all2 r a b"
    by (simp add: list_all2_all_nthI lesub_def)
  then show ?thesis by (simp add: Listn.le_def lesub_def)
qed
(*>*)

lemma plus_list_Nil [simp]: "[] [\<squnion>\<^bsub>f\<^esub>] xs = []"
(*<*)
apply (unfold plussub_def)
apply simp
done
(*>*)

lemma plus_list_Cons [simp]:
  "(x#xs) [\<squnion>\<^bsub>f\<^esub>] ys = (case ys of [] \<Rightarrow> [] | y#ys \<Rightarrow> (x \<squnion>\<^sub>f y)#(xs [\<squnion>\<^bsub>f\<^esub>] ys))"
(*<*) by (simp add: plussub_def split: list.split) (*>*)

lemma length_plus_list [rule_format, simp]:
  "\<forall>ys. size(xs [\<squnion>\<^bsub>f\<^esub>] ys) = min(size xs) (size ys)"
(*<*)
apply (induct xs)
 apply simp
apply clarify
apply (simp (no_asm_simp) split: list.split)
done
(*>*)

lemma nth_plus_list [rule_format, simp]:
  "\<forall>xs ys i. size xs = n \<longrightarrow> size ys = n \<longrightarrow> i<n \<longrightarrow> (xs [\<squnion>\<^bsub>f\<^esub>] ys)!i = (xs!i) \<squnion>\<^sub>f (ys!i)"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (case_tac xs)
 apply simp
apply (force simp add: nth_Cons split: list.split nat.split)
done
(*>*)


lemma (in Semilat) plus_list_ub1 [rule_format]:
 "\<lbrakk> set xs \<subseteq> A; set ys \<subseteq> A; size xs = size ys \<rbrakk>
  \<Longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] xs [\<squnion>\<^bsub>f\<^esub>] ys"
(*<*)
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done
(*>*)

lemma (in Semilat) plus_list_ub2:
 "\<lbrakk>set xs \<subseteq> A; set ys \<subseteq> A; size xs = size ys \<rbrakk> \<Longrightarrow> ys [\<sqsubseteq>\<^bsub>r\<^esub>] xs [\<squnion>\<^bsub>f\<^esub>] ys"
(*<*)
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done
(*>*)

lemma (in Semilat) plus_list_lub [rule_format]:
shows "\<forall>xs ys zs. set xs \<subseteq> A \<longrightarrow> set ys \<subseteq> A \<longrightarrow> set zs \<subseteq> A
  \<longrightarrow> size xs = n \<and> size ys = n \<longrightarrow>
  xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs \<and> ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs \<longrightarrow> xs [\<squnion>\<^bsub>f\<^esub>] ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs"
(*<*)
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done
(*>*)

lemma (in Semilat) list_update_incr [rule_format]:
 "x\<in>A \<Longrightarrow> set xs \<subseteq> A \<longrightarrow>
  (\<forall>i. i<size xs \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] xs[i := x \<squnion>\<^sub>f xs!i])"
(*<*)
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
apply (induct xs)
 apply simp
apply (simp add: in_nlists_Suc_iff)
apply clarify
apply (simp add: nth_Cons split: nat.split)
done
(*>*)


lemma closed_nlistsI:
  "closed S f \<Longrightarrow> closed (nlists n S) (map2 f)"
(*<*)
apply (unfold closed_def)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_nlists_Suc_iff)
apply clarify
apply simp
done
(*>*)


lemma Listn_sl_aux:
assumes "Semilat A r f" shows "semilat (Listn.sl n (A,r,f))"
(*<*)
proof -
  interpret Semilat A r f by fact
  show ?thesis
  apply (unfold Listn.sl_def)
  apply (simp (no_asm) only: semilat_Def split_conv)
  apply (rule conjI)
   apply simp
  apply (rule conjI)
   apply (simp only: closedI closed_nlistsI)
  apply (simp (no_asm) only: nlists_def)
  apply (simp (no_asm_simp) add: plus_list_ub1 plus_list_ub2 plus_list_lub)
  done
qed
(*>*)

lemma Listn_sl: "semilat L \<Longrightarrow> semilat (Listn.sl n L)"
(*<*) apply (cases L) apply simp
apply (drule Semilat.intro)
by (simp add: Listn_sl_aux split_tupled_all) (*>*)

lemma coalesce_in_err_list [rule_format]:
  "\<forall>xes. xes \<in> nlists n (err A) \<longrightarrow> coalesce xes \<in> err(nlists n A)"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_nlists_Suc_iff)
apply clarify
apply (simp (no_asm) add: plussub_def Err.sup_def lift2_def split: err.split)
apply force
done
(*>*)

lemma lem: "\<And>x xs. x \<squnion>\<^bsub>(#)\<^esub> xs = x#xs"
(*<*) by (simp add: plussub_def) (*>*)

lemma coalesce_eq_OK1_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow>
  \<forall>xs. xs \<in> nlists n A \<longrightarrow> (\<forall>ys. ys \<in> nlists n A \<longrightarrow>
  (\<forall>zs. coalesce (xs [\<squnion>\<^bsub>f\<^esub>] ys) = OK zs \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs))"
(*<*)
apply (induct n)
  apply simp
apply clarify
apply (simp add: in_nlists_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
apply (force simp add: semilat_le_err_OK1)
done
(*>*)

lemma coalesce_eq_OK2_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow>
  \<forall>xs. xs \<in> nlists n A \<longrightarrow> (\<forall>ys. ys \<in> nlists n A \<longrightarrow>
  (\<forall>zs. coalesce (xs [\<squnion>\<^bsub>f\<^esub>] ys) = OK zs \<longrightarrow> ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs))"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_nlists_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
apply (force simp add: semilat_le_err_OK2)
done
(*>*)

lemma lift2_le_ub:
  "\<lbrakk> semilat(err A, Err.le r, lift2 f); x\<in>A; y\<in>A; x \<squnion>\<^sub>f y = OK z;
      u\<in>A; x \<sqsubseteq>\<^sub>r u; y \<sqsubseteq>\<^sub>r u \<rbrakk> \<Longrightarrow> z \<sqsubseteq>\<^sub>r u"
(*<*)
apply (unfold semilat_Def plussub_def err_def')
apply (simp add: lift2_def)
apply clarify
apply (rotate_tac -3)
apply (erule thin_rl)
apply (erule thin_rl)
apply force
done
(*>*)

lemma coalesce_eq_OK_ub_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow>
  \<forall>xs. xs \<in> nlists n A \<longrightarrow> (\<forall>ys. ys \<in> nlists n A \<longrightarrow>
  (\<forall>zs us. coalesce (xs [\<squnion>\<^bsub>f\<^esub>] ys) = OK zs \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] us \<and> ys [\<sqsubseteq>\<^bsub>r\<^esub>] us
           \<and> us \<in> nlists n A \<longrightarrow> zs [\<sqsubseteq>\<^bsub>r\<^esub>] us))"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_nlists_Suc_iff)
apply clarify
apply (simp (no_asm_use) split: err.split_asm add: lem Err.sup_def lift2_def)
apply clarify
apply (rule conjI)
 apply (blast intro: lift2_le_ub)
apply blast
done
(*>*)

lemma lift2_eq_ErrD:
  "\<lbrakk> x \<squnion>\<^sub>f y = Err; semilat(err A, Err.le r, lift2 f); x\<in>A; y\<in>A \<rbrakk>
  \<Longrightarrow> \<not>(\<exists>u\<in>A. x \<sqsubseteq>\<^sub>r u \<and> y \<sqsubseteq>\<^sub>r u)"
(*<*) by (simp add: OK_plus_OK_eq_Err_conv [THEN iffD1]) (*>*)


lemma coalesce_eq_Err_D [rule_format]:
  "\<lbrakk> semilat(err A, Err.le r, lift2 f) \<rbrakk>
  \<Longrightarrow> \<forall>xs. xs \<in> nlists n A \<longrightarrow> (\<forall>ys. ys \<in> nlists n A \<longrightarrow>
      coalesce (xs [\<squnion>\<^bsub>f\<^esub>] ys) = Err \<longrightarrow>
      \<not>(\<exists>zs \<in> nlists n A. xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs \<and> ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs))"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_nlists_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
 apply (blast dest: lift2_eq_ErrD)
done
(*>*)

lemma closed_err_lift2_conv:
  "closed (err A) (lift2 f) = (\<forall>x\<in>A. \<forall>y\<in>A. x \<squnion>\<^sub>f y \<in> err A)"
(*<*)
apply (unfold closed_def)
apply (simp add: err_def')
done
(*>*)

lemma closed_map2_list [rule_format]:
  "closed (err A) (lift2 f) \<Longrightarrow>
  \<forall>xs. xs \<in> nlists n A \<longrightarrow> (\<forall>ys. ys \<in> nlists n A \<longrightarrow>
  map2 f xs ys \<in> nlists n (err A))"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_nlists_Suc_iff)
apply clarify
apply (simp add: plussub_def closed_err_lift2_conv)
done
(*>*)

lemma closed_lift2_sup:
  "closed (err A) (lift2 f) \<Longrightarrow>
  closed (err (nlists n A)) (lift2 (sup f))"
(*<*) by (fastforce  simp add: closed_def plussub_def sup_def lift2_def
                          coalesce_in_err_list closed_map2_list
                split: err.split) (*>*)

lemma err_semilat_sup:
  "err_semilat (A,r,f) \<Longrightarrow>
  err_semilat (nlists n A, Listn.le r, sup f)"
(*<*)
apply (unfold Err.sl_def)
apply (simp only: split_conv)
apply (simp (no_asm) only: semilat_Def plussub_def)
apply (simp (no_asm_simp) only: Semilat.closedI [OF Semilat.intro] closed_lift2_sup)
apply (rule conjI)
 apply (drule Semilat.orderI [OF Semilat.intro])
 apply simp
apply (simp (no_asm) only: unfold_lesub_err Err.le_def err_def' sup_def lift2_def)
apply (simp (no_asm_simp) add: coalesce_eq_OK1_D coalesce_eq_OK2_D split: err.split)
apply (blast intro: coalesce_eq_OK_ub_D dest: coalesce_eq_Err_D)
done
(*>*)

lemma err_semilat_upto_esl:
  "\<And>L. err_semilat L \<Longrightarrow> err_semilat(upto_esl m L)"
(*<*)
apply (unfold Listn.upto_esl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
apply (fastforce intro!: err_semilat_UnionI err_semilat_sup
                dest: lesub_list_impl_same_size
                simp add: plussub_def Listn.sup_def)
done
(*>*)

end
