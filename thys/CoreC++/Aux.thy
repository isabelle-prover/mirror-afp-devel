(*  Title:       CoreC++
    ID:          $Id: Aux.thy,v 1.8 2006-11-06 11:54:13 wasserra Exp $
    Author:      David von Oheimb, Tobias Nipkow, Daniel Wasserrab  
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

header {* \isaheader{Auxiliary Definitions} *}

theory Aux imports Main While_Combinator begin


declare
 option.splits[split]
 Let_def[simp]
 subset_insertI2 [simp]
 Un_subset_iff[simp]
 Cons_eq_map_conv [iff]

(* FIXME move and possibly turn into a general simproc *)
lemma nat_add_max_le[simp]:
  "((n::nat) + max i j \<le> m) = (n + i \<le> m \<and> n + j \<le> m)"
 by arith

lemma Suc_add_max_le[simp]:
  "(Suc(n + max i j) \<le> m) = (Suc(n + i) \<le> m \<and> Suc(n + j) \<le> m)"
by arith


syntax "_Some" :: "'a \<Rightarrow> 'a option" ("(\<lfloor>_\<rfloor>)")

translations "\<lfloor>x\<rfloor>" == "Some x"

declare
 option.splits[split]
 Let_def[simp]
 subset_insertI2 [simp]
 Un_subset_iff[simp]



lemma butlast_tail:
  "butlast (Xs@[X,Y]) = Xs@[X]"
by (induct Xs) auto


lemma butlast_noteq:"Cs \<noteq> [] \<Longrightarrow> butlast Cs \<noteq> Cs"
by(induct Cs)simp_all


lemma app_hd_tl:"\<lbrakk>Cs \<noteq> []; Cs = Cs' @ tl Cs\<rbrakk> \<Longrightarrow> Cs' = [hd Cs]"

apply (subgoal_tac "[hd Cs] @ tl Cs = Cs' @ tl Cs")
 apply fast
apply simp
done



lemma only_one_append:"\<lbrakk>C' \<notin> set Cs; C' \<notin> set Cs'; Ds@ C'#Ds' = Cs@ C'#Cs'\<rbrakk> 
\<Longrightarrow> Cs = Ds \<and> Cs' = Ds'"

  apply -
  apply (simp add:append_eq_append_conv2)
  apply (auto simp:in_set_conv_decomp)
     apply (subgoal_tac "hd (us @ C'#Ds') = C'")
      apply (case_tac us)
       apply simp
      apply fastsimp
     apply simp
    apply (subgoal_tac "hd (us @ C'#Ds') = C'")
     apply (case_tac us)
      apply simp
     apply fastsimp
    apply simp
   apply (subgoal_tac "hd (us @ C'#Cs') = C'")
    apply (case_tac us)
     apply simp
    apply fastsimp
   apply (subgoal_tac "hd(C'#Ds') = C'")
    apply simp
   apply (simp (no_asm))
  apply (subgoal_tac "hd (us @ C'#Cs') = C'")
   apply (case_tac us)
    apply simp
   apply fastsimp
  apply (subgoal_tac "hd(C'#Ds') = C'")
   apply simp
  apply (simp (no_asm))
  done


lemma assumes elem:"a \<in> A" shows Singleton_card:"(card A = 1) = (\<forall>a' \<in> A. a = a')"
proof -
  { assume elem:"a \<in> A" "\<forall>a'\<in>A. a = a'"
    hence "A \<subseteq> {a}" by -(rule subsetI,erule_tac x="x" in ballE,simp+)
    with elem have "A = {a}" by fastsimp
    hence "card A = Suc 0" by simp }
  hence 1:"\<lbrakk>a \<in> A; \<forall>a'\<in>A. a = a'\<rbrakk> \<Longrightarrow> card A = Suc 0" .
  { fix b assume elem:"a \<in> A" and cardSuc:"card A = Suc 0" and elem':"b \<in> A"
    from cardSuc have "~(card A = 0)" by simp
    from contrapos_nn[OF this card_infinite[of A]] have "finite A" by fastsimp
    with elem cardSuc have "A - {a} = {}"
      by -(frule card_Diff_singleton,simp+)
    with elem' have "a = b" by auto }
  hence 2:"\<And>b. \<lbrakk>a \<in> A; card A = Suc 0; b \<in> A\<rbrakk> \<Longrightarrow> a = b" by simp
  from elem show ?thesis by (auto intro:1 2)
qed



constdefs
  pick ::"'a set \<Rightarrow> 'a"
  "pick A \<equiv> SOME x. x \<in> A"


lemma pick_is_element:"x \<in> A \<Longrightarrow> pick A \<in> A"
by (unfold pick_def,rule_tac x="x" in someI)


constdefs
  set2list :: "'a set \<Rightarrow> 'a list"
  "set2list A \<equiv> fst (while (\<lambda>(Es,S). S \<noteq> {})
                       (\<lambda>(Es,S). let x = pick S in (x#Es,S-{x}))
                       ([],A) )"

lemma card_pick:"\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> Suc(card(A-{pick(A)})) = card A"
by (drule card_Suc_Diff1,auto dest!:pick_is_element simp:ex_in_conv)


lemma set2list_prop:"\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> 
  \<exists>xs. while (\<lambda>(Es,S). S \<noteq> {})
             (\<lambda>(Es,S). let x = pick S in (x#Es,S-{x}))
             ([],A) = (xs,{}) \<and> (set xs \<union> {} = A)"

apply(rule_tac P="(\<lambda>xs. (set(fst xs) \<union> snd xs = A))" and 
               r="measure (card o snd)"  in while_rule)
apply(auto dest:pick_is_element)
apply(auto dest:card_pick simp:ex_in_conv measure_def inv_image_def)
done


lemma set2list_correct:"\<lbrakk>finite A; A \<noteq> {}; set2list A = xs\<rbrakk> \<Longrightarrow> set xs = A"
by (auto dest:set2list_prop simp:set2list_def)



section {*@{text distinct_fst}*}
 
constdefs
  distinct_fst  :: "('a \<times> 'b) list \<Rightarrow> bool"
  "distinct_fst  \<equiv>  distinct \<circ> map fst"

lemma distinct_fst_Nil [simp]:
  "distinct_fst []"
 
apply (unfold distinct_fst_def)
apply (simp (no_asm))
done


lemma distinct_fst_Cons [simp]:
  "distinct_fst ((k,x)#kxs) = (distinct_fst kxs \<and> (\<forall>y. (k,y) \<notin> set kxs))"

apply (unfold distinct_fst_def)
apply (auto simp:image_def)
done


lemma map_of_SomeI:
  "\<lbrakk> distinct_fst kxs; (k,x) \<in> set kxs \<rbrakk> \<Longrightarrow> map_of kxs k = Some x"
by (induct kxs) (auto simp:fun_upd_apply)


section {* Using @{term list_all2} for relations *}

constdefs
  fun_of :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  "fun_of S \<equiv> \<lambda>x y. (x,y) \<in> S"

text {* Convenience lemmas *}

declare fun_of_def [simp]

lemma rel_list_all2_Cons [iff]:
  "list_all2 (fun_of S) (x#xs) (y#ys) = 
   ((x,y) \<in> S \<and> list_all2 (fun_of S) xs ys)"
  by simp

lemma rel_list_all2_Cons1:
  "list_all2 (fun_of S) (x#xs) ys = 
  (\<exists>z zs. ys = z#zs \<and> (x,z) \<in> S \<and> list_all2 (fun_of S) xs zs)"
  by (cases ys) auto

lemma rel_list_all2_Cons2:
  "list_all2 (fun_of S) xs (y#ys) = 
  (\<exists>z zs. xs = z#zs \<and> (z,y) \<in> S \<and> list_all2 (fun_of S) zs ys)"
  by (cases xs) auto

lemma rel_list_all2_refl:
  "(\<And>x. (x,x) \<in> S) \<Longrightarrow> list_all2 (fun_of S) xs xs"
  by (simp add: list_all2_refl)

lemma rel_list_all2_antisym:
  "\<lbrakk> (\<And>x y. \<lbrakk>(x,y) \<in> S; (y,x) \<in> T\<rbrakk> \<Longrightarrow> x = y); 
     list_all2 (fun_of S) xs ys; list_all2 (fun_of T) ys xs \<rbrakk> \<Longrightarrow> xs = ys"
  by (rule list_all2_antisym) auto

lemma rel_list_all2_trans: 
  "\<lbrakk> \<And>a b c. \<lbrakk>(a,b) \<in> R; (b,c) \<in> S\<rbrakk> \<Longrightarrow> (a,c) \<in> T;
    list_all2 (fun_of R) as bs; list_all2 (fun_of S) bs cs\<rbrakk> 
  \<Longrightarrow> list_all2 (fun_of T) as cs"
  by (rule list_all2_trans) auto

lemma rel_list_all2_update_cong:
  "\<lbrakk> i<size xs; list_all2 (fun_of S) xs ys; (x,y) \<in> S \<rbrakk> 
  \<Longrightarrow> list_all2 (fun_of S) (xs[i:=x]) (ys[i:=y])"
  by (simp add: list_all2_update_cong)

lemma rel_list_all2_nthD:
  "\<lbrakk> list_all2 (fun_of S) xs ys; p < size xs \<rbrakk> \<Longrightarrow> (xs!p,ys!p) \<in> S"
  by (drule list_all2_nthD) auto

lemma rel_list_all2I:
  "\<lbrakk> length a = length b; \<And>n. n < length a \<Longrightarrow> (a!n,b!n) \<in> S \<rbrakk> \<Longrightarrow> list_all2 (fun_of S) a b"
  by (erule list_all2_all_nthI) simp

declare fun_of_def [simp del]

end
