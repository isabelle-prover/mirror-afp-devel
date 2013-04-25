(*  Title:       Preservation and respectfulness theorems for coinductive lists
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Quotient preservation and respectfulness theorems for coinductive lists *}

theory Quotient_Coinductive_List imports
  "~~/src/HOL/Library/Quotient_List"
  "~~/src/HOL/Library/Quotient_Set"
  Coinductive_List
begin

lemma transpD: "\<lbrakk> transp R; R a b; R b c \<rbrakk> \<Longrightarrow> R a c"
  by (erule transpE) blast

lemma bi_total_conv_left_right: "bi_total R \<longleftrightarrow> left_total R \<and> right_total R"
by(simp add: left_total_def right_total_def bi_total_def)

lemma bi_unique_conv_left_right: "bi_unique R \<longleftrightarrow> left_unique R \<and> right_unique R"
by(auto simp add: left_unique_def right_unique_def bi_unique_def)

lemma bi_uniqueDr: "\<lbrakk> bi_unique A; A x y; A x z \<rbrakk> \<Longrightarrow> y = z"
by(simp add: bi_unique_def)

lemma bi_uniqueDl: "\<lbrakk> bi_unique A; A x y; A z y \<rbrakk> \<Longrightarrow> x = z"
by(simp add: bi_unique_def)

lemma right_uniqueI: "(\<And>x y z. \<lbrakk> A x y; A x z \<rbrakk> \<Longrightarrow> y = z) \<Longrightarrow> right_unique A"
unfolding right_unique_def by blast

lemma right_uniqueD: "\<lbrakk> right_unique A; A x y; A x z \<rbrakk> \<Longrightarrow> y = z"
unfolding right_unique_def by blast

lemma left_uniqueI: "(\<And>x y z. \<lbrakk> A x z; A y z \<rbrakk> \<Longrightarrow> x = y) \<Longrightarrow> left_unique A"
unfolding left_unique_def by blast

lemma left_uniqueD: "\<lbrakk> left_unique A; A x z; A y z \<rbrakk> \<Longrightarrow> x = y"
unfolding left_unique_def by blast


lemma id_respect [quot_respect]:
  "(R ===> R) id id"
  by (fact id_rsp)

lemma id_preserve [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(Rep ---> Abs) id = id"
  using Quotient3_abs_rep [OF assms] by (simp add: fun_eq_iff)

enriched_type lmap: lmap
   by (simp_all add: fun_eq_iff id_def llist.map_comp')

declare lmap_id [id_simps]

subsection {* Relator for type @{typ "'a llist"} *}

lemma reflp_llist_all2 [reflexivity_rule]: "reflp R \<Longrightarrow> reflp (llist_all2 R)"
  by (auto intro!: reflpI elim: reflpE simp add: llist_all2_conv_all_lnth)

lemma llist_all2_left_total [reflexivity_rule]:
  assumes "left_total R"
  shows "left_total (llist_all2 R)"
proof (rule left_totalI)
  fix xs
  have *: "\<And>x. R x (SOME y. R x y)"
    using assms by(rule left_totalE)(rule someI_ex)

  have "llist_all2 R xs (lmap (\<lambda>x. SOME y. R x y) xs)"
    by(coinduct xs rule: llist_all2_fun_coinduct)(auto simp add: *)
  thus "\<exists>ys. llist_all2 R xs ys" ..
qed

lemma llist_all2_right_total [transfer_rule]:
  assumes "right_total R"
  shows "right_total (llist_all2 R)"
  unfolding right_total_def
proof
  fix ys
  have *: "\<And>y. R (SOME x. R x y) y"
    using assms unfolding right_total_def by - (rule someI_ex, blast)

  have "llist_all2 R (lmap (\<lambda>y. SOME x. R x y) ys) ys"
    by(coinduct ys rule: llist_all2_fun_coinduct)(auto simp add: *)
  thus "\<exists>xs. llist_all2 R xs ys" ..
qed

lemma bi_total_llist_all2 [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (llist_all2 A)"
by(simp add: bi_total_conv_left_right llist_all2_right_total llist_all2_left_total)

lemma right_unique_llist_all2 [transfer_rule]:
  assumes "right_unique A"
  shows "right_unique (llist_all2 A)"
proof(rule right_uniqueI)
  fix xs ys zs
  assume "llist_all2 A xs ys" "llist_all2 A xs zs"
  hence "\<exists>xs. llist_all2 A xs ys \<and> llist_all2 A xs zs" by auto
  thus "ys = zs"
    by(coinduct ys zs rule: llist_strong_coinduct)(auto simp add: neq_LNil_conv llist_all2_LCons1 llist_all2_LCons2 dest: right_uniqueD[OF assms])
qed

lemma left_unique_llist_all2 [transfer_rule]:
  assumes "left_unique A"
  shows "left_unique (llist_all2 A)"
proof(rule left_uniqueI)
  fix xs ys zs
  assume "llist_all2 A xs zs" "llist_all2 A ys zs"
  hence "\<exists>zs. llist_all2 A xs zs \<and> llist_all2 A ys zs" by auto
  thus "xs = ys"
    by(coinduct xs ys rule: llist_strong_coinduct)(auto simp add: neq_LNil_conv llist_all2_LCons1 llist_all2_LCons2 dest: left_uniqueD[OF assms])
qed

lemma bi_unique_list_all2 [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (llist_all2 A)"
unfolding bi_unique_conv_left_right
by(simp add: right_unique_llist_all2 left_unique_llist_all2)

lemma symp_llist_all2: "symp R \<Longrightarrow> symp (llist_all2 R)"
  by (rule sympI) (auto simp add: llist_all2_conv_all_lnth elim: sympE)

lemma transp_llist_all2: "transp R \<Longrightarrow> transp (llist_all2 R)"
  by (rule transpI) (rule llist_all2_trans)

lemma llist_equivp [quot_equiv]:
  "equivp R \<Longrightarrow> equivp (llist_all2 R)"
  by (simp add: equivp_reflp_symp_transp reflp_llist_all2 symp_llist_all2 transp_llist_all2)

subsection {* Transfer rules for transfer package *}

lemma pre_llist_set1_transfer [transfer_rule]:
  "(sum_rel op = (prod_rel A B) ===> set_rel A) pre_llist_set1 pre_llist_set1"
by(auto simp add: Transfer.fun_rel_def pre_llist_set1_def set_rel_def collect_def sum_set_defs fsts_def sum_rel_def split: sum.split_asm)

lemma pre_llist_set2_transfer [transfer_rule]:
  "(sum_rel op = (prod_rel A B) ===> set_rel B) pre_llist_set2 pre_llist_set2"
by(auto simp add: Transfer.fun_rel_def pre_llist_set2_def set_rel_def collect_def sum_set_defs snds_def sum_rel_def split: sum.split_asm)

lemma llist_Hset_transfer [transfer_rule]:
  "((A ===> sum_rel op = (prod_rel B A)) ===> A ===> set_rel B) llist_Hset llist_Hset"
by(unfold llist_Hset_def[abs_def] llist_Hset_rec_def) transfer_prover

lemma llist_dtor_transfer [transfer_rule]:
  "(llist_all2 A ===> sum_rel op = (prod_rel A (llist_all2 A))) llist_dtor llist_dtor"
apply(rule fun_relI)
apply(erule llist_all2_cases)
apply(auto simp add: sum_rel_def LNil_def LCons_def llist.dtor_ctor split: sum.split)
done

lemma LNil_transfer [transfer_rule]: "llist_all2 P LNil LNil"
by simp

lemma LCons_transfer [transfer_rule]:
  "(A ===> llist_all2 A ===> llist_all2 A) LCons LCons"
unfolding Transfer.fun_rel_def by simp

lemma llist_case_transfer [transfer_rule]:
  "(B ===> (A ===> llist_all2 A ===> B) ===> llist_all2 A ===> B)
    llist_case llist_case"
unfolding Transfer.fun_rel_def by (simp split: llist.split)

lemma llist_unfold_transfer [transfer_rule]:
  "((A ===> op =) ===> (A ===> B) ===> (A ===> A) ===> A ===> llist_all2 B) llist_unfold llist_unfold"
apply(rule fun_relI)+
apply(erule llist_all2_fun_coinduct_invar2[where X=A])
apply(auto 4 4 elim: fun_relE)
done

lemma llist_corec_transfer [transfer_rule]:
  "((A ===> op =) ===> (A ===> B) ===> (A ===> op =) ===> (A ===> llist_all2 B) ===> (A ===> A) ===> A ===> llist_all2 B) llist_corec llist_corec"
apply(rule fun_relI)+
apply(erule llist_all2_fun_coinduct_invar2[where X=A])
apply(auto 4 4 elim: fun_relE)
done

lemma ltl_transfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 A) ltl ltl"
  unfolding ltl_def[abs_def] by transfer_prover

lemma lset_transfer [transfer_rule]:
  "(llist_all2 A ===> set_rel A) lset lset"
  unfolding llist_set_def by transfer_prover

lemma lmap_transfer [transfer_rule]:
  "((A ===> B) ===> llist_all2 A ===> llist_all2 B) lmap lmap"
by(auto simp add: Transfer.fun_rel_def llist_all2_lmap1 llist_all2_lmap2 elim: llist_all2_mono)

lemma lappend_transfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 A ===> llist_all2 A) lappend lappend"
by(auto simp add: Transfer.fun_rel_def intro: llist_all2_lappendI)

lemma iterates_transfer [transfer_rule]:
  "((A ===> A) ===> A ===> llist_all2 A) iterates iterates"
unfolding iterates_def by transfer_prover

lemma lfinite_transfer [transfer_rule]:
  "(llist_all2 A ===> op =) lfinite lfinite"
by(auto dest: llist_all2_lfiniteD)

lemma llist_of_transfer [transfer_rule]:
  "(list_all2 A ===> llist_all2 A) llist_of llist_of"
unfolding llist_of_def by transfer_prover

lemma llength_transfer [transfer_rule]:
  "(llist_all2 A ===> op =) llength llength"
by(auto dest: llist_all2_llengthD)


lemma ltake_transfer [transfer_rule]:
  "(op = ===> llist_all2 A ===> llist_all2 A) ltake ltake"
by(auto intro: llist_all2_ltakeI)

lemma ldropn_transfer [transfer_rule]:
  "(op = ===> llist_all2 A ===> llist_all2 A) ldropn ldropn"
unfolding ldropn_def[abs_def] by transfer_prover


lemma ldrop_transfer [transfer_rule]:
  "(op = ===> llist_all2 A ===> llist_all2 A) ldrop ldrop"
by(auto intro: llist_all2_ldropI)

lemma ltakeWhile_transfer [transfer_rule]:
  "((A ===> op =) ===> llist_all2 A ===> llist_all2 A) ltakeWhile ltakeWhile"
proof(rule fun_relI)+
  fix P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool" and xs :: "'a llist" and ys :: "'b llist"
  assume PQ: "(A ===> op =) P Q"
  assume "llist_all2 A xs ys"
  thus "llist_all2 A (ltakeWhile P xs) (ltakeWhile Q ys)"
    apply(coinduct xs ys rule: llist_all2_fun_coinduct_invar2)
    using PQ by(auto 4 4 elim: fun_relE simp add: neq_LNil_conv llist_all2_LCons2 llist_all2_LCons1)
qed

lemma ldropWhile_transfer [transfer_rule]:
  "((A ===> op =) ===> llist_all2 A ===> llist_all2 A) ldropWhile ldropWhile"
unfolding ldropWhile_def[abs_def] by transfer_prover

lemma lzip_ltransfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 B ===> llist_all2 (prod_rel A B)) lzip lzip"
by(auto intro: llist_all2_lzipI)

lemma inf_llist_transfer [transfer_rule]:
  "((op = ===> A) ===> llist_all2 A) inf_llist inf_llist"
unfolding inf_llist_def[abs_def] by transfer_prover

lemma lfilter_transfer [transfer_rule]:
  "((A ===> op =) ===> llist_all2 A ===> llist_all2 A) lfilter lfilter"
by(auto simp add: Transfer.fun_rel_def intro: llist_all2_lfilterI)

lemma lconcat_transfer [transfer_rule]:
  "(llist_all2 (llist_all2 A) ===> llist_all2 A) lconcat lconcat"
by(auto intro: llist_all2_lconcatI)

lemma lsublist_transfer [transfer_rule]:
  "(llist_all2 A ===> op = ===> llist_all2 A) lsublist lsublist"
unfolding lsublist_def[abs_def] by transfer_prover

subsection {* Setup for transfer package *}

lemma Quotient_llist [quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (llist_all2 R) (lmap Abs) (lmap Rep) (llist_all2 T)"
unfolding Quotient_alt_def
proof(intro conjI strip)
  from assms have 1: "\<And>x y. T x y \<Longrightarrow> Abs x = y"
    unfolding Quotient_alt_def by simp
  fix xs ys
  assume "llist_all2 T xs ys"
  thus "lmap Abs xs = ys"
    by(coinduct xs ys rule: llist_fun_coinduct_invar2)(auto simp add: neq_LNil_conv 1)
next
  from assms have 2: "\<And>x. T (Rep x) x"
    unfolding Quotient_alt_def by simp
  fix xs
  show "llist_all2 T (lmap Rep xs) xs" by(simp add: llist_all2_lmap1 2)
next
  from assms have 3: "R = (\<lambda>x y. T x (Abs x) \<and> T y (Abs y) \<and> Abs x = Abs y)"
    unfolding Quotient_alt_def by(simp add: fun_eq_iff)
  fix xs ys
  show "llist_all2 R xs ys \<longleftrightarrow> llist_all2 T xs (lmap Abs xs) \<and> llist_all2 T ys (lmap Abs ys) \<and> lmap Abs xs = lmap Abs ys"
    unfolding 3 lmap_eq_lmap_conv_llist_all2 by(auto simp add: llist_all2_conv_all_lnth)
qed

definition llist_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool"
where "llist_all P xs = (\<forall>x\<in>lset xs. P x)"

lemma llist_all_transfer [transfer_rule]:
  "((A ===> op =) ===> llist_all2 A ===> op =) llist_all llist_all"
  unfolding llist_all_def[abs_def] by transfer_prover

lemma llist_all2_invariant_commute [invariant_commute]:
  "llist_all2 (Lifting.invariant P) = Lifting.invariant (llist_all P)" (is "?lhs = ?rhs")
proof(intro ext iffI)
  fix xs ys
  assume "?lhs xs ys"
  moreover hence "llist_all2 op = xs ys"
    by(rule llist_all2_mono)(simp add: Lifting.invariant_def)
  ultimately show "?rhs xs ys" unfolding Lifting.invariant_def
    by(simp add: llist_all2_eq llist_all_def)
qed(simp add: Lifting.invariant_def llist_all_def)


subsection {* Rules for quotient package *}

lemma llist_unfold_preserve [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "((Abs1 ---> id) ---> (Abs1 ---> Rep2) ---> (Abs1 ---> Rep1) ---> Rep1 ---> lmap Abs2) llist_unfold = llist_unfold"
  (is "?lhs = ?rhs")
proof(intro ext)
  fix IS_LNIL LHD LTL a
  show "?lhs IS_LNIL LHD LTL a = ?rhs IS_LNIL LHD LTL a"
    by(coinduct a rule: llist_fun_coinduct)(auto simp add: Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2])
qed

lemma Quotient_lmap_Abs_Rep:
  "Quotient3 R Abs Rep \<Longrightarrow> lmap Abs (lmap Rep a) = a"
  by (drule abs_o_rep) (simp add: lmap_id llist.map_comp')

lemma llist_all2_rel:
  assumes "Quotient3 R Abs Rep"
  shows "llist_all2 R r s \<longleftrightarrow> llist_all2 R r r \<and> llist_all2 R s s \<and> (lmap Abs r = lmap Abs s)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  hence "llist_all2 R r r"
    apply -
    apply(rule llist_all2_reflI)
    apply(clarsimp simp add: lset_def)
    apply(metis Quotient3_rel[OF assms] llist_all2_lnthD)
    done
  moreover from `?lhs` have "llist_all2 R s s"
    apply -
    apply(rule llist_all2_reflI)
    apply(clarsimp simp add: lset_def)
    apply(metis Quotient3_rel[OF assms] llist_all2_lnthD2)
    done
  moreover from `?lhs` have "llength r = llength s" by(rule llist_all2_llengthD)
  hence "lmap Abs r = lmap Abs s" using `?lhs`
    unfolding lmap_eq_lmap_conv_llist_all2
    apply -
    apply(erule llist_all2_all_lnthI)
    apply(drule (1) llist_all2_lnthD)
    apply(metis Quotient3_rel[OF assms])
    done
  ultimately show ?rhs by blast
next
  assume ?rhs thus ?lhs
    unfolding lmap_eq_lmap_conv_llist_all2
    by(clarsimp simp add: llist_all2_conv_all_lnth simp del: llist_all2_same)(metis Quotient3_rel[OF assms])
qed

lemma Quotient_llist_all2_lmap_Rep:
  "Quotient3 R Abs Rep \<Longrightarrow> llist_all2 R (lmap Rep a) (lmap Rep a)"
by(auto intro!: llist_all2_all_lnthI intro: Quotient3_rep_reflp)

lemma llist_quotient [quot_thm]:
  "Quotient3 R Abs Rep \<Longrightarrow> Quotient3 (llist_all2 R) (lmap Abs) (lmap Rep)"
by(blast intro: Quotient3I dest: Quotient_lmap_Abs_Rep Quotient_llist_all2_lmap_Rep llist_all2_rel)

declare [[mapQ3 llist = (llist_rel, llist_quotient)]]

lemma LCons_preserve [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(Rep ---> (lmap Rep) ---> (lmap Abs)) LCons = LCons"
using Quotient3_abs_rep[OF assms]
by(simp add: fun_eq_iff llist.map_comp' o_def)

lemma LCons_respect [quot_respect]:
  "(R ===> llist_all2 R ===> llist_all2 R) LCons LCons"
  by (auto intro!: fun_relI)

lemma LNil_preserve [quot_preserve]:
  "lmap Abs LNil = LNil"
by simp

lemma LNil_respect [quot_respect]:
  "llist_all2 R LNil LNil"
by simp

lemma lmap_preserve [quot_preserve]:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> rep2) ---> (lmap rep1) ---> (lmap abs2)) lmap = lmap"
  and   "((abs1 ---> id) ---> lmap rep1 ---> id) lmap = lmap"
using Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b]
by(simp_all add: fun_eq_iff llist.map_comp' o_def)

lemma lmap_respect [quot_respect]:
  shows "((R1 ===> R2) ===> (llist_all2 R1) ===> llist_all2 R2) lmap lmap"
  and   "((R1 ===> op =) ===> (llist_all2 R1) ===> op =) lmap lmap"
by (simp_all add: llist_all2_conv_all_lnth lmap_eq_lmap_conv_llist_all2 Transfer.fun_rel_def)

lemma llist_all2_rsp:
  assumes r: "\<forall>x y. R x y \<longrightarrow> (\<forall>a b. R a b \<longrightarrow> S x a = T y b)"
  and l1: "llist_all2 R x y"
  and l2: "llist_all2 R a b"
  shows "llist_all2 S x a = llist_all2 T y b"
proof(cases "llength x = llength a")
  case True
  thus ?thesis using l1 l2 
    by(simp add: llist_all2_conv_all_lnth)(blast dest: r[rule_format])
next
  case False
  with llist_all2_llengthD[OF l1] llist_all2_llengthD[OF l2]
  show ?thesis by(simp add: llist_all2_conv_all_lnth)
qed

lemma llist_all2_respect [quot_respect]:
  "((R ===> R ===> op =) ===> llist_all2 R ===> llist_all2 R ===> op =) llist_all2 llist_all2"
  by (simp add: llist_all2_rsp Transfer.fun_rel_def)

lemma llist_all2_preserve [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "((Abs ---> Abs ---> id) ---> lmap Rep ---> lmap Rep ---> id) llist_all2 = llist_all2"
using Quotient3_abs_rep[OF assms]
by(simp add: fun_eq_iff llist_all2_lmap1 llist_all2_lmap2)

lemma llist_all2_preserve2 [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(llist_all2 ((Rep ---> Rep ---> id) R) l m) = (l = m)"
  by (simp add: map_fun_def [abs_def] Quotient3_rel_rep [OF assms] llist_all2_eq comp_def)

lemma llist_corec_preserve [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "((Abs1 ---> id) ---> (Abs1 ---> Rep2) ---> (Abs1 ---> id) ---> 
          (Abs1 ---> lmap Rep2) ---> (Abs1 ---> Rep1) ---> Rep1 ---> lmap Abs2) llist_corec = llist_corec"
  (is "?lhs = ?rhs")
proof(intro ext)
  fix IS_LNIL LHD endORmore LTL_end LTL_more b
  show "?lhs IS_LNIL LHD endORmore LTL_end LTL_more b = ?rhs IS_LNIL LHD endORmore LTL_end LTL_more b"
    by(coinduct b rule: llist_fun_coinduct)
      (auto simp add: Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2] Quotient_lmap_Abs_Rep[OF q2])
qed

end
