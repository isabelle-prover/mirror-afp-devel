(*  Title:       Preservation and respectfulness theorems for coinductive lists
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Quotient preservation and respectfulness theorems for coinductive lists *}

theory Quotient_Coinductive_List imports
  Quotient_Syntax
  Coinductive_List_Lib
begin

lemma transpD: "\<lbrakk> transp R; R a b; R b c \<rbrakk> \<Longrightarrow> R a c"
  by (erule transpE) blast

lemma id_respect [quot_respect]:
  "(R ===> R) id id"
  by (fact id_rsp)

lemma id_preserve [quot_preserve]:
  assumes "Quotient R Abs Rep"
  shows "(Rep ---> Abs) id = id"
  using Quotient_abs_rep [OF assms] by (simp add: fun_eq_iff)

;enriched_type lmap: lmap
   by (simp_all add: fun_eq_iff id_def)

declare [[map llist = (lmap, llist_all2)]]

lemma reflp_llist_all2: "reflp R \<Longrightarrow> reflp (llist_all2 R)"
  by (auto intro!: reflpI elim: reflpE simp add: llist_all2_conv_all_lnth)

lemma symp_llist_all2: "symp R \<Longrightarrow> symp (llist_all2 R)"
  by (rule sympI) (auto simp add: llist_all2_conv_all_lnth elim: sympE)

lemma llist_all2_trans:
  "\<lbrakk> llist_all2 P xs ys; llist_all2 P ys zs; transp P \<rbrakk>
  \<Longrightarrow> llist_all2 P xs zs"
apply(rule llist_all2_all_lnthI)
 apply(simp add: llist_all2_llengthD)
apply(frule llist_all2_llengthD)
apply(drule (1) llist_all2_lnthD)
apply(drule llist_all2_lnthD)
 apply simp
apply(erule (2) transpD)
done

lemma transp_llist_all2: "transp R \<Longrightarrow> transp (llist_all2 R)"
  by (rule transpI) (rule llist_all2_trans)

lemma llist_equivp [quot_equiv]:
  "equivp R \<Longrightarrow> equivp (llist_all2 R)"
  by (simp add: equivp_reflp_symp_transp reflp_llist_all2 symp_llist_all2 transp_llist_all2)

lemma Quotient_lmap_Abs_Rep:
  "Quotient R Abs Rep \<Longrightarrow> lmap Abs (lmap Rep a) = a"
  by (drule abs_o_rep) (simp add: lmap_id lmap_compose [symmetric] del: lmap_compose)

lemma llist_all2_rel:
  assumes "Quotient R Abs Rep"
  shows "llist_all2 R r s \<longleftrightarrow> llist_all2 R r r \<and> llist_all2 R s s \<and> (lmap Abs r = lmap Abs s)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  hence "llist_all2 R r r"
    apply -
    apply(rule llist_all2_reflI)
    apply(clarsimp simp add: lset_def)
    apply(metis Quotient_rel[OF assms] llist_all2_lnthD)
    done
  moreover from `?lhs` have "llist_all2 R s s"
    apply -
    apply(rule llist_all2_reflI)
    apply(clarsimp simp add: lset_def)
    apply(metis Quotient_rel[OF assms] llist_all2_lnthD2)
    done
  moreover from `?lhs` have "llength r = llength s" by(rule llist_all2_llengthD)
  hence "lmap Abs r = lmap Abs s" using `?lhs`
    unfolding lmap_eq_lmap_conv_llist_all2
    apply -
    apply(erule llist_all2_all_lnthI)
    apply(drule (1) llist_all2_lnthD)
    apply(metis Quotient_rel[OF assms])
    done
  ultimately show ?rhs by blast
next
  assume ?rhs thus ?lhs
    unfolding lmap_eq_lmap_conv_llist_all2
    by(clarsimp simp add: llist_all2_conv_all_lnth)(metis Quotient_rel[OF assms])
qed

lemma Quotient_llist_all2_lmap_Rep:
  "Quotient R Abs Rep \<Longrightarrow> llist_all2 R (lmap Rep a) (lmap Rep a)"
by(auto intro!: llist_all2_all_lnthI intro: Quotient_rep_reflp)

lemma llist_quotient [quot_thm]:
  "Quotient R Abs Rep \<Longrightarrow> Quotient (llist_all2 R) (lmap Abs) (lmap Rep)"
by(blast intro: QuotientI dest: Quotient_lmap_Abs_Rep Quotient_llist_all2_lmap_Rep llist_all2_rel)

lemma LCons_preserve [quot_preserve]:
  assumes "Quotient R Abs Rep"
  shows "(Rep ---> (lmap Rep) ---> (lmap Abs)) LCons = LCons"
using Quotient_abs_rep[OF assms]
by(simp add: fun_eq_iff lmap_compose[symmetric] o_def del: lmap_compose)

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
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "((abs1 ---> rep2) ---> (lmap rep1) ---> (lmap abs2)) lmap = lmap"
  and   "((abs1 ---> id) ---> lmap rep1 ---> id) lmap = lmap"
using Quotient_abs_rep[OF a] Quotient_abs_rep[OF b]
by(simp_all add: fun_eq_iff lmap_compose[symmetric] o_def del: lmap_compose)

lemma lmap_respect [quot_respect]:
  shows "((R1 ===> R2) ===> (llist_all2 R1) ===> llist_all2 R2) lmap lmap"
  and   "((R1 ===> op =) ===> (llist_all2 R1) ===> op =) lmap lmap"
  by (simp_all add: llist_all2_conv_all_lnth lmap_eq_lmap_conv_llist_all2 fun_rel_def)

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
  by (simp add: llist_all2_rsp fun_rel_def)

lemma llist_all2_preserve [quot_preserve]:
  assumes "Quotient R Abs Rep"
  shows "((Abs ---> Abs ---> id) ---> lmap Rep ---> lmap Rep ---> id) llist_all2 = llist_all2"
using Quotient_abs_rep[OF assms]
by(simp add: fun_eq_iff llist_all2_lmap1 llist_all2_lmap2)

lemma llist_all2_eq [id_simps]: "llist_all2 (op =) = (op =)"
proof(intro ext iffI)
  fix xs ys
  assume "llist_all2 (op =) xs ys"
  hence "(xs, ys) \<in> {(xs, ys). llist_all2 (op =) xs ys}" by blast
  thus "xs = ys"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs ys where "q = (xs, ys)" "llist_all2 (op =) xs ys" by blast
    thus ?case
      by(cases xs)(case_tac [2] ys, auto simp add: llist_all2_LNil1)
  qed
next
  fix xs ys :: "'a llist"
  assume "xs = ys"
  thus "llist_all2 (op =) xs ys"
    by(simp add: llist_all2_conv_all_lnth)
qed

lemma llist_all2_preserve2 [quot_preserve]:
  assumes "Quotient R Abs Rep"
  shows "(llist_all2 ((Rep ---> Rep ---> id) R) l m) = (l = m)"
  by (simp add: map_fun_def_raw Quotient_rel_rep [OF assms] llist_all2_eq comp_def)

lemma llist_corec_preserve [quot_preserve]: 
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  shows "(Rep1 ---> (Abs1 ---> Option.map (map_pair Rep2 Rep1)) ---> lmap Abs2) llist_corec = llist_corec"
proof(intro ext)
  fix a f
  let ?fmap = "Rep1 ---> (Abs1 ---> Option.map (map_pair Rep2 Rep1)) ---> lmap Abs2"
  have "(?fmap llist_corec a f, llist_corec a f) \<in>
        {(?fmap llist_corec a f, llist_corec a f)|a. True}" by blast
  thus "?fmap llist_corec a f = llist_corec a f"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain a where q: "q = (?fmap llist_corec a f, llist_corec a f)" by blast
    show ?case
    proof(cases "f a")
      case None
      hence ?EqLNil unfolding q
        using Quotient_abs_rep[OF q1] by(simp add: llist_corec)
      thus ?thesis ..
    next
      case (Some a')
      hence ?EqLCons
        unfolding q using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2]
        by(cases a')(simp, subst (1 2) llist_corec, auto)
      thus ?thesis ..
    qed
  qed
qed

end
