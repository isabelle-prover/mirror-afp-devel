(*  Title:       Preservation and respectfulness theorems for terminated coinductive lists
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Quotient preservation and respectfulness theorems for terminated coinductive lists *}

theory Quotient_TLList imports
  TLList
  "~~/src/HOL/Library/Quotient_Product"
  "~~/src/HOL/Library/Quotient_Sum"
  "~~/src/HOL/Library/Quotient_Set"
begin

subsection {* Rules for the Quotient package *}

lemma sum_case_preserve [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  and q3: "Quotient3 R3 Abs3 Rep3"
  shows "((Abs1 ---> Rep2) ---> (Abs3 ---> Rep2) ---> sum_map Rep1 Rep3 ---> Abs2) sum_case = sum_case"
using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2] Quotient3_abs_rep[OF q3]
by(simp add: fun_eq_iff split: sum.split)

lemma sum_case_preserve2 [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "((id ---> Rep) ---> (id ---> Rep) ---> id ---> Abs) sum_case = sum_case"
using Quotient3_abs_rep[OF q]
by(auto intro!: ext split: sum.split)

lemma prod_case_preserve [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  and q3: "Quotient3 R3 Abs3 Rep3"
  shows "((Abs1 ---> Abs2 ---> Rep3) ---> map_pair Rep1 Rep2 ---> Abs3) prod_case = prod_case"
using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2] Quotient3_abs_rep[OF q3]
by(simp add: fun_eq_iff split: prod.split)

lemma prod_case_preserve2 [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "((id ---> id ---> Rep) ---> id ---> Abs) prod_case = prod_case"
using Quotient3_abs_rep[OF q]
by(auto intro!: ext)

lemma id_preserve [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(Rep ---> Abs) id = id"
using Quotient3_abs_rep[OF assms]
by(auto intro: ext)

enriched_type tmap: tmap
   by(simp_all add: fun_eq_iff tmap_id_id tllist.map_comp')

lemma symp_tllist_all2: "\<lbrakk> symp R; symp S \<rbrakk> \<Longrightarrow> symp (tllist_all2 R S)"
by (rule sympI)(auto 4 3 simp add: tllist_all2_conv_all_tnth elim: sympE dest: lfinite_llength_enat not_lfinite_llength)

lemma transp_tllist_all2: "\<lbrakk> transp R; transp S \<rbrakk> \<Longrightarrow> transp (tllist_all2 R S)"
  by (rule transpI) (rule tllist_all2_trans)

lemma tllist_equivp [quot_equiv]:
  "\<lbrakk> equivp R; equivp S \<rbrakk> \<Longrightarrow> equivp (tllist_all2 R S)"
  by (simp add: equivp_reflp_symp_transp reflp_tllist_all2 symp_tllist_all2 transp_tllist_all2)

declare tllist_all2_eq [simp, id_simps]

lemma tmap_preserve [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  and q3: "Quotient3 R3 Abs3 Rep3"
  and q4: "Quotient3 R4 Abs4 Rep4"
  shows "((Abs1 ---> Rep2) ---> (Abs3 ---> Rep4) ---> tmap Rep1 Rep3 ---> tmap Abs2 Abs4) tmap = tmap"
  and "((Abs1 ---> id) ---> (Abs2 ---> id) ---> tmap Rep1 Rep2 ---> id) tmap = tmap"
using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2] Quotient3_abs_rep[OF q3] Quotient3_abs_rep[OF q4]
by(simp_all add: fun_eq_iff tllist.map_comp' o_def)

lemma tmap_respect [quot_respect]:
  "((R1 ===> R2) ===> (R3 ===> R4) ===> tllist_all2 R1 R3 ===> tllist_all2 R2 R4) tmap tmap"
proof -
  {
    fix f f' g g' ts ts'
    assume f: "(R1 ===> R2) f f'"
      and g: "(R3 ===> R4) g g'"
      and ts: "tllist_all2 R1 R3 ts ts'"
    from ts have "tllist_all2 R2 R4 (tmap f g ts) (tmap f' g' ts')"
      unfolding tllist_all2_tmap1 tllist_all2_tmap2
      apply(rule tllist_all2_mono)
      using f g by(auto elim: fun_relE)
    }
  thus ?thesis by (auto intro!: fun_relI)
qed

lemma Quotient3_tmap_Abs_Rep:
  "\<lbrakk>Quotient3 R1 Abs1 Rep1; Quotient3 R2 Abs2 Rep2\<rbrakk>
  \<Longrightarrow> tmap Abs1 Abs2 (tmap Rep1 Rep2 ts) = ts"
by(drule abs_o_rep)+(simp add: tllist.map_comp' tmap_id_id)

lemma Quotient3_tllist_all2_tmap_tmapI:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "tllist_all2 R1 R2 (tmap Rep1 Rep2 ts) (tmap Rep1 Rep2 ts)"
by(coinduct ts rule: tllist_all2_fun_coinduct)(auto simp add: Quotient3_rep_reflp[OF q1] Quotient3_rep_reflp[OF q2])

lemma tllist_all2_rel:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "tllist_all2 R1 R2 r s \<longleftrightarrow> (tllist_all2 R1 R2 r r \<and> tllist_all2 R1 R2 s s \<and> tmap Abs1 Abs2 r = tmap Abs1 Abs2 s)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI)
  assume "?lhs"
  thus "tllist_all2 R1 R2 r r"
    apply -
    apply(rule tllist_all2_reflI)
    apply(clarsimp simp add: in_tset_conv_tnth)
    apply(metis tllist_all2_tnthD Quotient3_rel [OF q1])
    apply(metis tllist_all2_tfinite1_terminalD Quotient3_rel [OF q2])
    done

  from `?lhs` show "tllist_all2 R1 R2 s s"
    apply -
    apply(rule tllist_all2_reflI)
    apply(clarsimp simp add: in_tset_conv_tnth)
    apply(metis tllist_all2_tnthD2 Quotient3_rel [OF q1])
    apply(metis tllist_all2_tfinite2_terminalD Quotient3_rel [OF q2])
    done

  from `?lhs` show "tmap Abs1 Abs2 r = tmap Abs1 Abs2 s"
    unfolding tmap_eq_tmap_conv_tllist_all2
    by(rule tllist_all2_mono)(metis Quotient3_rel[OF q1] Quotient3_rel[OF q2])+
next
  assume "?rhs"
  thus "?lhs"
    unfolding tmap_eq_tmap_conv_tllist_all2
    apply(clarsimp simp add: tllist_all2_conv_all_tnth)
    apply(subst Quotient3_rel[OF q1, symmetric])
    apply(subst Quotient3_rel[OF q2, symmetric])
    apply(auto 4 3 dest: lfinite_llength_enat not_lfinite_llength)
    done
qed
    
lemma tllist_quotient [quot_thm]:
  "\<lbrakk> Quotient3 R1 Abs1 Rep1; Quotient3 R2 Abs2 Rep2 \<rbrakk> 
  \<Longrightarrow> Quotient3 (tllist_all2 R1 R2) (tmap Abs1 Abs2) (tmap Rep1 Rep2)"
by(blast intro: Quotient3I dest: Quotient3_tmap_Abs_Rep Quotient3_tllist_all2_tmap_tmapI tllist_all2_rel)

declare [[mapQ3 tllist = (tllist_all2, tllist_quotient)]]

lemma Quotient_llist[quot_map]:
  assumes "Quotient R1 Abs1 Rep1 T1"
  and "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (tllist_all2 R1 R2) (tmap Abs1 Abs2) (tmap Rep1 Rep2) (tllist_all2 T1 T2)"
unfolding Quotient_alt_def
proof(intro conjI strip)
  from assms have 1: "\<And>x y. T1 x y \<Longrightarrow> Abs1 x = y"
    and 2: "\<And>x y. T2 x y \<Longrightarrow> Abs2 x = y"
    unfolding Quotient_alt_def by simp_all
  fix xs ys
  assume "tllist_all2 T1 T2 xs ys"
  thus "tmap Abs1 Abs2 xs = ys"
    by(coinduct xs ys rule: tllist_fun_coinduct_invar2)(auto simp add: 1 2 dest: tllist_all2_is_TNilD tllist_all2_tfinite1_terminalD tllist_all2_thdD intro: tllist_all2_ttlI)
next
  from assms have 1: "\<And>x. T1 (Rep1 x) x"
    and 2: "\<And>x. T2 (Rep2 x) x"
    unfolding Quotient_alt_def by simp_all
  fix xs
  show "tllist_all2 T1 T2 (tmap Rep1 Rep2 xs) xs"
    by(simp add: tllist_all2_tmap1 1 2 tllist_all2_refl)
next
  from assms have 1: "R1 = (\<lambda>x y. T1 x (Abs1 x) \<and> T1 y (Abs1 y) \<and> Abs1 x = Abs1 y)"
    and 2: "R2 = (\<lambda>x y. T2 x (Abs2 x) \<and> T2 y (Abs2 y) \<and> Abs2 x = Abs2 y)"
    unfolding Quotient_alt_def by(simp_all add: fun_eq_iff)
  fix xs ys
  show "tllist_all2 R1 R2 xs ys
    \<longleftrightarrow> tllist_all2 T1 T2 xs (tmap Abs1 Abs2 xs) \<and> 
    tllist_all2 T1 T2 ys (tmap Abs1 Abs2 ys) \<and> 
    tmap Abs1 Abs2 xs = tmap Abs1 Abs2 ys"
    unfolding 1 2 tmap_eq_tmap_conv_tllist_all2
    by(auto 4 3 simp add: tllist_all2_conv_all_tnth dest: lfinite_llength_enat not_lfinite_llength)
qed

lemma TCons_preserve [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep1 ---> (tmap Rep1 Rep2) ---> (tmap Abs1 Abs2)) TCons = TCons"
using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2] 
by(simp add: fun_eq_iff tllist.map_comp' o_def tmap_id_id[unfolded id_def])

lemma TCons_respect [quot_respect]:
  "(R ===> tllist_all2 R Q ===> tllist_all2 R Q) TCons TCons"
  by (auto intro!: fun_relI)

lemma TNil_preserve [quot_preserve]:
  assumes "Quotient3 R2 Abs2 Rep2"
  shows "(Rep2 ---> tmap Abs1 Abs2) TNil = TNil"
using Quotient3_abs_rep[OF assms]
by(simp add: fun_eq_iff)

lemma LNil_respect [quot_respect]:
  "(R2 ===> tllist_all2 R1 R2) TNil TNil"
  by auto

lemma tllist_all2_rsp: 
  assumes R1: "\<forall>x y. R1 x y \<longrightarrow> (\<forall>a b. R1 a b \<longrightarrow> S x a = T y b)"
  and R2: "\<forall>x y. R2 x y \<longrightarrow> (\<forall>a b. R2 a b \<longrightarrow> S' x a = T' y b)"
  and xsys: "tllist_all2 R1 R2 xs ys"
  and xs'ys': "tllist_all2 R1 R2 xs' ys'"
  shows "tllist_all2 S S' xs xs' = tllist_all2 T T' ys ys'"
proof
  assume "tllist_all2 S S' xs xs'"
  with xsys xs'ys'
  have "\<exists>xs xs'. tllist_all2 S S' xs xs' \<and> tllist_all2 R1 R2 xs ys \<and> tllist_all2 R1 R2 xs' ys'" by blast
  thus "tllist_all2 T T' ys ys'"
  proof(coinduct rule: tllist_all2_coinduct)
    case (tllist_all2 ys ys')
    then obtain xs xs' where "tllist_all2 S S' xs xs'" "tllist_all2 R1 R2 xs ys" "tllist_all2 R1 R2 xs' ys'"
      by blast
    thus ?case
      by cases (auto 4 4 simp add: tllist_all2_TCons1 tllist_all2_TCons2 tllist_all2_TNil1 tllist_all2_TNil2 dest: R1[rule_format] R2[rule_format])
  qed
next
  assume "tllist_all2 T T' ys ys'"
  with xsys xs'ys'
  have "\<exists>ys ys'. tllist_all2 T T' ys ys' \<and> tllist_all2 R1 R2 xs ys \<and> tllist_all2 R1 R2 xs' ys'" by blast
  thus "tllist_all2 S S' xs xs'"
  proof(coinduct rule: tllist_all2_coinduct)
    case (tllist_all2 xs xs')
    then obtain ys ys' where "tllist_all2 T T' ys ys'" "tllist_all2 R1 R2 xs ys" "tllist_all2 R1 R2 xs' ys'"
      by blast
    thus ?case
      by cases(auto 4 4 simp add: tllist_all2_TCons1 tllist_all2_TCons2 tllist_all2_TNil1 tllist_all2_TNil2 dest: R1[rule_format] R2[rule_format])
  qed
qed

lemma tllist_all2_respect [quot_respect]:
  "((R1 ===> R1 ===> op =) ===> (R2 ===> R2 ===> op =) ===>
    tllist_all2 R1 R2 ===> tllist_all2 R1 R2 ===> op =) tllist_all2 tllist_all2"
  by (simp add: tllist_all2_rsp Transfer.fun_rel_def)

lemma tllist_all2_prs:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "tllist_all2 ((Abs1 ---> Abs1 ---> id) P) ((Abs2 ---> Abs2 ---> id) Q)
                     (tmap Rep1 Rep2 ts) (tmap Rep1 Rep2 ts')
         \<longleftrightarrow> tllist_all2 P Q ts ts'"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
  proof(coinduct rule: tllist_all2_coinduct)
    case (tllist_all2 ts ts')
    thus ?case using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2]
      by(cases ts)(case_tac [!] ts', auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)
  qed
next
  assume ?rhs
  thus ?lhs
    apply(coinduct ts ts' rule: tllist_all2_fun_coinduct_invar2)
    using Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2]
    by(auto dest: tllist_all2_is_TNilD intro: tllist_all2_tfinite1_terminalD tllist_all2_thdD tllist_all2_ttlI)
qed

lemma tllist_all2_preserve [quot_preserve]:
  assumes "Quotient3 R1 Abs1 Rep1"
  and "Quotient3 R2 Abs2 Rep2"
  shows "((Abs1 ---> Abs1 ---> id) ---> (Abs2 ---> Abs2 ---> id) ---> 
          tmap Rep1 Rep2 ---> tmap Rep1 Rep2 ---> id) tllist_all2 = tllist_all2"
by(simp add: fun_eq_iff tllist_all2_prs[OF assms])

lemma tllist_all2_preserve2 [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "(tllist_all2 ((Rep1 ---> Rep1 ---> id) R1) ((Rep2 ---> Rep2 ---> id) R2)) = (op =)"
  by (simp add: fun_eq_iff map_fun_def comp_def Quotient3_rel_rep[OF q1] Quotient3_rel_rep[OF q2]
    tllist_all2_eq)

lemma tllist_corec_preserve [quot_preserve]: 
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  and q3: "Quotient3 R3 Abs3 Rep3"
  shows "((Abs1 ---> id) ---> (Abs1 ---> Rep2) ---> (Abs1 ---> Rep3) ---> (Abs1 ---> id) ---> (Abs1 ---> tmap Rep3 Rep2) ---> (Abs1 ---> Rep1) ---> Rep1 ---> tmap Abs3 Abs2) tllist_corec = tllist_corec"
  (is "?lhs = ?rhs")
proof(intro ext)
  fix IS_TNIL TNIL THD endORmore TTL_end TTL_more b
  show "?lhs IS_TNIL TNIL THD endORmore TTL_end TTL_more b = ?rhs IS_TNIL TNIL THD endORmore TTL_end TTL_more b"
    (is "?lhs' b = ?rhs' b")
    by(rule tllist_fun_coinduct[where f="?lhs'" and g="?rhs'" and x=b])(auto simp add: Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2] Quotient3_abs_rep[OF q3] Quotient3_tmap_Abs_Rep[OF q3 q2])
qed

end