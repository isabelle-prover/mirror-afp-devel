(*  Title:       Preservation and respectfulness theorems for terminated coinductive lists
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Quotient preservation and respectfulness theorems for terminated coinductive lists *}

theory Quotient_TLList imports
  TLList
begin

lemma Basic_BNFs_sum_rel_Quotient_Sum_sum_rel:
  "Basic_BNFs.sum_rel = Quotient_Sum.sum_rel"
proof(intro ext)
  fix P Q x y
  show "Basic_BNFs.sum_rel P Q x y = Quotient_Sum.sum_rel P Q x y"
    by(cases "(P, Q, x, y)" rule: Quotient_Sum.sum_rel.cases) simp_all
qed

lemma OO_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_total B"
  shows "((A ===> B ===> op =) ===> (B ===> C ===> op =) ===> A ===> C ===> op =) op OO op OO"
unfolding OO_def[abs_def]
by transfer_prover


enriched_type tmap: tmap
   by(simp_all add: fun_eq_iff tmap_id_id tllist.map_comp')

subsection {* Relator for type @{typ "('a, 'b) tllist"} *}

lemma reflp_tllist_all2: 
  assumes R: "reflp R" and Q: "reflp Q"
  shows "reflp (tllist_all2 R Q)"
proof(rule reflpI)
  fix xs
  show "tllist_all2 R Q xs xs"
    apply(coinduct xs rule: tllist_all2_fun_coinduct)
    using assms by(auto elim: reflpE)
qed

lemma tllist_all2_left_total[reflexivity_rule]:
  assumes R: "left_total R"
  and S: "left_total S"
  shows "left_total (tllist_all2 R S)"
proof (rule left_totalI)
  fix xs
  have *: "\<And>x. R x (SOME y. R x y)"
    using R by(rule left_totalE)(rule someI_ex)
  have **: "\<And>x. S x (SOME y. S x y)"
    using S by(rule left_totalE)(rule someI_ex)

  have "tllist_all2 R S xs (tmap (\<lambda>x. SOME y. R x y) (\<lambda>x. SOME y. S x y) xs)"
    by(coinduct xs rule: tllist_all2_fun_coinduct)(auto simp add: * **)
  thus "\<exists>ys. tllist_all2 R S xs ys" ..
qed

lemma tllist_all2_right_total[transfer_rule]:
  assumes R: "right_total R"
  and S: "right_total S"
  shows "right_total (tllist_all2 R S)"
  unfolding right_total_def
proof
  fix ys
  have *: "\<And>y. R (SOME x. R x y) y"
    using assms unfolding right_total_def by - (rule someI_ex, blast)
  have **: "\<And>y. S (SOME x. S x y) y"
    using assms unfolding right_total_def by - (rule someI_ex, blast)

  have "tllist_all2 R S (tmap (\<lambda>y. SOME x. R x y) (\<lambda>y. SOME x. S x y) ys) ys"
    by(coinduct ys rule: tllist_all2_fun_coinduct)(auto simp add: * **)
  thus "\<exists>xs. tllist_all2 R S xs ys" ..
qed

lemma bi_total_tllist_all2 [transfer_rule]:
  "\<lbrakk> bi_total A; bi_total B \<rbrakk> \<Longrightarrow> bi_total (tllist_all2 A B)"
by(simp add: bi_total_conv_left_right tllist_all2_right_total tllist_all2_left_total)

lemma left_unique_tllist_all2 [transfer_rule]:
  assumes A: "left_unique A" and B: "left_unique B"
  shows "left_unique (tllist_all2 A B)"
proof(rule left_uniqueI)
  fix xs ys zs
  assume "tllist_all2 A B xs zs" "tllist_all2 A B ys zs"
  hence "\<exists>zs. tllist_all2 A B xs zs \<and> tllist_all2 A B ys zs" by auto
  thus "xs = ys"
    by(coinduct xs ys rule: tllist.strong_coinduct)(auto 4 3 dest: left_uniqueD[OF A] left_uniqueD[OF B] tllist_all2_is_TNilD tllist_all2_thdD tllist_all2_tfinite1_terminalD intro: tllist_all2_ttlI)
qed

lemma right_unique_tllist_all2 [transfer_rule]:
  assumes A: "right_unique A" and B: "right_unique B"
  shows "right_unique (tllist_all2 A B)"
proof(rule right_uniqueI)
  fix xs ys zs
  assume "tllist_all2 A B xs ys" "tllist_all2 A B xs zs"
  hence "\<exists>xs. tllist_all2 A B xs ys \<and> tllist_all2 A B xs zs" by auto
  thus "ys = zs"
    by(coinduct ys zs rule: tllist.strong_coinduct)(auto 4 3 dest: tllist_all2_is_TNilD right_uniqueD[OF B] right_uniqueD[OF A] tllist_all2_thdD tllist_all2_tfinite2_terminalD intro: tllist_all2_ttlI)
qed

lemma bi_unique_tllist_all2 [transfer_rule]:
  "\<lbrakk> bi_unique A; bi_unique B \<rbrakk> \<Longrightarrow> bi_unique (tllist_all2 A B)"
by(simp add: bi_unique_conv_left_right left_unique_tllist_all2 right_unique_tllist_all2)

lemma symp_tllist_all2: "\<lbrakk> symp R; symp S \<rbrakk> \<Longrightarrow> symp (tllist_all2 R S)"
by (rule sympI)(auto 4 3 simp add: tllist_all2_conv_all_tnth elim: sympE dest: lfinite_llength_enat not_lfinite_llength)

lemma transp_tllist_all2: "\<lbrakk> transp R; transp S \<rbrakk> \<Longrightarrow> transp (tllist_all2 R S)"
  by (rule transpI) (rule tllist_all2_trans)

lemma tllist_equivp [quot_equiv]:
  "\<lbrakk> equivp R; equivp S \<rbrakk> \<Longrightarrow> equivp (tllist_all2 R S)"
  by (simp add: equivp_reflp_symp_transp reflp_tllist_all2 symp_tllist_all2 transp_tllist_all2)

lemma tllist_all2_mono2 [relator_mono]:
  assumes "A \<le> B" and "C \<le> D"
  shows "(tllist_all2 A C) \<le> (tllist_all2 B D)"
using assms by(auto intro: tllist_all2_mono)

lemma tllist_all2_OO [relator_distr]:
  "tllist_all2 A B OO tllist_all2 A' B' = tllist_all2 (A OO A') (B OO B')"
by transfer(auto intro!: ext simp add: llist_all2_OO[symmetric] dest: llist_all2_lfiniteD)

declare tllist_all2_eq [simp, id_simps, relator_eq]

subsection {* Transfer rules for transfer package *}

lemma pre_tllist_set1_transfer [transfer_rule]:
  "(sum_rel A (prod_rel B C) ===> set_rel B) pre_tllist_set1 pre_tllist_set1"
unfolding Basic_BNFs_sum_rel_Quotient_Sum_sum_rel[symmetric]
by(auto simp add: Transfer.fun_rel_def pre_tllist_set1_def set_rel_def collect_def sum_set_defs Basic_BNFs.sum_rel_def fsts_def split: sum.split_asm)

lemma pre_tllist_set2_transfer [transfer_rule]:
  "(sum_rel A (prod_rel B C) ===> set_rel A) pre_tllist_set2 pre_tllist_set2"
unfolding Basic_BNFs_sum_rel_Quotient_Sum_sum_rel[symmetric]
by(auto simp add: Transfer.fun_rel_def pre_tllist_set2_def set_rel_def collect_def sum_set_defs snds_def Basic_BNFs.sum_rel_def split: sum.split_asm)

lemma pre_tllist_set3_transfer [transfer_rule]:
  "(sum_rel A (prod_rel B C) ===> set_rel C) pre_tllist_set3 pre_tllist_set3"
unfolding Basic_BNFs_sum_rel_Quotient_Sum_sum_rel[symmetric]
by(auto simp add: Transfer.fun_rel_def pre_tllist_set3_def set_rel_def collect_def sum_set_defs snds_def Basic_BNFs.sum_rel_def split: sum.split_asm)

lemma tllist_Hset1_transfer [transfer_rule]:
  "((A ===> sum_rel B (prod_rel C A)) ===> A ===> set_rel C) tllist_Hset1 tllist_Hset1"
by(unfold tllist_Hset1_def[abs_def] tllist_Hset_rec1_def) transfer_prover

lemma tllist_dtor_transfer [transfer_rule]:
  "(tllist_all2 A B ===> sum_rel B (prod_rel A (tllist_all2 A B))) tllist_dtor tllist_dtor"
unfolding Basic_BNFs_sum_rel_Quotient_Sum_sum_rel[symmetric]
apply(rule fun_relI)
apply(erule tllist_all2_cases)
apply(auto simp add: Basic_BNFs.sum_rel_def TNil_def TCons_def tllist.dtor_ctor split: sum.split)
done

lemma TNil_transfer [transfer_rule]: "(B ===> tllist_all2 A B) TNil TNil"
by auto

lemma TCons_transfer [transfer_rule]:
  "(A ===> tllist_all2 A B ===> tllist_all2 A B) TCons TCons"
unfolding Transfer.fun_rel_def by simp

lemma tllist_case_transfer [transfer_rule]:
  "((B ===> C) ===> (A ===> tllist_all2 A B ===> C) ===> tllist_all2 A B ===> C)
    tllist_case tllist_case"
unfolding Transfer.fun_rel_def
by (simp add: tllist_all2_TNil1 tllist_all2_TNil2 split: tllist.split)

lemma tllist_unfold_transfer [transfer_rule]:
  "((A ===> op =) ===> (A ===> B) ===> (A ===> C) ===> (A ===> A) ===> A ===> tllist_all2 C B) tllist_unfold tllist_unfold"
apply(rule fun_relI)+
apply(erule tllist_all2_fun_coinduct_invar2[where X=A])
apply(auto 4 4 elim: fun_relE)
done

lemma llist_corec_transfer [transfer_rule]:
  "((A ===> op =) ===> (A ===> B) ===> (A ===> C) ===> (A ===> op =) ===> (A ===> tllist_all2 C B) ===> (A ===> A) ===> A ===> tllist_all2 C B) tllist_corec tllist_corec"
apply(rule fun_relI)+
apply(erule tllist_all2_fun_coinduct_invar2[where X=A])
apply(auto 4 4 elim: fun_relE)
done

lemma ttl_transfer [transfer_rule]:
  "(tllist_all2 A B ===> tllist_all2 A B) ttl ttl"
  unfolding ttl_def[abs_def] by transfer_prover

lemma tset_transfer [transfer_rule]:
  "(tllist_all2 A B ===> set_rel A) tset tset"
  unfolding tllist_set1_def by transfer_prover

lemma tmap_transfer [transfer_rule]:
  "((A ===> B) ===> (C ===> D) ===> tllist_all2 A C ===> tllist_all2 B D) tmap tmap"
by(auto simp add: Transfer.fun_rel_def tllist_all2_tmap1 tllist_all2_tmap2 elim: tllist_all2_mono)

lemma is_TNil_transfer [transfer_rule]:
  "(tllist_all2 A B ===> op =) is_TNil is_TNil"
by(auto dest: tllist_all2_is_TNilD)

lemma tappend_transfer [transfer_rule]:
  "(tllist_all2 A B ===> (B ===> tllist_all2 A C) ===> tllist_all2 A C) tappend tappend"
by(auto intro: tllist_all2_tappendI elim: fun_relE)

lemma lappendt_transfer [transfer_rule]:
  "(llist_all2 A ===> tllist_all2 A B ===> tllist_all2 A B) lappendt lappendt"
unfolding Transfer.fun_rel_def
by transfer(auto intro: llist_all2_lappendI)

lemma llist_of_tllist_transfer [transfer_rule]:
  "(tllist_all2 A B ===> llist_all2 A) llist_of_tllist llist_of_tllist"
by(auto intro: llist_all2_tllist_of_llistI)

lemma tllist_of_llist_transfer [transfer_rule]:
  "(B ===> llist_all2 A ===> tllist_all2 A B) tllist_of_llist tllist_of_llist"
by(auto intro!: fun_relI)

lemma tlength_transfer [transfer_rule]:
  "(tllist_all2 A B ===> op =) tlength tlength"
by(auto dest: tllist_all2_tlengthD)

lemma tdropn_transfer [transfer_rule]:
  "(op = ===> tllist_all2 A B ===> tllist_all2 A B) tdropn tdropn"
unfolding Transfer.fun_rel_def
by transfer(auto intro: llist_all2_ldropnI)

lemma tfilter_transfer [transfer_rule]:
  "(B ===> (A ===> op =) ===> tllist_all2 A B ===> tllist_all2 A B) tfilter tfilter"
unfolding Transfer.fun_rel_def
by transfer(auto intro: llist_all2_lfilterI dest: llist_all2_lfiniteD)

lemma tconcat_transfer [transfer_rule]:
  "(B ===> tllist_all2 (llist_all2 A) B ===> tllist_all2 A B) tconcat tconcat"
unfolding Transfer.fun_rel_def
by transfer(auto intro: llist_all2_lconcatI dest: llist_all2_lfiniteD)


subsection {* Setup for quotient package *}

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

declare [[mapQ3 tllist = (tllist_rel, tllist_quotient)]]

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