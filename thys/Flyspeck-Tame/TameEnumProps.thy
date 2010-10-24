(*  Author:  Gertrud Bauer, Tobias Nipkow  *)

header "Properties of Tame Graph Enumeration (2)"

theory TameEnumProps
imports GeneratorProps
begin


text{* Completeness of filter for final graphs. *}

(*
lemma tame\<^isub>2_is_tame\<^isub>2: "tame\<^isub>2 g \<Longrightarrow> is_tame\<^isub>2 g"
apply(auto simp: is_tame\<^isub>2_def tame\<^isub>2_def ok3_def)
apply(fastsimp simp:eval_nat_numeral length_Suc_conv
  intro!:norm_eq_if_face_cong[OF congs_sym, THEN sym])
done
*)

lemma "help": "(EX x. (EX y:A. x = f y) & P x) = (EX y:A. P(f y))"
by blast

lemma tame\<^isub>3_is_tame\<^isub>3: "tame\<^isub>3 g \<Longrightarrow> is_tame\<^isub>3 g"
apply(clarsimp simp: tame\<^isub>3_def is_tame\<^isub>3_def eval_nat_numeral length_Suc_conv)
apply((erule allE)+, erule impE, blast)
apply(simp add: ok4_def ok42_def tame_quad_def norm_subset_def
  pr_iso_subseteq_def pr_iso_in_def image_def
  ex_disj_distrib bex_disj_distrib "help" conj_disj_distribL)
apply(erule disjE, rule disjI1)
apply(fastsimp intro!:norm_eq_if_face_cong simp:tameConf\<^isub>1_def)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>2_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>2_def dest!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>3_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>3_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>3_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>3_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>4_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp intro!:norm_eq_if_face_cong simp:tameConf\<^isub>1_def)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>2_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>2_def dest!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>3_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>3_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>3_def intro!:norm_eq_if_face_cong)
apply(rule disjI2, erule disjE, rule disjI1)
apply(fastsimp simp: tameConf\<^isub>3_def intro!:norm_eq_if_face_cong)
apply(rule disjI2)
apply(fastsimp simp: tameConf\<^isub>4_def intro!:norm_eq_if_face_cong)
done


lemma untame_negFin:
assumes pl: "inv g" and fin: "final g" and tame: "tame g"
shows "is_tame g"
proof (unfold is_tame_def, intro conjI)
  show "tame\<^isub>4\<^isub>5 g" using tame by(auto simp:tame_def)
next
  show "tame\<^isub>6 g" using tame by(auto simp:tame_def)
next
  show "tame\<^isub>8 g" using tame by(auto simp:tame_def)
next
  show "is_tame\<^isub>3 g" using tame by(simp add:tame_def tame\<^isub>3_is_tame\<^isub>3)
next
  from tame obtain w where adm: "admissible w g"
    and sqn: "\<Sum>\<^bsub>f \<in> faces g\<^esub> w f < squanderTarget" by(auto simp:tame_def tame\<^isub>7_def)
  moreover have "squanderLowerBound g \<le>  \<Sum>\<^bsub>f \<in> faces g\<^esub> w f"
    using pl fin tame adm sqn by (rule total_weight_lowerbound)

  ultimately show "is_tame\<^isub>7 g" by(auto simp:is_tame\<^isub>7_def)
qed


lemma next_tame_comp:
 "\<lbrakk> tame g; final g; Seed\<^bsub>p\<^esub> [next_tame1 p]\<rightarrow>* g \<rbrakk>
 \<Longrightarrow> Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g"
apply (unfold next_tame_def)
apply(rule filter_tame_succs[OF inv_inv_next_tame1])
     apply(simp add:next_tame1_def next_tame0_def finalGraph_def)
    apply(rule context_conjI)
     apply(simp)
    apply(blast dest:untame_negFin)
   apply assumption
  apply(rule inv_Seed)
 apply assumption+
done


end
