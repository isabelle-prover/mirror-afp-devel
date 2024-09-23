\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bounded Quantifiers\<close>
theory Bounded_Quantifiers
  imports
    HOL_Basics_Base
    Predicates_Lattice
    ML_Unification.ML_Unification_HOL_Setup
begin

consts ball :: "'a \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> bool"

bundle ball_syntax
begin
syntax
  "_ball"  :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close> (\<open>(2\<forall>_ : _./ _)\<close> 10)
  "_ball2" :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close>
notation ball (\<open>\<forall>(\<^bsub>_\<^esub>)\<close>)
end
bundle no_ball_syntax
begin
no_syntax
  "_ball"  :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close> (\<open>(2\<forall>_ : _./ _)\<close> 10)
  "_ball2" :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close>
no_notation ball (\<open>\<forall>(\<^bsub>_\<^esub>)\<close>)
end
unbundle ball_syntax
syntax_consts
  "_ball" "_ball2" \<rightleftharpoons> ball
translations
  "\<forall>x xs : P. Q" \<rightharpoonup> "CONST ball P (\<lambda>x. _ball2 xs P Q)"
  "_ball2 x P Q" \<rightharpoonup> "\<forall>x : P. Q"
  "\<forall>x : P. Q" \<rightleftharpoons> "CONST ball P (\<lambda>x. Q)"

consts bex :: "'a \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> bool"

bundle bex_syntax
begin
syntax
  "_bex"  :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close> (\<open>(2\<exists>_ : _./ _)\<close> 10)
  "_bex2" :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close>
notation bex (\<open>\<exists>(\<^bsub>_\<^esub>)\<close>)
end
bundle no_bex_syntax
begin
no_syntax
  "_bex"  :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close> (\<open>(2\<exists>_ : _./ _)\<close> 10)
  "_bex2" :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close>
no_notation bex (\<open>\<exists>(\<^bsub>_\<^esub>)\<close>)
end
unbundle bex_syntax
syntax_consts
  "_bex" "_bex2" \<rightleftharpoons> bex
translations
  "\<exists>x xs : P. Q" \<rightharpoonup> "CONST bex P (\<lambda>x. _bex2 xs P Q)"
  "_bex2 x P Q" \<rightharpoonup> "\<exists>x : P. Q"
  "\<exists>x : P. Q" \<rightleftharpoons> "CONST bex P (\<lambda>x. Q)"

consts bex1 :: "'a \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> bool"

bundle bex1_syntax
begin
syntax
  "_bex1"  :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close> (\<open>(2\<exists>!_ : _./ _)\<close> 10)
  "_bex12" :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close>
notation bex1 (\<open>\<exists>!(\<^bsub>_\<^esub>)\<close>)
end
bundle no_bex1_syntax
begin
no_syntax
  "_bex1"  :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close> (\<open>(2\<exists>!_ : _./ _)\<close> 10)
  "_bex12" :: \<open>[idts, 'a, bool] \<Rightarrow> bool\<close>
no_notation bex1 (\<open>\<exists>!(\<^bsub>_\<^esub>)\<close>)
end
unbundle bex1_syntax
syntax_consts
  "_bex1" "_bex12" \<rightleftharpoons> bex1
translations
  "\<exists>!x xs : P. Q" \<rightharpoonup> "CONST bex1 P (\<lambda>x. _bex12 xs P Q)"
  "_bex12 x P Q" \<rightharpoonup> "\<exists>!x : P. Q"
  "\<exists>!x : P. Q" \<rightleftharpoons> "CONST bex1 P (\<lambda>x. Q)"

bundle bounded_quantifier_syntax begin unbundle ball_syntax bex_syntax bex1_syntax end
bundle no_bounded_quantifier_syntax begin unbundle no_ball_syntax no_bex_syntax no_bex1_syntax end

definition "ball_pred P Q \<equiv> \<forall>x. P x \<longrightarrow> Q x"
adhoc_overloading ball ball_pred

definition "bex_pred P Q \<equiv> \<exists>x. P x \<and> Q x"
adhoc_overloading bex bex_pred

definition "bex1_pred P Q \<equiv> \<exists>!x. P x \<and> Q x"
adhoc_overloading bex1 bex1_pred

(*copied from HOL.Set.thy*)
simproc_setup defined_ball ("\<forall>x : P. Q x \<longrightarrow> U x") = \<open>
  K (Quantifier1.rearrange_Ball (fn ctxt => unfold_tac ctxt @{thms ball_pred_def}))
\<close>
simproc_setup defined_bex ("\<exists>x : P. Q x \<and> U x") = \<open>
  K (Quantifier1.rearrange_Bex (fn ctxt => unfold_tac ctxt @{thms bex_pred_def}))
\<close>

lemma ballI [intro!]:
  assumes "\<And>x. P x \<Longrightarrow> Q x"
  shows "\<forall>x : P. Q x"
  using assms unfolding ball_pred_def by blast

lemma ballE [elim]:
  assumes "\<forall>x : P. Q x"
  obtains "\<And>x. P x \<Longrightarrow> Q x"
  using assms unfolding ball_pred_def by blast

lemma ballE':
  assumes "\<forall>x : P. Q x"
  obtains "\<not>(P x)" | "P x" "Q x"
  using assms by blast

lemma ballD: "\<forall>x : P. Q x \<Longrightarrow> P x \<Longrightarrow> Q x"
  by blast

lemma ball_cong: "\<lbrakk>P = P'; \<And>x. P' x \<Longrightarrow> Q x \<longleftrightarrow> Q' x\<rbrakk> \<Longrightarrow> (\<forall>x : P. Q x) \<longleftrightarrow> (\<forall>x : P'. Q' x)"
  by auto

lemma ball_cong_simp [cong]:
  "\<lbrakk>P = P'; \<And>x. P' x =simp=> Q x \<longleftrightarrow> Q' x\<rbrakk> \<Longrightarrow> (\<forall>x : P. Q x) \<longleftrightarrow> (\<forall>x : P'. Q' x)"
  unfolding simp_implies_def by (rule ball_cong)

(*copied from HOL.Set.thy*)
ML \<open>
structure Simpdata =
struct
  open Simpdata
  val mksimps_pairs = [(\<^const_name>\<open>ball_pred\<close>, @{thms ballD})] @ mksimps_pairs
end
open Simpdata
\<close>
declaration \<open>fn _ => Simplifier.map_ss (Simplifier.set_mksimps (mksimps mksimps_pairs))\<close>

lemma atomize_ball: "(\<And>x. P x \<Longrightarrow> Q x) \<equiv> Trueprop (\<forall>x : P. Q x)"
  by (simp only: ball_pred_def atomize_all atomize_imp)

declare atomize_ball[symmetric, rulify]
declare atomize_ball[symmetric, defn]

lemma bexI [intro!]:
  (*better argument order: Q often determines the choice for x*)
  assumes "\<exists>x. Q x \<and> P x"
  shows "\<exists>x : P. Q x"
  using assms unfolding bex_pred_def by blast

lemma bexE [elim!]:
  assumes "\<exists>x : P. Q x"
  obtains x where "P x" "Q x"
  using assms unfolding bex_pred_def by blast

lemma bexD:
  assumes "\<exists>x : P. Q x"
  shows "\<exists>x. P x \<and> Q x"
  using assms by blast

lemma bex_cong:
  "\<lbrakk>P = P'; \<And>x. P' x \<Longrightarrow> Q x \<longleftrightarrow> Q' x\<rbrakk> \<Longrightarrow> (\<exists>x : P. Q x) \<longleftrightarrow> (\<exists>x : P'. Q' x)"
  by blast

lemma bex_cong_simp [cong]:
  "\<lbrakk>P = P'; \<And>x. P' x =simp=> Q x \<longleftrightarrow> Q' x\<rbrakk> \<Longrightarrow> (\<exists>x : P. Q x) \<longleftrightarrow> (\<exists>x : P'. Q' x)"
  unfolding simp_implies_def by (rule bex_cong)

lemma bex1I [intro]:
  (*better argument order: Q often determines the choice for x*)
  assumes "\<exists>!x. Q x \<and> P x"
  shows "\<exists>!x : P. Q x"
  using assms unfolding bex1_pred_def by blast

lemma bex1D [dest!]:
  assumes "\<exists>!x : P. Q x"
  shows "\<exists>!x. P x \<and> Q x"
  using assms unfolding bex1_pred_def by blast

lemma bex1_cong: "\<lbrakk>P = P'; \<And>x. P x \<Longrightarrow> Q x \<longleftrightarrow> Q' x\<rbrakk> \<Longrightarrow> (\<exists>!x : P. Q x) \<longleftrightarrow> (\<exists>!x : P'. Q' x)"
  by blast

lemma bex1_cong_simp [cong]:
  "\<lbrakk>P = P'; \<And>x. P x =simp=> Q x \<longleftrightarrow> Q' x\<rbrakk> \<Longrightarrow> (\<exists>!x : P. Q x) \<longleftrightarrow> (\<exists>!x : P'. Q' x)"
  unfolding simp_implies_def by (rule bex1_cong)

lemma ball_iff_ex_pred [iff]: "(\<forall>x : P. Q) \<longleftrightarrow> ((\<exists>x. P x) \<longrightarrow> Q)"
  by auto

lemma bex_iff_ex_and [iff]: "(\<exists>x : P. Q) \<longleftrightarrow> ((\<exists>x. P x) \<and> Q)"
  by blast

lemma ball_eq_imp_iff_imp [iff]: "(\<forall>x : P. x = y \<longrightarrow> Q x) \<longleftrightarrow> (P y \<longrightarrow> Q y)"
  by blast

lemma ball_eq_imp_iff_imp' [iff]: "(\<forall>x : P. y = x \<longrightarrow> Q x) \<longleftrightarrow> (P y \<longrightarrow> Q y)"
  by blast

lemma bex_eq_iff_pred [iff]: "(\<exists>x : P. x = y) \<longleftrightarrow> P y"
  by blast

lemma bex_eq_iff_pred' [iff]: "(\<exists>x : P. y = x) \<longleftrightarrow> P y"
  by blast

lemma bex_eq_and_iff_pred [iff]: "(\<exists>x : P. x = y \<and> Q x) \<longleftrightarrow> P y \<and> Q y"
  by blast

lemma bex_eq_and_iff_pred' [iff]: "(\<exists>x : P. y = x \<and> Q x) \<longleftrightarrow> P y \<and> Q y"
  by blast

lemma ball_and_iff_ball_and_ball: "(\<forall>x : P. Q x \<and> U x) \<longleftrightarrow> (\<forall>x : P. Q x) \<and> (\<forall>x : P. U x)"
  by auto

lemma bex_or_iff_bex_or_bex: "(\<exists>x : P. Q x \<or> U x) \<longleftrightarrow> (\<exists>x : P. Q x) \<or> (\<exists>x : P. U x)"
  by auto

lemma ball_or_iff_ball_or [iff]: "(\<forall>x : P. Q x \<or> U) \<longleftrightarrow> ((\<forall>x : P. Q x) \<or> U)"
  by auto

lemma ball_or_iff_or_ball [iff]: "(\<forall>x : P. Q \<or> U x) \<longleftrightarrow> (Q \<or> (\<forall>x : P. U x))"
  by auto

lemma ball_imp_iff_imp_ball [iff]: "(\<forall>x : P. Q \<longrightarrow> U x) \<longleftrightarrow> (Q \<longrightarrow> (\<forall>x : P. U x))"
  by auto

lemma bex_and_iff_bex_and [iff]: "(\<exists>x : P. Q x \<and> U) \<longleftrightarrow> ((\<exists>x : P. Q x) \<and> U)"
  by auto

lemma bex_and_iff_and_bex [iff]: "(\<exists>x : P. Q \<and> U x) \<longleftrightarrow> (Q \<and> (\<exists>x : P. U x))"
  by auto

lemma ball_imp_iff_bex_imp [iff]: "(\<forall>x : P. Q x \<longrightarrow> U) \<longleftrightarrow> ((\<exists>x : P. Q x) \<longrightarrow> U)"
  by auto

lemma not_ball_iff_bex_not [iff]: "(\<not>(\<forall>x : P. Q x)) \<longleftrightarrow> (\<exists>x : P. \<not>(Q x))"
  by auto

lemma not_bex_iff_ball_not [iff]: "(\<not>(\<exists>x : P. Q x)) \<longleftrightarrow> (\<forall>x : P. \<not>(Q x))"
  by auto

lemma bex1_iff_bex_and [iff]: "(\<exists>!x : P. Q) \<longleftrightarrow> ((\<exists>!x. P x) \<and> Q)"
  by auto

lemma ball_bottom_eq_top [simp]: "\<forall>\<^bsub>\<bottom>\<^esub> = \<top>" by auto
lemma bex_bottom_eq_bottom [simp]: "\<exists>\<^bsub>\<bottom>\<^esub> = \<bottom>" by fastforce
lemma bex1_bottom_eq_bottom [simp]: "\<exists>!\<^bsub>\<bottom>\<^esub> = \<bottom>" by fastforce

lemma ball_top_eq_all [simp]: "\<forall>\<^bsub>\<top>\<^esub> = All" by fastforce

lemma ball_top_eq_all_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "\<forall>\<^bsub>P\<^esub> \<equiv> All"
  using assms by simp

lemma bex_top_eq_ex [simp]: "\<exists>\<^bsub>\<top>\<^esub> = Ex" by fastforce

lemma bex_top_eq_ex_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "\<exists>\<^bsub>P\<^esub> \<equiv> Ex"
  using assms by simp

lemma bex1_top_eq_ex1 [simp]: "\<exists>!\<^bsub>\<top>\<^esub> = Ex1" by fastforce

lemma bex1_top_eq_ex1_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "\<exists>!\<^bsub>P\<^esub> \<equiv> Ex1"
  using assms by simp

end