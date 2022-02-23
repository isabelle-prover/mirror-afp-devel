(*<*)
theory Interval
  imports "HOL-Library.Product_Lexorder" Timestamp
begin
(*>*)

section \<open>Intervals\<close>

typedef (overloaded) ('a :: timestamp) \<I> = "{(i :: 'a, j :: 'a, lei :: bool, lej :: bool). 0 \<le> i \<and> i \<le> j \<and> i \<in> tfin \<and> \<not>(j = 0 \<and> \<not>lej)}"
  by (intro exI[of _ "(0, 0, True, True)"]) (auto intro: zero_tfin)

setup_lifting type_definition_\<I>

instantiation \<I> :: (timestamp) equal begin

lift_definition equal_\<I> :: "'a \<I> \<Rightarrow> 'a \<I> \<Rightarrow> bool" is "(=)" .

instance by standard (transfer, auto)

end

lift_definition right :: "'a :: timestamp \<I> \<Rightarrow> 'a" is "fst \<circ> snd" .

lift_definition memL :: "'a :: timestamp \<Rightarrow> 'a \<Rightarrow> 'a \<I> \<Rightarrow> bool" is
  "\<lambda>t t' (a, b, lei, lej). if lei then t + a \<le> t' else t + a < t'" .

lift_definition memR :: "'a :: timestamp \<Rightarrow> 'a \<Rightarrow> 'a \<I> \<Rightarrow> bool" is
  "\<lambda>t t' (a, b, lei, lej). if lej then t' \<le> t + b else t' < t + b" .

definition mem :: "'a :: timestamp \<Rightarrow> 'a \<Rightarrow> 'a \<I> \<Rightarrow> bool" where
  "mem t t' I \<longleftrightarrow> memL t t' I \<and> memR t t' I"

lemma memL_mono: "memL t t' I \<Longrightarrow> t'' \<le> t \<Longrightarrow> memL t'' t' I"
  by transfer (auto simp: add.commute order_le_less_subst2 order_subst2 add_mono split: if_splits)

lemma memL_mono': "memL t t' I \<Longrightarrow> t' \<le> t'' \<Longrightarrow> memL t t'' I"
  by transfer (auto split: if_splits)

lemma memR_mono: "memR t t' I \<Longrightarrow> t \<le> t'' \<Longrightarrow> memR t'' t' I"
  apply transfer
  apply (simp split: prod.splits)
  apply (meson add_mono_comm dual_order.trans order_less_le_trans)
  done

lemma memR_mono': "memR t t' I \<Longrightarrow> t'' \<le> t' \<Longrightarrow> memR t t'' I"
  by transfer (auto split: if_splits)

lemma memR_dest: "memR t t' I \<Longrightarrow> t' \<le> t + right I"
  by transfer (auto split: if_splits)

lemma memR_tfin_refl:
  assumes fin: "t \<in> tfin"
  shows "memR t t I"
  by (transfer fixing: t) (force split: if_splits intro: order_trans[OF _ add_mono, where ?x=t and ?a1=t and ?c1=0] add_pos[OF fin])

lemma right_I_add_mono:
  fixes x :: "'a :: timestamp"
  shows "x \<le> x + right I"
  by transfer (auto split: if_splits intro: order_trans[OF _ add_mono, of _ _ 0])

lift_definition interval :: "'a :: timestamp \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'a \<I>" is
  "\<lambda>i j lei lej. (if 0 \<le> i \<and> i \<le> j \<and> i \<in> tfin \<and> \<not>(j = 0 \<and> \<not>lej)then (i, j, lei, lej) else Code.abort (STR ''malformed interval'') (\<lambda>_. (0, 0, True, True)))"
  by (auto intro: zero_tfin)

lemma "Rep_\<I> I = (l, r, b1, b2) \<Longrightarrow> memL 0 0 I \<longleftrightarrow> l = 0 \<and> b1"
  by transfer auto

lift_definition dropL :: "'a :: timestamp \<I> \<Rightarrow> 'a \<I>" is
  "\<lambda>(l, r, b1, b2). (0, r, True, b2)"
  by (auto intro: zero_tfin)

lemma memL_dropL: "t \<le> t' \<Longrightarrow> memL t t' (dropL I)"
  by transfer auto

lemma memR_dropL: "memR t t' (dropL I) = memR t t' I"
  by transfer auto

lift_definition flipL :: "'a :: timestamp \<I> \<Rightarrow> 'a \<I>" is
  "\<lambda>(l, r, b1, b2). if \<not>(l = 0 \<and> b1) then (0, l, True, \<not>b1) else Code.abort (STR ''invalid flipL'') (\<lambda>_. (0, 0, True, True))"
  by (auto intro: zero_tfin split: if_splits)

lemma memL_flipL: "t \<le> t' \<Longrightarrow> memL t t' (flipL I)"
  by transfer (auto split: if_splits)

lemma memR_flipLD: "\<not>memL 0 0 I \<Longrightarrow> memR t t' (flipL I) \<Longrightarrow> \<not>memL t t' I"
  by transfer (auto split: if_splits)

lemma memR_flipLI:
  fixes t :: "'a :: timestamp"
  shows "(\<And>u v. (u :: 'a :: timestamp) \<le> v \<or> v \<le> u) \<Longrightarrow> \<not>memL t t' I \<Longrightarrow> memR t t' (flipL I)"
  by transfer (force split: if_splits)

lemma "t \<in> tfin \<Longrightarrow> memL 0 0 I \<longleftrightarrow> memL t t I"
  apply transfer
  apply (simp split: prod.splits)
  apply (metis add.right_neutral add_pos antisym_conv2 dual_order.eq_iff order_less_imp_not_less)
  done

definition "full (I :: ('a :: timestamp) \<I>) \<longleftrightarrow> (\<forall>t t'. 0 \<le> t \<and> t \<le> t' \<and> t \<in> tfin \<and> t' \<in> tfin \<longrightarrow> mem t t' I)"

lemma "memL 0 0 (I :: ('a :: timestamp_total) \<I>) \<Longrightarrow> right I \<notin> tfin \<Longrightarrow> full I"
  unfolding full_def mem_def
  by transfer (fastforce split: if_splits dest: add_not_tfin)

(*<*)
end
(*>*)
