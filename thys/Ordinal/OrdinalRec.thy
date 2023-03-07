(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Recursive Definitions\<close>

theory OrdinalRec
imports OrdinalCont
begin

definition
  oPrec :: "ordinal \<Rightarrow> ordinal" where
  "oPrec x = (THE p. x = oSuc p)"

lemma oPrec_oSuc [simp]: "oPrec (oSuc x) = x"
  by (simp add: oPrec_def)

lemma oPrec_less: "\<exists>p. x = oSuc p \<Longrightarrow> oPrec x < x"
  by clarsimp

definition
  ordinal_rec0 ::
    "['a, ordinal \<Rightarrow> 'a \<Rightarrow> 'a, (nat \<Rightarrow> 'a) \<Rightarrow> 'a, ordinal] \<Rightarrow> 'a" where
  "ordinal_rec0 z s l \<equiv> wfrec {(x,y). x < y} (\<lambda>F x.
    if x = 0 then z else
    if (\<exists>p. x = oSuc p) then s (oPrec x) (F (oPrec x)) else
    (THE y. \<forall>f. (\<forall>n. f n < oLimit f) \<and> oLimit f = x
            \<longrightarrow> l (\<lambda>n. F (f n)) = y))"

lemma ordinal_rec0_0 [simp]: "ordinal_rec0 z s l 0 = z"
  by (simp add: cut_apply def_wfrec[OF ordinal_rec0_def wf])

lemma ordinal_rec0_oSuc: "ordinal_rec0 z s l (oSuc x) = s x (ordinal_rec0 z s l x)"
  by (simp add: cut_apply def_wfrec[OF ordinal_rec0_def wf])

lemma limit_ordinal_not_0: "limit_ordinal x \<Longrightarrow> x \<noteq> 0" and limit_ordinal_not_oSuc: "limit_ordinal x \<Longrightarrow> x \<noteq> oSuc p"
  by auto


lemma ordinal_rec0_limit_ordinal:
"limit_ordinal x \<Longrightarrow> ordinal_rec0 z s l x =
 (THE y. \<forall>f. (\<forall>n. f n < oLimit f) \<and> oLimit f = x \<longrightarrow> 
   l (\<lambda>n. ordinal_rec0 z s l (f n)) = y)"
 apply (rule trans[OF def_wfrec[OF ordinal_rec0_def wf]])
 apply (simp add: limit_ordinal_not_oSuc limit_ordinal_not_0)
 apply (rule_tac f=The in arg_cong, rule ext)
 apply (rule_tac f=All in arg_cong, rule ext)
 apply safe
  apply (simp add: cut_apply)
 apply (simp add: cut_apply)
done


subsection \<open>Partial orders\<close>

locale porder =
  fixes le  :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "<<" 55)
assumes po_refl:    "\<And>x. x << x"
    and po_trans:   "\<And>x y z. \<lbrakk>x << y; y << z\<rbrakk> \<Longrightarrow> x << z"
    and po_antisym: "\<And>x y. \<lbrakk>x << y; y << x\<rbrakk> \<Longrightarrow> x = y"

lemma porder_order: "porder ((\<le>) :: 'a::order \<Rightarrow> 'a \<Rightarrow> bool)"
  using porder_def by fastforce

lemma (in porder) flip: "porder (\<lambda>x y. y << x)"
  by (metis (no_types, lifting) po_antisym po_refl po_trans porder_def)

locale omega_complete = porder +
  fixes lub :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  assumes is_ub_lub: "\<And>f n. f n << lub f"
  assumes is_lub_lub: "\<And>f x. \<forall>n. f n << x \<Longrightarrow> lub f << x"

lemma (in omega_complete) lub_cong_lemma:
"\<lbrakk>\<forall>n. f n < oLimit f; \<forall>m. g m < oLimit g; oLimit f \<le> oLimit g;
 \<forall>y<oLimit g. \<forall>x\<le>y. F x << F y\<rbrakk>
 \<Longrightarrow> lub (\<lambda>n. F (f n)) << lub (\<lambda>n. F (g n))"
 apply (rule is_lub_lub[rule_format])
  by (metis dual_order.trans is_ub_lub leD linorder_le_cases oLimit_leI po_trans)


lemma (in omega_complete) lub_cong:
"\<lbrakk>\<forall>n. f n < oLimit f; \<forall>m. g m < oLimit g; oLimit f = oLimit g;
 \<forall>y<oLimit g. \<forall>x\<le>y. F x << F y\<rbrakk>
 \<Longrightarrow> lub (\<lambda>n. F (f n)) = lub (\<lambda>n. F (g n))"
  by (simp add: lub_cong_lemma po_antisym)

lemma (in omega_complete) ordinal_rec0_mono:
  assumes s: "\<forall>p x. x << s p x" and "x \<le> y"
  shows "ordinal_rec0 z s lub x << ordinal_rec0 z s lub y"
proof -
  have "\<forall>y\<le>w. \<forall>x\<le>y. ordinal_rec0 z s lub x << ordinal_rec0 z s lub y" for w
  proof (induction w rule: oLimit_induct)
    case zero
    then show ?case
      by (simp add: po_refl)
  next
    case (suc x)
    then show ?case
      by (metis le_oSucE oSuc_le_oSuc ordinal_rec0_oSuc po_refl po_trans s)
  next
    case (lim f)
    then have "\<forall>g. (\<forall>n. g n < oLimit g) \<and> oLimit g = oLimit f \<longrightarrow>
             lub (\<lambda>n. ordinal_rec0 z s lub (g n)) =
             lub (\<lambda>n. ordinal_rec0 z s lub (f n))"
      by (metis linorder_not_le lub_cong oLimit_leI order_le_less strict_mono_less_oLimit)
    with lim have "ordinal_rec0 z s lub (oLimit f) =
                     lub (\<lambda>n. ordinal_rec0 z s lub (f n))"
      apply (simp add: ordinal_rec0_limit_ordinal strict_mono_limit_ordinal)
      by (smt (verit, del_insts) the_equality strict_mono_less_oLimit)
    then show ?case
      by (smt (verit, ccfv_SIG) is_ub_lub le_oLimitE lim.IH order_le_less po_refl po_trans)
  qed
  with assms show ?thesis
    by blast
qed

lemma (in omega_complete) ordinal_rec0_oLimit:
  assumes s: "\<forall>p x. x << s p x"
  shows "ordinal_rec0 z s lub (oLimit f) =
         lub (\<lambda>n. ordinal_rec0 z s lub (f n))"
proof (cases "\<forall>n. f n < oLimit f")
  case True
  then show ?thesis
    apply (simp add: ordinal_rec0_limit_ordinal limit_ordinal_oLimitI)
    apply (rule the_equality)
     apply (metis lub_cong omega_complete.ordinal_rec0_mono omega_complete_axioms s)
    by simp
next
  case False
  then show ?thesis
    apply (simp add: linorder_not_less, clarify)
    by (smt (verit, best) is_lub_lub is_ub_lub le_oLimit ordinal_rec0_mono po_antisym s)    
qed


subsection \<open>Recursive definitions for @{typ "ordinal => ordinal"}\<close>

definition
  ordinal_rec ::
    "[ordinal, ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal, ordinal] \<Rightarrow> ordinal" where
  "ordinal_rec z s = ordinal_rec0 z s oLimit"

lemma omega_complete_oLimit: "omega_complete (\<le>) oLimit"
  by (simp add: oLimit_leI omega_complete_axioms_def omega_complete_def porder_order)

lemma ordinal_rec_0 [simp]: "ordinal_rec z s 0 = z"
  by (simp add: ordinal_rec_def)

lemma ordinal_rec_oSuc [simp]:
  "ordinal_rec z s (oSuc x) = s x (ordinal_rec z s x)"
  by (unfold ordinal_rec_def, rule ordinal_rec0_oSuc)

lemma ordinal_rec_oLimit:
  assumes s: "\<forall>p x. x \<le> s p x"
  shows "ordinal_rec z s (oLimit f) = oLimit (\<lambda>n. ordinal_rec z s (f n))"
  by (metis omega_complete.ordinal_rec0_oLimit omega_complete_oLimit ordinal_rec_def s)

lemma continuous_ordinal_rec:
  assumes s: "\<forall>p x. x \<le> s p x"
  shows "continuous (ordinal_rec z s)"
  by (simp add: continuous.intro ordinal_rec_oLimit s)

lemma mono_ordinal_rec:
  assumes s: "\<forall>p x. x \<le> s p x"
  shows "mono (ordinal_rec z s)"
  by (simp add: continuous.mono continuous_ordinal_rec s)

lemma normal_ordinal_rec:
  assumes s: "\<forall>p x. x < s p x"
  shows "normal (ordinal_rec z s)"
  by (simp add: assms continuous.cont continuous_ordinal_rec less_imp_le normalI)

end
