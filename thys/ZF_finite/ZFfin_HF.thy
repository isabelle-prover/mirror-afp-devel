(*  Author:     Štěpán Holub, Department of Algebra, Charles University
    Author:     Zuzana Haniková, Institute of Computer Science of the Czech Academy of Sciences
*)


chapter \<open>Models and counter-models\<close>
theory ZFfin_HF
imports HereditarilyFinite.Rank ZFfin
begin

section \<open>Hereditarily finite sets\<close>

text \<open>We show that the hereditarily finite sets as implemented in @{theory HereditarilyFinite.HF} are a model of 
 ZFfin as implemented in @{theory ZF_finite.ZFfin}\<close>

interpretation zfhf: ZFfin "(\<^bold>\<in>)"
  rewrites "zfhf.emptysetM = 0" and
           "zfhf.singletonM y = \<lbrace>y\<rbrace>" and
           "zfhf.setsucM x y = x \<triangleleft> y"
proof-
  interpret zfhf: L_setsuc  "(\<^bold>\<in>)"
    by unfold_locales blast+ 
  interpret zfhf: L_empty  "(\<^bold>\<in>)"
    by unfold_locales blast
  interpret zfhf: L_setext_empty  "(\<^bold>\<in>)"
    by unfold_locales blast
  show zfhf_emp: "zfhf.emptysetM = 0"
      using zfhf.empty_is_empty by auto
  interpret zfhf: L_setsuc  "(\<^bold>\<in>)"
    by unfold_locales blast+ 
  interpret zfhf: L_empty  "(\<^bold>\<in>)"
    by unfold_locales blast
  interpret zfhf: L_setext_empty_setsuc "(\<^bold>\<in>)"
    by unfold_locales
  show zfhf_sing: "zfhf.singletonM y = \<lbrace>y\<rbrace>" for y
    using zfhf.singleton_def' by blast  
  show zfhf_suc:  "zfhf.setsucM x y = x \<triangleleft> y" for x y
    unfolding zfhf.setext[of _ "x \<triangleleft> y"] zfhf.setsuc_def'  by auto 
  interpret L_setind "(\<^bold>\<in>)"
  proof
    show "zfhf.SetFormulaPredicate P \<Longrightarrow>  P (\<Xi>(0 := zfhf.emptysetM)) \<longrightarrow>
        (\<forall>x y. P (\<Xi>(0 := x)) \<longrightarrow> P (\<Xi>(0 := zfhf.setsucM x y))) \<longrightarrow> (\<forall>x. P (\<Xi>(0 := x)))" for P \<Xi>
      unfolding zfhf_suc zfhf_emp using hf_induct[of "\<lambda> a. P (\<Xi>(0:=a))"] by blast
  qed
  interpret L_setext_empty_setsuc_setind "(\<^bold>\<in>)"
    by unfold_locales
  interpret L_epsind "(\<^bold>\<in>)"
  proof
    fix \<Xi>  :: "nat \<Rightarrow> hf" and Q
    from Rank.hmem_induct[of "\<lambda> x. Q(\<Xi>(0:=x))"]
    show "(\<forall>x. (\<forall>y. y \<^bold>\<in> x \<longrightarrow> Q (\<Xi>(0 := y))) \<longrightarrow> Q (\<Xi>(0 := x))) \<longrightarrow> (\<forall>x. Q (\<Xi>(0 := x)))"
      by blast
  qed
  show "ZFfin (\<^bold>\<in>)"
  proof (unfold_locales, unfold zfhf_emp zfhf_suc) 
    fix \<Xi>  :: "nat \<Rightarrow> hf" and P
    from hf_induct[of "\<lambda> x. P(\<Xi>(0:=x))"]
    show "\<nexists>x. 0 \<^bold>\<in> x \<and> (\<forall>y. y \<^bold>\<in> x \<longrightarrow> y \<triangleleft> y \<^bold>\<in> x)"
      using fin zfhf_emp zfhf_suc by auto
  qed
qed  

end