(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

header {* Hoare Logic *}

theory HoareLogic
  imports KAT
begin

context kat
begin

text {*
  We encode validity of Hoare triples and derive the inference rules of propositional Hoare logic,
  that is, Hoare logic without the assignement rule, in Kleene algebra with tests.
*}

definition hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>") where
  "\<lbrace>p\<rbrace> x \<lbrace>q\<rbrace> \<equiv> p\<cdot>x = p\<cdot>x\<cdot>q \<and> test p \<and> test q"

lemma hoare_triple_def_var: "\<lbrace>p\<rbrace> x \<lbrace>q\<rbrace> = (p\<cdot>x \<le> x\<cdot>q \<and> test p \<and> test q)"
  by (metis hoare_triple_def kat_eq1 kat_eq2)

lemma skip_rule: "test p \<Longrightarrow> \<lbrace>p\<rbrace>1\<lbrace>p\<rbrace>"
  by (simp add: hoare_triple_def)

lemma sequence_rule: "\<lbrace>p\<rbrace>x\<lbrace>q'\<rbrace> \<Longrightarrow> \<lbrace>q'\<rbrace>x'\<lbrace>q\<rbrace> \<Longrightarrow> \<lbrace>p\<rbrace>x\<cdot>x'\<lbrace>q\<rbrace>"
  by (simp add: hoare_triple_def, metis mult.assoc)

lemma conditional_rule: "\<lbrakk>\<lbrace>p\<cdot>b\<rbrace>x\<lbrace>q\<rbrace>; \<lbrace>p\<cdot>!b\<rbrace>x'\<lbrace>q\<rbrace>; test p; test b\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>b\<cdot>x + !b\<cdot>x'\<lbrace>q\<rbrace>"
  by (simp add: hoare_triple_def, metis mult.assoc distrib_left distrib_right)

lemma consequence_rule: "\<lbrakk>test p; p \<le> p'; \<lbrace>p'\<rbrace>x\<lbrace>q'\<rbrace>; q' \<le> q; test q\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>x\<lbrace>q\<rbrace>"
  by (unfold hoare_triple_def, metis (full_types) mult.assoc test_leq_mult_def_var)

lemma while_rule_var: "\<lbrace>p\<rbrace>x\<lbrace>p\<rbrace> \<Longrightarrow> \<lbrace>p\<rbrace>x\<^sup>\<star>\<lbrace>p\<rbrace>"
  by (metis hoare_triple_def_var star_sim2)

lemma while_rule: "\<lbrakk>test q; \<lbrace>p\<cdot>q\<rbrace>x\<lbrace>p\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>(q\<cdot>x)\<^sup>\<star>\<cdot>!q\<lbrace>p\<cdot>!q\<rbrace>"
proof (unfold hoare_triple_def_var, auto)
  assume assms: "test p" "test q" "p\<cdot>q\<cdot>x \<le> x\<cdot>p"
  hence "q\<cdot>p\<cdot>q\<cdot>x \<le> q\<cdot>x\<cdot>p"
    by (metis mult.assoc mult_isol)
  thus "p\<cdot>((q\<cdot>x)\<^sup>\<star>\<cdot>!q) \<le> (q\<cdot>x)\<^sup>\<star>\<cdot>!q\<cdot>(p\<cdot>!q)"
    by (metis assms(1,2) test_mult_comm_var star_sim2 mult_isor kat_eq3 mult.assoc test2)
qed (metis test_comp_closed_var test_mult_closed)

definition (in kat) while_inv :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _" [64,64,64] 63) where
  "while b inv i do p = (b\<cdot>p)\<^sup>\<star> \<cdot> !b"

lemma hoare_while_inv:
  assumes tb: "test b" and tp: "test p" and tq: "test q"
  and pi: "p \<le> i" and iq: "i \<cdot> !b \<le> q"
  and inv_loop: "\<lbrace>i \<cdot> b\<rbrace> c \<lbrace>i\<rbrace>"
  shows "\<lbrace>p\<rbrace> while b inv i do c \<lbrace>q\<rbrace>"
  by (metis assms while_inv_def while_rule consequence_rule)

end
end
