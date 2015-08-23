(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Abstract-Rewriting\<close>

text \<open>Some lemmas which should be merged into the AFP-entry Abstract-Rewriting.\<close>

theory Missing_Abstract_Rewriting
imports
  "../Abstract-Rewriting/Relative_Rewriting"
begin

lemma closed_imp_rtrancl_closed: assumes L: "L \<subseteq> A"
  and R: "R `` A \<subseteq> A"
  shows "{t | s. s \<in> L \<and> (s,t) \<in> R^*} \<subseteq> A"
proof -
  {
    fix s t
    assume "(s,t) \<in> R^*" and "s \<in> L" 
    hence "t \<in> A"
      by (induct, insert L R, auto)
  }
  thus ?thesis by auto
qed

lemma trancl_steps_relpow: assumes "a \<subseteq> b^+"
  shows "(x,y) \<in> a^^n \<Longrightarrow> \<exists> m. m \<ge> n \<and> (x,y) \<in> b^^m"
proof (induct n arbitrary: y)
  case 0 thus ?case by (intro exI[of _ 0], auto)
next
  case (Suc n z)
  from Suc(2) obtain y where xy: "(x,y) \<in> a ^^ n" and yz: "(y,z) \<in> a" by auto
  from Suc(1)[OF xy] obtain m where m: "m \<ge> n" and xy: "(x,y) \<in> b ^^ m" by auto
  from yz assms have "(y,z) \<in> b^+" by auto
  from this[unfolded trancl_power] obtain k where k: "k > 0" and yz: "(y,z) \<in> b ^^ k" by auto
  from xy yz have "(x,z) \<in> b ^^ (m + k)" unfolding relpow_add by auto
  with k m show ?case by (intro exI[of _ "m + k"], auto)
qed

lemma relpow_image: assumes f: "\<And> s t. (s,t) \<in> r \<Longrightarrow> (f s, f t) \<in> r'"
  shows "(s,t) \<in> r ^^ n \<Longrightarrow> (f s, f t) \<in> r' ^^ n"
proof (induct n arbitrary: t)
  case (Suc n u)
  from Suc(2) obtain t where st: "(s,t) \<in> r ^^ n" and tu: "(t,u) \<in> r" by auto
  from Suc(1)[OF st] f[OF tu] show ?case by auto
qed auto

lemma relto_trancl_subset: assumes "a \<subseteq> c" and "b \<subseteq> c" shows "relto a b \<subseteq> c^+"
proof -
  have "relto a b \<subseteq> (a \<union> b)^+" by regexp
  also have "\<dots> \<subseteq> c^+"
    by (rule trancl_mono_set, insert assms, auto)
  finally show ?thesis .
qed

lemma relpow_refl_mono:
 assumes refl:"\<And> x. (x,x) \<in> Rel"
 shows "m \<le> n \<Longrightarrow>(a,b) \<in> Rel ^^ m \<Longrightarrow> (a,b) \<in> Rel ^^ n"
proof (induct rule:dec_induct)
  case (step i)
  hence abi:"(a, b) \<in> Rel ^^ i" by auto
  from refl[of b] abi relpowp_Suc_I[of i "\<lambda> x y. (x,y) \<in> Rel"] show "(a, b) \<in> Rel ^^ Suc i" by auto
qed

end