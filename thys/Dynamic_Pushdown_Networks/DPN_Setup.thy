theory DPN_Setup
imports "Program-Conflict-Analysis.LTS" "Automatic_Refinement.Misc"
begin

section \<open>Additions to LTS\<close>

lemma trcl_struct: "\<And>s. \<lbrakk>(s,w,s')\<in>trcl D; D\<subseteq>S\<times>A\<times>S'\<rbrakk> \<Longrightarrow> (s=s' \<and> w=[]) \<or> (s\<in>S \<and> s'\<in>S' \<and> w\<in>lists A)" 
proof (induct w)
  case Nil
  then show ?case by simp
next
  case (Cons e w)
  then obtain sh where SPLIT: "(s,e,sh)\<in>D \<and> (sh,w,s')\<in>trcl D" by (blast dest: trcl_uncons)
  from SPLIT Cons.prems have "s\<in>S \<and> e\<in>A \<and> sh\<in>S'" by auto
  moreover from SPLIT Cons have "(sh=s' \<and> w=[]) \<or> (s'\<in>S' \<and> w\<in>lists A)" by blast
  ultimately show ?case by auto
qed


lemma trcl_structE: 
  assumes "(s,w,s')\<in>trcl D" "D\<subseteq>S\<times>A\<times>S'"
  obtains (empty) "s=s'" "w=[]" | (nonempty) "s\<in>S" "s'\<in>S'" "w\<in>lists A"
  using assms
  by (blast dest: trcl_struct)


end
