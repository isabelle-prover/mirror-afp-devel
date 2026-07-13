theory MSOinHOL_experiments_classic
  imports
    MSOinHOL_deep
    MSOinHOL_shallow
    MSOinHOL_shallow_minimal
begin

abbreviation "(x::V) \<equiv> 1"
abbreviation "(y::V) \<equiv> 2"
abbreviation "(z::V) \<equiv> 3"
abbreviation "(u::V) \<equiv> 4"
abbreviation "(v::V) \<equiv> 5"
abbreviation "(X::V2) \<equiv> 1"
abbreviation "(Y::V2) \<equiv> 2"
abbreviation "(Z::V2) \<equiv> 3"

consts P :: R

subsubsection \<open>Boolean closure (B\"uchi 1960; Thomas 1997) under @{text "\<Turnstile>\<^sup>d'"}\<close>

lemma complement_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2X. \<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d \<not>\<^sup>d X\<^sup>d(x)))"
  unfolding DefD
  apply (intro allI, simp add: SetMod_def EnvMod_def, intro allI)
  subgoal for S
    by (rule exI[of _ "\<lambda>d. \<not> S d"]) (auto simp: SetMod_def EnvMod_def)
  done

lemma intersection_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2X. \<forall>\<^sup>d\<^sub>2Y. \<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d (X\<^sup>d(x) \<and>\<^sup>d Y\<^sup>d(x))))"
  unfolding DefD
  apply (intro allI, simp add: SetMod_def EnvMod_def, intro allI)
  subgoal for S Sa
    by (rule exI[of _ "\<lambda>d. S d \<and> Sa d"])
       (auto simp: SetMod_def EnvMod_def)
  done

lemma union_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2X. \<forall>\<^sup>d\<^sub>2Y. \<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d (X\<^sup>d(x) \<or>\<^sup>d Y\<^sup>d(x))))"
  unfolding DefD
  apply (intro allI, simp add: SetMod_def EnvMod_def, intro allI)
  subgoal for S Sa
    by (rule exI[of _ "\<lambda>d. S d \<or> Sa d"])
       (auto simp: SetMod_def EnvMod_def)
  done

subsubsection \<open>Graph operations (Courcelle 2012)\<close>

lemma separation_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2X. \<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d (X\<^sup>d(x) \<and>\<^sup>d P\<^sup>d(x,x))))"
  unfolding DefD
  apply (intro allI, simp add: SetMod_def EnvMod_def, intro allI)
  subgoal for I S
    by (rule exI[of _ "\<lambda>d. S d \<and> I P d d"])
       (auto simp: SetMod_def EnvMod_def)
  done

lemma image_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2X. \<exists>\<^sup>d\<^sub>2Y. \<forall>\<^sup>dx. (Y\<^sup>d(x) \<longleftrightarrow>\<^sup>d \<exists>\<^sup>dy. (X\<^sup>d(y) \<and>\<^sup>d P\<^sup>d(y,x))))"
  unfolding DefD
  apply (intro allI, simp add: SetMod_def EnvMod_def, intro allI)
  subgoal for I S
    by (rule exI[of _ "\<lambda>d. \<exists>d'. S d' \<and> I P d' d"])
       (auto simp: SetMod_def EnvMod_def)
  done

lemma preimage_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2X. \<exists>\<^sup>d\<^sub>2Y. \<forall>\<^sup>dx. (Y\<^sup>d(x) \<longleftrightarrow>\<^sup>d \<exists>\<^sup>dy. (P\<^sup>d(x,y) \<and>\<^sup>d X\<^sup>d(y))))"
  unfolding DefD
  apply (intro allI, simp add: SetMod_def EnvMod_def, intro allI)
  subgoal for I S
    by (rule exI[of _ "\<lambda>d. \<exists>d'. I P d d' \<and> S d'"])
       (auto simp: SetMod_def EnvMod_def)
  done

text \<open>Reachability (Basin and Klarlund 1995): not universally valid;
  reflexive variant is.\<close>

lemma reachability_not_valid_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2Z. ((Z\<^sup>d(x) \<and>\<^sup>d (\<forall>\<^sup>du. (Z\<^sup>d(u) \<supset>\<^sup>d \<forall>\<^sup>dv. (P\<^sup>d(u,v) \<supset>\<^sup>d Z\<^sup>d(v))))) \<supset>\<^sup>d Z\<^sup>d(y)))"
  unfolding DefD apply simp nitpick oops

lemma reachability_reflexive_d:
  "\<Turnstile>\<^sup>d' (\<forall>\<^sup>d\<^sub>2Z. ((Z\<^sup>d(x) \<and>\<^sup>d (\<forall>\<^sup>du. (Z\<^sup>d(u) \<supset>\<^sup>d \<forall>\<^sup>dv. (P\<^sup>d(u,v) \<supset>\<^sup>d Z\<^sup>d(v))))) \<supset>\<^sup>d Z\<^sup>d(x)))"
  unfolding DefD by simp

text \<open>2-colorability (Thomas 1997): refuted on the triangle \<open>K\<^sub>3\<close>
  (the complete graph on three vertices).\<close>

lemma two_colorability_not_valid_d:
  "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. \<forall>\<^sup>dy. (P\<^sup>d(x,y) \<supset>\<^sup>d (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d \<not>\<^sup>d Z\<^sup>d(y))))"
  unfolding DefD apply simp nitpick oops

subsubsection \<open>Maximal-shallow embedding\<close>

text \<open>Same landmarks in the maximal-shallow embedding: structurally
  identical proofs.\<close>

lemma complement_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>s\<^sub>2X. \<exists>\<^sup>s\<^sub>2Z. \<forall>\<^sup>sx. (Z\<^sup>s(x) \<longleftrightarrow>\<^sup>s \<not>\<^sup>s X\<^sup>s(x)))"
  unfolding DefS
  apply (intro allI, simp, intro allI)
  subgoal for S by (rule exI[of _ "\<lambda>d. \<not> S d"]) auto
  done

lemma intersection_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>s\<^sub>2X. \<forall>\<^sup>s\<^sub>2Y. \<exists>\<^sup>s\<^sub>2Z. \<forall>\<^sup>sx. (Z\<^sup>s(x) \<longleftrightarrow>\<^sup>s (X\<^sup>s(x) \<and>\<^sup>s Y\<^sup>s(x))))"
  unfolding DefS
  apply (intro allI, simp, intro allI)
  subgoal for S Sa by (rule exI[of _ "\<lambda>d. S d \<and> Sa d"]) auto
  done

lemma union_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>s\<^sub>2X. \<forall>\<^sup>s\<^sub>2Y. \<exists>\<^sup>s\<^sub>2Z. \<forall>\<^sup>sx. (Z\<^sup>s(x) \<longleftrightarrow>\<^sup>s (X\<^sup>s(x) \<or>\<^sup>s Y\<^sup>s(x))))"
  unfolding DefS
  apply (intro allI, simp, intro allI)
  subgoal for S Sa by (rule exI[of _ "\<lambda>d. S d \<or> Sa d"]) auto
  done

lemma separation_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>s\<^sub>2X. \<exists>\<^sup>s\<^sub>2Z. \<forall>\<^sup>sx. (Z\<^sup>s(x) \<longleftrightarrow>\<^sup>s (X\<^sup>s(x) \<and>\<^sup>s P\<^sup>s(x,x))))"
  unfolding DefS
  apply (intro allI, simp, intro allI)
  subgoal for I S by (rule exI[of _ "\<lambda>d. S d \<and> I P d d"]) auto
  done

lemma image_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>s\<^sub>2X. \<exists>\<^sup>s\<^sub>2Y. \<forall>\<^sup>sx. (Y\<^sup>s(x) \<longleftrightarrow>\<^sup>s (\<exists>\<^sup>sy. (X\<^sup>s(y) \<and>\<^sup>s P\<^sup>s(y,x)))))"
  unfolding DefS
  apply (intro allI, simp, intro allI)
  subgoal for I S
    by (rule exI[of _ "\<lambda>d. \<exists>d'. S d' \<and> I P d' d"]) auto
  done

lemma preimage_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>s\<^sub>2X. \<exists>\<^sup>s\<^sub>2Y. \<forall>\<^sup>sx. (Y\<^sup>s(x) \<longleftrightarrow>\<^sup>s (\<exists>\<^sup>sy. (P\<^sup>s(x,y) \<and>\<^sup>s X\<^sup>s(y)))))"
  unfolding DefS
  apply (intro allI, simp, intro allI)
  subgoal for I S
    by (rule exI[of _ "\<lambda>d. \<exists>d'. I P d d' \<and> S d'"]) auto
  done

lemma reachability_not_valid_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>s\<^sub>2Z. ((Z\<^sup>s(x) \<and>\<^sup>s (\<forall>\<^sup>su. (Z\<^sup>s(u) \<supset>\<^sup>s (\<forall>\<^sup>sv. (P\<^sup>s(u,v) \<supset>\<^sup>s Z\<^sup>s(v)))))) \<supset>\<^sup>s Z\<^sup>s(y)))"
  unfolding DefS apply (intro allI) apply simp nitpick oops

lemma reachability_reflexive_s:
  "\<Turnstile>\<^sup>s' (\<forall>\<^sup>s\<^sub>2Z. ((Z\<^sup>s(x) \<and>\<^sup>s (\<forall>\<^sup>su. (Z\<^sup>s(u) \<supset>\<^sup>s (\<forall>\<^sup>sv. (P\<^sup>s(u,v) \<supset>\<^sup>s Z\<^sup>s(v)))))) \<supset>\<^sup>s Z\<^sup>s(x)))"
  unfolding DefS by simp

lemma two_colorability_not_valid_s:
  "\<Turnstile>\<^sup>s' (\<exists>\<^sup>s\<^sub>2Z. \<forall>\<^sup>sx. \<forall>\<^sup>sy. (P\<^sup>s(x,y) \<supset>\<^sup>s (Z\<^sup>s(x) \<longleftrightarrow>\<^sup>s \<not>\<^sup>s Z\<^sup>s(y))))"
  unfolding DefS apply (intro allI) apply simp nitpick oops

subsubsection \<open>Minimal-shallow embedding\<close>

text \<open>Minimal embedding: SO quantifier ranges over the countable
  \<open>Range GG\<close> (via \<open>nat\<close>), not all of \<open>Pow(D)\<close>.  Nitpick can only certify
  a POTENTIAL countermodel.\<close>

lemma complement_m_not_valid:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>m\<^sub>2X. \<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m \<not>\<^sup>m X\<^sup>m(x)))"
  unfolding DefM nitpick[expect=potential] oops

lemma intersection_m_not_valid:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>m\<^sub>2X. \<forall>\<^sup>m\<^sub>2Y. \<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m (X\<^sup>m(x) \<and>\<^sup>m Y\<^sup>m(x))))"
  unfolding DefM nitpick[expect=potential] oops

lemma reachability_not_valid_m:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>m\<^sub>2Z. ((Z\<^sup>m(x) \<and>\<^sup>m (\<forall>\<^sup>mu. (Z\<^sup>m(u) \<supset>\<^sup>m (\<forall>\<^sup>mv. (P\<^sup>m(u,v) \<supset>\<^sup>m Z\<^sup>m(v)))))) \<supset>\<^sup>m Z\<^sup>m(y)))"
  unfolding DefM nitpick[expect=potential] oops

text \<open>Reflexive reachability: the conclusion is the first conjunct of the
  antecedent; genuinely valid.\<close>

lemma reachability_reflexive_m:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>m\<^sub>2Z. ((Z\<^sup>m(x) \<and>\<^sup>m (\<forall>\<^sup>mu. (Z\<^sup>m(u) \<supset>\<^sup>m (\<forall>\<^sup>mv. (P\<^sup>m(u,v) \<supset>\<^sup>m Z\<^sup>m(v)))))) \<supset>\<^sup>m Z\<^sup>m(x)))"
  unfolding DefM by simp

lemma two_colorability_not_valid_m:
  "\<Turnstile>\<^sup>m (\<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. \<forall>\<^sup>my. (P\<^sup>m(x,y) \<supset>\<^sup>m (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m \<not>\<^sup>m Z\<^sup>m(y))))"
  unfolding DefM nitpick[expect=potential] oops

end
