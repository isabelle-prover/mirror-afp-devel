theory MSOinHOL_experiments_classic_elementary
  imports
    MSOinHOL_deep
    MSOinHOL_shallow
    MSOinHOL_shallow_minimal_elementary
begin

text \<open>Extra simp rules for derived quantifiers / connectives.\<close>

lemma ren_for_subst2_simp_All [simp]:
  "ren_for_subst2 X Z (\<forall>\<^sup>d\<^sub>2Y. \<phi>) =
     (if Y = Z \<and> X free2_in \<phi>
      then let f = max (fresh2 \<phi>) (Z+1); \<phi>' = [Y\<leftarrow>\<^sub>2f](\<phi>)
           in (\<forall>\<^sup>d\<^sub>2f. ren_for_subst2 X Z \<phi>')
      else \<forall>\<^sup>d\<^sub>2Y. ren_for_subst2 X Z \<phi>)"
  unfolding DefD by (auto simp: Let_def)

lemma subst2_all [simp]:
  "[X\<leftarrow>\<^sub>2Z](\<forall>\<^sup>d\<^sub>2Y. \<phi>) =
     (if X = Y then (\<forall>\<^sup>d\<^sub>2Y. \<phi>) else (\<forall>\<^sup>d\<^sub>2Y. [X\<leftarrow>\<^sub>2Z](\<phi>)))"
  unfolding DefD by (auto simp: Let_def)

lemma free2_in_equiv [simp]:
  "X free2_in (\<phi> \<longleftrightarrow>\<^sup>d \<psi>) = (X free2_in \<phi> \<or> X free2_in \<psi>)"
  by (auto simp add: DefD)

lemma free2_in_all [simp]:
  "X free2_in (\<forall>\<^sup>dy. \<phi>) = (X free2_in \<phi>)"
  by (simp add: AllD_def)

lemma free2_in_all2 [simp]:
  "X free2_in (\<forall>\<^sup>d\<^sub>2Y. \<phi>) = (X free2_in \<phi> \<and> X \<noteq> Y)"
  by (metis AllD2_def is_free2.simps)

text \<open>Some abbreviations for variables.\<close>

abbreviation "(x::V) \<equiv> 1"
abbreviation "(y::V) \<equiv> 2"
abbreviation "(z::V) \<equiv> 3"
abbreviation "(u::V) \<equiv> 4"
abbreviation "(v::V) \<equiv> 5"
abbreviation "(X::V2) \<equiv> 1"
abbreviation "(Y::V2) \<equiv> 2"
abbreviation "(Z::V2) \<equiv> 3"

consts P :: R

subsubsection \<open>Boolean closure (B\"uchi 1960; Thomas 1997)\<close>

text \<open>Under @{text "\<Turnstile>\<^sup>d'"}: witnesses supplied via @{text exI}.\<close>

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

lemma intersection_d':
  "\<Turnstile>\<^sup>d' (\<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d (X\<^sup>d(x) \<and>\<^sup>d Y\<^sup>d(x))))"
  by (simp add: comprehension_schema)

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

subsubsection \<open>Transfer to the elementary minimal embedding\<close>

text \<open>Via the @{text DpToShS} normal-form and @{text ValidM_if_ValidD'}.\<close>

lemma compl_m_DpToSh:
  "\<lparr>\<forall>\<^sup>d\<^sub>2X. \<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d \<not>\<^sup>d X\<^sup>d(x))\<rparr> = (\<forall>\<^sup>m\<^sub>2X. \<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m \<not>\<^sup>m X\<^sup>m(x)))"
  by (auto simp add: ren_subst2_def ren_subst_def Let_def)
     (auto simp: DefD DefM ren_subst_def)

lemma compl_m_valid:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>m\<^sub>2X. \<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m \<not>\<^sup>m X\<^sup>m(x)))"
  using compl_m_DpToSh ValidM_if_ValidD'[OF complement_d] by simp

lemma inters_m_DpToSh':
  "\<lparr>\<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d (X\<^sup>d(x) \<and>\<^sup>d Y\<^sup>d(x)))\<rparr> = (\<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m (X\<^sup>m(x) \<and>\<^sup>m Y\<^sup>m(x))))"
  by (auto simp add: ren_subst2_def ren_subst_def Let_def)
     (auto simp: DefD DefM ren_subst_def)

lemma DpToSh_alleqI:
  "(\<And>d. \<lparr>[X \<leftarrow>\<^sub>r\<^sub>2 d](\<phi>)\<rparr> = \<psi> d) \<Longrightarrow> \<lparr>\<forall>\<^sup>d\<^sub>2X. \<phi>\<rparr> = (\<forall>\<^sup>m\<^sub>2X. \<psi> X)"
  by simp

lemma all_m_eqI:
  "(\<And>X. \<phi> X = \<psi> X) \<Longrightarrow> (\<forall>\<^sup>m\<^sub>2X. \<phi> X) = (\<forall>\<^sup>m\<^sub>2X. \<psi> X)"
  by presburger

lemmas DpToSh_simps = DefM Let_def ren_subst_def DefD ren_subst2_def

lemma intersect_m_DpToSh:
  "\<lparr>\<forall>\<^sup>d\<^sub>2X. \<forall>\<^sup>d\<^sub>2Y. \<exists>\<^sup>d\<^sub>2Z. \<forall>\<^sup>dx. (Z\<^sup>d(x) \<longleftrightarrow>\<^sup>d (X\<^sup>d(x) \<and>\<^sup>d Y\<^sup>d(x)))\<rparr> = (\<forall>\<^sup>m\<^sub>2X. \<forall>\<^sup>m\<^sub>2Y. \<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m (X\<^sup>m(x) \<and>\<^sup>m Y\<^sup>m(x))))"
  \<comment> \<open>Push @{term DpToShM} through the two outer set quantifiers and split on
      whether the fresh index @{term d} chosen by the renaming coincides with
      @{term Z}, with @{term Y}, or with neither.  Each case is discharged
      inside its own @{text subgoal} block, so no @{text auto} step silently
      hands its leftover goals to the next one.\<close>
  apply (rule DpToSh_alleqI,
         simp only: ren_subst2_def subst2_all ren_for_subst2_simp_All,
         simp)
  subgoal for d
    apply (cases "d = Z", simp, rule all_m_eqI)
    subgoal by (auto simp: DpToSh_simps)
    apply (simp, cases "d = Y", simp)
    subgoal by (auto simp: DpToSh_simps; metis)
        \<comment> \<open>Remaining case @{text "d \<notin> {Y,Z}"}: normalise the renamed body and offer
      the bound predicate @{term D} as the existential witness.  The fresh index
      @{term "max Z (max d Y)"} exceeds both @{term Y} and @{term d}, so the two
      guarded substitutions collapse.  Normalisation and the witness step are
      kept together in one @{text subgoal}, so any change in the shape of the
      @{text auto}-normalised goal fails here rather than downstream.\<close>
    apply (simp, rule all_m_eqI)
    subgoal for da
      apply (auto simp: ren_subst2_def ren_subst_def Let_def)
      subgoal apply (auto simp: DpToSh_simps)
        subgoal for D
          apply (rule exI[where x=D])
          apply (subgoal_tac "Suc (max Z (max d Y)) \<noteq> d" "max Z (max d Y) \<noteq> Y")
            apply simp
           apply simp
          apply (simp add: le_imp_less_Suc max.coboundedI2)
          done
        done
      by (auto simp: DpToSh_simps)
    done
  done

lemma intersection_m_valid:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>m\<^sub>2X. \<forall>\<^sup>m\<^sub>2Y. \<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m (X\<^sup>m(x) \<and>\<^sup>m Y\<^sup>m(x))))"
  using ValM_def ValidM_if_ValidD' intersection_d intersect_m_DpToSh
  by blast

text \<open>Reachability and 2-colorability remain refuted in the elementary
  minimal embedding.\<close>

lemma reachability_not_valid_m:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>m\<^sub>2Z. ((Z\<^sup>m(x) \<and>\<^sup>m (\<forall>\<^sup>mu. (Z\<^sup>m(u) \<supset>\<^sup>m (\<forall>\<^sup>mv. (P\<^sup>m(u,v) \<supset>\<^sup>m Z\<^sup>m(v)))))) \<supset>\<^sup>m Z\<^sup>m(y)))"
  unfolding DefM oops

lemma reachability_reflexive_m:
  "\<Turnstile>\<^sup>m (\<forall>\<^sup>m\<^sub>2Z. ((Z\<^sup>m(x) \<and>\<^sup>m (\<forall>\<^sup>mu. (Z\<^sup>m(u) \<supset>\<^sup>m (\<forall>\<^sup>mv. (P\<^sup>m(u,v) \<supset>\<^sup>m Z\<^sup>m(v)))))) \<supset>\<^sup>m Z\<^sup>m(x)))"
  unfolding DefM by simp

lemma two_colorability_not_valid_m:
  "\<Turnstile>\<^sup>m (\<exists>\<^sup>m\<^sub>2Z. \<forall>\<^sup>mx. \<forall>\<^sup>my. (P\<^sup>m(x,y) \<supset>\<^sup>m (Z\<^sup>m(x) \<longleftrightarrow>\<^sup>m \<not>\<^sup>m Z\<^sup>m(y))))"
  unfolding DefM oops

end
