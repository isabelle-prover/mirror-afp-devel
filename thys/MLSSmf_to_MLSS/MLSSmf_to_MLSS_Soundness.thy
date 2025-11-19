theory MLSSmf_to_MLSS_Soundness
  imports MLSSmf_to_MLSS MLSSmf_Semantics Proper_Venn_Regions MLSSmf_HF_Extras
begin

locale satisfiable_normalized_MLSSmf_clause =
  normalized_MLSSmf_clause \<C> for \<C> :: "('v, 'f) MLSSmf_clause" +
    fixes M\<^sub>v :: "'v \<Rightarrow> hf"
      and M\<^sub>f :: "'f \<Rightarrow> hf \<Rightarrow> hf"
  assumes model_for_\<C>: "I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>"
begin

interpretation proper_Venn_regions V M\<^sub>v
  using finite_V by unfold_locales

function \<M> :: "('v, 'f) Composite \<Rightarrow> hf" where
  "\<M> (Solo x)  = M\<^sub>v x"
| "\<M> (v\<^bsub>\<alpha>\<^esub>)    = proper_Venn_region \<alpha>"
| "\<M> (UnionOfVennRegions xss) = \<Squnion>HF ((\<M> \<circ> VennRegion) ` set xss)"
| "\<M> (w\<^bsub>f\<^esub>\<^bsub>l\<^esub>) = (M\<^sub>f f) (\<M> (UnionOfVennRegions (var_set_set_to_var_set_list l)))"
| "\<M> (UnionOfVars xs) = \<Squnion>HF (M\<^sub>v ` set xs)"
| "\<M> (InterOfVars xs) = \<Sqinter>HF (M\<^sub>v ` set xs)"
| "\<M> (MemAux x) = HF {M\<^sub>v x}"
| "\<M> (InterOfWAux f l m) = \<M> w\<^bsub>f\<^esub>\<^bsub>l\<^esub> - \<M> w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
| "\<M> (InterOfVarsAux xs) = M\<^sub>v (hd xs) - \<M> (InterOfVars (tl xs))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>comp. case comp of
                    InterOfVarsAux _ \<Rightarrow> Suc 0
                  | UnionOfVennRegions _ \<Rightarrow> Suc 0
                  | w\<^bsub>_\<^esub>\<^bsub>_\<^esub> \<Rightarrow> Suc (Suc 0)
                  | InterOfWAux _ _ _ \<Rightarrow> Suc (Suc (Suc 0))
                  | _ \<Rightarrow> 0)")
       apply auto
  done

lemma soundness_restriction_on_InterOfVars:
  assumes "set xs \<in> P\<^sup>+ V"
    shows "\<forall>a \<in> restriction_on_InterOfVars xs. I\<^sub>s\<^sub>a \<M> a"
proof (induction xs rule: restriction_on_InterOfVars.induct)
  case (2 x)
  {fix a assume "a \<in> restriction_on_InterOfVars [x]"
    then have "a = Var (InterOfVars [x]) =\<^sub>s Var (Solo x)" by simp
    then have "I\<^sub>s\<^sub>a \<M> a" by (simp add: HInter_singleton)
  }
  then show ?case by blast
next
  case (3 y x xs)
  {fix a assume "a \<in> restriction_on_InterOfVars (y # x # xs) - restriction_on_InterOfVars (x # xs)"
    then consider "a = Var (InterOfVarsAux (y # x # xs)) =\<^sub>s Var (Solo y) -\<^sub>s Var (InterOfVars (x # xs))"
                | "a = Var (InterOfVars (y # x # xs)) =\<^sub>s Var (Solo y) -\<^sub>s Var (InterOfVarsAux (y # x # xs))"
      by fastforce
    then have "I\<^sub>s\<^sub>a \<M> a"
    proof (cases)
      case 1
      then show ?thesis by simp
    next
      case 2
      have "\<Sqinter>HF (insert (M\<^sub>v y) (insert (M\<^sub>v x) (M\<^sub>v ` set xs))) =
            \<Sqinter> (HF ((insert (M\<^sub>v x) (M\<^sub>v ` set xs))) \<triangleleft> M\<^sub>v y)"
        using HF_insert_hinsert by auto
      also have "... = M\<^sub>v y \<sqinter> \<Sqinter>HF (insert (M\<^sub>v x) (M\<^sub>v ` set xs))"
        by (simp add: HF_nonempty)
      also have "... = M\<^sub>v y - (M\<^sub>v y - \<Sqinter>HF (insert (M\<^sub>v x) (M\<^sub>v ` set xs)))"
        by blast
      finally show ?thesis using 2 by simp
    qed
  }
  with "3.IH" show ?case by blast
qed simp

lemma soundness_restriction_on_UnionOfVars:
  assumes "set xs \<in> Pow V"
    shows "\<forall>a \<in> restriction_on_UnionOfVars xs. I\<^sub>s\<^sub>a \<M> a"
proof (induction xs rule: restriction_on_UnionOfVars.induct)
  case 1
  then show ?case by auto
next
  case (2 x xs)
  {fix a assume "a \<in> restriction_on_UnionOfVars (x # xs) - restriction_on_UnionOfVars xs"
    then have a: "a = Var (UnionOfVars (x # xs)) =\<^sub>s Var (Solo x) \<squnion>\<^sub>s Var (UnionOfVars xs)"
      by fastforce
    have "\<Squnion>HF (insert (M\<^sub>v x) (M\<^sub>v ` set xs)) = \<Squnion> (HF (M\<^sub>v ` set xs) \<triangleleft> M\<^sub>v x)"
      by (simp add: HF_insert_hinsert)
    also have "... = M\<^sub>v x \<squnion> \<Squnion>HF (M\<^sub>v ` set xs)" by auto
    finally have "I\<^sub>s\<^sub>a \<M> a"
      using a by simp
  }
  with "2.IH" show ?case by blast
qed

lemma soundness_introduce_v:
  "\<forall>fml \<in> introduce_v. interp I\<^sub>s\<^sub>a \<M> fml"
proof -
  {fix \<alpha> assume "\<alpha> \<in> P\<^sup>+ V"
    have "\<M> v\<^bsub>\<alpha>\<^esub> = \<Sqinter>HF (M\<^sub>v ` \<alpha>) - \<Squnion>HF (M\<^sub>v ` (V - \<alpha>))"
      by simp
    also have "... = \<Sqinter>HF ((\<M> \<circ> Solo) ` \<alpha>) - \<Squnion>HF ((\<M> \<circ> Solo) ` (V - \<alpha>))"
      by simp
    finally have "I\<^sub>s\<^sub>a \<M> (restriction_on_v \<alpha>)"
      apply (simp add: set_V_list)
      using \<open>\<alpha> \<in> P\<^sup>+ V\<close>
      by (metis Int_def inf.absorb2 mem_P_plus_subset set_diff_eq)
  }
  then have "\<forall>\<alpha> \<in> P\<^sup>+ V. interp I\<^sub>s\<^sub>a \<M> (AT (restriction_on_v \<alpha>))"
    by simp
  moreover
  from soundness_restriction_on_InterOfVars
  have "\<forall>a \<in> (restriction_on_InterOfVars \<circ> var_set_to_list) \<alpha>. I\<^sub>s\<^sub>a \<M> a" if "\<alpha> \<in> P\<^sup>+ V" for \<alpha>
    by (metis comp_apply mem_P_plus_subset set_var_set_to_list that)
  then have "\<forall>lt \<in> AT ` \<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` P\<^sup>+ V). interp I\<^sub>s\<^sub>a \<M> lt"
    by fastforce
  moreover
  from soundness_restriction_on_UnionOfVars
  have "\<forall>a \<in> (restriction_on_UnionOfVars \<circ> var_set_to_list) \<alpha>. I\<^sub>s\<^sub>a \<M> a" if "\<alpha> \<in> Pow V" for \<alpha>
    by (metis Pow_iff comp_apply set_var_set_to_list that)
  then have "\<forall>lt \<in> AT ` \<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` Pow V). interp I\<^sub>s\<^sub>a \<M> lt"
    by fastforce
  ultimately
  show ?thesis
    unfolding introduce_v_def by blast
qed

lemma soundness_restriction_on_UnionOfVennRegions:
  assumes "set \<alpha>s \<in> Pow (Pow V)"
    shows "\<forall>a \<in> restriction_on_UnionOfVennRegions \<alpha>s. I\<^sub>s\<^sub>a \<M> a"
proof (induction \<alpha>s rule: restriction_on_UnionOfVennRegions.induct)
  case 1
  then show ?case by auto
next
  case (2 \<alpha> \<alpha>s)
  {fix a assume "a \<in> restriction_on_UnionOfVennRegions (\<alpha> # \<alpha>s) - restriction_on_UnionOfVennRegions \<alpha>s"
    then have a: "a = Var (UnionOfVennRegions (\<alpha> # \<alpha>s)) =\<^sub>s Var v\<^bsub>\<alpha>\<^esub> \<squnion>\<^sub>s Var (UnionOfVennRegions \<alpha>s)"
      by fastforce
    have "\<Squnion>HF ((\<M> \<circ> VennRegion) ` set (\<alpha> # \<alpha>s)) = \<Squnion>HF (insert (\<M> v\<^bsub>\<alpha>\<^esub>) ((\<M> \<circ> VennRegion) ` set \<alpha>s))"
      by simp
    also have "... = \<Squnion> (HF ((\<M> \<circ> VennRegion) ` set \<alpha>s) \<triangleleft> \<M> v\<^bsub>\<alpha>\<^esub>)"
      by (simp add: HF_insert_hinsert)
    also have "... = \<M> v\<^bsub>\<alpha>\<^esub> \<squnion> \<Squnion>HF ((\<M> \<circ> VennRegion) ` set \<alpha>s)"
      by blast
    finally have "I\<^sub>s\<^sub>a \<M> a" using a by simp
  }
  with "2.IH" show ?case by blast
qed

lemma soundness_introduce_UnionOfVennRegions:
  "\<forall>lt \<in> introduce_UnionOfVennRegions. interp I\<^sub>s\<^sub>a \<M> lt"
proof
  fix lt assume "lt \<in> introduce_UnionOfVennRegions"
  then obtain \<alpha>s where "\<alpha>s \<in> set all_V_set_lists" "lt \<in> AT ` restriction_on_UnionOfVennRegions \<alpha>s"
    unfolding introduce_UnionOfVennRegions_def by blast
  with soundness_restriction_on_UnionOfVennRegions
  show "interp I\<^sub>s\<^sub>a \<M> lt"
    using set_all_V_set_lists by fastforce
qed

lemma soundness_restriction_on_FunOfUnionOfVennRegions:
  assumes l'_l: "l' = var_set_set_to_var_set_list l"
      and m'_m: "m' = var_set_set_to_var_set_list m"
    shows "\<exists>lt \<in> set (restriction_on_FunOfUnionOfVennRegions l' m' f). interp I\<^sub>s\<^sub>a \<M> lt"
proof (cases "\<M> (UnionOfVennRegions l') = \<M> (UnionOfVennRegions m')")
  case True
  then have "\<M> w\<^bsub>f\<^esub>\<^bsub>l\<^esub> = \<M> w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
    using l'_l m'_m by auto
  then have "interp I\<^sub>s\<^sub>a \<M> (AT (Var w\<^bsub>f\<^esub>\<^bsub>set l'\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>set m'\<^esub>))"
    using l'_l m'_m by auto
  then show ?thesis by simp
next
  case False
  then have "interp I\<^sub>s\<^sub>a \<M> (AF (Var (UnionOfVennRegions l') =\<^sub>s Var (UnionOfVennRegions m')))"
    by fastforce
  then show ?thesis by simp
qed

lemma soundness_introduce_w:
  "\<exists>clause \<in> introduce_w. \<forall>lt \<in> clause. interp I\<^sub>s\<^sub>a \<M> lt"
proof -
  let ?f = "\<lambda>lts. if interp I\<^sub>s\<^sub>a \<M> (lts ! 0) then lts ! 0 else lts ! 1"
  let ?g = "\<lambda>(l, m, f). restriction_on_FunOfUnionOfVennRegions l m f"
  let ?xs = "List.product all_V_set_lists (List.product all_V_set_lists F_list)"
  have "\<forall>(l', m', f) \<in> set ?xs. ?f (?g (l', m', f)) \<in> set (?g (l', m', f))"
    by fastforce
  with valid_choice[where ?f = ?f and ?g = ?g and ?xs = ?xs]
  have "map ?f (map ?g ?xs) \<in> set (choices_from_lists (map ?g ?xs))"
    by fast
  then have "set (map ?f (map ?g ?xs)) \<in> introduce_w"
    unfolding introduce_w_def
    using mem_set_map[where ?x = "map ?f (map ?g ?xs)" and ?f = set]
    by blast
  moreover
  have "{x \<in> set V_set_list. x \<in> set l'} = set l'" if "l' \<in> set all_V_set_lists" for l'
    using that set_V_set_list set_all_V_set_lists by auto
  then have "interp I\<^sub>s\<^sub>a \<M> (?f (restriction_on_FunOfUnionOfVennRegions l' m' f))"
    if "l' \<in> set all_V_set_lists" "m' \<in> set all_V_set_lists" for l' m' f
    using that by auto
  then have "\<forall>lt \<in> set (map ?f (map ?g ?xs)). interp I\<^sub>s\<^sub>a \<M> lt"
    by force
  ultimately
  show ?thesis by blast
qed

lemma soundness_reduce_literal:
  assumes "lt \<in> set \<C>"
    shows "\<forall>fml \<in> reduce_literal lt. interp I\<^sub>s\<^sub>a \<M> fml"
proof -
  from norm_\<C> \<open>lt \<in> set \<C>\<close> have "norm_literal lt" by auto
  then show ?thesis
  proof (cases rule: norm_literal.cases)
    case (inc f)
    show ?thesis
    proof
      fix fml assume "fml \<in> reduce_literal lt"
      then have "fml \<in> reduce_literal (AT\<^sub>m (inc(f)))"
        using inc by blast
      then obtain l m where lm: "l \<subseteq> P\<^sup>+ V" "m \<subseteq> P\<^sup>+ V" "l \<subseteq> m"
                        and fml: "fml = AT (Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub>)"
        by auto
      from model_for_\<C> \<open>lt \<in> set \<C>\<close> inc have "I\<^sub>a M\<^sub>v M\<^sub>f (inc(f))" by fastforce
      then have "\<forall>s t. s \<le> t \<longrightarrow> (M\<^sub>f f) s \<le> (M\<^sub>f f) t" by simp
      moreover
      from lm have "\<Squnion>HF ((\<M> \<circ> VennRegion) ` l) \<le> \<Squnion>HF ((\<M> \<circ> VennRegion) ` m)"
        by (metis HUnion_proper_Venn_region_inter \<M>.simps(2) comp_apply image_cong inf.absorb_iff2)
      ultimately
      have "M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` l)) \<le> M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` m))"
        by blast
      then have "M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` m)) =
                 M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` m)) \<squnion> M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` l))"
        by blast
      with fml lm show "interp I\<^sub>s\<^sub>a \<M> fml"
        by (auto simp only: interp.simps I\<^sub>s\<^sub>a.simps I\<^sub>s\<^sub>t.simps \<M>.simps set_var_set_set_to_var_set_list)
    qed
  next
    case (dec f)
    show ?thesis
    proof
      fix fml assume "fml \<in> reduce_literal lt"
      then have "fml \<in> reduce_literal (AT\<^sub>m (dec(f)))"
        using dec by blast
      then obtain l m where lm: "l \<subseteq> P\<^sup>+ V" "m \<subseteq> P\<^sup>+ V" "l \<subseteq> m"
                        and fml: "fml = AT (Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>)"
        by auto
      from model_for_\<C> \<open>lt \<in> set \<C>\<close> dec have "I\<^sub>a M\<^sub>v M\<^sub>f (dec(f))" by fastforce
      then have "\<forall>s t. s \<le> t \<longrightarrow> (M\<^sub>f f) t \<le> (M\<^sub>f f) s" by simp
      moreover
      from lm have "\<Squnion>HF ((\<M> \<circ> VennRegion) ` l) \<le> \<Squnion>HF ((\<M> \<circ> VennRegion) ` m)"
        by (metis HUnion_proper_Venn_region_inter \<M>.simps(2) comp_apply image_cong inf.absorb_iff2)
      ultimately
      have "M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` m)) \<le> M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` l))"
        by blast
      then have "M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` l)) =
                 M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` l)) \<squnion> M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` m))"
        by blast
      with fml lm show "interp I\<^sub>s\<^sub>a \<M> fml"
        by (auto simp only: interp.simps I\<^sub>s\<^sub>a.simps I\<^sub>s\<^sub>t.simps \<M>.simps set_var_set_set_to_var_set_list)
    qed
  next
    case (add f)
    show ?thesis
    proof
      fix fml assume "fml \<in> reduce_literal lt"
      then have "fml \<in> reduce_literal (AT\<^sub>m (add(f)))"
        using add by blast
      then obtain l m where lm: "l \<subseteq> P\<^sup>+ V" "m \<subseteq> P\<^sup>+ V"
                        and fml: "fml = AT (Var w\<^bsub>f\<^esub>\<^bsub>l\<union>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>)"
        by auto
      from model_for_\<C> \<open>lt \<in> set \<C>\<close> add have "I\<^sub>a M\<^sub>v M\<^sub>f (add(f))" by fastforce
      then have "\<forall>s t. (M\<^sub>f f) (s \<squnion> t) = (M\<^sub>f f) s \<squnion> (M\<^sub>f f) t" by simp
      moreover
      have "\<Squnion>HF ((\<M> \<circ> VennRegion) ` (l \<union> m)) = \<Squnion>HF ((\<M> \<circ> VennRegion) ` l) \<squnion> \<Squnion>HF ((\<M> \<circ> VennRegion) ` m)"
        using HUnion_proper_Venn_region_union \<M>.simps(2) lm(1) lm(2) by auto
      ultimately
      have "M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` (l \<union> m))) =
            M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` l)) \<squnion> M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` m))"
        by auto
      with fml lm show "interp I\<^sub>s\<^sub>a \<M> fml"
        using set_var_set_set_to_var_set_list
        apply (simp only: interp.simps I\<^sub>s\<^sub>a.simps I\<^sub>s\<^sub>t.simps \<M>.simps)
        by (metis le_sup_iff)
    qed
  next
    case (mul f)
    with model_for_\<C> \<open>lt \<in> set \<C>\<close> have "I\<^sub>a M\<^sub>v M\<^sub>f (mul(f))" by fastforce
    then have f_mul: "\<forall>s t. (M\<^sub>f f) (s \<sqinter> t) = (M\<^sub>f f) s \<sqinter> (M\<^sub>f f) t" by simp
    have InterOfWAux: "I\<^sub>s\<^sub>a \<M> (Var (InterOfWAux f l m) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>)" for l m
      by auto
    {fix l m assume "l \<subseteq> P\<^sup>+ V" "m \<subseteq> P\<^sup>+ V"
      then have "\<Squnion>HF ((\<M> \<circ> VennRegion) ` (l \<inter> m)) = \<Squnion>HF ((\<M> \<circ> VennRegion) ` l) \<sqinter> \<Squnion>HF ((\<M> \<circ> VennRegion) ` m)"
        using HUnion_proper_Venn_region_inter by force
      then have "\<M> (UnionOfVennRegions (var_set_set_to_var_set_list (l \<inter> m))) =
                 \<M> (UnionOfVennRegions (var_set_set_to_var_set_list l)) \<sqinter>
                 \<M> (UnionOfVennRegions (var_set_set_to_var_set_list m))"
        using set_var_set_set_to_var_set_list \<open>l \<subseteq> P\<^sup>+ V\<close> \<open>m \<subseteq> P\<^sup>+ V\<close>
        by (metis \<M>.simps(3) inf.absorb_iff2 inf_left_commute)
      with f_mul have "\<M> w\<^bsub>f\<^esub>\<^bsub>l\<inter>m\<^esub> = \<M> w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<sqinter> \<M> w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
        by auto
      moreover
      from InterOfWAux have "\<M> (InterOfWAux f l m) = \<M> w\<^bsub>f\<^esub>\<^bsub>l\<^esub> - \<M> w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
        by simp
      ultimately
      have "\<M> w\<^bsub>f\<^esub>\<^bsub>l\<inter>m\<^esub> = \<M> w\<^bsub>f\<^esub>\<^bsub>l\<^esub> - \<M> (InterOfWAux f l m)"
        by auto
      then have "I\<^sub>s\<^sub>a \<M> (Var w\<^bsub>f\<^esub>\<^bsub>l\<inter>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var (InterOfWAux f l m))"
        by auto
    }
    with InterOfWAux show ?thesis
      using mul by auto
  next
    case (le f g)
    show ?thesis
    proof
      fix fml assume "fml \<in> reduce_literal lt"
      then have "fml \<in> reduce_literal (AT\<^sub>m (f \<preceq>\<^sub>m g))"
        using le by blast
      then obtain l where l: "l \<subseteq> P\<^sup>+ V"
                      and fml: "fml = AT (Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub>)"
        by auto
      from model_for_\<C> \<open>lt \<in> set \<C>\<close> le have "I\<^sub>a M\<^sub>v M\<^sub>f (f \<preceq>\<^sub>m g)" by fastforce
      then have "\<forall>s. (M\<^sub>f f) s \<le> (M\<^sub>f g) s" by simp
      then have "M\<^sub>f f (\<Squnion>HF ((\<M> \<circ> VennRegion) ` l)) \<le> M\<^sub>f g (\<Squnion>HF ((\<M> \<circ> VennRegion) ` l))"
        by auto
      with fml l show "interp I\<^sub>s\<^sub>a \<M> fml"
        using set_var_set_set_to_var_set_list
        by (auto simp only: interp.simps I\<^sub>s\<^sub>a.simps I\<^sub>s\<^sub>t.simps \<M>.simps)
    qed
  next
    case (eq_empty x n)
    with \<open>lt \<in> set \<C>\<close> model_for_\<C> have "M\<^sub>v x = 0" by auto
    show ?thesis
    proof
      fix fml assume "fml \<in> reduce_literal lt"
      with eq_empty have "fml = AT (Var (Solo x) =\<^sub>s \<emptyset> n)"
        by simp
      with \<open>M\<^sub>v x = 0\<close> show "interp I\<^sub>s\<^sub>a \<M> fml" by auto
    qed
  next
    case (eq x y)
    with \<open>lt \<in> set \<C>\<close> model_for_\<C> have "M\<^sub>v x = M\<^sub>v y" by auto
    show ?thesis
    proof
      fix fml assume "fml \<in> reduce_literal lt"
      with eq have "fml = AT (Var (Solo x) =\<^sub>s Var (Solo y))"
        by simp
      with \<open>M\<^sub>v x = M\<^sub>v y\<close> show "interp I\<^sub>s\<^sub>a \<M> fml" by auto
    qed
  next
    case (neq x y)
    with \<open>lt \<in> set \<C>\<close> model_for_\<C> have "M\<^sub>v x \<noteq> M\<^sub>v y" by auto
    show ?thesis
    proof
      fix fml assume "fml \<in> reduce_literal lt"
      with neq have "fml = AF (Var (Solo x) =\<^sub>s Var (Solo y))"
        by simp
      with \<open>M\<^sub>v x \<noteq> M\<^sub>v y\<close> show "interp I\<^sub>s\<^sub>a \<M> fml" by auto
    qed
  next
    case (union x y z)
    with \<open>lt \<in> set \<C>\<close> model_for_\<C> have "M\<^sub>v x = M\<^sub>v y \<squnion> M\<^sub>v z" by fastforce
    then have "interp I\<^sub>s\<^sub>a \<M> (AT (Var (Solo x) =\<^sub>s Var (Solo y) \<squnion>\<^sub>s Var (Solo z)))" by simp
    with union show ?thesis by auto
  next
    case (diff x y z)
    with \<open>lt \<in> set \<C>\<close> model_for_\<C> have "M\<^sub>v x = M\<^sub>v y - M\<^sub>v z" by fastforce
    then have "interp I\<^sub>s\<^sub>a \<M> (AT (Var (Solo x) =\<^sub>s Var (Solo y) -\<^sub>s Var (Solo z)))" by simp
    with diff show ?thesis by auto
  next
    case (single x y)
    with \<open>lt \<in> set \<C>\<close> model_for_\<C> have "M\<^sub>v x = HF {M\<^sub>v y}" by fastforce
    then have "interp I\<^sub>s\<^sub>a \<M> (AT (Var (Solo x) =\<^sub>s Single (Var (Solo y))))" by simp
    with single show ?thesis by auto
  next
    case (app x f y)
    with \<open>lt \<in> set \<C>\<close> model_for_\<C>
    have "M\<^sub>v x = (M\<^sub>f f) (M\<^sub>v y)" by fastforce
    moreover
    from app \<open>lt \<in> set \<C>\<close> have "y \<in> V"
      unfolding V_def by force
    with variable_as_composition_of_proper_Venn_regions
    have "M\<^sub>v y = \<Squnion>HF (proper_Venn_region ` \<L> V y)"
      by presburger
    then have "M\<^sub>v y = \<Squnion>HF ((\<M> \<circ> VennRegion) ` \<L> V y)"
      by simp
    ultimately
    have "\<M> (Solo x) = \<M> w\<^bsub>f\<^esub>\<^bsub>\<L> V y\<^esub>"
      using \<M>.simps set_var_set_set_to_var_set_list \<L>_subset_P_plus
      by metis
    with app show ?thesis by simp
  qed
qed

lemma soundness_reduce_cl:
  "\<forall>fml \<in> reduce_clause. interp I\<^sub>s\<^sub>a \<M> fml"
  unfolding reduce_clause_def
  using soundness_reduce_literal
  by fastforce

lemma \<M>_is_model_for_reduced_dnf: "is_model_for_reduced_dnf \<M>"
  unfolding is_model_for_reduced_dnf_def
  unfolding reduced_dnf_def
  using soundness_introduce_v soundness_introduce_w soundness_introduce_UnionOfVennRegions soundness_reduce_cl
  by (metis (no_types, lifting) Un_iff imageI)

end

lemma MLSSmf_to_MLSS_soundness:
  assumes \<C>_norm: "norm_clause \<C>"
      and \<C>_has_model: "\<exists>M\<^sub>v M\<^sub>f. I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>"
    shows "\<exists>M. normalized_MLSSmf_clause.is_model_for_reduced_dnf \<C> M"
proof -
  from \<C>_has_model obtain M\<^sub>v M\<^sub>f where "I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>" by blast
  with \<C>_norm
  interpret satisfiable_normalized_MLSSmf_clause \<C> M\<^sub>v M\<^sub>f
    by unfold_locales
  from \<M>_is_model_for_reduced_dnf show ?thesis by auto
qed

end