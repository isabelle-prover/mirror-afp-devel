theory Type_Instances_Impl
  imports Bot_Terms
    TA_Clousure_Const
    Regular_Tree_Relations.Tree_Automata_Class_Instances_Impl
begin


section \<open>Type class instantiations for the implementation\<close>

derive linorder sum
derive linorder bot_term
derive linorder cl_states

derive compare bot_term
derive compare cl_states

derive (eq) ceq bot_term mctxt cl_states

derive (compare) ccompare bot_term cl_states

derive (rbt) set_impl bot_term cl_states

derive (no) cenum bot_term

instantiation cl_states :: cenum
begin
abbreviation "cl_all_list \<equiv> [cl_state, tr_state, fin_state, fin_clstate]"
definition cEnum_cl_states :: "(cl_states list \<times> ((cl_states \<Rightarrow> bool) \<Rightarrow> bool) \<times> ((cl_states \<Rightarrow> bool) \<Rightarrow> bool)) option"
  where "cEnum_cl_states = Some (cl_all_list, (\<lambda> P. list_all P cl_all_list),  (\<lambda> P. list_ex P cl_all_list))"
instance
  apply intro_classes apply (auto simp: cEnum_cl_states_def elim!: cl_states.induct)
  using cl_states.exhaust apply blast
  by (metis cl_states.exhaust)
end

lemma infinite_bot_term_UNIV[simp, intro]: "infinite (UNIV :: 'f bot_term set)"
proof -
  fix f :: 'f
  let ?inj = "\<lambda>n. BFun f (replicate n Bot)"
  have "inj ?inj" unfolding inj_on_def by auto
  from infinite_super[OF _ range_inj_infinite[OF this]]
  show ?thesis by blast
qed

lemma finite_cl_states: "(UNIV :: cl_states set) = {cl_state, tr_state, fin_state, fin_clstate}"
  using cl_states.exhaust
  by auto

instantiation cl_states :: card_UNIV begin
definition "finite_UNIV = Phantom(cl_states) True"
definition "card_UNIV = Phantom(cl_states) 4"
instance
  by intro_classes (simp_all add: card_UNIV_cl_states_def finite_UNIV_cl_states_def finite_cl_states)
end

instantiation bot_term :: (type) finite_UNIV
begin
definition "finite_UNIV = Phantom('a bot_term) False"
instance
  by (intro_classes, unfold finite_UNIV_bot_term_def, simp)
end


instantiation bot_term :: (compare) cproper_interval
begin
definition "cproper_interval = (\<lambda> ( _ :: 'a bot_term option) _ . False)"
instance by (intro_classes, auto)
end

instantiation cl_states :: cproper_interval
begin

(* cl_all_list *)
definition cproper_interval_cl_states :: "cl_states option \<Rightarrow> cl_states option \<Rightarrow> bool"
  where "cproper_interval_cl_states x y =
   (case ID CCOMPARE(cl_states) of Some f \<Rightarrow>
   (case x of None \<Rightarrow>
     (case y of None \<Rightarrow> True | Some c \<Rightarrow> list_ex (\<lambda> x. (lt_of_comp f) x c) cl_all_list)
   | Some c \<Rightarrow>
     (case y of None \<Rightarrow> list_ex (\<lambda> x. (lt_of_comp f) c x) cl_all_list
      | Some d \<Rightarrow> (filter (\<lambda> x. (lt_of_comp f) x d \<and> (lt_of_comp f) c x) cl_all_list) \<noteq> [])))"

instance
proof (intro_classes)
  assume ass: "(ID ccompare :: (cl_states \<Rightarrow> cl_states \<Rightarrow> order) option) \<noteq> None"
  from ass obtain f where comp: "(ID ccompare :: (cl_states \<Rightarrow> cl_states \<Rightarrow> order) option) = Some f" by auto
  let ?g = "cproper_interval :: cl_states option \<Rightarrow> cl_states option \<Rightarrow> bool"
  have [simp]: "x < y \<longleftrightarrow> lt_of_comp f x y" for x y
    by (metis ID_Some ccompare_cl_states_def comp compare_cl_states_def less_cl_states_def option.sel)
  {fix c d x assume "lt_of_comp f x d" "lt_of_comp f c x"
    then have "c < x" "x < d" by simp_all}
  moreover
  {fix c d assume "\<exists> z. (c ::cl_states) < z \<and> z < d"
    then obtain z where w: "c < z \<and> z < d" by blast
    then have "z \<in> set cl_all_list" by (cases z) auto
    moreover have "lt_of_comp f z d \<and> lt_of_comp f c z" using w comp
      by auto
    ultimately have "filter (\<lambda>x. lt_of_comp f x d \<and> lt_of_comp f c x) cl_all_list \<noteq> []" using w
      by auto}
  ultimately have "filter (\<lambda>x. lt_of_comp f x d \<and> lt_of_comp f c x) cl_all_list \<noteq> [] \<longleftrightarrow> (\<exists> z. c < z \<and> z < d)" for d c using comp
    unfolding filter_empty_conv by simp blast
  then have "?g (Some x) (Some y) = (\<exists> z. x < z \<and> z < y)" for x y
    by (simp add: comp cproper_interval_cl_states_def)
  moreover have "?g None None = True" by (simp add: comp cproper_interval_cl_states_def)
  moreover have "?g None (Some y) = (\<exists>z. z < y)" for y using comp
    by (auto simp add: cproper_interval_cl_states_def ccompare_cl_states_def) (metis cl_states.exhaust)+
  moreover have "?g (Some y) None = (\<exists>z. y < z)" for y using comp
    by (auto simp add: cproper_interval_cl_states_def) (metis cl_states.exhaust)+
  ultimately show "class.proper_interval cless ?g"
    unfolding class.proper_interval_def comp
    by simp
qed
end

derive (rbt) mapping_impl cl_states
derive (rbt) mapping_impl bot_term

end