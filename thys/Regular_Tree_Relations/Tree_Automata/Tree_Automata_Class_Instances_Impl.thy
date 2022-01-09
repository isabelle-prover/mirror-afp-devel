theory Tree_Automata_Class_Instances_Impl
  imports Tree_Automata
   Deriving.Compare_Instances
   Containers.Collection_Order
   Containers.Collection_Eq
   Containers.Collection_Enum
   Containers.Set_Impl
   Containers.Mapping_Impl
begin

derive linorder ta_rule
derive linorder "term"
derive compare "term"
derive (compare) ccompare "term"
derive ceq ta_rule
derive (eq) ceq fset
derive (eq) ceq FSet_Lex_Wrapper
derive (no) cenum ta_rule
derive (no) cenum FSet_Lex_Wrapper
derive ccompare ta_rule
derive (eq) ceq "term" ctxt
derive (no) cenum "term"
derive (rbt) set_impl fset FSet_Lex_Wrapper ta_rule "term"


instantiation fset :: (linorder) compare
begin
definition compare_fset :: "('a fset \<Rightarrow> 'a fset \<Rightarrow> order)"
  where "compare_fset = (\<lambda> A B.
    (let A' = sorted_list_of_fset A in
     let B' = sorted_list_of_fset B in
     if A' < B' then Lt else if B' < A' then Gt else Eq))"
instance
  apply intro_classes apply (auto simp: compare_fset_def comparator_def Let_def split!: if_splits)
  using sorted_list_of_fset_id apply blast+
  done
end

instantiation fset :: (linorder) ccompare
begin
definition ccompare_fset :: "('a fset \<Rightarrow> 'a fset \<Rightarrow> order) option"
  where "ccompare_fset = Some (\<lambda> A B.
    (let A' = sorted_list_of_fset A in
     let B' = sorted_list_of_fset B in
     if A' < B' then Lt else if B' < A' then Gt else Eq))"
instance
  apply intro_classes apply (auto simp: ccompare_fset_def comparator_def Let_def split!: if_splits)
  using sorted_list_of_fset_id apply blast+
  done
end

instantiation FSet_Lex_Wrapper :: (linorder) compare
begin

definition compare_FSet_Lex_Wrapper :: "'a FSet_Lex_Wrapper \<Rightarrow> 'a FSet_Lex_Wrapper \<Rightarrow> order"
  where "compare_FSet_Lex_Wrapper = (\<lambda> A B.
    (let A' = sorted_list_of_fset (ex A) in
     let B' = sorted_list_of_fset (ex B) in
     if A' < B' then Lt else if B' < A' then Gt else Eq))"

instance
  apply intro_classes apply (auto simp: compare_FSet_Lex_Wrapper_def comparator_def Let_def split!: if_splits)
  using sorted_list_of_fset_id
  by (metis FSet_Lex_Wrapper.expand) 
end

instantiation FSet_Lex_Wrapper :: (linorder) ccompare
begin

definition ccompare_FSet_Lex_Wrapper :: "('a FSet_Lex_Wrapper \<Rightarrow> 'a FSet_Lex_Wrapper \<Rightarrow> order) option"
  where "ccompare_FSet_Lex_Wrapper = Some (\<lambda> A B.
    (let A' = sorted_list_of_fset (ex A) in
     let B' = sorted_list_of_fset (ex B) in
     if A' < B' then Lt else if B' < A' then Gt else Eq))"

instance
  apply intro_classes apply (auto simp: ccompare_FSet_Lex_Wrapper_def comparator_def Let_def split!: if_splits)
  using sorted_list_of_fset_id
  by (metis FSet_Lex_Wrapper.expand) 
end

lemma infinite_ta_rule_UNIV[simp, intro]: "infinite (UNIV :: ('q,'f) ta_rule set)"
proof -
  fix f :: 'f
  fix q :: 'q
  let ?map = "\<lambda> n. (f (replicate n q) \<rightarrow> q)"
  have "inj ?map" unfolding inj_on_def by auto
  from infinite_super[OF _ range_inj_infinite[OF this]]
  show ?thesis by blast
qed

instantiation ta_rule :: (type, type) card_UNIV begin
definition "finite_UNIV = Phantom(('a, 'b) ta_rule) False"
definition "card_UNIV = Phantom(('a, 'b)ta_rule) 0"
instance
  by intro_classes
     (simp_all add: infinite_ta_rule_UNIV card_UNIV_ta_rule_def finite_UNIV_ta_rule_def)
end

instantiation ta_rule :: (ccompare,ccompare)cproper_interval
begin
definition "cproper_interval = (\<lambda> ( _ :: ('a,'b)ta_rule option) _ . False)"
instance by (intro_classes, auto)
end

lemma finite_finite_Fpow:
  assumes "finite A"
  shows "finite (Fpow A)" using assms
proof (induct A)
  case (insert x F)
  {fix X assume ass: "X \<subseteq> insert x F \<and> finite X"
    then have "X - {x} \<subseteq> F" using ass by auto
    then have fpow :"X - {x} \<in> Fpow F" using conjunct2[OF ass]
       by (auto simp: Fpow_def)
    have "X \<in> Fpow F \<union> insert x ` Fpow F"
    proof (cases "x \<in> X")
      case True
      then have "X \<in> insert x ` Fpow F" using fpow
        by (metis True image_eqI insert_Diff)        
      then show ?thesis by simp
    next
      case False
      then show ?thesis using fpow by simp
    qed}
  then have *: "Fpow (insert x F) = Fpow F \<union> insert x ` Fpow F"
    by (auto simp add: Fpow_def image_def)
  show ?case using insert unfolding *
    by simp
qed (auto simp: Fpow_def)

lemma infinite_infinite_Fpow:
  assumes "infinite A"
  shows "infinite (Fpow A)"
proof -
  have inj: "inj (\<lambda> S. {S})" by auto
  have "(\<lambda> S. {S}) ` A \<subseteq> Fpow A" by (auto simp: Fpow_def)
  from finite_subset[OF this] inj assms
  show ?thesis
    by (auto simp: finite_image_iff)
qed

lemma inj_on_Abs_fset:
  "(\<And> X. X \<in> A \<Longrightarrow> finite X) \<Longrightarrow> inj_on Abs_fset A" unfolding inj_on_def
  by (auto simp add: Abs_fset_inject)

lemma UNIV_FSet_Lex_Wrapper:
  "(UNIV :: 'a FSet_Lex_Wrapper set) = (Wrapp \<circ> Abs_fset) ` (Fpow (UNIV :: 'a set))"
  by (simp add: image_def Fpow_def) (metis (mono_tags, lifting) Abs_fset_cases FSet_Lex_Wrapper.exhaust UNIV_eq_I mem_Collect_eq)

lemma FSet_Lex_Wrapper_UNIV:
  "(UNIV :: 'a FSet_Lex_Wrapper set) = (Wrapp \<circ> Abs_fset) ` (Fpow (UNIV :: 'a set))"
  by (simp add: comp_def image_def Fpow_def)
       (metis (mono_tags, lifting) Abs_fset_cases Abs_fset_inverse Collect_cong FSet_Lex_Wrapper.induct iso_tuple_UNIV_I mem_Collect_eq top_set_def)

lemma Wrapp_Abs_fset_inj:
  "inj_on (Wrapp \<circ> Abs_fset) (Fpow A)"
  using inj_on_Abs_fset inj_FSet_Lex_Wrapper Fpow_def
  by (auto simp: inj_on_def inj_def)

lemma infinite_FSet_Lex_Wrapper_UNIV:
  assumes "infinite (UNIV :: 'a set)"
  shows "infinite (UNIV :: 'a FSet_Lex_Wrapper set)"
proof -
  let ?FP = "Fpow (UNIV :: 'a set)"
  have "finite ((Wrapp \<circ> Abs_fset) ` ?FP) \<Longrightarrow> finite ?FP"
    using finite_image_iff[OF Wrapp_Abs_fset_inj]
    by (auto simp: inj_on_def inj_def)
  then show ?thesis unfolding FSet_Lex_Wrapper_UNIV using infinite_infinite_Fpow[OF assms]
    by auto
qed

lemma finite_FSet_Lex_Wrapper_UNIV:
  assumes "finite (UNIV :: 'a set)"
  shows "finite (UNIV :: 'a FSet_Lex_Wrapper set)" using assms
  unfolding FSet_Lex_Wrapper_UNIV
  using finite_image_iff[OF Wrapp_Abs_fset_inj]
  using finite_finite_Fpow[OF assms]
  by simp

instantiation FSet_Lex_Wrapper :: (finite_UNIV) finite_UNIV begin
definition "finite_UNIV = Phantom('a FSet_Lex_Wrapper) 
  (of_phantom (finite_UNIV :: 'a finite_UNIV))"
instance using infinite_FSet_Lex_Wrapper_UNIV
  by intro_classes
    (auto simp add: finite_UNIV_FSet_Lex_Wrapper_def finite_UNIV finite_FSet_Lex_Wrapper_UNIV)
end


instantiation FSet_Lex_Wrapper :: (linorder) cproper_interval begin
fun cproper_interval_FSet_Lex_Wrapper :: "'a FSet_Lex_Wrapper option \<Rightarrow> 'a FSet_Lex_Wrapper option \<Rightarrow> bool"  where
  "cproper_interval_FSet_Lex_Wrapper None None \<longleftrightarrow> True"
| "cproper_interval_FSet_Lex_Wrapper None (Some B) \<longleftrightarrow> (\<exists> Z. sorted_list_of_fset (ex Z) < sorted_list_of_fset (ex B))"
| "cproper_interval_FSet_Lex_Wrapper (Some A) None \<longleftrightarrow> (\<exists> Z. sorted_list_of_fset (ex A) < sorted_list_of_fset (ex Z))"
| "cproper_interval_FSet_Lex_Wrapper (Some A) (Some B) \<longleftrightarrow> (\<exists> Z. sorted_list_of_fset (ex A) < sorted_list_of_fset (ex Z) \<and>
    sorted_list_of_fset (ex Z) < sorted_list_of_fset (ex B))"
declare cproper_interval_FSet_Lex_Wrapper.simps [code del]

lemma lt_of_comp_sorted_list [simp]:
  "ID ccompare = Some f \<Longrightarrow> lt_of_comp f X Z \<longleftrightarrow> sorted_list_of_fset (ex X) < sorted_list_of_fset (ex Z)"
  by (auto simp: lt_of_comp_def ID_code ccompare_FSet_Lex_Wrapper_def Let_def split!: if_splits)

instance by (intro_classes) (auto simp: class.proper_interval_def)
end



lemma infinite_term_UNIV[simp, intro]: "infinite (UNIV :: ('f,'v)term set)"
proof -
  fix f :: 'f and v :: 'v
  let ?inj = "\<lambda>n. Fun f (replicate n (Var v))"
  have "inj ?inj" unfolding inj_on_def by auto
  from infinite_super[OF _ range_inj_infinite[OF this]]
  show ?thesis by blast
qed

instantiation "term" :: (type,type) finite_UNIV
begin
definition "finite_UNIV = Phantom(('a,'b)term) False"
instance
  by (intro_classes, unfold finite_UNIV_term_def, simp)
end



instantiation "term" :: (compare,compare) cproper_interval
begin
definition "cproper_interval = (\<lambda> ( _ :: ('a,'b)term option) _ . False)"
instance by (intro_classes, auto)
end

derive (assoclist) mapping_impl FSet_Lex_Wrapper

end
