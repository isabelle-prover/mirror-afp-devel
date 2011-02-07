header {* HOLCF Utility lemmas *}
theory HOLCFUtils
imports HOLCF
begin

text {*
We use @{theory HOLCF} to define the denotational semantics. By default, HOLCF does not turn the regular @{text set} type into a partial order, so this is done here. Some of the lemmas here are contributed by Brian Huffman.

We start by making the type @{text bool} a pointed chain-complete partial order. Because @{text "'a set"} is just an abbreviation for @{text "'a => bool"}, this gives us a pcpo for sets.
*}

instantiation bool :: po
begin
definition
  "x \<sqsubseteq> y \<longleftrightarrow> (x \<longrightarrow> y)"
instance by (default, unfold below_bool_def, fast+)
end

instance bool :: chfin
apply default
apply (drule finite_range_imp_finch)
apply (rule finite)
apply (simp add: finite_chain_def)
done

instance bool :: pcpo
proof
  have "\<forall>y. False \<sqsubseteq> y" by (simp add: below_bool_def)
  thus "\<exists>x::bool. \<forall>y. x \<sqsubseteq> y" ..
qed

lemma bottom_eq_False[simp]: "\<bottom> = False"
by (rule below_antisym [OF minimal], simp add: below_bool_def)

text {*
To convert between the squared syntax used by @{theory HOLCF} and the regular, round syntax for sets, we state some of the equivalencies.
*}

lemma sqsubset_is_subset:"A \<sqsubseteq> B \<longleftrightarrow> A \<subseteq> B"
unfolding below_fun_def and below_bool_def
  by (auto simp:mem_def)

lemma lub_is_union: "lub S = \<Union>S"
apply(rule lub_eqI)
  unfolding is_lub_def and is_ub_def
  by (auto iff:sqsubset_is_subset)

lemma const_False_is_bot[simp]: "(\<lambda>a. False) = {}" 
  by (rule ext, auto)

lemma bot_bool_is_emptyset[simp]: "\<bottom> = {}"
  by (simp add:inst_fun_pcpo)

lemma emptyset_is_bot[simp]: "{} \<sqsubseteq> S"
  by (simp add:sqsubset_is_subset)

text {*
To actually use these instance in @{text fixrec} definitions or fixed-point inductions, we need continuity requrements for various boolean and set operations.
*}

lemma cont2cont_disj [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)" and g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x \<or> g x)"
apply (rule cont_apply [OF f])
apply (rule chfindom_monofun2cont)
apply (rule monofunI, simp add: below_bool_def)
apply (rule cont_compose [OF _ g])
apply (rule chfindom_monofun2cont)
apply (rule monofunI, simp add: below_bool_def)
done

lemma cont2cont_imp[simp, cont2cont]:
  assumes f: "cont (\<lambda>x. \<not> f x)" and g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x \<longrightarrow> g x)"
unfolding imp_conv_disj by (rule cont2cont_disj[OF f g])

lemma cont2cont_Collect [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. {y. f x y})"
unfolding Collect_def using assms
by (rule cont2cont_lambda)

lemma cont2cont_mem [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)"
  shows "cont (\<lambda>x. y \<in> f x)"
unfolding mem_def using assms
by (rule cont2cont_fun)

lemma cont2cont_union [simp, cont2cont]:
  "cont (\<lambda>x. f x) \<Longrightarrow> cont (\<lambda>x. g x)
\<Longrightarrow> cont (\<lambda>x. f x \<union> g x)"
unfolding Un_def by simp

lemma cont2cont_insert [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)"
  shows "cont (\<lambda>x. insert y (f x))"
unfolding insert_def using assms
by (intro cont2cont)

lemmas adm_subset = adm_below[where ?'b = "'a::type set", standard, unfolded sqsubset_is_subset]

lemma cont2cont_UNION[cont2cont,simp]:
  assumes "cont f"
      and "\<And> y. cont (\<lambda>x. g x y)"
  shows "cont (\<lambda>x. \<Union>y\<in> f x. g x y)"
proof(induct rule: contI2[case_names Mono Limit])
case Mono
  show "monofun (\<lambda>x. \<Union>y\<in>f x. g x y)"
    by (rule monofunI)(auto iff:sqsubset_is_subset dest: monofunE[OF assms(1)[THEN cont2mono]] monofunE[OF assms(2)[THEN cont2mono]])
next
case (Limit Y)
  have "(\<Union>y\<in>f (\<Squnion> i. Y i). g (\<Squnion> j. Y j) y) \<subseteq> (\<Squnion> k. \<Union>y\<in>f (Y k). g (Y k) y)"
  proof
    fix x assume "x \<in> (\<Union>y\<in>f (\<Squnion> i. Y i). g (\<Squnion> j. Y j) y)"
    then obtain y where "y\<in>f (\<Squnion> i. Y i)" and "x\<in> g (\<Squnion> j. Y j) y" by auto
    hence "y \<in> (\<Squnion> i. f (Y i))" and "x\<in> (\<Squnion> j. g (Y j) y)" by (auto simp add: cont2contlubE[OF assms(1) Limit(1)] cont2contlubE[OF assms(2) Limit(1)])
    then obtain i and j where yi: "y\<in> f (Y i)" and xj: "x\<in> g (Y j) y" by (auto simp add:lub_is_union)
    obtain k where "i\<le>k" and "j\<le>k" by (erule_tac x = "max i j" in meta_allE)auto
    from yi and xj have "y \<in> f (Y k)" and "x\<in> g (Y k) y"
      using monofunE[OF assms(1)[THEN cont2mono], OF chain_mono[OF Limit(1) `i\<le>k`]]
        and monofunE[OF assms(2)[THEN cont2mono], OF chain_mono[OF Limit(1) `j\<le>k`]]
      by (auto simp add:sqsubset_is_subset)
    hence "x\<in> (\<Union>y\<in> f (Y k). g (Y k) y)" by auto
    thus "x\<in> (\<Squnion> k. \<Union>y\<in>f (Y k). g (Y k) y)" by (auto simp add:lub_is_union)
  qed
  thus ?case by (simp add:sqsubset_is_subset)
qed

lemma cont2cont_Let_simple[simp,cont2cont]:
  assumes "cont (\<lambda>x. g x t)"
  shows "cont (\<lambda>x. let y = t in g x y)"
unfolding Let_def using assms .


lemma cont2cont_list_case [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x)"
     and  "\<And>y z. cont (\<lambda>x. f2 x y z)"
  shows "cont (\<lambda>x. list_case (f1 x) (f2 x) l)"
using assms
by (cases l) auto


text {* As with the continuity lemmas, we need admissibility lemmas. *}

lemma adm_not_mem:
  assumes "cont (\<lambda>x. f x)"
  shows "adm (\<lambda>x. y \<notin> f x)"
using assms
apply (erule_tac t = f in adm_subst)
proof (rule admI)
fix Y :: "nat \<Rightarrow> 'b \<Rightarrow> bool"
assume chain: "chain Y"
assume "\<forall>i. y \<notin> Y i" hence  "(\<Squnion> i. Y i y) = False"
  unfolding mem_def by (auto simp del: const_False_is_bot)
thus "y \<notin> (\<Squnion> i. Y i)"
  using chain unfolding mem_def by (subst lub_fun) auto
qed

lemma adm_id[simp]: "adm (\<lambda>x . x)"
by (rule adm_chfin)

lemma adm_Not[simp]: "adm Not"
by (rule adm_chfin)

lemma adm_prod_split:
  assumes "adm (\<lambda>p. f (fst p) (snd p))"
  shows "adm (\<lambda>(x,y). f x y)"
using assms unfolding split_def .

lemma adm_ball':
  assumes "\<And> y. adm (\<lambda>x. y \<in> A x \<longrightarrow> P x y)"
  shows "adm (\<lambda>x. \<forall>y \<in> A x . P x y)"
by (subst Ball_def, rule adm_all[OF assms])

lemma adm_not_conj:
  "\<lbrakk>adm (\<lambda>x. \<not> P x); adm (\<lambda>x. \<not> Q x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. \<not> (P x \<and> Q x))"
by simp

lemma adm_single_valued:
 assumes "cont (\<lambda>x. f x)"
 shows "adm (\<lambda>x. single_valued (f x))"
using assms
unfolding single_valued_def
by (intro adm_lemmas adm_not_mem cont2cont adm_subst[of f])

text {*
To match Shivers' syntax we introduce the power-syntax for iterated function application.
*}

abbreviation niceiterate ("(_\<^bsup>_\<^esup>)" [1000] 1000)
  where "niceiterate f i \<equiv> iterate i\<cdot>f"

end
