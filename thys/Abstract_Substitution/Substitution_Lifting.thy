theory Substitution_Lifting \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  imports Substitution Natural_Magma_Functor
begin


section \<open>Lifting of substitutions using natural functors\<close>

locale substitution_lifting =
  sub: substitution where 
  subst = sub_subst and vars = sub_vars and apply_subst = apply_subst and
  is_ground = sub_is_ground +
  non_empty_natural_functor where map = map and to_set = to_set
  for
    sub_vars :: "'sub \<Rightarrow> 'v set" and
    sub_subst :: "'sub \<Rightarrow> 'subst \<Rightarrow> 'sub" and
    sub_is_ground :: "'sub \<Rightarrow> bool" and
    map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr" and
    to_set :: "'expr \<Rightarrow> 'sub set" and
    apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl "\<cdot>v" 69)
begin

definition vars :: "'expr \<Rightarrow> 'v set" where
  "vars expr \<equiv> \<Union> (sub_vars ` to_set expr)"

definition is_ground :: "'expr \<Rightarrow> bool" where
  "is_ground expr \<equiv> \<forall>sub \<in> to_set expr. sub_is_ground sub"

notation sub_subst (infixl "\<cdot>\<^sub>s" 70)

definition subst :: "'expr \<Rightarrow> 'subst \<Rightarrow> 'expr" (infixl "\<cdot>" 70) where
  "expr \<cdot> \<sigma> \<equiv> map (\<lambda>sub. sub \<cdot>\<^sub>s \<sigma>) expr"

lemma subst_in_to_set_subst [intro]:
  assumes "sub \<in> to_set expr"
  shows "sub \<cdot>\<^sub>s \<sigma> \<in> to_set (expr \<cdot> \<sigma>)"
  unfolding subst_def to_set_map
  using assms
  by simp

sublocale substitution where subst = "(\<cdot>)" and vars = vars and is_ground = is_ground
proof unfold_locales
  fix expr \<sigma>\<^sub>1 \<sigma>\<^sub>2

  show "expr \<cdot> (\<sigma>\<^sub>1 \<odot> \<sigma>\<^sub>2) = expr \<cdot> \<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2"
    unfolding subst_def map_comp comp_apply sub.subst_comp_subst ..
next
  fix expr

  show "expr \<cdot> id_subst = expr"
    using map_ident
    unfolding subst_def sub.subst_id_subst .
next
  fix expr
  assume "is_ground expr"

  then show "\<forall>\<sigma>. expr \<cdot> \<sigma> = expr"
    unfolding subst_def is_ground_def
    by simp
next
  fix expr 
  assume "is_ground expr"

  then show "vars expr = {}"
    unfolding is_ground_def vars_def
    by (simp add: sub.no_vars_if_is_ground)
qed

lemma exists_nonground_iff_sub_exists_nonground: "exists_nonground \<longleftrightarrow> sub.exists_nonground"
  using exists_functor is_ground_def
  by fastforce

lemma ground_subst_iff_sub_ground_subst [simp]: "is_ground_subst \<gamma> \<longleftrightarrow> sub.is_ground_subst \<gamma>"
proof(unfold is_ground_subst_def sub.is_ground_subst_def, intro iffI allI)
  fix sub
  assume all_ground: "\<forall>expr. is_ground (expr \<cdot> \<gamma>)"
  show "sub_is_ground (sub \<cdot>\<^sub>s \<gamma>)"
  proof(rule ccontr)
    assume sub_not_ground: "\<not>sub_is_ground (sub \<cdot>\<^sub>s \<gamma>)"

    then obtain expr where "sub \<in> to_set expr"
      using exists_functor 
      by blast

    then have "\<not>is_ground (expr \<cdot> \<gamma>)"
      using sub_not_ground to_set_map
      unfolding subst_def is_ground_def
      by auto

    then show False
      using all_ground
      by blast
  qed
next
  fix expr
  assume "\<forall>sub. sub_is_ground (sub \<cdot>\<^sub>s \<gamma>)"

  then show "is_ground (expr \<cdot> \<gamma>)"
    unfolding is_ground_def subst_def
    using to_set_map
    by simp
qed

lemma to_set_is_ground [intro]:
  assumes "sub \<in> to_set expr" "is_ground expr"
  shows "sub_is_ground sub"
  using assms
  by (simp add: is_ground_def)

lemma to_set_is_ground_subst:
  assumes "sub \<in> to_set expr" "is_ground (expr \<cdot> \<gamma>)"
  shows "sub_is_ground (sub \<cdot>\<^sub>s \<gamma>)"
  using assms
  by (meson subst_in_to_set_subst to_set_is_ground)

lemma subst_empty:
  assumes "to_set expr' = {}"
  shows "expr \<cdot> \<sigma> = expr' \<longleftrightarrow> expr = expr'"
  using assms map_id_cong to_set_map
  unfolding subst_def
  by (metis empty_iff image_is_empty)

lemma empty_is_ground:
  assumes "to_set expr = {}"
  shows "is_ground expr"
  using assms
  by (simp add: is_ground_def)

lemma to_set_image: "to_set (expr \<cdot> \<sigma>) = (\<lambda>a. a \<cdot>\<^sub>s \<sigma>) ` to_set expr"
  unfolding subst_def to_set_map ..

lemma to_set_subset_vars_subset:
  assumes "to_set expr \<subseteq> to_set expr'"
  shows "vars expr \<subseteq> vars expr'"
  using assms
  unfolding vars_def
  by blast

lemma to_set_subset_is_ground:
  assumes "to_set expr' \<subseteq> to_set expr" "is_ground expr"
  shows "is_ground expr'"
  using assms to_set_subset_vars_subset is_ground_def
  by auto

end


subsection \<open>Lifting of properties\<close>

locale subst_update_lifting =
  sub: subst_update where 
  vars = "sub_vars :: 'sub \<Rightarrow> 'v set" and subst = sub_subst and is_ground = sub_is_ground +
  substitution_lifting
begin

sublocale subst_update where vars = vars and subst = subst and is_ground = is_ground
proof unfold_locales
  fix \<sigma> x update
  assume "exists_nonground"

  then show "x \<cdot>v \<sigma>\<lbrakk>x := update\<rbrakk> = update"
    unfolding is_ground_def
    using sub.subst_update_var(1)
    by fastforce
next
  fix x expr update \<sigma>
  assume "x \<notin> vars expr"

  then show "expr \<cdot> \<sigma>\<lbrakk>x := update\<rbrakk> = expr \<cdot> \<sigma>"
    unfolding vars_def subst_def
    by auto
qed simp_all

end

locale subst_updates_lifting =
  sub: subst_updates where 
  vars = "sub_vars :: 'sub \<Rightarrow> 'v set" and subst = sub_subst and is_ground = sub_is_ground +
  substitution_lifting
begin

sublocale subst_updates where vars = vars and subst = subst and is_ground = is_ground
proof unfold_locales
  fix x \<sigma> update 
  assume "exists_nonground"

  then show "x \<cdot>v \<sigma>\<lbrakk>update\<rbrakk> = get_or (update x) (x \<cdot>v \<sigma>)"
    by (simp add: exists_nonground_iff_sub_exists_nonground)
next
  fix expr \<sigma> b

  show "expr \<cdot> \<sigma>\<lbrakk>\<lambda>x. if x \<in> vars expr then None else b x\<rbrakk> = expr \<cdot> \<sigma>"
    unfolding subst_def vars_def
    by (smt (verit, ccfv_SIG) UN_I local.map_cong sub.redundant_subst_updates)
qed

end

locale finite_variables_lifting =
  sub: finite_variables where 
  vars = "sub_vars :: 'sub \<Rightarrow> 'v set" and subst = sub_subst and is_ground = sub_is_ground +
  finite_natural_functor where to_set = "to_set :: 'expr \<Rightarrow> 'sub set" +
  substitution_lifting
begin

abbreviation to_fset :: "'expr \<Rightarrow> 'sub fset" where
  "to_fset expr \<equiv> Abs_fset (to_set expr)"

sublocale finite_variables where vars = vars and subst = subst and is_ground = is_ground
  by unfold_locales (auto simp: vars_def finite_to_set)

lemma fset_to_fset [simp]: "fset (to_fset expr) = to_set expr"
  using Abs_fset_inverse finite_to_set
  by blast

lemma to_fset_map: "to_fset (map f expr) = f |`| to_fset expr"
  using to_set_map
  by (metis fset.set_map fset_inverse fset_to_fset)

lemma to_fset_is_ground_subst:
  assumes "sub |\<in>| to_fset expr" "is_ground (subst expr \<gamma>)"
  shows "sub_is_ground (sub \<cdot>\<^sub>s \<gamma>)"
  using assms
  by (simp add: to_set_is_ground_subst)

end

locale renaming_variables_lifting =
  substitution_lifting +
  sub: renaming_variables where vars = sub_vars and subst = sub_subst and is_ground = sub_is_ground
begin

sublocale renaming_variables where subst = subst and vars = vars and is_ground = is_ground
proof unfold_locales
  fix expr \<rho>
  assume "sub.is_renaming \<rho>"

  then show "vars (expr \<cdot> \<rho>) = rename \<rho> ` vars expr"
    using sub.rename_variables
    unfolding vars_def subst_def to_set_map
    by fastforce
next
  fix \<rho>
  assume "exists_nonground"

  then show "sub.is_renaming \<rho> \<Longrightarrow> (inj (\<lambda>x. x \<cdot>v \<rho>) \<and> (\<forall>x. \<exists>x'. x \<cdot>v \<rho> = x' \<cdot>v id_subst))"
    unfolding is_ground_def
    using sub.is_renaming_imp
    by auto
qed

end

locale exists_ground_subst_lifting = 
  substitution_lifting +
  sub: exists_ground_subst where vars = sub_vars and subst = sub_subst and is_ground = sub_is_ground
begin

sublocale exists_ground_subst where vars = vars and subst = subst and is_ground = is_ground
proof unfold_locales
  show "\<exists>\<gamma>. is_ground_subst \<gamma>"
    by (simp add: sub.exists_ground_subst)
qed

end

locale grounding_lifting =
  substitution_lifting where sub_vars = sub_vars and sub_subst = sub_subst and map = map +
  sub: grounding where vars = sub_vars and subst = sub_subst and to_ground = sub_to_ground and
    from_ground = sub_from_ground and is_ground = sub_is_ground +
  natural_functor_conversion where map = map and map_to = to_ground_map and
    map_from = from_ground_map and map' = ground_map and to_set' = to_set_ground
  for
    sub_to_ground :: "'sub \<Rightarrow> 'sub\<^sub>G" and
    sub_from_ground :: "'sub\<^sub>G \<Rightarrow> 'sub" and
    sub_vars :: "'sub \<Rightarrow> 'var set" and
    sub_subst :: "'sub \<Rightarrow> 'subst \<Rightarrow> 'sub" and
    map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr" and
    to_ground_map :: "('sub \<Rightarrow> 'sub\<^sub>G) \<Rightarrow> 'expr \<Rightarrow> 'expr\<^sub>G" and
    from_ground_map :: "('sub\<^sub>G \<Rightarrow> 'sub) \<Rightarrow> 'expr\<^sub>G \<Rightarrow> 'expr" and
    ground_map :: "('sub\<^sub>G \<Rightarrow> 'sub\<^sub>G) \<Rightarrow> 'expr\<^sub>G \<Rightarrow> 'expr\<^sub>G" and
    to_set_ground :: "'expr\<^sub>G \<Rightarrow> 'sub\<^sub>G set"
begin

definition to_ground :: "'expr \<Rightarrow> 'expr\<^sub>G" where
  "to_ground expr \<equiv> to_ground_map sub_to_ground expr"

definition from_ground :: "'expr\<^sub>G \<Rightarrow> 'expr" where
  "from_ground expr\<^sub>G \<equiv> from_ground_map sub_from_ground expr\<^sub>G"

sublocale grounding where
  vars = vars and subst = subst and to_ground = to_ground and from_ground = from_ground and
  is_ground = is_ground
proof unfold_locales

  {
    fix expr

    assume "is_ground expr"

    then have "\<forall>sub\<in>to_set expr. sub \<in> range sub_from_ground"
      by (simp add: sub.is_ground_iff_range_from_ground is_ground_def)

    then have "\<forall>sub\<in>to_set expr. \<exists>sub\<^sub>G. sub_from_ground sub\<^sub>G = sub"
      by fast

    then have "\<exists>expr\<^sub>G. from_ground expr\<^sub>G = expr"
      unfolding from_ground_def
      by (metis conversion_map_comp map_id_cong)

    then have "expr \<in> range from_ground"
      unfolding from_ground_def
      by blast
  }

  then show "{expr. is_ground expr} = range from_ground"
    by (simp add: from_ground_def is_ground_def subset_antisym subset_eq)
next
  fix expr\<^sub>G
  show "to_ground (from_ground expr\<^sub>G) = expr\<^sub>G"
    unfolding from_ground_def to_ground_def
    by simp
qed

lemma to_set_from_ground: "to_set (from_ground expr) = sub_from_ground ` (to_set_ground expr)"
  unfolding from_ground_def
  by simp

lemma sub_in_ground_is_ground:
  assumes "sub \<in> to_set (from_ground expr)"
  shows "sub_is_ground sub"
  using assms
  by (simp add: to_set_is_ground)

lemma ground_sub_in_ground:
  "sub \<in> to_set_ground expr \<longleftrightarrow> sub_from_ground sub \<in> to_set (from_ground expr)"
  by (simp add: inj_image_mem_iff sub.inj_from_ground to_set_from_ground)

lemma ground_sub:
  "(\<forall>sub \<in> to_set (from_ground expr\<^sub>G). P sub) \<longleftrightarrow>
   (\<forall>sub\<^sub>G \<in> to_set_ground expr\<^sub>G. P (sub_from_ground sub\<^sub>G))"
  by (simp add: to_set_from_ground)

end

locale exists_non_ident_subst_lifting = 
  finite_variables_lifting where map = map +
  sub: exists_non_ident_subst where subst = sub_subst and vars = sub_vars and
  is_ground = sub_is_ground
for map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr"
begin

sublocale exists_non_ident_subst where subst = subst and vars = vars and is_ground = is_ground
proof unfold_locales
  fix expr :: 'expr and S :: "'expr set"

  assume finite: "finite S" and not_ground: "\<not> is_ground expr"

  then have finite_subs: "finite (\<Union>(to_set ` insert expr S))"
    using finite_to_set 
    by blast

  obtain sub where sub: "sub \<in> to_set expr" and sub_not_ground: "\<not> sub_is_ground sub"
    using not_ground
    unfolding is_ground_def
    by blast

  obtain \<sigma> where \<sigma>_not_ident: "sub \<cdot>\<^sub>s \<sigma> \<noteq> sub" "sub \<cdot>\<^sub>s \<sigma> \<notin> \<Union> (to_set ` insert expr S)"
    using sub.exists_non_ident_subst[OF finite_subs sub_not_ground]
    by blast

  then have "expr \<cdot> \<sigma> \<noteq> expr"
    using sub
    unfolding subst_def
    by (simp add: to_set_map_not_ident)

  moreover have "expr \<cdot> \<sigma> \<notin> S"
    using \<sigma>_not_ident(2) sub to_set_map
    unfolding subst_def
    by auto

  ultimately show "\<exists>\<sigma>. expr \<cdot> \<sigma> \<noteq> expr \<and> expr \<cdot> \<sigma> \<notin> S"
    by blast
qed

end

locale all_subst_ident_iff_ground_lifting =
  exists_non_ident_subst_lifting where map = map +
  sub: all_subst_ident_iff_ground where 
  subst = sub_subst and vars = sub_vars and is_ground = sub_is_ground
for map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr"
begin

sublocale all_subst_ident_iff_ground where subst = subst and vars = vars and is_ground = is_ground
proof unfold_locales
  fix expr

  show "is_ground expr \<longleftrightarrow> (\<forall>\<sigma>. expr \<cdot> \<sigma> = expr)"
  proof(rule iffI allI)
    assume "is_ground expr"

    then show "\<forall>\<sigma>. expr \<cdot> \<sigma> = expr"
      by simp
  next
    assume all_subst_ident: "\<forall>\<sigma>. expr \<cdot> \<sigma> = expr"

    show "is_ground expr"
    proof(rule ccontr)
      assume "\<not>is_ground expr"

      then obtain sub where sub: "sub \<in> to_set expr" "\<not>sub_is_ground sub"
        unfolding is_ground_def
        by blast

      then obtain \<sigma> where "sub \<cdot>\<^sub>s \<sigma> \<noteq> sub" and "sub \<cdot>\<^sub>s \<sigma> \<notin> to_set expr"
        using sub.exists_non_ident_subst finite_to_set
        by blast

      then show False
        using sub subst_in_to_set_subst all_subst_ident
        by metis
    qed
  qed
qed

end

locale natural_magma_substitution_lifting = substitution_lifting + natural_magma
begin

lemma vars_add [simp]:
  "vars (add sub expr) = sub_vars sub \<union> vars expr"
  unfolding vars_def
  using to_set_add by auto

lemma vars_plus [simp]:
  "vars (plus expr expr') = vars expr \<union> vars expr'"
  unfolding vars_def
  by simp

lemma is_ground_plus [simp]:
  "is_ground (plus expr expr') \<longleftrightarrow> is_ground expr \<and> is_ground expr'"
  unfolding is_ground_def
  by auto

lemma is_ground_add [simp]:
  "is_ground (add sub expr) \<longleftrightarrow> sub_is_ground sub \<and> is_ground expr"
  unfolding is_ground_def
  by simp

end

locale natural_magma_functor_substitution_lifting =
  natural_magma_substitution_lifting + natural_magma_functor
begin

lemma add_subst [simp]:
  "(add sub expr) \<cdot> \<sigma> = add (sub \<cdot>\<^sub>s \<sigma>) (expr \<cdot> \<sigma>)"
  unfolding subst_def
  using map_add
  by simp

lemma plus_subst [simp]: "(plus expr expr') \<cdot> \<sigma> = plus (expr \<cdot> \<sigma>) (expr' \<cdot> \<sigma>)"
  unfolding subst_def
  using map_plus
  by simp

end

locale natural_magma_grounding_lifting =
  grounding_lifting +
  natural_magma_substitution_lifting +
  ground: natural_magma where
  to_set = to_set_ground and plus = plus_ground and wrap = wrap_ground and add = add_ground
for plus_ground wrap_ground add_ground +
assumes
  to_ground_plus [simp]:
   "\<And>expr expr'. to_ground (plus expr expr') = plus_ground (to_ground expr) (to_ground expr')" and
  wrap_from_ground: "\<And>sub. from_ground (wrap_ground sub) = wrap (sub_from_ground sub)" and
  wrap_to_ground: "\<And>sub. to_ground (wrap sub) = wrap_ground (sub_to_ground sub)"
begin

lemma from_ground_plus [simp]:
  "from_ground (plus_ground expr expr') = plus (from_ground expr) (from_ground expr')"
  using to_ground_plus
  by (metis from_ground_inverse ground_is_ground to_ground_inverse is_ground_plus)

lemma from_ground_add [simp]:
  "from_ground (add_ground sub expr) = add (sub_from_ground sub) (from_ground expr)"
  unfolding ground.add_def add_def
  using from_ground_plus
  by (simp add: wrap_from_ground)

lemma to_ground_add [simp]:
  "to_ground (add sub expr) = add_ground (sub_to_ground sub) (to_ground expr)"
  unfolding ground.add_def add_def
  using from_ground_add wrap_to_ground
  by simp

lemma ground_add:
  assumes "from_ground expr = add sub expr'"
  shows "expr = add_ground (sub_to_ground sub) (to_ground expr')"
  using assms
  by (metis from_ground_inverse to_ground_add)

end

locale natural_magma_with_empty_grounding_lifting =
  natural_magma_grounding_lifting +
  natural_magma_with_empty +
  ground: natural_magma_with_empty where 
  to_set = to_set_ground and plus = plus_ground and wrap = wrap_ground and add = add_ground and 
  empty = empty_ground
for empty_ground +
assumes to_ground_empty [simp]: "to_ground empty = empty_ground"
begin

lemmas empty_magma_is_ground [simp] = empty_is_ground[OF to_set_empty]

lemmas magma_subst_empty [simp] =
  subst_ident_if_ground[OF empty_magma_is_ground]
  subst_empty[OF to_set_empty]

lemma from_ground_empty [simp]: "from_ground empty_ground = empty"
  using to_ground_inverse[OF empty_magma_is_ground]
  by simp

lemma to_ground_empty' [simp]: "to_ground expr = empty_ground \<longleftrightarrow> expr = empty"
  using from_ground_empty to_ground_empty ground.to_set_empty to_ground_inverse
  unfolding to_ground_def is_ground_def
  by fastforce

lemma from_ground_empty' [simp]: "from_ground expr = empty \<longleftrightarrow> expr = empty_ground"
  using from_ground_empty from_ground_eq
  unfolding from_ground_def  
  by auto

end

(* TODO: Not compatible with polymorphic terms *)
locale subst_updates_compat_lifting = 
  subst_updates_lifting +
  sub: subst_updates_compat where 
  vars = sub_vars and subst = sub_subst and is_ground = sub_is_ground
begin

sublocale subst_updates_compat where vars = vars and subst = subst and is_ground = is_ground
proof unfold_locales
  fix expr X \<sigma> b

  assume "vars expr \<subseteq> X"

  then have "\<forall>sub \<in> to_set expr. sub_vars sub \<subseteq> X"
    unfolding vars_def
    by blast

  then have "\<forall>sub \<in> to_set expr. sub \<cdot>\<^sub>s id_subst\<lbrakk>\<lambda>x. if x \<in> X then Some (x \<cdot>v \<sigma>) else b x\<rbrakk> = sub \<cdot>\<^sub>s \<sigma>"
    by (simp add: sub.subst_updates_compat(1))

  then show "expr \<cdot> id_subst\<lbrakk>\<lambda>x. if x \<in> X then Some (x \<cdot>v \<sigma>) else b x\<rbrakk> = expr \<cdot> \<sigma>"
    unfolding subst_def
    by simp
next
  fix expr X \<sigma> b
  assume "vars expr \<inter> X = {}"

  then have "\<forall>sub \<in> to_set expr. sub_vars sub \<inter> X = {}"
    unfolding vars_def
    by blast

  then have "\<forall>sub \<in> to_set expr. sub \<cdot>\<^sub>s id_subst\<lbrakk>\<lambda>x. if x \<in> X then b x else Some (x \<cdot>v \<sigma>)\<rbrakk> = sub \<cdot>\<^sub>s \<sigma>"
    by (simp add: sub.subst_updates_compat(2))
  
  then show "expr \<cdot> id_subst\<lbrakk>\<lambda>x. if x \<in> X then b x else Some (x \<cdot>v \<sigma>)\<rbrakk> = expr \<cdot> \<sigma>"
    unfolding subst_def
    by simp
qed

end

locale subst_eq_lifting =
  sub: subst_eq where
  vars = "sub_vars :: 'sub \<Rightarrow> 'v set" and subst = sub_subst and is_ground = sub_is_ground +
  substitution_lifting
begin

sublocale subst_eq where vars = vars and subst = subst and is_ground = is_ground
proof unfold_locales
  fix expr \<sigma> \<tau> 
  assume "\<And>x. x \<in> vars expr \<Longrightarrow> x \<cdot>v \<sigma> = x \<cdot>v \<tau>"

  then show "expr \<cdot> \<sigma> = expr \<cdot> \<tau>"
    unfolding vars_def subst_def
    using sub.subst_eq
    by (meson UN_I local.map_cong)
qed

end

locale is_ground_if_no_vars_lifting = 
  substitution_lifting + 
  sub: is_ground_if_no_vars where
  vars = sub_vars and is_ground = sub_is_ground and subst = sub_subst
begin

sublocale is_ground_if_no_vars where vars = vars and is_ground = is_ground and subst = subst
  by unfold_locales (simp add: is_ground_def sub.is_ground_if_no_vars vars_def)

end

end
