section \<open> Map Type: extra functions and properties \<close>

theory Map_Extra
  imports
  Relation_Extra
  "HOL-Library.Countable_Set"
  "HOL-Library.Monad_Syntax"
  "HOL-Library.AList"
begin

subsection \<open> Extensionality and Update \<close>

lemma map_eq_iff: "f = g \<longleftrightarrow> (\<forall> x \<in> dom(f) \<union> dom(g). f x = g x)"
  by (auto simp add: fun_eq_iff)

subsection \<open> Graphing Maps \<close>

definition map_graph :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b)" where
"map_graph f = {(x,y) | x y. f x = Some y}"

definition graph_map :: "('a \<leftrightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"graph_map g = (\<lambda> x. if (x \<in> fst ` g) then Some (SOME y. (x,y) \<in> g) else None)"

definition graph_map' :: "('a \<leftrightarrow> 'b) \<rightharpoonup> ('a \<rightharpoonup> 'b)" where
"graph_map' R = (if (functional R) then Some (graph_map R) else None)"

lemma map_graph_mem_equiv: "(x, y) \<in> map_graph f \<longleftrightarrow> f(x) = Some y"
  by (simp add: map_graph_def)

lemma map_graph_functional[simp]: "functional (map_graph f)"
  by (simp add:functional_def map_graph_def inj_on_def)

lemma map_graph_countable [simp]: "countable (dom f) \<Longrightarrow> countable (map_graph f)"
  by (metis countable_image graph_def graph_eq_to_snd_dom map_graph_def)

lemma map_graph_inv [simp]: "graph_map (map_graph f) = f"
  by (force simp add:map_graph_def graph_map_def image_def)

lemma graph_map_empty[simp]: "graph_map {} = Map.empty"
  by (simp add:graph_map_def)

lemma graph_map_insert [simp]: "\<lbrakk>functional g; g``{x} \<subseteq> {y}\<rbrakk> \<Longrightarrow> graph_map (insert (x,y) g) = (graph_map g)(x \<mapsto> y)"
  by (rule ext, auto simp add:graph_map_def)

lemma dom_map_graph: "dom f = Domain(map_graph f)"
  by (simp add: map_graph_def dom_def image_def)

lemma ran_map_graph: "ran f = Range(map_graph f)"
  by (simp add: map_graph_def ran_def image_def)

lemma graph_map_set: "functional (set xs) \<Longrightarrow> graph_map (set xs) = map_of xs"
  by (induct xs; force)

lemma rel_apply_map_graph:
  "x \<in> dom(f) \<Longrightarrow> (map_graph f)(x)\<^sub>r = the (f x)"
  by (auto simp add: rel_apply_def map_graph_def)

lemma ran_map_add_subset:
  "ran (x ++ y) \<subseteq> (ran x) \<union> (ran y)"
  by (auto simp add:ran_def)

lemma finite_dom_graph: "finite (dom f) \<Longrightarrow> finite (map_graph f)"
  by (metis dom_map_graph finite_imageD fst_eq_Domain functional_def map_graph_functional)

lemma finite_dom_ran [simp]: "finite (dom f) \<Longrightarrow> finite (ran f)"
  by (metis finite_Range finite_dom_graph ran_map_graph)

lemma functional_insert: "functional (insert a R) \<Longrightarrow> functional R"
  by (simp add: single_valued_def)

lemma Domain_insert: "Domain (insert a R) = insert (fst a) (Domain R)"
  by (simp add: Domain_fst)

lemma card_map_graph: "\<lbrakk> finite R; functional R \<rbrakk> \<Longrightarrow> card R = card (Domain R)"
  by (induct R rule: finite.induct, simp_all add: functional_insert card_insert_if Domain_insert finite_Domain)
     (metis DiffD1 Diff_insert_absorb DomainE Map_Extra.Domain_insert insertI1 insert_Diff prod.collapse single_valued_def)

lemma graph_map_inv [simp]: "functional g \<Longrightarrow> map_graph (graph_map g) = g"
  apply (simp add:map_graph_def graph_map_def functional_def, safe)
   apply (metis (lifting, no_types) image_iff option.distinct(1) option.inject someI surjective_pairing)
  apply (simp add:inj_on_def)
  apply safe
   apply (metis fst_conv snd_conv some_equality)
  apply (metis (lifting) fst_conv image_iff)
  done

lemma graph_map_dom: "dom (graph_map R) = fst ` R"
  by (simp add: graph_map_def dom_def)

lemma graph_map_countable_dom: "countable R \<Longrightarrow> countable (dom (graph_map R))"
  by (simp add: graph_map_dom)

lemma countable_ran:
  assumes "countable (dom f)"
  shows "countable (ran f)"
proof -
  have "countable (map_graph f)"
    by (simp add: assms)
  then have "countable (Range(map_graph f))"
    by (simp add: Range_snd)
  thus ?thesis
    by (simp add: ran_map_graph)
qed

lemma map_graph_inv' [simp]:
  "graph_map' (map_graph f) = Some f"
  by (simp add: graph_map'_def)

lemma map_graph_inj:
  "inj map_graph"
  by (metis injI map_graph_inv)

lemma map_eq_graph: "f = g \<longleftrightarrow> map_graph f = map_graph g"
  by (auto simp add: inj_eq map_graph_inj)

lemma map_le_graph: "f \<subseteq>\<^sub>m g \<longleftrightarrow> map_graph f \<subseteq> map_graph g"
  by (force simp add: map_le_def map_graph_def)

lemma map_graph_comp: "map_graph (g \<circ>\<^sub>m f) = (map_graph f) O (map_graph g)"
  by (metis graph_def graph_map_comp map_graph_def)

lemma rel_comp_map: "R O map_graph f = (\<lambda> p. (fst p, the (f (snd p)))) ` (R \<rhd>\<^sub>r dom(f))"
  by (force simp add: map_graph_def relcomp_unfold rel_ranres_def image_def dom_def)

lemma map_graph_update: "map_graph (f(k \<mapsto> v)) = insert (k, v) ((- {k}) \<lhd>\<^sub>r map_graph f)"
  by (simp add: map_graph_def rel_domres_def, safe, simp_all, metis option.sel)

subsection \<open> Map Application \<close>

definition map_apply :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>m" [999,0] 999) where
"map_apply = (\<lambda> f x. the (f x))"

subsection \<open> Map Membership \<close>

fun map_member :: "'a \<times> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool" (infix "\<in>\<^sub>m" 50) where
"(k, v) \<in>\<^sub>m m \<longleftrightarrow> m(k) = Some(v)"

lemma map_ext:
  "\<lbrakk> \<And> x y. (x, y) \<in>\<^sub>m A \<longleftrightarrow> (x, y) \<in>\<^sub>m B \<rbrakk> \<Longrightarrow> A = B"
  by (rule ext, simp_all, metis not_None_eq)

lemma map_member_alt_def:
  "(x, y) \<in>\<^sub>m A \<longleftrightarrow> (x \<in> dom A \<and> A(x)\<^sub>m = y)"
  by (auto simp add: map_apply_def)

lemma map_le_member:
  "f \<subseteq>\<^sub>m g \<longleftrightarrow> (\<forall> x y. (x,y) \<in>\<^sub>m f \<longrightarrow> (x,y) \<in>\<^sub>m g)"
  by (force simp add: map_le_def)

subsection \<open> Preimage \<close>

definition preimage :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set" where
"preimage f B = {x \<in> dom(f). the(f(x)) \<in> B}"

lemma preimage_range: "preimage f (ran f) = dom f"
  by (auto simp add: preimage_def ran_def)

lemma dom_preimage: "dom (m \<circ>\<^sub>m f) = preimage f (dom m)"
  apply (simp add: dom_def preimage_def, safe, simp_all)
   apply (meson map_comp_Some_iff)
  apply (metis map_comp_def option.case_eq_if option.distinct(1))
  done



lemma countable_preimage:
  assumes "countable A" "inj_on f (preimage f A)"
  shows "countable (preimage f A)"
proof -
  obtain g :: "'a \<Rightarrow> nat" where g: "inj_on g A"
    using assms(1) by blast
  have "inj_on (g \<circ> the \<circ> f) (preimage f A)"
  proof (rule inj_onI)
    fix x y
    assume "x \<in> preimage f A" "y \<in> preimage f A" "(g \<circ> the \<circ> f) x = (g \<circ> the \<circ> f) y"
    with assms g show "x = y"
      unfolding preimage_def by (metis (lifting) comp_apply domIff inj_onD mem_Collect_eq option.expand)
  qed
  thus ?thesis
    by (simp add: countableI)
qed

subsection \<open> Minus operation for maps \<close>

definition map_minus :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixl "--" 100)
where "map_minus f g = (\<lambda> x. if (f x = g x) then None else f x)"

lemma map_minus_apply [simp]: "y \<in> dom(f -- g) \<Longrightarrow> (f -- g)(y)\<^sub>m = f(y)\<^sub>m"
  by (auto simp add: map_minus_def dom_def map_apply_def)

lemma map_member_plus:
  "(x, y) \<in>\<^sub>m f ++ g \<longleftrightarrow> ((x \<notin> dom(g) \<and> (x, y) \<in>\<^sub>m f) \<or> (x, y) \<in>\<^sub>m g)"
  by (auto simp add: map_add_Some_iff)

lemma map_member_minus:
  "(x, y) \<in>\<^sub>m f -- g \<longleftrightarrow> (x, y) \<in>\<^sub>m f \<and> (\<not> (x, y) \<in>\<^sub>m g)"
  by (auto simp add: map_minus_def)

lemma map_minus_plus_commute:
  "dom(g) \<inter> dom(h) = {} \<Longrightarrow> (f -- g) ++ h = (f ++ h) -- g"
  apply (rule map_ext)
  apply (simp add: map_member_plus map_member_minus del: map_member.simps)
  apply (auto simp add: map_member_alt_def)
  done

lemma map_graph_minus: "map_graph (f -- g) = map_graph f - map_graph g"
  by (simp add: map_minus_def map_graph_def, safe, simp_all, (meson option.distinct(1))+)

lemma map_minus_common_subset:
  "\<lbrakk> h \<subseteq>\<^sub>m f; h \<subseteq>\<^sub>m g \<rbrakk> \<Longrightarrow> (f -- h = g -- h) = (f = g)"
  by (auto simp add: map_eq_graph map_graph_minus map_le_graph)

subsection \<open> Map Bind \<close>

text \<open> Create some extra intro/elim rules to help dealing with proof about option bind. \<close>

lemma option_bindSomeE [elim!]:
  "\<lbrakk> X >>= F = Some(v); \<And> x. \<lbrakk> X = Some(x); F(x) = Some(v) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases X, auto)

lemma option_bindSomeI [intro]:
  "\<lbrakk> X = Some(x); F(x) = Some(y) \<rbrakk> \<Longrightarrow> X >>= F = Some(y)"
  by (simp)

lemma ifSomeE [elim]: "\<lbrakk> (if c then Some(x) else None) = Some(y); \<lbrakk> c; x = y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases c, auto)

subsection \<open> Range Restriction \<close>

text \<open> A range restriction operator; only domain restriction is provided in HOL. \<close>

definition ran_restrict_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a \<rightharpoonup> 'b" ("_\<upharpoonleft>\<^bsub>_\<^esub>" [111,110] 110) where
"ran_restrict_map f B = (\<lambda>x. do { v <- f(x); if (v \<in> B) then Some(v) else None })"

lemma ran_restrict_alt_def: "f\<upharpoonleft>\<^bsub>B\<^esub> = (\<lambda> x. if x \<in> dom(f) \<and> the(f(x)) \<in> B then f x else None)"
  by (auto simp add: ran_restrict_map_def fun_eq_iff bind_eq_None_conv)

lemma ran_restrict_empty [simp]: "f\<upharpoonleft>\<^bsub>{}\<^esub> = Map.empty"
  by (simp add:ran_restrict_map_def)

lemma ran_restrict_ran [simp]: "f\<upharpoonleft>\<^bsub>ran(f) \<^esub> = f"
proof
  fix x
  show "(f\<upharpoonleft>\<^bsub>ran(f)\<^esub>) x = f x"
  proof (cases "f(x)")
    case None
    then show ?thesis by (simp add: ran_restrict_map_def ran_def)
  next
    case (Some a)
    then show ?thesis by (auto simp add: ran_restrict_map_def ran_def)
  qed
qed

lemma ran_ran_restrict [simp]: "ran(f\<upharpoonleft>\<^bsub>B\<^esub>) = ran(f) \<inter> B"
  by (force simp add:ran_restrict_map_def ran_def)

lemma dom_ran_restrict: "dom(f\<upharpoonleft>\<^bsub>B\<^esub>) \<subseteq> dom(f)"
  by (auto simp add:ran_restrict_map_def dom_def)

lemma ran_restrict_finite_dom [intro]:
  "finite(dom(f)) \<Longrightarrow> finite(dom(f\<upharpoonleft>\<^bsub>B\<^esub>))"
  by (metis finite_subset dom_ran_restrict)

lemma dom_Some [simp]: "dom (Some \<circ> f) = UNIV"
  by (auto)

lemma map_dres_rres_commute: "f\<upharpoonleft>\<^bsub>B\<^esub> |` A = (f |` A)\<upharpoonleft>\<^bsub>B\<^esub>"
  by (auto simp add: restrict_map_def ran_restrict_map_def)

lemma ran_restrict_map_twice [simp]: "(f\<upharpoonleft>\<^bsub>A\<^esub>)\<upharpoonleft>\<^bsub>B\<^esub> = f\<upharpoonleft>\<^bsub>(A \<inter> B)\<^esub>"
proof 
  fix x
  show "((f\<upharpoonleft>\<^bsub>A\<^esub>)\<upharpoonleft>\<^bsub>B\<^esub>) x = (f\<upharpoonleft>\<^bsub>(A \<inter> B)\<^esub>) x"
  proof (cases "f x")
    case None
    then show ?thesis by (simp add: ran_restrict_map_def)
  next
    case (Some a)
    then show ?thesis by (simp add: ran_restrict_map_def fun_eq_iff option.case_eq_if)
  qed
qed

lemma dom_left_map_add [simp]: "x \<in> dom g \<Longrightarrow> (f ++ g) x = g x"
  by (auto simp add:map_add_def dom_def)

lemma dom_right_map_add [simp]: "\<lbrakk> x \<notin> dom g; x \<in> dom f \<rbrakk> \<Longrightarrow> (f ++ g) x = f x"
  by (auto simp add:map_add_def dom_def)

lemma map_add_restrict:
  "f ++ g = (f |` (- dom g)) ++ g"
  by (rule ext, auto simp add: map_add_def restrict_map_def)

subsection \<open> Map Inverse and Identity \<close>

definition map_inv :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'a)" where
"map_inv f \<equiv> \<lambda> y. if (y \<in> ran f) then Some (SOME x. f x = Some y) else None"

definition map_id_on :: "'a set \<Rightarrow> ('a \<rightharpoonup> 'a)" where
"map_id_on xs \<equiv> \<lambda> x. if (x \<in> xs) then Some x else None"

lemma map_id_on_in [simp]:
  "x \<in> xs \<Longrightarrow> map_id_on xs x = Some x"
  by (simp add:map_id_on_def)

lemma map_id_on_out [simp]:
  "x \<notin> xs \<Longrightarrow> map_id_on xs x = None"
  by (simp add:map_id_on_def)

lemma map_id_dom [simp]: "dom (map_id_on xs) = xs"
  by (simp add:dom_def map_id_on_def)

lemma map_id_ran [simp]: "ran (map_id_on xs) = xs"
  by (force simp add:ran_def map_id_on_def)

lemma map_id_on_UNIV[simp]: "map_id_on UNIV = Some"
  by (simp add:map_id_on_def)

lemma map_id_on_inj [simp]:
  "inj_on (map_id_on xs) xs"
  by (simp add:inj_on_def)

lemma restrict_map_inj_on:
  "inj_on f (dom f) \<Longrightarrow> inj_on (f |` A) (dom f \<inter> A)"
  by (auto simp add:inj_on_def)

lemma map_inv_empty [simp]: "map_inv Map.empty = Map.empty"
  by (simp add:map_inv_def)

lemma map_inv_id [simp]:
  "map_inv (map_id_on xs) = map_id_on xs"
  by (force simp add:map_inv_def map_id_on_def ran_def)

lemma map_inv_Some [simp]: "map_inv Some = Some"
  by (simp add:map_inv_def ran_def)

lemma map_inv_f_f [simp]:
  "\<lbrakk> inj_on f (dom f); f x = Some y \<rbrakk> \<Longrightarrow> map_inv f y = Some x"
  apply (simp add: map_inv_def, safe)
   apply (rule some_equality)
    apply (auto simp add:inj_on_def dom_def ran_def)
  done

lemma dom_map_inv [simp]:
  "dom (map_inv f) = ran f"
  by (auto simp add:map_inv_def)

lemma ran_map_inv [simp]:
  "inj_on f (dom f) \<Longrightarrow> ran (map_inv f) = dom f"
  apply (simp add:map_inv_def ran_def, safe)
   apply (metis (mono_tags, lifting) verit_sko_ex')
  apply (metis (mono_tags, lifting) domI domIff map_inv_def map_inv_f_f option.inject)
  done

lemma dom_image_ran: "f ` dom f = Some ` ran f"
  by (auto simp add:dom_def ran_def image_def)

lemma inj_map_inv [intro]:
  "inj_on f (dom f) \<Longrightarrow> inj_on (map_inv f) (ran f)"
  apply (simp add:map_inv_def inj_on_def dom_def ran_def, safe)
  apply (metis (mono_tags, lifting) option.sel someI_ex)
  done

lemma inj_map_bij: "inj_on f (dom f) \<Longrightarrow> bij_betw f (dom f) (Some ` ran f)"
  by (auto simp add:inj_on_def dom_def ran_def image_def bij_betw_def)

lemma map_inv_map_inv [simp]:
  assumes "inj_on f (dom f)"
  shows "map_inv (map_inv f) = f"
proof -

  from assms have "inj_on (map_inv f) (ran f)"
    by auto

  thus ?thesis
    by (metis (no_types, lifting) ext assms domIff dom_map_inv map_inv_f_f option.collapse
        ran_map_inv)
qed

lemma map_self_adjoin_complete [intro]:
  assumes "dom f \<inter> ran f = {}" "inj_on f (dom f)"
  shows "inj_on (map_inv f ++ f) (dom f \<union> ran f)"
proof (rule inj_onI)
  fix x y
  assume x:"x \<in> dom f \<union> ran f" and y:"y \<in> dom f \<union> ran f" 
     and f:"(map_inv f ++ f) x = (map_inv f ++ f) y"

  show "x = y"
  proof (cases "x \<in> dom f")
    case True
    then show ?thesis
      by (metis assms(1,2) disjoint_iff_not_equal domD dom_left_map_add f inj_on_def
          map_add_dom_app_simps(3) ranI ran_map_inv) 
  next
    case False
    then show ?thesis
      by (metis (full_types) UnE assms(1,2) disjoint_iff domIff dom_left_map_add dom_map_inv
          f inj_map_inv inj_on_def map_add_dom_app_simps(3) ran_map_inv ran_restrict_alt_def
          ran_restrict_ran x) 
  qed
qed

lemma inj_completed_map [intro]:
  assumes "dom f = ran f" "inj_on f (dom f)"
  shows "inj (Some ++ f)"
proof (rule injI)
  fix x y
  assume f:"(Some ++ f) x = (Some ++ f) y"
  have bb: "bij_betw f (dom f) (Some ` ran f)"
    using assms(2) inj_map_bij by blast
  thus "x = y"
  proof (cases "x \<in> dom f")
    case True
    then show ?thesis
      by (metis assms(1,2) f inj_on_contraD map_add_dom_app_simps(1,3) ranI) 
  next
    case False
    then show ?thesis
      by (metis assms(1) dom_left_map_add f map_add_dom_app_simps(3) option.inject
          ranI) 
  qed
qed

lemma bij_completed_map [intro]:
  fixes f :: "'a \<rightharpoonup> 'a"
  assumes "dom f = ran f" "inj_on f (dom f)"
  shows "bij_betw (Some ++ f) UNIV (range Some)"
proof -
  have "range (Some ++ f) = range Some"
  proof (rule set_eqI, rule iffI)
    fix x
    assume "x \<in> range (Some ++ f)"
    thus "x \<in> range Some"
      using image_iff by fastforce
  next
    fix x :: "'a option"
    assume "x \<in> range Some"
    thus "x \<in> range (Some ++ f)"
      by (metis assms(1) dom_image_ran[of f] image_iff[of x f "dom f"] image_iff[of "Some _" Some "dom f"] image_iff[of x Some UNIV]
          map_add_dom_app_simps(1)[of _ f Some] map_add_dom_app_simps(3)[of _ f Some] rangeI[of "Some ++ f"])
  qed
  thus ?thesis
    by (metis assms(1,2) inj_completed_map inj_on_imp_bij_betw)
qed


lemma bij_map_Some:
  "bij_betw f a (Some ` b) \<Longrightarrow> bij_betw (the \<circ> f) a b"
  apply (simp add:bij_betw_def)
  apply (safe)
    apply (metis (opaque_lifting, no_types) comp_inj_on_iff f_the_inv_into_f inj_on_inverseI option.sel)
   apply (metis (opaque_lifting, no_types) image_iff option.sel)
  apply (metis Option.these_def Some_image_these_eq image_image these_image_Some_eq)
  done

lemma ran_map_add [simp]:
  "m`(dom m \<inter> dom n) = n`(dom m \<inter> dom n) \<Longrightarrow>
   ran(m++n) = ran n \<union> ran m"
  apply (simp add:ran_def, safe, simp_all)
   apply (metis)
  apply (metis domI map_add_dom_app_simps(1))
  apply (metis (no_types, opaque_lifting) IntI domI dom_left_map_add image_iff map_add_dom_app_simps(3))
  done

lemma ran_maplets [simp]:
  "\<lbrakk> length xs = length ys; distinct xs \<rbrakk> \<Longrightarrow> ran [xs [\<mapsto>] ys] = set ys"
    by (induct rule:list_induct2, simp_all)

lemma inj_map_add:
  "\<lbrakk> inj_on f (dom f); inj_on g (dom g); ran f \<inter> ran g = {} \<rbrakk> \<Longrightarrow>
   inj_on (f ++ g) (dom f \<union> dom g)"
  apply (simp add:inj_on_def, safe, simp_all)
     apply (metis (full_types) disjoint_iff_not_equal domI dom_left_map_add map_add_dom_app_simps(3) ranI)
    apply (metis disjoint_iff_not_equal domI map_add_SomeD ranI)
   apply (metis disjoint_iff_not_equal domIff map_add_Some_iff ranI)
  apply (metis domI)
  done

lemma map_inv_add':
  assumes "inj_on f (dom f)" "inj_on g (dom g)"
          "dom f \<inter> dom g = {}" "ran f \<inter> ran g = {}"
 shows "map_inv (f ++ g) = map_inv f ++ map_inv g"
proof (rule ext)

  from assms have minj: "inj_on (f ++ g) (dom (f ++ g))"
    by (simp, metis inj_map_add sup_commute)

  fix x
  have "x \<in> ran g \<Longrightarrow> map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
  proof -
    assume ran:"x \<in> ran g"
    then obtain y where dom:"g y = Some x" "y \<in> dom g"
      by (auto simp add:ran_def)

    hence "(f ++ g) y = Some x"
      by simp

    with assms minj ran dom show "map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
      by simp
  qed

  moreover have "\<lbrakk> x \<notin> ran g; x \<in> ran f \<rbrakk> \<Longrightarrow> map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
  proof -
    assume ran:"x \<notin> ran g" "x \<in> ran f"
    with assms obtain y where dom:"f y = Some x" "y \<in> dom f" "y \<notin> dom g"
      by (auto simp add:ran_def)

    with ran have "(f ++ g) y = Some x"
      by (simp)

    with assms minj ran dom show "map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
      by simp
  qed

  moreover from assms minj have "\<lbrakk> x \<notin> ran g; x \<notin> ran f \<rbrakk> \<Longrightarrow> map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
    apply (simp add:map_inv_def ran_def map_add_def)
    apply (metis dom_left_map_add map_add_def map_add_dom_app_simps(3))
    done

  ultimately show "map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
    by blast
qed

lemma map_inv_dom_res:
  assumes "inj_on f (dom f)"
  shows "map_inv (f |` A) = (map_inv f) \<upharpoonleft>\<^bsub>A\<^esub>"
  using assms
  apply (simp add: map_inv_def restrict_map_def ran_restrict_map_def dom_def ran_def fun_eq_iff inj_on_def)
  apply (safe intro!: some_equality)
     apply (metis (mono_tags, lifting) someI_ex)+
  done

lemma map_inv_ran_res:
  assumes "inj_on f (dom f)"
  shows "map_inv (f \<upharpoonleft>\<^bsub>A\<^esub>) = (map_inv f) |` A"
  using assms someI_ex by (force intro!: some_equality simp add: map_inv_def restrict_map_def ran_restrict_map_def dom_def ran_def fun_eq_iff inj_on_def)

lemma map_update_as_add: "f(x \<mapsto> y) = f ++ [x \<mapsto> y]"
  by (auto simp add: map_add_def)

lemma map_add_lookup [simp]:
  "x \<notin> dom f \<Longrightarrow> ([x \<mapsto> y] ++ f) x = Some y"
  by (simp add:map_add_def dom_def)

lemma map_add_Some: "Some ++ f = map_id_on (- dom f) ++ f"
proof 
  fix x
  show "(Some ++ f) x = (map_id_on (- dom f) ++ f) x"
  proof (cases "x \<in> dom f")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis by simp
  qed
qed

lemma distinct_map_dom:
  "x \<notin> set xs \<Longrightarrow> x \<notin> dom [xs [\<mapsto>] ys]"
  by (simp add:dom_def)

lemma distinct_map_ran:
  "\<lbrakk> distinct xs; y \<notin> set ys; length xs = length ys \<rbrakk> \<Longrightarrow>
   y \<notin> ran ([xs [\<mapsto>] ys])"
  apply (simp add:map_upds_def)
  apply (subgoal_tac "distinct (map fst (rev (zip xs ys)))")
  apply (simp add:ran_distinct)
  apply (metis (opaque_lifting, no_types) image_iff set_zip_rightD surjective_pairing)
  apply (simp add:zip_rev[THEN sym])
done

lemma maplets_lookup [dest]:
  "\<lbrakk> length xs = length ys; distinct xs; \<forall> y. [xs [\<mapsto>] ys] x = Some y \<rbrakk> \<Longrightarrow> y \<in> set ys"
  using ranI by fastforce
  
lemma maplets_distinct_inj [intro]:
  "\<lbrakk> length xs = length ys; distinct xs; distinct ys; set xs \<inter> set ys = {} \<rbrakk> \<Longrightarrow>
   inj_on [xs [\<mapsto>] ys] (set xs)"
  apply (induct rule:list_induct2)
   apply (simp_all)
  apply (rule conjI)
   apply (rule inj_onI)
  apply (metis fun_upd_def inj_on_contraD)
  apply (metis image_iff ranI ran_maplets)
  done

lemma map_inv_maplet[simp]: "map_inv [x \<mapsto> y] = [y \<mapsto> x]"
  by (auto simp add:map_inv_def)

lemma map_inv_add:
  assumes "inj_on f (dom f)" "inj_on g (dom g)"
          "ran f \<inter> ran g = {}"
  shows "map_inv (f ++ g) = map_inv f\<upharpoonleft>\<^bsub>(- dom g)\<^esub> ++ map_inv g"
proof -
  have "map_inv (f ++ g) = map_inv (f |` (- dom(g))  ++ g)"
    by (metis map_add_restrict)
  also have "... = map_inv (f |` (- dom g)) ++ map_inv g"
    by (rule map_inv_add', simp_all add: assms restrict_map_inj_on)
       (metis assms(3) disjoint_iff ranI ran_restrictD)
  also have "... = map_inv f\<upharpoonleft>\<^bsub>(- dom g)\<^esub> ++ map_inv g"
    by (simp add: map_inv_dom_res assms) 
  finally show ?thesis .
qed

lemma map_inv_upd:
  assumes "inj_on f (dom f)" "inj_on g (dom g)" "v \<notin> ran f"
  shows "map_inv (f(k \<mapsto> v)) = (map_inv (f |` (- {k})))(v \<mapsto> k)"
proof -
  have "map_inv (f(k \<mapsto> v)) = map_inv (f ++ [k \<mapsto> v])"
    by (auto)
  also have "... = map_inv f\<upharpoonleft>\<^bsub>(- dom [k \<mapsto> v])\<^esub> ++ map_inv [k \<mapsto> v]"
    by (rule map_inv_add, simp_all add: assms)
  also have "... = (map_inv f\<upharpoonleft>\<^bsub>(- {k})\<^esub>)(v \<mapsto> k)"
    by (simp)
  also have "... = (map_inv (f |` (- {k})))(v \<mapsto> k)"
    by (simp add: assms(1) map_inv_dom_res)
  finally show ?thesis .
qed
  
lemma map_inv_maplets [simp]:
  "\<lbrakk> length xs = length ys; distinct xs; distinct ys; set xs \<inter> set ys = {} \<rbrakk> \<Longrightarrow>
  map_inv [xs [\<mapsto>] ys] = [ys [\<mapsto>] xs]"
proof (induct rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  have "map_inv ([xs [\<mapsto>] ys] ++ [x \<mapsto> y]) = map_inv [xs [\<mapsto>] ys] ++ map_inv [x \<mapsto> y]"
  proof (rule map_inv_add')
    from Cons show "inj_on [xs [\<mapsto>] ys] (dom [xs [\<mapsto>] ys])" by auto
    from Cons show "inj_on [x \<mapsto> y] (dom [x \<mapsto> y])" by auto
    from Cons show "dom [xs [\<mapsto>] ys] \<inter> dom [x \<mapsto> y] = {}" by auto
    from Cons show "ran [xs [\<mapsto>] ys] \<inter> ran [x \<mapsto> y] = {}" by auto
  qed
  with Cons show ?case
    by (metis disjoint_iff distinct.simps(2) list.set_intros(2) map_inv_maplet map_update_as_add map_upds_Cons map_upds_twist)
qed

lemma maplets_lookup_nth [simp]:
  "\<lbrakk> length xs = length ys; distinct xs; i < length ys \<rbrakk> \<Longrightarrow>
   [xs [\<mapsto>] ys] (xs ! i) = Some (ys ! i)"
  apply (induct arbitrary: i rule:list_induct2)
  apply simp
  using less_Suc_eq_0_disj apply auto
  done

theorem inv_map_inv:
  assumes "inj_on f (dom f)" "ran f = dom f"
  shows "inv (the \<circ> (Some ++ f)) = the \<circ> map_inv (Some ++ f)"
proof
  fix x
  show "(inv (the \<circ> (Some ++ f))) x = (the \<circ> map_inv (Some ++ f)) x"
  proof (cases "x \<in> ran f")
    case True
    then obtain y where y:"f y = Some x"
      by (metis dom_image_ran image_iff)
    with assms show ?thesis 
      apply (simp add:map_add_Some map_inv_add' inv_def)
      apply (rule some_equality)
      apply simp
      apply (metis (full_types) Compl_iff domIff inj_on_def map_add_Some map_add_dom_app_simps(2,3) map_id_dom option.exhaust_sel ranI)
      done
  next
    case False
    then show ?thesis 
      apply (simp add:map_add_Some map_inv_add' inv_def)
      apply (rule some_equality)
      apply (simp add: assms(1,2) map_inv_add')
      apply (metis (no_types, opaque_lifting) Un_UNIV_right assms(1,2) dom_map_add inj_completed_map map_add_None map_add_Some map_id_dom map_id_on_UNIV map_inv_f_f option.exhaust_sel
          option.sel)
      done
  qed
qed

lemma map_comp_dom: "dom (g \<circ>\<^sub>m f) \<subseteq> dom f"
  by (metis (lifting, full_types) Collect_mono dom_def map_comp_simps(1))

lemma map_comp_assoc: "f \<circ>\<^sub>m (g \<circ>\<^sub>m h) = f \<circ>\<^sub>m g \<circ>\<^sub>m h"
proof
  fix x
  show "(f \<circ>\<^sub>m (g \<circ>\<^sub>m h)) x = (f \<circ>\<^sub>m g \<circ>\<^sub>m h) x"
  proof (cases "h x")
    case None thus ?thesis
      by (auto simp add: map_comp_def)
  next
    case (Some y) thus ?thesis
      by (auto simp add: map_comp_def)
  qed
qed

lemma map_comp_runit [simp]: "f \<circ>\<^sub>m Some = f"
  by (simp add: map_comp_def)

lemma map_comp_lunit [simp]: "Some \<circ>\<^sub>m f = f"
proof
  fix x
  show "(Some \<circ>\<^sub>m f) x = f x"
  proof (cases "f x")
    case None thus ?thesis
      by (simp add: map_comp_def)
  next
    case (Some y) thus ?thesis
      by (simp add: map_comp_def)
  qed
qed

lemma map_comp_apply [simp]: "(f \<circ>\<^sub>m g) x = g(x) >>= f"
  by (auto simp add: map_comp_def option.case_eq_if)

lemma map_graph_map_inv: "inj_on f (dom f) \<Longrightarrow> map_graph (map_inv f) = (map_graph f)\<inverse>"
  by (simp add: map_graph_def, safe, simp_all, metis dom_map_inv inj_map_inv map_inv_f_f map_inv_map_inv)

subsection \<open> Merging of compatible maps \<close>

definition comp_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool" (infixl "\<parallel>\<^sub>m" 60) where
"comp_map f g = (\<forall> x \<in> dom(f) \<inter> dom(g). the(f(x)) = the(g(x)))"

lemma comp_map_unit: "Map.empty \<parallel>\<^sub>m f"
  by (simp add: comp_map_def)

lemma comp_map_refl: "f \<parallel>\<^sub>m f"
  by (simp add: comp_map_def)

lemma comp_map_sym: "f \<parallel>\<^sub>m g \<Longrightarrow> g \<parallel>\<^sub>m f"
  by (simp add: comp_map_def)

definition merge :: "('a \<rightharpoonup> 'b) set \<Rightarrow> 'a \<rightharpoonup> 'b" where
"merge fs =
  (\<lambda> x. if (\<exists> f \<in> fs. x \<in> dom(f)) then (THE y. \<forall> f \<in> fs. x \<in> dom(f) \<longrightarrow> f(x) = y) else None)"

lemma merge_empty: "merge {} = Map.empty"
  by (simp add: merge_def)

lemma merge_singleton: "merge {f} = f"
  unfolding merge_def
  by (auto simp add: fun_eq_iff domIff)

subsection \<open> Conversion between lists and maps \<close>

definition map_of_list :: "'a list \<Rightarrow> (nat \<rightharpoonup> 'a)" where
"map_of_list xs = (\<lambda> i. if (i < length xs) then Some (xs!i) else None)"

lemma map_of_list_nil [simp]: "map_of_list [] = Map.empty"
  by (simp add: map_of_list_def)

lemma dom_map_of_list [simp]: "dom (map_of_list xs) = {0..<length xs}"
  by (auto simp add: map_of_list_def dom_def)

lemma ran_map_of_list [simp]: "ran (map_of_list xs) = set xs"
  apply (simp add: ran_def map_of_list_def)
  apply (safe)
   apply (force)
  apply (meson in_set_conv_nth)
  done

definition list_of_map :: "(nat \<rightharpoonup> 'a) \<Rightarrow> 'a list" where
"list_of_map f = (if (f = Map.empty) then [] else map (the \<circ> f) [0 ..< Suc(GREATEST x. x \<in> dom f)])"

lemma list_of_map_empty [simp]: "list_of_map Map.empty = []"
  by (simp add: list_of_map_def)

definition list_of_map' :: "(nat \<rightharpoonup> 'a) \<rightharpoonup> 'a list" where
"list_of_map' f = (if (\<exists> n. dom f = {0..<n}) then Some (list_of_map f) else None)"

lemma map_of_list_inv [simp]: "list_of_map (map_of_list xs) = xs"
proof (cases "xs = []")
  case True thus ?thesis by (simp)
next
  case False
  moreover hence "(GREATEST x. x \<in> dom (map_of_list xs)) = length xs - 1"
    by (auto intro: Greatest_equality)
  moreover from False have "map_of_list xs \<noteq> Map.empty"
    by (metis ran_empty ran_map_of_list set_empty)
  ultimately show ?thesis
    by (auto intro!:nth_equalityI simp add: list_of_map_def map_of_list_def  fun_eq_iff)
qed

subsection \<open> Map Comprehension \<close>

text \<open> Map comprehension simply converts a relation built through set comprehension into a map. \<close>

syntax
  "_Mapcompr" :: "'a \<Rightarrow> 'b \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a \<rightharpoonup> 'b"    ("(1[_ \<mapsto> _ |/_./ _])")

translations
  "_Mapcompr F G xs P" == "CONST graph_map {(F, G) | xs. P}"

lemma map_compr_eta:
  "[x \<mapsto> y | x y. (x, y) \<in>\<^sub>m f] = f"
  apply (rule ext)
  apply (simp add: graph_map_def, safe, simp_all)
  apply (metis (mono_tags, lifting) Domain.DomainI fst_eq_Domain mem_Collect_eq old.prod.case option.distinct(1) option.expand option.sel)
  done

lemma map_compr_simple:
  "[x \<mapsto> F x y | x y. (x, y) \<in>\<^sub>m f] = (\<lambda> x. do { y \<leftarrow> f(x); Some(F x y) })"
  apply (rule ext)
  apply (auto simp add: graph_map_def image_Collect)
  done

lemma map_compr_dom_simple [simp]:
  "dom [x \<mapsto> f x | x. P x] = {x. P x}"
  by (force simp add: graph_map_dom image_Collect)

lemma map_compr_ran_simple [simp]:
  "ran [x \<mapsto> f x | x. P x] = {f x | x. P x}"
  apply (simp add: graph_map_def ran_def, safe, simp_all)
  apply blast
  apply (metis (mono_tags, lifting) fst_eqD image_eqI mem_Collect_eq someI)
  done

lemma map_compr_eval_simple [simp]:
  "[x \<mapsto> f x | x. P x] x = (if (P x) then Some (f x) else None)"
  by (auto simp add: graph_map_def image_Collect)

subsection \<open> Sorted lists from maps \<close>

definition sorted_list_of_map :: "('a::linorder \<rightharpoonup> 'b) \<Rightarrow> ('a \<times> 'b) list" where
"sorted_list_of_map f = map (\<lambda> k. (k, the (f k))) (sorted_list_of_set(dom(f)))"

lemma sorted_list_of_map_empty [simp]:
  "sorted_list_of_map Map.empty = []"
  by (simp add: sorted_list_of_map_def)

lemma sorted_list_of_map_inv:
  assumes "finite(dom(f))"
  shows "map_of (sorted_list_of_map f) = f"
proof -
  obtain A where "finite A" "A = dom(f)"
    by (simp add: assms)
  thus ?thesis
  proof (induct A rule: finite_induct)
    case empty thus ?thesis
      by (simp add: sorted_list_of_map_def, metis dom_empty empty_iff map_le_antisym map_le_def)
  next
    case (insert x A) thus ?thesis
      by (simp add: assms sorted_list_of_map_def map_of_map_keys)
  qed
qed

declare map_member.simps [simp del]

subsection \<open> Extra map lemmas \<close>

lemma map_eqI:
  "\<lbrakk> dom f = dom g; \<forall> x\<in>dom(f). the(f x) = the(g x) \<rbrakk> \<Longrightarrow> f = g"
  by (metis domIff map_le_antisym map_le_def option.expand)

lemma map_restrict_dom [simp]: "f |` dom f = f"
  by (simp add: map_eqI)

lemma map_restrict_dom_compl: "f |` (- dom f) = Map.empty"
  by (metis dom_eq_empty_conv dom_restrict inf_compl_bot)

lemma restrict_map_neg_disj:
  "dom(f) \<inter> A = {} \<Longrightarrow> f |` (- A) = f"
  by (simp add: restrict_map_def, rule ext, metis IntI domIff empty_iff)

lemma map_plus_restrict_dist: "(f ++ g) |` A = (f |` A) ++ (g |` A)"
  by (auto simp add: restrict_map_def map_add_def)

lemma map_plus_eq_left:
  assumes "f ++ h = g ++ h"
  shows "(f |` (- dom h)) = (g |` (- dom h))"
proof -
  have "h |` (- dom h) = Map.empty"
    by (metis Compl_disjoint dom_eq_empty_conv dom_restrict)
  then have f2: "f |` (- dom h) = (f ++ h) |` (- dom h)"
    by (simp add: map_plus_restrict_dist)
  have "h |` (- dom h) = Map.empty"
    by (metis (no_types) Compl_disjoint dom_eq_empty_conv dom_restrict)
  then show ?thesis
    using f2 assms by (simp add: map_plus_restrict_dist)
qed

lemma map_add_split:
  "dom(f) = A \<union> B \<Longrightarrow> (f |` A) ++ (f |` B) = f"
  by (rule ext, auto simp add: map_add_def restrict_map_def option.case_eq_if)

lemma map_le_via_restrict:
  "f \<subseteq>\<^sub>m g \<longleftrightarrow> g |` dom(f) = f"
  by (auto simp add: map_le_def restrict_map_def dom_def fun_eq_iff)

lemma map_add_cancel:
  "f \<subseteq>\<^sub>m g \<Longrightarrow> f ++ (g -- f) = g"
  by (simp add: map_le_def map_add_def map_minus_def fun_eq_iff option.case_eq_if)
     (metis domIff)

lemma map_le_iff_add: "f \<subseteq>\<^sub>m g \<longleftrightarrow> (\<exists> h. dom(f) \<inter> dom(h) = {} \<and> f ++ h = g)"
proof 
  assume "f \<subseteq>\<^sub>m g" 
  hence "dom f \<inter> dom (g -- f) = {} \<and> f ++ (g -- f) = g"
    by (metis (no_types, lifting) Int_emptyI domIff map_add_cancel map_le_def map_minus_def)
  thus "\<exists>h. dom f \<inter> dom h = {} \<and> f ++ h = g" by blast
next
  assume "\<exists>h. dom f \<inter> dom h = {} \<and> f ++ h = g"
  thus "f \<subseteq>\<^sub>m g"
    by (auto simp add: map_add_comm)
qed

lemma map_add_comm_weak: "(\<forall> k \<in> dom m1 \<inter> dom m2. m1(k) = m2(k)) \<Longrightarrow> m1 ++ m2 = m2 ++ m1"
  by (simp add: map_add_def option.case_eq_if fun_eq_iff)
     (metis IntI domI)

lemma map_add_comm_weak': "Q |` dom P = P |` dom Q \<Longrightarrow> P ++ Q = Q ++ P"
  by (metis IntD1 IntD2 map_add_comm_weak restrict_in)

lemma map_compat_add: "Q |` dom P = P |` dom Q \<Longrightarrow> R |` (dom Q \<union> dom P) = (P ++ Q) |` dom R \<Longrightarrow> R |` dom P = P |` dom R"
  by (metis Int_commute Map.restrict_restrict Un_Int_eq(2) map_add_comm_weak' map_le_iff_map_add_commute map_le_via_restrict)

abbreviation "rel_map R \<equiv> rel_fun (=) (rel_option R)"

lemma rel_map_iff: 
  "rel_map R f g \<longleftrightarrow> (dom(f) = dom(g) \<and> (\<forall> x\<in>dom(f). R (the (f x)) (the (g x))))"
  apply (simp add: rel_fun_def, safe)
  apply (metis not_None_eq option.rel_distinct(2))
  apply (metis not_None_eq option.rel_distinct(1))
  apply (metis option.rel_sel option.sel option.simps(3))
  apply (metis domIff option.rel_sel)
  done

end