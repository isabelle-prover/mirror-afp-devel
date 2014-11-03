section {* Finite partial functions *}

theory Finite_Map imports
  Main
  "~~/src/HOL/Library/FSet"
begin

text {* The type of finite partial functions is obtained by restricting the 
  type of partial functions to those with a finite domain. We use the
  lifting package to transfer several theories from the Map library to our
  finite setting. *}  

typedef ('k, 'v) fmap (infix "\<rightharpoonup>\<^sub>f" 9) = "{f :: 'k \<rightharpoonup> 'v. finite (dom f)}"
by (intro exI[of _ "empty"], simp)

setup_lifting type_definition_fmap

subsection {* Union *}

lift_definition 
  fmap_add :: "('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v)"
is "map_add"
by (unfold dom_map_add, auto)

abbreviation
  FMAP_ADD :: "('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v)" (infixl "\<oplus>" 100) 
where
  "xs \<oplus> ys \<equiv> fmap_add xs ys"

lemma fmap_add_assoc:
  "A \<oplus> (B \<oplus> C) = (A \<oplus> B) \<oplus> C"
by (transfer, auto)

subsection {* Difference *}

definition
  map_diff :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k fset \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "map_diff f ks = restrict_map f (- fset ks)"

lift_definition
  fmap_diff :: "('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> 'k fset \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v)"
is "map_diff"
by (auto simp add: map_diff_def)

abbreviation 
  FMAP_DIFF :: "('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> 'k fset \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v)" (infix "\<ominus>" 110) 
where 
  "xs \<ominus> ys \<equiv> fmap_diff xs ys"

subsection {* Comprehension *}

definition 
  make_map :: "'k fset \<Rightarrow> 'v \<Rightarrow> ('k \<rightharpoonup> 'v)"
where 
  "make_map ks v \<equiv> \<lambda>k. if k \<in> fset ks then Some v else None"

lemma dom_make_map: 
  "dom (make_map ks v) = fset ks"
by (metis domIff make_map_def not_Some_eq set_eqI)

lift_definition
  make_fmap :: "'k fset \<Rightarrow> 'v \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v)"
is "make_map"
by (unfold make_map_def dom_def, auto)

abbreviation 
  MAKE_FMAP :: "'k fset \<Rightarrow> 'v \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v)" ("[ _ |=> _ ]")
where
  "[ ks |=> v ] \<equiv> make_fmap ks v"

subsection {* The empty finite partial function *}

lift_definition
  fmap_empty :: "('k \<rightharpoonup>\<^sub>f 'v)"
is "empty"
by auto

subsection {* Domain *}

definition
  dom_fset :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k fset"
where "dom_fset f \<equiv> THE x. fset x = dom f"

lift_definition
  fdom :: "('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> 'k fset"
is "dom_fset" .

lemma inv_fset:
  assumes "finite X"
  shows "\<exists>!x. fset x = X"
using assms 
apply (induct rule: finite_induct)
apply (intro ex1I[of _ "{||}"])
apply (metis bot_fset.rep_eq)
apply (metis fset_cong bot_fset.rep_eq)
by (metis finsert.rep_eq fset_inject)

lemma fset_inv_fset:
  assumes "finite X"
  shows "fset (THE x. fset x = X) = X"
using assms 
by (metis (lifting, mono_tags) fset_cong inv_fset the_equality)

lemma fset_dom_fset:
  assumes "finite (dom f)"
  shows "fset (dom_fset f) = dom f"
by (metis dom_fset_def assms fset_inv_fset)

lemma fmap_add_commute:
  assumes "fdom A |\<inter>| fdom B = {||}"
  shows "A \<oplus> B = B \<oplus> A"
using assms
apply (transfer)
apply (fold fset_cong, simp add: dom_fset_def fset_inv_fset)
apply (rule map_add_comm, assumption)
done

lemma make_fmap_union: 
  "[ xs |=> v ] \<oplus> [ ys |=> v] = [ xs |\<union>| ys |=> v ]"
by (transfer, auto simp add: make_map_def map_add_def)

lemma fdom_union: 
  "fdom (xs \<oplus> ys) = fdom xs |\<union>| fdom ys"
by (transfer, fold fset_cong, auto simp add: dom_fset_def fset_inv_fset)

lemma fdom_make_fmap:
  "fdom [ ks |=> v ] = ks"
by (transfer, auto simp add: fset_cong dom_fset_def fset_inv_fset dom_make_map)

subsection {* Lookup *}

lift_definition
  lookup :: "('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> 'k \<Rightarrow> 'v"
is "op \<circ> the" .

lemma lookup_make_fmap:
  assumes "k \<in> fset ks"
  shows "lookup [ ks |=> v ] k = v"
using assms by (transfer, simp add: make_map_def)

lemma lookup_make_fmap1:
  "lookup [ {|k|} |=> v ] k = v"
by (metis finsert.rep_eq insert_iff lookup_make_fmap)

lemma lookup_union1:
  assumes "k |\<in>| fdom ys"
  shows "lookup (xs \<oplus> ys) k = lookup ys k"
using assms 
by transfer (metis comp_apply fmember.rep_eq fset_dom_fset map_add_dom_app_simps(1))

lemma lookup_union2:
  assumes "k |\<notin>| fdom ys"
  shows "lookup (xs \<oplus> ys) k = lookup xs k"
using assms 
by transfer (metis comp_apply fmember.rep_eq fset_dom_fset map_add_dom_app_simps(3))

lemma lookup_union3:
  assumes "k |\<notin>| fdom xs"
  shows "lookup (xs \<oplus> ys) k = lookup ys k"
using assms
apply (cases "k |\<in>| fdom ys")
apply (simp add: lookup_union1)
by transfer (metis comp_apply fmember.rep_eq fset_dom_fset map_add_dom_app_simps(2))

end
