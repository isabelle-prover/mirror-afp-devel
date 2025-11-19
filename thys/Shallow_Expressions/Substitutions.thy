section \<open> Substitutions \<close>

theory Substitutions
  imports Unrestriction
begin

subsection \<open> Types and Constants \<close>

text \<open> A substitution is simply a function between two state spaces. Typically,
  they are used to express mappings from variables to values (e.g. assignments). \<close>

type_synonym ('s\<^sub>1, 's\<^sub>2) psubst = "'s\<^sub>1 \<Rightarrow> 's\<^sub>2"
type_synonym 's subst = "'s \<Rightarrow> 's"

text \<open> There are different ways of constructing an empty substitution. \<close>

definition subst_id :: "'s subst" ("[\<leadsto>]") 
  where [expr_defs, code_unfold]: "subst_id = (\<lambda>s. s)"

definition subst_nil :: "('s\<^sub>1, 's\<^sub>2) psubst" ("\<lparr>\<leadsto>\<rparr>") 
  where [expr_defs, code_unfold]: "\<lparr>\<leadsto>\<rparr> = (\<lambda> s. undefined)"

definition subst_default :: "('s\<^sub>1, 's\<^sub>2::default) psubst" ("\<lblot>\<leadsto>\<rblot>") 
  where [expr_defs, code_unfold]: "\<lblot>\<leadsto>\<rblot> = (\<lambda> s. default)"

text \<open> We can update a substitution by adding a new variable maplet. \<close>

definition subst_upd :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('a \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('a, 's\<^sub>1) expr \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) psubst"
  where [expr_defs, code_unfold]: "subst_upd \<sigma> x e = (\<lambda> s. put\<^bsub>x\<^esub> (\<sigma> s) (e s))"

text \<open> The next two operators extend and restrict the alphabet of a substitution. \<close>

definition subst_ext :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>2, 's\<^sub>1) psubst" ("_\<^sup>\<up>" [999] 999) where
[expr_defs, code_unfold]: "subst_ext a = get\<^bsub>a\<^esub>"

definition subst_res :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) psubst" ("_\<^sub>\<down>" [999] 999) where
[expr_defs, code_unfold]: "subst_res a = create\<^bsub>a\<^esub>"

text \<open> Application of a substitution to an expression is effectively function composition. \<close>

definition subst_app :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('a, 's\<^sub>2) expr \<Rightarrow> ('a, 's\<^sub>1) expr" 
  where [expr_defs]: "subst_app \<sigma> e = (\<lambda> s. e (\<sigma> s))"

abbreviation "aext P a \<equiv> subst_app (a\<^sup>\<up>) P"
abbreviation "ares P a \<equiv> subst_app (a\<^sub>\<down>) P"

text \<open> We can also lookup the expression a variable is mapped to. \<close>

definition subst_lookup :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('a \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('a, 's\<^sub>1) expr" ("\<langle>_\<rangle>\<^sub>s")
  where [expr_defs, code_unfold]: "\<langle>\<sigma>\<rangle>\<^sub>s x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> s))"

definition subst_comp :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('s\<^sub>3, 's\<^sub>1) psubst \<Rightarrow> ('s\<^sub>3, 's\<^sub>2) psubst" (infixl "\<circ>\<^sub>s" 55) 
    where [expr_defs, code_unfold]: "subst_comp = comp"

definition unrest_usubst :: "'s scene \<Rightarrow> 's subst \<Rightarrow> bool" 
  where [expr_defs]: "unrest_usubst a \<sigma> = (\<forall> s s'. \<sigma> (s \<oplus>\<^sub>S s' on a) = (\<sigma> s) \<oplus>\<^sub>S s' on a)"

definition par_subst :: "'s subst \<Rightarrow> 's scene \<Rightarrow> 's scene \<Rightarrow> 's subst \<Rightarrow> 's subst"
  where [expr_defs]: "par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2 = (\<lambda> s. (s \<oplus>\<^sub>S (\<sigma>\<^sub>1 s) on A) \<oplus>\<^sub>S (\<sigma>\<^sub>2 s) on B)"

definition subst_restrict :: "'s subst \<Rightarrow> 's scene \<Rightarrow> 's subst" where 
[expr_defs]: "subst_restrict \<sigma> a = (\<lambda> s. s \<oplus>\<^sub>S \<sigma> s on a)"

text \<open> Create a substitution that copies the region from the given scene from a given state.
  This is used primarily in calculating unrestriction conditions. \<close>

definition sset :: "'s scene \<Rightarrow> 's \<Rightarrow> 's subst" 
  where [expr_defs, code_unfold]: "sset a s' = (\<lambda> s. s \<oplus>\<^sub>S s' on a)"

syntax "_sset" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("sset[_, _]")
translations "_sset a P" == "CONST sset a P"

subsection \<open> Syntax Translations \<close>

nonterminal uexprs and smaplet and smaplets

syntax
  "_subst_app" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<dagger>" 65)
  "_smaplet"        :: "[svid, logic] => smaplet" ("_ \<leadsto> _")
  ""                :: "smaplet => smaplets" ("_")
  "_SMaplets"       :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  \<comment> \<open> A little syntax utility to extract a list of variable identifiers from a substitution \<close>
  "_smaplets_svids" :: "smaplets \<Rightarrow> logic"
  "_SubstUpd"       :: "[logic, smaplets] => logic" ("_/'(_')" [900,0] 900)
  "_Subst"          :: "smaplets => logic" ("(1[_])")
  "_PSubst"         :: "smaplets => logic" ("(1\<lparr>_\<rparr>)")
  "_DSubst"         :: "smaplets \<Rightarrow> logic" ("(1\<lblot>_\<rblot>)")
  "_psubst"         :: "[logic, svids, uexprs] \<Rightarrow> logic"
  "_subst"          :: "logic \<Rightarrow> uexprs \<Rightarrow> svids \<Rightarrow> logic" ("(_\<lbrakk>_'/_\<rbrakk>)" [990,0,0] 991)
  "_uexprs"         :: "[logic, uexprs] => uexprs" ("_,/ _")
  ""                :: "logic => uexprs" ("_")
  "_par_subst"      :: "logic \<Rightarrow> salpha \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ [_|_]\<^sub>s _" [100,0,0,101] 101)
  "_subst_restrict" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\<restriction>\<^sub>s" 85)
  "_unrest_usubst"  :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>\<^sub>s" 20)

translations
  "_subst_app \<sigma> e"                    == "CONST subst_app \<sigma> e"
  "_subst_app \<sigma> e"                    <= "_subst_app \<sigma> (e)\<^sub>e"
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet x y)"        == "CONST subst_upd m x (y)\<^sub>e"
  "_Subst ms"                         == "_SubstUpd [\<leadsto>] ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_PSubst ms"                        == "_SubstUpd \<lparr>\<leadsto>\<rparr> ms"
  "_PSubst (_SMaplets ms1 ms2)"       <= "_SubstUpd (_PSubst ms1) ms2"
  "_DSubst ms"                        == "_SubstUpd \<lblot>\<leadsto>\<rblot> ms"
  "_DSubst (_SMaplets ms1 ms2)"       <= "_SubstUpd (_DSubst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"
  "_smaplets_svids (_SMaplets (_smaplet x e) ms)" => "x +\<^sub>L (_smaplets_svids ms)"
  "_smaplets_svids (_smaplet x e)" => "x"
  "_subst P es vs" => "CONST subst_app (_psubst [\<leadsto>] vs es) P"
  "_psubst m (_svid_list x xs) (_uexprs v vs)" => "_psubst (_psubst m x v) xs vs"
  "_psubst m x v"  => "CONST subst_upd m x (v)\<^sub>e"
  "_subst P v x" <= "CONST subst_app (CONST subst_upd [\<leadsto>] x (v)\<^sub>e) P"
  "_subst P v x" <= "_subst_app (_Subst (_smaplet x v)) P"
  "_subst P v x" <= "_subst (_sexp_quote P)  v x"
  "_subst P v (_svid_tuple (_of_svid_list (x +\<^sub>L y)))" <= "_subst P v (x +\<^sub>L y)"
  "_par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2" == "CONST par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2"
  "_subst_restrict \<sigma> a" == "CONST subst_restrict \<sigma> a"
  "_unrest_usubst x p" == "CONST unrest_usubst x p"
  "_unrest_usubst (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_unrest_usubst (x +\<^sub>L y) P"

expr_constructor subst_app (1) \<comment> \<open> Only the second parameter (1) should be treated as a lifted expression. \<close> 
expr_constructor subst_id
expr_constructor subst_nil
expr_constructor subst_default
expr_constructor subst_upd
expr_constructor subst_lookup

ML_file \<open>Expr_Util.ML\<close>

subsection \<open> Substitution Laws \<close>

named_theorems usubst and usubst_eval

lemma subst_id_apply [usubst]: "[\<leadsto>] \<dagger> P = P"
  by (expr_auto)

lemma subst_unrest [usubst]:
  "\<lbrakk> vwb_lens x; $x \<sharp> v \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> e) \<dagger> v = \<sigma> \<dagger> v"
  by expr_auto

lemma subst_lookup_id [usubst]: "\<langle>[\<leadsto>]\<rangle>\<^sub>s x = [var x]\<^sub>e"
  by expr_simp

lemma subst_lookup_aext [usubst]: "\<langle>a\<^sup>\<up>\<rangle>\<^sub>s x = [get\<^bsub>ns_alpha a x\<^esub>]\<^sub>e"
  by expr_auto

lemma subst_id_var: "[\<leadsto>] = ($\<^bold>v)\<^sub>e"
  by expr_simp

lemma subst_upd_id_lam [usubst]: "subst_upd ($\<^bold>v)\<^sub>e x v = subst_upd [\<leadsto>] x v"
  by expr_simp

lemma subst_id [simp]: "[\<leadsto>] \<circ>\<^sub>s \<sigma> = \<sigma>" "\<sigma> \<circ>\<^sub>s [\<leadsto>] = \<sigma>"
  by expr_auto+

lemma subst_default_id [simp]: "\<lblot>\<leadsto>\<rblot> \<circ>\<^sub>s \<sigma> = \<lblot>\<leadsto>\<rblot>"
  by (simp add: expr_defs comp_def)

lemma subst_lookup_one_lens [usubst]: "\<langle>\<sigma>\<rangle>\<^sub>s 1\<^sub>L = \<sigma>"
  by expr_simp

text \<open> The following law can break expressions abstraction, so it is not by default a 
  "usubst" law. \<close>

lemma subst_apply_SEXP: "subst_app \<sigma> [e]\<^sub>e = [subst_app \<sigma> e]\<^sub>e"
  by expr_simp

lemma subst_apply_twice [usubst]: 
  "\<rho> \<dagger> (\<sigma> \<dagger> e) = (\<sigma> \<circ>\<^sub>s \<rho>) \<dagger> e"
  by expr_simp

lemma subst_apply_twice_SEXP [usubst]: 
  "\<rho> \<dagger> [\<sigma> \<dagger> e]\<^sub>e = (\<sigma> \<circ>\<^sub>s \<rho>) \<dagger> [e]\<^sub>e"
  by expr_simp

(* FIXME: Figure out how to make laws like this parse and simplify *)

term "(f (\<sigma> \<dagger> e))\<^sub>e"

term "(\<forall> x. x + $y > $z)\<^sub>e"

term "(\<forall> k. P\<lbrakk>\<guillemotleft>k\<guillemotright>/x\<rbrakk>)\<^sub>e"

lemma subst_get [usubst]: "\<sigma> \<dagger> get\<^bsub>x\<^esub> = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (simp add: expr_defs)

lemma subst_var [usubst]: "\<sigma> \<dagger> ($x)\<^sub>e = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (simp add: expr_defs)

text \<open> We can't use this as simplification unfortunately as the expression structure is too
  ambiguous to support automatic rewriting. \<close>

lemma subst_uop: "\<sigma> \<dagger> (\<guillemotleft>f\<guillemotright> e)\<^sub>e = (\<guillemotleft>f\<guillemotright> (\<sigma> \<dagger> e))\<^sub>e"
  by (simp add: expr_defs)

lemma subst_bop: "\<sigma> \<dagger> (\<guillemotleft>f\<guillemotright> e\<^sub>1 e\<^sub>2)\<^sub>e = (\<guillemotleft>f\<guillemotright> (\<sigma> \<dagger> e\<^sub>1) (\<sigma> \<dagger> e\<^sub>2))\<^sub>e"
  by (simp add: expr_defs)

lemma subst_lit [usubst]: "\<sigma> \<dagger> (\<guillemotleft>v\<guillemotright>)\<^sub>e = (\<guillemotleft>v\<guillemotright>)\<^sub>e"
  by (expr_simp)

lemmas subst_basic_ops [usubst] =
  subst_bop[where f=conj] 
  subst_bop[where f=disj] 
  subst_bop[where f=implies] 
  subst_uop[where f=Not]
  subst_bop[where f=HOL.eq] 
  subst_bop[where f=less]
  subst_bop[where f=less_eq]
  subst_bop[where f=Set.member] 
  subst_bop[where f=inf]
  subst_bop[where f=sup]
  subst_bop[where f=Pair]

text \<open> A substitution update naturally yields the given expression. \<close>
    
lemma subst_lookup_upd [usubst]:
  assumes "weak_lens x"
  shows "\<langle>\<sigma>(x \<leadsto> v)\<rangle>\<^sub>s x = (v)\<^sub>e"
  using assms by (simp add: expr_defs)

lemma subst_lookup_upd_diff [usubst]:
  assumes "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<leadsto> v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms by (simp add: expr_defs)

lemma subst_lookup_pair [usubst]: 
  "\<langle>\<sigma>\<rangle>\<^sub>s (x +\<^sub>L y) = ((\<langle>\<sigma>\<rangle>\<^sub>s x, \<langle>\<sigma>\<rangle>\<^sub>s y))\<^sub>e"
  by (expr_simp)

text \<open> Substitution update is idempotent. \<close>

lemma usubst_upd_idem [usubst]:
  assumes "mwb_lens x"
  shows "\<sigma>(x \<leadsto> u, x \<leadsto> v) = \<sigma>(x \<leadsto> v)"
  using assms by (simp add: expr_defs)

lemma usubst_upd_idem_sub [usubst]:
  assumes "x \<subseteq>\<^sub>L y" "mwb_lens y"
  shows "\<sigma>(x \<leadsto> u, y \<leadsto> v) = \<sigma>(y \<leadsto> v)"
  using assms by (simp add: expr_defs assms fun_eq_iff sublens_put_put)

text \<open> Substitution updates commute when the lenses are independent. \<close>
    
lemma subst_upd_comm:
  assumes "x \<bowtie> y"
  shows "\<sigma>(x \<leadsto> u, y \<leadsto> v) = \<sigma>(y \<leadsto> v, x \<leadsto> u)"
  using assms unfolding subst_upd_def
  by (auto simp add: subst_upd_def assms comp_def lens_indep_comm)

lemma subst_upd_comm2:
  assumes "z \<bowtie> y"
  shows "\<sigma>(x \<leadsto> u, y \<leadsto> v, z \<leadsto> s) = \<sigma>(x \<leadsto> u, z \<leadsto> s, y \<leadsto> v)"
  using assms unfolding subst_upd_def
  by (auto simp add: subst_upd_def assms comp_def lens_indep_comm)

lemma subst_upd_var_id [usubst]:
  "vwb_lens x \<Longrightarrow> [x \<leadsto> $x] = [\<leadsto>]"
  by (simp add: subst_upd_def subst_id_def id_lens_def SEXP_def)

lemma subst_upd_pair [usubst]:
  "\<sigma>((x, y) \<leadsto> (e, f)) = \<sigma>(y \<leadsto> f, x \<leadsto> e)"
  by (simp add: subst_upd_def lens_defs SEXP_def fun_eq_iff)

lemma subst_upd_comp [usubst]:
  "\<rho>(x \<leadsto> v) \<circ>\<^sub>s \<sigma> = (\<rho> \<circ>\<^sub>s \<sigma>)(x \<leadsto> \<sigma> \<dagger> v)"
  by (simp add: expr_defs fun_eq_iff)

lemma swap_subst_inj: "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> inj [(x, y) \<leadsto> ($y, $x)]"
  by (simp add: expr_defs lens_defs inj_on_def)
     (metis lens_indep.lens_put_irr2 lens_indep_get vwb_lens.source_determination vwb_lens_def wb_lens_weak weak_lens.put_get)

subsection \<open> Proof rules \<close>

text \<open> In proof, a lens can always be substituted for an arbitrary but fixed value. \<close>

lemma taut_substI:
  assumes "vwb_lens x" "\<And> v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`"
  shows "`P`"
  using assms by (expr_simp, metis vwb_lens.put_eq)

lemma eq_substI:
  assumes "vwb_lens x" "\<And> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> = Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>"
  shows "P = Q"
  using assms by (expr_simp, metis vwb_lens.put_eq)

lemma bool_eq_substI:
  assumes "vwb_lens x" "P\<lbrakk>True/x\<rbrakk> = Q\<lbrakk>True/x\<rbrakk>" "P\<lbrakk>False/x\<rbrakk> = Q\<lbrakk>False/x\<rbrakk>"
  shows "P = Q"
  by (metis (full_types) assms eq_substI)

lemma less_eq_substI:
  assumes "vwb_lens x" "\<And> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<le> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>"
  shows "P \<le> Q"
  using assms by (expr_simp, metis le_funE le_funI vwb_lens_def wb_lens.source_stability)

subsection \<open> Ordering substitutions \<close>

text \<open> A simplification procedure to reorder substitutions maplets lexicographically by variable syntax \<close>

simproc_setup subst_order ("subst_upd (subst_upd \<sigma> x u) y v") =
  \<open> (fn _ => fn ctx => fn ct => 
        case (Thm.term_of ct) of
          Const (@{const_name subst_upd}, _) $ (Const (@{const_name subst_upd}, _) $ s $ x $ u) $ y $ v
            => if (XML.content_of (YXML.parse_body (Syntax.string_of_term ctx x)) > XML.content_of (YXML.parse_body (Syntax.string_of_term ctx y)))
               then SOME (mk_meta_eq @{thm subst_upd_comm})
               else NONE  |
          _ => NONE) 
  \<close>

subsection \<open> Substitution Unrestriction Laws \<close>

lemma unrest_subst_lens [expr_simps]: "mwb_lens x \<Longrightarrow> ($x \<sharp>\<^sub>s \<sigma>) = (\<forall>s v. \<sigma> (put\<^bsub>x\<^esub> s v) = put\<^bsub>x\<^esub> (\<sigma> s) v)"
  by (simp add: unrest_usubst_def, metis lens_override_def mwb_lens_weak weak_lens.create_get)

lemma unrest_subst_empty [unrest]: "x \<sharp>\<^sub>s [\<leadsto>]"
  by (expr_simp)

lemma unrest_subst_upd [unrest]: "\<lbrakk> vwb_lens x; x \<bowtie> y; $x \<sharp> (e)\<^sub>e; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> $x \<sharp>\<^sub>s \<sigma>(y \<leadsto> e)"
  by (expr_auto add: lens_indep_comm)

lemma unrest_subst_upd_compl [unrest]: "\<lbrakk> vwb_lens x; y \<subseteq>\<^sub>L x; -$x \<sharp> (e)\<^sub>e; -$x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> -$x \<sharp>\<^sub>s \<sigma>(y \<leadsto> e)"
  by (expr_auto, simp add: lens_override_def scene_override_commute)

lemma unrest_subst_apply [unrest]:
  "\<lbrakk> $x \<sharp> P; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> $x \<sharp> (\<sigma> \<dagger> P)"
  by (expr_auto)

lemma unrest_sset [unrest]:
  "x \<bowtie> y \<Longrightarrow> $x \<sharp>\<^sub>s sset[$y, v]"
  by (expr_auto, meson lens_indep_impl_scene_indep scene_override_commute_indep)

subsection \<open> Conditional Substitution Laws \<close>

lemma subst_cond_upd_1 [usubst]:
  "\<sigma>(x \<leadsto> u) \<triangleleft> b \<triangleright> \<rho>(x \<leadsto> v) = (\<sigma> \<triangleleft> b \<triangleright> \<rho>)(x \<leadsto> (u \<triangleleft> b \<triangleright> v))"
  by expr_auto

lemma subst_cond_upd_2 [usubst]:
  "\<lbrakk> vwb_lens x; $x \<sharp>\<^sub>s \<rho> \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> u) \<triangleleft> b \<triangleright> \<rho> = (\<sigma> \<triangleleft> b \<triangleright> \<rho>)(x \<leadsto> (u \<triangleleft> b \<triangleright> ($x)\<^sub>e))"
  by (expr_auto, metis lens_override_def lens_override_idem)

lemma subst_cond_upd_3 [usubst]:
  "\<lbrakk> vwb_lens x; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<triangleleft> b \<triangleright> \<rho>(x \<leadsto> v) = (\<sigma> \<triangleleft> b \<triangleright> \<rho>)(x \<leadsto> (($x)\<^sub>e \<triangleleft> b \<triangleright> v))"
  by (expr_auto, metis lens_override_def lens_override_idem)

lemma expr_if_bool_var_left: "vwb_lens x \<Longrightarrow> P\<lbrakk>True/x\<rbrakk> \<triangleleft> $x \<triangleright> Q = P \<triangleleft> $x \<triangleright> Q"
  by (expr_simp, metis (full_types) lens_override_def lens_override_idem)

lemma expr_if_bool_var_right: "vwb_lens x \<Longrightarrow> P \<triangleleft> $x \<triangleright> Q\<lbrakk>False/x\<rbrakk> = P \<triangleleft> $x \<triangleright> Q"
  by (expr_simp, metis (full_types) lens_override_def lens_override_idem)

lemma subst_expr_if [usubst]: "\<sigma> \<dagger> (P \<triangleleft> B \<triangleright> Q) = (\<sigma> \<dagger> P) \<triangleleft> (\<sigma> \<dagger> B) \<triangleright> (\<sigma> \<dagger> Q)"
  by expr_simp

subsection \<open> Substitution Restriction Laws \<close>

lemma subst_restrict_id [usubst]: "idem_scene a \<Longrightarrow> [\<leadsto>] \<restriction>\<^sub>s a = [\<leadsto>]"
  by expr_simp

lemma subst_restrict_out [usubst]: "\<lbrakk> vwb_lens x; vwb_lens a; x \<bowtie> a \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> e) \<restriction>\<^sub>s $a = \<sigma> \<restriction>\<^sub>s $a" 
  by (expr_simp add: lens_indep.lens_put_irr2)

lemma subst_restrict_in [usubst]: "\<lbrakk> vwb_lens x; vwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> e) \<restriction>\<^sub>s $y = (\<sigma> \<restriction>\<^sub>s $y)(x \<leadsto> e)" 
  by (expr_auto)

lemma subst_restrict_twice [simp]: "\<sigma> \<restriction>\<^sub>s a \<restriction>\<^sub>s a = \<sigma> \<restriction>\<^sub>s a"
  by expr_simp

subsection \<open> Evaluation \<close>

lemma subst_SEXP [usubst_eval]: "\<sigma> \<dagger> [\<lambda> s. e s]\<^sub>e = [\<lambda> s. e (\<sigma> s)]\<^sub>e"
  by (simp add: SEXP_def subst_app_def fun_eq_iff)

lemma get_subst_id [usubst_eval]: "get\<^bsub>x\<^esub> ([\<leadsto>] s) = get\<^bsub>x\<^esub> s"
  by (simp add: subst_id_def)

lemma get_subst_upd_same [usubst_eval]: "weak_lens x \<Longrightarrow> get\<^bsub>x\<^esub> ((\<sigma>(x \<leadsto> e)) s) = e s"
  by (simp add: subst_upd_def SEXP_def)

lemma get_subst_upd_indep [usubst_eval]: 
  "x \<bowtie> y \<Longrightarrow> get\<^bsub>x\<^esub> ((\<sigma>(y \<leadsto> e)) s) = get\<^bsub>x\<^esub> (\<sigma> s)"
  by (simp add: subst_upd_def)

lemma unrest_ssubst: "(a \<sharp> P) \<longleftrightarrow> (\<forall> s'. sset a s' \<dagger> P = (P)\<^sub>e)"
  by (auto simp add: expr_defs fun_eq_iff)

lemma unrest_ssubst_expr: "(a \<sharp> (P)\<^sub>e) = (\<forall>s'. sset[a, s'] \<dagger> (P)\<^sub>e = (P)\<^sub>e)"
  by (simp add: unrest_ssubst)

lemma get_subst_sset_out [usubst_eval]: "\<lbrakk> vwb_lens x; var_alpha x \<bowtie>\<^sub>S a \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> (sset a s' s) = get\<^bsub>x\<^esub> s"
  by (simp add: expr_defs var_alpha_def get_scene_override_indep)

lemma get_subst_sset_in [usubst_eval]: "\<lbrakk> vwb_lens x; var_alpha x \<le> a \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> (sset a s' s) = get\<^bsub>x\<^esub> s'"
  by (simp add: get_scene_override_le sset_def var_alpha_def)

lemma get_subst_ext [usubst_eval]: "get\<^bsub>x\<^esub> (subst_ext a s) = get\<^bsub>ns_alpha a x\<^esub> s"
  by (expr_simp)

lemma unrest_sset_lens [unrest]: "\<lbrakk> mwb_lens x; mwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> $x \<sharp>\<^sub>s sset[$y, s]"
  by (simp add: sset_def unrest_subst_lens lens_indep_comm lens_override_def)

lemma get_subst_restrict_out [usubst_eval]: "\<lbrakk> vwb_lens a; x \<bowtie> a \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> ((\<sigma> \<restriction>\<^sub>s $a) s) = get\<^bsub>x\<^esub> s"
  by (expr_simp)

lemma get_subst_restrict_in [usubst_eval]: "\<lbrakk> vwb_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> ((\<sigma> \<restriction>\<^sub>s $a) s) = get\<^bsub>x\<^esub> (\<sigma> s)"
  by (expr_simp, force)

text \<open> If a variable is unrestricted in a substitution then it's application has no effect. \<close>

lemma subst_apply_unrest:
  "\<lbrakk> vwb_lens x; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s x = var x"
proof -
  assume 1: "vwb_lens x" and "$x \<sharp>\<^sub>s \<sigma>"
  hence "\<forall>s s'. \<sigma> (s \<oplus>\<^sub>L s' on x) = \<sigma> s \<oplus>\<^sub>L s' on x"
    by (simp add: unrest_usubst_def)
  thus "\<langle>\<sigma>\<rangle>\<^sub>s x = var x"
    by (metis 1 lens_override_def lens_override_idem mwb_lens_weak subst_lookup_def vwb_lens_mwb weak_lens.put_get)
qed

text \<open> A tactic for proving unrestrictions by evaluating a special kind of substitution. \<close>

method unrest uses add = (simp add: add unrest unrest_ssubst_expr var_alpha_combine usubst usubst_eval)

text \<open> A tactic for evaluating substitutions. \<close>

method subst_eval uses add = (simp add: add usubst_eval usubst unrest)

text \<open> We can exercise finer grained control over substitutions with the following method. \<close>

declare vwb_lens_mwb [lens]
declare mwb_lens_weak [lens]

method subst_eval' = (simp only: lens usubst_eval usubst unrest SEXP_apply)

end