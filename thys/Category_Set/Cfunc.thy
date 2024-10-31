section \<open>Basic Types and Operators for the Category of Sets\<close>

theory Cfunc
  imports Main "HOL-Eisbach.Eisbach"
begin

typedecl cset
typedecl cfunc

text \<open>We declare @{type cset} and @{type cfunc} as types to represent the sets and functions within
  ETCS, as distinct from HOL sets and functions.
  The "c" prefix here is intended to stand for "category", and emphasises that these are
  category-theoretic objects.\<close>

text \<open>The axiomatization below corresponds to Axiom 1 (Sets Is a Category) in Halvorson.\<close>
axiomatization
  domain :: "cfunc \<Rightarrow> cset" and
  codomain :: "cfunc \<Rightarrow> cset" and
  comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<circ>\<^sub>c" 55) and
  id :: "cset \<Rightarrow> cfunc" ("id\<^sub>c") 
where
  domain_comp: "domain g = codomain f \<Longrightarrow> domain (g \<circ>\<^sub>c f) = domain f" and
  codomain_comp: "domain g = codomain f \<Longrightarrow> codomain (g \<circ>\<^sub>c f) = codomain g" and
  comp_associative: "domain h = codomain g \<Longrightarrow> domain g = codomain f \<Longrightarrow> h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f" and
  id_domain: "domain (id X) = X" and
  id_codomain: "codomain (id X) = X" and
  id_right_unit: "f \<circ>\<^sub>c id (domain f) = f" and
  id_left_unit: "id (codomain f) \<circ>\<^sub>c f = f"


text \<open>We define a neater way of stating types and lift the type axioms into lemmas using it.\<close>
definition cfunc_type :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" ("_ : _ \<rightarrow> _" [50, 50, 50]50) where
  "(f : X \<rightarrow> Y) \<longleftrightarrow> (domain f = X \<and> codomain f = Y)"

lemma comp_type:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> g \<circ>\<^sub>c f : X \<rightarrow> Z"
  by (simp add: cfunc_type_def codomain_comp domain_comp)

lemma comp_associative2:
  "f : X \<rightarrow> Y \<Longrightarrow> g : Y \<rightarrow> Z \<Longrightarrow> h : Z \<rightarrow> W \<Longrightarrow> h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f"
  by (simp add: cfunc_type_def comp_associative)

lemma id_type: "id X : X \<rightarrow> X"
  unfolding cfunc_type_def using id_domain id_codomain by auto

lemma id_right_unit2: "f : X \<rightarrow> Y \<Longrightarrow> f \<circ>\<^sub>c id X = f"
  unfolding cfunc_type_def using id_right_unit by auto

lemma id_left_unit2: "f : X \<rightarrow> Y \<Longrightarrow> id Y \<circ>\<^sub>c f = f"
  unfolding cfunc_type_def using id_left_unit by auto

subsection \<open>Tactics for Applying Typing Rules\<close>

text \<open>ETCS lemmas often have assumptions on its ETCS type, which can often be cumbersome to prove.
  To simplify proofs involving ETCS types, we provide proof methods that apply type rules in a
  structured way to prove facts about ETCS function types.
  The type rules state the types of the basic constants and operators of ETCS and are declared as
  a named set of theorems called $type\_rule$.\<close>

named_theorems type_rule

declare id_type[type_rule]
declare comp_type[type_rule]

ML_file \<open>typecheck.ml\<close>

subsubsection \<open>typecheck\_cfuncs: Tactic to Construct Type Facts\<close>

method_setup typecheck_cfuncs =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_method\<close>
  "Check types of cfuncs in current goal and add as assumptions of the current goal"

method_setup typecheck_cfuncs_all =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_all_method\<close>
  "Check types of cfuncs in all subgoals and add as assumptions of the current goal"

method_setup typecheck_cfuncs_prems =
  \<open>Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> typecheck_cfuncs_prems_method\<close>
  "Check types of cfuncs in assumptions of the current goal and add as assumptions of the current goal"

subsubsection \<open>etcs\_rule: Tactic to Apply Rules with ETCS Typechecking\<close>

method_setup etcs_rule = 
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_resolve_method\<close>
  "apply rule with ETCS type checking"

subsubsection \<open>etcs\_subst: Tactic to Apply Substitutions with ETCS Typechecking\<close>

method_setup etcs_subst = 
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_subst_method\<close> 
  "apply substitution with ETCS type checking"

method etcs_assocl declares type_rule = (etcs_subst comp_associative2)+
method etcs_assocr declares type_rule = (etcs_subst sym[OF comp_associative2])+

method_setup etcs_subst_asm = 
  \<open>Runtime.exn_trace (fn _ => Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_subst_asm_method)\<close> 
  "apply substitution to assumptions of the goal, with ETCS type checking"

method etcs_assocl_asm declares type_rule = (etcs_subst_asm comp_associative2)+
method etcs_assocr_asm declares type_rule = (etcs_subst_asm sym[OF comp_associative2])+

subsubsection \<open>etcs\_erule: Tactic to Apply Elimination Rules with ETCS Typechecking\<close>

method_setup etcs_erule = 
  \<open>Scan.repeats (Scan.unless (Scan.lift (Args.$$$ "type_rule" -- Args.colon)) Attrib.multi_thm)
    -- Scan.option ((Scan.lift (Args.$$$ "type_rule" -- Args.colon)) |-- Attrib.thms)
     >> ETCS_eresolve_method\<close>
  "apply erule with ETCS type checking"

subsection \<open>Monomorphisms, Epimorphisms and Isomorphisms\<close>

subsubsection \<open>Monomorphisms\<close>

definition monomorphism :: "cfunc \<Rightarrow> bool" where
  "monomorphism f \<longleftrightarrow> (\<forall> g h. 
    (codomain g = domain f \<and> codomain h = domain f) \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"

lemma monomorphism_def2:
  "monomorphism f \<longleftrightarrow> (\<forall> g h A X Y. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<and> f : X \<rightarrow> Y \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"
  unfolding monomorphism_def by (smt cfunc_type_def domain_comp)

lemma monomorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "monomorphism f \<longleftrightarrow> (\<forall> g h A. g : A \<rightarrow> X \<and> h : A \<rightarrow> X \<longrightarrow> (f \<circ>\<^sub>c g = f \<circ>\<^sub>c h \<longrightarrow> g = h))"
  unfolding monomorphism_def2 using assms cfunc_type_def by auto 

text \<open>The lemma below corresponds to Exercise 2.1.7a in Halvorson.\<close>
lemma comp_monic_imp_monic:
  assumes "domain g = codomain f"
  shows "monomorphism (g \<circ>\<^sub>c f) \<Longrightarrow> monomorphism f"
  unfolding monomorphism_def
proof clarify
  fix s t
  assume gf_monic: "\<forall>s. \<forall>t. 
    codomain s = domain (g \<circ>\<^sub>c f) \<and> codomain t = domain (g \<circ>\<^sub>c f) \<longrightarrow>
          (g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume codomain_s: "codomain s = domain f"
  assume codomain_t: "codomain t = domain f"
  assume "f \<circ>\<^sub>c s = f \<circ>\<^sub>c t"

  then have "(g \<circ>\<^sub>c f) \<circ>\<^sub>c s = (g \<circ>\<^sub>c f) \<circ>\<^sub>c t"
    by (metis assms codomain_s codomain_t comp_associative)
  then show "s = t"
    using gf_monic codomain_s codomain_t domain_comp by (simp add: assms)
qed

lemma comp_monic_imp_monic':
  assumes "f : X \<rightarrow> Y" "g : Y \<rightarrow> Z"
  shows "monomorphism (g \<circ>\<^sub>c f) \<Longrightarrow> monomorphism f"
  by (metis assms cfunc_type_def comp_monic_imp_monic)

text \<open>The lemma below corresponds to Exercise 2.1.7c in Halvorson.\<close>
lemma composition_of_monic_pair_is_monic:
  assumes "codomain f = domain g"
  shows "monomorphism f \<Longrightarrow> monomorphism g \<Longrightarrow> monomorphism (g \<circ>\<^sub>c f)"
  unfolding monomorphism_def
proof clarify
  fix h k
  assume f_mono: "\<forall>s t. 
    codomain s = domain f \<and> codomain t = domain f \<longrightarrow> f \<circ>\<^sub>c s = f \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume g_mono: "\<forall>s. \<forall>t. 
    codomain s = domain g \<and> codomain t = domain g \<longrightarrow> g \<circ>\<^sub>c s = g \<circ>\<^sub>c t \<longrightarrow> s = t"
  assume codomain_k: "codomain k = domain (g \<circ>\<^sub>c f)"
  assume codomain_h: "codomain h = domain (g \<circ>\<^sub>c f)"
  assume gfh_eq_gfk: "(g \<circ>\<^sub>c f) \<circ>\<^sub>c k = (g \<circ>\<^sub>c f) \<circ>\<^sub>c h"
 
  have "g \<circ>\<^sub>c (f \<circ>\<^sub>c h) = (g  \<circ>\<^sub>c f)  \<circ>\<^sub>c h"
    by (simp add: assms codomain_h comp_associative domain_comp)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c k"
    by (simp add: gfh_eq_gfk)
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)"
    by (simp add: assms codomain_k comp_associative domain_comp)
  ultimately have "f \<circ>\<^sub>c h = f \<circ>\<^sub>c k"
    using assms cfunc_type_def codomain_h codomain_k comp_type domain_comp g_mono by auto
  then show "k = h"
    by (simp add: codomain_h codomain_k domain_comp f_mono assms)
qed

subsubsection \<open>Epimorphisms\<close>

definition epimorphism :: "cfunc \<Rightarrow> bool" where
  "epimorphism f \<longleftrightarrow> (\<forall> g h. 
    (domain g = codomain f \<and> domain h = codomain f) \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"

lemma epimorphism_def2:
  "epimorphism f \<longleftrightarrow> (\<forall> g h A X Y. f : X \<rightarrow> Y \<and> g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"
  unfolding epimorphism_def by (smt cfunc_type_def codomain_comp) 

lemma epimorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "epimorphism f \<longleftrightarrow> (\<forall> g h A. g : Y \<rightarrow> A \<and> h : Y \<rightarrow> A \<longrightarrow> (g \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> g = h))"
  unfolding epimorphism_def2 using assms cfunc_type_def by auto

text \<open>The lemma below corresponds to Exercise 2.1.7b in Halvorson.\<close>
lemma comp_epi_imp_epi:
  assumes "domain g = codomain f"
  shows "epimorphism (g \<circ>\<^sub>c f) \<Longrightarrow> epimorphism g"
  unfolding epimorphism_def
proof clarify
  fix s t
  assume gf_epi: "\<forall>s. \<forall>t.
    domain s = codomain (g \<circ>\<^sub>c f) \<and> domain t = codomain (g \<circ>\<^sub>c f) \<longrightarrow>
          s \<circ>\<^sub>c g \<circ>\<^sub>c f = t \<circ>\<^sub>c g \<circ>\<^sub>c f \<longrightarrow> s = t"
  assume domain_s: "domain s = codomain g"
  assume domain_t: "domain t = codomain g"
  assume sf_eq_tf: "s \<circ>\<^sub>c g = t \<circ>\<^sub>c g"

  from sf_eq_tf have "s \<circ>\<^sub>c (g \<circ>\<^sub>c f) = t \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: assms comp_associative domain_s domain_t)
  then show "s = t"
    using gf_epi codomain_comp domain_s domain_t by (simp add: assms)
qed

text \<open>The lemma below corresponds to Exercise 2.1.7d in Halvorson.\<close>
lemma composition_of_epi_pair_is_epi:
assumes "codomain f = domain g"
  shows "epimorphism f \<Longrightarrow> epimorphism g \<Longrightarrow> epimorphism (g \<circ>\<^sub>c f)"
  unfolding epimorphism_def
proof clarify
  fix h k
  assume f_epi :"\<forall> s h.
    (domain s = codomain f \<and> domain h = codomain f) \<longrightarrow> (s \<circ>\<^sub>c f = h \<circ>\<^sub>c f \<longrightarrow> s = h)"
  assume g_epi :"\<forall> s h.
    (domain s = codomain g \<and> domain h = codomain g) \<longrightarrow> (s \<circ>\<^sub>c g = h \<circ>\<^sub>c g \<longrightarrow> s = h)"
  assume domain_k: "domain k = codomain (g \<circ>\<^sub>c f)"
  assume domain_h: "domain h = codomain (g \<circ>\<^sub>c f)"
  assume hgf_eq_kgf: "h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = k \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
  
  have "(h \<circ>\<^sub>c g) \<circ>\<^sub>c f = h \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: assms codomain_comp comp_associative domain_h)
  also have "... = k \<circ>\<^sub>c (g \<circ>\<^sub>c f)"
    by (simp add: hgf_eq_kgf)
  also have "... =(k \<circ>\<^sub>c g) \<circ>\<^sub>c f "
    by (simp add: assms codomain_comp comp_associative domain_k)
  ultimately have "h \<circ>\<^sub>c g = k \<circ>\<^sub>c g"
    by (simp add: assms codomain_comp domain_comp domain_h domain_k f_epi)
  then show "h = k"
    by (simp add: codomain_comp domain_h domain_k g_epi assms)
qed

subsubsection \<open>Isomorphisms\<close>

definition isomorphism :: "cfunc \<Rightarrow> bool" where
  "isomorphism f \<longleftrightarrow> (\<exists> g. domain g = codomain f \<and> codomain g = domain f \<and> 
    g \<circ>\<^sub>c f = id(domain f) \<and> f \<circ>\<^sub>c g = id(domain g))"

lemma isomorphism_def2:
  "isomorphism f \<longleftrightarrow> (\<exists> g X Y. f : X \<rightarrow> Y \<and> g : Y \<rightarrow> X \<and> g \<circ>\<^sub>c f = id X \<and> f \<circ>\<^sub>c g = id Y)"
  unfolding isomorphism_def cfunc_type_def by auto

lemma isomorphism_def3:
  assumes "f : X \<rightarrow> Y"
  shows "isomorphism f \<longleftrightarrow> (\<exists> g. g : Y \<rightarrow> X \<and> g \<circ>\<^sub>c f = id X \<and> f \<circ>\<^sub>c g = id Y)"
  using assms unfolding isomorphism_def2 cfunc_type_def by auto

definition inverse :: "cfunc \<Rightarrow> cfunc" ("_\<^bold>\<inverse>" [1000] 999) where
  "inverse f = (THE g. g : codomain f \<rightarrow> domain f \<and> g \<circ>\<^sub>c f = id(domain f) \<and> f \<circ>\<^sub>c g = id(codomain f))"

lemma inverse_def2:
  assumes "isomorphism f"
  shows "f\<^bold>\<inverse> : codomain f \<rightarrow> domain f \<and> f\<^bold>\<inverse> \<circ>\<^sub>c f = id(domain f) \<and> f \<circ>\<^sub>c f\<^bold>\<inverse> = id(codomain f)"
  unfolding inverse_def
proof (rule theI', safe)
  show "\<exists>g. g : codomain f \<rightarrow> domain f \<and> g \<circ>\<^sub>c f = id\<^sub>c (domain f) \<and> f \<circ>\<^sub>c g = id\<^sub>c (codomain f)"
    using assms unfolding isomorphism_def cfunc_type_def by auto
next
  fix g1 g2
  assume g1_f: "g1 \<circ>\<^sub>c f = id\<^sub>c (domain f)" and f_g1: "f \<circ>\<^sub>c g1 = id\<^sub>c (codomain f)"
  assume g2_f: "g2 \<circ>\<^sub>c f = id\<^sub>c (domain f)" and f_g2: "f \<circ>\<^sub>c g2 = id\<^sub>c (codomain f)"
  assume "g1 : codomain f \<rightarrow> domain f" "g2 : codomain f \<rightarrow> domain f"
  then have "codomain g1 = domain f" "domain g2 = codomain f"
    unfolding cfunc_type_def by auto
  then show "g1 = g2"
    by (metis comp_associative f_g1 g2_f id_left_unit id_right_unit)
qed

lemma inverse_type[type_rule]:
  assumes "isomorphism f" "f : X \<rightarrow> Y"
  shows "f\<^bold>\<inverse> : Y \<rightarrow> X"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_left:
  assumes "isomorphism f" "f : X \<rightarrow> Y"
  shows "f\<^bold>\<inverse> \<circ>\<^sub>c f = id X"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_right:
  assumes "isomorphism f" "f : X \<rightarrow> Y"
  shows "f \<circ>\<^sub>c f\<^bold>\<inverse> = id Y"
  using assms inverse_def2 unfolding cfunc_type_def by auto

lemma inv_iso:
  assumes "isomorphism f"
  shows "isomorphism(f\<^bold>\<inverse>)"
  using assms inverse_def2 unfolding isomorphism_def cfunc_type_def by (intro exI[where x=f], auto)

lemma inv_idempotent:
  assumes "isomorphism f"
  shows "(f\<^bold>\<inverse>)\<^bold>\<inverse> = f"
  by (smt assms cfunc_type_def comp_associative id_left_unit inv_iso inverse_def2)

definition is_isomorphic :: "cset \<Rightarrow> cset \<Rightarrow> bool" (infix "\<cong>" 50)  where
  "X \<cong> Y \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> Y \<and> isomorphism f)"

lemma id_isomorphism: "isomorphism (id X)"
  unfolding isomorphism_def
  by (intro exI[where x= "id X"], auto simp add: id_codomain id_domain, metis id_domain id_right_unit)

lemma isomorphic_is_reflexive: "X \<cong> X"
  unfolding is_isomorphic_def
  by (intro exI[where x= "id X"], auto simp add: id_domain id_codomain id_isomorphism id_type)

lemma isomorphic_is_symmetric: "X \<cong> Y \<longrightarrow> Y \<cong> X"
  unfolding is_isomorphic_def isomorphism_def 
  by (auto, metis cfunc_type_def)

lemma isomorphism_comp: 
  "domain f = codomain g \<Longrightarrow> isomorphism f \<Longrightarrow> isomorphism g \<Longrightarrow> isomorphism (f \<circ>\<^sub>c g)"
  unfolding isomorphism_def by (auto, smt codomain_comp comp_associative domain_comp id_right_unit)

lemma isomorphism_comp': 
  assumes "f : Y \<rightarrow> Z" "g : X \<rightarrow> Y"
  shows "isomorphism f \<Longrightarrow> isomorphism g \<Longrightarrow> isomorphism (f \<circ>\<^sub>c g)"
  using assms cfunc_type_def isomorphism_comp by auto

lemma isomorphic_is_transitive: "(X \<cong> Y \<and> Y \<cong> Z) \<longrightarrow> X \<cong> Z"
  unfolding is_isomorphic_def by (auto, metis cfunc_type_def comp_type isomorphism_comp)

lemma is_isomorphic_equiv:
  "equiv UNIV {(X, Y). X \<cong> Y}"
  unfolding equiv_def
proof safe
  show "refl {(x, y). x \<cong> y}"
    unfolding refl_on_def using isomorphic_is_reflexive by auto
next
  show "sym {(x, y). x \<cong> y}"
    unfolding sym_def using isomorphic_is_symmetric by blast
next
  show "trans {(x, y). x \<cong> y}"
    unfolding trans_def using isomorphic_is_transitive by blast
qed

text \<open>The lemma below corresponds to Exercise 2.1.7e in Halvorson.\<close>
lemma iso_imp_epi_and_monic:
  "isomorphism f \<Longrightarrow> epimorphism f \<and> monomorphism f"
  unfolding isomorphism_def epimorphism_def monomorphism_def
proof safe
  fix g s t
  assume domain_g: "domain g = codomain f"
  assume codomain_g: "codomain g = domain f"
  assume gf_id: "g \<circ>\<^sub>c f = id (domain f)"
  assume fg_id: "f \<circ>\<^sub>c g = id (domain g)"
  assume domain_s: "domain s = codomain f"
  assume domain_t: "domain t = codomain f"
  assume sf_eq_tf: "s \<circ>\<^sub>c f = t \<circ>\<^sub>c f"

  have "s = s \<circ>\<^sub>c id(codomain(f))"
    by (metis domain_s id_right_unit)
  also have "... = s \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
    by (simp add: domain_g fg_id)
  also have "... = (s \<circ>\<^sub>c f) \<circ>\<^sub>c g"
    by (simp add: codomain_g comp_associative domain_s)
  also have "... = (t \<circ>\<^sub>c f) \<circ>\<^sub>c g"
    by (simp add: sf_eq_tf)
  also have "... = t \<circ>\<^sub>c (f \<circ>\<^sub>c g)"
    by (simp add: codomain_g comp_associative domain_t)
  also have "... = t \<circ>\<^sub>c id(codomain f)"
    by (simp add: domain_g fg_id)
  also have "... = t"
    by (metis domain_t id_right_unit)    
  finally show "s = t".
next
  fix g h k
  assume domain_g: "domain g = codomain f"
  assume codomain_g: "codomain g = domain f"
  assume gf_id: "g \<circ>\<^sub>c f = id (domain f)"
  assume fg_id: "f \<circ>\<^sub>c g = id (domain g)"
  assume codomain_h: "codomain h = domain f"
  assume codomain_k: "codomain k = domain f"
  assume fk_eq_fh: "f \<circ>\<^sub>c k = f \<circ>\<^sub>c h"

  have "h = id(domain f) \<circ>\<^sub>c h"
    by (metis codomain_h id_left_unit)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c h"
    using gf_id by auto
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c h)"
    by (simp add: codomain_h comp_associative domain_g)
  also have "... = g \<circ>\<^sub>c (f \<circ>\<^sub>c k)"
    by (simp add: fk_eq_fh)
  also have "... = (g \<circ>\<^sub>c f) \<circ>\<^sub>c k"
    by (simp add: codomain_k comp_associative domain_g)
  also have "... = id(domain f) \<circ>\<^sub>c k"
    by (simp add: gf_id)
  also have "... = k"
    by (metis codomain_k id_left_unit)
  ultimately show "k = h"
    by simp
qed

lemma isomorphism_sandwich: 
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C" and h_type: "h: C \<rightarrow> D"
  assumes f_iso: "isomorphism f"
  assumes h_iso: "isomorphism h"
  assumes hgf_iso: "isomorphism(h \<circ>\<^sub>c g \<circ>\<^sub>c f)"
  shows "isomorphism g"
proof -
  have "isomorphism(h\<^bold>\<inverse> \<circ>\<^sub>c (h \<circ>\<^sub>c g \<circ>\<^sub>c f) \<circ>\<^sub>c f\<^bold>\<inverse>)"
    using assms by (typecheck_cfuncs, simp add: f_iso h_iso hgf_iso inv_iso isomorphism_comp')
  then show "isomorphism g"
    using assms by (typecheck_cfuncs_prems, smt comp_associative2 id_left_unit2 id_right_unit2 inv_left inv_right)
qed

end