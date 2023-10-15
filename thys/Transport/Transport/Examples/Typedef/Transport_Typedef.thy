\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Transport_Typedef
  imports
    "HOL-Library.FSet"
    Transport_Typedef_Base
    Transport_Prototype
    Transport_Syntax
begin

context
  includes galois_rel_syntax transport_syntax
begin

typedef pint = "{i :: int. 0 \<le> i}" by auto

interpretation typedef_pint : type_definition Rep_pint Abs_pint "{i :: int. 0 \<le> i}"
  by (fact type_definition_pint)

lemma [trp_relator_rewrite, trp_uhint]:
  "(\<^bsub>(=\<^bsub>Collect ((\<le>) (0 :: int))\<^esub>)\<^esub>\<lessapprox>\<^bsub>(=) Rep_pint\<^esub>) \<equiv> typedef_pint.AR"
  using typedef_pint.left_Galois_eq_AR by (intro eq_reflection) simp

typedef 'a fset = "{s :: 'a set. finite s}" by auto

interpretation typedef_fset :
  type_definition Rep_fset Abs_fset "{s :: 'a set. finite s}"
  by (fact type_definition_fset)

lemma [trp_relator_rewrite, trp_uhint]:
  "(\<^bsub>(=\<^bsub>{s :: 'a set. finite s}\<^esub>) :: 'a set \<Rightarrow> _\<^esub>\<lessapprox>\<^bsub>(=) Rep_fset\<^esub>) \<equiv> typedef_fset.AR"
  using typedef_fset.left_Galois_eq_AR by (intro eq_reflection) simp

lemma eq_restrict_set_eq_eq_uhint [trp_uhint]:
  "P \<equiv> \<lambda>x. x \<in> A \<Longrightarrow> ((=\<^bsub>A :: 'a set\<^esub>) :: 'a \<Rightarrow> _) \<equiv> (=\<^bsub>P\<^esub>)"
  by simp

(*could also automatically tagged for every instance in type_definition*)
declare
  typedef_pint.partial_equivalence_rel_equivalence[per_intro]
  typedef_fset.partial_equivalence_rel_equivalence[per_intro]


lemma one_parametric [trp_in_dom]: "typedef_pint.L 1 1" by auto

trp_term pint_one :: "pint" where x = "1 :: int"
  by trp_prover

lemma add_parametric [trp_in_dom]:
  "(typedef_pint.L \<Rrightarrow> typedef_pint.L \<Rrightarrow> typedef_pint.L) (+) (+)"
  by (intro Dep_Fun_Rel_relI) (auto intro!: eq_restrictI elim!: eq_restrictE)

trp_term pint_add :: "pint \<Rightarrow> pint \<Rightarrow> pint"
  where x = "(+) :: int \<Rightarrow> _"
  by trp_prover

lemma empty_parametric [trp_in_dom]: "typedef_fset.L {} {}"
  by auto

trp_term fempty :: "'a fset" where x = "{} :: 'a set"
  by trp_prover


lemma insert_parametric [trp_in_dom]:
  "((=) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L) insert insert"
  by auto

trp_term finsert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where x = insert
  and L = "((=) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L)"
  and R = "((=) \<Rrightarrow> typedef_fset.R \<Rrightarrow> typedef_fset.R)"
  by trp_prover


(*experiments with white-box transports*)

context
  notes refl[trp_related_intro]
begin

trp_term insert_add_int_fset_whitebox :: "int fset"
  where x = "insert (1 + (1 :: int)) {}" !
  by trp_whitebox_prover

lemma empty_parametric' [trp_related_intro]: "(rel_set R) {} {}"
  by (intro Dep_Fun_Rel_relI rel_setI) (auto dest: rel_setD1 rel_setD2)

lemma insert_parametric' [trp_related_intro]:
  "(R \<Rrightarrow> rel_set R \<Rrightarrow> rel_set R) insert insert"
  by (intro Dep_Fun_Rel_relI rel_setI) (auto dest: rel_setD1 rel_setD2)

context
  assumes [trp_uhint]:
  (*proven for all natural functors*)
  "L \<equiv> rel_set (L1 :: int \<Rightarrow> int \<Rightarrow> bool) \<Longrightarrow> R \<equiv> rel_set (R1 :: pint \<Rightarrow> pint \<Rightarrow> bool)
  \<Longrightarrow> r \<equiv> image r1 \<Longrightarrow> S \<equiv> (\<^bsub>L1\<^esub>\<lessapprox>\<^bsub>R1 r1\<^esub>) \<Longrightarrow> (\<^bsub>L\<^esub>\<lessapprox>\<^bsub>R r\<^esub>) \<equiv> rel_set S"
begin

trp_term insert_add_pint_set_whitebox :: "pint set"
  where x = "insert (1 + (1 :: int)) {}" !
  by trp_whitebox_prover

print_statement insert_add_int_fset_whitebox_def insert_add_pint_set_whitebox_def

end
end

lemma image_parametric [trp_in_dom]:
  "(((=) \<Rrightarrow> (=)) \<Rrightarrow> typedef_fset.L \<Rrightarrow> typedef_fset.L) image image"
  by (intro Dep_Fun_Rel_relI) auto

trp_term fimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" where x = image
  by trp_prover

(*experiments with compositions*)

lemma rel_fun_eq_Fun_Rel_rel: "rel_fun = Fun_Rel_rel"
  by (intro ext iffI Dep_Fun_Rel_relI) (auto elim: rel_funE)

lemma image_parametric' [trp_related_intro]:
  "((R \<Rrightarrow> S) \<Rrightarrow> rel_set R \<Rrightarrow> rel_set S) image image"
  using transfer_raw[simplified rel_fun_eq_Fun_Rel_rel Transfer.Rel_def]
  by simp

lemma Galois_id_hint [trp_uhint]:
  "(L :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> R \<Longrightarrow> r \<equiv> id \<Longrightarrow> E \<equiv> L \<Longrightarrow> (\<^bsub>L\<^esub>\<lessapprox>\<^bsub>R r\<^esub>) \<equiv> E"
  by (simp only: eq_reflection[OF transport_id.left_Galois_eq_left])

lemma Freq [trp_uhint]: "L \<equiv> (=) \<Rrightarrow> (=) \<Longrightarrow> L \<equiv> (=)"
  by auto

context
  fixes L1 R1 l1 r1 L R l r
  assumes per1: "(L1 \<equiv>\<^bsub>PER\<^esub> R1) l1 r1"
  defines "L \<equiv> rel_set L1" and "R \<equiv> rel_set R1"
  and "l \<equiv> image l1" and "r \<equiv> image r1"
begin

interpretation transport L R l r .

context
  (*proven for all natural functors*)
  assumes transport_per_set: "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and compat: "transport_comp.middle_compatible_codom R typedef_fset.L"
begin

trp_term fempty_param :: "'b fset"
  where x = "{} :: 'a set"
  and L = "transport_comp.L ?L1 ?R1 (?l1 :: 'a set \<Rightarrow> 'b set) ?r1 typedef_fset.L"
  and R = "transport_comp.L typedef_fset.R typedef_fset.L ?r2 ?l2 ?R1"
  apply (rule transport_comp.partial_equivalence_rel_equivalenceI)
    apply (rule transport_per_set)
    apply per_prover
    apply (fact compat)
  apply (rule transport_comp.left_relI[where ?y="{}" and ?y'="{}"])
  apply (unfold L_def R_def l_def r_def)
  apply (auto intro!: galois_rel.left_GaloisI in_codomI empty_transfer)
  done

definition "set_succ \<equiv> image ((+) (1 :: int))"

lemma set_succ_parametric [trp_in_dom]:
  "(typedef_fset.L \<Rrightarrow> typedef_fset.L) set_succ set_succ"
  unfolding set_succ_def by auto

trp_term fset_succ :: "int fset \<Rightarrow> int fset"
  where x = set_succ
  and L = "typedef_fset.L \<Rrightarrow> typedef_fset.L"
  and R = "typedef_fset.R \<Rrightarrow> typedef_fset.R"
  by trp_prover

trp_term fset_succ' :: "int fset \<Rightarrow> int fset"
  where x = set_succ
  and L = "typedef_fset.L \<Rrightarrow> typedef_fset.L"
  and R = "typedef_fset.R \<Rrightarrow> typedef_fset.R"
  unfold set_succ_def !
  (*current prototype gets lost in this example*)
  using refl[trp_related_intro]
  apply (tactic \<open>Transport.instantiate_skeleton_tac @{context} 1\<close>)
  apply (tactic \<open>Transport.transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>Transport.transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>Transport.transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>Transport.transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>Transport.transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>Transport.transport_related_step_tac @{context} 1\<close>)
  apply assumption
  apply assumption
  prefer 3
  apply (tactic \<open>Transport.transport_related_step_tac @{context} 1\<close>)
  apply (tactic \<open>Transport.transport_related_step_tac @{context} 1\<close>)
  apply (fold trp_def)
  apply (trp_relator_rewrite)+
  apply (unfold trp_def)
  apply (trp_hints_resolve refl)
  done

lemma pint_middle_compat:
  "transport_comp.middle_compatible_codom (rel_set ((=) :: pint \<Rightarrow> _))
  (=\<^bsub>Collect (finite :: pint set \<Rightarrow> _)\<^esub>)"
  by (intro transport_comp.middle_compatible_codom_if_right1_le_eqI)
  (auto simp: rel_set_eq intro!: transitiveI)

trp_term pint_fset_succ :: "pint fset \<Rightarrow> pint fset"
  where x = "set_succ :: int set \<Rightarrow> int set"
  (*automation for composition not supported as of now*)
  oops

end
end
end

end