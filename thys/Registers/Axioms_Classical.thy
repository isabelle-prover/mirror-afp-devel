section \<open>Classical instantiation of registerss\<close>

(* AXIOM INSTANTIATION (use instantiate_laws.py to generate Laws_Classical.thy)
 
   domain \<rightarrow> type
   comp_update \<rightarrow> map_comp
   id_update \<rightarrow> Some

   Generic laws about registers \<rightarrow> Generic laws about registers, instantiated classically
*)

theory Axioms_Classical
  imports Main
begin

type_synonym 'a update = \<open>'a \<rightharpoonup> 'a\<close>

lemma id_update_left: "Some \<circ>\<^sub>m a = a"
  by (auto intro!: ext simp add: map_comp_def option.case_eq_if)
lemma id_update_right: "a \<circ>\<^sub>m Some = a"
  by auto

lemma comp_update_assoc: "(a \<circ>\<^sub>m b) \<circ>\<^sub>m c = a \<circ>\<^sub>m (b \<circ>\<^sub>m c)"
  by (auto intro!: ext simp add: map_comp_def option.case_eq_if)

type_synonym ('a,'b) preregister = \<open>'a update \<Rightarrow> 'b update\<close>
definition preregister :: \<open>('a,'b) preregister \<Rightarrow> bool\<close> where
  \<open>preregister F \<longleftrightarrow> (\<exists>g s. \<forall>a m. F a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> s x m))\<close>

lemma id_preregister: \<open>preregister id\<close>
  unfolding preregister_def
  apply (rule exI[of _ \<open>\<lambda>m. m\<close>])
  apply (rule exI[of _ \<open>\<lambda>a m. Some a\<close>])
  by (simp add: option.case_eq_if)

lemma preregister_mult_right: \<open>preregister (\<lambda>a. a \<circ>\<^sub>m z)\<close>
  unfolding preregister_def 
  apply (rule exI[of _ \<open>\<lambda>m. the (z m)\<close>])
  apply (rule exI[of _ \<open>\<lambda>x m. case z m of None \<Rightarrow> None | _ \<Rightarrow> Some x\<close>])
  by (auto simp add: option.case_eq_if)

lemma preregister_mult_left: \<open>preregister (\<lambda>a. z \<circ>\<^sub>m a)\<close>
  unfolding preregister_def 
  apply (rule exI[of _ \<open>\<lambda>m. m\<close>])
  apply (rule exI[of _ \<open>\<lambda>x m. z x\<close>])
  by (auto simp add: option.case_eq_if)

lemma comp_preregister: "preregister (G \<circ> F)" if "preregister F" and \<open>preregister G\<close>
proof -
  from \<open>preregister F\<close>
  obtain sF gF where F: \<open>F a m = (case a (gF m) of None \<Rightarrow> None | Some x \<Rightarrow> sF x m)\<close> for a m
    using preregister_def by blast
  from \<open>preregister G\<close>
  obtain sG gG where G: \<open>G a m = (case a (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> sG x m)\<close> for a m
    using preregister_def by blast
  define s g where \<open>s a m = (case sF a (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> sG x m)\<close>
    and \<open>g m = gF (gG m)\<close> for a m
  have \<open>(G \<circ> F) a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> s x m)\<close> for a m
    unfolding F G s_def g_def
    by (auto simp add: option.case_eq_if)
  then show "preregister (G \<circ> F)"
    using preregister_def by blast
qed

definition tensor_update :: \<open>'a update \<Rightarrow> 'b update \<Rightarrow> ('a\<times>'b) update\<close> where
  \<open>tensor_update a b m = (case a (fst m) of None \<Rightarrow> None | Some x \<Rightarrow> (case b (snd m) of None \<Rightarrow> None | Some y \<Rightarrow> Some (x,y)))\<close>

lemma tensor_update_mult: \<open>tensor_update a c \<circ>\<^sub>m tensor_update b d = tensor_update (a \<circ>\<^sub>m b) (c \<circ>\<^sub>m d)\<close>
  by (auto intro!: ext simp add: map_comp_def option.case_eq_if tensor_update_def)

definition update1 :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a update\<close> where
  \<open>update1 x y m = (if m=x then Some y else None)\<close>

lemma update1_extensionality:
  assumes \<open>preregister F\<close>
  assumes \<open>preregister G\<close>
  assumes FGeq: \<open>\<And>x y. F (update1 x y) = G (update1 x y)\<close>
  shows "F = G"
proof (rule ccontr)
  assume neq: \<open>F \<noteq> G\<close>
  then obtain z m where neq': \<open>F z m \<noteq> G z m\<close> 
    apply atomize_elim by auto
  obtain gF sF where gsF: \<open>F z m = (case z (gF m) of None \<Rightarrow> None | Some x \<Rightarrow> sF x m)\<close> for z m
    using \<open>preregister F\<close> preregister_def by blast
  obtain gG sG where gsG: \<open>G z m = (case z (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> sG x m)\<close> for z m
    using \<open>preregister G\<close> preregister_def by blast
  consider (abeq) x where \<open>z (gF m) = Some x\<close> \<open>z (gG m) = Some x\<close> \<open>gF m = gG m\<close>
    | (abnone) \<open>z (gG m) = None\<close> \<open>z (gF m) = None\<close>
    | (neqF) x where \<open>gF m \<noteq> gG m\<close> \<open>F z m = Some x\<close>
    | (neqG) y where \<open>gF m \<noteq> gG m\<close> \<open>G z m = Some y\<close>
    | (neqNone) \<open>gF m \<noteq> gG m\<close> \<open>F z m = None\<close> \<open>G z m = None\<close>
    apply atomize_elim by (metis option.exhaust_sel)
  then show False
  proof cases
    case (abeq x)
    then have \<open>F z m = sF x m\<close> and \<open>G z m = sG x m\<close>
      by (simp_all add: gsF gsG)
    moreover have \<open>F (update1 (gF m) x) m = sF x m\<close>
      by (simp add: gsF update1_def)
    moreover have \<open>G (update1 (gF m) x) m = sG x m\<close>
      by (simp add: abeq gsG update1_def)
    ultimately show False
      using FGeq neq' by force
  next
    case abnone
    then show False
      using gsF gsG neq' by force
  next
    case neqF
    moreover
    have \<open>F (update1 (gF m) (the (z (gF m)))) m = F z m\<close>
      by (metis gsF neqF(2) option.case_eq_if option.simps(3) option.simps(5) update1_def)
    moreover have \<open>G (update1 (gF m) (the (z (gF m)))) m = None\<close>
      by (metis gsG neqF(1) option.case_eq_if update1_def)
    ultimately show False
      using FGeq by force
  next
    case neqG
    moreover
    have \<open>G (update1 (gG m) (the (z (gG m)))) m = G z m\<close>
      by (metis gsG neqG(2) option.case_eq_if option.distinct(1) option.simps(5) update1_def)
    moreover have \<open>F (update1 (gG m) (the (z (gG m)))) m = None\<close>
      by (simp add: gsF neqG(1) update1_def)
    ultimately show False
      using FGeq by force
  next
    case neqNone
    with neq' show False
      by fastforce
  qed
qed

lemma tensor_extensionality:
  assumes \<open>preregister F\<close>
  assumes \<open>preregister G\<close>
  assumes FGeq: \<open>\<And>a b. F (tensor_update a b) = G (tensor_update a b)\<close>
  shows "F = G"
proof -
  have \<open>F (update1 x y) = G (update1 x y)\<close> for x y
    using FGeq[of \<open>update1 (fst x) (fst y)\<close> \<open>update1 (snd x) (snd y)\<close>]
    apply (auto intro!:ext simp: tensor_update_def[abs_def] update1_def[abs_def])
    by (smt (z3) assms(1) assms(2) option.case(2) option.case_eq_if preregister_def prod.collapse)
  with assms(1,2) show "F = G"
    by (rule update1_extensionality)
qed

definition "valid_getter_setter g s \<longleftrightarrow> 
  (\<forall>b. b = s (g b) b) \<and> (\<forall>a b. g (s a b) = a) \<and> (\<forall>a a' b. s a (s a' b) = s a b)"

definition \<open>register_from_getter_setter g s a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (s x m))\<close>
definition \<open>register_apply F a = the o F (Some o a)\<close>
definition \<open>setter F a m = register_apply F (\<lambda>_. a) m\<close> for F :: \<open>'a update \<Rightarrow> 'b update\<close>
definition \<open>getter F m = (THE x. setter F x m = m)\<close> for F :: \<open>'a update \<Rightarrow> 'b update\<close>

lemma
  assumes \<open>valid_getter_setter g s\<close>
  shows getter_of_register_from_getter_setter[simp]: \<open>getter (register_from_getter_setter g s) = g\<close>
    and setter_of_register_from_getter_setter[simp]: \<open>setter (register_from_getter_setter g s) = s\<close>
proof -
  define g' s' where \<open>g' = getter (register_from_getter_setter g s)\<close>
    and \<open>s' = setter (register_from_getter_setter g s)\<close>
  show \<open>s' = s\<close>
    by (auto intro!:ext simp: s'_def setter_def register_apply_def register_from_getter_setter_def)
  moreover show \<open>g' = g\<close>
  proof (rule ext, rename_tac m)
    fix m
    have \<open>g' m = (THE x. s x m = m)\<close>
      by (auto intro!:ext simp: g'_def s'_def[symmetric] \<open>s'=s\<close> getter_def register_apply_def register_from_getter_setter_def)
    moreover have \<open>s (g m) m = m\<close>
      by (metis assms valid_getter_setter_def)
    moreover have \<open>x = x'\<close> if \<open>s x m = m\<close> \<open>s x' m = m\<close> for x x'
      by (metis assms that(1) that(2) valid_getter_setter_def)
    ultimately show \<open>g' m = g m\<close>
      by (simp add: Uniq_def the1_equality')
  qed
qed

definition register :: \<open>('a,'b) preregister \<Rightarrow> bool\<close> where
  \<open>register F \<longleftrightarrow> (\<exists>g s. F = register_from_getter_setter g s \<and> valid_getter_setter g s)\<close>

lemma register_of_id: \<open>register F \<Longrightarrow> F Some = Some\<close>
  by (auto simp add: register_def valid_getter_setter_def register_from_getter_setter_def)

lemma register_id: \<open>register id\<close>
  unfolding register_def
  apply (rule exI[of _ id], rule exI[of _ \<open>\<lambda>a m. a\<close>])
  by (auto intro!: ext simp: option.case_eq_if register_from_getter_setter_def valid_getter_setter_def)

lemma register_tensor_left: \<open>register (\<lambda>a. tensor_update a Some)\<close>
  apply (auto simp: register_def)
  apply (rule exI[of _ fst])
  apply (rule exI[of _ \<open>\<lambda>x' (x,y). (x',y)\<close>])
  by (auto intro!: ext simp add: tensor_update_def valid_getter_setter_def register_from_getter_setter_def option.case_eq_if)

lemma register_tensor_right: \<open>register (\<lambda>a. tensor_update Some a)\<close>
  apply (auto simp: register_def)
  apply (rule exI[of _ snd])
  apply (rule exI[of _ \<open>\<lambda>y' (x,y). (x,y')\<close>])
  by (auto intro!: ext simp add: tensor_update_def valid_getter_setter_def register_from_getter_setter_def option.case_eq_if)

lemma register_preregister: "preregister F" if \<open>register F\<close>
proof -
  from \<open>register F\<close>
  obtain s g where F: \<open>F a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (s x m))\<close> for a m
    unfolding register_from_getter_setter_def register_def by blast
  show ?thesis
    unfolding preregister_def
    apply (rule exI[of _ g])
    apply (rule exI[of _ \<open>\<lambda>x m. Some (s x m)\<close>])
    using F by simp
qed

lemma register_comp: "register (G \<circ> F)" if \<open>register F\<close> and \<open>register G\<close>
  for F :: "('a,'b) preregister" and G :: "('b,'c) preregister"
proof -
  from \<open>register F\<close>
  obtain sF gF where F: \<open>F a m = (case a (gF m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sF x m))\<close>
    and validF: \<open>valid_getter_setter gF sF\<close> for a m
    unfolding register_def register_from_getter_setter_def by blast
  from \<open>register G\<close>
  obtain sG gG where G: \<open>G a m = (case a (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sG x m))\<close>
    and validG: \<open>valid_getter_setter gG sG\<close> for a m
    unfolding register_def register_from_getter_setter_def by blast
  define s g where \<open>s a m = sG (sF a (gG m)) m\<close> and \<open>g m = gF (gG m)\<close> for a m
  have \<open>(G \<circ> F) a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (s x m))\<close> for a m
    by (auto simp add: option.case_eq_if F G s_def g_def)
  moreover have \<open>valid_getter_setter g s\<close>
    using validF validG by (auto simp: valid_getter_setter_def s_def g_def)
  ultimately show "register (G \<circ> F)"
    unfolding register_def register_from_getter_setter_def by blast
qed

lemma register_mult: "register F \<Longrightarrow> F a \<circ>\<^sub>m F b = F (a \<circ>\<^sub>m b)"
  by (auto intro!: ext simp: register_def register_from_getter_setter_def[abs_def] valid_getter_setter_def map_comp_def option.case_eq_if)

definition register_pair ::
  \<open>('a update \<Rightarrow> 'c update) \<Rightarrow> ('b update \<Rightarrow> 'c update) \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  \<open>register_pair F G =
    register_from_getter_setter (\<lambda>m. (getter F m, getter G m)) (\<lambda>(a,b) m. setter F a (setter G b m))\<close>

lemma compatible_setter:
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  assumes compat: \<open>\<And>a b. F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a\<close>
  shows \<open>setter F x o setter G y = setter G y o setter F x\<close>
  using compat apply (auto intro!: ext simp: setter_def register_apply_def o_def map_comp_def)
  by (smt (verit, best) assms(1) assms(2) option.case_eq_if option.distinct(1) register_def register_from_getter_setter_def)

lemma register_pair_apply:
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  assumes \<open>\<And>a b. F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a\<close>
  shows \<open>(register_pair F G) (tensor_update a b) = F a \<circ>\<^sub>m G b\<close>
proof -
  have validF: \<open>valid_getter_setter (getter F) (setter F)\<close> and validG: \<open>valid_getter_setter (getter G) (setter G)\<close>
    by (metis assms getter_of_register_from_getter_setter register_def setter_of_register_from_getter_setter)+
  then have F: \<open>F = register_from_getter_setter (getter F) (setter F)\<close> and G: \<open>G = register_from_getter_setter (getter G) (setter G)\<close>
    by (metis assms getter_of_register_from_getter_setter register_def setter_of_register_from_getter_setter)+
  have gFsG: \<open>getter F (setter G y m) = getter F m\<close> for y m
  proof -
    have \<open>getter F (setter G y m) = getter F (setter G y (setter F (getter F m) m))\<close>
      using validF by (metis valid_getter_setter_def)
    also have \<open>\<dots> = getter F (setter F (getter F m) (setter G y m))\<close>
      by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) comp_eq_dest_lhs compatible_setter)
    also have \<open>\<dots> = getter F m\<close>
      by (metis validF valid_getter_setter_def)
    finally show ?thesis by -
  qed

  show ?thesis
    apply (subst (2) F, subst (2) G)
    by (auto intro!:ext simp: register_pair_def tensor_update_def map_comp_def option.case_eq_if
              register_from_getter_setter_def gFsG)
qed

lemma register_pair_is_register:
  fixes F :: \<open>'a update \<Rightarrow> 'c update\<close> and G
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close>
  assumes compat: \<open>\<And>a b. F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a\<close>
  shows \<open>register (register_pair F G)\<close>
proof -
  have validF: \<open>valid_getter_setter (getter F) (setter F)\<close> and validG: \<open>valid_getter_setter (getter G) (setter G)\<close>
    by (metis assms getter_of_register_from_getter_setter register_def setter_of_register_from_getter_setter)+
  then have \<open>valid_getter_setter (\<lambda>m. (getter F m, getter G m)) (\<lambda>(a, b) m. setter F a (setter G b m))\<close>
    apply (simp add: valid_getter_setter_def)
    by (metis (mono_tags, lifting) assms comp_eq_dest_lhs compat compatible_setter)
  then show ?thesis
    by (auto simp: register_pair_def register_def)
qed

end
